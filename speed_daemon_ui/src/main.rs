use eframe::egui;
use std::ffi::c_void;
use std::path::{Path, PathBuf};
use windows::core::{s, w};
use windows::Win32::Foundation::{BOOL, CloseHandle, HANDLE, INVALID_HANDLE_VALUE};
use windows::Win32::System::Diagnostics::Debug::WriteProcessMemory;
use windows::Win32::System::Diagnostics::ToolHelp::{
    CreateToolhelp32Snapshot, Module32FirstW, Module32NextW, Process32FirstW, Process32NextW,
    MODULEENTRY32W, PROCESSENTRY32W, TH32CS_SNAPMODULE, TH32CS_SNAPMODULE32, TH32CS_SNAPPROCESS,
};
use windows::Win32::System::LibraryLoader::{GetModuleHandleW, GetProcAddress};
use windows::Win32::System::Memory::{
    CreateFileMappingW, MapViewOfFile, VirtualAllocEx, VirtualFreeEx, FILE_MAP_ALL_ACCESS,
    MEM_COMMIT, MEM_RELEASE, MEM_RESERVE, PAGE_READWRITE,
};
use windows::Win32::System::Threading::{
    CreateRemoteThread, IsWow64Process, OpenProcess, WaitForSingleObject, INFINITE,
    PROCESS_CREATE_THREAD, PROCESS_QUERY_INFORMATION, PROCESS_QUERY_LIMITED_INFORMATION,
    PROCESS_VM_OPERATION, PROCESS_VM_READ, PROCESS_VM_WRITE,
};

const PRESETS: &[f64] = &[
    0.1, 0.25, 0.5, 1.0, 1.5, 2.0, 3.0, 5.0, 10.0, 25.0, 50.0, 100.0,
];

/// Common user-mode anti-cheat background services, launchers, and tray daemons.
const KNOWN_ANTICHEAT_PROCESSES: &[(&str, &str)] = &[
    ("eaclauncher.exe", "Easy Anti-Cheat (EAC)"),
    ("easyanticheat.exe", "Easy Anti-Cheat (EAC)"),
    ("easyanticheat_eos.exe", "Easy Anti-Cheat (EOS)"),
    ("beservice.exe", "BattlEye Service"),
    ("bedaisy.exe", "BattlEye"),
    ("vgtray.exe", "Riot Vanguard"),
    ("vgc.exe", "Riot Vanguard Service"),
    ("faceitclient.exe", "FACEIT Anti-Cheat"),
    ("faceitservice.exe", "FACEIT Anti-Cheat"),
    ("eseaclient.exe", "ESEA Anti-Cheat"),
    ("punkbstra.exe", "PunkBuster A"),
    ("punkbstrb.exe", "PunkBuster B"),
    ("xhunter1.sys", "XIGNCODE3"),
    ("xxd-0.xem", "XIGNCODE3"),
    ("gameguard.des", "nProtect GameGuard"),
    ("gamemon.des", "nProtect GameGuard"),
    ("mhyprot2.sys", "HoYoverse Anti-Cheat"),
    ("zksvc.exe", "ACE / Anti-Cheat Expert"),
    ("sguard64.exe", "ACE / Anti-Cheat Expert"),
    ("sguardsvc64.exe", "ACE / Anti-Cheat Expert"),
    ("ricochet.exe", "Call of Duty RICOCHET"),
];

/// Anti-cheat DLL modules commonly loaded directly inside a game's process space.
const KNOWN_ANTICHEAT_MODULES: &[&str] = &[
    "easyanticheat",
    "beclient",
    "battleye",
    "vgk",
    "vanguard",
    "xigncode",
    "gameguard",
    "nprotect",
    "ace-base",
    "equ8",
    "wellbia",
];

#[repr(C)]
struct SharedState {
    speed: f64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TargetArch {
    X64,
    X86,
    Unknown,
}

impl TargetArch {
    fn label(&self) -> &'static str {
        match self {
            TargetArch::X64 => "64-bit (x64)",
            TargetArch::X86 => "32-bit (x86)",
            TargetArch::Unknown => "Unknown Arch",
        }
    }

    fn dll_filename(&self) -> &'static str {
        match self {
            TargetArch::X86 => "speed_daemon_dll_x86.dll",
            TargetArch::X64 | TargetArch::Unknown => "speed_daemon_dll.dll",
        }
    }
}

#[derive(Clone)]
struct ProcessItem {
    pid: u32,
    name: String,
    arch: TargetArch,
}

// --- ISOLATED WIN32 HELPERS ---

/// Detects whether a target process is 32-bit (WOW64) or native 64-bit on 64-bit Windows.
fn detect_process_arch(pid: u32) -> TargetArch {
    // SAFETY: Queries read-only process architecture info via OpenProcess + IsWow64Process.
    unsafe {
        let Ok(h_proc) = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, false, pid) else {
            return TargetArch::Unknown;
        };
        let mut is_wow64 = BOOL(0);
        let ok = IsWow64Process(h_proc, &mut is_wow64).is_ok();
        let _ = CloseHandle(h_proc);

        if !ok {
            TargetArch::Unknown
        } else if is_wow64.as_bool() {
            TargetArch::X86
        } else {
            TargetArch::X64
        }
    }
}

fn list_running_processes() -> Vec<ProcessItem> {
    let mut list = Vec::new();
    // SAFETY: Standard ToolHelp32 snapshot iteration.
    unsafe {
        let Ok(snapshot) = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0) else {
            return list;
        };

        let mut entry = PROCESSENTRY32W {
            dwSize: std::mem::size_of::<PROCESSENTRY32W>() as u32,
            ..Default::default()
        };

        if Process32FirstW(snapshot, &mut entry).is_ok() {
            loop {
                let len = entry
                    .szExeFile
                    .iter()
                    .position(|&c| c == 0)
                    .unwrap_or(entry.szExeFile.len());
                let name = String::from_utf16_lossy(&entry.szExeFile[..len]);
                let pid = entry.th32ProcessID;
                if pid > 4 && !name.is_empty() {
                    let arch = detect_process_arch(pid);
                    list.push(ProcessItem { pid, name, arch });
                }
                if Process32NextW(snapshot, &mut entry).is_err() {
                    break;
                }
            }
        }
        let _ = CloseHandle(snapshot);
    }
    list.sort_by(|a, b| a.name.to_lowercase().cmp(&b.name.to_lowercase()));
    list
}

/// Scans running processes AND loaded modules inside the selected target PID for anti-cheat signs.
fn detect_anticheat_indicators(processes: &[ProcessItem], target_pid: Option<u32>) -> Vec<String> {
    let mut findings = Vec::new();

    // 1. Check active background processes
    for proc in processes {
        let lower = proc.name.to_lowercase();
        for &(exe_name, label) in KNOWN_ANTICHEAT_PROCESSES {
            if lower == exe_name {
                let msg = format!("Running service/process: {} ({})", proc.name, label);
                if !findings.contains(&msg) {
                    findings.push(msg);
                }
            }
        }
    }

    // 2. Inspect loaded DLL modules inside the specific target process (non-invasive read snapshot)
    if let Some(pid) = target_pid {
        // SAFETY: Read-only module enumeration via ToolHelp32 snapshot.
        unsafe {
            if let Ok(snap) =
                CreateToolhelp32Snapshot(TH32CS_SNAPMODULE | TH32CS_SNAPMODULE32, pid)
            {
                let mut mod_entry = MODULEENTRY32W {
                    dwSize: std::mem::size_of::<MODULEENTRY32W>() as u32,
                    ..Default::default()
                };
                if Module32FirstW(snap, &mut mod_entry).is_ok() {
                    loop {
                        let len = mod_entry
                            .szModule
                            .iter()
                            .position(|&c| c == 0)
                            .unwrap_or(mod_entry.szModule.len());
                        let mod_name = String::from_utf16_lossy(&mod_entry.szModule[..len]);
                        let lower_mod = mod_name.to_lowercase();

                        for &sig in KNOWN_ANTICHEAT_MODULES {
                            if lower_mod.contains(sig) {
                                let msg = format!("Loaded module in target PID {pid}: {mod_name}");
                                if !findings.contains(&msg) {
                                    findings.push(msg);
                                }
                            }
                        }

                        if Module32NextW(snap, &mut mod_entry).is_err() {
                            break;
                        }
                    }
                }
                let _ = CloseHandle(snap);
            }
        }
    }

    findings
}

fn resolve_dll_path(arch: TargetArch) -> Result<PathBuf, String> {
    let mut exe_dir = std::env::current_exe().map_err(|e| e.to_string())?;
    exe_dir.pop();

    let filename = arch.dll_filename();
    let dll_path = exe_dir.join(filename);
    if dll_path.exists() {
        Ok(dll_path)
    } else if arch == TargetArch::X86 {
        Err(format!(
            "Target is 32-bit, but '{}' was not found next to executable.\n\
             Build it with: cargo build --release -p speed_daemon_dll --target i686-pc-windows-msvc\n\
             and copy target/i686-pc-windows-msvc/release/speed_daemon_dll.dll to {}",
            filename,
            dll_path.display()
        ))
    } else {
        Err(format!(
            "Could not find '{}' next to executable ({})",
            filename,
            dll_path.display()
        ))
    }
}

fn inject_dll(pid: u32, dll_path: &Path) -> Result<(), String> {
    let wide_path: Vec<u16> = dll_path
        .to_string_lossy()
        .encode_utf16()
        .chain(std::iter::once(0))
        .collect();
    let byte_len = wide_path.len() * std::mem::size_of::<u16>();

    // SAFETY: Standard CreateRemoteThread + LoadLibraryW DLL injection into target PID.
    unsafe {
        let access = PROCESS_CREATE_THREAD
            | PROCESS_QUERY_INFORMATION
            | PROCESS_VM_OPERATION
            | PROCESS_VM_WRITE
            | PROCESS_VM_READ;

        let h_proc: HANDLE = OpenProcess(access, false, pid)
            .map_err(|e| format!("OpenProcess failed (protected process or needs Admin): {e}"))?;

        let remote_mem = VirtualAllocEx(
            h_proc,
            None,
            byte_len,
            MEM_COMMIT | MEM_RESERVE,
            PAGE_READWRITE,
        );
        if remote_mem.is_null() {
            let _ = CloseHandle(h_proc);
            return Err("VirtualAllocEx returned null".into());
        }

        if let Err(e) = WriteProcessMemory(
            h_proc,
            remote_mem,
            wide_path.as_ptr() as *const c_void,
            byte_len,
            None,
        ) {
            let _ = VirtualFreeEx(h_proc, remote_mem, 0, MEM_RELEASE);
            let _ = CloseHandle(h_proc);
            return Err(format!("WriteProcessMemory failed: {e}"));
        }

        let k32 = GetModuleHandleW(w!("kernel32.dll")).map_err(|e| e.to_string())?;
        let load_lib = GetProcAddress(k32, s!("LoadLibraryW"))
            .ok_or("Failed to resolve LoadLibraryW")?;

        let thread_proc: unsafe extern "system" fn(*mut c_void) -> u32 =
            std::mem::transmute(load_lib);

        let h_thread =
            CreateRemoteThread(h_proc, None, 0, Some(thread_proc), Some(remote_mem), 0, None)
                .map_err(|e| format!("CreateRemoteThread failed: {e}"))?;

        WaitForSingleObject(h_thread, INFINITE);

        let _ = CloseHandle(h_thread);
        let _ = VirtualFreeEx(h_proc, remote_mem, 0, MEM_RELEASE);
        let _ = CloseHandle(h_proc);
    }

    Ok(())
}

// --- GUI APPLICATION ---

struct SpeedDaemonApp {
    speed: f64,
    preset_index: usize,
    custom_input: String,
    shared_ptr: *mut SharedState,
    processes: Vec<ProcessItem>,
    selected_pid: Option<u32>,
    filter_text: String,
    status_msg: String,
    anticheat_warnings: Vec<String>,
    show_disclaimer_modal: bool,
    disclaimer_acknowledged: bool,
    pending_inject_pid: Option<u32>,
}

impl SpeedDaemonApp {
    fn new() -> Self {
        let shared_ptr = unsafe {
            let h_map = CreateFileMappingW(
                INVALID_HANDLE_VALUE,
                None,
                PAGE_READWRITE,
                0,
                std::mem::size_of::<SharedState>() as u32,
                w!("Local\\SpeedDaemonMem"),
            )
            .expect("Failed to create shared memory");

            let view = MapViewOfFile(
                h_map,
                FILE_MAP_ALL_ACCESS,
                0,
                0,
                std::mem::size_of::<SharedState>(),
            );
            let ptr = view.Value as *mut SharedState;
            if !ptr.is_null() {
                (*ptr).speed = 1.0;
            }
            ptr
        };

        let processes = list_running_processes();
        let initial_warnings = detect_anticheat_indicators(&processes, None);
        let has_warnings = !initial_warnings.is_empty();

        Self {
            speed: 1.0,
            preset_index: 3, // 1.0x
            custom_input: "1.0".to_string(),
            shared_ptr,
            processes,
            selected_pid: None,
            filter_text: String::new(),
            status_msg: "Ready. Select a target process and click Inject.".to_string(),
            anticheat_warnings: initial_warnings,
            show_disclaimer_modal: has_warnings,
            disclaimer_acknowledged: false,
            pending_inject_pid: None,
        }
    }

    fn refresh_processes(&mut self) {
        self.processes = list_running_processes();
        let warnings = detect_anticheat_indicators(&self.processes, self.selected_pid);
        if !warnings.is_empty() && warnings != self.anticheat_warnings {
            self.disclaimer_acknowledged = false;
            self.show_disclaimer_modal = true;
        }
        self.anticheat_warnings = warnings;
    }

    fn perform_injection(&mut self, pid: u32) {
        let arch = self
            .processes
            .iter()
            .find(|p| p.pid == pid)
            .map(|p| p.arch)
            .unwrap_or(TargetArch::X64);

        if arch == TargetArch::X86 {
            self.status_msg =
                "Note: 32-bit process detected. Cross-arch injection requires a 32-bit helper/injector.".into();
            return;
        }

        match resolve_dll_path(arch) {
            Ok(path) => match inject_dll(pid, &path) {
                Ok(()) => {
                    self.status_msg = format!(
                        "Injected {} ({}) successfully into PID {pid}!",
                        path.file_name().unwrap_or_default().to_string_lossy(),
                        arch.label()
                    );
                }
                Err(err) => {
                    self.status_msg = format!("Error: {err}");
                }
            },
            Err(err) => {
                self.status_msg = err;
            }
        }
    }

    fn set_speed(&mut self, new_speed: f64) {
        let clamped = new_speed.clamp(0.0, 10_000.0);
        self.speed = clamped;
        self.custom_input = format!("{clamped}");

        if let Some((idx, _)) = PRESETS
            .iter()
            .enumerate()
            .min_by(|(_, a), (_, b)| (*a - clamped).abs().total_cmp(&(*b - clamped).abs()))
        {
            self.preset_index = idx;
        }

        if !self.shared_ptr.is_null() {
            // SAFETY: Valid mapped view owned by UI process.
            unsafe {
                (*self.shared_ptr).speed = clamped;
            }
        }
    }
}

impl eframe::App for SpeedDaemonApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        // --- ANTI-CHEAT DISCLAIMER POPUP MODAL ---
        if self.show_disclaimer_modal {
            egui::Window::new("Disclaimer: Anti-Cheat Detected")
                .collapsible(false)
                .resizable(false)
                .anchor(egui::Align2::CENTER_CENTER, [0.0, 0.0])
                .show(ctx, |ui| {
                    ui.colored_label(
                        egui::Color32::from_rgb(255, 180, 60),
                        "Warning: Active anti-cheat software was detected on your system.",
                    );
                    ui.add_space(6.0);
                    ui.label(
                        "Injecting a DLL or hooking Windows timers in a game protected by \
                         anti-cheat will very likely result in a permanent account ban.",
                    );
                    ui.add_space(6.0);
                    ui.label("Detected indicators:");
                    for item in &self.anticheat_warnings {
                        ui.label(format!("  • {item}"));
                    }
                    ui.add_space(8.0);
                    ui.label(
                        "Only proceed if you are targeting an offline/single-player game \
                         without anti-cheat protection.",
                    );
                    ui.add_space(10.0);

                    ui.horizontal(|ui| {
                        if ui.button("I Understand, Dismiss").clicked() {
                            self.disclaimer_acknowledged = true;
                            self.show_disclaimer_modal = false;
                            if let Some(pid) = self.pending_inject_pid.take() {
                                self.perform_injection(pid);
                            }
                        }
                        if ui.button("Cancel").clicked() {
                            self.pending_inject_pid = None;
                            self.show_disclaimer_modal = false;
                            self.status_msg = "Injection cancelled due to anti-cheat warning.".into();
                        }
                    });
                });
        }

        egui::CentralPanel::default().show(ctx, |ui| {
            if self.show_disclaimer_modal {
                ui.disable();
            }

            ui.heading("Speed Daemon");
            ui.add_space(6.0);

            // --- TARGET PROCESS & INJECTION ---
            ui.group(|ui| {
                ui.horizontal(|ui| {
                    ui.label("Filter:");
                    ui.add(egui::TextEdit::singleline(&mut self.filter_text).desired_width(160.0));
                    if ui.button("Refresh").clicked() {
                        self.refresh_processes();
                    }
                });

                let selected_proc = self
                    .selected_pid
                    .and_then(|pid| self.processes.iter().find(|p| p.pid == pid))
                    .cloned();

                let selected_label = selected_proc
                    .as_ref()
                    .map(|p| format!("{} (PID: {}) [{}]", p.name, p.pid, p.arch.label()))
                    .unwrap_or_else(|| "Select a process...".to_string());

                let prev_pid = self.selected_pid;
                ui.horizontal(|ui| {
                    egui::ComboBox::from_id_salt("proc_combo")
                        .selected_text(selected_label)
                        .width(270.0)
                        .show_ui(ui, |ui| {
                            let filter = self.filter_text.to_lowercase();
                            for proc in &self.processes {
                                if filter.is_empty() || proc.name.to_lowercase().contains(&filter) {
                                    let label = format!(
                                        "{} ({}) [{}]",
                                        proc.name,
                                        proc.pid,
                                        proc.arch.label()
                                    );
                                    ui.selectable_value(
                                        &mut self.selected_pid,
                                        Some(proc.pid),
                                        label,
                                    );
                                }
                            }
                        });

                    if self.selected_pid != prev_pid {
                        let warnings =
                            detect_anticheat_indicators(&self.processes, self.selected_pid);
                        if !warnings.is_empty() {
                            self.anticheat_warnings = warnings;
                            self.disclaimer_acknowledged = false;
                            self.show_disclaimer_modal = true;
                        }
                    }

                    if ui.button("Inject DLL").clicked() {
                        if let Some(pid) = self.selected_pid {
                            let warnings =
                                detect_anticheat_indicators(&self.processes, Some(pid));
                            if !warnings.is_empty() && !self.disclaimer_acknowledged {
                                self.anticheat_warnings = warnings;
                                self.pending_inject_pid = Some(pid);
                                self.show_disclaimer_modal = true;
                            } else {
                                self.perform_injection(pid);
                            }
                        } else {
                            self.status_msg = "Select a target process first.".to_string();
                        }
                    }
                });
            });

            ui.add_space(8.0);

            // --- PRESET DISCRETE SLIDER ---
            ui.group(|ui| {
                ui.label(format!("Current Multiplier: {}x", self.speed));

                let mut idx = self.preset_index;
                let preset_label = format!("Preset: {}x", PRESETS[idx]);
                let slider = ui.add(
                    egui::Slider::new(&mut idx, 0..=(PRESETS.len() - 1))
                        .show_value(false)
                        .text(preset_label),
                );
                if slider.changed() {
                    self.preset_index = idx;
                    self.set_speed(PRESETS[idx]);
                }

                ui.add_space(4.0);

                // --- FREE-FORM INPUT & QUICK ACTIONS ---
                ui.horizontal(|ui| {
                    ui.label("Custom (0 - 10000):");
                    let resp = ui.add(
                        egui::TextEdit::singleline(&mut self.custom_input).desired_width(80.0),
                    );
                    if resp.lost_focus() && ui.input(|i| i.key_pressed(egui::Key::Enter)) {
                        if let Ok(val) = self.custom_input.trim().parse::<f64>() {
                            self.set_speed(val);
                        }
                    }
                    if ui.button("Apply").clicked() {
                        if let Ok(val) = self.custom_input.trim().parse::<f64>() {
                            self.set_speed(val);
                        }
                    }
                    if ui.button("Pause (0x)").clicked() {
                        self.set_speed(0.0);
                    }
                    if ui.button("Reset (1x)").clicked() {
                        self.set_speed(1.0);
                    }
                });
            });

            ui.add_space(6.0);
            ui.label(&self.status_msg);
        });
    }
}

fn main() -> eframe::Result {
    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default().with_inner_size([450.0, 265.0]),
        ..Default::default()
    };
    eframe::run_native(
        "Speed Daemon",
        options,
        Box::new(|_cc| Ok(Box::new(SpeedDaemonApp::new()))),
    )
}
