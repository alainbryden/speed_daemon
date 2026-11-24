use minhook::MinHook;
use std::ffi::c_void;
use std::sync::atomic::{AtomicI64, AtomicU64, Ordering};
use windows::core::{s, w, PCSTR, PCWSTR};
use windows::Win32::Foundation::{BOOL, FILETIME, HANDLE, HINSTANCE, HWND, INVALID_HANDLE_VALUE};
use windows::Win32::Media::timeGetTime;
use windows::Win32::System::LibraryLoader::{GetModuleHandleW, GetProcAddress, LoadLibraryW};
use windows::Win32::System::Memory::{
    CreateFileMappingW, MapViewOfFile, FILE_MAP_ALL_ACCESS, PAGE_READWRITE,
};
use windows::Win32::System::Performance::QueryPerformanceCounter;
use windows::Win32::System::SystemInformation::{
    GetSystemTimeAsFileTime, GetSystemTimePreciseAsFileTime, GetTickCount, GetTickCount64,
};
use windows::Win32::System::SystemServices::{DLL_PROCESS_ATTACH, DLL_PROCESS_DETACH};
use windows::Win32::System::Threading::{
    SetWaitableTimer, SetWaitableTimerEx, Sleep, PTIMERAPCROUTINE, REASON_CONTEXT,
};
use windows::Win32::UI::WindowsAndMessaging::{SetTimer, TIMERPROC};

#[repr(C)]
struct SharedState {
    speed: f64,
}

static SHARED_PTR: AtomicU64 = AtomicU64::new(0);

/// Thread-safe lock-free clock scaler usable by any monotonic timestamp API.
struct VirtualClock {
    initialized: AtomicU64,
    last_speed_bits: AtomicU64,
    base_real: AtomicI64,
    base_virtual: AtomicI64,
}

impl VirtualClock {
    const fn new() -> Self {
        Self {
            initialized: AtomicU64::new(0),
            last_speed_bits: AtomicU64::new(1.0_f64.to_bits()),
            base_real: AtomicI64::new(0),
            base_virtual: AtomicI64::new(0),
        }
    }

    fn scale(&self, real_now: i64) -> i64 {
        if self.initialized.swap(1, Ordering::AcqRel) == 0 {
            self.base_real.store(real_now, Ordering::Relaxed);
            self.base_virtual.store(real_now, Ordering::Relaxed);
            return real_now;
        }

        let current_speed = read_target_speed();
        let last_bits = self.last_speed_bits.load(Ordering::Relaxed);
        let new_bits = current_speed.to_bits();

        let mut base_r = self.base_real.load(Ordering::Relaxed);
        let mut base_v = self.base_virtual.load(Ordering::Relaxed);

        if last_bits != new_bits {
            let old_speed = f64::from_bits(last_bits);
            base_v = base_v.wrapping_add(((real_now.wrapping_sub(base_r)) as f64 * old_speed) as i64);
            base_r = real_now;

            self.base_real.store(base_r, Ordering::Relaxed);
            self.base_virtual.store(base_v, Ordering::Relaxed);
            self.last_speed_bits.store(new_bits, Ordering::Relaxed);
        }

        let delta = real_now.wrapping_sub(base_r) as f64;
        base_v.wrapping_add((delta * current_speed) as i64)
    }
}

static CLOCK_QPC: VirtualClock = VirtualClock::new();
static CLOCK_GTC64: VirtualClock = VirtualClock::new();
static CLOCK_GTC32: VirtualClock = VirtualClock::new();
static CLOCK_TGT: VirtualClock = VirtualClock::new();
static CLOCK_FILETIME: VirtualClock = VirtualClock::new();
static CLOCK_PRECISE_FT: VirtualClock = VirtualClock::new();

static ORIG_QPC: AtomicU64 = AtomicU64::new(0);
static ORIG_GTC64: AtomicU64 = AtomicU64::new(0);
static ORIG_GTC32: AtomicU64 = AtomicU64::new(0);
static ORIG_TGT: AtomicU64 = AtomicU64::new(0);
static ORIG_FT: AtomicU64 = AtomicU64::new(0);
static ORIG_PRECISE_FT: AtomicU64 = AtomicU64::new(0);
static ORIG_SLEEP: AtomicU64 = AtomicU64::new(0);
static ORIG_SET_TIMER: AtomicU64 = AtomicU64::new(0);
static ORIG_WAIT_TIMER: AtomicU64 = AtomicU64::new(0);
static ORIG_WAIT_TIMER_EX: AtomicU64 = AtomicU64::new(0);

// --- SAFE HELPERS ---

fn read_target_speed() -> f64 {
    let ptr_addr = SHARED_PTR.load(Ordering::Relaxed);
    if ptr_addr == 0 {
        return 1.0;
    }
    // SAFETY: Valid mapped view for process lifetime.
    let speed = unsafe { (*(ptr_addr as *const SharedState)).speed };
    if speed.is_finite() && (0.0..=10_000.0).contains(&speed) {
        speed
    } else {
        1.0
    }
}

fn scale_duration_ms(ms: u32) -> u32 {
    if ms == 0 || ms == u32::MAX {
        return ms;
    }
    let speed = read_target_speed();
    if speed <= 0.001 {
        ms.max(10)
    } else {
        ((ms as f64) / speed).round().max(1.0) as u32
    }
}

fn filetime_to_i64(ft: FILETIME) -> i64 {
    ((ft.dwHighDateTime as i64) << 32) | (ft.dwLowDateTime as u32 as i64)
}

fn i64_to_filetime(val: i64) -> FILETIME {
    FILETIME {
        dwLowDateTime: val as u32,
        dwHighDateTime: (val >> 32) as u32,
    }
}

// --- 10 HOOK DETOURS ---

unsafe extern "system" fn hooked_qpc(lp_count: *mut i64) -> BOOL {
    type FnType = unsafe extern "system" fn(*mut i64) -> BOOL;
    let mut real_now = 0;
    // SAFETY: Valid trampoline from MinHook.
    let res = unsafe {
        let orig: FnType = std::mem::transmute(ORIG_QPC.load(Ordering::Relaxed) as *const c_void);
        orig(&mut real_now)
    };
    if res.as_bool() && !lp_count.is_null() {
        // SAFETY: Null-checked output pointer.
        unsafe { *lp_count = CLOCK_QPC.scale(real_now) };
    }
    res
}

unsafe extern "system" fn hooked_gtc64() -> u64 {
    type FnType = unsafe extern "system" fn() -> u64;
    // SAFETY: Valid trampoline from MinHook.
    let real_now = unsafe {
        let orig: FnType = std::mem::transmute(ORIG_GTC64.load(Ordering::Relaxed) as *const c_void);
        orig()
    };
    CLOCK_GTC64.scale(real_now as i64) as u64
}

unsafe extern "system" fn hooked_gtc32() -> u32 {
    type FnType = unsafe extern "system" fn() -> u32;
    // SAFETY: Valid trampoline from MinHook.
    let real_now = unsafe {
        let orig: FnType = std::mem::transmute(ORIG_GTC32.load(Ordering::Relaxed) as *const c_void);
        orig()
    };
    CLOCK_GTC32.scale(real_now as i64) as u32
}

unsafe extern "system" fn hooked_tgt() -> u32 {
    type FnType = unsafe extern "system" fn() -> u32;
    // SAFETY: Valid trampoline from MinHook.
    let real_now = unsafe {
        let orig: FnType = std::mem::transmute(ORIG_TGT.load(Ordering::Relaxed) as *const c_void);
        orig()
    };
    CLOCK_TGT.scale(real_now as i64) as u32
}

unsafe extern "system" fn hooked_ft(lp_ft: *mut FILETIME) {
    type FnType = unsafe extern "system" fn(*mut FILETIME);
    let mut real_ft = FILETIME::default();
    // SAFETY: Valid trampoline from MinHook.
    unsafe {
        let orig: FnType = std::mem::transmute(ORIG_FT.load(Ordering::Relaxed) as *const c_void);
        orig(&mut real_ft);
    }
    if !lp_ft.is_null() {
        let scaled = CLOCK_FILETIME.scale(filetime_to_i64(real_ft));
        // SAFETY: Null-checked output pointer.
        unsafe { *lp_ft = i64_to_filetime(scaled) };
    }
}

unsafe extern "system" fn hooked_precise_ft(lp_ft: *mut FILETIME) {
    type FnType = unsafe extern "system" fn(*mut FILETIME);
    let mut real_ft = FILETIME::default();
    // SAFETY: Valid trampoline from MinHook.
    unsafe {
        let orig: FnType =
            std::mem::transmute(ORIG_PRECISE_FT.load(Ordering::Relaxed) as *const c_void);
        orig(&mut real_ft);
    }
    if !lp_ft.is_null() {
        let scaled = CLOCK_PRECISE_FT.scale(filetime_to_i64(real_ft));
        // SAFETY: Null-checked output pointer.
        unsafe { *lp_ft = i64_to_filetime(scaled) };
    }
}

unsafe extern "system" fn hooked_sleep(dw_milliseconds: u32) {
    type FnType = unsafe extern "system" fn(u32);
    let scaled_ms = scale_duration_ms(dw_milliseconds);
    // SAFETY: Valid trampoline from MinHook.
    unsafe {
        let orig: FnType = std::mem::transmute(ORIG_SLEEP.load(Ordering::Relaxed) as *const c_void);
        orig(scaled_ms);
    }
}

unsafe extern "system" fn hooked_set_timer(
    hwnd: HWND,
    nid_event: usize,
    u_elapse: u32,
    lp_timer_func: TIMERPROC,
) -> usize {
    type FnType = unsafe extern "system" fn(HWND, usize, u32, TIMERPROC) -> usize;
    let scaled_elapse = scale_duration_ms(u_elapse);
    // SAFETY: Valid trampoline from MinHook.
    unsafe {
        let orig: FnType =
            std::mem::transmute(ORIG_SET_TIMER.load(Ordering::Relaxed) as *const c_void);
        orig(hwnd, nid_event, scaled_elapse, lp_timer_func)
    }
}

unsafe extern "system" fn hooked_wait_timer(
    htimer: HANDLE,
    lp_due_time: *const i64,
    l_period: i32,
    pfn_completion: PTIMERAPCROUTINE,
    lp_arg: *const c_void,
    f_resume: BOOL,
) -> BOOL {
    type FnType = unsafe extern "system" fn(
        HANDLE,
        *const i64,
        i32,
        PTIMERAPCROUTINE,
        *const c_void,
        BOOL,
    ) -> BOOL;

    let speed = read_target_speed().max(0.001);
    let scaled_due: i64;
    let due_ptr = if !lp_due_time.is_null() {
        // SAFETY: Null-checked pointer. Negative due times represent relative intervals.
        let raw_due = unsafe { *lp_due_time };
        scaled_due = if raw_due < 0 {
            ((raw_due as f64) / speed) as i64
        } else {
            raw_due
        };
        &scaled_due as *const i64
    } else {
        std::ptr::null()
    };

    let scaled_period = if l_period > 0 {
        ((l_period as f64) / speed).round().max(1.0) as i32
    } else {
        l_period
    };

    // SAFETY: Valid trampoline from MinHook.
    unsafe {
        let orig: FnType =
            std::mem::transmute(ORIG_WAIT_TIMER.load(Ordering::Relaxed) as *const c_void);
        orig(htimer, due_ptr, scaled_period, pfn_completion, lp_arg, f_resume)
    }
}

unsafe extern "system" fn hooked_wait_timer_ex(
    htimer: HANDLE,
    lp_due_time: *const i64,
    l_period: i32,
    pfn_completion: PTIMERAPCROUTINE,
    lp_arg: *const c_void,
    wake_context: *const REASON_CONTEXT,
    ul_tolerable_delay: u32,
) -> BOOL {
    type FnType = unsafe extern "system" fn(
        HANDLE,
        *const i64,
        i32,
        PTIMERAPCROUTINE,
        *const c_void,
        *const REASON_CONTEXT,
        u32,
    ) -> BOOL;

    let speed = read_target_speed().max(0.001);
    let scaled_due: i64;
    let due_ptr = if !lp_due_time.is_null() {
        // SAFETY: Null-checked pointer.
        let raw_due = unsafe { *lp_due_time };
        scaled_due = if raw_due < 0 {
            ((raw_due as f64) / speed) as i64
        } else {
            raw_due
        };
        &scaled_due as *const i64
    } else {
        std::ptr::null()
    };

    let scaled_period = if l_period > 0 {
        ((l_period as f64) / speed).round().max(1.0) as i32
    } else {
        l_period
    };

    // SAFETY: Valid trampoline from MinHook.
    unsafe {
        let orig: FnType =
            std::mem::transmute(ORIG_WAIT_TIMER_EX.load(Ordering::Relaxed) as *const c_void);
        orig(
            htimer,
            due_ptr,
            scaled_period,
            pfn_completion,
            lp_arg,
            wake_context,
            ul_tolerable_delay,
        )
    }
}

// --- ISOLATED HOOK REGISTRATION ---

fn hook_export(module: PCWSTR, proc_name: PCSTR, detour: *mut c_void, slot: &AtomicU64) {
    // SAFETY: Resolves exported Win32 symbol and registers a MinHook trampoline.
    unsafe {
        let h_mod = GetModuleHandleW(module).or_else(|_| LoadLibraryW(module));
        if let Ok(h_mod) = h_mod {
            if let Some(target) = GetProcAddress(h_mod, proc_name) {
                if let Ok(trampoline) = MinHook::create_hook(target as *mut c_void, detour) {
                    slot.store(trampoline as u64, Ordering::Relaxed);
                }
            }
        }
    }
}

fn setup_speedhack() -> Result<(), Box<dyn std::error::Error>> {
    // Force linker to retain import symbols for crates
    let _ = (
        QueryPerformanceCounter as usize,
        GetTickCount64 as usize,
        GetTickCount as usize,
        timeGetTime as usize,
        GetSystemTimeAsFileTime as usize,
        GetSystemTimePreciseAsFileTime as usize,
        Sleep as usize,
        SetTimer as usize,
        SetWaitableTimer as usize,
        SetWaitableTimerEx as usize,
    );

    let size = std::mem::size_of::<SharedState>();
    // SAFETY: Maps shared memory created by UI or creates it if DLL loaded first.
    let view = unsafe {
        let h_map = CreateFileMappingW(
            INVALID_HANDLE_VALUE,
            None,
            PAGE_READWRITE,
            0,
            size as u32,
            w!("Local\\SpeedDaemonMem"),
        )?;
        MapViewOfFile(h_map, FILE_MAP_ALL_ACCESS, 0, 0, size)
    };
    if !view.Value.is_null() {
        SHARED_PTR.store(view.Value as u64, Ordering::Relaxed);
    }

    let k32 = w!("kernel32.dll");
    let u32_dll = w!("user32.dll");
    let winmm = w!("winmm.dll");

    hook_export(k32, s!("QueryPerformanceCounter"), hooked_qpc as *mut c_void, &ORIG_QPC);
    hook_export(k32, s!("GetTickCount64"), hooked_gtc64 as *mut c_void, &ORIG_GTC64);
    hook_export(k32, s!("GetTickCount"), hooked_gtc32 as *mut c_void, &ORIG_GTC32);
    hook_export(winmm, s!("timeGetTime"), hooked_tgt as *mut c_void, &ORIG_TGT);
    hook_export(k32, s!("GetSystemTimeAsFileTime"), hooked_ft as *mut c_void, &ORIG_FT);
    hook_export(
        k32,
        s!("GetSystemTimePreciseAsFileTime"),
        hooked_precise_ft as *mut c_void,
        &ORIG_PRECISE_FT,
    );
    hook_export(k32, s!("Sleep"), hooked_sleep as *mut c_void, &ORIG_SLEEP);
    hook_export(u32_dll, s!("SetTimer"), hooked_set_timer as *mut c_void, &ORIG_SET_TIMER);
    hook_export(k32, s!("SetWaitableTimer"), hooked_wait_timer as *mut c_void, &ORIG_WAIT_TIMER);
    hook_export(
        k32,
        s!("SetWaitableTimerEx"),
        hooked_wait_timer_ex as *mut c_void,
        &ORIG_WAIT_TIMER_EX,
    );

    // SAFETY: Enables all registered MinHook detours atomically.
    unsafe {
        MinHook::enable_all_hooks().map_err(|e| format!("MinHook enable failed: {e:?}"))?;
    }
    Ok(())
}

#[unsafe(no_mangle)]
#[allow(non_snake_case)]
pub unsafe extern "system" fn DllMain(
    _hinst_dll: HINSTANCE,
    fdw_reason: u32,
    _lpv_reserved: *mut c_void,
) -> BOOL {
    match fdw_reason {
        DLL_PROCESS_ATTACH => {
            let _ = setup_speedhack();
        }
        DLL_PROCESS_DETACH => {
            // SAFETY: Unhooks all functions cleanly when unloaded.
            unsafe {
                let _ = MinHook::disable_all_hooks();
            }
        }
        _ => {}
    }
    BOOL(1)
}
