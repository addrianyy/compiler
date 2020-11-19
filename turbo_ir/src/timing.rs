use std::sync::atomic::{AtomicU64, AtomicBool, Ordering};
use std::time::{Instant, Duration};
use std::convert::TryInto;
use std::cell::RefCell;

type AtomicTime = AtomicU64;
type Time       = u64;

struct TimingEntry {
    name:       &'static str,
    total_time: AtomicTime,
    exact_time: AtomicTime,
}

struct CollectedTimingEntry {
    name:       &'static str,
    total_time: f64,
    exact_time: f64,
}

pub struct TimedBlock {
    entry: &'static TimingEntry,
    start: Instant,
}

thread_local! {
    static TIME_STACK: RefCell<Vec<Time>> = RefCell::new(Vec::with_capacity(8));
}

fn time_from_duration(duration: Duration) -> Time {
    duration.as_micros().try_into().expect("Operation took too long and amount of elapsed \
                                            microseconds don't fit in 64 bit integer.")
}

fn time_to_seconds(time: Time) -> f64 {
    time as f64 / 1_000_000.0
}

impl Drop for TimedBlock {
    fn drop(&mut self) {
        let elapsed = time_from_duration(self.start.elapsed());
        let inside  = TIME_STACK.with(|stack| {
            let mut stack = stack.borrow_mut();

            let inside = stack.pop()
                .expect("Timing stack was corrupted.");

            if !stack.is_empty() {
                let top = stack.len() - 1;

                stack[top] += elapsed;
            }

            inside
        });

        assert!(elapsed >= inside, "Full time is smaller than exact time.");

        self.entry.total_time.fetch_add(elapsed, Ordering::Relaxed);
        self.entry.exact_time.fetch_add(elapsed - inside, Ordering::Relaxed);
    }
}

macro_rules! timing {
    ($($name: ident),*) => {
        struct Timing {
            $(
                $name: TimingEntry,
            )*
        }

        impl Timing {
            const fn new() -> Self {
                Self {
                    $(
                        $name: TimingEntry {
                            name:       stringify!($name),
                            total_time: AtomicTime::new(0),
                            exact_time: AtomicTime::new(0),
                        },
                    )*
                }
            }
        }

        static GLOBAL_TIMING: Timing = Timing::new();

        $(
            pub fn $name() -> TimedBlock {
                TIME_STACK.with(|stack| {
                    stack.borrow_mut().push(0);
                });

                TimedBlock {
                    entry: &GLOBAL_TIMING.$name,
                    start: Instant::now(),
                }
            }
        )*

        fn collect_timings() -> Vec<CollectedTimingEntry> {
            let mut collected = Vec::new();

            $(
                {
                    let entry      = &GLOBAL_TIMING.$name;
                    let total_time = time_to_seconds(entry.total_time.load(Ordering::Relaxed));
                    let exact_time = time_to_seconds(entry.exact_time.load(Ordering::Relaxed));

                    collected.push(CollectedTimingEntry {
                        name: entry.name,
                        total_time,
                        exact_time,
                    });
                }
            )*

            collected
        }
    }
}

macro_rules! time {
    ($name: ident) => {
        let _time = crate::timing::$name();
    }
}

timing!(value_processing_order, pointer_users, users, phi_used_values, find_stackallocs,
        find_uses, value_creators, usage_counts, validate_ssa, validate_path, dominates, 
        validate_path_complex, validate_blocks, escaping_cycle_blocks,
        escaping_cycle_blocks_internal, can_reach, constant_values, replace_phi_incoming,
        depends_on_predecessors, analyse_pointers, safe_pointers, get_pointer_origin,
        can_call_access_pointer, can_alias, block_contains_phi, finalize, codegen_cleanup,
        optimize, default_passes, rewrite_values, add_value_usage, value_dies, uniquely_map_rest,
        pick_color, unique_edges, coloring_order, color, liveness, interference_graph,
        coalesce_values, map_virtual_registers, rewrite_phis, rewrite_arguments,
        constants_and_skips, allocate_registers, generate_function, generate_function_body,
        traverse_dfs_postorder, dominators, for_each_label_bfs, flow_graph_outgoing,
        flow_graph_incoming, reachable_labels_dfs, fvs_new, processing_order_presolve,
        input_parameters);

pub fn show_timings() {
    let mut timings  = collect_timings();
    let total        = timings.iter().fold(0.0, |value, x| value + x.exact_time);
    let longest_name = timings.iter().fold(0,   |value, x| value.max(x.name.len()));
    
    timings.sort_by(|a, b| b.exact_time.partial_cmp(&a.exact_time).unwrap());

    for timing in timings {
        print!("{}", timing.name);

        for _ in 0..(longest_name - timing.name.len()) {
            print!(" ");
        }

        println!(" | exact {:>3.5} [{:0>1.2}] | total {:>3.5} [{:0>1.2}]",
                 timing.exact_time, timing.exact_time / total,
                 timing.total_time, timing.total_time / total);
    }
}

pub fn register_exit_callback() {
    static REGISTERED_CALLBACK: AtomicBool = AtomicBool::new(false);

    extern "C" {
        fn atexit(cb: extern "C" fn()) -> i32;
    }

    extern "C" fn callback() {
        show_timings();
    }

    if !REGISTERED_CALLBACK.compare_and_swap(false, true, Ordering::Relaxed) {
        unsafe {
            assert_eq!(atexit(callback), 0, "Failed to set `atexit` callback.");
        }
    }
}
