//! Subset Sum CLI - Benchmarking tool for subset sum algorithms.
//!
//! This CLI allows you to run and benchmark different subset sum algorithms
//! with configurable input parameters.

use clap::{Parser, Subcommand};
use rand::seq::SliceRandom;
use rand::Rng;
use std::time::Instant;
use subset_sum::{run_algorithm, verify_solution, AlgorithmResult, ALGORITHM_NAMES};

/// Subset Sum Algorithm Benchmarking Tool
#[derive(Parser)]
#[command(name = "subset-sum")]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Run a single algorithm with specified parameters
    Run {
        /// Target sum to find (natural number > 0). If not provided, uses random 1-256.
        #[arg(short = 't', long)]
        target_sum: Option<u64>,

        /// Space-separated list of natural numbers (e.g., "3 7 1 8 4"). If not provided, generates random unique numbers.
        #[arg(short = 'n', long)]
        numbers_set: Option<String>,

        /// Algorithm to use
        #[arg(short = 'a', long, default_value = "brute_force")]
        algorithm: String,

        /// Enable verbose output showing each step
        #[arg(short = 'v', long, default_value_t = false)]
        verbose: bool,
    },

    /// Run all algorithms and compare performance
    Benchmark {
        /// Target sum to find (natural number > 0). If not provided, uses random 1-256.
        #[arg(short = 't', long)]
        target_sum: Option<u64>,

        /// Space-separated list of natural numbers (e.g., "3 7 1 8 4"). If not provided, generates random unique numbers.
        #[arg(short = 'n', long)]
        numbers_set: Option<String>,

        /// Enable verbose output
        #[arg(short = 'v', long, default_value_t = false)]
        verbose: bool,

        /// Algorithms to skip (comma-separated)
        #[arg(long, default_value = "")]
        skip: String,
    },

    /// List all available algorithms
    List,

    /// Run scaling test to demonstrate non-polynomial growth
    ScalingTest {
        /// Starting size of input array
        #[arg(long, default_value_t = 5)]
        start_size: usize,

        /// Ending size of input array
        #[arg(long, default_value_t = 20)]
        end_size: usize,

        /// Size increment
        #[arg(long, default_value_t = 1)]
        step: usize,

        /// Algorithm to test
        #[arg(short = 'a', long, default_value = "brute_force")]
        algorithm: String,

        /// Output format (table or csv)
        #[arg(long, default_value = "table")]
        format: String,
    },
}

fn parse_numbers(input: &str) -> Result<Vec<u64>, String> {
    let numbers: Result<Vec<u64>, _> = input
        .split_whitespace()
        .map(|s| {
            s.parse::<u64>().map_err(|_| {
                format!(
                    "Invalid number: '{}'. Must be a natural number (positive integer).",
                    s
                )
            })
        })
        .collect();

    let numbers = numbers?;

    // Validate all numbers are natural (> 0)
    for &n in &numbers {
        if n == 0 {
            return Err(
                "Zero is not allowed. All numbers must be natural numbers (positive integers)."
                    .to_string(),
            );
        }
    }

    if numbers.is_empty() {
        return Err("Numbers set cannot be empty.".to_string());
    }

    Ok(numbers)
}

fn validate_target(target: u64) -> Result<(), String> {
    if target == 0 {
        return Err(
            "Target sum must be a natural number (positive integer), not zero.".to_string(),
        );
    }
    Ok(())
}

/// Generates a random set of unique numbers.
/// Size: random 1-64, each number: random 1-64
fn generate_random_numbers() -> Vec<u64> {
    let mut rng = rand::thread_rng();
    let size = rng.gen_range(1..=64);

    // Create a pool of numbers 1-64 and shuffle to pick unique ones
    let mut pool: Vec<u64> = (1..=64).collect();
    pool.shuffle(&mut rng);

    // Take the first `size` numbers
    pool.into_iter().take(size).collect()
}

/// Generates a random target sum between 1 and 256.
fn generate_random_target() -> u64 {
    let mut rng = rand::thread_rng();
    rng.gen_range(1..=256)
}

fn run_single_algorithm(
    algorithm: &str,
    numbers: &[u64],
    target: u64,
    verbose: bool,
) -> Result<(), String> {
    if !ALGORITHM_NAMES.contains(&algorithm) {
        return Err(format!(
            "Unknown algorithm: '{}'. Use 'subset-sum list' to see available algorithms.",
            algorithm
        ));
    }

    println!("Running {} algorithm", algorithm);
    println!("Numbers: {:?}", numbers);
    println!("Target: {}", target);
    println!();

    let start = Instant::now();
    let result = run_algorithm(algorithm, numbers, target, verbose)
        .ok_or_else(|| format!("Failed to run algorithm: {}", algorithm))?;
    let elapsed = start.elapsed();

    print_result(&result, numbers, target, elapsed);
    Ok(())
}

fn print_result(
    result: &AlgorithmResult,
    numbers: &[u64],
    target: u64,
    elapsed: std::time::Duration,
) {
    match &result.solution {
        Some(subset) => {
            println!("FOUND subset: {:?}", subset);
            println!("Sum: {}", subset.iter().sum::<u64>());

            let valid = verify_solution(numbers, target, subset);
            println!("Valid: {}", if valid { "YES" } else { "NO" });
        }
        None => {
            println!("NOT FOUND - No subset sums to target");
        }
    }
    println!();
    println!("Steps: {}", result.steps);
    println!("Time: {} µs", elapsed.as_micros());
}

fn run_benchmark(numbers: &[u64], target: u64, verbose: bool, skip: &str) -> Result<(), String> {
    let skip_list: Vec<&str> = skip
        .split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect();

    println!("╔══════════════════════════════════════════════════════════════════╗");
    println!("║           SUBSET SUM ALGORITHM COMPARISON                        ║");
    println!("╚══════════════════════════════════════════════════════════════════╝");
    println!();
    println!("Numbers: {:?}", numbers);
    println!("Target: {}", target);
    println!("Input size (n): {}", numbers.len());
    println!();

    println!(
        "{:<25} {:>12} {:>12} {:>10}",
        "Algorithm", "Steps", "Time (µs)", "Result"
    );
    println!("{:-<25} {:->12} {:->12} {:->10}", "", "", "", "");

    for &algo in &ALGORITHM_NAMES {
        if skip_list.contains(&algo) {
            println!("{:<25} {:>12} {:>12} {:>10}", algo, "-", "-", "SKIPPED");
            continue;
        }

        let start = Instant::now();
        let result = run_algorithm(algo, numbers, target, verbose)
            .ok_or_else(|| format!("Failed to run algorithm: {}", algo))?;
        let elapsed = start.elapsed();

        let status = match &result.solution {
            Some(subset) => {
                if verify_solution(numbers, target, subset) {
                    "FOUND"
                } else {
                    "INVALID"
                }
            }
            None => "NOT FOUND",
        };

        println!(
            "{:<25} {:>12} {:>12} {:>10}",
            algo,
            result.steps,
            elapsed.as_micros(),
            status
        );
    }

    println!();
    print_complexity_summary();

    Ok(())
}

fn print_complexity_summary() {
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("ALGORITHM COMPLEXITY SUMMARY");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("{:<25} {:<20} {:<20}", "Algorithm", "Time", "Space");
    println!("{:-<25} {:-<20} {:-<20}", "", "", "");
    println!(
        "{:<25} {:<20} {:<20}",
        "smart_brute_force", "O(2^n) optimized", "O(n)"
    );
    println!("{:<25} {:<20} {:<20}", "brute_force", "O(2^n)", "O(n)");
    println!("{:<25} {:<20} {:<20}", "backtracking", "O(2^n)", "O(n)");
    println!(
        "{:<25} {:<20} {:<20}",
        "backtracking_pruned", "O(2^n) worst", "O(n)"
    );
    println!(
        "{:<25} {:<20} {:<20}",
        "dynamic_programming", "O(n × target)", "O(target)"
    );
    println!(
        "{:<25} {:<20} {:<20}",
        "meet_in_middle", "O(2^(n/2))", "O(2^(n/2))"
    );
    println!(
        "{:<25} {:<20} {:<20}",
        "meet_in_middle_hash", "O(2^(n/2))", "O(2^(n/2))"
    );
    println!(
        "{:<25} {:<20} {:<20}",
        "branch_and_bound", "O(2^n) worst", "O(n)"
    );
    println!(
        "{:<25} {:<20} {:<20}",
        "randomized", "O(2^n) expected", "O(2^n)"
    );
    println!();
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("KEY INSIGHTS");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("• Smart Brute Force: Optimized with power-of-two detection");
    println!("• Meet in Middle: Best for moderate n (25-40), any target size");
    println!("• Dynamic Programming: Best when target value is small");
    println!("• Backtracking Pruned: Best for small targets with positive numbers");
    println!("• Branch and Bound: Good all-around with intelligent pruning");
    println!("• Brute Force: Only for n < 20");
    println!("• No polynomial solution exists (unless P = NP)");
}

fn run_scaling_test(
    start_size: usize,
    end_size: usize,
    step: usize,
    algorithm: &str,
    format: &str,
) -> Result<(), String> {
    if !ALGORITHM_NAMES.contains(&algorithm) {
        return Err(format!(
            "Unknown algorithm: '{}'. Use 'subset-sum list' to see available algorithms.",
            algorithm
        ));
    }

    println!("Scaling Test for: {}", algorithm);
    println!("Testing exponential growth of computational steps");
    println!();

    if format == "csv" {
        println!("n,steps,time_us,2^n,ratio");
    } else {
        println!(
            "{:>5} {:>15} {:>12} {:>15} {:>10}",
            "n", "Steps", "Time (µs)", "2^n", "Ratio"
        );
        println!("{:->5} {:->15} {:->12} {:->15} {:->10}", "", "", "", "", "");
    }

    for n in (start_size..=end_size).step_by(step) {
        // Generate worst-case input: consecutive numbers, impossible target
        let numbers: Vec<u64> = (1..=n as u64).collect();
        let total_sum: u64 = numbers.iter().sum();
        let target = total_sum + 1; // Impossible target forces full search

        let start = Instant::now();
        let result = run_algorithm(algorithm, &numbers, target, false)
            .ok_or_else(|| format!("Failed to run algorithm: {}", algorithm))?;
        let elapsed = start.elapsed();

        let expected = 1u64 << n.min(63);
        let ratio = if expected > 0 {
            result.steps as f64 / expected as f64
        } else {
            0.0
        };

        if format == "csv" {
            println!(
                "{},{},{},{},{:.4}",
                n,
                result.steps,
                elapsed.as_micros(),
                expected,
                ratio
            );
        } else {
            println!(
                "{:>5} {:>15} {:>12} {:>15} {:>10.4}",
                n,
                result.steps,
                elapsed.as_micros(),
                expected,
                ratio
            );
        }
    }

    println!();
    println!("Note: Steps grow exponentially with n (2^n), demonstrating");
    println!("that the Subset Sum problem has no known polynomial-time solution.");
    println!("This is consistent with its NP-complete classification.");

    Ok(())
}

fn list_algorithms() {
    println!("Available algorithms:");
    println!();
    for algo in ALGORITHM_NAMES {
        println!("  • {}", algo);
    }
    println!();
    println!("Use --algorithm <name> to select an algorithm.");
}

fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        Commands::Run {
            target_sum,
            numbers_set,
            algorithm,
            verbose,
        } => {
            // Generate random values if not provided
            let numbers = match numbers_set {
                Some(ref ns) => match parse_numbers(ns) {
                    Ok(n) => n,
                    Err(e) => return print_error_and_exit(&e),
                },
                None => generate_random_numbers(),
            };
            let target = target_sum.unwrap_or_else(generate_random_target);

            if let Err(e) = validate_target(target) {
                return print_error_and_exit(&e);
            }
            run_single_algorithm(&algorithm, &numbers, target, verbose)
        }
        Commands::Benchmark {
            target_sum,
            numbers_set,
            verbose,
            skip,
        } => {
            // Generate random values if not provided
            let numbers = match numbers_set {
                Some(ref ns) => match parse_numbers(ns) {
                    Ok(n) => n,
                    Err(e) => return print_error_and_exit(&e),
                },
                None => generate_random_numbers(),
            };
            let target = target_sum.unwrap_or_else(generate_random_target);

            if let Err(e) = validate_target(target) {
                return print_error_and_exit(&e);
            }
            run_benchmark(&numbers, target, verbose, &skip)
        }
        Commands::List => {
            list_algorithms();
            Ok(())
        }
        Commands::ScalingTest {
            start_size,
            end_size,
            step,
            algorithm,
            format,
        } => run_scaling_test(start_size, end_size, step, &algorithm, &format),
    };

    if let Err(e) = result {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}

fn print_error_and_exit(e: &str) {
    eprintln!("Error: {}", e);
    std::process::exit(1);
}
