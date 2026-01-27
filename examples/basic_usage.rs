//! Basic usage example for subset-sum.
//!
//! This example demonstrates how to use the subset sum algorithms.
//!
//! Run with: `cargo run --example basic_usage`

use subset_sum::{
    brute_force, dynamic_programming, meet_in_middle, run_algorithm, verify_solution, InputSet,
    ALGORITHM_NAMES, VERSION,
};

fn main() {
    println!("Subset Sum Library v{}", VERSION);
    println!("================================");
    println!();

    // Example 1: Simple subset sum with brute force
    println!("Example 1: Brute Force Algorithm");
    let input = InputSet::new(vec![3, 7, 1, 8, 4]).unwrap();
    let target = 15;
    println!("Numbers: {:?}", input.numbers());
    println!("Target sum: {}", target);

    let result = brute_force(&input, target, false);
    match &result.solution {
        Some(subset) => {
            println!("Found subset: {:?}", subset);
            println!("Sum: {}", subset.iter().sum::<u64>());
            println!(
                "Valid: {}",
                verify_solution(input.numbers(), target, subset)
            );
        }
        None => println!("No solution found"),
    }
    println!("Steps taken: {}", result.steps);
    println!();

    // Example 2: Dynamic Programming with larger target
    println!("Example 2: Dynamic Programming");
    let input = InputSet::new(vec![100, 200, 300, 400, 500]).unwrap();
    let target = 900;
    println!("Numbers: {:?}", input.numbers());
    println!("Target sum: {}", target);

    let result = dynamic_programming(&input, target, false);
    match &result.solution {
        Some(subset) => {
            println!("Found subset: {:?}", subset);
            println!(
                "Valid: {}",
                verify_solution(input.numbers(), target, subset)
            );
        }
        None => println!("No solution found"),
    }
    println!("Steps taken: {}", result.steps);
    println!();

    // Example 3: Meet in the Middle for larger input
    println!("Example 3: Meet in the Middle");
    let numbers: Vec<u64> = (1..=20).collect();
    let input = InputSet::new(numbers).unwrap();
    let target = 100;
    println!("Numbers: 1 to 20");
    println!("Target sum: {}", target);

    let result = meet_in_middle(&input, target, false);
    match &result.solution {
        Some(subset) => {
            println!("Found subset: {:?}", subset);
            println!(
                "Valid: {}",
                verify_solution(input.numbers(), target, subset)
            );
        }
        None => println!("No solution found"),
    }
    println!("Steps taken: {}", result.steps);
    println!();

    // Example 4: Using run_algorithm to select by name
    println!("Example 4: Running algorithm by name");
    println!("Available algorithms: {:?}", ALGORITHM_NAMES);
    let input = InputSet::new(vec![5, 10, 15, 20, 25]).unwrap();
    let target = 40;
    println!("Numbers: {:?}", input.numbers());
    println!("Target sum: {}", target);

    for algo_name in &["backtracking", "branch_and_bound"] {
        if let Some(result) = run_algorithm(algo_name, &input, target, false) {
            println!(
                "  {}: {} steps, found: {}",
                algo_name,
                result.steps,
                result.solution.is_some()
            );
        }
    }
    println!();

    // Example 5: Verbose mode demonstration
    println!("Example 5: Verbose mode (showing first few steps)");
    let input = InputSet::new(vec![1, 2, 3]).unwrap();
    let target = 4;
    println!("Numbers: {:?}", input.numbers());
    println!("Target sum: {}", target);
    println!("Running with verbose=true:");
    let _result = brute_force(&input, target, true);
    println!();

    // Example 6: InputSet validation (demonstrating duplicate rejection)
    println!("Example 6: Input validation");
    match InputSet::new(vec![1, 2, 2, 3]) {
        Ok(_) => println!("Unexpected: should have rejected duplicates"),
        Err(e) => println!("Correctly rejected invalid input: {}", e),
    }
    println!();

    println!("Done! For more options, use the CLI: subset-sum --help");
}
