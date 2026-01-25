use std::time::Instant;
use rand::Rng;
use itertools::Itertools;

// ============================================================================
// 1. BRUTE FORCE - O(2^n)
// Try all possible subsets using bitmask
// ============================================================================
fn brute_force(numbers: &[u64], target: u64) -> (Option<Vec<u64>>, u64) {
    let n = numbers.len();
    let mut steps: u64 = 0;

    for mask in 0..(1u64 << n) {
        steps += 1;

        let mut sum = 0;
        let mut subset = Vec::new();

        for i in 0..n {
            if mask & (1 << i) != 0 {
                sum += numbers[i];
                subset.push(numbers[i]);
            }
        }

        if sum == target {
            return (Some(subset), steps);
        }
    }

    (None, steps)
}


fn smart_brute_force(numbers: &[u64], target: u64) -> (Option<Vec<u64>>, u64) {
    let mut sorted_numbers = numbers
            .iter()
            .cloned()
            // filter out numbers greater than target and lower than 1 (only natural numbers)
            .filter(|&x| x >= 1 && x <= target)
            .sorted()
            .collect::<Vec<u64>>();

    let n = sorted_numbers.len();

    let total_sum: u64 = sorted_numbers.iter().sum();

    let min = sorted_numbers[0];
    let max = sorted_numbers[n - 1];

    println!("Filtered and sorted numbers: {:?}", sorted_numbers);
    println!("Minimum number: {}", min);
    println!("Maximum number: {}", max);
    println!("Total sum of numbers: {}", total_sum);

    if (max == target) {
        return (Some(vec![max]), 1);
    }
    if target < min || target > total_sum {
        return (None, 0);
    }

    let mut existing_powers_of_two: u64 = 0;
    for &number in &sorted_numbers {
        if number.is_power_of_two() {
            existing_powers_of_two |= 1 << number.trailing_zeros();
        }
    }

    println!("Existing powers of two (binary): {:064b}", existing_powers_of_two);

    let missing_powers_of_two = existing_powers_of_two ^ 0xFFFFFFFFFFFFFFFF;

    println!("Missing powers of two (binary): {:064b}", missing_powers_of_two);

    let powers_of_to_missing_for_target = missing_powers_of_two & target;

    println!("Powers of two missing for target (binary): {:064b}", powers_of_to_missing_for_target);

    if (powers_of_to_missing_for_target == 0) {
        // build our target using available power of two
        let mut sum = 0;
        let mut subset = Vec::new();

        for i in 0..64 {
            if target & (1 << i) != 0 {
                // we need this power of two
                if existing_powers_of_two & (1 << i) != 0 {
                    // we have it
                    let power_of_two = 1u64 << i;
                    sum += power_of_two;
                    subset.push(power_of_two);
                }
            }
        }
        return (Some(subset), 0);
    }

    let mut steps: u64 = 0;

    for mask in 0..(1u64 << n) {
        steps += 1;

        let mut sum = 0;
        let mut subset = Vec::new();

        for i in 0..n {
            if mask & (1 << i) != 0 {
                sum += sorted_numbers[i];
                subset.push(sorted_numbers[i]);
            }
        }

        if sum == target {
            return (Some(subset), steps);
        }
    }

    (None, steps)
}

// ============================================================================
// VERIFICATION
// ============================================================================
fn verify(numbers: &[u64], target: u64, subset: &[u64]) -> bool {
    let mut available = numbers.to_vec();
    for &x in subset {
        if let Some(pos) = available.iter().position(|&n| n == x) {
            available.remove(pos);
        } else {
            return false;
        }
    }
    subset.iter().sum::<u64>() == target
}

// ============================================================================
// BENCHMARKING
// ============================================================================
fn run_benchmark<F>(name: &str, f: F, numbers: &[u64], target: u64) -> (bool, u64, u128)
where
    F: Fn(&[u64], u64) -> (Option<Vec<u64>>, u64),
{
    let start = Instant::now();
    let (result, steps) = f(numbers, target);
    let elapsed = start.elapsed().as_micros();

    let valid = match &result {
        Some(subset) => verify(numbers, target, subset),
        None => true, // no solution found, can't verify
    };

    println!(
        "  {:<25} {:>12} steps  {:>10} µs  {}",
        name,
        steps,
        elapsed,
        if result.is_some() { "FOUND" } else { "NOT FOUND" }
    );

    if result.is_some() && valid{
        // print binary representation of the subset
        let subset = result.unwrap();
        println!("    Subset:");
        for &num in &subset {
            println!("      {:08b} ({})", num, num);
        }
    }

    (valid, steps, elapsed)
}

fn make_random_number(max_value: u64) -> u64 {
    let mut rng = rand::thread_rng();
    rng.gen_range(1..=max_value)
}

fn make_unique_random_numbers(n: usize, max_value: u64) -> Vec<u64> {
    let mut numbers = std::collections::HashSet::new();
    while numbers.len() < n {
        numbers.insert(make_random_number(max_value));
    }
    numbers.into_iter().collect()
}

fn main() {
    println!("╔══════════════════════════════════════════════════════════════════╗");
    println!("║           SUBSET SUM ALGORITHM COMPARISON                        ║");
    println!("╚══════════════════════════════════════════════════════════════════╝\n");

    // Test 1: Small example with solution
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("TEST 1: Small example (n=10, has solution)");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    // let numbers_original = vec![3, 7, 1, 8, 4, 12, 5, 6, 9, 2];
    let numbers_original = make_unique_random_numbers(200, 200);
    let mut numbers_sorted = numbers_original.clone();
    numbers_sorted.sort();
    let target = make_random_number(200);
    println!("Numbers: {:?}", numbers_sorted);

    for &number in &numbers_sorted {
        println!("  Number (binary): {:08b}", number);
    }

    println!("Target: {}\n", target);
    println!("Target (binary): {:08b}", target);

    run_benchmark("Brute Force", smart_brute_force, &numbers_sorted, target);

    // Test 2: Medium, no solution (worst case)
    println!("\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("TEST 2: No solution - worst case (n=20)");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    let numbers: Vec<u64> = (1..=20).collect();
    let target = numbers.iter().sum::<u64>() + 1; // impossible
    println!("Numbers: 1..=20");

    for &number in &numbers {
        println!("  Number (binary): {:08b}", number);
    }

    let total_sum: u64 = numbers.iter().sum();
    println!("Total Sum: {} (binary: {:08b})", total_sum, total_sum);

    println!("Target: {} (impossible)\n", target);
    println!("Target (binary): {:08b}", target);

    run_benchmark("Brute Force", smart_brute_force, &numbers, target);

    // Complexity comparison table
    println!("\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("ALGORITHM COMPLEXITY SUMMARY");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("  {:<25} {:<20} {:<20}", "Algorithm", "Time", "Space");
    println!("  {:-<25} {:-<20} {:-<20}", "", "", "");
    println!("  {:<25} {:<20} {:<20}", "Brute Force",           "O(2^n)",             "O(n)");
    println!("  {:<25} {:<20} {:<20}", "Backtracking",          "O(2^n)",             "O(n)");
    println!("  {:<25} {:<20} {:<20}", "Backtracking Pruned",   "O(2^n) worst",       "O(n)");
    println!("  {:<25} {:<20} {:<20}", "Dynamic Programming",   "O(n × target)",      "O(target)");
    println!("  {:<25} {:<20} {:<20}", "Meet in Middle",        "O(2^(n/2))",         "O(2^(n/2))");
    println!("  {:<25} {:<20} {:<20}", "Meet in Middle (Hash)", "O(2^(n/2))",         "O(2^(n/2))");
    println!("  {:<25} {:<20} {:<20}", "Branch and Bound",      "O(2^n) worst",       "O(n)");
    println!("  {:<25} {:<20} {:<20}", "Randomized",            "O(2^n) expected",    "O(2^n)");

    println!("\n━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("KEY INSIGHTS");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("• Meet in Middle: Best for moderate n (25-40), any target size");
    println!("• Dynamic Programming: Best when target value is small");
    println!("• Backtracking Pruned: Best for small targets with positive numbers");
    println!("• Branch and Bound: Good all-around with intelligent pruning");
    println!("• Brute Force: Only for n < 20");
    println!("• No polynomial solution exists (unless P = NP)");
}