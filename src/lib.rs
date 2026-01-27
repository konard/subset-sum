//! Subset Sum Algorithm Library
//!
//! This library provides multiple implementations of the subset sum problem,
//! a classic NP-complete problem in computer science.
//!
//! # The Problem
//!
//! Given a set of natural numbers and a target sum, determine if there exists
//! a subset that adds up to exactly the target sum.
//!
//! # Algorithms
//!
//! - **Smart Brute Force**: O(2^n) optimized - with power-of-two detection (by konard)
//! - **Brute Force**: O(2^n) - tries all possible subsets
//! - **Backtracking**: O(2^n) worst case - recursive with early termination
//! - **Backtracking Pruned**: O(2^n) worst case - with sum-based pruning
//! - **Dynamic Programming**: O(n * target) - pseudo-polynomial time
//! - **Incremental Pruning**: O(2^n) worst case - level-wise subset construction with pruning
//! - **Meet in the Middle**: O(2^(n/2)) - splits array, uses binary search
//! - **Meet in the Middle (Hash)**: O(2^(n/2)) - uses hash set for lookup
//! - **Branch and Bound**: O(2^n) worst case - intelligent pruning
//! - **Randomized**: O(2^n) expected - random order exploration
//!
//! # Example
//!
//! ```
//! use subset_sum::{brute_force, AlgorithmResult};
//!
//! let numbers = vec![3, 7, 1, 8, 4];
//! let target = 15;
//!
//! let result = brute_force(&numbers, target, false);
//! assert!(result.solution.is_some());
//! ```

mod algorithms;

pub use algorithms::{
    backtracking, backtracking_pruned, branch_and_bound, brute_force, dynamic_programming,
    incremental_pruning, meet_in_middle, meet_in_middle_hash, randomized, smart_brute_force,
};

/// Library version from Cargo.toml.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Result of a subset sum algorithm execution.
#[derive(Debug, Clone)]
pub struct AlgorithmResult {
    /// The subset that sums to target, if found.
    pub solution: Option<Vec<u64>>,
    /// Number of computational steps taken.
    pub steps: u64,
}

impl AlgorithmResult {
    /// Creates a new `AlgorithmResult`.
    #[must_use]
    pub const fn new(solution: Option<Vec<u64>>, steps: u64) -> Self {
        Self { solution, steps }
    }
}

/// Macro for verbose logging.
#[macro_export]
macro_rules! verbose_log {
    ($verbose:expr, $($arg:tt)*) => {
        if $verbose {
            println!($($arg)*);
        }
    };
}

// ============================================================================
// VERIFICATION
// ============================================================================

/// Verifies that a solution is correct.
///
/// # Arguments
///
/// * `numbers` - Original set of numbers
/// * `target` - Target sum
/// * `subset` - Proposed solution subset
///
/// # Returns
///
/// `true` if the subset sums to target and all elements are from numbers
#[must_use]
pub fn verify_solution(numbers: &[u64], target: u64, subset: &[u64]) -> bool {
    // Check that all elements in subset are in numbers
    let mut available: Vec<u64> = numbers.to_vec();
    for &x in subset {
        if let Some(pos) = available.iter().position(|&n| n == x) {
            available.remove(pos);
        } else {
            return false;
        }
    }

    // Check that sum equals target
    subset.iter().sum::<u64>() == target
}

/// All available algorithm names.
pub const ALGORITHM_NAMES: [&str; 10] = [
    "smart_brute_force",
    "brute_force",
    "backtracking",
    "backtracking_pruned",
    "dynamic_programming",
    "incremental_pruning",
    "meet_in_middle",
    "meet_in_middle_hash",
    "branch_and_bound",
    "randomized",
];

/// Runs a specific algorithm by name.
///
/// # Arguments
///
/// * `name` - Algorithm name (one of `ALGORITHM_NAMES`)
/// * `numbers` - Input numbers
/// * `target` - Target sum
/// * `verbose` - Enable verbose logging
///
/// # Returns
///
/// `Some(AlgorithmResult)` if algorithm name is valid, `None` otherwise
#[must_use]
pub fn run_algorithm(
    name: &str,
    numbers: &[u64],
    target: u64,
    verbose: bool,
) -> Option<AlgorithmResult> {
    match name {
        "smart_brute_force" => Some(smart_brute_force(numbers, target, verbose)),
        "brute_force" => Some(brute_force(numbers, target, verbose)),
        "backtracking" => Some(backtracking(numbers, target, verbose)),
        "backtracking_pruned" => Some(backtracking_pruned(numbers, target, verbose)),
        "dynamic_programming" => Some(dynamic_programming(numbers, target, verbose)),
        "incremental_pruning" => Some(incremental_pruning(numbers, target, verbose)),
        "meet_in_middle" => Some(meet_in_middle(numbers, target, verbose)),
        "meet_in_middle_hash" => Some(meet_in_middle_hash(numbers, target, verbose)),
        "branch_and_bound" => Some(branch_and_bound(numbers, target, verbose)),
        "randomized" => Some(randomized(numbers, target, verbose, 12345)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_algorithm<F>(algo: F, name: &str)
    where
        F: Fn(&[u64], u64, bool) -> AlgorithmResult,
    {
        // Test 1: Simple case with solution
        let numbers = vec![3, 7, 1, 8, 4];
        let target = 15;
        let result = algo(&numbers, target, false);
        assert!(
            result.solution.is_some(),
            "{}: Should find solution for target 15",
            name
        );
        assert!(
            verify_solution(&numbers, target, result.solution.as_ref().unwrap()),
            "{}: Solution should be valid",
            name
        );

        // Test 2: No solution exists
        let numbers = vec![2, 4, 6, 8];
        let target = 1;
        let result = algo(&numbers, target, false);
        assert!(
            result.solution.is_none(),
            "{}: Should not find solution for target 1",
            name
        );

        // Test 3: Target is zero (empty subset)
        let numbers = vec![1, 2, 3];
        let target = 0;
        let result = algo(&numbers, target, false);
        assert!(
            result.solution.is_some(),
            "{}: Should find empty subset for target 0",
            name
        );
        assert!(
            result.solution.as_ref().unwrap().is_empty()
                || result.solution.as_ref().unwrap().iter().sum::<u64>() == 0,
            "{}: Solution for target 0 should be empty or sum to 0",
            name
        );

        // Test 4: Single element equals target
        let numbers = vec![5];
        let target = 5;
        let result = algo(&numbers, target, false);
        assert!(
            result.solution.is_some(),
            "{}: Should find single element solution",
            name
        );

        // Test 5: Multiple elements sum to target
        let numbers = vec![1, 2, 3, 4, 5];
        let target = 10;
        let result = algo(&numbers, target, false);
        assert!(
            result.solution.is_some(),
            "{}: Should find solution for target 10",
            name
        );
        assert!(
            verify_solution(&numbers, target, result.solution.as_ref().unwrap()),
            "{}: Solution should be valid for target 10",
            name
        );
    }

    #[test]
    fn test_smart_brute_force() {
        test_algorithm(smart_brute_force, "smart_brute_force");
    }

    #[test]
    fn test_smart_brute_force_power_of_two() {
        // Test power of two optimization
        let numbers = vec![1, 2, 4, 8, 16, 32];
        let target = 21; // 1 + 4 + 16 = 21
        let result = smart_brute_force(&numbers, target, false);
        assert!(result.solution.is_some());
        assert!(verify_solution(
            &numbers,
            target,
            result.solution.as_ref().unwrap()
        ));
    }

    #[test]
    fn test_brute_force() {
        test_algorithm(brute_force, "brute_force");
    }

    #[test]
    fn test_backtracking() {
        test_algorithm(backtracking, "backtracking");
    }

    #[test]
    fn test_backtracking_pruned() {
        test_algorithm(backtracking_pruned, "backtracking_pruned");
    }

    #[test]
    fn test_dynamic_programming() {
        test_algorithm(dynamic_programming, "dynamic_programming");
    }

    #[test]
    fn test_meet_in_middle() {
        test_algorithm(meet_in_middle, "meet_in_middle");
    }

    #[test]
    fn test_meet_in_middle_hash() {
        test_algorithm(meet_in_middle_hash, "meet_in_middle_hash");
    }

    #[test]
    fn test_branch_and_bound() {
        test_algorithm(branch_and_bound, "branch_and_bound");
    }

    #[test]
    fn test_incremental_pruning() {
        test_algorithm(incremental_pruning, "incremental_pruning");
    }

    #[test]
    fn test_randomized() {
        let algo = |numbers: &[u64], target: u64, verbose: bool| {
            randomized(numbers, target, verbose, 12345)
        };
        test_algorithm(algo, "randomized");
    }

    #[test]
    fn test_verify_solution() {
        // Valid solution
        assert!(verify_solution(&[1, 2, 3, 4], 6, &[2, 4]));

        // Invalid: wrong sum
        assert!(!verify_solution(&[1, 2, 3, 4], 6, &[1, 2]));

        // Invalid: element not in numbers
        assert!(!verify_solution(&[1, 2, 3, 4], 10, &[5, 5]));

        // Empty subset, target 0
        assert!(verify_solution(&[1, 2, 3], 0, &[]));
    }

    #[test]
    fn test_run_algorithm() {
        let numbers = vec![3, 7, 1, 8, 4];
        let target = 15;

        for name in ALGORITHM_NAMES {
            let result = run_algorithm(name, &numbers, target, false);
            assert!(result.is_some(), "Algorithm {} should exist", name);
            let result = result.unwrap();
            assert!(
                result.solution.is_some(),
                "Algorithm {} should find solution",
                name
            );
        }

        // Invalid algorithm name
        assert!(run_algorithm("invalid", &numbers, target, false).is_none());
    }

    #[test]
    fn test_steps_counted() {
        let numbers = vec![1, 2, 3, 4, 5];
        let target = 100; // impossible

        // All algorithms should count steps
        let result = brute_force(&numbers, target, false);
        assert!(result.steps > 0, "Brute force should count steps");

        let result = backtracking(&numbers, target, false);
        assert!(result.steps > 0, "Backtracking should count steps");

        let result = dynamic_programming(&numbers, target, false);
        assert!(result.steps > 0, "DP should count steps");
    }

    #[test]
    fn test_larger_input() {
        // Test with moderately larger input (n=15)
        let numbers: Vec<u64> = (1..=15).collect();
        let target = 50;

        for name in ALGORITHM_NAMES {
            let result = run_algorithm(name, &numbers, target, false);
            assert!(result.is_some());
            let result = result.unwrap();
            assert!(
                result.solution.is_some(),
                "Algorithm {} should find solution for n=15",
                name
            );
            assert!(
                verify_solution(&numbers, target, result.solution.as_ref().unwrap()),
                "Algorithm {} should produce valid solution for n=15",
                name
            );
        }
    }
}
