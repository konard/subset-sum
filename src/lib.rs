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
//! # Input Model
//!
//! The input is modeled as a **set** of natural numbers, not a multiset. This means:
//! - Each number must be unique (no duplicates allowed)
//! - Numbers are automatically sorted for algorithm optimization
//! - The [`InputSet`] struct provides immutable, preprocessed input with min/max/sum
//!
//! This design moves sorting and uniqueness verification outside of individual
//! algorithm implementations, ensuring fair benchmarking and consistent behavior.
//!
//! # Algorithms
//!
//! - **Smart Brute Force**: O(2^n) optimized - with power-of-two detection (by konard)
//! - **Brute Force**: O(2^n) - tries all possible subsets
//! - **Backtracking**: O(2^n) worst case - recursive with early termination
//! - **Backtracking Pruned**: O(2^n) worst case - with sum-based pruning
//! - **Dynamic Programming**: O(n * target) - pseudo-polynomial time
//! - **Incremental Pruning**: O(2^n) worst case - level-wise subset construction with pruning
//! - **Max-First Reduction**: O(2^n) worst case - recursively includes largest elements first
//! - **Meet in the Middle**: O(2^(n/2)) - splits array, uses binary search
//! - **Meet in the Middle (Hash)**: O(2^(n/2)) - uses hash set for lookup
//! - **Branch and Bound**: O(2^n) worst case - intelligent pruning
//! - **Randomized**: O(2^n) expected - random order exploration
//!
//! # Example
//!
//! ```
//! use subset_sum::{InputSet, brute_force, AlgorithmResult};
//!
//! // Create an InputSet from numbers (validates uniqueness and sorts)
//! let input = InputSet::new(vec![3, 7, 1, 8, 4]).unwrap();
//! let target = 15;
//!
//! let result = brute_force(&input, target, false);
//! assert!(result.solution.is_some());
//! ```

mod algorithms;

pub use algorithms::{
    backtracking, backtracking_pruned, branch_and_bound, brute_force, dynamic_programming,
    incremental_pruning, max_first_reduction, meet_in_middle, meet_in_middle_hash, randomized,
    smart_brute_force,
};

// Re-export InputSet and InputSetError for public API
// (They are defined in this file, so no need to re-export, just documenting they're public)

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

// ============================================================================
// INPUT SET - Preprocessed, validated input for subset sum algorithms
// ============================================================================

/// Error type for `InputSet` creation failures.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InputSetError {
    /// The input contains duplicate values.
    DuplicateValues(Vec<u64>),
    /// The input is empty.
    EmptyInput,
    /// The input contains zero, which is not a natural number.
    ContainsZero,
}

impl std::fmt::Display for InputSetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateValues(dups) => {
                write!(
                    f,
                    "Input contains duplicate values: {:?}. The subset sum problem operates on sets, not multisets. Each number must be unique.",
                    dups
                )
            }
            Self::EmptyInput => {
                write!(f, "Input set cannot be empty.")
            }
            Self::ContainsZero => {
                write!(
                    f,
                    "Input contains zero. All numbers must be natural numbers (positive integers)."
                )
            }
        }
    }
}

impl std::error::Error for InputSetError {}

/// A preprocessed, immutable input set for subset sum algorithms.
///
/// This struct ensures that input is:
/// - Non-empty
/// - Contains only natural numbers (positive integers, no zeros)
/// - Contains only unique values (no duplicates)
/// - Sorted in ascending order
///
/// It also precomputes useful values like `min`, `max`, and `total_sum`
/// to enable algorithm optimizations without redundant computation.
///
/// # Why `InputSet`?
///
/// The subset sum problem is defined on **sets** of numbers, not multisets.
/// A sorted sequence with unique elements is mathematically equivalent to a set.
/// By validating and preprocessing input once, we:
///
/// 1. **Ensure correctness**: Duplicate values would make the problem ill-defined
/// 2. **Enable fair benchmarking**: Sorting/validation time is excluded from algorithm measurements
/// 3. **Simplify algorithms**: Algorithms can assume sorted, unique input
/// 4. **Provide optimizations**: Min/max/sum are precomputed for pruning strategies
///
/// # Example
///
/// ```
/// use subset_sum::InputSet;
///
/// // Valid input
/// let input = InputSet::new(vec![5, 2, 8, 1]).unwrap();
/// assert_eq!(input.numbers(), &[1, 2, 5, 8]); // Sorted
/// assert_eq!(input.min(), 1);
/// assert_eq!(input.max(), 8);
/// assert_eq!(input.total_sum(), 16);
///
/// // Invalid: contains duplicates
/// let result = InputSet::new(vec![3, 5, 3, 7]);
/// assert!(result.is_err());
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputSet {
    /// Sorted, unique numbers.
    numbers: Vec<u64>,
    /// Minimum value in the set.
    min: u64,
    /// Maximum value in the set.
    max: u64,
    /// Sum of all numbers in the set.
    total_sum: u64,
}

impl InputSet {
    /// Creates a new `InputSet` from a vector of numbers.
    ///
    /// The numbers are validated to ensure:
    /// - The vector is non-empty
    /// - All values are positive (no zeros)
    /// - All values are unique (no duplicates)
    ///
    /// The numbers are then sorted in ascending order.
    ///
    /// # Arguments
    ///
    /// * `numbers` - A vector of natural numbers
    ///
    /// # Returns
    ///
    /// `Ok(InputSet)` if the input is valid, `Err(InputSetError)` otherwise.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The input is empty (`InputSetError::EmptyInput`)
    /// - The input contains zero (`InputSetError::ContainsZero`)
    /// - The input contains duplicates (`InputSetError::DuplicateValues`)
    ///
    /// # Example
    ///
    /// ```
    /// use subset_sum::InputSet;
    ///
    /// let input = InputSet::new(vec![3, 1, 4, 1, 5]).unwrap_err();
    /// // Error: duplicate value 1
    /// ```
    pub fn new(mut numbers: Vec<u64>) -> Result<Self, InputSetError> {
        if numbers.is_empty() {
            return Err(InputSetError::EmptyInput);
        }

        // Check for zeros
        if numbers.contains(&0) {
            return Err(InputSetError::ContainsZero);
        }

        // Sort first to make duplicate detection efficient
        numbers.sort_unstable();

        // Find duplicates
        let mut duplicates: Vec<u64> = Vec::new();
        for window in numbers.windows(2) {
            if window[0] == window[1]
                && (duplicates.is_empty() || duplicates.last() != Some(&window[0]))
            {
                duplicates.push(window[0]);
            }
        }

        if !duplicates.is_empty() {
            return Err(InputSetError::DuplicateValues(duplicates));
        }

        // Compute statistics
        let min = numbers[0]; // Already sorted, first is min
        let max = numbers[numbers.len() - 1]; // Last is max
        let total_sum = numbers.iter().sum();

        Ok(Self {
            numbers,
            min,
            max,
            total_sum,
        })
    }

    /// Creates an `InputSet` from already sorted, unique numbers without validation.
    ///
    /// # Safety
    ///
    /// This is not unsafe in the Rust sense, but the caller must ensure:
    /// - Numbers are sorted in ascending order
    /// - Numbers contain no duplicates
    /// - Numbers contain no zeros
    /// - Numbers are non-empty
    ///
    /// This is useful for performance-critical paths where input is known to be valid.
    ///
    /// # Example
    ///
    /// ```
    /// use subset_sum::InputSet;
    ///
    /// // Only use this if you're absolutely sure the input is valid!
    /// let input = InputSet::new_unchecked(vec![1, 2, 5, 8]);
    /// ```
    #[must_use]
    pub fn new_unchecked(numbers: Vec<u64>) -> Self {
        debug_assert!(!numbers.is_empty(), "InputSet cannot be empty");
        debug_assert!(
            numbers.iter().all(|&n| n > 0),
            "InputSet cannot contain zeros"
        );
        debug_assert!(
            numbers.windows(2).all(|w| w[0] < w[1]),
            "InputSet must be sorted and unique"
        );

        let min = numbers[0];
        let max = numbers[numbers.len() - 1];
        let total_sum = numbers.iter().sum();

        Self {
            numbers,
            min,
            max,
            total_sum,
        }
    }

    /// Returns the sorted, unique numbers in the set.
    #[must_use]
    pub fn numbers(&self) -> &[u64] {
        &self.numbers
    }

    /// Returns the number of elements in the set.
    #[must_use]
    pub fn len(&self) -> usize {
        self.numbers.len()
    }

    /// Returns `true` if the set is empty.
    ///
    /// Note: A valid `InputSet` is never empty, so this always returns `false`.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.numbers.is_empty()
    }

    /// Returns the minimum value in the set.
    #[must_use]
    pub const fn min(&self) -> u64 {
        self.min
    }

    /// Returns the maximum value in the set.
    #[must_use]
    pub const fn max(&self) -> u64 {
        self.max
    }

    /// Returns the sum of all numbers in the set.
    #[must_use]
    pub const fn total_sum(&self) -> u64 {
        self.total_sum
    }

    /// Checks if a target sum is achievable (within bounds).
    ///
    /// Returns `false` if target is greater than the total sum of all numbers,
    /// which means no solution can exist.
    #[must_use]
    pub const fn is_target_achievable(&self, target: u64) -> bool {
        target <= self.total_sum
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

/// Verifies that a solution is correct for an `InputSet`.
///
/// # Arguments
///
/// * `input` - The input set that was searched
/// * `target` - Target sum
/// * `subset` - Proposed solution subset
///
/// # Returns
///
/// `true` if the subset sums to target and all elements are from the input set
#[must_use]
pub fn verify_solution_for_input(input: &InputSet, target: u64, subset: &[u64]) -> bool {
    verify_solution(input.numbers(), target, subset)
}

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
pub const ALGORITHM_NAMES: [&str; 11] = [
    "smart_brute_force",
    "brute_force",
    "backtracking",
    "backtracking_pruned",
    "dynamic_programming",
    "incremental_pruning",
    "max_first_reduction",
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
/// * `input` - Preprocessed input set
/// * `target` - Target sum
/// * `verbose` - Enable verbose logging
///
/// # Returns
///
/// `Some(AlgorithmResult)` if algorithm name is valid, `None` otherwise
#[must_use]
pub fn run_algorithm(
    name: &str,
    input: &InputSet,
    target: u64,
    verbose: bool,
) -> Option<AlgorithmResult> {
    match name {
        "smart_brute_force" => Some(smart_brute_force(input, target, verbose)),
        "brute_force" => Some(brute_force(input, target, verbose)),
        "backtracking" => Some(backtracking(input, target, verbose)),
        "backtracking_pruned" => Some(backtracking_pruned(input, target, verbose)),
        "dynamic_programming" => Some(dynamic_programming(input, target, verbose)),
        "incremental_pruning" => Some(incremental_pruning(input, target, verbose)),
        "max_first_reduction" => Some(max_first_reduction(input, target, verbose)),
        "meet_in_middle" => Some(meet_in_middle(input, target, verbose)),
        "meet_in_middle_hash" => Some(meet_in_middle_hash(input, target, verbose)),
        "branch_and_bound" => Some(branch_and_bound(input, target, verbose)),
        "randomized" => Some(randomized(input, target, verbose, 12345)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_algorithm<F>(algo: F, name: &str)
    where
        F: Fn(&InputSet, u64, bool) -> AlgorithmResult,
    {
        // Test 1: Simple case with solution
        let input = InputSet::new(vec![3, 7, 1, 8, 4]).unwrap();
        let target = 15;
        let result = algo(&input, target, false);
        assert!(
            result.solution.is_some(),
            "{}: Should find solution for target 15",
            name
        );
        assert!(
            verify_solution_for_input(&input, target, result.solution.as_ref().unwrap()),
            "{}: Solution should be valid",
            name
        );

        // Test 2: No solution exists
        let input = InputSet::new(vec![2, 4, 6, 8]).unwrap();
        let target = 1;
        let result = algo(&input, target, false);
        assert!(
            result.solution.is_none(),
            "{}: Should not find solution for target 1",
            name
        );

        // Test 3: Target is zero (empty subset)
        let input = InputSet::new(vec![1, 2, 3]).unwrap();
        let target = 0;
        let result = algo(&input, target, false);
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
        let input = InputSet::new(vec![5]).unwrap();
        let target = 5;
        let result = algo(&input, target, false);
        assert!(
            result.solution.is_some(),
            "{}: Should find single element solution",
            name
        );

        // Test 5: Multiple elements sum to target
        let input = InputSet::new(vec![1, 2, 3, 4, 5]).unwrap();
        let target = 10;
        let result = algo(&input, target, false);
        assert!(
            result.solution.is_some(),
            "{}: Should find solution for target 10",
            name
        );
        assert!(
            verify_solution_for_input(&input, target, result.solution.as_ref().unwrap()),
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
        let input = InputSet::new(vec![1, 2, 4, 8, 16, 32]).unwrap();
        let target = 21; // 1 + 4 + 16 = 21
        let result = smart_brute_force(&input, target, false);
        assert!(result.solution.is_some());
        assert!(verify_solution_for_input(
            &input,
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
    fn test_max_first_reduction() {
        test_algorithm(max_first_reduction, "max_first_reduction");
    }

    #[test]
    fn test_randomized() {
        let algo = |input: &InputSet, target: u64, verbose: bool| {
            randomized(input, target, verbose, 12345)
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
        let input = InputSet::new(vec![3, 7, 1, 8, 4]).unwrap();
        let target = 15;

        for name in ALGORITHM_NAMES {
            let result = run_algorithm(name, &input, target, false);
            assert!(result.is_some(), "Algorithm {} should exist", name);
            let result = result.unwrap();
            assert!(
                result.solution.is_some(),
                "Algorithm {} should find solution",
                name
            );
        }

        // Invalid algorithm name
        assert!(run_algorithm("invalid", &input, target, false).is_none());
    }

    #[test]
    fn test_steps_counted() {
        let input = InputSet::new(vec![1, 2, 3, 4, 5]).unwrap();
        let target = 100; // impossible

        // All algorithms should count steps
        let result = brute_force(&input, target, false);
        assert!(result.steps > 0, "Brute force should count steps");

        let result = backtracking(&input, target, false);
        assert!(result.steps > 0, "Backtracking should count steps");

        let result = dynamic_programming(&input, target, false);
        assert!(result.steps > 0, "DP should count steps");
    }

    #[test]
    fn test_larger_input() {
        // Test with moderately larger input (n=15)
        let input = InputSet::new((1..=15).collect()).unwrap();
        let target = 50;

        for name in ALGORITHM_NAMES {
            let result = run_algorithm(name, &input, target, false);
            assert!(result.is_some());
            let result = result.unwrap();
            assert!(
                result.solution.is_some(),
                "Algorithm {} should find solution for n=15",
                name
            );
            assert!(
                verify_solution_for_input(&input, target, result.solution.as_ref().unwrap()),
                "Algorithm {} should produce valid solution for n=15",
                name
            );
        }
    }

    // =========================================================================
    // InputSet tests
    // =========================================================================

    #[test]
    fn test_input_set_creation() {
        // Valid input
        let input = InputSet::new(vec![5, 2, 8, 1]).unwrap();
        assert_eq!(input.numbers(), &[1, 2, 5, 8]); // Sorted
        assert_eq!(input.min(), 1);
        assert_eq!(input.max(), 8);
        assert_eq!(input.total_sum(), 16);
        assert_eq!(input.len(), 4);
    }

    #[test]
    fn test_input_set_rejects_duplicates() {
        let result = InputSet::new(vec![3, 5, 3, 7]);
        assert!(result.is_err());
        match result {
            Err(InputSetError::DuplicateValues(dups)) => {
                assert_eq!(dups, vec![3]);
            }
            _ => panic!("Expected DuplicateValues error"),
        }
    }

    #[test]
    fn test_input_set_rejects_multiple_duplicates() {
        let result = InputSet::new(vec![3, 5, 3, 7, 5, 5]);
        assert!(result.is_err());
        match result {
            Err(InputSetError::DuplicateValues(dups)) => {
                assert!(dups.contains(&3));
                assert!(dups.contains(&5));
            }
            _ => panic!("Expected DuplicateValues error"),
        }
    }

    #[test]
    fn test_input_set_rejects_empty() {
        let result = InputSet::new(vec![]);
        assert!(result.is_err());
        match result {
            Err(InputSetError::EmptyInput) => {}
            _ => panic!("Expected EmptyInput error"),
        }
    }

    #[test]
    fn test_input_set_rejects_zero() {
        let result = InputSet::new(vec![1, 0, 3]);
        assert!(result.is_err());
        match result {
            Err(InputSetError::ContainsZero) => {}
            _ => panic!("Expected ContainsZero error"),
        }
    }

    #[test]
    fn test_input_set_is_target_achievable() {
        let input = InputSet::new(vec![1, 2, 3]).unwrap();
        assert!(input.is_target_achievable(6)); // sum = 6
        assert!(input.is_target_achievable(5));
        assert!(!input.is_target_achievable(7)); // > sum
    }

    #[test]
    fn test_input_set_unchecked() {
        let input = InputSet::new_unchecked(vec![1, 2, 5, 8]);
        assert_eq!(input.numbers(), &[1, 2, 5, 8]);
        assert_eq!(input.min(), 1);
        assert_eq!(input.max(), 8);
    }
}
