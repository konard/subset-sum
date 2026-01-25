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
//! - **Brute Force**: O(2^n) - tries all possible subsets
//! - **Backtracking**: O(2^n) worst case - recursive with early termination
//! - **Backtracking Pruned**: O(2^n) worst case - with sum-based pruning
//! - **Dynamic Programming**: O(n * target) - pseudo-polynomial time
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

use std::collections::HashMap;

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
macro_rules! verbose_log {
    ($verbose:expr, $($arg:tt)*) => {
        if $verbose {
            println!($($arg)*);
        }
    };
}

// ============================================================================
// 1. SMART BRUTE FORCE - O(2^n) but with optimizations
// konard's algorithm with power-of-two optimization and early exits
// ============================================================================

/// Smart brute force subset sum algorithm.
///
/// This algorithm (by konard) includes several optimizations:
/// - Filters out numbers greater than target
/// - Sorts numbers for efficient processing
/// - Special case: if target is a single number in set, returns immediately
/// - Special case: if target can be built from available powers of two, returns immediately
/// - Falls back to brute force for general case
///
/// # Arguments
///
/// * `numbers` - Slice of natural numbers to search through
/// * `target` - Target sum to find
/// * `verbose` - Enable verbose logging output
///
/// # Returns
///
/// `AlgorithmResult` containing the solution (if found) and step count
///
/// # Time Complexity
///
/// O(2^n) worst case, but with multiple early exit conditions
///
/// # Examples
///
/// ```
/// use subset_sum::smart_brute_force;
///
/// let numbers = vec![3, 7, 1, 8, 4];
/// let result = smart_brute_force(&numbers, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn smart_brute_force(numbers: &[u64], target: u64, verbose: bool) -> AlgorithmResult {
    if numbers.is_empty() {
        verbose_log!(verbose, "[Smart Brute Force] Empty input");
        return AlgorithmResult::new(if target == 0 { Some(vec![]) } else { None }, 0);
    }

    // Filter and sort numbers
    let mut sorted_numbers: Vec<u64> = numbers
        .iter()
        .copied()
        .filter(|&x| x >= 1 && x <= target)
        .collect();
    sorted_numbers.sort_unstable();

    verbose_log!(
        verbose,
        "[Smart Brute Force] Filtered and sorted numbers: {:?}",
        sorted_numbers
    );

    if sorted_numbers.is_empty() {
        verbose_log!(
            verbose,
            "[Smart Brute Force] No valid numbers after filtering"
        );
        return AlgorithmResult::new(if target == 0 { Some(vec![]) } else { None }, 0);
    }

    let n = sorted_numbers.len();
    let total_sum: u64 = sorted_numbers.iter().sum();

    let min = sorted_numbers[0];
    let max = sorted_numbers[n - 1];

    verbose_log!(verbose, "[Smart Brute Force] Minimum number: {}", min);
    verbose_log!(verbose, "[Smart Brute Force] Maximum number: {}", max);
    verbose_log!(
        verbose,
        "[Smart Brute Force] Total sum of numbers: {}",
        total_sum
    );

    // Special case: max equals target
    if max == target {
        verbose_log!(
            verbose,
            "[Smart Brute Force] Max equals target, returning [{}]",
            max
        );
        return AlgorithmResult::new(Some(vec![max]), 1);
    }

    // Early exit: target impossible
    if target < min || target > total_sum {
        verbose_log!(
            verbose,
            "[Smart Brute Force] Target impossible (min={}, max_sum={})",
            min,
            total_sum
        );
        return AlgorithmResult::new(None, 0);
    }

    // Check if target is 0
    if target == 0 {
        verbose_log!(
            verbose,
            "[Smart Brute Force] Target is 0, returning empty subset"
        );
        return AlgorithmResult::new(Some(vec![]), 0);
    }

    // Build bitmap of existing powers of two
    let mut existing_powers_of_two: u64 = 0;
    for &number in &sorted_numbers {
        if number.is_power_of_two() && number.trailing_zeros() < 64 {
            existing_powers_of_two |= 1 << number.trailing_zeros();
        }
    }

    verbose_log!(
        verbose,
        "[Smart Brute Force] Existing powers of two (binary): {:064b}",
        existing_powers_of_two
    );

    let missing_powers_of_two = !existing_powers_of_two;
    let powers_of_two_missing_for_target = missing_powers_of_two & target;

    verbose_log!(
        verbose,
        "[Smart Brute Force] Missing powers of two (binary): {:064b}",
        missing_powers_of_two
    );
    verbose_log!(
        verbose,
        "[Smart Brute Force] Powers of two missing for target (binary): {:064b}",
        powers_of_two_missing_for_target
    );

    // If we can build target from available powers of two
    if powers_of_two_missing_for_target == 0 {
        let mut subset = Vec::new();
        for i in 0..64 {
            if target & (1 << i) != 0 && existing_powers_of_two & (1 << i) != 0 {
                let power_of_two = 1u64 << i;
                subset.push(power_of_two);
            }
        }
        verbose_log!(
            verbose,
            "[Smart Brute Force] Built target from powers of two: {:?}",
            subset
        );
        return AlgorithmResult::new(Some(subset), 0);
    }

    // Fall back to brute force
    let mut steps: u64 = 0;

    // Limit to 63 bits to avoid overflow
    if n > 63 {
        verbose_log!(verbose, "[Smart Brute Force] Too many numbers (max 63)");
        return AlgorithmResult::new(None, steps);
    }

    let total_subsets = 1u64 << n;
    for mask in 0..total_subsets {
        steps += 1;

        let mut sum: u64 = 0;
        let mut subset = Vec::new();

        for i in 0..n {
            if mask & (1 << i) != 0 {
                sum = sum.saturating_add(sorted_numbers[i]);
                subset.push(sorted_numbers[i]);
            }
        }

        verbose_log!(
            verbose,
            "[Smart Brute Force] Step {}: mask={:b}, subset={:?}, sum={}",
            steps,
            mask,
            subset,
            sum
        );

        if sum == target {
            verbose_log!(verbose, "[Smart Brute Force] Found solution: {:?}", subset);
            return AlgorithmResult::new(Some(subset), steps);
        }
    }

    verbose_log!(
        verbose,
        "[Smart Brute Force] No solution found after {} steps",
        steps
    );
    AlgorithmResult::new(None, steps)
}

// ============================================================================
// 2. BRUTE FORCE - O(2^n)
// Try all possible subsets using bitmask
// ============================================================================

/// Brute force subset sum algorithm.
///
/// Tries all possible subsets using bitmask enumeration.
///
/// # Arguments
///
/// * `numbers` - Slice of natural numbers to search through
/// * `target` - Target sum to find
/// * `verbose` - Enable verbose logging output
///
/// # Returns
///
/// `AlgorithmResult` containing the solution (if found) and step count
///
/// # Time Complexity
///
/// O(2^n) where n is the length of numbers
///
/// # Examples
///
/// ```
/// use subset_sum::brute_force;
///
/// let numbers = vec![3, 7, 1, 8, 4];
/// let result = brute_force(&numbers, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn brute_force(numbers: &[u64], target: u64, verbose: bool) -> AlgorithmResult {
    let n = numbers.len();
    let mut steps: u64 = 0;

    verbose_log!(
        verbose,
        "[Brute Force] Starting with {} numbers, target={}",
        n,
        target
    );

    // Limit to 63 bits to avoid overflow
    if n > 63 {
        verbose_log!(
            verbose,
            "[Brute Force] Too many numbers (max 63 for brute force)"
        );
        return AlgorithmResult::new(None, steps);
    }

    let total_subsets = 1u64 << n;
    for mask in 0..total_subsets {
        steps += 1;

        let mut sum: u64 = 0;
        let mut subset = Vec::new();

        for i in 0..n {
            if mask & (1 << i) != 0 {
                sum = sum.saturating_add(numbers[i]);
                subset.push(numbers[i]);
            }
        }

        verbose_log!(
            verbose,
            "[Brute Force] Step {}: mask={:b}, subset={:?}, sum={}",
            steps,
            mask,
            subset,
            sum
        );

        if sum == target {
            verbose_log!(verbose, "[Brute Force] Found solution: {:?}", subset);
            return AlgorithmResult::new(Some(subset), steps);
        }
    }

    verbose_log!(
        verbose,
        "[Brute Force] No solution found after {} steps",
        steps
    );
    AlgorithmResult::new(None, steps)
}

// ============================================================================
// 2. BACKTRACKING - O(2^n) worst case, often better
// Recursive with early termination
// ============================================================================

/// Backtracking subset sum algorithm.
///
/// Uses recursion with early termination when solution is found.
///
/// # Arguments
///
/// * `numbers` - Slice of natural numbers to search through
/// * `target` - Target sum to find
/// * `verbose` - Enable verbose logging output
///
/// # Returns
///
/// `AlgorithmResult` containing the solution (if found) and step count
///
/// # Time Complexity
///
/// O(2^n) worst case, but often better due to early termination
///
/// # Examples
///
/// ```
/// use subset_sum::backtracking;
///
/// let numbers = vec![3, 7, 1, 8, 4];
/// let result = backtracking(&numbers, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn backtracking(numbers: &[u64], target: u64, verbose: bool) -> AlgorithmResult {
    let mut steps: u64 = 0;
    let mut result: Option<Vec<u64>> = None;

    verbose_log!(
        verbose,
        "[Backtracking] Starting with {} numbers, target={}",
        numbers.len(),
        target
    );

    fn recurse(
        nums: &[u64],
        target: u64,
        index: usize,
        current_sum: u64,
        subset: &mut Vec<u64>,
        steps: &mut u64,
        result: &mut Option<Vec<u64>>,
        verbose: bool,
    ) -> bool {
        *steps += 1;

        verbose_log!(
            verbose,
            "[Backtracking] Step {}: index={}, current_sum={}, subset={:?}",
            steps,
            index,
            current_sum,
            subset
        );

        if current_sum == target {
            *result = Some(subset.clone());
            verbose_log!(verbose, "[Backtracking] Found solution: {:?}", subset);
            return true;
        }

        if index >= nums.len() {
            return false;
        }

        // include current element
        subset.push(nums[index]);
        if recurse(
            nums,
            target,
            index + 1,
            current_sum.saturating_add(nums[index]),
            subset,
            steps,
            result,
            verbose,
        ) {
            return true;
        }
        subset.pop();

        // exclude current element
        recurse(
            nums,
            target,
            index + 1,
            current_sum,
            subset,
            steps,
            result,
            verbose,
        )
    }

    recurse(
        numbers,
        target,
        0,
        0,
        &mut Vec::new(),
        &mut steps,
        &mut result,
        verbose,
    );

    verbose_log!(verbose, "[Backtracking] Completed with {} steps", steps);
    AlgorithmResult::new(result, steps)
}

// ============================================================================
// 3. BACKTRACKING WITH PRUNING - O(2^n) worst case, much better average
// Sort first, prune when sum exceeds target
// ============================================================================

/// Backtracking with pruning subset sum algorithm.
///
/// Sorts numbers first and prunes branches when sum exceeds target.
///
/// # Arguments
///
/// * `numbers` - Slice of natural numbers to search through
/// * `target` - Target sum to find
/// * `verbose` - Enable verbose logging output
///
/// # Returns
///
/// `AlgorithmResult` containing the solution (if found) and step count
///
/// # Time Complexity
///
/// O(2^n) worst case, but much better average case due to pruning
///
/// # Examples
///
/// ```
/// use subset_sum::backtracking_pruned;
///
/// let numbers = vec![3, 7, 1, 8, 4];
/// let result = backtracking_pruned(&numbers, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn backtracking_pruned(numbers: &[u64], target: u64, verbose: bool) -> AlgorithmResult {
    let mut sorted = numbers.to_vec();
    sorted.sort_unstable();

    let mut steps: u64 = 0;
    let mut result: Option<Vec<u64>> = None;

    verbose_log!(
        verbose,
        "[Backtracking Pruned] Starting with {} numbers, target={}",
        numbers.len(),
        target
    );
    verbose_log!(verbose, "[Backtracking Pruned] Sorted: {:?}", sorted);

    fn recurse(
        nums: &[u64],
        target: u64,
        index: usize,
        current_sum: u64,
        subset: &mut Vec<u64>,
        steps: &mut u64,
        result: &mut Option<Vec<u64>>,
        verbose: bool,
    ) -> bool {
        *steps += 1;

        verbose_log!(
            verbose,
            "[Backtracking Pruned] Step {}: index={}, current_sum={}, subset={:?}",
            steps,
            index,
            current_sum,
            subset
        );

        if current_sum == target {
            *result = Some(subset.clone());
            verbose_log!(
                verbose,
                "[Backtracking Pruned] Found solution: {:?}",
                subset
            );
            return true;
        }

        if current_sum > target {
            verbose_log!(
                verbose,
                "[Backtracking Pruned] Pruning: sum {} > target {}",
                current_sum,
                target
            );
            return false;
        }

        if index >= nums.len() {
            return false;
        }

        for i in index..nums.len() {
            if current_sum.saturating_add(nums[i]) > target {
                verbose_log!(
                    verbose,
                    "[Backtracking Pruned] Pruning: all remaining elements too large"
                );
                break;
            }

            subset.push(nums[i]);
            if recurse(
                nums,
                target,
                i + 1,
                current_sum.saturating_add(nums[i]),
                subset,
                steps,
                result,
                verbose,
            ) {
                return true;
            }
            subset.pop();
        }

        false
    }

    recurse(
        &sorted,
        target,
        0,
        0,
        &mut Vec::new(),
        &mut steps,
        &mut result,
        verbose,
    );

    verbose_log!(
        verbose,
        "[Backtracking Pruned] Completed with {} steps",
        steps
    );
    AlgorithmResult::new(result, steps)
}

// ============================================================================
// 4. DYNAMIC PROGRAMMING - O(n * target)
// Pseudo-polynomial: polynomial in n and target value
// ============================================================================

/// Dynamic programming subset sum algorithm.
///
/// Uses bottom-up DP to build achievable sums.
///
/// # Arguments
///
/// * `numbers` - Slice of natural numbers to search through
/// * `target` - Target sum to find
/// * `verbose` - Enable verbose logging output
///
/// # Returns
///
/// `AlgorithmResult` containing the solution (if found) and step count
///
/// # Time Complexity
///
/// O(n * target) - pseudo-polynomial
///
/// # Examples
///
/// ```
/// use subset_sum::dynamic_programming;
///
/// let numbers = vec![3, 7, 1, 8, 4];
/// let result = dynamic_programming(&numbers, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn dynamic_programming(numbers: &[u64], target: u64, verbose: bool) -> AlgorithmResult {
    let mut steps: u64 = 0;

    verbose_log!(
        verbose,
        "[DP] Starting with {} numbers, target={}",
        numbers.len(),
        target
    );

    // Limit target to prevent memory exhaustion
    if target > 10_000_000 {
        verbose_log!(verbose, "[DP] Target too large for DP approach");
        return AlgorithmResult::new(None, steps);
    }

    let target_usize = target as usize;

    // dp[i] = true if sum i is achievable
    let mut dp = vec![false; target_usize + 1];
    // parent[i] = (previous_sum, number_added) to reconstruct solution
    let mut parent: Vec<Option<(usize, u64)>> = vec![None; target_usize + 1];

    dp[0] = true;

    for &num in numbers {
        if num > target {
            continue;
        }
        let num_usize = num as usize;

        verbose_log!(verbose, "[DP] Processing number {}", num);

        // iterate backwards to avoid using same number twice
        for s in (num_usize..=target_usize).rev() {
            steps += 1;
            if dp[s - num_usize] && !dp[s] {
                dp[s] = true;
                parent[s] = Some((s - num_usize, num));
                verbose_log!(verbose, "[DP] Step {}: sum {} is now achievable", steps, s);
            }
        }

        if dp[target_usize] {
            verbose_log!(verbose, "[DP] Target reached early, exiting");
            break;
        }
    }

    if dp[target_usize] {
        // reconstruct solution
        let mut subset = Vec::new();
        let mut current = target_usize;
        while let Some((prev, num)) = parent[current] {
            subset.push(num);
            current = prev;
        }
        verbose_log!(verbose, "[DP] Found solution: {:?}", subset);
        AlgorithmResult::new(Some(subset), steps)
    } else {
        verbose_log!(verbose, "[DP] No solution found after {} steps", steps);
        AlgorithmResult::new(None, steps)
    }
}

// ============================================================================
// 5. MEET IN THE MIDDLE - O(2^(n/2))
// Split array, compute all sums for each half, find matching pair
// ============================================================================

/// Meet in the middle subset sum algorithm.
///
/// Splits array in half and uses binary search to find matching sums.
///
/// # Arguments
///
/// * `numbers` - Slice of natural numbers to search through
/// * `target` - Target sum to find
/// * `verbose` - Enable verbose logging output
///
/// # Returns
///
/// `AlgorithmResult` containing the solution (if found) and step count
///
/// # Time Complexity
///
/// O(2^(n/2) * log(2^(n/2))) = O(n * 2^(n/2))
///
/// # Examples
///
/// ```
/// use subset_sum::meet_in_middle;
///
/// let numbers = vec![3, 7, 1, 8, 4];
/// let result = meet_in_middle(&numbers, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn meet_in_middle(numbers: &[u64], target: u64, verbose: bool) -> AlgorithmResult {
    let n = numbers.len();
    let mid = n / 2;
    let mut steps: u64 = 0;

    verbose_log!(
        verbose,
        "[Meet in Middle] Starting with {} numbers, target={}",
        n,
        target
    );
    verbose_log!(verbose, "[Meet in Middle] Splitting at index {}", mid);

    // Limit to prevent memory exhaustion
    if mid > 25 {
        verbose_log!(
            verbose,
            "[Meet in Middle] Array too large (max ~50 elements)"
        );
        return AlgorithmResult::new(None, steps);
    }

    // compute all subset sums for first half
    let mut left_sums: Vec<(u64, u64)> = Vec::with_capacity(1 << mid);
    let left_count = 1u64 << mid;
    for mask in 0..left_count {
        steps += 1;
        let sum: u64 = (0..mid)
            .filter(|&i| mask & (1 << i) != 0)
            .map(|i| numbers[i])
            .fold(0u64, |acc, x| acc.saturating_add(x));
        left_sums.push((sum, mask));
    }

    verbose_log!(
        verbose,
        "[Meet in Middle] Computed {} left sums",
        left_sums.len()
    );

    // sort for binary search
    left_sums.sort_by_key(|&(sum, _)| sum);

    // compute all subset sums for second half, look for complement
    let right_count = 1u64 << (n - mid);
    for mask_right in 0..right_count {
        steps += 1;
        let right_sum: u64 = (0..(n - mid))
            .filter(|&i| mask_right & (1 << i) != 0)
            .map(|i| numbers[mid + i])
            .fold(0u64, |acc, x| acc.saturating_add(x));

        if right_sum > target {
            continue;
        }
        let needed = target - right_sum;

        verbose_log!(
            verbose,
            "[Meet in Middle] Step {}: right_sum={}, need={}",
            steps,
            right_sum,
            needed
        );

        // binary search in left sums
        if let Ok(idx) = left_sums.binary_search_by_key(&needed, |&(sum, _)| sum) {
            let (_, mask_left) = left_sums[idx];

            // reconstruct subset
            let mut subset = Vec::new();
            for i in 0..mid {
                if mask_left & (1 << i) != 0 {
                    subset.push(numbers[i]);
                }
            }
            for i in 0..(n - mid) {
                if mask_right & (1 << i) != 0 {
                    subset.push(numbers[mid + i]);
                }
            }
            verbose_log!(verbose, "[Meet in Middle] Found solution: {:?}", subset);
            return AlgorithmResult::new(Some(subset), steps);
        }
    }

    verbose_log!(
        verbose,
        "[Meet in Middle] No solution found after {} steps",
        steps
    );
    AlgorithmResult::new(None, steps)
}

// ============================================================================
// 6. MEET IN THE MIDDLE WITH HASHSET - O(2^(n/2))
// Same idea but using hash set for O(1) lookup
// ============================================================================

/// Meet in the middle with hash set subset sum algorithm.
///
/// Splits array in half and uses hash map for O(1) lookup.
///
/// # Arguments
///
/// * `numbers` - Slice of natural numbers to search through
/// * `target` - Target sum to find
/// * `verbose` - Enable verbose logging output
///
/// # Returns
///
/// `AlgorithmResult` containing the solution (if found) and step count
///
/// # Time Complexity
///
/// O(2^(n/2)) with O(1) hash lookups
///
/// # Examples
///
/// ```
/// use subset_sum::meet_in_middle_hash;
///
/// let numbers = vec![3, 7, 1, 8, 4];
/// let result = meet_in_middle_hash(&numbers, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn meet_in_middle_hash(numbers: &[u64], target: u64, verbose: bool) -> AlgorithmResult {
    let n = numbers.len();
    let mid = n / 2;
    let mut steps: u64 = 0;

    verbose_log!(
        verbose,
        "[Meet in Middle Hash] Starting with {} numbers, target={}",
        n,
        target
    );

    // Limit to prevent memory exhaustion
    if mid > 25 {
        verbose_log!(
            verbose,
            "[Meet in Middle Hash] Array too large (max ~50 elements)"
        );
        return AlgorithmResult::new(None, steps);
    }

    // compute all subset sums for first half, store in hash map
    let mut left_map: HashMap<u64, u64> = HashMap::new();
    let left_count = 1u64 << mid;
    for mask in 0..left_count {
        steps += 1;
        let sum: u64 = (0..mid)
            .filter(|&i| mask & (1 << i) != 0)
            .map(|i| numbers[i])
            .fold(0u64, |acc, x| acc.saturating_add(x));
        left_map.insert(sum, mask);
    }

    verbose_log!(
        verbose,
        "[Meet in Middle Hash] Computed {} left sums",
        left_map.len()
    );

    // compute all subset sums for second half, look for complement
    let right_count = 1u64 << (n - mid);
    for mask_right in 0..right_count {
        steps += 1;
        let right_sum: u64 = (0..(n - mid))
            .filter(|&i| mask_right & (1 << i) != 0)
            .map(|i| numbers[mid + i])
            .fold(0u64, |acc, x| acc.saturating_add(x));

        if right_sum > target {
            continue;
        }
        let needed = target - right_sum;

        verbose_log!(
            verbose,
            "[Meet in Middle Hash] Step {}: right_sum={}, need={}",
            steps,
            right_sum,
            needed
        );

        if let Some(&mask_left) = left_map.get(&needed) {
            // reconstruct subset
            let mut subset = Vec::new();
            for i in 0..mid {
                if mask_left & (1 << i) != 0 {
                    subset.push(numbers[i]);
                }
            }
            for i in 0..(n - mid) {
                if mask_right & (1 << i) != 0 {
                    subset.push(numbers[mid + i]);
                }
            }
            verbose_log!(
                verbose,
                "[Meet in Middle Hash] Found solution: {:?}",
                subset
            );
            return AlgorithmResult::new(Some(subset), steps);
        }
    }

    verbose_log!(
        verbose,
        "[Meet in Middle Hash] No solution found after {} steps",
        steps
    );
    AlgorithmResult::new(None, steps)
}

// ============================================================================
// 7. BRANCH AND BOUND - O(2^n) worst case
// Use upper/lower bounds to prune branches more aggressively
// ============================================================================

/// Branch and bound subset sum algorithm.
///
/// Uses bounds to prune the search space more aggressively.
///
/// # Arguments
///
/// * `numbers` - Slice of natural numbers to search through
/// * `target` - Target sum to find
/// * `verbose` - Enable verbose logging output
///
/// # Returns
///
/// `AlgorithmResult` containing the solution (if found) and step count
///
/// # Time Complexity
///
/// O(2^n) worst case, but often much better with good pruning
///
/// # Examples
///
/// ```
/// use subset_sum::branch_and_bound;
///
/// let numbers = vec![3, 7, 1, 8, 4];
/// let result = branch_and_bound(&numbers, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn branch_and_bound(numbers: &[u64], target: u64, verbose: bool) -> AlgorithmResult {
    let mut sorted: Vec<(u64, usize)> = numbers
        .iter()
        .copied()
        .enumerate()
        .map(|(i, x)| (x, i))
        .collect();
    sorted.sort_by_key(|&(x, _)| x);

    // precompute suffix sums (max possible sum from index i onward)
    let mut suffix_sum = vec![0u64; sorted.len() + 1];
    for i in (0..sorted.len()).rev() {
        suffix_sum[i] = suffix_sum[i + 1].saturating_add(sorted[i].0);
    }

    let mut steps: u64 = 0;
    let mut result: Option<Vec<u64>> = None;

    verbose_log!(
        verbose,
        "[Branch and Bound] Starting with {} numbers, target={}",
        numbers.len(),
        target
    );
    verbose_log!(verbose, "[Branch and Bound] Sorted: {:?}", sorted);

    fn recurse(
        sorted: &[(u64, usize)],
        suffix_sum: &[u64],
        target: u64,
        index: usize,
        current_sum: u64,
        subset: &mut Vec<u64>,
        steps: &mut u64,
        result: &mut Option<Vec<u64>>,
        verbose: bool,
    ) -> bool {
        *steps += 1;

        verbose_log!(
            verbose,
            "[Branch and Bound] Step {}: index={}, current_sum={}, subset={:?}",
            steps,
            index,
            current_sum,
            subset
        );

        if current_sum == target {
            *result = Some(subset.clone());
            verbose_log!(verbose, "[Branch and Bound] Found solution: {:?}", subset);
            return true;
        }

        if index >= sorted.len() {
            return false;
        }

        // prune: even taking all remaining can't reach target
        if current_sum.saturating_add(suffix_sum[index]) < target {
            verbose_log!(
                verbose,
                "[Branch and Bound] Pruning: max possible sum {} < target",
                current_sum.saturating_add(suffix_sum[index])
            );
            return false;
        }

        // prune: already exceeded target
        if current_sum > target {
            verbose_log!(
                verbose,
                "[Branch and Bound] Pruning: sum {} > target {}",
                current_sum,
                target
            );
            return false;
        }

        let (num, _) = sorted[index];

        // try including
        if current_sum.saturating_add(num) <= target {
            subset.push(num);
            if recurse(
                sorted,
                suffix_sum,
                target,
                index + 1,
                current_sum.saturating_add(num),
                subset,
                steps,
                result,
                verbose,
            ) {
                return true;
            }
            subset.pop();
        }

        // try excluding
        recurse(
            sorted,
            suffix_sum,
            target,
            index + 1,
            current_sum,
            subset,
            steps,
            result,
            verbose,
        )
    }

    recurse(
        &sorted,
        &suffix_sum,
        target,
        0,
        0,
        &mut Vec::new(),
        &mut steps,
        &mut result,
        verbose,
    );

    verbose_log!(verbose, "[Branch and Bound] Completed with {} steps", steps);
    AlgorithmResult::new(result, steps)
}

// ============================================================================
// 8. RANDOMIZED (Las Vegas) - Expected O(2^n), can get lucky
// Random order exploration, sometimes finds solution faster
// ============================================================================

/// Randomized (Las Vegas) subset sum algorithm.
///
/// Explores subsets in random order, may find solution faster by luck.
///
/// # Arguments
///
/// * `numbers` - Slice of natural numbers to search through
/// * `target` - Target sum to find
/// * `verbose` - Enable verbose logging output
/// * `seed` - Random seed for reproducibility
///
/// # Returns
///
/// `AlgorithmResult` containing the solution (if found) and step count
///
/// # Time Complexity
///
/// O(2^n) expected, but may find solution earlier with good luck
///
/// # Examples
///
/// ```
/// use subset_sum::randomized;
///
/// let numbers = vec![3, 7, 1, 8, 4];
/// let result = randomized(&numbers, 15, false, 12345);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn randomized(numbers: &[u64], target: u64, verbose: bool, seed: u64) -> AlgorithmResult {
    let n = numbers.len();
    let mut steps: u64 = 0;

    verbose_log!(
        verbose,
        "[Randomized] Starting with {} numbers, target={}, seed={}",
        n,
        target,
        seed
    );

    // Limit to 63 bits to avoid overflow
    if n > 63 {
        verbose_log!(verbose, "[Randomized] Too many numbers (max 63)");
        return AlgorithmResult::new(None, steps);
    }

    // simple PRNG (Linear Congruential Generator)
    let mut rng_state = seed;
    let mut next_rand = || {
        rng_state = rng_state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        rng_state
    };

    // generate random permutation of masks
    let total = 1u64 << n;
    let mut masks: Vec<u64> = (0..total).collect();

    // Fisher-Yates shuffle
    for i in (1..masks.len()).rev() {
        let j = (next_rand() as usize) % (i + 1);
        masks.swap(i, j);
    }

    verbose_log!(verbose, "[Randomized] Shuffled {} masks", masks.len());

    for mask in masks {
        steps += 1;

        let mut sum: u64 = 0;
        let mut subset = Vec::new();

        for i in 0..n {
            if mask & (1 << i) != 0 {
                sum = sum.saturating_add(numbers[i]);
                subset.push(numbers[i]);
            }
        }

        verbose_log!(
            verbose,
            "[Randomized] Step {}: mask={:b}, subset={:?}, sum={}",
            steps,
            mask,
            subset,
            sum
        );

        if sum == target {
            verbose_log!(verbose, "[Randomized] Found solution: {:?}", subset);
            return AlgorithmResult::new(Some(subset), steps);
        }
    }

    verbose_log!(
        verbose,
        "[Randomized] No solution found after {} steps",
        steps
    );
    AlgorithmResult::new(None, steps)
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
pub const ALGORITHM_NAMES: [&str; 9] = [
    "smart_brute_force",
    "brute_force",
    "backtracking",
    "backtracking_pruned",
    "dynamic_programming",
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
