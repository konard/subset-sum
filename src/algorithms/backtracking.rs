//! Backtracking algorithms for the subset sum problem.

use crate::{verbose_log, AlgorithmResult};

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
