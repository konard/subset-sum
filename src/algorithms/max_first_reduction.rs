//! Max-first reduction algorithm for the subset sum problem.
//!
//! This algorithm works by using sorted input and recursively trying to include
//! the largest element first. If including the max doesn't lead to a solution,
//! it's excluded and the search continues with smaller elements.
//!
//! The idea is that by committing to the largest elements early, we can
//! reduce the target sum faster and potentially prune more of the search space.

use crate::{verbose_log, AlgorithmResult, InputSet};

/// Max-first reduction subset sum algorithm.
///
/// This algorithm:
/// 1. Uses pre-sorted input from `InputSet`
/// 2. Filters out numbers greater than target
/// 3. Handles edge cases (target = 0, single element solutions, etc.)
/// 4. Recursively tries to include the largest element:
///    - If max <= remaining target: include max, recurse with (target - max)
///    - If no solution found with max, exclude it and try without
///
/// The intuition is that larger numbers reduce the target faster,
/// potentially leading to earlier termination.
///
/// # Arguments
///
/// * `input` - Preprocessed input set (sorted, unique numbers with precomputed min/max/sum)
/// * `target` - Target sum to find
/// * `verbose` - Enable verbose logging output
///
/// # Returns
///
/// `AlgorithmResult` containing the solution (if found) and step count
///
/// # Time Complexity
///
/// O(2^n) worst case, but with early pruning when large elements
/// quickly exceed or reach the target.
///
/// # Examples
///
/// ```
/// use subset_sum::{max_first_reduction, InputSet};
///
/// let input = InputSet::new(vec![3, 7, 1, 8, 4]).unwrap();
/// let result = max_first_reduction(&input, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn max_first_reduction(input: &InputSet, target: u64, verbose: bool) -> AlgorithmResult {
    let mut steps: u64 = 0;

    verbose_log!(
        verbose,
        "[Max-First Reduction] Starting with {} numbers, target={}",
        input.len(),
        target
    );

    // Handle target = 0
    if target == 0 {
        verbose_log!(
            verbose,
            "[Max-First Reduction] Target is 0, returning empty subset"
        );
        return AlgorithmResult::new(Some(Vec::new()), 0);
    }

    // Filter numbers: keep only those <= target (input is already sorted and > 0)
    let sorted: Vec<u64> = input
        .numbers()
        .iter()
        .copied()
        .filter(|&x| x <= target)
        .collect();

    if sorted.is_empty() {
        verbose_log!(
            verbose,
            "[Max-First Reduction] No valid numbers after filtering"
        );
        return AlgorithmResult::new(None, 0);
    }

    verbose_log!(
        verbose,
        "[Max-First Reduction] Filtered numbers (<= target): {:?}",
        sorted
    );

    let n = sorted.len();
    let total_sum: u64 = sorted.iter().sum();

    // Early exit: target impossible
    if target > total_sum {
        verbose_log!(
            verbose,
            "[Max-First Reduction] Target {} > total sum {}, impossible",
            target,
            total_sum
        );
        return AlgorithmResult::new(None, 0);
    }

    // Check if total sum equals target (take all)
    if target == total_sum {
        verbose_log!(
            verbose,
            "[Max-First Reduction] Target equals total sum, returning all numbers"
        );
        return AlgorithmResult::new(Some(sorted), 1);
    }

    // Check for single element solution
    if sorted.contains(&target) {
        verbose_log!(
            verbose,
            "[Max-First Reduction] Found single element solution: {}",
            target
        );
        return AlgorithmResult::new(Some(vec![target]), 1);
    }

    // Precompute prefix sums for pruning (sum of elements 0..=i)
    let mut prefix_sum = vec![0u64; n + 1];
    for i in 0..n {
        prefix_sum[i + 1] = prefix_sum[i].saturating_add(sorted[i]);
    }

    let mut result_subset: Option<Vec<u64>> = None;

    // Recursive helper that works from the end (largest) towards the start
    // Returns true if solution found
    fn recurse(
        sorted: &[u64],
        prefix_sum: &[u64],
        target: u64,
        end_idx: usize, // exclusive upper bound (elements 0..end_idx available)
        current_target: u64,
        subset: &mut Vec<u64>,
        steps: &mut u64,
        result: &mut Option<Vec<u64>>,
        verbose: bool,
    ) -> bool {
        *steps += 1;

        verbose_log!(
            verbose,
            "[Max-First Reduction] Step {}: end_idx={}, current_target={}, subset={:?}",
            steps,
            end_idx,
            current_target,
            subset
        );

        // Base case: found exact match
        if current_target == 0 {
            *result = Some(subset.clone());
            verbose_log!(
                verbose,
                "[Max-First Reduction] Found solution: {:?}",
                subset
            );
            return true;
        }

        // No more elements to consider
        if end_idx == 0 {
            return false;
        }

        // Pruning: even taking all remaining elements can't reach target
        if prefix_sum[end_idx] < current_target {
            verbose_log!(
                verbose,
                "[Max-First Reduction] Pruning: max possible sum {} < target {}",
                prefix_sum[end_idx],
                current_target
            );
            return false;
        }

        // Get the max element (last in the available range)
        let max_idx = end_idx - 1;
        let max_val = sorted[max_idx];

        // Case 1: max == current_target → found solution
        if max_val == current_target {
            subset.push(max_val);
            *result = Some(subset.clone());
            verbose_log!(
                verbose,
                "[Max-First Reduction] max={} equals target, found solution: {:?}",
                max_val,
                subset
            );
            return true;
        }

        // Case 2: max > current_target → skip this element entirely
        if max_val > current_target {
            verbose_log!(
                verbose,
                "[Max-First Reduction] max={} > target={}, skipping",
                max_val,
                current_target
            );
            return recurse(
                sorted,
                prefix_sum,
                target,
                max_idx,
                current_target,
                subset,
                steps,
                result,
                verbose,
            );
        }

        // Case 3: max < current_target → try including, then excluding
        subset.push(max_val);
        verbose_log!(
            verbose,
            "[Max-First Reduction] Including max={}, new_target={}",
            max_val,
            current_target - max_val
        );

        if recurse(
            sorted,
            prefix_sum,
            target,
            max_idx,
            current_target - max_val,
            subset,
            steps,
            result,
            verbose,
        ) {
            return true;
        }
        subset.pop();

        // Try excluding max
        verbose_log!(
            verbose,
            "[Max-First Reduction] Excluding max={}, continuing with smaller elements",
            max_val
        );

        recurse(
            sorted,
            prefix_sum,
            target,
            max_idx,
            current_target,
            subset,
            steps,
            result,
            verbose,
        )
    }

    recurse(
        &sorted,
        &prefix_sum,
        target,
        n,
        target,
        &mut Vec::new(),
        &mut steps,
        &mut result_subset,
        verbose,
    );

    verbose_log!(
        verbose,
        "[Max-First Reduction] Completed with {} steps",
        steps
    );
    AlgorithmResult::new(result_subset, steps)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_solution() {
        let input = InputSet::new(vec![3, 7, 1, 8, 4]).unwrap();
        let result = max_first_reduction(&input, 15, false);
        assert!(result.solution.is_some());
        let solution = result.solution.unwrap();
        assert_eq!(solution.iter().sum::<u64>(), 15);
    }

    #[test]
    fn test_no_solution() {
        let input = InputSet::new(vec![2, 4, 6, 8]).unwrap();
        let result = max_first_reduction(&input, 1, false);
        assert!(result.solution.is_none());
    }

    #[test]
    fn test_target_zero() {
        let input = InputSet::new(vec![1, 2, 3]).unwrap();
        let result = max_first_reduction(&input, 0, false);
        assert!(result.solution.is_some());
        assert!(result.solution.unwrap().is_empty());
    }

    #[test]
    fn test_single_element() {
        let input = InputSet::new(vec![5]).unwrap();
        let result = max_first_reduction(&input, 5, false);
        assert!(result.solution.is_some());
        assert_eq!(result.solution.unwrap(), vec![5]);
    }

    #[test]
    fn test_all_elements() {
        let input = InputSet::new(vec![1, 2, 3, 4]).unwrap();
        let result = max_first_reduction(&input, 10, false);
        assert!(result.solution.is_some());
        assert_eq!(result.solution.unwrap().iter().sum::<u64>(), 10);
    }

    #[test]
    fn test_max_first_behavior() {
        // When max is part of solution, should find it quickly
        let input = InputSet::new(vec![1, 2, 3, 10]).unwrap();
        let result = max_first_reduction(&input, 13, false); // 10 + 3 = 13
        assert!(result.solution.is_some());
        let solution = result.solution.unwrap();
        assert!(solution.contains(&10));
        assert_eq!(solution.iter().sum::<u64>(), 13);
    }

    #[test]
    fn test_large_numbers_filtered() {
        // Numbers > target should be filtered out
        let input = InputSet::new(vec![100, 200, 1, 2, 3]).unwrap();
        let result = max_first_reduction(&input, 6, false);
        assert!(result.solution.is_some());
        assert_eq!(result.solution.unwrap().iter().sum::<u64>(), 6);
    }

    #[test]
    fn test_impossible_target() {
        let input = InputSet::new(vec![1, 2, 3]).unwrap();
        let result = max_first_reduction(&input, 100, false);
        assert!(result.solution.is_none());
    }
}
