//! Branch and bound algorithm for the subset sum problem.

use crate::{verbose_log, AlgorithmResult, InputSet};

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
/// O(2^n) worst case, but often much better with good pruning
///
/// # Examples
///
/// ```
/// use subset_sum::{branch_and_bound, InputSet};
///
/// let input = InputSet::new(vec![3, 7, 1, 8, 4]).unwrap();
/// let result = branch_and_bound(&input, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn branch_and_bound(input: &InputSet, target: u64, verbose: bool) -> AlgorithmResult {
    // Input is already sorted, create indexed version
    let numbers = input.numbers();
    let sorted: Vec<(u64, usize)> = numbers
        .iter()
        .copied()
        .enumerate()
        .map(|(i, x)| (x, i))
        .collect();

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
    verbose_log!(verbose, "[Branch and Bound] Numbers: {:?}", sorted);

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
