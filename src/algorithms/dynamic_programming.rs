//! Dynamic programming algorithm for the subset sum problem.

use crate::{verbose_log, AlgorithmResult};

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
