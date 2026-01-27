//! Meet in the middle algorithms for the subset sum problem.

use std::collections::HashMap;

use crate::{verbose_log, AlgorithmResult, InputSet};

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
/// O(2^(n/2) * log(2^(n/2))) = O(n * 2^(n/2))
///
/// # Examples
///
/// ```
/// use subset_sum::{meet_in_middle, InputSet};
///
/// let input = InputSet::new(vec![3, 7, 1, 8, 4]).unwrap();
/// let result = meet_in_middle(&input, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn meet_in_middle(input: &InputSet, target: u64, verbose: bool) -> AlgorithmResult {
    let numbers = input.numbers();
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
/// O(2^(n/2)) with O(1) hash lookups
///
/// # Examples
///
/// ```
/// use subset_sum::{meet_in_middle_hash, InputSet};
///
/// let input = InputSet::new(vec![3, 7, 1, 8, 4]).unwrap();
/// let result = meet_in_middle_hash(&input, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn meet_in_middle_hash(input: &InputSet, target: u64, verbose: bool) -> AlgorithmResult {
    let numbers = input.numbers();
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
