//! Incremental pruning algorithm for the subset sum problem.
//!
//! This algorithm builds subsets level-by-level, starting from pairs (doublets)
//! and extending by one element at a time. It prunes subsets that exceed the
//! target sum, exploiting the anti-monotone property: if sum(S) > target,
//! then sum(S') > target for all supersets S' ⊇ S.
//!
//! This is similar to the Apriori algorithm from frequent itemset mining.

use crate::{verbose_log, AlgorithmResult};
use std::collections::HashSet;

/// Represents a subset as a bitmask and its sum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct SubsetState {
    /// Bitmask representing which elements are included
    mask: u64,
    /// Precomputed sum of the subset
    sum: u64,
}

impl SubsetState {
    const fn new(mask: u64, sum: u64) -> Self {
        Self { mask, sum }
    }

    /// Check if element at index i is in this subset
    const fn contains(&self, i: usize) -> bool {
        (self.mask & (1u64 << i)) != 0
    }

    /// Create a new subset by adding element at index i with value v
    const fn extend(&self, i: usize, v: u64) -> Self {
        Self {
            mask: self.mask | (1u64 << i),
            sum: self.sum.saturating_add(v),
        }
    }
}

/// Incremental pruning subset sum algorithm.
///
/// Builds subsets incrementally from pairs (doublets), extending each valid
/// subset by one element at a time. Prunes subsets that exceed the target,
/// preventing exploration of all their supersets.
///
/// # Algorithm
///
/// 1. Check for single-element solutions (k=1)
/// 2. Generate all pairs (k=2) with sum ≤ target
/// 3. For each level k, extend valid subsets by adding one unused element
/// 4. Prune subsets where sum > target (anti-monotone property)
/// 5. Return when solution found or no valid subsets remain
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
/// O(2^n) worst case, but with early pruning based on sum exceeding target.
/// Effective when many subsets exceed the target early.
///
/// # Space Complexity
///
/// O(C(n,k)) where k is the current level - stores all valid subsets at each level.
///
/// # Examples
///
/// ```
/// use subset_sum::incremental_pruning;
///
/// let numbers = vec![3, 7, 1, 8, 4];
/// let result = incremental_pruning(&numbers, 15, false);
/// assert!(result.solution.is_some());
/// ```
#[must_use]
pub fn incremental_pruning(numbers: &[u64], target: u64, verbose: bool) -> AlgorithmResult {
    let n = numbers.len();
    let mut steps: u64 = 0;

    verbose_log!(
        verbose,
        "[Incremental Pruning] Starting with {} numbers, target={}",
        n,
        target
    );
    verbose_log!(verbose, "[Incremental Pruning] Numbers: {:?}", numbers);

    // Handle edge cases
    if target == 0 {
        verbose_log!(
            verbose,
            "[Incremental Pruning] Target is 0, returning empty subset"
        );
        return AlgorithmResult::new(Some(Vec::new()), 0);
    }

    if n == 0 {
        verbose_log!(verbose, "[Incremental Pruning] No numbers provided");
        return AlgorithmResult::new(None, 0);
    }

    // Limit to 63 bits for bitmask representation
    if n > 63 {
        verbose_log!(
            verbose,
            "[Incremental Pruning] Too many numbers ({}), falling back to first 63",
            n
        );
    }
    let n = n.min(63);

    // Check for single-element solutions (k=1)
    verbose_log!(
        verbose,
        "[Incremental Pruning] Checking single elements (k=1)"
    );
    for (i, &num) in numbers.iter().take(n).enumerate() {
        steps += 1;
        if num == target {
            verbose_log!(
                verbose,
                "[Incremental Pruning] Found single element solution: {}",
                num
            );
            return AlgorithmResult::new(Some(vec![num]), steps);
        }
        verbose_log!(
            verbose,
            "[Incremental Pruning] Element {} = {} (not equal to target)",
            i,
            num
        );
    }

    // Generate initial pairs (k=2) - the "doublets"
    verbose_log!(verbose, "[Incremental Pruning] Generating pairs (k=2)");
    let mut current_level: HashSet<SubsetState> = HashSet::new();

    for i in 0..n {
        for j in (i + 1)..n {
            steps += 1;
            let sum = numbers[i].saturating_add(numbers[j]);
            let mask = (1u64 << i) | (1u64 << j);

            if sum == target {
                verbose_log!(
                    verbose,
                    "[Incremental Pruning] Found pair solution: {} + {} = {}",
                    numbers[i],
                    numbers[j],
                    target
                );
                return AlgorithmResult::new(Some(vec![numbers[i], numbers[j]]), steps);
            }

            if sum < target {
                let state = SubsetState::new(mask, sum);
                current_level.insert(state);
                verbose_log!(
                    verbose,
                    "[Incremental Pruning] Valid pair: {} + {} = {} (keeping)",
                    numbers[i],
                    numbers[j],
                    sum
                );
            } else {
                verbose_log!(
                    verbose,
                    "[Incremental Pruning] Pair {} + {} = {} exceeds target (pruning)",
                    numbers[i],
                    numbers[j],
                    sum
                );
            }
        }
    }

    verbose_log!(
        verbose,
        "[Incremental Pruning] After k=2: {} valid subsets",
        current_level.len()
    );

    // Extend level by level (k=3, 4, 5, ...)
    let mut k = 2usize;
    while !current_level.is_empty() && k < n {
        k += 1;
        verbose_log!(
            verbose,
            "[Incremental Pruning] Extending to k={}, starting with {} subsets",
            k,
            current_level.len()
        );

        let mut next_level: HashSet<SubsetState> = HashSet::new();

        for state in &current_level {
            // Try adding each element not already in the subset
            for i in 0..n {
                if state.contains(i) {
                    continue;
                }

                steps += 1;
                let new_state = state.extend(i, numbers[i]);

                if new_state.sum == target {
                    // Found solution! Reconstruct the subset
                    let solution: Vec<u64> = (0..n)
                        .filter(|&j| new_state.contains(j))
                        .map(|j| numbers[j])
                        .collect();
                    verbose_log!(
                        verbose,
                        "[Incremental Pruning] Found solution at k={}: {:?}",
                        k,
                        solution
                    );
                    return AlgorithmResult::new(Some(solution), steps);
                }

                if new_state.sum < target {
                    // Only keep subsets that don't exceed target
                    next_level.insert(new_state);
                }
                // If sum > target, this subset and all its supersets are pruned
            }
        }

        verbose_log!(
            verbose,
            "[Incremental Pruning] After k={}: {} valid subsets",
            k,
            next_level.len()
        );

        current_level = next_level;
    }

    verbose_log!(
        verbose,
        "[Incremental Pruning] No solution found after {} steps",
        steps
    );
    AlgorithmResult::new(None, steps)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_solution() {
        let numbers = vec![3, 7, 1, 8, 4];
        let result = incremental_pruning(&numbers, 15, false);
        assert!(result.solution.is_some());
        let solution = result.solution.unwrap();
        assert_eq!(solution.iter().sum::<u64>(), 15);
    }

    #[test]
    fn test_no_solution() {
        let numbers = vec![2, 4, 6, 8];
        let result = incremental_pruning(&numbers, 1, false);
        assert!(result.solution.is_none());
    }

    #[test]
    fn test_target_zero() {
        let numbers = vec![1, 2, 3];
        let result = incremental_pruning(&numbers, 0, false);
        assert!(result.solution.is_some());
        assert!(result.solution.unwrap().is_empty());
    }

    #[test]
    fn test_single_element() {
        let numbers = vec![5];
        let result = incremental_pruning(&numbers, 5, false);
        assert!(result.solution.is_some());
        assert_eq!(result.solution.unwrap(), vec![5]);
    }

    #[test]
    fn test_pair_solution() {
        let numbers = vec![3, 7, 10];
        let result = incremental_pruning(&numbers, 10, false);
        assert!(result.solution.is_some());
        let solution = result.solution.unwrap();
        assert_eq!(solution.iter().sum::<u64>(), 10);
    }

    #[test]
    fn test_pruning_effectiveness() {
        // Large numbers should get pruned early
        let numbers = vec![100, 200, 300, 1, 2, 3];
        let result = incremental_pruning(&numbers, 6, false);
        assert!(result.solution.is_some());
        assert_eq!(result.solution.unwrap().iter().sum::<u64>(), 6);
        // Steps should be relatively low due to pruning
    }

    #[test]
    fn test_larger_subset() {
        let numbers = vec![1, 2, 3, 4, 5];
        let result = incremental_pruning(&numbers, 12, false);
        assert!(result.solution.is_some());
        assert_eq!(result.solution.unwrap().iter().sum::<u64>(), 12);
    }
}
