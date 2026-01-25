//! Randomized algorithm for the subset sum problem.

use crate::{verbose_log, AlgorithmResult};

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
