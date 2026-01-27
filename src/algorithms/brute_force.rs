//! Brute force algorithms for the subset sum problem.

use crate::{verbose_log, AlgorithmResult};

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

    verbose_log!(verbose, "[Smart Brute Force] ---");

    for &number in &sorted_numbers {
        verbose_log!(verbose, "[Smart Brute Force] {:064b}", number);
    }

    verbose_log!(verbose, "[Smart Brute Force] ---");

    verbose_log!(verbose, "[Smart Brute Force] {:064b}", target);

    verbose_log!(verbose, "[Smart Brute Force] ---");

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


// def can_sum(numbers, target):
//     # Используем bitset-оптимизацию (в Python это работа с большими числами)
//     # Это невероятно быстрый способ для задачи Subset Sum
//     possible_sums = 1
//     for x in numbers:
//         possible_sums |= (possible_sums << x)
//         # Если бит на позиции target стал 1, значит сумма найдена
//         if (possible_sums >> target) & 1:
//             return True
//     return (possible_sums >> target) & 1

// # Генерируем 10 000 случайных чисел
// import random
// numbers = [random.randint(1, 100) for _ in range(10000)]
// target = 5000 # Пример суммы

// import time
// start = time.time()
// result = can_sum(numbers, target)
// print(f"Результат: {result}, Время: {time.time() - start:.4f} сек")


    // Can 0000000000000000000000000000000000000000000000000000000000000001 be satisfied?

    let mut digit_place: u64 = 1;

    // required?

    // while  {
    //     for &number in &sorted_numbers {
    //         // Can digit place be satisfied?
    //         if (number & digit_place) == digit_place {
                
    //         }

            
    //     }
    //     digit_place <<= 1;
    // }

    // for all required digit places in target:

    // // Find highest digit place in target
    // while digit_place <= target {
    //     digit_place <<= 1;
    // }
    // digit_place >>= 1;

    // Find all set bits in all numbers
    let mut set_bits_in_numbers: u64 = 0;
    for &number in &sorted_numbers {
        set_bits_in_numbers |= number;
    }

    while digit_place <= target {
        // // Is this digit place required by target?
        // if (target & digit_place) > 0 {
        //     // Is this digit place available in all numbers?
        //     if (set_bits_in_numbers & digit_place) == 0 {
        //         verbose_log!(
        //             verbose,
        //             "[Smart Brute Force] Missing required digit place {:064b}, should be no solution",
        //             digit_place
        //         );
        //         return AlgorithmResult::new(None, 0);
        //     } else {
        //         verbose_log!(
        //             verbose,
        //             "[Smart Brute Force] Required digit place {:064b} is available",
        //             digit_place
        //         );
        //     }
        // }

        digit_place <<= 1;
    }
    
    // while digit_place > 0 {
    //     verbose_log!(
    //         verbose,
    //         "[Smart Brute Force] Checking digit place: {:064b}",
    //         digit_place
    //     );

    //     // Is this digit place required by target?
    //     if (target & digit_place) > 0 {
    //         // Is this digit place available in all numbers?
    //         if (set_bits_in_numbers & digit_place) == 0 {
    //             verbose_log!(
    //                 verbose,
    //                 "[Smart Brute Force] Missing required digit place {:064b}, should be no solution",
    //                 digit_place
    //             );

    //             // Can it be constructed from the previous digit places?
                

    //             // return AlgorithmResult::new(None, 0);
    //         } else {
    //             verbose_log!(
    //                 verbose,
    //                 "[Smart Brute Force] Required digit place {:064b} is available",
    //                 digit_place
    //             );
    //         }
    //     }

    //     digit_place >>= 1;
    // }


    // let mut steps: u64 = 0;

    // for i in 0..n {
    //     let first_number = sorted_numbers[i];
    //     let mut possible_sum: u64 = first_number;
    //     let mut missing_powers_of_two = possible_sum ^ target;
    //     let mut subset: Vec<u64> = vec![first_number];

    //     for j in (i + 1)..n {
    //         steps += 1;

    //         let second_number = sorted_numbers[j];

    //         if (second_number & missing_powers_of_two) == second_number {
    //             possible_sum = possible_sum.saturating_add(second_number);
    //             missing_powers_of_two = possible_sum ^ target;
    //             subset.push(second_number);
    //         }

    //         if possible_sum == target {
    //             verbose_log!(
    //                 verbose,
    //                 "[Smart Brute Force] Found solution during preprocessing: {:?}",
    //                 subset
    //             );
    //             return AlgorithmResult::new(Some(subset), steps);
    //         }
    //     }
    // }

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
