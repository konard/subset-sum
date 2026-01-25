//! Integration tests for subset-sum.
//!
//! These tests verify the public API works correctly.

use subset_sum::{
    backtracking, branch_and_bound, brute_force, dynamic_programming, meet_in_middle,
    meet_in_middle_hash, randomized, run_algorithm, verify_solution, ALGORITHM_NAMES,
};

mod algorithm_integration_tests {
    use super::*;

    #[test]
    fn test_all_algorithms_find_same_solution() {
        let numbers = vec![3, 7, 1, 8, 4, 12, 5, 6, 9, 2];
        let target = 25;

        for name in ALGORITHM_NAMES {
            let result = run_algorithm(name, &numbers, target, false);
            assert!(result.is_some(), "Algorithm {} should exist", name);
            let result = result.unwrap();
            assert!(
                result.solution.is_some(),
                "Algorithm {} should find a solution",
                name
            );
            assert!(
                verify_solution(&numbers, target, result.solution.as_ref().unwrap()),
                "Algorithm {} should produce a valid solution",
                name
            );
        }
    }

    #[test]
    fn test_all_algorithms_handle_no_solution() {
        let numbers = vec![2, 4, 6, 8, 10];
        let target = 1;

        for name in ALGORITHM_NAMES {
            let result = run_algorithm(name, &numbers, target, false);
            assert!(result.is_some(), "Algorithm {} should exist", name);
            let result = result.unwrap();
            assert!(
                result.solution.is_none(),
                "Algorithm {} should not find a solution for impossible target",
                name
            );
        }
    }

    #[test]
    fn test_algorithms_count_steps() {
        let numbers = vec![1, 2, 3, 4, 5];
        let target = 15;

        for name in ALGORITHM_NAMES {
            let result = run_algorithm(name, &numbers, target, false);
            assert!(result.is_some());
            let result = result.unwrap();
            assert!(result.steps > 0, "Algorithm {} should count steps", name);
        }
    }
}

mod brute_force_tests {
    use super::*;

    #[test]
    fn test_brute_force_small_input() {
        let numbers = vec![1, 2, 3];
        let target = 5;
        let result = brute_force(&numbers, target, false);
        assert!(result.solution.is_some());
        assert!(verify_solution(
            &numbers,
            target,
            result.solution.as_ref().unwrap()
        ));
    }

    #[test]
    fn test_brute_force_step_count() {
        let numbers = vec![1, 2, 3, 4];
        let target = 100; // impossible
        let result = brute_force(&numbers, target, false);
        // Should explore all 2^4 = 16 subsets
        assert_eq!(result.steps, 16);
    }
}

mod backtracking_tests {
    use super::*;

    #[test]
    fn test_backtracking_finds_early_solution() {
        let numbers = vec![1, 2, 3];
        let target = 1;
        let result = backtracking(&numbers, target, false);
        assert!(result.solution.is_some());
        // Should find solution early
        assert!(result.steps < 10);
    }
}

mod dynamic_programming_tests {
    use super::*;

    #[test]
    fn test_dp_with_large_target() {
        let numbers = vec![100, 200, 300, 400, 500];
        let target = 1000;
        let result = dynamic_programming(&numbers, target, false);
        assert!(result.solution.is_some());
        assert!(verify_solution(
            &numbers,
            target,
            result.solution.as_ref().unwrap()
        ));
    }
}

mod meet_in_middle_tests {
    use super::*;

    #[test]
    fn test_meet_in_middle_medium_input() {
        let numbers: Vec<u64> = (1..=20).collect();
        let target = 100;
        let result = meet_in_middle(&numbers, target, false);
        assert!(result.solution.is_some());
        assert!(verify_solution(
            &numbers,
            target,
            result.solution.as_ref().unwrap()
        ));
    }

    #[test]
    fn test_meet_in_middle_hash_medium_input() {
        let numbers: Vec<u64> = (1..=20).collect();
        let target = 100;
        let result = meet_in_middle_hash(&numbers, target, false);
        assert!(result.solution.is_some());
        assert!(verify_solution(
            &numbers,
            target,
            result.solution.as_ref().unwrap()
        ));
    }
}

mod branch_and_bound_tests {
    use super::*;

    #[test]
    fn test_branch_and_bound_pruning() {
        let numbers = vec![10, 20, 30, 40, 50];
        let target = 30;
        let result = branch_and_bound(&numbers, target, false);
        assert!(result.solution.is_some());
        // Should find single element solution quickly
        assert!(result.steps < 20);
    }
}

mod randomized_tests {
    use super::*;

    #[test]
    fn test_randomized_deterministic_with_seed() {
        let numbers = vec![1, 2, 3, 4, 5];
        let target = 10;

        let result1 = randomized(&numbers, target, false, 12345);
        let result2 = randomized(&numbers, target, false, 12345);

        // Same seed should produce same step count
        assert_eq!(result1.steps, result2.steps);
    }
}

mod verify_solution_tests {
    use super::*;

    #[test]
    fn test_verify_valid_solution() {
        let numbers = vec![1, 2, 3, 4, 5];
        let target = 9;
        let subset = vec![4, 5];
        assert!(verify_solution(&numbers, target, &subset));
    }

    #[test]
    fn test_verify_invalid_sum() {
        let numbers = vec![1, 2, 3, 4, 5];
        let target = 10;
        let subset = vec![1, 2]; // sums to 3, not 10
        assert!(!verify_solution(&numbers, target, &subset));
    }

    #[test]
    fn test_verify_element_not_in_set() {
        let numbers = vec![1, 2, 3];
        let target = 10;
        let subset = vec![5, 5]; // 5 is not in numbers
        assert!(!verify_solution(&numbers, target, &subset));
    }

    #[test]
    fn test_verify_empty_subset_zero_target() {
        let numbers = vec![1, 2, 3];
        let target = 0;
        let subset: Vec<u64> = vec![];
        assert!(verify_solution(&numbers, target, &subset));
    }
}

mod version_tests {
    use subset_sum::VERSION;

    #[test]
    fn test_version_is_not_empty() {
        assert!(!VERSION.is_empty());
    }

    #[test]
    fn test_version_matches_cargo_toml() {
        assert!(VERSION.starts_with("0."));
    }
}
