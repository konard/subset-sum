//! Integration tests for subset-sum.
//!
//! These tests verify the public API works correctly.

use subset_sum::{
    backtracking, branch_and_bound, brute_force, dynamic_programming, meet_in_middle,
    meet_in_middle_hash, randomized, run_algorithm, verify_solution, InputSet, InputSetError,
    ALGORITHM_NAMES,
};

mod algorithm_integration_tests {
    use super::*;

    #[test]
    fn test_all_algorithms_find_same_solution() {
        let input = InputSet::new(vec![3, 7, 1, 8, 4, 12, 5, 6, 9, 2]).unwrap();
        let target = 25;

        for name in ALGORITHM_NAMES {
            let result = run_algorithm(name, &input, target, false);
            assert!(result.is_some(), "Algorithm {} should exist", name);
            let result = result.unwrap();
            assert!(
                result.solution.is_some(),
                "Algorithm {} should find a solution",
                name
            );
            assert!(
                verify_solution(input.numbers(), target, result.solution.as_ref().unwrap()),
                "Algorithm {} should produce a valid solution",
                name
            );
        }
    }

    #[test]
    fn test_all_algorithms_handle_no_solution() {
        let input = InputSet::new(vec![2, 4, 6, 8, 10]).unwrap();
        let target = 1;

        for name in ALGORITHM_NAMES {
            let result = run_algorithm(name, &input, target, false);
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
        let input = InputSet::new(vec![1, 2, 3, 4, 5]).unwrap();
        let target = 15;

        for name in ALGORITHM_NAMES {
            let result = run_algorithm(name, &input, target, false);
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
        let input = InputSet::new(vec![1, 2, 3]).unwrap();
        let target = 5;
        let result = brute_force(&input, target, false);
        assert!(result.solution.is_some());
        assert!(verify_solution(
            input.numbers(),
            target,
            result.solution.as_ref().unwrap()
        ));
    }

    #[test]
    fn test_brute_force_step_count() {
        let input = InputSet::new(vec![1, 2, 3, 4]).unwrap();
        let target = 100; // impossible
        let result = brute_force(&input, target, false);
        // Should explore all 2^4 = 16 subsets
        assert_eq!(result.steps, 16);
    }
}

mod backtracking_tests {
    use super::*;

    #[test]
    fn test_backtracking_finds_early_solution() {
        let input = InputSet::new(vec![1, 2, 3]).unwrap();
        let target = 1;
        let result = backtracking(&input, target, false);
        assert!(result.solution.is_some());
        // Should find solution early
        assert!(result.steps < 10);
    }
}

mod dynamic_programming_tests {
    use super::*;

    #[test]
    fn test_dp_with_large_target() {
        let input = InputSet::new(vec![100, 200, 300, 400, 500]).unwrap();
        let target = 1000;
        let result = dynamic_programming(&input, target, false);
        assert!(result.solution.is_some());
        assert!(verify_solution(
            input.numbers(),
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
        let input = InputSet::new(numbers).unwrap();
        let target = 100;
        let result = meet_in_middle(&input, target, false);
        assert!(result.solution.is_some());
        assert!(verify_solution(
            input.numbers(),
            target,
            result.solution.as_ref().unwrap()
        ));
    }

    #[test]
    fn test_meet_in_middle_hash_medium_input() {
        let numbers: Vec<u64> = (1..=20).collect();
        let input = InputSet::new(numbers).unwrap();
        let target = 100;
        let result = meet_in_middle_hash(&input, target, false);
        assert!(result.solution.is_some());
        assert!(verify_solution(
            input.numbers(),
            target,
            result.solution.as_ref().unwrap()
        ));
    }
}

mod branch_and_bound_tests {
    use super::*;

    #[test]
    fn test_branch_and_bound_pruning() {
        let input = InputSet::new(vec![10, 20, 30, 40, 50]).unwrap();
        let target = 30;
        let result = branch_and_bound(&input, target, false);
        assert!(result.solution.is_some());
        // Should find single element solution quickly
        assert!(result.steps < 20);
    }
}

mod randomized_tests {
    use super::*;

    #[test]
    fn test_randomized_deterministic_with_seed() {
        let input = InputSet::new(vec![1, 2, 3, 4, 5]).unwrap();
        let target = 10;

        let result1 = randomized(&input, target, false, 12345);
        let result2 = randomized(&input, target, false, 12345);

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

mod input_set_tests {
    use super::*;

    #[test]
    fn test_input_set_rejects_duplicates() {
        let result = InputSet::new(vec![1, 2, 3, 3, 4]);
        assert!(result.is_err());
        match result {
            Err(InputSetError::DuplicateValues(dups)) => {
                assert!(dups.contains(&3));
            }
            _ => panic!("Expected DuplicateValues error"),
        }
    }

    #[test]
    fn test_input_set_rejects_multiple_duplicates() {
        let result = InputSet::new(vec![1, 1, 2, 2, 3]);
        assert!(result.is_err());
        match result {
            Err(InputSetError::DuplicateValues(dups)) => {
                assert!(dups.contains(&1));
                assert!(dups.contains(&2));
            }
            _ => panic!("Expected DuplicateValues error"),
        }
    }

    #[test]
    fn test_input_set_rejects_empty() {
        let result = InputSet::new(vec![]);
        assert!(result.is_err());
        match result {
            Err(InputSetError::EmptyInput) => {}
            _ => panic!("Expected EmptyInput error"),
        }
    }

    #[test]
    fn test_input_set_rejects_zero() {
        let result = InputSet::new(vec![1, 0, 3]);
        assert!(result.is_err());
        match result {
            Err(InputSetError::ContainsZero) => {}
            _ => panic!("Expected ContainsZero error"),
        }
    }

    #[test]
    fn test_input_set_sorts_numbers() {
        let input = InputSet::new(vec![5, 3, 1, 4, 2]).unwrap();
        assert_eq!(input.numbers(), &[1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_input_set_computes_min_max_sum() {
        let input = InputSet::new(vec![5, 3, 1, 4, 2]).unwrap();
        assert_eq!(input.min(), 1);
        assert_eq!(input.max(), 5);
        assert_eq!(input.total_sum(), 15);
        assert_eq!(input.len(), 5);
    }

    #[test]
    fn test_input_set_is_target_achievable() {
        let input = InputSet::new(vec![1, 2, 3]).unwrap();
        assert!(input.is_target_achievable(6)); // total_sum
        assert!(input.is_target_achievable(1)); // min
        assert!(input.is_target_achievable(0)); // empty subset sums to 0
        assert!(!input.is_target_achievable(7)); // more than total_sum
    }

    #[test]
    fn test_input_set_error_display() {
        let err = InputSetError::DuplicateValues(vec![3, 5]);
        let msg = err.to_string();
        assert!(msg.contains("duplicate"));
        assert!(msg.contains('3'));
        assert!(msg.contains('5'));

        let err = InputSetError::EmptyInput;
        assert!(err.to_string().contains("empty"));

        let err = InputSetError::ContainsZero;
        assert!(err.to_string().contains("zero"));
    }
}
