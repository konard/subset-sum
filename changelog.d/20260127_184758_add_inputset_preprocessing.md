---
bump: minor
---

### Added
- New `InputSet` struct for validated, preprocessed algorithm input
- `InputSetError` enum for clear input validation error messages
- Duplicate value rejection with descriptive error messages
- Precomputed min, max, and total_sum for input sets

### Changed
- All 11 algorithms now accept `InputSet` instead of raw slices
- Benchmarks no longer include sorting/validation time in measurements
- CLI validates input and provides clear error messages for invalid input

### Removed
- Redundant internal sorting from algorithms (backtracking_pruned, branch_and_bound, smart_brute_force, max_first_reduction)
