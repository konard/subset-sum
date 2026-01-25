---
bump: major
---

### Added
- Complete subset sum algorithm library with 9 implementations:
  - Smart Brute Force (O(2^n) optimized with power-of-two detection) - by konard
  - Brute Force (O(2^n))
  - Backtracking (O(2^n) worst case)
  - Backtracking Pruned (O(2^n) worst case with sum-based pruning)
  - Dynamic Programming (O(n × target) pseudo-polynomial)
  - Meet in the Middle (O(2^(n/2)))
  - Meet in the Middle with Hash (O(2^(n/2)))
  - Branch and Bound (O(2^n) worst case with intelligent pruning)
  - Randomized (O(2^n) expected)
- CLI tool with subcommands:
  - `run`: Execute single algorithm with configurable parameters
  - `benchmark`: Compare all algorithms on same input
  - `list`: Show available algorithms
  - `scaling-test`: Demonstrate exponential growth
- Verbose mode for step-by-step execution logging
- Step counting for algorithm performance comparison
- Input validation for natural numbers (u64, non-zero)
- CI/CD scaling demonstration job showing non-polynomial growth

### Changed
- Replaced template placeholder code with subset sum implementation
- Updated README with algorithm documentation and usage examples
