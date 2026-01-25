# subset-sum

A comprehensive Rust library for the Subset Sum problem with multiple algorithm implementations and a CLI benchmarking tool.

[![CI/CD Pipeline](https://github.com/konard/subset-sum/workflows/CI%2FCD%20Pipeline/badge.svg)](https://github.com/konard/subset-sum/actions)
[![Rust Version](https://img.shields.io/badge/rust-1.70%2B-blue.svg)](https://www.rust-lang.org/)
[![License: Unlicense](https://img.shields.io/badge/license-Unlicense-blue.svg)](http://unlicense.org/)

## The Problem

The **Subset Sum Problem** is a classic NP-complete problem in computer science:

> Given a set of natural numbers and a target sum, determine if there exists a subset that adds up to exactly the target sum.

This library provides 8 different algorithm implementations to solve this problem, each with different time/space complexity trade-offs.

## Features

- **8 Algorithm Implementations**: From brute force to advanced meet-in-the-middle
- **CLI Tool**: Benchmark and compare algorithms with various inputs
- **Verbose Mode**: Step-by-step execution logging for learning
- **Step Counting**: Track computational steps for algorithm comparison
- **Natural Numbers Only**: Works with positive integers (u64)
- **CI/CD Integration**: Automated scaling tests demonstrate non-polynomial growth

## Installation

### As a Library

Add to your `Cargo.toml`:

```toml
[dependencies]
subset-sum = "0.1"
```

### As a CLI Tool

```bash
cargo install subset-sum
```

Or build from source:

```bash
git clone https://github.com/konard/subset-sum.git
cd subset-sum
cargo build --release
```

## Quick Start

### Library Usage

```rust
use subset_sum::{brute_force, dynamic_programming, verify_solution};

fn main() {
    let numbers = vec![3, 7, 1, 8, 4];
    let target = 15;

    // Run brute force algorithm
    let result = brute_force(&numbers, target, false);

    if let Some(subset) = &result.solution {
        println!("Found subset: {:?}", subset);
        println!("Valid: {}", verify_solution(&numbers, target, subset));
    }
    println!("Steps taken: {}", result.steps);
}
```

### CLI Usage

```bash
# Run a single algorithm
subset-sum run -t 25 -n "3 7 1 8 4 12 5 6 9 2" -a brute_force

# Compare all algorithms
subset-sum benchmark -t 25 -n "3 7 1 8 4 12 5 6 9 2"

# List available algorithms
subset-sum list

# Run scaling test to see exponential growth
subset-sum scaling-test --start-size 5 --end-size 20 -a brute_force
```

## Algorithms

| Algorithm | Time Complexity | Space Complexity | Best For |
|-----------|----------------|------------------|----------|
| `brute_force` | O(2^n) | O(n) | Small inputs (n < 20) |
| `backtracking` | O(2^n) worst | O(n) | Early solution finding |
| `backtracking_pruned` | O(2^n) worst | O(n) | Small targets with positive numbers |
| `dynamic_programming` | O(n × target) | O(target) | Small target values |
| `meet_in_middle` | O(2^(n/2)) | O(2^(n/2)) | Moderate n (25-40), any target |
| `meet_in_middle_hash` | O(2^(n/2)) | O(2^(n/2)) | Same as above, hash-based lookup |
| `branch_and_bound` | O(2^n) worst | O(n) | Good all-around with pruning |
| `randomized` | O(2^n) expected | O(2^n) | Probabilistic approach |

### Algorithm Details

#### Brute Force
Exhaustively enumerates all 2^n possible subsets and checks each one. Simple but exponential.

#### Backtracking
Recursive approach with early termination when a solution is found. Explores the decision tree depth-first.

#### Backtracking Pruned
Enhanced backtracking that prunes branches when the current sum exceeds the target (works because all numbers are positive).

#### Dynamic Programming
Uses a bottom-up approach building a table of achievable sums. Pseudo-polynomial - efficient when the target value is small relative to n.

#### Meet in the Middle
Splits the input in half, generates all subset sums for each half, then uses binary search to find complementary pairs. Reduces complexity from O(2^n) to O(2^(n/2)).

#### Meet in the Middle (Hash)
Same as meet-in-the-middle but uses a hash set for O(1) lookups instead of binary search.

#### Branch and Bound
Intelligent tree exploration with bounds checking. Prunes subtrees that cannot lead to better solutions.

#### Randomized
Explores subsets in random order. Can be faster for some inputs but has non-deterministic behavior.

## CLI Commands

### `run` - Execute Single Algorithm

```bash
subset-sum run [OPTIONS] -t <TARGET_SUM> -n <NUMBERS_SET>

Options:
  -t, --target-sum <TARGET_SUM>    Target sum to find (natural number > 0)
  -n, --numbers-set <NUMBERS_SET>  Space-separated list of natural numbers
  -a, --algorithm <ALGORITHM>      Algorithm to use [default: brute_force]
  -v, --verbose                    Enable verbose output showing each step
```

### `benchmark` - Compare All Algorithms

```bash
subset-sum benchmark [OPTIONS] -t <TARGET_SUM> -n <NUMBERS_SET>

Options:
  -t, --target-sum <TARGET_SUM>    Target sum to find
  -n, --numbers-set <NUMBERS_SET>  Space-separated list of natural numbers
  -v, --verbose                    Enable verbose output
      --skip <SKIP>                Algorithms to skip (comma-separated)
```

### `scaling-test` - Demonstrate Exponential Growth

```bash
subset-sum scaling-test [OPTIONS]

Options:
      --start-size <START_SIZE>  Starting size of input array [default: 5]
      --end-size <END_SIZE>      Ending size of input array [default: 20]
      --step <STEP>              Size increment [default: 1]
  -a, --algorithm <ALGORITHM>    Algorithm to test [default: brute_force]
      --format <FORMAT>          Output format (table or csv) [default: table]
```

### `list` - Show Available Algorithms

```bash
subset-sum list
```

## Example Output

### Benchmark Comparison

```
╔══════════════════════════════════════════════════════════════════╗
║           SUBSET SUM ALGORITHM COMPARISON                        ║
╚══════════════════════════════════════════════════════════════════╝

Numbers: [3, 7, 1, 8, 4, 12, 5, 6, 9, 2]
Target: 25
Input size (n): 10

Algorithm                      Steps     Time (µs)     Result
------------------------- ------------ ------------ ----------
brute_force                       1024          120      FOUND
backtracking                        15            2      FOUND
backtracking_pruned                 12            1      FOUND
dynamic_programming                260           15      FOUND
meet_in_middle                      96           10      FOUND
meet_in_middle_hash                 96            8      FOUND
branch_and_bound                    18            2      FOUND
randomized                         128           12      FOUND
```

### Scaling Test

```
Scaling Test for: brute_force
Testing exponential growth of computational steps

    n           Steps     Time (µs)             2^n      Ratio
----- --------------- ------------ --------------- ----------
    5              32            5              32     1.0000
   10            1024           50            1024     1.0000
   15           32768         1500           32768     1.0000
   20         1048576        52000         1048576     1.0000

Note: Steps grow exponentially with n (2^n), demonstrating
that the Subset Sum problem has no known polynomial-time solution.
This is consistent with its NP-complete classification.
```

## NP-Completeness

The Subset Sum problem is **NP-complete**, meaning:

1. **No polynomial-time solution is known** - All known exact algorithms have exponential worst-case complexity
2. **Verification is polynomial** - Given a proposed solution, we can verify it in O(n) time
3. **It's as hard as any NP problem** - If we could solve it in polynomial time, we could solve all NP problems efficiently (P = NP)

The CI/CD pipeline includes automated scaling tests that demonstrate this exponential growth empirically.

## Development

### Running Tests

```bash
# All tests
cargo test

# With verbose output
cargo test --verbose

# Doc tests only
cargo test --doc

# Run specific test
cargo test test_brute_force
```

### Code Quality

```bash
# Format code
cargo fmt

# Run lints
cargo clippy --all-targets --all-features

# Run example
cargo run --example basic_usage
```

### Project Structure

```
.
├── src/
│   ├── lib.rs          # Library with all algorithms
│   └── main.rs         # CLI binary
├── tests/
│   └── integration_test.rs
├── examples/
│   └── basic_usage.rs
├── changelog.d/        # Changelog fragments
└── .github/workflows/  # CI/CD configuration
```

## Contributing

Contributions are welcome! Please see [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

1. Fork the repository
2. Create a feature branch
3. Make changes and add tests
4. Run `cargo fmt && cargo clippy && cargo test`
5. Add a changelog fragment in `changelog.d/`
6. Submit a Pull Request

## License

[Unlicense](LICENSE) - Public Domain

## References

- [Subset Sum Problem - Wikipedia](https://en.wikipedia.org/wiki/Subset_sum_problem)
- [NP-Completeness - Wikipedia](https://en.wikipedia.org/wiki/NP-completeness)
- [Meet-in-the-Middle Algorithm](https://en.wikipedia.org/wiki/Meet-in-the-middle_attack)
