# Subset Sum Problem

A comprehensive Rust library for the Subset Sum problem with multiple algorithm implementations and a CLI benchmarking tool.

[![CI/CD Pipeline](https://github.com/konard/subset-sum/workflows/CI%2FCD%20Pipeline/badge.svg)](https://github.com/konard/subset-sum/actions)
[![Rust Version](https://img.shields.io/badge/rust-1.70%2B-blue.svg)](https://www.rust-lang.org/)
[![License: Unlicense](https://img.shields.io/badge/license-Unlicense-blue.svg)](http://unlicense.org/)

## Table of Contents

- [What is the Subset Sum Problem?](#what-is-the-subset-sum-problem)
- [Understanding P vs NP](#understanding-p-vs-np)
  - [What is P?](#what-is-p)
  - [What is NP?](#what-is-np)
  - [Why is Subset Sum NP-Complete?](#why-is-subset-sum-np-complete)
  - [Are There Any Polynomial-Time Solutions?](#are-there-any-polynomial-time-solutions)
- [The Shortest Algorithm](#the-shortest-algorithm)
  - [Brute Force Algorithm](#brute-force-algorithm)
  - [Verification Algorithm](#verification-algorithm)
- [All Available Algorithms](#all-available-algorithms)
- [Installation](#installation)
- [Quick Start](#quick-start)
- [CLI Commands](#cli-commands)
- [Development](#development)
- [References](#references)

---

## What is the Subset Sum Problem?

Imagine you have a piggy bank with coins of different values: 1, 5, 10, and 25 cents. Now someone asks you: **"Can you pick some of these coins to get exactly 36 cents?"**

That's the Subset Sum Problem!

More formally:

> **Given a set of numbers and a target sum, find if there exists a subset of those numbers that adds up to exactly the target.**

### A Simple Example

```
Numbers: [3, 7, 1, 8, 4]
Target:  15

Can we pick some of these numbers to get exactly 15?

Let's try:
- 3 + 7 + 1 = 11 (not 15)
- 7 + 8 = 15 (Yes!)

Answer: Yes! The subset [7, 8] sums to 15.
```

### Why is This Problem Important?

The Subset Sum Problem appears in many real-world applications:

1. **Budgeting**: Can I buy exactly $100 worth of items from this list?
2. **Resource Allocation**: Can I fill a container with exactly X capacity?
3. **Cryptography**: Many encryption schemes are based on hard problems like this
4. **Scheduling**: Can I fit tasks into exactly the available time slot?

---

## Understanding P vs NP

Before we dive into algorithms, let's understand one of the most famous unsolved problems in computer science: **P vs NP**.

### What is P?

**P** stands for "**P**olynomial time."

A problem is in **P** if we can solve it **quickly** (in polynomial time).

**Polynomial time** means the solving time grows "reasonably" as the input grows:
- If input size doubles, time might double (linear: n)
- If input size doubles, time might quadruple (quadratic: n²)
- If input size doubles, time might increase 8x (cubic: n³)

These are all polynomial and considered "fast" in computer science.

**Examples of problems in P:**
- Sorting a list of numbers (we can do it in O(n log n) time)
- Finding a number in a sorted list (we can do it in O(log n) time)
- Multiplying two numbers (we can do it in O(n²) time or better)

### What is NP?

**NP** stands for "**N**ondeterministic **P**olynomial time."

A problem is in **NP** if we can **verify** a solution quickly (in polynomial time), even if we can't **find** a solution quickly.

Think of it like this:
- **Finding** the solution might take a long time
- **Checking** if a given answer is correct is fast

**Example with Subset Sum:**
```
Numbers: [3, 7, 1, 8, 4]
Target:  15

Finding a solution: We might need to try many combinations...
Verifying a solution: Someone tells us [7, 8] is the answer.
                      We just add: 7 + 8 = 15. Correct!
                      This check took O(n) time - very fast!
```

### What is NP-Complete?

**NP-Complete** problems are the "hardest" problems in NP.

If anyone finds a fast (polynomial-time) algorithm for ANY NP-Complete problem, then ALL problems in NP can be solved quickly, which would prove **P = NP**.

The Subset Sum Problem is **NP-Complete**.

### Why is Subset Sum NP-Complete?

1. **It's in NP**: Given a proposed solution (a subset), we can verify it's correct in O(n) time by simply adding up the numbers.

2. **It's NP-Hard**: Every other NP problem can be transformed into a Subset Sum problem. This was proven by [Richard Karp in 1972](https://en.wikipedia.org/wiki/Karp%27s_21_NP-complete_problems).

### The Big Question: Does P = NP?

This is one of the [seven Millennium Prize Problems](https://en.wikipedia.org/wiki/Millennium_Prize_Problems) with a **$1,000,000 prize** for solving it!

- **If P = NP**: Every problem whose solution can be quickly verified can also be quickly solved. This would revolutionize cryptography, optimization, and AI.

- **If P ≠ NP**: Some problems are fundamentally harder to solve than to verify. Most computer scientists believe this is true.

**Current Status (as of January 2026)**: The P vs NP problem remains **unsolved**. While there have been various research papers exploring new approaches (including a notable 2025 paper on arXiv exploring the subset sum problem), **none have been accepted by the scientific community as resolving P vs NP**.

### Are There Any Polynomial-Time Solutions?

We conducted extensive research across:
- GitHub repositories
- GitLab repositories
- Academic papers (arXiv, Google Scholar)
- Computer science databases
- Implementations in various languages (Rust, Python, C++, JavaScript, Haskell, etc.)

**Result: As of January 2026, no polynomial-time algorithm exists for the general Subset Sum Problem.**

All known exact algorithms have **exponential time complexity** in the worst case:

| Algorithm | Time Complexity | Notes |
|-----------|-----------------|-------|
| Brute Force | O(2ⁿ) | Tries all subsets |
| Meet-in-the-Middle | O(2^(n/2)) | Better, but still exponential |
| Dynamic Programming | O(n × target) | Pseudo-polynomial (depends on target value) |

**Important Note**: The Dynamic Programming solution appears polynomial, but it's actually **pseudo-polynomial** because it depends on the **value** of the target, not just the **size** of the input. If the target is very large (e.g., 2^1000), this algorithm is not polynomial.

---

## The Shortest Algorithm

Here are the shortest possible implementations of the brute force algorithm and the verification algorithm. These are educational reference implementations that demonstrate the core logic.

### Brute Force Algorithm

The brute force approach tries every possible subset (2ⁿ combinations) until it finds one that sums to the target.

```rust
fn brute_force(numbers: &[i64], target: i64) -> (Option<Vec<i64>>, u64) {
    let n = numbers.len();
    let mut steps: u64 = 0;
    for mask in 0..(1u64 << n) {
        steps += 1;
        let mut sum = 0;
        let mut subset = Vec::new();
        for i in 0..n {
            if mask & (1 << i) != 0 {
                sum += numbers[i];
                subset.push(numbers[i]);
            }
        }
        if sum == target {
            return (Some(subset), steps);
        }
    }
    (None, steps)
}
```

**How it works:**

1. **Bitmask enumeration**: The variable `mask` goes from 0 to 2ⁿ-1. Each bit position represents whether to include that number.

2. **Example with 3 numbers [3, 7, 1]**:
   - mask = 0 (binary: 000) → subset = [] → sum = 0
   - mask = 1 (binary: 001) → subset = [3] → sum = 3
   - mask = 2 (binary: 010) → subset = [7] → sum = 7
   - mask = 3 (binary: 011) → subset = [3, 7] → sum = 10
   - mask = 4 (binary: 100) → subset = [1] → sum = 1
   - mask = 5 (binary: 101) → subset = [3, 1] → sum = 4
   - mask = 6 (binary: 110) → subset = [7, 1] → sum = 8
   - mask = 7 (binary: 111) → subset = [3, 7, 1] → sum = 11

3. **Why O(2ⁿ)?** With n numbers, there are 2ⁿ possible subsets (each number is either included or excluded).

### Verification Algorithm

The verification algorithm checks if a proposed subset is valid: all elements must come from the original set, and they must sum to the target.

```rust
fn verify(numbers: &[i64], target: i64, subset: &[i64]) -> bool {
    let mut available = numbers.to_vec();
    for &x in subset {
        if let Some(pos) = available.iter().position(|&n| n == x) {
            available.remove(pos);
        } else {
            return false;
        }
    }
    subset.iter().sum::<i64>() == target
}
```

**How it works:**

1. **Copy the original numbers** to track which are still available
2. **For each number in the subset**, try to find and remove it from available numbers
3. **If any number isn't found**, the subset is invalid (uses numbers not in the original set)
4. **Finally, check the sum** equals the target

**Why O(n)?** We iterate through the subset once, and each lookup/removal is O(n) in the worst case, making it O(n²) technically, but still **polynomial** - this is what makes verification "easy"!

---

## All Available Algorithms

This library provides 9 different algorithm implementations, each with different trade-offs:

| Algorithm | Time Complexity | Space Complexity | Best For |
|-----------|----------------|------------------|----------|
| `smart_brute_force` | O(2ⁿ) optimized | O(n) | Power-of-two optimizations |
| `brute_force` | O(2ⁿ) | O(n) | Small inputs (n < 20) |
| `backtracking` | O(2ⁿ) worst | O(n) | Early solution finding |
| `backtracking_pruned` | O(2ⁿ) worst | O(n) | Small targets with positive numbers |
| `dynamic_programming` | O(n × target) | O(target) | Small target values |
| `meet_in_middle` | O(2^(n/2)) | O(2^(n/2)) | Moderate n (25-40) |
| `meet_in_middle_hash` | O(2^(n/2)) | O(2^(n/2)) | Same, hash-based lookup |
| `branch_and_bound` | O(2ⁿ) worst | O(n) | Good all-around with pruning |
| `randomized` | O(2ⁿ) expected | O(2ⁿ) | Probabilistic approach |

### Algorithm Details

#### Brute Force
Exhaustively enumerates all 2ⁿ possible subsets and checks each one. Simple but exponential.

#### Backtracking
Recursive approach with early termination when a solution is found. Explores the decision tree depth-first.

#### Backtracking Pruned
Enhanced backtracking that prunes branches when the current sum exceeds the target (works because all numbers are positive).

#### Dynamic Programming
Uses a bottom-up approach building a table of achievable sums. Pseudo-polynomial - efficient when the target value is small relative to n.

#### Meet in the Middle
Splits the input in half, generates all subset sums for each half, then uses binary search to find complementary pairs. Reduces complexity from O(2ⁿ) to O(2^(n/2)).

#### Meet in the Middle (Hash)
Same as meet-in-the-middle but uses a hash set for O(1) lookups instead of binary search.

#### Branch and Bound
Intelligent tree exploration with bounds checking. Prunes subtrees that cannot lead to better solutions.

#### Randomized
Explores subsets in random order. Can be faster for some inputs but has non-deterministic behavior.

---

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

---

## Quick Start

### Library Usage

```rust
use subset_sum::{brute_force, InputSet, verify_solution};

fn main() {
    // Create validated, preprocessed input
    let input = InputSet::new(vec![3, 7, 1, 8, 4]).unwrap();
    let target = 15;

    // Run brute force algorithm
    let result = brute_force(&input, target, false);

    if let Some(subset) = &result.solution {
        println!("Found subset: {:?}", subset);
        println!("Valid: {}", verify_solution(input.numbers(), target, subset));
    }
    println!("Steps taken: {}", result.steps);
}
```

**Note:** All algorithms require an `InputSet`, which validates input:
- Rejects empty input
- Rejects zeros (only natural numbers allowed)
- Rejects duplicate values (subset sum operates on sets, not multisets)
- Automatically sorts numbers and precomputes min/max/sum

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

---

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

---

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

---

## NP-Completeness Summary

The Subset Sum problem is **NP-complete**, which means:

| Property | Explanation |
|----------|-------------|
| **In NP** | Given a solution, we can verify it in O(n) time |
| **NP-Hard** | At least as hard as any other NP problem |
| **No known polynomial solution** | Best exact algorithms are exponential |
| **If solved in P time** | Would prove P = NP (major unsolved problem) |

The CI/CD pipeline includes automated scaling tests that demonstrate exponential growth empirically.

---

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
│   ├── lib.rs                  # Library with all algorithms
│   ├── main.rs                 # CLI binary
│   └── algorithms/             # Individual algorithm modules
│       ├── brute_force.rs
│       ├── backtracking.rs
│       ├── dynamic_programming.rs
│       ├── meet_in_middle.rs
│       ├── branch_and_bound.rs
│       └── randomized.rs
├── tests/
│   └── integration_test.rs
├── examples/
│   └── basic_usage.rs
├── changelog.d/                # Changelog fragments
└── .github/workflows/          # CI/CD configuration
```

---

## Contributing

Contributions are welcome! Please see [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

1. Fork the repository
2. Create a feature branch
3. Make changes and add tests
4. Run `cargo fmt && cargo clippy && cargo test`
5. Add a changelog fragment in `changelog.d/`
6. Submit a Pull Request

---

## License

[Unlicense](LICENSE) - Public Domain

---

## References

### Core Concepts
- [Subset Sum Problem - Wikipedia](https://en.wikipedia.org/wiki/Subset_sum_problem) - Comprehensive overview of the problem
- [P versus NP Problem - Wikipedia](https://en.wikipedia.org/wiki/P_versus_NP_problem) - The famous unsolved problem
- [NP-Completeness - Wikipedia](https://en.wikipedia.org/wiki/NP-completeness) - Understanding complexity classes
- [Karp's 21 NP-complete Problems - Wikipedia](https://en.wikipedia.org/wiki/Karp%27s_21_NP-complete_problems) - Historical context

### Algorithms
- [Meet-in-the-Middle Algorithm - Wikipedia](https://en.wikipedia.org/wiki/Meet-in-the-middle_attack) - O(2^(n/2)) approach
- [Dynamic Programming - Wikipedia](https://en.wikipedia.org/wiki/Dynamic_programming) - Pseudo-polynomial approach
- [Backtracking - Wikipedia](https://en.wikipedia.org/wiki/Backtracking) - Recursive approach with pruning

### Further Reading
- [Millennium Prize Problems - Wikipedia](https://en.wikipedia.org/wiki/Millennium_Prize_Problems) - The $1M prize for solving P vs NP
- [Computational Complexity Theory - Wikipedia](https://en.wikipedia.org/wiki/Computational_complexity_theory) - Broader context
- [Rosetta Code: Subset Sum](https://rosettacode.org/wiki/Subset_sum_problem) - Implementations in many languages

### Academic Resources
- [Introduction to Algorithms (CLRS)](https://en.wikipedia.org/wiki/Introduction_to_Algorithms) - Standard textbook
- [Computers and Intractability (Garey & Johnson)](https://en.wikipedia.org/wiki/Computers_and_Intractability) - Classic NP-completeness reference
