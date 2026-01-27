# Conjectures and Assumptions

This document lists the mathematical assumptions, properties, and conjectures that each subset sum algorithm relies upon for correctness and equivalence.

---

## Problem Definition

The **Subset Sum Problem**: Given a set (or multiset) of non-negative integers and a target sum, determine whether there exists a subset whose elements sum to exactly the target.

### Correctness Criteria

For an algorithm to be **correct**, it must:

- **Soundness**: If it returns a solution, that solution must be valid (sum equals target, all elements from input).

- **Completeness**: If a solution exists, the algorithm must find one (not necessarily unique).

- **Negative completeness**: If no solution exists, the algorithm must report failure (return None).

### Equivalence Criteria

All algorithms are **equivalent** if:

- **Same problem**: They all solve the subset sum decision/search problem.

- **Any solution suffices**: The problem only requires finding *some* valid subset, not a specific one or all of them. Different algorithms may return different valid solutions for the same input.

- **First solution termination**: All algorithms terminate upon finding the first valid solution. They do not continue searching for additional or "better" solutions.

- **Consistent verdict**: For any input, all algorithms agree on whether a solution exists.

- **Exploration order independence**: The order in which elements or subsets are explored (left-to-right, right-to-left, smallest-first, largest-first, random) affects which solution is found first, but not whether a solution is found.

---

## General Assumptions (All Algorithms)

These foundational assumptions apply to every algorithm in this library:

### Structural Assumptions

- **Set-unique-sequence equivalence**: A set is equivalent to an ordered sequence (array) containing no duplicate items. Each element appears exactly once in the sequence.

- **Set-sequence equivalence**: A set can be represented as an ordered sequence (array) with positional indexing. The order of elements does not affect which sums are achievable.

- **Multiset handling**: The input may contain duplicate values. Each *position* in the array is treated as a distinct element, even if values repeat. For input `[1, 1, 2]` with target `2`, both `[1, 1]` (positions 0,1) and `[2]` (position 2) are valid solutions.

- **Subset as index selection**: A subset corresponds to selecting a set of *indices* from the array. The subset's sum is the sum of values at those indices.

- **Bitmask-index correspondence**: A bitmask of n bits bijectively maps to subsets of an n-element array: bit `i` set means index `i` is included.

- **Finite representation**: We limit to 63 elements due to 64-bit bitmask representation (one bit reserved or avoiding sign issues).

### Arithmetic Assumptions

- **Non-negative integers**: All input numbers are natural numbers (non-negative integers ≥ 0).

- **Positive numbers enable pruning**: Most pruning strategies rely on numbers being positive (> 0). With positive numbers, adding elements can only increase the sum, enabling the anti-monotone property. Negative numbers would invalidate many pruning assumptions.

- **Exact integer arithmetic**: Integer addition is exact with no rounding errors (unlike floating-point).

- **Addition properties**: Integer addition is:
  - Associative: (a + b) + c = a + (b + c)
  - Commutative: a + b = b + a
  - Has identity: a + 0 = a

- **No overflow (or safe overflow)**: Sums do not overflow u64, or `saturating_add` correctly handles potential overflow by capping at u64::MAX.

- **Subtraction is inverse of addition**: For non-negative integers where a ≥ b, we have (a - b) + b = a. Used when computing `target - partial_sum`.

- **Equality decidability**: Two sums can be compared for equality in O(1) time.

- **Comparison operators correctness**: The operators `<`, `>`, `<=`, `>=`, `==` work correctly on u64 values and define a total ordering consistent with natural number ordering.

- **Bitwise operations correctness**: Left shift (`<<`), bitwise AND (`&`), OR (`|`), and XOR (`^`) operations work correctly on u64 values and correspond to their mathematical definitions.

### Subset Properties

- **Empty subset**: The empty subset (no elements selected) has sum 0.

- **Target zero solution**: If target = 0, the empty subset is always a valid solution.

- **Empty input handling**: If the input set is empty and target ≠ 0, no solution exists. If target = 0, the empty subset is the solution.

- **Unique usage**: Each element (by position) can be used at most once in any subset.

- **Finite search space**: For n elements, there are exactly 2^n possible subsets (including empty set).

- **Subset-sum well-defined**: For any subset S, sum(S) is uniquely determined by the multiset of values at selected positions.

- **Solution elements from input**: Any returned solution contains only values that appear in the input at the selected positions (no fabricated values).

### Practical/Implementation Assumptions

- **Zero contributes nothing**: Elements with value 0 can be excluded from consideration since they don't change any sum. Some algorithms filter `x >= 1`.

- **Sorting stability not required**: When sorting, equal elements are interchangeable for subset sum purposes. Algorithms may use unstable sort.

- **Sorting correctness**: The sort function produces a sequence where elements are ordered by their values (ascending or descending as specified). This enables index-based reasoning about relative magnitudes.

- **Recursion depth bounded**: For recursive algorithms, the recursion depth is at most n (the number of elements), which is assumed to fit within stack limits.

- **Hash function correctness**: Algorithms using HashSet or HashMap rely on the hash function correctly distributing values and the data structure correctly handling collisions.

- **Memory availability**: Algorithms assume sufficient memory is available for their data structures (e.g., DP table of size O(target), meet-in-middle storage of O(2^(n/2)) sums).

---

## Brute Force

**File**: `brute_force.rs` (function: `brute_force`)

### Assumptions

- **Completeness of enumeration**: Iterating through all 2^n bitmasks (0 to 2^n - 1) covers every possible subset exactly once.

- **Bitmask representation**: A bitmask where bit `i` is set corresponds to including element `i` in the subset.

- **No pruning correctness**: Checking every subset guarantees finding a solution if one exists.

### Complexity Basis

- **Time**: O(2^n) — must examine all subsets in worst case.
- **Space**: O(n) — only stores current subset being examined.

---

## Smart Brute Force

**File**: `brute_force.rs` (function: `smart_brute_force`)

### Assumptions

- **Filtering safety**: Numbers greater than target can be safely excluded — they cannot be part of any valid solution since all numbers are positive.

- **Sorting invariant**: Sorting numbers does not change the set of achievable sums (follows from commutativity of addition).

- **Equal values are interchangeable**: If multiple elements have the same value, any one of them can be used equivalently.

- **Power-of-two decomposition**: If the target can be expressed as a sum of distinct powers of two, and each required power of two exists in the input set, then that collection forms a valid solution.
  - Relies on: Every positive integer has a unique binary representation.

- **XOR complement property**: For a current sum `s` and target `t`, the value `s XOR t` identifies the bits that still need to be "filled in" to reach the target.

- **Early exit validity**: If `target < min(numbers)` or `target > sum(numbers)`, no solution exists.

- **Single element check**: If any element equals target, that single element is a valid solution.

- **Minimum and maximum bounds**: After filtering, if min or max equals target, we have an immediate solution.

### Complexity Basis

- **Time**: O(2^n) worst case, but optimizations provide early exits.
- **Space**: O(n).

---

## Backtracking

**File**: `backtracking.rs` (function: `backtracking`)

### Assumptions

- **Binary decision tree completeness**: For each element, making a binary choice (include/exclude) and recursing explores all 2^n subsets.

- **Early termination correctness**: Once `current_sum == target`, we can return immediately — the first solution found is valid.

- **Recursion termination**: The recursion terminates because the index increases monotonically until it exceeds the array length.

### Complexity Basis

- **Time**: O(2^n) worst case, but early termination often reduces this.
- **Space**: O(n) for recursion stack depth.

---

## Backtracking with Pruning

**File**: `backtracking.rs` (function: `backtracking_pruned`)

### Assumptions

- **Sorting enables pruning**: After sorting in ascending order, if adding the current (smallest remaining) element exceeds the target, all larger elements will also exceed it.

- **Anti-monotone property (positive numbers)**: If `current_sum > target`, then adding any more positive numbers will only increase the sum further — prune this branch.

- **Sorted iteration pruning**: When iterating through sorted elements, if `current_sum + nums[i] > target`, we can break the loop — all subsequent elements are larger.

- **Completeness despite pruning**: Pruning branches that exceed target does not eliminate any valid solutions (all numbers are positive).

### Complexity Basis

- **Time**: O(2^n) worst case, but significantly better average case.
- **Space**: O(n).

---

## Dynamic Programming

**File**: `dynamic_programming.rs` (function: `dynamic_programming`)

### Assumptions

- **Optimal substructure**: A sum `s` is achievable if and only if either:
  - `s = 0` (base case: empty subset), or
  - There exists some number `x` in the set such that `s - x` is achievable without using `x`.

- **Backward iteration prevents reuse**: Iterating from `target` down to `num` ensures each number is used at most once per achievable sum.

- **Boolean propagation**: `dp[s] = true` means sum `s` is achievable; this propagates correctly through the recurrence.

- **Solution reconstruction**: Parent pointers correctly track which number was added to reach each sum.

- **Pseudo-polynomial validity**: The algorithm's complexity depends on the *value* of the target, not just the *size* of the input — this is acceptable for the subset sum problem.

- **Target as array index**: The target value can be used as an array index, requiring O(target) memory. This assumes target is small enough to fit in addressable memory.

- **Practical memory limit**: The implementation limits target to 10,000,000 to prevent memory exhaustion.

- **Zero is achievable base case**: `dp[0] = true` because the empty subset achieves sum 0.

- **Numbers greater than target skipped**: Elements where `num > target` are skipped since they alone exceed the target and all numbers are positive.

### Complexity Basis

- **Time**: O(n × target) — pseudo-polynomial.
- **Space**: O(target) for the DP table.

---

## Incremental Pruning (Apriori-like)

**File**: `incremental_pruning.rs` (function: `incremental_pruning`)

### Assumptions

- **Level-wise completeness**: Building subsets by size (k = 1, 2, 3, ...) eventually explores all subsets.

- **Anti-monotone property**: If `sum(S) > target` for subset S, then `sum(S') > target` for all supersets S' ⊇ S.
  - Corollary: Pruning subsets that exceed target eliminates only invalid branches.

- **Extension correctness**: Extending a k-subset by one element produces a valid (k+1)-subset.

- **Bitmask subset representation**: A 64-bit bitmask can represent subsets of up to 63 elements.

- **Starting from pairs**: Beginning with pairs (k=2) after checking singletons (k=1) is complete — if a solution exists with k ≥ 2 elements, it will be found.

- **SubsetState equality**: Two SubsetState objects are equal if and only if they have the same bitmask. The HashSet correctly identifies and deduplicates identical subsets.

### Complexity Basis

- **Time**: O(2^n) worst case, but pruning can significantly reduce explored space.
- **Space**: O(C(n,k)) for storing subsets at level k.

---

## Max-First Reduction

**File**: `max_first_reduction.rs` (function: `max_first_reduction`)

### Assumptions

- **Filtering safety**: Numbers greater than target can be excluded — they cannot contribute to any solution.

- **Sorting preserves solutions**: Sorting does not change the set of achievable sums.

- **Max-first heuristic**: Processing elements from largest to smallest can lead to faster target reduction and earlier pruning.

- **Three-case exhaustiveness**: For any max value and current_target, exactly one of these holds:
  - `max == current_target`: max alone completes the solution.
  - `max > current_target`: max cannot be in the solution (must exclude).
  - `max < current_target`: try including max, then try excluding if no solution found.

  These three cases are mutually exclusive and exhaustive (trichotomy of comparison).

- **Prefix sum pruning**: If `sum(all remaining elements) < current_target`, no solution exists in this branch — prune.

- **Include-then-exclude completeness**: Trying to include an element first, then excluding it if unsuccessful, explores all possibilities.

- **Total sum check**: If `target == sum(all numbers)`, the solution is to take all elements.

- **Single element search**: Linear search (`contains`) correctly determines if target exists as a single element in the filtered set.

### Complexity Basis

- **Time**: O(2^n) worst case, but large elements reduce target quickly.
- **Space**: O(n) for recursion and prefix sums.

---

## Meet in the Middle

**File**: `meet_in_middle.rs` (function: `meet_in_middle`)

### Assumptions

- **Subset partitioning**: Any subset of the full array can be partitioned into a subset of the left half and a subset of the right half.

- **Sum decomposition**: If `sum(subset) = target`, then `sum(left_part) + sum(right_part) = target`, where left_part and right_part are the portions from each half.

- **Complement search**: For each right sum `r`, if there exists a left sum `l = target - r` in the left sums, then combining them yields a valid solution.

- **Binary search correctness**: After sorting left sums, binary search correctly finds a matching complement in O(log n) time.

- **Exponential reduction**: Splitting n elements into two halves reduces 2^n to 2 × 2^(n/2) = 2^(n/2 + 1).

- **Arbitrary split point**: The array can be split at any point (typically middle) without affecting correctness — any subset can still be reconstructed from left and right parts.

- **Independence of halves**: Computing all subset sums of the left half is independent of the right half, enabling the divide-and-conquer approach.

- **Practical size limit**: The implementation limits `mid` to 25 (effectively n ≈ 50) to prevent memory exhaustion from storing 2^(n/2) sums.

### Complexity Basis

- **Time**: O(2^(n/2) × log(2^(n/2))) = O(n × 2^(n/2)).
- **Space**: O(2^(n/2)) for storing left half sums.

---

## Meet in the Middle (Hash)

**File**: `meet_in_middle.rs` (function: `meet_in_middle_hash`)

### Assumptions

- **Same as Meet in the Middle**: Subset partitioning, sum decomposition, complement search, exponential reduction, arbitrary split point, independence of halves.

- **Hash map O(1) lookup**: Hash map provides expected O(1) lookup time for finding complements.

- **Hash collision handling**: The hash map correctly handles collisions and returns the correct mask for a given sum.

- **Any solution suffices**: When multiple left-half subsets have the same sum, storing only one mask is sufficient — we only need to find *any* valid solution, not all of them.

### Complexity Basis

- **Time**: O(2^(n/2)) with O(1) expected hash lookups.
- **Space**: O(2^(n/2)) for the hash map.

---

## Branch and Bound

**File**: `branch_and_bound.rs` (function: `branch_and_bound`)

### Assumptions

- **Sorting enables bounding**: Sorting allows precomputation of suffix sums for effective upper bounds.

- **Suffix sum upper bound**: `suffix_sum[i]` = sum of elements from index i to end provides the maximum possible sum from remaining elements.

- **Lower bound pruning**: If `current_sum + suffix_sum[index] < target`, the target is unreachable — prune.

- **Upper bound pruning**: If `current_sum > target`, we've exceeded the target — prune.

- **Include-before-exclude heuristic**: Trying to include elements before excluding them is a search strategy that can find solutions faster (but doesn't affect correctness).

- **Pruning preserves completeness**: Both pruning conditions only eliminate branches that cannot lead to valid solutions.

### Complexity Basis

- **Time**: O(2^n) worst case, but bounds often dramatically reduce search space.
- **Space**: O(n) for recursion stack and suffix sums.

---

## Randomized (Las Vegas)

**File**: `randomized.rs` (function: `randomized`)

### Assumptions

- **Completeness**: Exploring all 2^n subsets (in any order) guarantees finding a solution if one exists.

- **Fisher-Yates correctness**: The Fisher-Yates shuffle produces a uniformly random permutation of subset masks.

- **Order independence**: The order in which subsets are examined does not affect correctness, only performance.

- **Las Vegas property**: The algorithm always produces a correct result; only the running time is probabilistic.

- **LCG randomness**: The Linear Congruential Generator provides sufficient randomness for shuffling (not cryptographic, but adequate for search order).

### Complexity Basis

- **Time**: O(2^n) expected and worst case, but may find solutions faster with luck.
- **Space**: O(2^n) for storing shuffled masks.

---

## Optimization-Enabling Properties

The following properties must hold for various optimizations to preserve algorithm equivalence (i.e., not change whether a solution exists or is found).

### Filtering Optimizations

- **Large element filtering**: Elements where `value > target` can be removed from consideration.
  - *Requires*: All numbers are non-negative. A single element exceeding target cannot be part of any valid solution.

- **Zero element filtering**: Elements with `value = 0` can be removed from consideration.
  - *Requires*: Adding zero does not change any sum (`a + 0 = a`).

- **Duplicate value equivalence**: When multiple elements have the same value, any one can represent the others for solution purposes.
  - *Requires*: Commutativity of addition. The specific position doesn't affect the sum.

### Early Exit Optimizations

- **Target below minimum**: If `target < min(numbers)`, no solution exists.
  - *Requires*: All numbers are positive. The smallest possible non-empty subset sum is `min(numbers)`.

- **Target above total**: If `target > sum(all numbers)`, no solution exists.
  - *Requires*: All numbers are non-negative. Cannot exceed the sum of all elements.

- **Single element match**: If any `number == target`, that element alone is a valid solution.
  - *Requires*: A single-element subset is a valid subset. Its sum equals its sole element.

- **Total sum match**: If `sum(all numbers) == target`, taking all elements is a valid solution.
  - *Requires*: The full set is a valid subset.

### Pruning Optimizations (Search Space Reduction)

- **Upper bound pruning (sum exceeds target)**: If `current_sum > target`, prune this branch.
  - *Requires*: **Anti-monotone property** — all numbers are positive, so adding more elements only increases the sum. No superset of the current subset can have a smaller sum.

- **Lower bound pruning (can't reach target)**: If `current_sum + sum(remaining) < target`, prune this branch.
  - *Requires*: All numbers are non-negative. Even taking all remaining elements cannot reach the target.

- **Sorted iteration pruning**: After sorting ascending, if `current_sum + nums[i] > target`, skip all `nums[j]` where `j > i`.
  - *Requires*: Sorting correctness (ascending order). All subsequent elements are ≥ current element, so they would also exceed target.

- **Level-wise pruning (Apriori)**: If a k-subset exceeds target, don't extend it to (k+1)-subsets.
  - *Requires*: **Anti-monotone property** — adding elements to a subset can only increase its sum.

### Ordering Optimizations

- **Sorting invariance**: Sorting the input does not change which sums are achievable.
  - *Requires*: Commutativity of addition (`a + b = b + a`). Sum is independent of element order.

- **Exploration order freedom**: Elements can be explored in any order (ascending, descending, random).
  - *Requires*: The set of all subsets is the same regardless of traversal order. Only affects which solution is found first, not whether one exists.

- **Include/exclude order**: Trying "include" before "exclude" (or vice versa) doesn't affect correctness.
  - *Requires*: Both branches are eventually explored if needed. Order only affects which solution is found first.

### Decomposition Optimizations

- **Meet-in-the-middle split**: The array can be split at any index for divide-and-conquer.
  - *Requires*: **Subset partitioning** — any subset can be expressed as the union of a left-half subset and a right-half subset. **Sum decomposition** — `sum(left ∪ right) = sum(left) + sum(right)` when left and right are disjoint.

- **Binary representation decomposition**: Target can be decomposed into powers of two.
  - *Requires*: Every positive integer has a unique binary representation. If all required powers of two exist in the input, their sum equals target.

### Iteration Optimizations

- **Backward DP iteration**: Iterating from `target` down to `num` prevents element reuse.
  - *Requires*: When updating `dp[s]` based on `dp[s - num]`, the value `dp[s - num]` must reflect sums achievable *without* the current number. Backward iteration ensures we read the "old" value before writing the "new" value.

- **Early termination on solution**: Stop searching once a valid solution is found.
  - *Requires*: **Any solution suffices** — we only need to find one valid subset, not all of them or a specific one.

### Data Structure Optimizations

- **Hash-based complement lookup**: Using HashMap instead of binary search for meet-in-the-middle.
  - *Requires*: Hash function correctly maps sums to buckets. Collisions are handled correctly. Any mask for a given sum suffices (we don't need a specific one).

- **Bitmask subset encoding**: Using u64 bits to represent subset membership.
  - *Requires*: Bijection between bitmasks and subsets. Bit operations (`&`, `|`, `^`, `<<`) correctly manipulate set membership.

---

## Theoretical Foundation

### NP-Completeness

The subset sum problem is NP-complete. This implies:

- **No known polynomial algorithm**: Unless P = NP, no algorithm can solve all instances in polynomial time with respect to input size.

- **Exponential worst case**: All known exact algorithms have exponential worst-case complexity.

- **Pseudo-polynomial exception**: Dynamic programming is O(n × target), which is polynomial in the *value* of target but exponential in the *bit length* of target.

### Why Pruning Works

Most pruning strategies rely on the **anti-monotone property** of sums with positive numbers:

> If the current partial sum exceeds the target, adding more positive numbers will only increase it further.

This allows early termination of entire subtrees of the search space.

### Meet in the Middle Insight

The key insight is that:

> 2^n = 2^(n/2) × 2^(n/2)

By splitting the problem, we trade space for time, achieving O(2^(n/2)) time at the cost of O(2^(n/2)) space.
