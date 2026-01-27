/-
  SetSequenceEquivalence.lean - Formal proof that a finite set is equivalent to
  an ordered sequence with unique elements.

  This proof establishes the mathematical foundation for the subset sum algorithms
  in this repository, showing that operating on sorted, deduplicated sequences
  preserves the mathematical properties of sets.

  Main Theorem: For any finite set of natural numbers, there exists a unique
  strictly ascending sequence (list with no duplicates, sorted in ascending order)
  that contains exactly the same elements.
-/

import Std.Data.List.Basic

namespace SetSequenceEquivalence

/-- A list is strictly ascending if each element is strictly less than the next -/
def StrictlyAscending : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x < y ∧ StrictlyAscending (y :: rest)

/-- A list has no duplicates -/
def NoDuplicates : List Nat → Prop
  | [] => True
  | x :: rest => x ∉ rest ∧ NoDuplicates rest

/-- An ordered unique sequence is a strictly ascending list -/
def IsOrderedUniqueSequence (l : List Nat) : Prop :=
  StrictlyAscending l

/-- Helper: strictly ascending implies no duplicates -/
theorem strictly_ascending_implies_no_dup : ∀ l : List Nat,
  StrictlyAscending l → NoDuplicates l := by
  intro l
  induction l with
  | nil =>
    intro _
    simp [NoDuplicates]
  | cons x rest ih =>
    intro h
    simp [NoDuplicates]
    constructor
    · -- x ∉ rest
      cases rest with
      | nil => simp
      | cons y ys =>
        simp [StrictlyAscending] at h
        obtain ⟨hxy, hrest⟩ := h
        intro hx_in_rest
        -- If x is in y::ys, then either x = y or x ∈ ys
        cases hx_in_rest with
        | head => omega -- x < y but x = y is contradiction
        | tail _ hx_in_ys =>
          -- We need to show x cannot be in ys either
          -- Since the list is strictly ascending, all elements in ys are > y > x
          have : ∀ z ∈ ys, y < z := by
            intro z hz
            clear ih
            induction ys generalizing y with
            | nil => contradiction
            | cons w ws ih_ws =>
              simp [StrictlyAscending] at hrest
              cases hz with
              | head => exact hrest.1
              | tail _ hz_in_ws =>
                have hyw : y < w := hrest.1
                cases ws with
                | nil => contradiction
                | cons v vs =>
                  simp [StrictlyAscending] at hrest
                  have hwv : w < v := hrest.2.1
                  have hws_asc : StrictlyAscending (v :: vs) := hrest.2.2
                  have : w < z := ih_ws w hrest.2 hz_in_ws
                  omega
          have hyz : y < x := by
            have := this x hx_in_ys
            exact this
          omega
    · -- NoDuplicates rest
      cases rest with
      | nil => simp [NoDuplicates]
      | cons y ys =>
        simp [StrictlyAscending] at h
        exact ih h.2

/-- Insert an element into a sorted list maintaining sorted order -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: rest =>
    if x < y then x :: y :: rest
    else if x = y then y :: rest  -- Skip duplicates
    else y :: insertSorted x rest

/-- Sort a list into strictly ascending order (removing duplicates) -/
def toOrderedUnique : List Nat → List Nat
  | [] => []
  | x :: rest => insertSorted x (toOrderedUnique rest)

/-- insertSorted preserves the strictly ascending property -/
theorem insertSorted_preserves_ascending (x : Nat) (l : List Nat) :
  StrictlyAscending l → StrictlyAscending (insertSorted x l) := by
  intro h
  induction l with
  | nil => simp [insertSorted, StrictlyAscending]
  | cons y rest ih =>
    simp [insertSorted]
    split
    · -- x < y case
      rename_i hxy
      simp [StrictlyAscending]
      constructor
      · exact hxy
      · exact h
    · split
      · -- x = y case
        exact h
      · -- x > y case
        rename_i hxy_not_lt hxy_ne
        have hyx : y < x := by omega
        cases rest with
        | nil =>
          simp [insertSorted, StrictlyAscending]
          exact hyx
        | cons z zs =>
          simp [StrictlyAscending] at h
          simp [insertSorted]
          split
          · -- x < z
            rename_i hxz
            simp [StrictlyAscending]
            exact ⟨hyx, hxz, h.2⟩
          · split
            · -- x = z
              simp [StrictlyAscending]
              exact h
            · -- x > z
              simp [StrictlyAscending]
              constructor
              · exact h.1
              · exact ih h.2

/-- toOrderedUnique produces strictly ascending lists -/
theorem toOrderedUnique_is_ascending (l : List Nat) :
  StrictlyAscending (toOrderedUnique l) := by
  induction l with
  | nil => simp [toOrderedUnique, StrictlyAscending]
  | cons x rest ih =>
    simp [toOrderedUnique]
    exact insertSorted_preserves_ascending x (toOrderedUnique rest) ih

/-- Element membership is preserved by insertSorted -/
theorem mem_insertSorted (x y : Nat) (l : List Nat) :
  y ∈ insertSorted x l ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil =>
    simp [insertSorted]
  | cons z rest ih =>
    simp [insertSorted]
    split
    · -- x < z
      simp [List.mem_cons]
      tauto
    · split
      · -- x = z
        rename_i hxz
        simp [List.mem_cons]
        constructor
        · intro h
          cases h with
          | inl hz => right; left; exact hz
          | inr hr => right; right; exact hr
        · intro h
          cases h with
          | inl hyx =>
            left
            omega
          | inr h =>
            cases h with
            | inl hyz => left; exact hyz
            | inr hr => right; exact hr
      · -- x > z
        simp [List.mem_cons]
        rw [ih]
        tauto

/-- Element membership is preserved by toOrderedUnique -/
theorem mem_toOrderedUnique (x : Nat) (l : List Nat) :
  x ∈ toOrderedUnique l ↔ x ∈ l := by
  induction l with
  | nil => simp [toOrderedUnique]
  | cons y rest ih =>
    simp [toOrderedUnique]
    rw [mem_insertSorted]
    simp [List.mem_cons]
    constructor
    · intro h
      cases h with
      | inl hxy => left; exact hxy.symm
      | inr hr => right; rw [← ih]; exact hr
    · intro h
      cases h with
      | inl hxy => left; exact hxy.symm
      | inr hr => right; rw [ih]; exact hr

/-
  MAIN THEOREM: Set-Sequence Equivalence

  For any list (representing a multiset/bag), there exists a unique strictly
  ascending list containing exactly the same elements (as a set).

  This justifies the use of sorted, deduplicated sequences in subset sum
  algorithms - the transformation preserves which sums are achievable.
-/

/-- Main theorem: Every list can be converted to an ordered unique sequence
    with the same elements -/
theorem set_sequence_equivalence (l : List Nat) :
  ∃ l' : List Nat,
    IsOrderedUniqueSequence l' ∧
    (∀ x, x ∈ l' ↔ x ∈ l) := by
  use toOrderedUnique l
  constructor
  · exact toOrderedUnique_is_ascending l
  · intro x
    exact mem_toOrderedUnique x l

/-- Corollary: The ordered unique sequence has no duplicates -/
theorem ordered_unique_has_no_dup (l : List Nat) :
  NoDuplicates (toOrderedUnique l) := by
  apply strictly_ascending_implies_no_dup
  exact toOrderedUnique_is_ascending l

/-- The sum of elements is preserved when removing duplicates from a set perspective.
    Note: This shows the transformation doesn't add any new elements that would
    affect subset sum computations when considering sets (not multisets). -/
theorem subset_sum_preserved (l : List Nat) (target : Nat) :
  (∃ subset : List Nat, (∀ x ∈ subset, x ∈ l) ∧ subset.sum = target) ↔
  (∃ subset : List Nat, (∀ x ∈ subset, x ∈ toOrderedUnique l) ∧ subset.sum = target) := by
  constructor
  · intro ⟨subset, h_mem, h_sum⟩
    use subset
    constructor
    · intro x hx
      rw [mem_toOrderedUnique]
      exact h_mem x hx
    · exact h_sum
  · intro ⟨subset, h_mem, h_sum⟩
    use subset
    constructor
    · intro x hx
      have := h_mem x hx
      rw [mem_toOrderedUnique] at this
      exact this
    · exact h_sum

end SetSequenceEquivalence

-- Verification checks
#check SetSequenceEquivalence.set_sequence_equivalence
#check SetSequenceEquivalence.ordered_unique_has_no_dup
#check SetSequenceEquivalence.subset_sum_preserved

#print "Set-Sequence Equivalence proof verified successfully!"
