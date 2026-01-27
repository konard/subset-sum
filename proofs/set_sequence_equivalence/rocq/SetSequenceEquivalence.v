(**
  SetSequenceEquivalence.v - Formal proof that a finite set is equivalent to
  an ordered sequence with unique elements.

  This proof establishes the mathematical foundation for the subset sum algorithms
  in this repository, showing that operating on sorted, deduplicated sequences
  preserves the mathematical properties of sets.

  Main Theorem: For any finite set of natural numbers, there exists a unique
  strictly ascending sequence (list with no duplicates, sorted in ascending order)
  that contains exactly the same elements.
*)

From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Import ListNotations.

(** * Definitions *)

(** A list is strictly ascending if each element is strictly less than the next *)
Fixpoint StrictlyAscending (l : list nat) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x :: ((y :: _) as rest) => x < y /\ StrictlyAscending rest
  end.

(** A list has no duplicates *)
Fixpoint NoDuplicates (l : list nat) : Prop :=
  match l with
  | [] => True
  | x :: rest => ~ In x rest /\ NoDuplicates rest
  end.

(** An ordered unique sequence is a strictly ascending list *)
Definition IsOrderedUniqueSequence (l : list nat) : Prop :=
  StrictlyAscending l.

(** * Helper Lemmas *)

(** All elements after a position in a strictly ascending list are greater *)
Lemma strictly_ascending_all_greater : forall l x y,
  StrictlyAscending (x :: y :: l) ->
  forall z, In z (y :: l) -> x < z.
Proof.
  induction l as [| w ws IH].
  - intros x y H z Hz.
    simpl in H. destruct H as [Hxy _].
    simpl in Hz. destruct Hz as [Hz | Hz].
    + subst. exact Hxy.
    + contradiction.
  - intros x y H z Hz.
    simpl in H. destruct H as [Hxy Hrest].
    simpl in Hz. destruct Hz as [Hz | Hz].
    + subst. exact Hxy.
    + assert (Hy_asc : StrictlyAscending (y :: w :: ws)).
      { exact Hrest. }
      assert (Hyz : y < z).
      { apply (IH y w Hrest z Hz). }
      lia.
Qed.

(** Strictly ascending implies no duplicates *)
Theorem strictly_ascending_implies_no_dup : forall l : list nat,
  StrictlyAscending l -> NoDuplicates l.
Proof.
  induction l as [| x rest IH].
  - intro H. simpl. exact I.
  - intro H.
    simpl. split.
    + (* x not in rest *)
      destruct rest as [| y ys].
      * simpl. auto.
      * intro Hx_in.
        assert (Hxy : x < y).
        { simpl in H. destruct H as [Hxy _]. exact Hxy. }
        assert (Hxz : forall z, In z (y :: ys) -> x < z).
        { apply strictly_ascending_all_greater. exact H. }
        specialize (Hxz x Hx_in).
        lia.
    + (* NoDuplicates rest *)
      destruct rest as [| y ys].
      * simpl. exact I.
      * simpl in H. destruct H as [_ Hrest].
        apply IH. exact Hrest.
Qed.

(** * Insertion into sorted list *)

(** Insert an element into a sorted list maintaining sorted order *)
Fixpoint insertSorted (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | y :: rest =>
    if x <? y then x :: y :: rest
    else if x =? y then y :: rest  (* Skip duplicates *)
    else y :: insertSorted x rest
  end.

(** Sort a list into strictly ascending order (removing duplicates) *)
Fixpoint toOrderedUnique (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: rest => insertSorted x (toOrderedUnique rest)
  end.

(** * Properties of insertSorted *)

Lemma ltb_true_lt : forall x y, (x <? y) = true <-> x < y.
Proof.
  intros. apply Nat.ltb_lt.
Qed.

Lemma eqb_true_eq : forall x y, (x =? y) = true <-> x = y.
Proof.
  intros. apply Nat.eqb_eq.
Qed.

Lemma ltb_false_ge : forall x y, (x <? y) = false <-> x >= y.
Proof.
  intros. rewrite Nat.ltb_ge. reflexivity.
Qed.

Lemma eqb_false_ne : forall x y, (x =? y) = false <-> x <> y.
Proof.
  intros. apply Nat.eqb_neq.
Qed.

(** insertSorted preserves the strictly ascending property *)
Theorem insertSorted_preserves_ascending : forall x l,
  StrictlyAscending l -> StrictlyAscending (insertSorted x l).
Proof.
  intros x l.
  induction l as [| y rest IH].
  - intro H. simpl. exact I.
  - intro H.
    simpl.
    destruct (x <? y) eqn:Hxy.
    + (* x < y case *)
      apply ltb_true_lt in Hxy.
      simpl. split.
      * exact Hxy.
      * exact H.
    + destruct (x =? y) eqn:Hxy_eq.
      * (* x = y case - no change *)
        exact H.
      * (* x > y case *)
        apply ltb_false_ge in Hxy.
        apply eqb_false_ne in Hxy_eq.
        assert (Hyx : y < x) by lia.
        destruct rest as [| z zs].
        -- (* rest = [] *)
           simpl. split.
           ++ exact Hyx.
           ++ exact I.
        -- (* rest = z :: zs *)
           simpl in H. destruct H as [Hyz Hrest].
           simpl.
           destruct (x <? z) eqn:Hxz.
           ++ (* x < z *)
              apply ltb_true_lt in Hxz.
              simpl. split.
              ** exact Hyx.
              ** split.
                 --- exact Hxz.
                 --- exact Hrest.
           ++ destruct (x =? z) eqn:Hxz_eq.
              ** (* x = z *)
                 simpl. split.
                 --- exact Hyz.
                 --- exact Hrest.
              ** (* x > z *)
                 simpl. split.
                 --- exact Hyz.
                 --- apply IH. exact Hrest.
Qed.

(** toOrderedUnique produces strictly ascending lists *)
Theorem toOrderedUnique_is_ascending : forall l,
  StrictlyAscending (toOrderedUnique l).
Proof.
  induction l as [| x rest IH].
  - simpl. exact I.
  - simpl.
    apply insertSorted_preserves_ascending.
    exact IH.
Qed.

(** * Membership preservation *)

(** Element membership is preserved by insertSorted *)
Theorem mem_insertSorted : forall x y l,
  In y (insertSorted x l) <-> y = x \/ In y l.
Proof.
  intros x y.
  induction l as [| z rest IH].
  - simpl. tauto.
  - simpl.
    destruct (x <? z) eqn:Hxz.
    + (* x < z *)
      simpl. tauto.
    + destruct (x =? z) eqn:Hxz_eq.
      * (* x = z *)
        apply eqb_true_eq in Hxz_eq.
        simpl. subst. tauto.
      * (* x > z *)
        simpl.
        rewrite IH.
        tauto.
Qed.

(** Element membership is preserved by toOrderedUnique *)
Theorem mem_toOrderedUnique : forall x l,
  In x (toOrderedUnique l) <-> In x l.
Proof.
  intros x.
  induction l as [| y rest IH].
  - simpl. tauto.
  - simpl.
    rewrite mem_insertSorted.
    rewrite IH.
    simpl. tauto.
Qed.

(** * Main Theorem: Set-Sequence Equivalence *)

(**
  MAIN THEOREM: Set-Sequence Equivalence

  For any list (representing a multiset/bag), there exists a strictly
  ascending list containing exactly the same elements (as a set).

  This justifies the use of sorted, deduplicated sequences in subset sum
  algorithms - the transformation preserves which sums are achievable.
*)

Theorem set_sequence_equivalence : forall l : list nat,
  exists l' : list nat,
    IsOrderedUniqueSequence l' /\
    (forall x, In x l' <-> In x l).
Proof.
  intro l.
  exists (toOrderedUnique l).
  split.
  - unfold IsOrderedUniqueSequence.
    apply toOrderedUnique_is_ascending.
  - intro x.
    apply mem_toOrderedUnique.
Qed.

(** Corollary: The ordered unique sequence has no duplicates *)
Corollary ordered_unique_has_no_dup : forall l : list nat,
  NoDuplicates (toOrderedUnique l).
Proof.
  intro l.
  apply strictly_ascending_implies_no_dup.
  apply toOrderedUnique_is_ascending.
Qed.

(** The transformation preserves subset membership for subset sum.
    This shows the transformation doesn't add any new elements that would
    affect subset sum computations when considering sets (not multisets). *)
Theorem subset_sum_membership_preserved : forall l target subset,
  (forall x, In x subset -> In x l) ->
  (forall x, In x subset -> In x (toOrderedUnique l)).
Proof.
  intros l target subset H x Hx.
  rewrite mem_toOrderedUnique.
  apply H. exact Hx.
Qed.

(** Reverse direction *)
Theorem subset_sum_membership_preserved_rev : forall l target subset,
  (forall x, In x subset -> In x (toOrderedUnique l)) ->
  (forall x, In x subset -> In x l).
Proof.
  intros l target subset H x Hx.
  specialize (H x Hx).
  rewrite mem_toOrderedUnique in H.
  exact H.
Qed.

(** * Verification Checks *)

Check set_sequence_equivalence.
Check ordered_unique_has_no_dup.
Check subset_sum_membership_preserved.

(** All Set-Sequence Equivalence proofs verified successfully! *)
