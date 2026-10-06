/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# The Cycle Decomposition

This file formalizes the cycle decomposition (or disjoint cycle decomposition) of a permutation,
as presented in Section "The cycle decomposition" of the source text.

## Main definitions

* `numCyclesTotal`: The total number of cycles including 1-cycles (fixed points).
* `numCycles`: The number of non-trivial cycles (length ≥ 2).
* `cycles`: The set of cycles of a permutation.
* `cycleLengthsPartition`: The partition of n given by cycle lengths.
* `dcdListToPerm`: Convert a list of lists (representing cycles) to a permutation.

## Main results

* `sameCycle_iff_exists_pow`: Two elements belong to the same cycle iff one is a power of the
  permutation applied to the other (Proposition \ref{prop.perm.cycs.same}).
* `exists_dcd`: Every permutation can be written as a product of disjoint cycles
  (Theorem \ref{thm.perm.dcd.main} (a)).
* `dcd_unique_cycleType`: Any two DCDs of the same permutation have the same cycle type
  (Theorem \ref{thm.perm.dcd.main} (b)).
* `canonicalDcd_exists_unique`: For totally ordered sets, there is a unique canonical DCD
  (Theorem \ref{thm.perm.dcd.main} (c)).
* `cycleType_eq_iff_isConj`: Two permutations have the same cycle type iff they are conjugate.
* `sign_eq_neg_one_pow_card_sub_numCycles`: The sign of a permutation equals `(-1)^(n - k)`
  where `k` is the number of cycles (Proposition \ref{prop.perm.cycs.sign}).

## References

* Theorem \ref{thm.perm.dcd.main} in the source
* Definition \ref{def.perm.cycs.cycs}
* Proposition \ref{prop.perm.cycs.same}
* Proposition \ref{prop.perm.cycs.sign}

## Implementation notes

This file mostly provides wrappers and restatements of Mathlib's existing API for
cycle decomposition (`Equiv.Perm.cycleFactorsFinset`, `Equiv.Perm.cycleType`, etc.)
in the language of the source text.
-/

namespace AlgebraicCombinatorics.CycleDecomposition

open Equiv Equiv.Perm Finset

/-!
### The cycle of a permutation containing a given element

Mathlib provides `Equiv.Perm.cycleOf f x`, the cycle of `f` containing `x`.
We provide additional characterizations and properties.
-/

section SameCycle

variable {α : Type*} [Fintype α]

/-- Two elements belong to the same cycle of a permutation iff one can be reached from
the other by repeated application of the permutation. This is the equivalence from
Proposition \ref{prop.perm.cycs.same}.

The forward direction uses that for finite types, zpow can be replaced by pow. -/
theorem sameCycle_iff_exists_pow (f : Perm α) (i j : α) :
    f.SameCycle i j ↔ ∃ p : ℕ, (f ^ p) i = j := by
  constructor
  · intro h
    -- f.SameCycle i j means ∃ k : ℤ, (f ^ k) i = j
    obtain ⟨k, hk⟩ := h
    -- Use that f has finite order, so we can reduce k mod (orderOf f)
    use (k % (orderOf f : ℤ)).toNat
    have hord : 0 < orderOf f := orderOf_pos f
    have heq : f ^ (k % ↑(orderOf f)) = f ^ k := zpow_mod_orderOf f k
    rw [← hk, ← heq]
    congr 1
    rw [← zpow_natCast]
    congr 1
    exact Int.toNat_of_nonneg (Int.emod_nonneg k (by omega))
  · intro ⟨p, hp⟩
    exact ⟨p, by simp [hp]⟩

/-- Symmetric version: `i` and `j` belong to the same cycle iff `j = σ^p(i)` for some `p`. -/
theorem sameCycle_iff_exists_pow' (f : Perm α) (i j : α) :
    f.SameCycle i j ↔ ∃ p : ℕ, (f ^ p) j = i := by
  constructor
  · intro h
    exact (sameCycle_iff_exists_pow f j i).mp h.symm
  · intro hp
    exact ((sameCycle_iff_exists_pow f j i).mpr hp).symm

end SameCycle

/-!
### Disjoint Cycle Decomposition (DCD)

Mathlib's `Equiv.Perm.cycleFactorsFinset` provides the set of cycles in the DCD.
The key theorem `cycleFactorsFinset_noncommProd` states that the product of these
cycles equals the original permutation.

Theorem \ref{thm.perm.dcd.main} (a): Existence of DCD.
-/

section DCD

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The number of cycles of a permutation (including 1-cycles / fixed points).
This counts all cycles in the DCD as defined in the source text.

Note: Mathlib's `cycleFactorsFinset` only includes cycles of length ≥ 2.
To get the total count including 1-cycles, we add the number of fixed points. -/
def numCyclesTotal (σ : Perm α) : ℕ :=
  σ.cycleFactorsFinset.card + (Fintype.card α - σ.support.card)

/-- The total number of cycles (including 1-cycles) for the identity is the cardinality of α.
This is a natural base case for reasoning about cycle decompositions. -/
@[simp] lemma numCyclesTotal_one : numCyclesTotal (1 : Perm α) = Fintype.card α := by
  simp [numCyclesTotal]

/-- The number of cycles (of length ≥ 2) in the DCD. -/
def numCycles (σ : Perm α) : ℕ := σ.cycleFactorsFinset.card

/-- The identity permutation has no non-trivial cycles.
This is a natural base case for reasoning about cycle decompositions. -/
@[simp] lemma numCycles_one : numCycles (1 : Perm α) = 0 := by
  simp [numCycles]

/-- Existence of DCD: Every permutation is a product of disjoint cycles.
This is Theorem \ref{thm.perm.dcd.main} (a). -/
theorem exists_dcd (σ : Perm α) :
    ∃ (cycs : Finset (Perm α)),
      (∀ c ∈ cycs, c.IsCycle) ∧
      (cycs : Set (Perm α)).Pairwise Disjoint ∧
      ∃ h : (cycs : Set (Perm α)).Pairwise Commute, cycs.noncommProd id h = σ := by
  refine ⟨σ.cycleFactorsFinset, ?_, ?_, ?_⟩
  · intro c hc
    exact (mem_cycleFactorsFinset_iff.mp hc).1
  · exact cycleFactorsFinset_pairwise_disjoint σ
  · exact ⟨cycleFactorsFinset_mem_commute σ, cycleFactorsFinset_noncommProd σ⟩

/-- Two permutations have the same cycle type iff they are conjugate.

Note: This is NOT Theorem \ref{thm.perm.dcd.main} (b), which states that any two DCDs
of the *same* permutation can be obtained from each other by swapping cycles and rotating.
That result is essentially trivial: any DCD of σ yields the same multiset of cycle lengths
(the cycle type), and different DCDs are just reorderings/rotations of the same cycles.

This theorem is a deeper result about when two *different* permutations have the same
cycle structure. -/
theorem cycleType_eq_iff_isConj (σ τ : Perm α) :
    σ.cycleType = τ.cycleType ↔ IsConj σ τ :=
  isConj_iff_cycleType_eq.symm

/-- Any two DCDs of the same permutation have the same cycle type (as a multiset of lengths).
This captures the essence of Theorem \ref{thm.perm.dcd.main} (b): the cycles of a DCD are
uniquely determined up to swapping and rotation, hence they have the same lengths.

In Mathlib's formalization, there is a canonical DCD (`cycleFactorsFinset`), so this is trivial:
any DCD must produce the same set of cycles as `cycleFactorsFinset`, just possibly listed
in a different order or with different rotations. -/
theorem dcd_unique_cycleType (σ : Perm α) :
    ∀ (cycs : Finset (Perm α)),
      (∀ c ∈ cycs, c.IsCycle) →
      (cycs : Set (Perm α)).Pairwise Disjoint →
      (∃ h : (cycs : Set (Perm α)).Pairwise Commute, cycs.noncommProd id h = σ) →
      (cycs.val.map fun c => c.support.card) = σ.cycleType := by
  intro cycs h_cycle h_disjoint ⟨h_commute, h_prod⟩
  symm
  rw [cycleType_eq' cycs h_cycle h_disjoint]
  · rfl
  · rw [Finset.noncommProd_congr rfl (fun _ _ => rfl)]
    exact h_prod

end DCD

/-!
### Cycles of a permutation (Definition \ref{def.perm.cycs.cycs})

This section formalizes Definition \ref{def.perm.cycs.cycs} from the source text:

**Definition (def.perm.cycs.cycs):** Let X be a finite set. Let σ be a permutation of X.

**(a)** The *cycles* of σ are defined to be the cycles in the DCD of σ
(as defined in Theorem \ref{thm.perm.dcd.main} (a)). This includes 1-cycles, if there
are any in the DCD of σ.

We shall equate a cycle of σ with any of its cyclic rotations; thus, for example,
(3, 1, 4) and (1, 4, 3) shall be regarded as being the same cycle (but (3, 1, 4)
and (3, 4, 1) shall not).

**(b)** The *cycle lengths partition* of σ shall denote the partition of |X| obtained
by writing down the lengths of the cycles of σ in weakly decreasing order.

**Implementation note:** Mathlib's `cycleFactorsFinset` only includes cycles of length ≥ 2
(non-trivial cycles). Fixed points (1-cycles) are not included. This differs from the
textbook which includes 1-cycles. However, for most purposes this is equivalent since
1-cycles act as the identity. The `numCyclesTotal` definition above accounts for this
by adding the number of fixed points.

Regarding cyclic rotations: In Mathlib, cycles are represented as permutations (elements
of `Perm α`), not as lists. Two cycles that are cyclic rotations of each other represent
the *same* permutation, so they are automatically equated. For example, the cycles
`cyc [3, 1, 4]` and `cyc [1, 4, 3]` are equal as permutations by `List.formPerm_rotate`.
-/

section Cycles

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The cycles of a permutation σ are the elements of `σ.cycleFactorsFinset`.
Each cycle is a permutation that is a cycle in the graph-theoretic sense.

Note: This only includes cycles of length ≥ 2 (non-trivial cycles).
Fixed points (1-cycles) are not included, following Mathlib's convention.
See `numCyclesTotal` for the total count including 1-cycles.

(Definition \ref{def.perm.cycs.cycs} (a)) -/
def cycles (σ : Perm α) : Finset (Perm α) := σ.cycleFactorsFinset

/-- The identity permutation has no cycles (of length ≥ 2).
This is a natural base case for reasoning about cycle decompositions. -/
@[simp] lemma cycles_one : cycles (1 : Perm α) = ∅ := by
  simp [cycles]

/-- The cycles of σ equal the cycle factors finset from Mathlib. -/
theorem cycles_eq_cycleFactorsFinset (σ : Perm α) : cycles σ = σ.cycleFactorsFinset := rfl

/-- A permutation c is a cycle of σ iff c is a cycle and c agrees with σ on c's support. -/
theorem mem_cycles_iff (σ : Perm α) (c : Perm α) :
    c ∈ cycles σ ↔ c.IsCycle ∧ ∀ a ∈ c.support, c a = σ a :=
  mem_cycleFactorsFinset_iff

/-- Every element of `cycles σ` is a cycle. -/
theorem cycles_mem_isCycle (σ : Perm α) (c : Perm α) (hc : c ∈ cycles σ) : c.IsCycle :=
  (mem_cycles_iff σ c).mp hc |>.1

/-- The cycles of σ are pairwise disjoint (their supports are disjoint). -/
theorem cycles_pairwise_disjoint (σ : Perm α) :
    (cycles σ : Set (Perm α)).Pairwise Disjoint :=
  cycleFactorsFinset_pairwise_disjoint σ

/-- The cycles of σ pairwise commute (since they are disjoint). -/
theorem cycles_mem_commute (σ : Perm α) :
    (cycles σ : Set (Perm α)).Pairwise Commute :=
  cycleFactorsFinset_mem_commute σ

/-- The product of cycles equals σ. -/
theorem cycles_noncommProd_eq (σ : Perm α) :
    (cycles σ).noncommProd id (cycles_mem_commute σ) = σ :=
  cycleFactorsFinset_noncommProd σ

/-- Each cycle in `cycles σ` has length at least 2. -/
theorem cycles_support_card_ge_two (σ : Perm α) (c : Perm α) (hc : c ∈ cycles σ) :
    2 ≤ c.support.card := by
  have hcycle := cycles_mem_isCycle σ c hc
  exact hcycle.two_le_card_support

/-- The cardinality of `cycles σ` equals the number of non-trivial cycles. -/
theorem cycles_card_eq_numCycles (σ : Perm α) : (cycles σ).card = numCycles σ := rfl

/-- The cycle of σ containing x (when x is not a fixed point) is in `cycles σ`. -/
theorem cycleOf_mem_cycles (σ : Perm α) (x : α) (hx : x ∈ σ.support) :
    σ.cycleOf x ∈ cycles σ := by
  rwa [cycles_eq_cycleFactorsFinset, cycleOf_mem_cycleFactorsFinset_iff]

/-- The cycle lengths partition of σ is the partition of |X| obtained by
listing the lengths of cycles in weakly decreasing order.
(Definition \ref{def.perm.cycs.cycs} (b)) -/
def cycleLengthsPartition (σ : Perm α) : (Fintype.card α).Partition := σ.partition

/-- The cycle lengths partition of the identity permutation consists of all 1s.
This is a natural base case for reasoning about cycle decompositions. -/
@[simp]
theorem cycleLengthsPartition_one_parts :
    (cycleLengthsPartition (1 : Perm α)).parts = Multiset.replicate (Fintype.card α) 1 := by
  simp [cycleLengthsPartition, Equiv.Perm.parts_partition]

/-- The cycle type as a multiset of cycle lengths. -/
def cycleLengths (σ : Perm α) : Multiset ℕ := σ.cycleType

/-- The identity permutation has empty cycle lengths.
This is a natural base case for reasoning about cycle decompositions. -/
@[simp]
theorem cycleLengths_one : cycleLengths (1 : Perm α) = 0 := by
  simp [cycleLengths, Equiv.Perm.cycleType_one]

/-- The cycle lengths equal the cycle type from Mathlib. -/
theorem cycleLengths_eq_cycleType (σ : Perm α) : cycleLengths σ = σ.cycleType := rfl

/-- The sum of cycle lengths equals the size of the support. -/
theorem cycleLengths_sum_eq_support_card (σ : Perm α) :
    (cycleLengths σ).sum = σ.support.card :=
  sum_cycleType σ

/-- The number of cycle lengths equals the number of cycles. -/
theorem cycleLengths_card_eq_numCycles (σ : Perm α) :
    (cycleLengths σ).card = numCycles σ := by
  simp only [cycleLengths, cycleType_def, Multiset.card_map, ← Finset.card_def]
  rfl

/-- Every element of the cycle lengths multiset is at least 2. -/
theorem cycleLengths_mem_ge_two (σ : Perm α) (m : ℕ) (hm : m ∈ cycleLengths σ) :
    2 ≤ m :=
  two_le_of_mem_cycleType hm

/-- The cycle lengths partition has parts equal to the cycle type plus 1-cycles. -/
theorem cycleLengthsPartition_parts (σ : Perm α) :
    (cycleLengthsPartition σ).parts = σ.cycleType + Multiset.replicate
      (Fintype.card α - σ.support.card) 1 := by
  simp only [cycleLengthsPartition, Equiv.Perm.partition]

/-- The cycle lengths partition sums to |X|. -/
theorem cycleLengthsPartition_sum (σ : Perm α) :
    (cycleLengthsPartition σ).parts.sum = Fintype.card α := by
  exact (cycleLengthsPartition σ).parts_sum

/-! #### Cyclic rotations of cycles

The textbook states that cycles are equated with their cyclic rotations.
In Mathlib, this is automatic since cycles are represented as permutations,
and cyclically rotated lists give the same permutation via `List.formPerm_rotate`.
-/

omit [Fintype α] in
/-- Cyclic rotation of a list gives the same cycle permutation.
This formalizes the textbook statement that (3, 1, 4) and (1, 4, 3) are the same cycle. -/
theorem cyc_rotate_eq {l : List α} (hl : l.Nodup) (k : ℕ) :
    l.formPerm = (l.rotate k).formPerm :=
  (List.formPerm_rotate l hl k).symm

omit [Fintype α] in
/-- Two lists that are cyclic rotations of each other give the same cycle. -/
theorem cyc_eq_of_isRotated {l₁ l₂ : List α} (h : l₁.IsRotated l₂) (hl : l₁.Nodup) :
    l₁.formPerm = l₂.formPerm := by
  obtain ⟨k, hk⟩ := h
  rw [← hk, List.formPerm_rotate l₁ hl k]

/-- Two elements are in the same cycle iff they are in the same equivalence class
under the SameCycle relation.

Note: This requires `i ∈ σ.support` (i.e., `i` is not a fixed point) because
`cycleFactorsFinset` only contains non-trivial cycles (length ≥ 2), so fixed points
are not contained in any cycle's support. For fixed points `i = j`, we have
`σ.SameCycle i i` but no cycle containing `i`.

This is an auxiliary characterization connecting cycle membership (in terms of
`cycleFactorsFinset`) to the `SameCycle` relation. The main characterization of
Proposition \ref{prop.perm.cycs.same} is `sameCycle_iff_exists_pow` above. -/
theorem mem_same_cycle_iff (σ : Perm α) (i j : α) (hi : i ∈ σ.support) :
    (∃ c ∈ cycles σ, i ∈ c.support ∧ j ∈ c.support) ↔ σ.SameCycle i j := by
  constructor
  · rintro ⟨c, hc, hi', hj⟩
    have hcycle : c.IsCycle := (mem_cycleFactorsFinset_iff.mp hc).1
    -- i and j are both moved by c, so they're in the same cycle of c
    have hi'' : c i ≠ i := by rwa [mem_support] at hi'
    have hj' : c j ≠ j := by rwa [mem_support] at hj
    have hc_same : c.SameCycle i j := hcycle.sameCycle hi'' hj'
    -- c = σ.cycleOf i since i ∈ c.support
    have hc_eq : c = σ.cycleOf i := eq_cycleOf_of_mem_cycleFactorsFinset_iff σ c hc i |>.mpr hi'
    -- Transfer from c.SameCycle to σ.SameCycle using that c = σ.cycleOf i
    -- c.SameCycle i j means ∃ k : ℤ, (c ^ k) i = j
    -- Since c = σ.cycleOf i, we have (σ.cycleOf i ^ k) i = (σ ^ k) i
    obtain ⟨k, hk⟩ := hc_same
    use k
    rw [hc_eq, cycleOf_zpow_apply_self] at hk
    exact hk
  · intro h
    -- i is not a fixed point (by hypothesis hi), so it's in some cycle
    have hcyc : σ.cycleOf i ∈ σ.cycleFactorsFinset := by
      rwa [cycleOf_mem_cycleFactorsFinset_iff]
    use σ.cycleOf i, hcyc
    constructor
    · rw [mem_support_cycleOf_iff]
      exact ⟨SameCycle.refl _ _, hi⟩
    · rw [mem_support_cycleOf_iff]
      exact ⟨h, hi⟩

end Cycles

/-!
### Sign and cycle count (Proposition \ref{prop.perm.cycs.sign})

The sign of a permutation is determined by its number of cycles.
-/

section Sign

variable {n : ℕ}

/-- Helper lemma: the card of a multiset is at most its sum when all elements are ≥ 1. -/
private lemma multiset_card_le_sum_of_one_le (s : Multiset ℕ) (h : ∀ m ∈ s, 1 ≤ m) :
    s.card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.card_cons, Multiset.sum_cons]
    have ha : 1 ≤ a := h a (Multiset.mem_cons_self a s)
    have hs : ∀ m ∈ s, 1 ≤ m := fun m hm => h m (Multiset.mem_cons_of_mem hm)
    have ih' := ih hs
    calc s.card + 1 ≤ s.sum + 1 := by omega
      _ ≤ s.sum + a := by omega
      _ = a + s.sum := by ring

/-- The sign of a permutation equals `(-1)^(n - k)` where `k` is the number of cycles
(including 1-cycles). This is Proposition \ref{prop.perm.cycs.sign}.

We prove this using Mathlib's `sign_of_cycleType` which gives:
  `sign f = (-1)^(cycleType.sum + cycleType.card)`

The key insight is that for a permutation with k total cycles (including 1-cycles),
we have n - k = Σ(m_i - 1) where m_i are the cycle lengths. -/
theorem sign_eq_neg_one_pow_card_sub_numCycles (σ : Perm (Fin n)) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (n - numCyclesTotal σ) := by
  rw [numCyclesTotal, sign_of_cycleType]
  -- We need to show the exponents are equal mod 2
  have hsum : σ.cycleType.sum = σ.support.card := sum_cycleType σ
  have hle : σ.support.card ≤ n := by
    have := σ.support.card_le_univ
    simp only [Fintype.card_fin] at this
    exact this
  have hcard_eq : σ.cycleType.card = σ.cycleFactorsFinset.card := by
    rw [cycleType_def, Multiset.card_map, Finset.card_def]
  simp only [Fintype.card_fin]
  rw [hsum, hcard_eq]
  -- Now we need: (-1)^(support.card + card) = (-1)^(n - (card + (n - support.card)))
  -- These have the same parity since their difference is 2 * card
  have hle2 : σ.cycleFactorsFinset.card ≤ σ.support.card := by
    have h2 : ∀ m ∈ σ.cycleType, 2 ≤ m := fun m hm => two_le_of_mem_cycleType hm
    have h1 : ∀ m ∈ σ.cycleType, 1 ≤ m := fun m hm => Nat.one_le_of_lt (h2 m hm)
    calc σ.cycleFactorsFinset.card = σ.cycleType.card := hcard_eq.symm
      _ ≤ σ.cycleType.sum := multiset_card_le_sum_of_one_le σ.cycleType h1
      _ = σ.support.card := hsum
  have h_parity : (σ.support.card + σ.cycleFactorsFinset.card) % 2 =
                  (n - (σ.cycleFactorsFinset.card + (n - σ.support.card))) % 2 := by
    omega
  conv_lhs => rw [Int.units_pow_eq_pow_mod_two, h_parity, ← Int.units_pow_eq_pow_mod_two]

/-- The sign of a permutation can also be expressed as `(-1)^(Σ(m_i - 1))` where
m_i are the cycle lengths (of length ≥ 2). -/
theorem sign_eq_neg_one_pow_sum_cycle_lengths_minus_one (σ : Perm (Fin n)) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (σ.cycleType.sum - σ.cycleType.card) := by
  rw [sign_of_cycleType]
  -- sum + card and sum - card have the same parity (differ by 2 * card)
  have h : σ.cycleType.card ≤ σ.cycleType.sum := by
    calc σ.cycleType.card
        = (σ.cycleType.map (fun _ => 1)).sum := by simp
      _ ≤ (σ.cycleType.map id).sum := by
          apply Multiset.sum_map_le_sum_map
          intro a ha
          exact Nat.one_le_of_lt (two_le_of_mem_cycleType ha)
      _ = σ.cycleType.sum := by simp
  have hmod : (σ.cycleType.sum + σ.cycleType.card) % 2 = (σ.cycleType.sum - σ.cycleType.card) % 2 := by omega
  rw [Int.units_pow_eq_pow_mod_two (-1) (σ.cycleType.sum + σ.cycleType.card),
      Int.units_pow_eq_pow_mod_two (-1) (σ.cycleType.sum - σ.cycleType.card), hmod]

/-- The sign of a k-cycle is `(-1)^(k-1)`.
Note: Mathlib's `IsCycle.sign` gives `sign σ = -(-1)^(support.card)` which equals
`(-1)^(support.card - 1)` since `-(-1)^n = (-1)^(n-1)` for n ≥ 1. -/
theorem sign_cycle (σ : Perm (Fin n)) (hσ : σ.IsCycle) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ (σ.support.card - 1) := by
  rw [hσ.sign]
  -- -(-1)^n = (-1)^(n-1) for n ≥ 1
  have hpos : 0 < σ.support.card := hσ.nonempty_support.card_pos
  cases' hn : σ.support.card with k
  · simp only [hn] at hpos; omega
  · simp only [add_tsub_cancel_right, pow_succ, mul_neg_one, neg_neg]

end Sign

/-!
### Canonical DCD (Theorem \ref{thm.perm.dcd.main} (c))

For a totally ordered finite set, there is a unique DCD where:
1. Each cycle starts with its smallest element
2. Cycles appear in decreasing order of first elements

This canonical form is useful for comparing permutations.
-/

section CanonicalDCD

variable {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α] [Inhabited α]

/-!
#### Helper definitions and lemmas for canonical DCD construction

We build the canonical DCD by:
1. Converting each cycle in `cycleFactorsFinset` to its canonical list (starting from minimum)
2. Adding singleton lists for fixed points
3. Sorting by decreasing first element
-/

/-- Get the minimum element of a cycle's support. -/
noncomputable def cycleMinElem (c : Perm α) (hc : c.IsCycle) : α :=
  c.support.min' hc.nonempty_support

omit [Inhabited α] in
/-- The minimum element is in the support. -/
lemma cycleMinElem_mem_support (c : Perm α) (hc : c.IsCycle) :
    cycleMinElem c hc ∈ c.support := Finset.min'_mem _ _

omit [Inhabited α] in
/-- The minimum element is moved by c. -/
lemma cycleMinElem_ne (c : Perm α) (hc : c.IsCycle) :
    c (cycleMinElem c hc) ≠ cycleMinElem c hc :=
  mem_support.mp (cycleMinElem_mem_support c hc)

/-- Get the canonical list representation of a cycle starting from its minimum element. -/
noncomputable def cycleToCanonicalList (c : Perm α) (hc : c.IsCycle) : List α :=
  toList c (cycleMinElem c hc)

omit [Inhabited α] in
/-- The canonical list is nonempty. -/
lemma cycleToCanonicalList_ne_nil (c : Perm α) (hc : c.IsCycle) :
    cycleToCanonicalList c hc ≠ [] := by
  simp only [cycleToCanonicalList, ne_eq, Perm.toList_eq_nil_iff, not_not]
  exact cycleMinElem_mem_support c hc


set_option backward.isDefEq.respectTransparency false in
omit [Inhabited α] in
/-- The first element of the canonical list is the minimum. -/
lemma cycleToCanonicalList_head (c : Perm α) (hc : c.IsCycle) :
    (cycleToCanonicalList c hc).head (cycleToCanonicalList_ne_nil c hc) = cycleMinElem c hc := by
  unfold cycleToCanonicalList
  have hne : toList c (cycleMinElem c hc) ≠ [] := by
    intro h
    rw [Perm.toList_eq_nil_iff] at h
    exact h (cycleMinElem_mem_support c hc)
  conv_lhs => rw [List.head_eq_getElem]
  rw [Perm.getElem_toList]
  rfl


omit [Inhabited α] in
/-- The first element is minimal in the canonical list. -/
lemma cycleToCanonicalList_head_le (c : Perm α) (hc : c.IsCycle) (x : α)
    (hx : x ∈ cycleToCanonicalList c hc) :
    (cycleToCanonicalList c hc).head (cycleToCanonicalList_ne_nil c hc) ≤ x := by
  rw [cycleToCanonicalList_head]
  unfold cycleToCanonicalList at hx
  rw [Perm.mem_toList_iff] at hx
  obtain ⟨hsc, _⟩ := hx
  have hx' : x ∈ c.support :=
    SameCycle.mem_support_iff hsc |>.mp (cycleMinElem_mem_support c hc)
  exact Finset.min'_le _ _ hx'


omit [Inhabited α] in
/-- formPerm of the canonical list equals the cycle. -/
lemma cycleToCanonicalList_formPerm (c : Perm α) (hc : c.IsCycle) :
    (cycleToCanonicalList c hc).formPerm = c := by
  unfold cycleToCanonicalList
  rw [Perm.formPerm_toList]
  exact hc.cycleOf_eq (cycleMinElem_ne c hc)

omit [Inhabited α] in
/-- The canonical list is nodup. -/
lemma cycleToCanonicalList_nodup (c : Perm α) (hc : c.IsCycle) :
    (cycleToCanonicalList c hc).Nodup := Perm.nodup_toList c _


omit [Inhabited α] in
/-- Elements of the canonical list are exactly the support. -/
lemma mem_cycleToCanonicalList_iff (c : Perm α) (hc : c.IsCycle) (x : α) :
    x ∈ cycleToCanonicalList c hc ↔ x ∈ c.support := by
  simp only [cycleToCanonicalList, Perm.mem_toList_iff]
  constructor
  · intro ⟨hsc, _⟩
    exact SameCycle.mem_support_iff hsc |>.mp (cycleMinElem_mem_support c hc)
  · intro hx
    constructor
    · exact hc.sameCycle (cycleMinElem_ne c hc) (mem_support.mp hx)
    · exact cycleMinElem_mem_support c hc


omit [Inhabited α] in
/-- Canonical lists of disjoint cycles are List.Disjoint. -/
lemma cycleToCanonicalList_disjoint {c d : Perm α} (hc : c.IsCycle) (hd : d.IsCycle)
    (h : Disjoint c d) :
    List.Disjoint (cycleToCanonicalList c hc) (cycleToCanonicalList d hd) := by
  intro x hxc hxd
  rw [mem_cycleToCanonicalList_iff] at hxc hxd
  have hdisj : _root_.Disjoint c.support d.support := disjoint_iff_disjoint_support.mp h
  exact Finset.disjoint_left.mp hdisj hxc hxd


omit [Inhabited α] in
/-- The cyclesList (list of canonical lists for each cycle) is pairwise List.Disjoint. -/
lemma cyclesList_pairwise_disjoint (σ : Perm α) (cyclesList : List (List α))
    (hcl : cyclesList = σ.cycleFactorsFinset.toList.attach.map fun ⟨c, hc⟩ =>
        let hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
        cycleToCanonicalList c hcycle) :
    cyclesList.Pairwise List.Disjoint := by
  rw [hcl, List.pairwise_map]
  apply List.Pairwise.imp _ (List.nodup_attach.mpr (Finset.nodup_toList σ.cycleFactorsFinset))
  intro ⟨c, hc⟩ ⟨d, hd⟩ hne
  have hcycle_c := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
  have hcycle_d := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hd)).1
  apply cycleToCanonicalList_disjoint hcycle_c hcycle_d
  have hne' : c ≠ d := fun h => hne (Subtype.ext h)
  exact cycleFactorsFinset_pairwise_disjoint σ (Finset.mem_toList.mp hc) (Finset.mem_toList.mp hd) hne'


omit [Inhabited α] in
/-- The flatten of cyclesList is nodup. -/
lemma cyclesList_flatten_nodup (σ : Perm α) (cyclesList : List (List α))
    (hcl : cyclesList = σ.cycleFactorsFinset.toList.attach.map fun ⟨c, hc⟩ =>
        let hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
        cycleToCanonicalList c hcycle) :
    cyclesList.flatten.Nodup := by
  rw [List.nodup_flatten]
  constructor
  · intro l hl
    rw [hcl] at hl
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hl
    obtain ⟨c, hc, rfl⟩ := hl
    exact cycleToCanonicalList_nodup c _
  · exact cyclesList_pairwise_disjoint σ cyclesList hcl


omit [Inhabited α] in
/-- The flatten of cyclesList covers exactly σ.support. -/
lemma cyclesList_flatten_eq_support (σ : Perm α) (cyclesList : List (List α))
    (hcl : cyclesList = σ.cycleFactorsFinset.toList.attach.map fun ⟨c, hc⟩ =>
        let hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
        cycleToCanonicalList c hcycle) :
    ∀ y : α, y ∈ cyclesList.flatten ↔ y ∈ σ.support := by
  intro y
  simp only [hcl, List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hyl⟩
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hl
    obtain ⟨c, hc, rfl⟩ := hl
    have hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
    rw [mem_cycleToCanonicalList_iff] at hyl
    exact mem_cycleFactorsFinset_support_le (Finset.mem_toList.mp hc) hyl
  · intro hy
    use cycleToCanonicalList (σ.cycleOf y) (isCycle_cycleOf σ (mem_support.mp hy))
    constructor
    · simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
      use σ.cycleOf y
      have h := cycleOf_mem_cycleFactorsFinset_iff.mpr hy
      exact ⟨Finset.mem_toList.mpr h, rfl⟩
    · rw [mem_cycleToCanonicalList_iff, mem_support_cycleOf_iff]
      exact ⟨SameCycle.refl σ y, hy⟩


omit [Inhabited α] in
/-- The product of formPerms of cyclesList equals σ. -/
lemma dcdListToPerm_cyclesList_eq (σ : Perm α) (cyclesList : List (List α))
    (hcl : cyclesList = σ.cycleFactorsFinset.toList.attach.map fun ⟨c, hc⟩ =>
        let hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
        cycleToCanonicalList c hcycle) :
    (cyclesList.map List.formPerm).prod = σ := by
  have h1 : σ.cycleFactorsFinset.noncommProd id (cycleFactorsFinset_mem_commute σ) = σ :=
    cycleFactorsFinset_noncommProd σ
  have h2 : σ.cycleFactorsFinset.noncommProd id (cycleFactorsFinset_mem_commute σ) =
            σ.cycleFactorsFinset.toList.prod := by
    unfold noncommProd
    have h : σ.cycleFactorsFinset.val = (σ.cycleFactorsFinset.toList : Multiset (Perm α)) := by
      simp only [Finset.toList, Multiset.coe_toList]
    simp only [h, Multiset.map_coe, Multiset.noncommProd_coe, List.map_id]
  rw [h2] at h1
  rw [hcl]
  simp only [List.map_map, Function.comp_def]
  suffices (σ.cycleFactorsFinset.toList.attach.map fun x =>
      (cycleToCanonicalList x.1 ((mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp x.2)).1)).formPerm)
      = σ.cycleFactorsFinset.toList by
    rw [this, h1]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_attach]
  · intro n h1n h2n
    simp only [List.getElem_map, List.getElem_attach]
    have hmem : σ.cycleFactorsFinset.toList[n] ∈ σ.cycleFactorsFinset := by
      exact Finset.mem_toList.mp (List.getElem_mem h2n)
    exact cycleToCanonicalList_formPerm _ ((mem_cycleFactorsFinset_iff.mp hmem).1)

omit [Inhabited α] [LinearOrder α] in
/-- The fixed points list is pairwise disjoint. -/
lemma fixedPointsList_pairwise_disjoint (σ : Perm α) :
    let fixedPointsList := (Finset.filter (fun x => x ∉ σ.support) Finset.univ).toList.map (fun x => [x])
    fixedPointsList.Pairwise List.Disjoint := by
  simp only [List.pairwise_map]
  apply List.Pairwise.imp _ (Finset.nodup_toList _)
  intro x y hne z hz1 hz2
  simp only [List.mem_singleton] at hz1 hz2
  rw [hz1] at hz2
  exact hne hz2


omit [Inhabited α] in
/-- Singletons (fixed points) are disjoint from cyclesList. -/
lemma singleton_disjoint_cyclesList (σ : Perm α) (x : α) (hx : x ∉ σ.support)
    (cyclesList : List (List α))
    (hcl : cyclesList = σ.cycleFactorsFinset.toList.attach.map fun ⟨c, hc⟩ =>
        let hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
        cycleToCanonicalList c hcycle) :
    ∀ l ∈ cyclesList, List.Disjoint [x] l := by
  intro l hl
  rw [hcl] at hl
  simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hl
  obtain ⟨c, hc, rfl⟩ := hl
  intro y hy1 hy2
  simp only [List.mem_singleton] at hy1
  rw [hy1] at hy2
  have hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
  rw [mem_cycleToCanonicalList_iff] at hy2
  have hx' := mem_cycleFactorsFinset_support_le (Finset.mem_toList.mp hc) hy2
  exact hx hx'

/-- Convert a list of lists representing cycles to a permutation by taking the product
of the cycle permutations. Each list `[a₁, a₂, ..., aₖ]` represents the k-cycle
`cyc_{a₁, a₂, ..., aₖ}` that sends a₁ → a₂ → ... → aₖ → a₁. -/
def dcdListToPerm (cycleReps : List (List α)) : Perm α :=
  (cycleReps.map List.formPerm).prod

/-
For a totally ordered set, the canonical DCD is uniquely determined.
This is Theorem \ref{thm.perm.dcd.main} (c).

The existence follows from taking any DCD and:
1. Rotating each cycle to start with its minimum element
2. Sorting cycles by decreasing first element

The uniqueness follows from Theorem \ref{thm.perm.dcd.main} (b): any two DCDs
differ only by swapping cycles and rotating, so after canonicalization they must agree.

The product condition states that composing all the cycle permutations
(where each list [a₁,...,aₖ] represents cyc_{a₁,...,aₖ}) equals σ.

**Proof outline:**

*Existence:* Construct the canonical DCD as follows:
- For each cycle c in `σ.cycleFactorsFinset`, form `cycleToCanonicalList c`
- For each fixed point x (i.e., x ∉ σ.support), form the singleton list [x]
- Combine these lists and sort by decreasing first element

*Uniqueness:* Suppose we have two valid canonical DCDs. Since both cover all elements
exactly once and represent the same permutation σ:
- The non-singleton lists must correspond to the cycles in `cycleFactorsFinset`
- Each cycle's canonical form is unique (determined by starting from minimum)
- The sorting by decreasing first element is unique

The detailed proof involves showing the constructed DCD satisfies all properties
and that any other valid DCD must equal it. -/

omit [Inhabited α] [Fintype α] [LinearOrder α] in
-- Helper: formPerm of a list of length ≤ 1 is 1
private lemma formPerm_eq_one_of_length_le_one {l : List α} (hl : l.Nodup) (hlen : l.length ≤ 1) :
    l.formPerm = 1 := by
  cases l with
  | nil => simp [List.formPerm]
  | cons hd tl =>
    simp only [List.length_cons, Nat.add_one_le_iff, Nat.lt_one_iff] at hlen
    simp only [List.length_eq_zero_iff] at hlen
    simp [hlen, List.formPerm]


omit [DecidableEq α] [Inhabited α] [Fintype α] [LinearOrder α] in
-- Helper: product of disjoint permutations acts as the unique one that moves the point
private lemma prod_disjoint_apply {perms : List (Perm α)} {p : Perm α} {a : α}
    (hp : p ∈ perms)
    (hpa : p a ≠ a)
    (hpwd : perms.Pairwise Perm.Disjoint) :
    perms.prod a = p a := by
  induction perms with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.prod_cons, Perm.mul_apply]
    cases List.mem_cons.mp hp with
    | inl heq =>
      subst heq
      suffices h : qs.prod a = a by rw [h]
      have hfix : ∀ r ∈ qs, r a = a := by
        intro r hr
        have hdisj : Perm.Disjoint p r := by
          rw [List.pairwise_cons] at hpwd
          exact hpwd.1 r hr
        exact (hdisj a).resolve_left hpa
      clear ih hpwd hp hpa
      induction qs with
      | nil => rfl
      | cons r rs ihr =>
        simp only [List.prod_cons, Perm.mul_apply]
        have hra : r a = a := hfix r (by simp)
        rw [ihr (fun s hs => hfix s (List.mem_cons_of_mem r hs)), hra]
    | inr hmem =>
      have hqa : q a = a := by
        have hdisj : Perm.Disjoint q p := by
          rw [List.pairwise_cons] at hpwd
          exact hpwd.1 p hmem
        exact (hdisj a).resolve_right hpa
      rw [ih hmem (List.Pairwise.of_cons hpwd)]
      have hdisj : Perm.Disjoint q p := by
        rw [List.pairwise_cons] at hpwd
        exact hpwd.1 p hmem
      have h := hdisj (p a)
      rcases h with hq | hp'
      · exact hq
      · exact absurd (p.injective hp') hpa

omit [Inhabited α] [LinearOrder α] in
-- Helper: if formPerm of a nodup list with length > 1 is part of a product that equals σ,
-- then formPerm is in σ.cycleFactorsFinset
private lemma formPerm_mem_cycleFactorsFinset_of_prod {cycleReps : List (List α)} (σ : Perm α)
    (hnodup_flat : cycleReps.flatten.Nodup)
    (hpwd : cycleReps.Pairwise List.Disjoint)
    (hprod : (cycleReps.map List.formPerm).prod = σ)
    (l : List α) (hl : l ∈ cycleReps) (hlen : 1 < l.length) :
    l.formPerm ∈ σ.cycleFactorsFinset := by
  have hnodup_l : l.Nodup := by
    have h := hnodup_flat
    rw [List.nodup_flatten] at h
    exact h.1 l hl
  have hne : ∀ y : α, l ≠ [y] := by intro y hy; rw [hy] at hlen; simp at hlen
  have hcycle : l.formPerm.IsCycle := List.isCycle_formPerm hnodup_l (by omega)
  have hsupp : l.formPerm.support = l.toFinset := List.support_formPerm_of_nodup l hnodup_l hne
  rw [mem_cycleFactorsFinset_iff]
  constructor
  · exact hcycle
  · intro a ha
    rw [hsupp, List.mem_toFinset] at ha
    have hpwd_perm : (cycleReps.map List.formPerm).Pairwise Perm.Disjoint := by
      rw [List.pairwise_map]
      apply hpwd.imp
      intro l₁ l₂ hdisj x
      by_cases hx₁ : x ∈ l₁ <;> by_cases hx₂ : x ∈ l₂
      · exact absurd hx₂ (hdisj hx₁)
      · right; exact List.formPerm_apply_of_notMem hx₂
      · left; exact List.formPerm_apply_of_notMem hx₁
      · left; exact List.formPerm_apply_of_notMem hx₁
    have hpa : l.formPerm a ≠ a := by
      rw [ne_eq, List.formPerm_apply_mem_eq_self_iff l hnodup_l a ha]
      omega
    have hmem : l.formPerm ∈ cycleReps.map List.formPerm := by
      rw [List.mem_map]
      exact ⟨l, hl, rfl⟩
    have h := prod_disjoint_apply hmem hpa hpwd_perm
    rw [hprod] at h
    exact h.symm


omit [Inhabited α] [Fintype α] in
-- Helper: If two nodup lists have the same formPerm, same length > 1, and both start with their minimum,
-- then they are equal
private lemma eq_of_formPerm_eq_of_min_head {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup)
    (hlen : 1 < l.length)
    (hfp : l.formPerm = l'.formPerm)
    (hne : l ≠ []) (hne' : l' ≠ [])
    (hmin : ∀ x ∈ l, l.head hne ≤ x)
    (hmin' : ∀ x ∈ l', l'.head hne' ≤ x) :
    l = l' := by
  have hrot' : l.IsRotated l' ∨ l.length ≤ 1 ∧ l'.length ≤ 1 :=
    List.formPerm_eq_formPerm_iff hl hl' |>.mp hfp
  rcases hrot' with hrot | ⟨hlen_bad, _⟩
  · have hlen_eq : l.length = l'.length := hrot.perm.length_eq
    obtain ⟨k, hk⟩ := hrot
    by_cases hk0 : k % l.length = 0
    · have hrotk : l.rotate k = l := by
        conv_lhs => rw [← List.rotate_mod]
        simp [hk0]
      rw [hrotk] at hk
      exact hk
    · exfalso
      have hlenpos : 0 < l.length := by omega
      have hklt : k % l.length < l.length := Nat.mod_lt k hlenpos
      have hne'' : l.rotate k ≠ [] := by simp [hne]
      have h1 : l'.head hne' = l[k % l.length]'hklt := by
        have h1a : l'.head hne' = (l.rotate k).head hne'' := by congr 1; exact hk.symm
        have h1b : (l.rotate k).head hne'' = (l.rotate k)[0]'(by simp; omega) := by
          rw [List.head_eq_getElem]
        have h1c : (l.rotate k)[0]'(by simp; omega) = l[(0 + k) % l.length]'(Nat.mod_lt _ hlenpos) := by
          rw [List.getElem_rotate]
        simp only [zero_add] at h1c
        rw [h1a, h1b, h1c]
      have h2 : l.head hne = l[0]'hlenpos := by rw [List.head_eq_getElem]
      have hle1 : l.head hne ≤ l[k % l.length]'hklt := hmin _ (List.getElem_mem hklt)
      have hl_mem_l' : l.head hne ∈ l' := by
        rw [← hk, List.mem_rotate]; exact List.head_mem hne
      have hle2 : l'.head hne' ≤ l.head hne := hmin' _ hl_mem_l'
      rw [h1] at hle2
      have heq : l.head hne = l[k % l.length]'hklt := le_antisymm hle1 hle2
      rw [h2] at heq
      have hinj : 0 = k % l.length ↔ l[0]'hlenpos = l[k % l.length]'hklt := by
        exact (hl.getElem_inj_iff (hi := hlenpos) (hj := hklt)).symm
      exact hk0 (hinj.mpr heq).symm
  · omega


omit [Inhabited α] in
-- Helper: canonical list has length ≥ 2
private lemma cycleToCanonicalList_length_ge_two (c : Perm α) (hc : c.IsCycle) :
    2 ≤ (cycleToCanonicalList c hc).length := by
  unfold cycleToCanonicalList
  rw [Perm.length_toList]
  calc 2 ≤ c.support.card := hc.two_le_card_support
    _ = (c.cycleOf (cycleMinElem c hc)).support.card := by
        rw [hc.cycleOf_eq (cycleMinElem_ne c hc)]


omit [Inhabited α] in
-- Helper: A nodup list starting with its minimum, whose formPerm is a cycle c,
-- equals the canonical list for c
private lemma eq_cycleToCanonicalList_of_formPerm_eq {l : List α} (hl : l.Nodup) (hlen : 1 < l.length)
    (c : Perm α) (hc : c.IsCycle) (hfp : l.formPerm = c)
    (hne : l ≠ []) (hmin : ∀ x ∈ l, l.head hne ≤ x) :
    l = cycleToCanonicalList c hc := by
  have hne' := cycleToCanonicalList_ne_nil c hc
  apply eq_of_formPerm_eq_of_min_head hl (cycleToCanonicalList_nodup c hc) hlen
    (hfp.trans (cycleToCanonicalList_formPerm c hc).symm) hne hne' hmin
  intro x hx
  exact cycleToCanonicalList_head_le c hc x hx

-- Comparison function for sorting lists by decreasing first element
private def cmpListsGe : List α → List α → Bool := fun l1 l2 => decide (l1.head! ≥ l2.head!)


omit [DecidableEq α] [Fintype α] in
-- Helper: mergeSort produces a pairwise ≥ list
private lemma mergeSort_pairwise_ge (l : List (List α)) :
    (l.mergeSort cmpListsGe).Pairwise (fun a b => a.head! ≥ b.head!) := by
  have h := List.pairwise_mergeSort (le := fun a b => a.head! ≥ b.head!)
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; exact le_trans hbc hab)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total b.head! a.head!) l
  convert h using 2 <;> first | rfl | simp


omit [DecidableEq α] [Fintype α] in
-- Helper: if first elements are distinct, ≥ implies >
private lemma pairwise_ge_to_gt_of_nodup {l : List (List α)}
    (hge : l.Pairwise (fun a b => a.head! ≥ b.head!))
    (hdistinct : (l.map (fun x => x.head!)).Nodup) :
    l.Pairwise (fun a b => a.head! > b.head!) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    rw [List.pairwise_cons] at hge ⊢
    rw [List.map_cons, List.nodup_cons] at hdistinct
    constructor
    · intro y hy
      have hge_xy := hge.1 y hy
      have hne : x.head! ≠ y.head! := by
        intro heq
        apply hdistinct.1
        rw [List.mem_map]
        exact ⟨y, hy, heq.symm⟩
      exact lt_of_le_of_ne hge_xy (Ne.symm hne)
    · exact ih hge.2 hdistinct.2


omit [Inhabited α] [Fintype α] [LinearOrder α] in
-- Helper: product of formPerms fixes elements not in any list
private lemma formPerm_prod_apply_not_mem {L : List (List α)} {x : α}
    (hx : ∀ l ∈ L, x ∉ l) : (L.map List.formPerm).prod x = x := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply]
    have hx_hd : x ∉ hd := hx hd (by simp)
    have hx_tl : ∀ l ∈ tl, x ∉ l := fun l hl => hx l (by simp [hl])
    rw [ih hx_tl, List.formPerm_apply_of_notMem hx_hd]


omit [Inhabited α] [Fintype α] [LinearOrder α] in
-- Helper: for pairwise disjoint lists, the product of formPerms at x equals the formPerm 
-- of the unique list containing x
private lemma formPerm_prod_apply_eq {L : List (List α)} {x : α} {l : List α}
    (hpwd : L.Pairwise List.Disjoint) (hl : l ∈ L) (hx : x ∈ l) :
    (L.map List.formPerm).prod x = l.formPerm x := by
  induction L with
  | nil => simp at hl
  | cons hd tl ih =>
    simp only [List.map_cons, List.prod_cons, mul_apply]
    simp only [List.pairwise_cons] at hpwd
    obtain ⟨hdisj, hpwd_tl⟩ := hpwd
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hl_tl
    · -- l = hd, x ∈ l (= hd)
      have hx_not_in_tl : ∀ l' ∈ tl, x ∉ l' := by
        intro l' hl'
        have hdisj' : List.Disjoint l l' := hdisj l' hl'
        exact fun hx' => hdisj' hx hx'
      rw [formPerm_prod_apply_not_mem hx_not_in_tl]
    · -- l ∈ tl, x ∈ l
      have hdisj_l : List.Disjoint hd l := hdisj l hl_tl
      have hx_notin_hd : x ∉ hd := fun h => hdisj_l h hx
      have h1 := ih hpwd_tl hl_tl
      rw [h1]
      have hfpx_in_l : l.formPerm x ∈ l := List.formPerm_mem_iff_mem.mpr hx
      have hfpx_notin_hd : l.formPerm x ∉ hd := fun h => hdisj_l h hfpx_in_l
      exact List.formPerm_apply_of_notMem hfpx_notin_hd


omit [DecidableEq α] [Inhabited α] [Fintype α] [LinearOrder α] in
-- Helper: pairwise disjoint nonempty lists form a nodup list
private lemma nodup_of_pairwise_disjoint_nonempty {L : List (List α)}
    (hpwd : L.Pairwise List.Disjoint) (hne : ∀ l ∈ L, l ≠ []) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons hd tl ih =>
    simp only [List.pairwise_cons] at hpwd
    rw [List.nodup_cons]
    constructor
    · intro hmem
      have hdisj' := hpwd.1 hd hmem
      have hne_hd := hne hd (by simp)
      have : hd = [] := by
        by_contra hne'
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil hd hne'
        exact hdisj' hx hx
      exact hne_hd this
    · exact ih hpwd.2 (fun l hl => hne l (List.mem_cons_of_mem hd hl))


omit [DecidableEq α] [Fintype α] [LinearOrder α] in
-- Helper: heads of pairwise disjoint nonempty lists are nodup
private lemma heads_nodup_of_pairwise_disjoint {L : List (List α)}
    (hpwd : L.Pairwise List.Disjoint) (hne : ∀ l ∈ L, l ≠ []) :
    (L.map (fun x => x.head!)).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  simp only [List.getElem_map, Fin.mk.injEq] at heq ⊢
  have hi' : i < L.length := by simp only [List.length_map] at hi; exact hi
  have hj' : j < L.length := by simp only [List.length_map] at hj; exact hj
  by_contra hne'
  have hli : L[i] ∈ L := List.getElem_mem hi'
  have hlj : L[j] ∈ L := List.getElem_mem hj'
  have hne_i := hne _ hli
  have hne_j := hne _ hlj
  have hhead_i : L[i].head! ∈ L[i] := List.head!_mem_self hne_i
  have hhead_j : L[j].head! ∈ L[j] := List.head!_mem_self hne_j
  rw [heq] at hhead_i
  -- Use pairwise disjoint: different indices means different lists
  have hne'' : L[i] ≠ L[j] := by
    intro heq'
    have hnodup := nodup_of_pairwise_disjoint_nonempty hpwd hne
    exact hne' (hnodup.getElem_inj_iff.mp heq')
  have hdisj : List.Disjoint L[i] L[j] := by
    have : Std.Symm (@List.Disjoint α) := ⟨fun _ _ h => h.symm⟩
    exact hpwd.forall hli hlj hne''
  exact hdisj hhead_i hhead_j

theorem canonicalDcd_exists_unique (σ : Perm α) :
    ∃! (cycleReps : List (List α)),
      -- Each list is nonempty
      (∀ l ∈ cycleReps, l ≠ []) ∧
      -- Each element appears exactly once across all lists
      (cycleReps.flatten.Nodup) ∧
      (∀ x : α, x ∈ cycleReps.flatten) ∧
      -- Each list starts with its minimum element
      (∀ l ∈ cycleReps, ∀ x ∈ l, l.head! ≤ x) ∧
      -- Lists are sorted by decreasing first element
      (cycleReps.Pairwise fun l1 l2 => l1.head! > l2.head!) ∧
      -- The product of cycles equals σ
      dcdListToPerm cycleReps = σ := by
  classical
  -- Construct the canonical DCD:
  -- 1. For each cycle in cycleFactorsFinset, get its canonical list (starting from minimum)
  -- 2. For each fixed point, create a singleton list
  -- 3. Sort all lists by decreasing first element
  let cyclesList : List (List α) :=
    σ.cycleFactorsFinset.toList.attach.map fun ⟨c, hc⟩ =>
      let hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
      cycleToCanonicalList c hcycle
  let fixedPointsList : List (List α) :=
    (Finset.filter (fun x => x ∉ σ.support) Finset.univ).toList.map (fun x => [x])
  let allLists := cyclesList ++ fixedPointsList
  let canonicalDcd := allLists.mergeSort cmpListsGe

  use canonicalDcd
  have hperm : canonicalDcd.Perm allLists := List.mergeSort_perm allLists cmpListsGe

  -- Key helper: all lists in allLists are nonempty
  have hne_all : ∀ l ∈ allLists, l ≠ [] := by
    intro l hl
    simp only [allLists, List.mem_append] at hl
    rcases hl with hl_cycle | hl_fixed
    · simp only [cyclesList, List.mem_map, List.mem_attach, true_and, Subtype.exists] at hl_cycle
      obtain ⟨c, hc, rfl⟩ := hl_cycle
      exact cycleToCanonicalList_ne_nil c _
    · simp only [fixedPointsList, List.mem_map] at hl_fixed
      obtain ⟨x, _, rfl⟩ := hl_fixed
      exact List.cons_ne_nil x []

  -- Key helper: allLists is pairwise disjoint
  have hpwd : allLists.Pairwise List.Disjoint := by
    rw [List.pairwise_append]
    constructor
    · exact cyclesList_pairwise_disjoint σ cyclesList rfl
    constructor
    · exact fixedPointsList_pairwise_disjoint σ
    · intro l1 hl1 l2 hl2
      simp only [cyclesList, List.mem_map, List.mem_attach, true_and, Subtype.exists] at hl1
      simp only [fixedPointsList, List.mem_map] at hl2
      obtain ⟨c, hc, rfl⟩ := hl1
      obtain ⟨x, hx, rfl⟩ := hl2
      intro y hy1 hy2
      simp only [List.mem_singleton] at hy2
      rw [hy2] at hy1
      have hcycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc)).1
      rw [mem_cycleToCanonicalList_iff] at hy1
      have hx_c : x ∈ c.support := hy1
      have hx' : x ∉ σ.support := by
        have hmem := Finset.mem_toList.mp hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact hmem
      exact hx' (mem_cycleFactorsFinset_support_le (Finset.mem_toList.mp hc) hx_c)

  -- Key helper: flatten of allLists is nodup
  have hflat_nodup : allLists.flatten.Nodup := by
    rw [List.nodup_flatten]
    constructor
    · intro l hl
      simp only [allLists, List.mem_append] at hl
      rcases hl with hl_cycle | hl_fixed
      · simp only [cyclesList, List.mem_map, List.mem_attach, true_and, Subtype.exists] at hl_cycle
        obtain ⟨c, hc, rfl⟩ := hl_cycle
        exact cycleToCanonicalList_nodup c _
      · simp only [fixedPointsList, List.mem_map] at hl_fixed
        obtain ⟨x, _, rfl⟩ := hl_fixed
        exact List.nodup_singleton x
    · exact hpwd

  -- Key helper: every element appears in allLists.flatten
  have hmem_all : ∀ x : α, x ∈ allLists.flatten := by
    intro x
    simp only [allLists, List.mem_flatten, List.mem_append]
    by_cases hx : x ∈ σ.support
    · -- x is in support, so it's in some cycle
      have hcycle := isCycle_cycleOf σ (mem_support.mp hx)
      refine ⟨cycleToCanonicalList (σ.cycleOf x) hcycle, Or.inl ?_, ?_⟩
      · simp only [cyclesList, List.mem_map, List.mem_attach, true_and, Subtype.exists]
        use σ.cycleOf x
        have h := cycleOf_mem_cycleFactorsFinset_iff.mpr hx
        exact ⟨Finset.mem_toList.mpr h, rfl⟩
      · rw [mem_cycleToCanonicalList_iff, mem_support_cycleOf_iff]
        exact ⟨SameCycle.refl σ x, hx⟩
    · -- x is a fixed point
      refine ⟨[x], Or.inr ?_, List.mem_singleton_self x⟩
      simp only [fixedPointsList, List.mem_map]
      use x
      constructor
      · exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
      · rfl

  -- Key helper: product of formPerms of allLists equals σ
  have hprod_all : (allLists.map List.formPerm).prod = σ := by
    simp only [allLists, List.map_append, List.prod_append]
    -- The fixed points contribute 1 since formPerm [x] = 1
    have hfixed : (fixedPointsList.map List.formPerm).prod = 1 := by
      simp only [fixedPointsList, List.map_map, Function.comp_def, List.formPerm_singleton]
      simp only [List.map_const', List.prod_replicate, one_pow]
    rw [hfixed, mul_one]
    exact dcdListToPerm_cyclesList_eq σ cyclesList rfl

  constructor
  · -- Existence: show all properties hold
    constructor
    · -- All lists are nonempty
      intro l hl
      rw [List.Perm.mem_iff hperm] at hl
      exact hne_all l hl
    constructor
    · -- flatten is nodup
      exact hperm.flatten.nodup_iff.mpr hflat_nodup
    constructor
    · -- every element appears
      intro x
      rw [hperm.flatten.mem_iff]
      exact hmem_all x
    constructor
    · -- each list starts with minimum
      intro l hl x hx
      rw [List.Perm.mem_iff hperm] at hl
      simp only [allLists, List.mem_append] at hl
      rcases hl with hl_cycle | hl_fixed
      · simp only [cyclesList, List.mem_map, List.mem_attach, true_and, Subtype.exists] at hl_cycle
        obtain ⟨c, hc_mem, rfl⟩ := hl_cycle
        have hcycle : c.IsCycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc_mem)).1
        have hne := cycleToCanonicalList_ne_nil c hcycle
        cases hl' : cycleToCanonicalList c hcycle with
        | nil => exact absurd hl' hne
        | cons y ys =>
          simp only [List.head!_cons]
          have hx'' : x ∈ cycleToCanonicalList c hcycle := hx
          have h := cycleToCanonicalList_head_le c hcycle x hx''
          simp only [hl', List.head_cons] at h
          exact h
      · simp only [fixedPointsList, List.mem_map] at hl_fixed
        obtain ⟨y, _, rfl⟩ := hl_fixed
        simp only [List.head!_cons, List.mem_singleton] at hx ⊢
        rw [hx]
    constructor
    · -- lists sorted by decreasing first element
      have hge := mergeSort_pairwise_ge allLists
      have hpwd_sorted : canonicalDcd.Pairwise List.Disjoint :=
        hperm.pairwise_iff (fun h => h.symm) |>.mpr hpwd
      have hne_sorted : ∀ l ∈ canonicalDcd, l ≠ [] := fun l hl => hne_all l (hperm.mem_iff.mp hl)
      have hdistinct := heads_nodup_of_pairwise_disjoint hpwd_sorted hne_sorted
      exact pairwise_ge_to_gt_of_nodup hge hdistinct
    · -- product equals σ
      unfold dcdListToPerm
      have hperm_fp := hperm.map List.formPerm
      rw [hperm_fp.prod_eq']
      · exact hprod_all
      · -- Prove pairwise commute from pairwise disjoint
        -- First get that allLists.map formPerm is pairwise commute
        have hcomm_all : (allLists.map List.formPerm).Pairwise Commute := by
          rw [List.pairwise_map]
          apply hpwd.imp
          intro l₁ l₂ hdisj
          apply Perm.Disjoint.commute
          intro x
          by_cases hx₁ : x ∈ l₁ <;> by_cases hx₂ : x ∈ l₂
          · exact absurd hx₂ (hdisj hx₁)
          · right; exact List.formPerm_apply_of_notMem hx₂
          · left; exact List.formPerm_apply_of_notMem hx₁
          · left; exact List.formPerm_apply_of_notMem hx₁
        -- Transfer via permutation
        exact hperm_fp.pairwise_iff (fun (hc : Commute _ _) => hc.symm) |>.mpr hcomm_all
  · -- Uniqueness
    intro cycleReps' ⟨hne', hnodup', hmem', hmin', hsort', hprod'⟩
    -- The uniqueness proof shows that any valid canonical DCD must equal our construction.
    -- Both cycleReps' and canonicalDcd are sorted by decreasing first element and
    -- contain the same lists, so they must be equal.

    -- Get pairwise disjoint for cycleReps'
    have hpwd' : cycleReps'.Pairwise List.Disjoint := by
      rw [List.nodup_flatten] at hnodup'
      exact hnodup'.2

    -- Key: cycleReps' and canonicalDcd have the same elements (as sets)
    have hmem_iff : ∀ l, l ∈ cycleReps' ↔ l ∈ canonicalDcd := by
      intro l
      rw [List.Perm.mem_iff hperm]
      constructor
      · -- l ∈ cycleReps' → l ∈ allLists
        intro hl'
        have hne_l := hne' l hl'
        -- Get some element x in l
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hne_l
        -- Determine if x is a fixed point or not
        by_cases hfixed : x ∈ σ.support
        · -- x is NOT a fixed point, so l corresponds to a cycle
          -- l = cycleToCanonicalList (σ.cycleOf x)
          have hnodup_l : l.Nodup := by
            rw [List.nodup_flatten] at hnodup'
            exact hnodup'.1 l hl'
          -- l.length > 1 since x is not a fixed point
          have hlen : 1 < l.length := by
            by_contra hlen'
            push Not at hlen'
            have hlen1 : l.length = 1 := by
              have hpos : 0 < l.length := List.length_pos_iff.mpr hne_l
              omega
            obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hlen1
            simp only [List.mem_singleton] at hx
            rw [hx] at hfixed
            -- But formPerm [y] = 1, so σ y = y, contradiction
            have hprod_y := formPerm_prod_apply_eq hpwd' hl' (List.mem_singleton_self y)
            simp only [List.formPerm_singleton] at hprod_y
            unfold dcdListToPerm at hprod'
            rw [hprod'] at hprod_y
            rw [Perm.mem_support] at hfixed
            simp only [one_apply] at hprod_y
            exact hfixed hprod_y
          -- l.formPerm is a cycle in σ.cycleFactorsFinset
          have hfp_mem : l.formPerm ∈ σ.cycleFactorsFinset := by
            unfold dcdListToPerm at hprod'
            exact formPerm_mem_cycleFactorsFinset_of_prod σ hnodup' hpwd' hprod' l hl' hlen
          -- l.formPerm = σ.cycleOf x
          have hfp_eq : l.formPerm = σ.cycleOf x := by
            have hx_supp : x ∈ l.formPerm.support := by
              have hne'' : ∀ y : α, l ≠ [y] := by intro y hy; rw [hy] at hlen; simp at hlen
              rw [List.support_formPerm_of_nodup l hnodup_l hne'', List.mem_toFinset]
              exact hx
            exact eq_cycleOf_of_mem_cycleFactorsFinset_iff σ l.formPerm hfp_mem x |>.mpr hx_supp
          -- l = cycleToCanonicalList (σ.cycleOf x)
          have hcycle := isCycle_cycleOf σ (mem_support.mp hfixed)
          have hmin_l : ∀ y ∈ l, l.head hne_l ≤ y := by
            intro y hy
            have h := hmin' l hl' y hy
            have heq : l.head! = l.head hne_l := by
              cases l with
              | nil => exact absurd rfl hne_l
              | cons z zs => simp [List.head!, List.head]
            rw [← heq]; exact h
          have hl_eq := eq_cycleToCanonicalList_of_formPerm_eq hnodup_l hlen (σ.cycleOf x) hcycle hfp_eq hne_l hmin_l
          -- cycleToCanonicalList (σ.cycleOf x) is in cyclesList
          rw [hl_eq]
          simp only [allLists, List.mem_append]
          left
          simp only [cyclesList, List.mem_map, List.mem_attach, true_and, Subtype.exists]
          use σ.cycleOf x
          have h := cycleOf_mem_cycleFactorsFinset_iff.mpr hfixed
          exact ⟨Finset.mem_toList.mpr h, rfl⟩
        · -- x IS a fixed point, so l = [x]
          have hl_singleton : l = [x] := by
            have hnodup_l : l.Nodup := by
              rw [List.nodup_flatten] at hnodup'
              exact hnodup'.1 l hl'
            have hσx : σ x = x := by
              rw [Perm.mem_support] at hfixed
              push Not at hfixed
              exact hfixed
            have hprod_x := formPerm_prod_apply_eq hpwd' hl' hx
            have hfp_x : l.formPerm x = x := by
              unfold dcdListToPerm at hprod'
              calc l.formPerm x = (cycleReps'.map List.formPerm).prod x := hprod_x.symm
                _ = σ x := by rw [hprod']
                _ = x := hσx
            have hlen : l.length ≤ 1 := by
              by_contra hlen'
              push Not at hlen'
              rw [List.formPerm_apply_mem_eq_self_iff l hnodup_l x hx] at hfp_x
              omega
            have hlen1 : l.length = 1 := by
              have hpos : 0 < l.length := List.length_pos_iff.mpr hne_l
              omega
            obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hlen1
            simp only [List.mem_singleton] at hx
            rw [hx]
          -- [x] is in fixedPointsList
          rw [hl_singleton]
          simp only [allLists, List.mem_append]
          right
          simp only [fixedPointsList, List.mem_map]
          use x
          constructor
          · exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfixed⟩)
          · rfl
      · -- l ∈ allLists → l ∈ cycleReps'
        intro hl_all
        simp only [allLists, List.mem_append] at hl_all
        rcases hl_all with hl_cycle | hl_fixed
        · -- l is a canonical cycle list
          simp only [cyclesList, List.mem_map, List.mem_attach, true_and, Subtype.exists] at hl_cycle
          obtain ⟨c, hc_mem, rfl⟩ := hl_cycle
          have hcycle : c.IsCycle := (mem_cycleFactorsFinset_iff.mp (Finset.mem_toList.mp hc_mem)).1
          -- Get the minimum element of c
          let x := cycleMinElem c hcycle
          have hx_supp : x ∈ c.support := cycleMinElem_mem_support c hcycle
          have hx_σ_supp : x ∈ σ.support := mem_cycleFactorsFinset_support_le (Finset.mem_toList.mp hc_mem) hx_supp
          -- x is in cycleReps'.flatten
          have hx_flat' : x ∈ cycleReps'.flatten := hmem' x
          rw [List.mem_flatten] at hx_flat'
          obtain ⟨l', hl'_mem, hx_l'⟩ := hx_flat'
          -- l' must equal cycleToCanonicalList c
          have hne_l' := hne' l' hl'_mem
          have hnodup_l' : l'.Nodup := by
            rw [List.nodup_flatten] at hnodup'
            exact hnodup'.1 l' hl'_mem
          -- l'.length > 1 since x is not a fixed point
          have hlen' : 1 < l'.length := by
            by_contra hlen''
            push Not at hlen''
            have hlen1 : l'.length = 1 := by
              have hpos : 0 < l'.length := List.length_pos_iff.mpr hne_l'
              omega
            obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hlen1
            simp only [List.mem_singleton] at hx_l'
            rw [hx_l'] at hx_σ_supp
            have hprod_y := formPerm_prod_apply_eq hpwd' hl'_mem (List.mem_singleton_self y)
            simp only [List.formPerm_singleton] at hprod_y
            unfold dcdListToPerm at hprod'
            rw [hprod'] at hprod_y
            rw [Perm.mem_support] at hx_σ_supp
            simp only [one_apply] at hprod_y
            exact hx_σ_supp hprod_y
          -- l'.formPerm ∈ σ.cycleFactorsFinset
          have hfp_mem' : l'.formPerm ∈ σ.cycleFactorsFinset := by
            unfold dcdListToPerm at hprod'
            exact formPerm_mem_cycleFactorsFinset_of_prod σ hnodup' hpwd' hprod' l' hl'_mem hlen'
          -- l'.formPerm = c since both contain x
          have hx_in_fp : x ∈ l'.formPerm.support := by
            have hne'' : ∀ y : α, l' ≠ [y] := by intro y hy; rw [hy] at hlen'; simp at hlen'
            rw [List.support_formPerm_of_nodup l' hnodup_l' hne'', List.mem_toFinset]
            exact hx_l'
          have hfp_eq_c : l'.formPerm = c := by
            have h1 := eq_cycleOf_of_mem_cycleFactorsFinset_iff σ l'.formPerm hfp_mem' x |>.mpr hx_in_fp
            have h2 := eq_cycleOf_of_mem_cycleFactorsFinset_iff σ c (Finset.mem_toList.mp hc_mem) x |>.mpr hx_supp
            rw [h1, h2]
          -- l' = cycleToCanonicalList c
          have hmin_l' : ∀ y ∈ l', l'.head hne_l' ≤ y := by
            intro y hy
            have h := hmin' l' hl'_mem y hy
            have heq : l'.head! = l'.head hne_l' := by
              cases l' with
              | nil => exact absurd rfl hne_l'
              | cons z zs => simp [List.head!, List.head]
            rw [← heq]; exact h
          have hl'_eq := eq_cycleToCanonicalList_of_formPerm_eq hnodup_l' hlen' c hcycle hfp_eq_c hne_l' hmin_l'
          rw [← hl'_eq]
          exact hl'_mem
        · -- l is a singleton [x] for a fixed point
          simp only [fixedPointsList, List.mem_map] at hl_fixed
          obtain ⟨x, hx_mem, rfl⟩ := hl_fixed
          have hx_fixed : x ∉ σ.support := by
            have hmem := Finset.mem_toList.mp hx_mem
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
            exact hmem
          -- x is in cycleReps'.flatten
          have hx_flat' : x ∈ cycleReps'.flatten := hmem' x
          rw [List.mem_flatten] at hx_flat'
          obtain ⟨l', hl'_mem, hx_l'⟩ := hx_flat'
          -- l' = [x] since x is a fixed point
          have hne_l' := hne' l' hl'_mem
          have hnodup_l' : l'.Nodup := by
            rw [List.nodup_flatten] at hnodup'
            exact hnodup'.1 l' hl'_mem
          have hσx : σ x = x := by
            rw [Perm.mem_support] at hx_fixed
            push Not at hx_fixed
            exact hx_fixed
          have hprod_x := formPerm_prod_apply_eq hpwd' hl'_mem hx_l'
          have hfp_x : l'.formPerm x = x := by
            unfold dcdListToPerm at hprod'
            calc l'.formPerm x = (cycleReps'.map List.formPerm).prod x := hprod_x.symm
              _ = σ x := by rw [hprod']
              _ = x := hσx
          have hlen : l'.length ≤ 1 := by
            by_contra hlen'
            push Not at hlen'
            rw [List.formPerm_apply_mem_eq_self_iff l' hnodup_l' x hx_l'] at hfp_x
            omega
          have hlen1 : l'.length = 1 := by
            have hpos : 0 < l'.length := List.length_pos_iff.mpr hne_l'
            omega
          obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hlen1
          simp only [List.mem_singleton] at hx_l'
          rw [hx_l']
          exact hl'_mem

    -- cycleReps' and canonicalDcd are permutations
    have hperm' : cycleReps'.Perm canonicalDcd := by
      have hnodup_cr' : cycleReps'.Nodup := nodup_of_pairwise_disjoint_nonempty hpwd' hne'
      have hpwd_cd : canonicalDcd.Pairwise List.Disjoint :=
        hperm.pairwise_iff (fun h => h.symm) |>.mpr hpwd
      have hne_cd : ∀ l ∈ canonicalDcd, l ≠ [] := fun l hl => hne_all l (hperm.mem_iff.mp hl)
      have hnodup_cd : canonicalDcd.Nodup := nodup_of_pairwise_disjoint_nonempty hpwd_cd hne_cd
      apply List.perm_of_nodup_nodup_toFinset_eq hnodup_cr' hnodup_cd
      ext l
      simp only [List.mem_toFinset]
      exact hmem_iff l

    -- Both are sorted by strict ordering, so they're equal
    apply List.Perm.eq_of_pairwise (le := fun a b => a.head! > b.head!) ?_ hsort' _ hperm'
    · intro a b _ _ hab hba
      have : a.head! < a.head! := lt_trans hba hab
      exact absurd this (lt_irrefl _)
    · have hge := mergeSort_pairwise_ge allLists
      have hpwd_sorted : canonicalDcd.Pairwise List.Disjoint :=
        hperm.pairwise_iff (fun h => h.symm) |>.mpr hpwd
      have hne_sorted : ∀ l ∈ canonicalDcd, l ≠ [] := fun l hl => hne_all l (hperm.mem_iff.mp hl)
      have hdistinct := heads_nodup_of_pairwise_disjoint hpwd_sorted hne_sorted
      exact pairwise_ge_to_gt_of_nodup hge hdistinct

end CanonicalDCD

end AlgebraicCombinatorics.CycleDecomposition
