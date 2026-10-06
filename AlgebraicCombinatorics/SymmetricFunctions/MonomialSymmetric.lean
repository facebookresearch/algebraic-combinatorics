/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.SymmetricFunctions.NPartition

/-!
# N-partitions and Monomial Symmetric Polynomials

This file formalizes N-partitions and monomial symmetric polynomials,
following Section sec.sf.m of the source.

## Main definitions

* `NPartition N` - a weakly decreasing N-tuple of nonnegative integers
  (Definition def.sf.Npar) — alias for canonical definition in `NPartition.lean`
* `NPartition.size` - the sum of entries of an N-partition (|λ|)
* `NPartition.ofPartition` - converts a partition of length ≤ N to an N-partition
  by padding with zeros (Proposition prop.sf.Npar-as-par) — re-exported from `NPartition.lean`
* `NPartition.toPartition` - converts an N-partition to a partition by removing zeros
  — re-exported from `NPartition.lean`
* `NPartition.equivPartition` - the equivalence (bijection) between partitions of
  length ≤ N and N-partitions (Proposition prop.sf.Npar-as-par)
* `monomialExp` - x^a for a ∈ ℕ^N (Definition def.sf.sort (a))
* `sortTuple` - sorts a tuple in weakly decreasing order (Definition def.sf.sort (b))
* `monomialSymm` - the monomial symmetric polynomial m_λ (Definition def.sf.m)
* `symmHomogeneous` - the submodule of homogeneous symmetric polynomials of degree n
  (Theorem thm.sf.m-basis (c))

## Main results

* `NPartition.bijection_partition` - bijection between partitions of length ≤ N and N-partitions
  (Proposition prop.sf.Npar-as-par)
* `elem_symm_eq_monomialSymm` - e_n expressed via monomial symmetric polynomials
  (Proposition prop.sf.ehp-through-m (a))
* `homog_symm_eq_sum_monomialSymm` - h_n as sum of m_μ over |μ| = n
  (Proposition prop.sf.ehp-through-m (b))
* `power_sum_eq_monomialSymm` - p_n expressed via monomial symmetric polynomials
  (Proposition prop.sf.ehp-through-m (c))
* `monomialSymm_linearIndependent` - the family (m_μ) is linearly independent
  (Theorem thm.sf.m-basis (a), part 1)
* `monomialSymm_spans` - the family (m_μ) spans the symmetric polynomials
  (Theorem thm.sf.m-basis (a), part 2)
* `symm_eq_sum_coeff_monomialSymm` - expansion formula for symmetric polynomials
  (Theorem thm.sf.m-basis (b))
* `monomialSymm_homogeneous_linearIndependent` - the family (m_μ) with |μ| = n is linearly independent
  (Theorem thm.sf.m-basis (d), linear independence)
* `monomialSymm_homogeneous_spans` - the family (m_μ) with |μ| = n spans 𝒮_n
  (Theorem thm.sf.m-basis (d), spanning)
* `monomialSymm_basis_homogeneous` - the family (m_μ) with |μ| = n forms a basis of 𝒮_n
  (Theorem thm.sf.m-basis (d))
* `sigma_coeff_permute` - permutation transforms polynomial coefficients
  (Proposition prop.sf.sigma-pol-coeff)

## References

* Source: AlgebraicCombinatorics/tex/SymmetricFunctions/MonomialSymmetric.tex

## Implementation notes

We use `Fin N → ℕ` to represent N-tuples of nonnegative integers.
The ordering on `Fin N` is the standard one, and "weakly decreasing" means
`∀ i j, i ≤ j → μ j ≤ μ i` (i.e., antitone with respect to the standard order on Fin N).

Mathlib already has `MvPolynomial.msymm` for monomial symmetric polynomials indexed by
`Nat.Partition`. Our `NPartition` provides an alternative indexing that is more natural
for the N-variable setting and corresponds directly to the textbook presentation.
-/

open scoped Polynomial
open MvPolynomial Finset Equiv

namespace AlgebraicCombinatorics

namespace SymmetricFunctions

variable {R : Type*} [CommSemiring R]
variable {N : ℕ}

/-!
## N-partitions (Definition def.sf.Npar)

An N-partition is a weakly decreasing N-tuple of nonnegative integers.

This namespace uses the canonical `NPartition` definition from `NPartition.lean`
(imported above). All basic lemmas (`ext`, `size`, `zero`, `length`, etc.) are
inherited from the canonical definition via the `abbrev` below.
-/

/-- Alias for the canonical `NPartition` type within this namespace.
    An N-partition is a weakly decreasing N-tuple of nonnegative integers.
    (Definition def.sf.Npar)

    This is represented as a function `Fin N → ℕ` that is antitone
    (i.e., `i ≤ j → parts j ≤ parts i`).

    All basic operations (`size`, `length`, `zero`, etc.) and lemmas are inherited
    from the canonical `_root_.NPartition` definition in `NPartition.lean`. -/
abbrev NPartition (N : ℕ) := _root_.NPartition N

namespace NPartition

-- All basic definitions and lemmas (ext, DecidableEq, size, zero, length, etc.)
-- are inherited from _root_.NPartition in NPartition.lean.

/-!
## Bijection with partitions of length ≤ N (Proposition prop.sf.Npar-as-par)

There is a bijection between partitions of length ≤ N and N-partitions.

The core definitions (`ofPartition`, `toPartition`, `ofPartition_size`, `toPartition_card_le`)
are defined in `NPartition.lean` and re-exported here for convenience within this namespace.
-/

-- Re-export canonical definitions from _root_.NPartition to this namespace.
-- This allows code in this file to use `ofPartition`, `toPartition`, etc.
-- without qualification, while avoiding code duplication.

/-- Convert a partition (as a `Nat.Partition`) to an N-partition by padding with zeros.
    Re-export of `_root_.NPartition.ofPartition`. -/
abbrev ofPartition {n : ℕ} (p : Nat.Partition n) (hp : Multiset.card p.parts ≤ N) : NPartition N :=
  _root_.NPartition.ofPartition p hp

/-- Convert an N-partition to a partition by removing trailing zeros.
    Re-export of `_root_.NPartition.toPartition`. -/
abbrev toPartition (mu : NPartition N) : Nat.Partition mu.size :=
  _root_.NPartition.toPartition mu

/-- The size of ofPartition p equals n (the sum of the original partition).
    Re-export of `_root_.NPartition.ofPartition_size`. -/
theorem ofPartition_size {n : ℕ} (p : Nat.Partition n) (hp : Multiset.card p.parts ≤ N) :
    (ofPartition p hp).size = n :=
  _root_.NPartition.ofPartition_size p hp

/-- The number of non-zero parts of an N-partition is at most N.
    Re-export of `_root_.NPartition.toPartition_card_le`. -/
theorem toPartition_card_le (mu : NPartition N) :
    Multiset.card mu.toPartition.parts ≤ N :=
  _root_.NPartition.toPartition_card_le mu

/-- Helper lemma: #{i : Fin n | L[i] = x} = List.count x L -/
private lemma finset_card_filter_get_eq_count {α : Type*} [DecidableEq α] (L : List α) (x : α) :
    (Finset.filter (fun i : Fin L.length => L.get i = x) Finset.univ).card = L.count x := by
  induction L with
  | nil => simp
  | cons a as ih =>
    simp only [List.length_cons, List.count_cons]
    have key : (Finset.filter (fun i : Fin (as.length + 1) => (a :: as).get i = x) Finset.univ).card =
               (if a = x then 1 else 0) + (Finset.filter (fun i : Fin as.length => as.get i = x) Finset.univ).card := by
      let S₀ : Finset (Fin (as.length + 1)) := if a = x then {0} else ∅
      let S₁ : Finset (Fin (as.length + 1)) := (Finset.filter (fun i : Fin as.length => as.get i = x) Finset.univ).map
                                                ⟨Fin.succ, Fin.succ_injective _⟩
      have hS₀_card : S₀.card = if a = x then 1 else 0 := by simp only [S₀]; split_ifs <;> simp
      have hS₁_card : S₁.card = (Finset.filter (fun i : Fin as.length => as.get i = x) Finset.univ).card := by
        simp only [S₁, Finset.card_map]
      have hdisj : Disjoint S₀ S₁ := by
        simp only [S₀, S₁]; rw [Finset.disjoint_left]; intro i hi
        split_ifs at hi with ha
        · simp only [Finset.mem_singleton] at hi
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
                     Function.Embedding.coeFn_mk, not_exists, not_and]
          intro j _; rw [hi]; intro heq; exact Fin.succ_ne_zero j heq
        · simp at hi
      have hunion : Finset.filter (fun i : Fin (as.length + 1) => (a :: as).get i = x) Finset.univ = S₀ ∪ S₁ := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, S₀, S₁]
        constructor
        · intro hi; cases' i using Fin.cases with j
          · left; simp only [List.get_cons_zero] at hi; rw [ite_eq_left hi]; exact Finset.mem_singleton_self 0
          · right; simp only [List.get_eq_getElem] at hi
            simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
            exact ⟨j, hi, rfl⟩
        · intro hi; rcases hi with (hi | hi)
          · split_ifs at hi with ha
            · simp only [Finset.mem_singleton] at hi; subst hi; simp [ha]
            · simp at hi
          · simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hi
            obtain ⟨j, hj, rfl⟩ := hi; simp only [List.get_eq_getElem]; exact hj
      rw [hunion, Finset.card_union_of_disjoint hdisj, hS₀_card, hS₁_card]
    rw [key, ih]
    by_cases ha : a = x
    · simp only [ha, ↓reduceIte, beq_self_eq_true]; ring
    · simp only [ha, ↓reduceIte, beq_false_of_ne ha, Bool.false_eq_true]; ring

/-- Key lemma for left_inv: toPartition (ofPartition p hp).parts = p.parts -/
private lemma toPartition_ofPartition_parts {n : ℕ} (p : Nat.Partition n) (hp : Multiset.card p.parts ≤ N) :
    (ofPartition p hp).toPartition.parts = p.parts := by
  simp only [_root_.NPartition.toPartition, _root_.NPartition.ofPartition]

  set sorted := p.parts.sort (· ≥ ·) with hsorted_def
  set f : Fin N → ℕ := fun i => if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0 with hf_def

  have hlen : sorted.length = Multiset.card p.parts := Multiset.length_sort (· ≥ ·)
  have hsorted_le : sorted.length ≤ N := hlen ▸ hp
  have hsorted_eq : (sorted : Multiset ℕ) = p.parts := by simp [sorted]

  -- All elements of sorted are positive
  have hsorted_pos : ∀ x ∈ sorted, 0 < x := by
    intro x hx
    have : x ∈ p.parts := by rw [← hsorted_eq]; exact Multiset.mem_coe.mpr hx
    exact p.parts_pos this

  -- Prove by multiset extensionality
  ext x
  simp only [Multiset.count_filter, Multiset.count_map]

  by_cases hx : x = 0
  · -- x = 0: both sides are 0
    subst hx
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    symm
    rw [Multiset.count_eq_zero]
    exact fun h => Nat.lt_irrefl 0 (p.parts_pos h)
  · -- x ≠ 0
    rw [ite_eq_left hx, ← hsorted_eq, Multiset.coe_count]

    have hfilter_card : (Finset.filter (fun a : Fin N => x = f a) Finset.univ).card =
                        List.count x sorted := by
      have h_f_val : ∀ i : Fin N, x = f i ↔ ∃ h : i.val < sorted.length, sorted.get ⟨i.val, h⟩ = x := by
        intro i; simp only [f]
        constructor
        · intro heq
          by_cases hlt : i.val < sorted.length
          · exact ⟨hlt, by simp only [hlt, ↓reduceDIte] at heq; exact heq.symm⟩
          · simp only [hlt, ↓reduceDIte] at heq; exact absurd heq hx
        · intro ⟨hlt, hget⟩; simp only [hlt, ↓reduceDIte, hget]

      have hcard_eq : (Finset.filter (fun a : Fin N => x = f a) Finset.univ).card =
                      (Finset.filter (fun a : Fin sorted.length => sorted.get a = x) Finset.univ).card := by
        refine Finset.card_bij (fun i hi => ⟨i.val, ?_⟩) ?_ ?_ ?_
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          obtain ⟨hlt, _⟩ := (h_f_val i).mp hi; exact hlt
        · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          obtain ⟨hlt, hget⟩ := (h_f_val i).mp hi; exact hget
        · intro i j _ _ heq; simp only [Fin.mk.injEq] at heq; exact Fin.ext heq
        · intro j hj; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have hjN : j.val < N := Nat.lt_of_lt_of_le j.isLt hsorted_le
          refine ⟨⟨j.val, hjN⟩, ?_, by simp⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (h_f_val ⟨j.val, hjN⟩).mpr ⟨j.isLt, hj⟩

      rw [hcard_eq, finset_card_filter_get_eq_count]

    exact hfilter_card

/-- Helper lemma: casting a partition preserves its parts. -/
lemma Nat.Partition.parts_cast {m n : ℕ} (h : m = n) (p : Nat.Partition m) :
    (h ▸ p).parts = p.parts := by
  induction h
  rfl

/-- For an antitone function, if f i = 0 and j ≥ i, then f j = 0.
    (Helper for right_inv of equivPartition) -/
private lemma antitone_zero_tail (f : Fin N → ℕ) (hf : Antitone f) (i j : Fin N)
    (hi : f i = 0) (hij : i ≤ j) : f j = 0 := by
  have : f j ≤ f i := hf hij
  omega

/-- For an antitone function f : Fin N → ℕ, the position i is less than the length of
    the filtered list (filter (· ≠ 0)) if and only if f i ≠ 0.
    (Helper for right_inv of equivPartition) -/
private lemma lt_filter_length_iff_ne_zero (f : Fin N → ℕ) (hf : Antitone f) (i : Fin N) :
    i.val < ((List.ofFn f).filter (· ≠ 0)).length ↔ f i ≠ 0 := by
  constructor
  · intro hi hfi
    have hbound : ∀ j : Fin N, f j ≠ 0 → j.val < i.val := fun j hfj => by
      by_contra hge
      push Not at hge
      exact hfj (antitone_zero_tail f hf i j hfi (Fin.mk_le_mk.mpr hge))
    have hlen_le : ((List.ofFn f).filter (· ≠ 0)).length ≤ i.val := by
      rw [List.countP_eq_length_filter.symm]
      have hsplit : List.ofFn f = (List.ofFn f).take i.val ++ (List.ofFn f).drop i.val :=
        (List.take_append_drop i.val (List.ofFn f)).symm
      rw [hsplit, List.countP_append]
      have hdrop_zero : ((List.ofFn f).drop i.val).countP (· ≠ 0) = 0 := by
        apply List.countP_eq_zero.mpr
        intro x hx
        rw [List.mem_drop_iff_getElem] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        simp only [decide_eq_true_eq, not_not, List.getElem_ofFn, List.length_ofFn] at hj ⊢
        exact antitone_zero_tail f hf i ⟨i.val + j, by omega⟩ hfi (Fin.mk_le_mk.mpr (by omega))
      rw [hdrop_zero, add_zero]
      calc ((List.ofFn f).take i.val).countP (· ≠ 0)
          ≤ ((List.ofFn f).take i.val).length := List.countP_le_length
        _ = min i.val N := by simp [List.length_take, List.length_ofFn]
        _ ≤ i.val := min_le_left _ _
    omega
  · intro hfi
    have h_prefix_nonzero : ∀ j : Fin N, j ≤ i → f j ≠ 0 := fun j hji hfj =>
      hfi (antitone_zero_tail f hf j i hfj hji)
    have hiN : i.val + 1 ≤ N := Nat.succ_le_of_lt i.isLt
    have hlen_ge : i.val + 1 ≤ ((List.ofFn f).filter (· ≠ 0)).length := by
      rw [List.countP_eq_length_filter.symm]
      have hsplit : List.ofFn f = (List.ofFn f).take (i.val + 1) ++ (List.ofFn f).drop (i.val + 1) := by
        simp [List.take_append_drop]
      rw [hsplit, List.countP_append]
      have htake_countP : ((List.ofFn f).take (i.val + 1)).countP (· ≠ 0) = i.val + 1 := by
        rw [List.countP_eq_length_filter]
        have hfilter_eq : ((List.ofFn f).take (i.val + 1)).filter (· ≠ 0) =
                          (List.ofFn f).take (i.val + 1) := by
          apply List.filter_eq_self.mpr
          intro x hx
          rw [List.mem_take_iff_getElem] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          simp only [decide_eq_true_eq, List.getElem_ofFn, List.length_ofFn] at hj ⊢
          exact h_prefix_nonzero ⟨j, by omega⟩ (Fin.mk_le_mk.mpr (by omega))
        rw [hfilter_eq]
        simp only [List.length_take, List.length_ofFn, min_eq_left hiN]
      omega
    omega

/-- For an antitone function f : Fin N → ℕ, List.ofFn f is pairwise ≥ (sorted descending).
    (Helper for right_inv of equivPartition) -/
private lemma list_ofFn_pairwise_of_antitone (f : Fin N → ℕ) (hf : Antitone f) :
    (List.ofFn f).Pairwise (· ≥ ·) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  simp only [List.get_ofFn]
  exact hf (Fin.mk_le_mk.mpr (le_of_lt hij))

/-- For an antitone function, filtering zeros preserves the pairwise ≥ property.
    (Helper for right_inv of equivPartition) -/
private lemma filter_nonzero_pairwise_of_antitone (f : Fin N → ℕ) (hf : Antitone f) :
    ((List.ofFn f).filter (· ≠ 0)).Pairwise (· ≥ ·) :=
  List.Pairwise.filter (· ≠ 0) (list_ofFn_pairwise_of_antitone f hf)

/-- For an antitone function, sorting the filtered list gives the same list.
    (Helper for right_inv of equivPartition) -/
private lemma sort_filter_nonzero_eq_self (f : Fin N → ℕ) (hf : Antitone f) :
    (↑((List.ofFn f).filter (· ≠ 0)) : Multiset ℕ).sort (· ≥ ·) =
    (List.ofFn f).filter (· ≠ 0) := by
  simp only [Multiset.coe_sort]
  exact List.mergeSort_eq_self (r := (· ≥ ·)) (filter_nonzero_pairwise_of_antitone f hf)

/-- Finset.univ.val.map f equals the multiset coercion of List.ofFn f.
    (Helper for right_inv of equivPartition) -/
private lemma finset_univ_val_map_eq_ofFn (f : Fin N → ℕ) :
    (Finset.univ.val.map f : Multiset ℕ) = ↑(List.ofFn f) := by
  change (↑(List.map f (List.finRange N)) : Multiset ℕ) = ↑(List.ofFn f)
  rw [List.ofFn_eq_map]

/-- For an antitone function, filtering out zeros gives a prefix of the original list.
    (Helper for right_inv of equivPartition) -/
private lemma filter_nonzero_eq_take (f : Fin N → ℕ) (hf : Antitone f) :
    (List.ofFn f).filter (· ≠ 0) = (List.ofFn f).take ((List.ofFn f).filter (· ≠ 0)).length := by
  set k := ((List.ofFn f).filter (· ≠ 0)).length with hk_def
  have hlen : (List.ofFn f).length = N := List.length_ofFn
  have hk_le : k ≤ N := by
    calc k = ((List.ofFn f).filter (· ≠ 0)).length := rfl
      _ ≤ (List.ofFn f).length := List.length_filter_le _ _
      _ = N := hlen
  -- The filter = take k because:
  -- 1. All elements in positions 0..k-1 are nonzero (so they pass the filter)
  -- 2. All elements in positions k..N-1 are zero (so they don't pass the filter)
  have h_take_all_ne : ∀ x ∈ (List.ofFn f).take k, x ≠ 0 := by
    intro x hx
    rw [List.mem_take_iff_getElem] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    simp only [hlen, List.getElem_ofFn] at hm ⊢
    have hm_lt_k : m < k := by omega
    have hm_lt_N : m < N := by omega
    exact (lt_filter_length_iff_ne_zero f hf ⟨m, hm_lt_N⟩).mp hm_lt_k
  have h_drop_all_zero : ∀ x ∈ (List.ofFn f).drop k, x = 0 := by
    intro x hx
    rw [List.mem_drop_iff_getElem] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    simp only [hlen, List.getElem_ofFn] at hm ⊢
    have hkm_lt_N : k + m < N := by omega
    have h_not_lt : ¬ (k + m < k) := by omega
    by_contra hne
    have : (k + m) < k := (lt_filter_length_iff_ne_zero f hf ⟨k + m, hkm_lt_N⟩).mpr hne
    omega
  have h_take_filter_eq : ((List.ofFn f).take k).filter (· ≠ 0) = (List.ofFn f).take k := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    exact h_take_all_ne x hx
  have h_drop_filter_empty : ((List.ofFn f).drop k).filter (· ≠ 0) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    simp only [decide_eq_true_eq, not_not]
    exact h_drop_all_zero x hx
  calc (List.ofFn f).filter (· ≠ 0)
      = ((List.ofFn f).take k).filter (· ≠ 0) ++ ((List.ofFn f).drop k).filter (· ≠ 0) := by
        rw [← List.filter_append, List.take_append_drop]
    _ = (List.ofFn f).take k ++ [] := by rw [h_take_filter_eq, h_drop_filter_empty]
    _ = (List.ofFn f).take k := List.append_nil _


/-- The equivalence between partitions of length ≤ N that sum to n and N-partitions of size n.
    (Proposition prop.sf.Npar-as-par)

    This provides the bijection:
    - Forward: pad partition with zeros to get N-partition
    - Backward: remove trailing zeros from N-partition to get partition

    Note: We state this as an `Equiv` which is the proper way to express a bijection in Mathlib. -/
noncomputable def equivPartition (n : ℕ) :
    {p : Nat.Partition n // Multiset.card p.parts ≤ N} ≃
    {mu : NPartition N // mu.size = n} where
  toFun := fun ⟨p, hp⟩ => ⟨ofPartition p hp, ofPartition_size p hp⟩
  invFun := fun ⟨mu, hmu⟩ =>
    let p' : Nat.Partition mu.size := mu.toPartition
    let hp' : Multiset.card p'.parts ≤ N := toPartition_card_le mu
    ⟨hmu ▸ p', by subst hmu; exact hp'⟩
  left_inv := by
    simp only
    intro ⟨p, hp⟩
    simp only [Subtype.mk.injEq]
    -- Need: toPartition (ofPartition p hp) = p (up to the size equality cast)
    -- The key is that the parts multiset is preserved
    have hparts := toPartition_ofPartition_parts p hp
    apply Nat.Partition.ext_iff.mpr
    rw [Nat.Partition.parts_cast, hparts]
  right_inv := by
    intro ⟨mu, hmu⟩
    simp only [Subtype.mk.injEq]
    subst hmu
    ext i
    simp only [_root_.NPartition.ofPartition, _root_.NPartition.toPartition]
    have h_univ_map : (Finset.univ.val.map mu.parts : Multiset ℕ) = ↑(List.ofFn mu.parts) :=
      finset_univ_val_map_eq_ofFn mu.parts
    have h_sort_eq : (↑((List.ofFn mu.parts).filter (· ≠ 0)) : Multiset ℕ).sort (· ≥ ·) =
        (List.ofFn mu.parts).filter (· ≠ 0) :=
      sort_filter_nonzero_eq_self mu.parts mu.antitone
    have h1 : ((Finset.univ.val.map mu.parts).filter (· ≠ 0)).sort (· ≥ ·) = 
              (List.ofFn mu.parts).filter (· ≠ 0) := by
      rw [h_univ_map, Multiset.filter_coe, h_sort_eq]
    simp only [h1]
    split_ifs with hi
    · -- Case: i < filter.length, need: filter.get = mu.parts i
      -- The goal has .get instead of [·], so we need to convert
      have h_filter_take := filter_nonzero_eq_take mu.parts mu.antitone
      have h_k_le_N : ((List.ofFn mu.parts).filter (· ≠ 0)).length ≤ N := by
        calc ((List.ofFn mu.parts).filter (· ≠ 0)).length
            ≤ (List.ofFn mu.parts).length := List.length_filter_le _ _
          _ = N := List.length_ofFn
      -- Cast hi to the take version
      have hi' : i.val < ((List.ofFn mu.parts).take ((List.ofFn mu.parts).filter (· ≠ 0)).length).length := by
        rw [List.length_take, List.length_ofFn]
        exact Nat.lt_min.mpr ⟨hi, i.isLt⟩
      -- Rewrite filter.get using filter = take k
      have list_get_eq : ∀ (l1 l2 : List ℕ) (h12 : l1 = l2) (j : ℕ) (hj1 : j < l1.length) (hj2 : j < l2.length),
          l1.get ⟨j, hj1⟩ = l2.get ⟨j, hj2⟩ := by
        intro l1 l2 h12 j hj1 hj2
        subst h12
        rfl
      -- Use h1 to rewrite the goal
      have h2 : (((Finset.univ.val.map mu.parts).filter (· ≠ 0)).sort (· ≥ ·)).get ⟨i.val, by rw [h1]; exact hi⟩ =
                ((List.ofFn mu.parts).filter (· ≠ 0)).get ⟨i.val, hi⟩ :=
        list_get_eq _ _ h1 _ _ hi
      rw [h2]
      -- Now use filter = take k
      have h3 : ((List.ofFn mu.parts).filter (· ≠ 0)).get ⟨i.val, hi⟩ =
                ((List.ofFn mu.parts).take ((List.ofFn mu.parts).filter (· ≠ 0)).length).get ⟨i.val, hi'⟩ :=
        list_get_eq _ _ h_filter_take _ hi hi'
      rw [h3]
      simp only [List.get_eq_getElem, List.getElem_take, List.getElem_ofFn]
    · -- Case: i ≥ filter.length, need: 0 = mu.parts i
      have hge : ¬(i.val < ((List.ofFn mu.parts).filter (· ≠ 0)).length) := hi
      push Not at hge
      have heq : mu.parts i = 0 := by
        by_contra hne
        have : i.val < ((List.ofFn mu.parts).filter (· ≠ 0)).length :=
          (lt_filter_length_iff_ne_zero mu.parts mu.antitone i).mpr hne
        omega
      exact heq.symm
theorem ofPartition_injective (n : ℕ) :
    Function.Injective (fun x : {p : Nat.Partition n // Multiset.card p.parts ≤ N} =>
      ofPartition x.val x.property) := by
  intro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ heq
  simp only [Subtype.mk.injEq]
  have hparts : (ofPartition p₁ hp₁).parts = (ofPartition p₂ hp₂).parts := by
    simp only at heq
    rw [heq]
  have hsorted : p₁.parts.sort (· ≥ ·) = p₂.parts.sort (· ≥ ·) := by
    have len1 : (p₁.parts.sort (· ≥ ·)).length = Multiset.card p₁.parts := Multiset.length_sort ..
    have len2 : (p₂.parts.sort (· ≥ ·)).length = Multiset.card p₂.parts := Multiset.length_sort ..
    apply List.ext_get
    · by_contra hne
      rcases Nat.lt_trichotomy (p₁.parts.sort (· ≥ ·)).length (p₂.parts.sort (· ≥ ·)).length with hlt | heq' | hgt
      · have hi : (p₁.parts.sort (· ≥ ·)).length < N := Nat.lt_of_lt_of_le hlt (len2.symm ▸ hp₂)
        let idx : Fin N := ⟨(p₁.parts.sort (· ≥ ·)).length, hi⟩
        have h1 : (ofPartition p₁ hp₁).parts idx = 0 := by
          simp only [_root_.NPartition.ofPartition, idx]
          split_ifs with h
          · omega
          · rfl
        have h2 : (ofPartition p₂ hp₂).parts idx ≠ 0 := by
          simp only [_root_.NPartition.ofPartition, idx]
          split_ifs with h
          · have hmem : (p₂.parts.sort (· ≥ ·))[(p₁.parts.sort (· ≥ ·)).length]'h ∈ p₂.parts := by
              exact (Multiset.mem_sort _).mp (List.getElem_mem h)
            exact Nat.pos_iff_ne_zero.mp (p₂.parts_pos hmem)
          · omega
        rw [hparts] at h1
        exact h2 h1
      · exact hne heq'
      · have hi : (p₂.parts.sort (· ≥ ·)).length < N := Nat.lt_of_lt_of_le hgt (len1.symm ▸ hp₁)
        let idx : Fin N := ⟨(p₂.parts.sort (· ≥ ·)).length, hi⟩
        have h1 : (ofPartition p₂ hp₂).parts idx = 0 := by
          simp only [_root_.NPartition.ofPartition, idx]
          split_ifs with h
          · omega
          · rfl
        have h2 : (ofPartition p₁ hp₁).parts idx ≠ 0 := by
          simp only [_root_.NPartition.ofPartition, idx]
          split_ifs with h
          · have hmem : (p₁.parts.sort (· ≥ ·))[(p₂.parts.sort (· ≥ ·)).length]'h ∈ p₁.parts := by
              exact (Multiset.mem_sort _).mp (List.getElem_mem h)
            exact Nat.pos_iff_ne_zero.mp (p₁.parts_pos hmem)
          · omega
        rw [hparts] at h2
        exact h2 h1
    · intro i hi1 hi2
      have hi1' : i < N := Nat.lt_of_lt_of_le hi1 (len1.symm ▸ hp₁)
      have hfun := congr_fun hparts ⟨i, hi1'⟩
      simp only [_root_.NPartition.ofPartition] at hfun
      simp only [dite_eq_left hi1, dite_eq_left hi2] at hfun
      exact hfun
  apply Nat.Partition.ext_iff.mpr
  rw [← Multiset.sort_eq p₁.parts (· ≥ ·), ← Multiset.sort_eq p₂.parts (· ≥ ·), hsorted]

/-- The bijection between partitions of length ≤ N and N-partitions
    (Proposition prop.sf.Npar-as-par)

    This is a corollary of `equivPartition` stating that the map is bijective. -/
theorem bijection_partition (n : ℕ) :
    Function.Bijective (fun x : {p : Nat.Partition n // Multiset.card p.parts ≤ N} =>
      (equivPartition n x : {mu : NPartition N // mu.size = n})) :=
  (equivPartition n).bijective

end NPartition

/-!
## Monomials and sorting (Definition def.sf.sort)
-/

/-- The monomial x^a = x₁^{a₁} x₂^{a₂} ⋯ x_N^{a_N} for a tuple a ∈ ℕ^N.
    (Definition def.sf.sort (a)) -/
noncomputable def monomialExp (a : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  ∏ i, X i ^ a i

/-- Sort a tuple in weakly decreasing order to get an N-partition.
    (Definition def.sf.sort (b)) -/
def sortTuple (a : Fin N → ℕ) : NPartition N where
  parts := fun i =>
    let sorted := (Finset.univ.val.map a).sort (· ≥ ·)
    if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0
  antitone := by
    intro i j hij
    simp only
    split_ifs with hi hj hj
    · have hsorted : ((Finset.univ.val.map a).sort (· ≥ ·)).Pairwise (· ≥ ·) :=
        Multiset.pairwise_sort (r := (· ≥ ·)) (Finset.univ.val.map a)
      exact List.Pairwise.rel_get_of_le hsorted hij
    · omega
    · exact Nat.zero_le _
    · exact le_refl 0

/-!
### API for monomialExp (Definition def.sf.sort (a))
-/

set_option backward.isDefEq.respectTransparency false in
/-- `monomialExp` equals the Mathlib monomial with the given exponent. -/
theorem monomialExp_eq_monomial (a : Fin N → ℕ) :
    (monomialExp a : MvPolynomial (Fin N) R) = monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  simp only [monomialExp, monomial_eq, Finsupp.prod_pow]
  congr 1 with i
  simp [Finsupp.equivFunOnFinite]

/-- Coefficient of the monomial x^a in monomialExp a is 1. -/
@[simp]
theorem monomialExp_coeff_self (a : Fin N → ℕ) :
    (monomialExp a : MvPolynomial (Fin N) R).coeff (Finsupp.equivFunOnFinite.symm a) = 1 := by
  rw [monomialExp_eq_monomial, coeff_monomial, ite_eq_left rfl]

/-- Coefficient of a different monomial in monomialExp a is 0. -/
theorem monomialExp_coeff_ne (a b : Fin N → ℕ) (h : a ≠ b) :
    (monomialExp a : MvPolynomial (Fin N) R).coeff (Finsupp.equivFunOnFinite.symm b) = 0 := by
  rw [monomialExp_eq_monomial, coeff_monomial]
  simp only [ite_eq_right_iff]
  intro heq
  exfalso
  apply h
  exact Finsupp.equivFunOnFinite.symm.injective heq

set_option backward.isDefEq.respectTransparency false in
/-- The total degree of monomialExp a is the sum of entries of a (when nonzero). -/
theorem monomialExp_totalDegree [Nontrivial R] (a : Fin N → ℕ) :
    (monomialExp a : MvPolynomial (Fin N) R).totalDegree = ∑ i, a i := by
  rw [monomialExp_eq_monomial]
  rw [MvPolynomial.totalDegree_monomial _ one_ne_zero]
  simp only [Finsupp.sum, Finsupp.equivFunOnFinite]
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun x => a x = 0)]
  simp

/-- monomialExp 0 is 1. -/
@[simp]
theorem monomialExp_zero : (monomialExp (0 : Fin N → ℕ) : MvPolynomial (Fin N) R) = 1 := by
  simp [monomialExp]

/-- monomialExp is multiplicative in the exponent. -/
theorem monomialExp_add (a b : Fin N → ℕ) :
    (monomialExp (a + b) : MvPolynomial (Fin N) R) = monomialExp a * monomialExp b := by
  simp only [monomialExp, Pi.add_apply, pow_add]
  rw [Finset.prod_mul_distrib]

/-!
### API for sortTuple (Definition def.sf.sort (b))
-/

/-- The length of the sorted list equals N. -/
theorem sortTuple_sorted_length (a : Fin N → ℕ) :
    ((Finset.univ.val.map a).sort (· ≥ ·)).length = N := by
  rw [Multiset.length_sort, Multiset.card_map]
  simp [Finset.card_univ]

/-- Access to the sorted list entries for valid indices. -/
theorem sortTuple_parts_eq (a : Fin N → ℕ) (i : Fin N) :
    (sortTuple a).parts i = ((Finset.univ.val.map a).sort (· ≥ ·)).get ⟨i.val, by
      rw [sortTuple_sorted_length]; exact i.isLt⟩ := by
  simp only [sortTuple]
  split_ifs with h
  · rfl
  · exfalso
    rw [sortTuple_sorted_length] at h
    exact h i.isLt

/-- The sum of entries is preserved by sorting. -/
theorem sortTuple_sum_eq (a : Fin N → ℕ) :
    ∑ i, (sortTuple a).parts i = ∑ i, a i := by
  -- Use the fact that the sorted list as multiset equals original multiset
  have hsort : ↑((Finset.univ.val.map a).sort (· ≥ ·)) = Finset.univ.val.map a :=
    Multiset.sort_eq (r := (· ≥ ·)) (Finset.univ.val.map a)
  have hlen : ((Finset.univ.val.map a).sort (· ≥ ·)).length = N := sortTuple_sorted_length a
  -- Sum over sortTuple equals sum of sorted list
  have h1 : ∑ i, (sortTuple a).parts i =
      ((Finset.univ.val.map a).sort (· ≥ ·)).sum := by
    trans (List.ofFn (sortTuple a).parts).sum
    · rw [List.sum_ofFn]
    · congr 1
      apply List.ext_get
      · simp only [List.length_ofFn]
        rw [hlen]
      · intro i hi1 hi2
        simp only [List.length_ofFn] at hi1
        simp only [List.get_ofFn]
        rw [sortTuple_parts_eq]
        congr 1
  rw [h1]
  -- Sum of sorted list equals sum of original multiset
  have h2 : ((Finset.univ.val.map a).sort (· ≥ ·)).sum = (Finset.univ.val.map a).sum := by
    rw [← Multiset.sum_coe, hsort]
  rw [h2]
  simp [Finset.sum_eq_multiset_sum]

/-- The size of sortTuple a equals the sum of entries of a. -/
theorem sortTuple_size (a : Fin N → ℕ) : (sortTuple a).size = ∑ i, a i :=
  sortTuple_sum_eq a

/-- If a tuple is already antitone (weakly decreasing), sorting doesn't change it. -/
theorem sortTuple_of_antitone (a : Fin N → ℕ) (ha : Antitone a) :
    (sortTuple a).parts = a := by
  ext i
  simp only [sortTuple]
  have hlen : ((Finset.univ.val.map a).sort (· ≥ ·)).length = N := sortTuple_sorted_length a
  have hi_lt : i.val < ((Finset.univ.val.map a).sort (· ≥ ·)).length := by rw [hlen]; exact i.isLt
  rw [dite_eq_left hi_lt]
  -- Key: The list (List.ofFn a) is already sorted in decreasing order
  have hsorted : List.Pairwise (· ≥ ·) (List.ofFn a) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    simp only [List.get_ofFn]
    exact ha (le_of_lt hij)
  -- The multiset equals List.ofFn a as a multiset
  have hmulti : Finset.univ.val.map a = ↑(List.ofFn a) := by
    simp only [Finset.univ, Fintype.elems, Multiset.map_coe]
    rw [List.ofFn_eq_map]
  -- mergeSort of a sorted list is the same list
  have hmerge : List.mergeSort (List.ofFn a) (fun x y => x ≥ y) = List.ofFn a := by
    apply List.mergeSort_eq_self
    exact hsorted
  -- The sorted list equals List.ofFn a
  have hsort_eq : (Finset.univ.val.map a).sort (· ≥ ·) = List.ofFn a := by
    rw [hmulti]
    simp only [Multiset.coe_sort]
    exact hmerge
  -- Use List.get_of_eq to handle the dependent type
  have hi_lt' : i.val < (List.ofFn a).length := by simp
  show ((Finset.univ.val.map a).sort (· ≥ ·)).get ⟨i.val, hi_lt⟩ = a i
  rw [List.get_of_eq hsort_eq, List.get_ofFn, Fin.cast_mk]

/-- Sorting an NPartition's parts returns the same NPartition. -/
theorem sortTuple_of_NPartition (mu : NPartition N) :
    sortTuple mu.parts = mu := by
  ext
  exact congrFun (sortTuple_of_antitone mu.parts mu.antitone) _

/-- Sorting is idempotent: sorting an already sorted tuple gives the same tuple. -/
theorem sortTuple_idempotent (a : Fin N → ℕ) :
    sortTuple (sortTuple a).parts = sortTuple a :=
  sortTuple_of_NPartition (sortTuple a)

/-!
## Addition of N-partitions

The `Add (NPartition N)` instance and related lemmas (`add_size`, `add_comm`, `add_zero`,
`zero_add`, `add_assoc`) are provided by the canonical `NPartition.lean` file.

The canonical definition uses component-wise addition (without sorting), which is equivalent
to sorting the sum for N-partitions since the sum of two antitone functions is antitone.
This is witnessed by `sortTuple_of_NPartition`.
-/

/-- Two tuples have the same sort if and only if one is a permutation of the other.
    (Two tuples have the same multiset of values iff they sort to the same N-partition.) -/
theorem sortTuple_eq_iff (a b : Fin N → ℕ) :
    sortTuple a = sortTuple b ↔
    (Finset.univ.val.map a) = (Finset.univ.val.map b) := by
  constructor
  · -- Forward: If sortTuple a = sortTuple b, then the multisets are equal
    intro h
    -- The sorted lists are equal (since NPartition.parts are equal)
    have h_parts : (sortTuple a).parts = (sortTuple b).parts := congrArg NPartition.parts h
    -- The sorted lists as multisets equal the original multisets
    have ha_sort : ↑((Finset.univ.val.map a).sort (· ≥ ·)) = Finset.univ.val.map a :=
      Multiset.sort_eq (r := (· ≥ ·)) (Finset.univ.val.map a)
    have hb_sort : ↑((Finset.univ.val.map b).sort (· ≥ ·)) = Finset.univ.val.map b :=
      Multiset.sort_eq (r := (· ≥ ·)) (Finset.univ.val.map b)
    -- We need to show the sorted lists are equal as lists
    have hlen_a : ((Finset.univ.val.map a).sort (· ≥ ·)).length = N := sortTuple_sorted_length a
    have hlen_b : ((Finset.univ.val.map b).sort (· ≥ ·)).length = N := sortTuple_sorted_length b
    -- Extract the sorted lists
    let sorted_a := (Finset.univ.val.map a).sort (· ≥ ·)
    let sorted_b := (Finset.univ.val.map b).sort (· ≥ ·)
    -- Show sorted_a = sorted_b as lists
    have h_lists_eq : sorted_a = sorted_b := by
      apply List.ext_get
      · rw [hlen_a, hlen_b]
      · intro n h1 h2
        have hn_a : n < N := by rw [← hlen_a]; exact h1
        have hn_b : n < N := by rw [← hlen_b]; exact h2
        -- (sortTuple a).parts ⟨n, hn_a⟩ = sorted_a.get ⟨n, h1⟩
        have eq_a : (sortTuple a).parts ⟨n, hn_a⟩ = sorted_a.get ⟨n, h1⟩ := by
          simp only [sortTuple]
          rw [dite_eq_left h1]
        have eq_b : (sortTuple b).parts ⟨n, hn_b⟩ = sorted_b.get ⟨n, h2⟩ := by
          simp only [sortTuple]
          rw [dite_eq_left h2]
        rw [← eq_a, ← eq_b]
        exact congrFun h_parts ⟨n, hn_a⟩
    -- Now use that equal lists have equal multisets
    calc Finset.univ.val.map a = ↑sorted_a := ha_sort.symm
      _ = ↑sorted_b := by rw [h_lists_eq]
      _ = Finset.univ.val.map b := hb_sort
  · -- Backward: If multisets are equal, then sorting gives the same result
    intro h
    -- If the multisets are equal, sorting them gives the same sorted list
    have h_sorted_eq : (Finset.univ.val.map a).sort (· ≥ ·) = (Finset.univ.val.map b).sort (· ≥ ·) := by
      rw [h]
    -- Show parts are equal by showing the defining functions agree
    apply NPartition.ext
    funext i
    simp only [sortTuple]
    -- Use the fact that the sorted lists are equal
    have hlen_eq : ((Finset.univ.val.map a).sort (· ≥ ·)).length =
                   ((Finset.univ.val.map b).sort (· ≥ ·)).length := by
      rw [h_sorted_eq]
    split_ifs with ha hb hb
    · -- Both conditions hold: use that equal lists have equal elements
      simp only [List.get_eq_getElem, h_sorted_eq]
    · -- ha holds but hb doesn't - contradiction since lengths are equal
      rw [hlen_eq] at ha
      exact absurd ha hb
    · -- ha doesn't hold but hb does - contradiction since lengths are equal
      rw [← hlen_eq] at hb
      exact absurd hb ha
    · -- Neither condition holds
      rfl

/-!
### Helper lemmas for symmetry proof

The following lemmas establish that sorting is invariant under permutation of the input,
which is the key insight for proving that monomial symmetric polynomials are symmetric.
-/

/-- The multiset of values is preserved under permutation of the domain.
    This is the key lemma showing that permuting the indices of a tuple
    doesn't change its multiset of values. -/
private lemma map_comp_perm_eq (a : Fin N → ℕ) (σ : Perm (Fin N)) :
    (Finset.univ.val.map (a ∘ σ)) = (Finset.univ.val.map a) := by
  rw [← Multiset.map_map]
  congr 1
  have h : Multiset.map σ (Finset.univ : Finset (Fin N)).val = (Finset.univ : Finset (Fin N)).val := by
    ext x
    simp only [Multiset.count_map]
    have key : (Multiset.filter (fun y => x = σ y) (Finset.univ : Finset (Fin N)).val).card = 1 := by
      have h1 : (Multiset.filter (fun y => x = σ y) (Finset.univ : Finset (Fin N)).val) =
                (Finset.filter (fun y => x = σ y) (Finset.univ : Finset (Fin N))).val := rfl
      rw [h1, Finset.card_val, Finset.card_eq_one]
      use σ⁻¹ x
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hy; exact σ.injective (by simp [hy])
      · intro hy; simp [hy]
    rw [key, Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin N)).nodup]
    exact Finset.mem_univ x
  exact h

/-- Sorting is invariant under permutation of the input tuple.
    This is the key insight: sortTuple (a ∘ σ) = sortTuple a for any permutation σ,
    because sorting only depends on the multiset of values, not their order. -/
lemma sortTuple_comp_perm (a : Fin N → ℕ) (σ : Perm (Fin N)) :
    sortTuple (a ∘ σ) = sortTuple a := by
  ext i
  unfold sortTuple
  simp only
  rw [map_comp_perm_eq a σ]

/-- Applying rename σ to a monomial x^a gives x^(a ∘ σ⁻¹). -/
private lemma rename_monomialExp (σ : Perm (Fin N)) (a : Fin N → ℕ) :
    rename σ (monomialExp (R := R) a) = monomialExp (a ∘ σ.symm) := by
  simp only [monomialExp]
  rw [map_prod]
  conv_lhs =>
    arg 2
    ext i
    rw [map_pow, rename_X]
  rw [← Finset.prod_equiv σ.symm]
  · simp
  · intro i _
    simp [Function.comp]

/-!
## Monomial symmetric polynomials (Definition def.sf.m)
-/

/-- The set of tuples a ∈ ℕ^N with sort(a) = μ and entries bounded by μ.size.
    This is a finite set since entries are bounded. -/
def sortPreimage (mu : NPartition N) : Finset (Fin N → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (mu.size + 1))).filter
    (fun a => sortTuple a = mu)

/-- The monomial symmetric polynomial m_μ corresponding to an N-partition μ.
    (Definition def.sf.m)

    m_μ = ∑_{a ∈ ℕ^N : sort(a) = μ} x^a

    This is the sum of all monomials whose exponent tuple sorts to μ. -/
noncomputable def monomialSymm (mu : NPartition N) : MvPolynomial (Fin N) R :=
  ∑ a ∈ sortPreimage mu, monomialExp a

/-- Permutation preserves membership in sortPreimage.
    If a is in the preimage of μ under sorting, then so is a ∘ σ.symm. -/
private lemma mem_sortPreimage_comp_perm {a : Fin N → ℕ} {mu : NPartition N} (σ : Perm (Fin N))
    (ha : a ∈ sortPreimage mu) : (a ∘ σ.symm) ∈ sortPreimage mu := by
  simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset] at ha ⊢
  refine ⟨?_, ?_⟩
  · intro i
    have := ha.1 (σ.symm i)
    simp only [Finset.mem_range] at this ⊢
    exact this
  · rw [sortTuple_comp_perm, ha.2]

/-- Permutation preserves membership in sortPreimage (variant with σ instead of σ.symm). -/
private lemma mem_sortPreimage_comp_perm' {a : Fin N → ℕ} {mu : NPartition N} (σ : Perm (Fin N))
    (ha : a ∈ sortPreimage mu) : (a ∘ σ) ∈ sortPreimage mu := by
  have h := mem_sortPreimage_comp_perm σ⁻¹ ha
  convert h; rfl

/-- The monomial symmetric polynomial is symmetric.
    (Follows from Definition def.sf.m)

    The proof uses the fact that:
    1. rename σ (monomialExp a) = monomialExp (a ∘ σ⁻¹)
    2. sortTuple (a ∘ σ) = sortTuple a for any permutation σ
    3. Therefore the sum over sortPreimage μ is invariant under rename σ -/
theorem monomialSymm_isSymmetric (mu : NPartition N) :
    (monomialSymm mu : MvPolynomial (Fin N) R).IsSymmetric := by
  intro σ
  simp only [monomialSymm]
  rw [map_sum]
  -- Rewrite each term using rename_monomialExp
  conv_lhs =>
    arg 2
    ext a
    rw [rename_monomialExp]
  -- The sum ∑ a ∈ sortPreimage mu, monomialExp (a ∘ σ.symm) equals
  -- ∑ a ∈ sortPreimage mu, monomialExp a because composition with σ.symm
  -- is a bijection on sortPreimage mu
  exact Finset.sum_bij' (fun a _ => a ∘ σ.symm) (fun b _ => b ∘ σ)
    (fun a ha => mem_sortPreimage_comp_perm σ ha)
    (fun b hb => mem_sortPreimage_comp_perm' σ hb)
    (fun a _ => by ext i; exact congrArg a (σ.symm_apply_apply i))
    (fun b _ => by ext i; exact congrArg b (σ.apply_symm_apply i))
    (fun a _ => rfl)

/-- The parts of an N-partition belong to its sortPreimage.
    This is because sorting an already sorted (antitone) tuple gives the same tuple. -/
lemma parts_mem_sortPreimage (mu : NPartition N) : mu.parts ∈ sortPreimage mu := by
  simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · intro i
    simp only [Finset.mem_range]
    calc mu.parts i ≤ mu.size := NPartition.parts_le_size mu i
      _ < mu.size + 1 := Nat.lt_succ_self _
  · exact sortTuple_of_NPartition mu

/-- The coefficient of x^{μ.parts} in m_μ is 1.
    This is because μ.parts is the unique element of sortPreimage μ that equals μ.parts. -/
lemma monomialSymm_coeff_self (mu : NPartition N) :
    (monomialSymm mu : MvPolynomial (Fin N) R).coeff (Finsupp.equivFunOnFinite.symm mu.parts) = 1 := by
  simp only [monomialSymm]
  rw [coeff_sum]
  have h : ∑ a ∈ sortPreimage mu, (monomialExp (R := R) a).coeff (Finsupp.equivFunOnFinite.symm mu.parts) =
      (monomialExp (R := R) mu.parts).coeff (Finsupp.equivFunOnFinite.symm mu.parts) := by
    rw [Finset.sum_eq_single_of_mem mu.parts (parts_mem_sortPreimage mu)]
    intro b _ hne
    rw [monomialExp_eq_monomial, coeff_monomial]
    simp only [ite_eq_right_iff]
    intro heq
    exfalso
    apply hne
    exact (Finsupp.equivFunOnFinite.symm.injective heq.symm).symm
  rw [h, monomialExp_eq_monomial, coeff_monomial, ite_eq_left rfl]

/-- The coefficient of x^{μ.parts} in m_ν is 0 when μ ≠ ν.
    This is because the only monomial in m_ν with exponent sorting to ν must have
    exponent ν.parts (when looking at the sorted exponent), not μ.parts. -/
lemma monomialSymm_coeff_ne (mu nu : NPartition N) (h : mu ≠ nu) :
    (monomialSymm nu : MvPolynomial (Fin N) R).coeff (Finsupp.equivFunOnFinite.symm mu.parts) = 0 := by
  simp only [monomialSymm]
  rw [coeff_sum]
  apply Finset.sum_eq_zero
  intro a ha
  rw [monomialExp_eq_monomial, coeff_monomial]
  simp only [ite_eq_right_iff]
  intro heq
  exfalso
  simp only [sortPreimage, Finset.mem_filter] at ha
  have ha_sort : sortTuple a = nu := ha.2
  have heq' : a = mu.parts := Finsupp.equivFunOnFinite.symm.injective heq
  rw [heq', sortTuple_of_NPartition] at ha_sort
  exact h ha_sort

/-!
## Elementary, homogeneous, and power sum via monomial symmetric polynomials
    (Proposition prop.sf.ehp-through-m)
-/

/-- The N-partition (1, 1, ..., 1, 0, 0, ..., 0) with n ones and N-n zeros. -/
def onesThenZeros (n : ℕ) (_hn : n ≤ N) : NPartition N where
  parts := fun i => if i.val < n then 1 else 0
  antitone := by
    intro i j hij
    simp only
    split_ifs with hi hj hj
    · exact le_refl 1
    · omega
    · exact Nat.zero_le _
    · exact le_refl 0

/-- The N-partition (n, 0, 0, ..., 0) with n in the first position and zeros elsewhere. -/
def singletonPartition (n : ℕ) (_hN : 0 < N) : NPartition N where
  parts := fun i => if i.val = 0 then n else 0
  antitone := by
    intro i j hij
    -- Goal: (if j.val = 0 then n else 0) ≤ (if i.val = 0 then n else 0)
    simp only
    split_ifs with h1 h2
    · -- h1 : j.val = 0, h2 : i.val = 0
      exact le_refl n
    · -- h1 : j.val = 0, h2 : ¬ i.val = 0
      -- Goal: n ≤ 0
      -- But j.val = 0 and i ≤ j means i.val ≤ 0, so i.val = 0, contradiction with h2
      have : i.val ≤ j.val := hij
      omega
    · -- h1 : ¬ j.val = 0, h2 : i.val = 0
      -- Goal: 0 ≤ n
      exact Nat.zero_le _
    · -- h1 : ¬ j.val = 0, h2 : ¬ i.val = 0
      exact le_refl 0

/-!
### Helper lemmas for Proposition prop.sf.ehp-through-m

These lemmas express the elementary, complete homogeneous, and power sum symmetric
polynomials in terms of products over all variables with appropriate exponents.
-/

/-- The product over a subset equals the product with indicator exponents. -/
private lemma prod_subset_eq_prod_indicator (S : Finset (Fin N)) :
    (∏ i ∈ S, X i : MvPolynomial (Fin N) R) =
    ∏ j : Fin N, X j ^ (if j ∈ S then 1 else 0) := by
  conv_rhs =>
    arg 2
    ext j
    rw [show (X j : MvPolynomial (Fin N) R) ^ (if j ∈ S then 1 else 0) =
        if j ∈ S then X j else 1 by split_ifs <;> simp]
  rw [Finset.prod_ite (p := fun j => j ∈ S)]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.prod_const_one, mul_one]

/-- The power X i ^ n equals the product with a single nonzero exponent. -/
private lemma X_pow_eq_prod_single (i : Fin N) (n : ℕ) :
    (X i : MvPolynomial (Fin N) R) ^ n = ∏ j : Fin N, X j ^ (if j = i then n else 0) := by
  conv_rhs =>
    arg 2
    ext j
    rw [show (X j : MvPolynomial (Fin N) R) ^ (if j = i then n else 0) =
        if j = i then X j ^ n else 1 by split_ifs <;> simp]
  rw [Finset.prod_ite_eq' Finset.univ i (fun j => X j ^ n)]
  simp

/-- Multiset product as product over all elements with count exponents. -/
private lemma multiset_prod_map_X_eq_prod_pow (s : Multiset (Fin N)) :
    (s.map (X : Fin N → MvPolynomial (Fin N) R)).prod =
    ∏ i : Fin N, X i ^ (Multiset.count i s) := by
  rw [Finset.prod_multiset_map_count s X]
  rw [← Finset.prod_subset (s.toFinset.subset_univ)]
  intro i _ hi
  simp only [Multiset.mem_toFinset] at hi
  rw [Multiset.count_eq_zero.mpr hi]
  simp

/-- The indicator tuple for a set S. -/
private def indicatorTuple (S : Finset (Fin N)) : Fin N → ℕ := fun j => if j ∈ S then 1 else 0

/-- The single tuple with n at position i. -/
private def singleTuple (i : Fin N) (n : ℕ) : Fin N → ℕ := fun j => if j = i then n else 0

/-- The count tuple for a Sym element. -/
private def countTuple {n : ℕ} (s : Sym (Fin N) n) : Fin N → ℕ := fun i => Multiset.count i s.1

set_option backward.isDefEq.respectTransparency false in
/-- The indicator tuple of an n-element subset sorts to onesThenZeros n. -/
private lemma sortTuple_indicatorTuple {n : ℕ} (S : Finset (Fin N)) (hn : S.card = n) (hn' : n ≤ N) :
    sortTuple (indicatorTuple S) = onesThenZeros n hn' := by
  -- Key insight: Both indicatorTuple S and onesThenZeros.parts have the same multiset of values
  -- (n ones and N-n zeros), so they sort to the same result.
  -- Since onesThenZeros is already an NPartition (antitone), sorting it gives itself.
  rw [← sortTuple_of_NPartition (onesThenZeros n hn')]
  rw [sortTuple_eq_iff]
  -- Now we show the multisets are equal
  rw [Multiset.ext]
  intro v
  simp only [Multiset.count_map, indicatorTuple, onesThenZeros]
  -- Convert multiset filter to finset filter for easier reasoning
  conv_lhs => rw [show (Multiset.filter (fun a : Fin N => v = if a ∈ S then 1 else 0) Finset.univ.val).card =
                       (Finset.univ.filter (fun a : Fin N => v = if a ∈ S then 1 else 0)).card by rfl]
  conv_rhs => rw [show (Multiset.filter (fun a : Fin N => v = if a.val < n then 1 else 0) Finset.univ.val).card =
                       (Finset.univ.filter (fun a : Fin N => v = if a.val < n then 1 else 0)).card by rfl]
  by_cases hv0 : v = 0
  · -- Case v = 0: count is N - n for both
    subst hv0
    have h1 : (Finset.univ.filter (fun j : Fin N => 0 = (if j ∈ S then 1 else 0))) = Finset.univ \ S := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · intro h hj; rw [ite_eq_left hj] at h; exact Nat.zero_ne_one h
      · intro hj; rw [ite_eq_right hj]
    have h2 : (Finset.univ.filter (fun j : Fin N => 0 = (if j.val < n then 1 else 0))) =
              Finset.univ.filter (fun j : Fin N => n ≤ j.val) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; by_contra hj; push Not at hj; rw [ite_eq_left hj] at h; exact Nat.zero_ne_one h
      · intro hj; rw [ite_eq_right (not_lt.mpr hj)]
    have h3 : (Finset.univ.filter (fun j : Fin N => n ≤ j.val)).card = N - n := by
      have hbij : (Finset.univ.filter (fun j : Fin N => n ≤ j.val)) =
                  (Finset.univ : Finset (Fin (N - n))).map
                    ⟨fun k => ⟨k.val + n, Nat.add_lt_of_lt_sub k.isLt⟩,
                     fun a b h => by simp only [Fin.mk.injEq] at h; omega⟩ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                   Function.Embedding.coeFn_mk, Fin.ext_iff]
        constructor
        · intro hj
          have hlt : j.val - n < N - n := Nat.sub_lt_sub_right hj j.isLt
          exact ⟨⟨j.val - n, hlt⟩, Nat.sub_add_cancel hj⟩
        · intro ⟨k, hk⟩; omega
      rw [hbij, Finset.card_map, Finset.card_fin]
    rw [h1, h2, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hn, h3]
  · by_cases hv1 : v = 1
    · -- Case v = 1: count is n for both
      subst hv1
      have h1 : (Finset.univ.filter (fun j : Fin N => 1 = (if j ∈ S then 1 else 0))) = S := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; by_contra hj; rw [ite_eq_right hj] at h; exact Nat.one_ne_zero h
        · intro hj; rw [ite_eq_left hj]
      have h2 : (Finset.univ.filter (fun j : Fin N => 1 = (if j.val < n then 1 else 0))) =
                Finset.univ.filter (fun j : Fin N => j.val < n) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; by_contra hj; push Not at hj; rw [ite_eq_right (not_lt.mpr hj)] at h; exact Nat.one_ne_zero h
        · intro hj; rw [ite_eq_left hj]
      have h3 : (Finset.univ.filter (fun j : Fin N => j.val < n)).card = n := by
        have hbij : (Finset.univ.filter (fun j : Fin N => j.val < n)) =
                    (Finset.univ : Finset (Fin n)).map ⟨Fin.castLE hn', Fin.castLE_injective hn'⟩ := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                     Function.Embedding.coeFn_mk]
          constructor
          · intro hj; exact ⟨⟨j.val, hj⟩, by simp [Fin.castLE]⟩
          · intro ⟨k, hk⟩; simp only [Fin.castLE, Fin.ext_iff] at hk; omega
        rw [hbij, Finset.card_map, Finset.card_fin]
      rw [h1, h2, hn, h3]
    · -- Case v ≠ 0 and v ≠ 1: both counts are 0
      have h1 : (Finset.univ.filter (fun j : Fin N => v = (if j ∈ S then 1 else 0))) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j _; split_ifs with hj; exact hv1; exact hv0
      have h2 : (Finset.univ.filter (fun j : Fin N => v = (if j.val < n then 1 else 0))) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j _; split_ifs with hj; exact hv1; exact hv0
      rw [h1, h2]

/-- The single tuple with n at position i sorts to singletonPartition n. -/
private lemma sortTuple_singleTuple (i : Fin N) (n : ℕ) (hN : 0 < N) :
    sortTuple (singleTuple i n) = singletonPartition n hN := by
  -- Key insight: singleTuple i n = (singletonPartition n hN).parts ∘ (swap ⟨0, hN⟩ i)
  -- This is because singleTuple has n at position i and 0 elsewhere,
  -- while singletonPartition has n at position 0 and 0 elsewhere.
  -- The swap permutation maps 0 ↔ i, so composing gives the same values.
  have h_eq : singleTuple i n = (singletonPartition n hN).parts ∘ (Equiv.swap ⟨0, hN⟩ i) := by
    ext j
    simp only [singleTuple, singletonPartition, Function.comp_apply]
    by_cases hj : j = i
    · simp only [hj, ↓reduceIte, Equiv.swap_apply_right]
    · by_cases hj0 : j = ⟨0, hN⟩
      · simp only [hj0, Equiv.swap_apply_left]
        by_cases hi0 : i = ⟨0, hN⟩
        · exact absurd (hj0.trans hi0.symm) hj
        · have hi0_val : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
          simp only [hi0_val, ↓reduceIte, Ne.symm hi0, ↓reduceIte]
      · simp only [hj, ↓reduceIte, Equiv.swap_apply_of_ne_of_ne hj0 hj]
        have hj_ne_0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        simp only [hj_ne_0, ↓reduceIte]
  rw [h_eq, sortTuple_comp_perm, sortTuple_of_NPartition]

/-- The count tuple sorts to an N-partition of size n. -/
private lemma sortTuple_countTuple_size {n : ℕ} (s : Sym (Fin N) n) :
    (sortTuple (countTuple s)).size = n := by
  rw [sortTuple_size]
  simp only [countTuple]
  -- Sum of counts equals card of multiset
  have h : ∑ i : Fin N, Multiset.count i s.1 = s.1.card := by
    rw [← Multiset.toFinset_sum_count_eq s.1]
    symm
    apply Finset.sum_subset s.1.toFinset.subset_univ
    intro i _ hi
    simp only [Multiset.mem_toFinset] at hi
    exact Multiset.count_eq_zero.mpr hi
  rw [h, s.2]

/-- Indicator tuple is in sortPreimage of onesThenZeros. -/
private lemma indicatorTuple_mem_sortPreimage {n : ℕ} (S : Finset (Fin N)) (hn : S.card = n) (hn' : n ≤ N) :
    indicatorTuple S ∈ sortPreimage (onesThenZeros n hn') := by
  simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · intro i
    simp only [indicatorTuple, onesThenZeros, NPartition.size]
    -- The size of onesThenZeros n is n (sum of n ones)
    -- Each entry of indicatorTuple is 0 or 1, so < n + 1
    -- First, compute the sum: ∑ j, if j.val < n then 1 else 0 = n
    have hsum : ∑ j : Fin N, (if j.val < n then 1 else 0) = n := by
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      have : (Finset.univ.filter (fun j : Fin N => j.val < n)) =
             (Finset.univ : Finset (Fin n)).map ⟨Fin.castLE hn', Fin.castLE_injective hn'⟩ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                   Function.Embedding.coeFn_mk]
        constructor
        · intro hj
          exact ⟨⟨j.val, hj⟩, by simp [Fin.castLE]⟩
        · intro ⟨k, hk⟩
          simp only [Fin.castLE, Fin.ext_iff] at hk
          omega
      rw [this, Finset.card_map, Finset.card_fin]
    rw [hsum]
    -- Now goal is: (if i ∈ S then 1 else 0) < n + 1
    split_ifs with hi
    · -- i ∈ S, indicator is 1, need 1 < n + 1
      have : S.Nonempty := ⟨i, hi⟩
      have : 0 < S.card := Finset.card_pos.mpr this
      omega
    · -- i ∉ S, indicator is 0, need 0 < n + 1
      omega
  · exact sortTuple_indicatorTuple S hn hn'

set_option backward.isDefEq.respectTransparency false in
/-- Single tuple is in sortPreimage of singletonPartition. -/
private lemma singleTuple_mem_sortPreimage (i : Fin N) (n : ℕ) (hN : 0 < N) :
    singleTuple i n ∈ sortPreimage (singletonPartition n hN) := by
  simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    singleTuple, singletonPartition, NPartition.size]
  constructor
  · intro j
    -- The size of singletonPartition n is n
    -- Each entry of singleTuple is 0 or n, so < n + 1
    have hsize : ∑ k : Fin N, (if k.val = 0 then n else 0) = n := by
      conv_lhs => arg 2; ext k; rw [show (if k.val = 0 then n else 0) =
                                        if k = ⟨0, hN⟩ then n else 0 by simp [Fin.ext_iff]]
      simp [Finset.sum_ite_eq']
    rw [hsize]
    split_ifs <;> omega
  · exact sortTuple_singleTuple i n hN

/-- monomialExp of singleTuple i n equals X i ^ n.
    This is a key helper for `power_sum_eq_monomialSymm`. -/
private lemma monomialExp_singleTuple (i : Fin N) (n : ℕ) :
    (monomialExp (singleTuple i n) : MvPolynomial (Fin N) R) = X i ^ n := by
  simp only [monomialExp, singleTuple]
  conv_lhs =>
    arg 2
    ext j
    rw [show (X j : MvPolynomial (Fin N) R) ^ (if j = i then n else 0) =
        if j = i then X j ^ n else 1 by
      split_ifs with h <;> simp [h]]
  simp [Finset.prod_ite_eq']

/-- Values in sortPreimage of singletonPartition are either 0 or n.
    This follows because sortTuple preserves multisets, and singletonPartition has only 0s and one n. -/
private lemma sortPreimage_singletonPartition_values (a : Fin N → ℕ) (n : ℕ) (hN : 0 < N)
    (ha : a ∈ sortPreimage (singletonPartition n hN)) (i : Fin N) :
    a i = 0 ∨ a i = n := by
  simp only [sortPreimage, Finset.mem_filter] at ha
  -- sortTuple a = singletonPartition n means the multisets are equal
  have hmulti : Finset.univ.val.map a = Finset.univ.val.map (singletonPartition n hN).parts := by
    rw [← sortTuple_eq_iff]
    rw [ha.2, sortTuple_of_NPartition]
  -- From hmulti, we know a i is in the multiset of singletonPartition values
  have hmem : a i ∈ Finset.univ.val.map (singletonPartition n hN).parts := by
    rw [← hmulti]
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, singletonPartition] at hmem
  obtain ⟨j, hj⟩ := hmem
  by_cases hj0 : j.val = 0
  · simp only [ite_eq_left hj0] at hj
    right; exact hj.symm
  · simp only [ite_eq_right hj0] at hj
    left; exact hj.symm

/-- If a ∈ sortPreimage (singletonPartition n hN) and n > 0, then a = singleTuple i n for some i. -/
private lemma mem_sortPreimage_singletonPartition_exists_singleTuple (a : Fin N → ℕ) (n : ℕ) (hn : n ≠ 0) (hN : 0 < N)
    (ha : a ∈ sortPreimage (singletonPartition n hN)) :
    ∃ i, a = singleTuple i n := by
  -- The sum of a equals n (since sortTuple preserves sum and singletonPartition has size n)
  have hsum : ∑ j, a j = n := by
    have h1 := sortTuple_sum_eq a
    simp only [sortPreimage, Finset.mem_filter] at ha
    rw [ha.2] at h1
    simp only [singletonPartition] at h1
    convert h1.symm
    conv_rhs => arg 2; ext k; rw [show (if k.val = 0 then n else 0) =
                                      if k = ⟨0, hN⟩ then n else 0 by simp [Fin.ext_iff]]
    simp [Finset.sum_ite_eq']
  -- Since all values are 0 or n and sum is n, exactly one value is n
  -- Find an index with value n
  have hexists : ∃ i, a i = n := by
    by_contra hall
    push Not at hall
    -- If all values are 0 or n but none is n, all are 0
    have hall0 : ∀ i, a i = 0 := by
      intro i
      rcases sortPreimage_singletonPartition_values a n hN ha i with h0 | hn'
      · exact h0
      · exact absurd hn' (hall i)
    -- But sum is n > 0, contradiction
    simp only [hall0, Finset.sum_const_zero] at hsum
    exact hn hsum.symm
  obtain ⟨i, hi⟩ := hexists
  use i
  ext j
  simp only [singleTuple]
  by_cases hji : j = i
  · simp [hji, hi]
  · simp only [hji, ↓reduceIte]
    -- j ≠ i, and a j is either 0 or n
    rcases sortPreimage_singletonPartition_values a n hN ha j with h0 | hn'
    · exact h0
    · -- If a j = n and a i = n with j ≠ i, then sum ≥ 2n > n (contradiction)
      exfalso
      have h2n : a i + a j ≤ ∑ k, a k := by
        have hsub : ({i, j} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
        calc a i + a j = ∑ k ∈ ({i, j} : Finset (Fin N)), a k := by
               simp [Finset.sum_pair (Ne.symm hji)]
             _ ≤ ∑ k, a k := Finset.sum_le_sum_of_subset hsub
      rw [hi, hn', hsum] at h2n
      omega

/-- The inverse map for indicator tuples: the support of a 0-1 tuple. -/
private def indicatorSupport (a : Fin N → ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => a i = 1)

set_option backward.isDefEq.respectTransparency false in
/-- indicatorSupport ∘ indicatorTuple = id -/
private lemma indicatorSupport_indicatorTuple (S : Finset (Fin N)) :
    indicatorSupport (indicatorTuple S) = S := by
  ext i
  simp only [indicatorSupport, indicatorTuple, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hne
    simp only [ite_eq_right hne] at h
    exact Nat.one_ne_zero h.symm
  · intro h
    simp only [ite_eq_left h]

/-- Values in sortPreimage of onesThenZeros are in {0, 1}.
    This follows because sortTuple preserves multisets, and onesThenZeros has only 0s and 1s. -/
private lemma sortPreimage_onesThenZeros_values {n : ℕ} (a : Fin N → ℕ) (hn' : n ≤ N)
    (ha : a ∈ sortPreimage (onesThenZeros n hn')) (i : Fin N) :
    a i = 0 ∨ a i = 1 := by
  simp only [sortPreimage, Finset.mem_filter] at ha
  -- sortTuple a = onesThenZeros n means the multisets are equal
  have hmulti : Finset.univ.val.map a = Finset.univ.val.map (onesThenZeros n hn').parts := by
    rw [← sortTuple_eq_iff]
    rw [ha.2, sortTuple_of_NPartition]
  -- From hmulti, we know a i is in the multiset of onesThenZeros values
  have hmem : a i ∈ Finset.univ.val.map (onesThenZeros n hn').parts := by
    rw [← hmulti]
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩
  simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, onesThenZeros] at hmem
  obtain ⟨j, hj⟩ := hmem
  by_cases hjn : j.val < n
  · simp only [ite_eq_left hjn] at hj
    right; exact hj.symm
  · simp only [ite_eq_right hjn] at hj
    left; exact hj.symm

/-- indicatorTuple ∘ indicatorSupport = id for elements of sortPreimage of onesThenZeros. -/
private lemma indicatorTuple_indicatorSupport {n : ℕ} (a : Fin N → ℕ) (hn' : n ≤ N)
    (ha : a ∈ sortPreimage (onesThenZeros n hn')) :
    indicatorTuple (indicatorSupport a) = a := by
  ext i
  simp only [indicatorTuple, indicatorSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases sortPreimage_onesThenZeros_values a hn' ha i with h0 | h1
  · simp [h0]
  · simp [h1]

/-- The cardinality of indicatorSupport for elements of sortPreimage of onesThenZeros equals n. -/
private lemma indicatorSupport_card {n : ℕ} (a : Fin N → ℕ) (hn' : n ≤ N)
    (ha : a ∈ sortPreimage (onesThenZeros n hn')) :
    (indicatorSupport a).card = n := by
  simp only [sortPreimage, Finset.mem_filter] at ha
  -- The sum of a equals n
  have hsum : ∑ i, a i = n := by
    calc ∑ i, a i = (sortTuple a).size := (sortTuple_size a).symm
      _ = (onesThenZeros n hn').size := by rw [ha.2]
      _ = n := by
        simp only [NPartition.size, onesThenZeros]
        rw [Finset.sum_boole]
        simp only [Nat.cast_id]
        have : (Finset.univ.filter (fun j : Fin N => j.val < n)) =
               (Finset.univ : Finset (Fin n)).map ⟨Fin.castLE hn', Fin.castLE_injective hn'⟩ := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                     Function.Embedding.coeFn_mk]
          constructor
          · intro hj; exact ⟨⟨j.val, hj⟩, by simp [Fin.castLE]⟩
          · intro ⟨k, hk⟩; simp only [Fin.castLE, Fin.ext_iff] at hk; omega
        rw [this, Finset.card_map, Finset.card_fin]
  -- Since a has values in {0, 1}, the sum equals the cardinality of indicatorSupport
  have ha' : a ∈ sortPreimage (onesThenZeros n hn') := by
    simp only [sortPreimage, Finset.mem_filter]
    exact ha
  have h : ∑ i, a i = (indicatorSupport a).card := by
    simp only [indicatorSupport, Finset.card_filter]
    rw [Finset.sum_congr rfl]
    intro i _
    rcases sortPreimage_onesThenZeros_values a hn' ha' i with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [← h, hsum]

/-- The product over a subset equals monomialExp of the indicator tuple. -/
private lemma prod_subset_eq_monomialExp (S : Finset (Fin N)) :
    (∏ i ∈ S, X i : MvPolynomial (Fin N) R) = monomialExp (indicatorTuple S) := by
  simp only [monomialExp, indicatorTuple]
  rw [prod_subset_eq_prod_indicator]

/-- e_n = m_{(1,1,...,1,0,0,...,0)} where there are n ones.
    (Proposition prop.sf.ehp-through-m (a))

    The proof uses the fact that esymm n is the sum over n-element subsets S of ∏_{i∈S} X_i,
    and each such product equals X^{χ_S} where χ_S is the indicator function of S.
    All indicator functions of n-element subsets sort to the same N-partition (1,...,1,0,...,0).

    Label: prop.sf.ehp-through-m.a -/
theorem elem_symm_eq_monomialSymm [DecidableEq (Fin N)] (n : ℕ) (hn : n ≤ N) :
    esymm (Fin N) R n = monomialSymm (onesThenZeros n hn) := by
  -- esymm n = ∑_{S : |S| = n} ∏_{i ∈ S} X_i
  -- monomialSymm (1,...,1,0,...,0) = ∑_{a : sort(a) = (1,...,1,0,...,0)} X^a
  simp only [esymm, monomialSymm]
  -- Use sum_bij' to establish a bijection between powersetCard n univ and sortPreimage
  apply Finset.sum_bij' (fun S _ => indicatorTuple S) (fun a _ => indicatorSupport a)
  -- indicatorTuple maps to sortPreimage
  · intro S hS
    have hcard : S.card = n := Finset.mem_powersetCard.mp hS |>.2
    exact indicatorTuple_mem_sortPreimage S hcard hn
  -- indicatorSupport maps to powersetCard
  · intro a ha
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, indicatorSupport_card a hn ha⟩
  -- Left inverse: indicatorSupport ∘ indicatorTuple = id
  · intro S _
    exact indicatorSupport_indicatorTuple S
  -- Right inverse: indicatorTuple ∘ indicatorSupport = id
  · intro a ha
    exact indicatorTuple_indicatorSupport a hn ha
  -- The terms match: ∏ i ∈ S, X i = monomialExp (indicatorTuple S)
  · intro S _
    exact prod_subset_eq_monomialExp S

/-- The set of N-partitions of a given size, as a finite set.
    This is finite because each entry is bounded by the size. -/
def NPartitionsOfSize (n : ℕ) : Finset (NPartition N) :=
  (Fintype.piFinset (fun _ => Finset.range (n + 1))).image
    (fun f => sortTuple f) |>.filter (fun mu => mu.size = n)

/-- Membership characterization for NPartitionsOfSize: an N-partition is in
    NPartitionsOfSize n if and only if its size equals n. -/
theorem mem_NPartitionsOfSize (mu : NPartition N) (n : ℕ) :
    mu ∈ NPartitionsOfSize n ↔ mu.size = n := by
  simp only [NPartitionsOfSize, Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset,
    Finset.mem_range, and_iff_right_iff_imp]
  intro hsize
  refine ⟨mu.parts, ?_, ?_⟩
  · intro i
    calc mu.parts i ≤ mu.size := NPartition.parts_le_size mu i
      _ = n := hsize
      _ < n + 1 := Nat.lt_succ_self n
  · -- sortTuple of an antitone tuple is the tuple itself
    exact sortTuple_of_NPartition mu

/-- The set of N-partitions of size n is finite.
    This provides a Fintype instance for the subtype { μ : NPartition N // μ.size = n }.

    This is needed for:
    1. Counting arguments involving N-partitions of fixed size
    2. Finite sums over N-partitions in the monomial symmetric polynomial basis theorems
    3. The basis theorem `thm.sf.m-basis` which requires finiteness of N-partitions of each degree -/
instance fintype_of_size (n : ℕ) : Fintype { μ : NPartition N // μ.size = n } :=
  Fintype.ofFinset (NPartitionsOfSize n) (fun mu => mem_NPartitionsOfSize mu n)

/-- The set of N-partitions of size n is finite (set version).
    This is the Set.Finite version of fintype_of_size. -/
theorem finite_of_size (n : ℕ) : Set.Finite { μ : NPartition N | μ.size = n } := by
  haveI : Fintype { μ : NPartition N // μ.size = n } := fintype_of_size n
  haveI : Finite { μ : NPartition N // μ.size = n } := Finite.of_fintype _
  exact Set.finite_coe_iff.mp this

/-- h_n = ∑_{|μ| = n} m_μ where the sum is over N-partitions of size n.
    (Proposition prop.sf.ehp-through-m (b))

    The proof uses the bijection between Sym (Fin N) n and tuples f : Fin N → ℕ with ∑ f = n,
    given by the count function. Each term (s.1.map X).prod = ∏ i, X i ^ (count i s)
    corresponds to a monomial X^f. Sorting partitions these tuples by their N-partition,
    so hsymm n = ∑_{|μ| = n} m_μ.

    Label: prop.sf.ehp-through-m.b -/
theorem homog_symm_eq_sum_monomialSymm [DecidableEq (Fin N)] (n : ℕ) :
    hsymm (Fin N) R n = ∑ mu ∈ NPartitionsOfSize n, monomialSymm mu := by
  -- hsymm n = ∑_{s : Sym (Fin N) n} (s.1.map X).prod
  --         = ∑_{s : Sym (Fin N) n} ∏ i, X i ^ (count i s)
  --         = ∑_{f : ∑ f = n} X^f
  --         = ∑_{|μ| = n} ∑_{sort(f) = μ} X^f
  --         = ∑_{|μ| = n} m_μ
  -- Step 1: Rewrite hsymm and transform each term to monomialExp
  simp only [hsymm]
  conv_lhs =>
    arg 2
    ext s
    rw [show (s.1.map X : Multiset (MvPolynomial (Fin N) R)).prod = monomialExp (fun i => s.1.count i) by
      simp only [monomialExp]
      rw [Finset.prod_multiset_map_count]
      -- Need to show: ∏ m ∈ s.1.toFinset, X m ^ count m s.1 = ∏ i, X i ^ count i s.1
      -- The RHS is over all of Fin N, the LHS is only over elements in s.1
      -- But for elements not in s.1, count is 0, so X i ^ 0 = 1
      apply Finset.prod_subset s.1.toFinset.subset_univ
      intro i _ hi
      simp only [Multiset.mem_toFinset] at hi
      rw [Multiset.count_eq_zero.mpr hi, pow_zero]]
  -- Step 2: Use the bijection between Sym (Fin N) n and piAntidiag univ n
  have huniv : (Finset.univ : Finset (Fin N)).sym n = Finset.univ := by ext s; simp
  let countEmbed : Sym (Fin N) n ↪ (Fin N → ℕ) :=
    ⟨fun m a => m.1.count a, Multiset.count_injective.comp Sym.coe_injective⟩
  have hmap : Finset.map countEmbed ((Finset.univ : Finset (Fin N)).sym n) =
              Finset.piAntidiag Finset.univ n :=
    Finset.map_sym_eq_piAntidiag (Finset.univ : Finset (Fin N)) n
  -- Step 3: Transform sum over Sym to sum over piAntidiag
  have h_sym_to_piAntidiag : ∑ s : Sym (Fin N) n, (monomialExp (fun i => s.1.count i) : MvPolynomial (Fin N) R) =
            ∑ f ∈ Finset.piAntidiag Finset.univ n, monomialExp f := by
    calc ∑ s : Sym (Fin N) n, (monomialExp (fun i => s.1.count i) : MvPolynomial (Fin N) R)
        = ∑ s : Sym (Fin N) n, monomialExp (countEmbed s) := rfl
      _ = ∑ s ∈ Finset.univ, monomialExp (countEmbed s) := rfl
      _ = ∑ s ∈ (Finset.univ : Finset (Fin N)).sym n, monomialExp (countEmbed s) := by rw [huniv]
      _ = ∑ f ∈ ((Finset.univ : Finset (Fin N)).sym n).map countEmbed, monomialExp f := by rw [Finset.sum_map]
      _ = ∑ f ∈ Finset.piAntidiag Finset.univ n, monomialExp f := by rw [hmap]
  rw [h_sym_to_piAntidiag]
  -- Step 4: Partition piAntidiag by sortTuple
  -- The sortPreimages are pairwise disjoint
  have h_disjoint : (↑(NPartitionsOfSize (N := N) n) : Set (NPartition N)).PairwiseDisjoint sortPreimage := by
    intro mu _ nu _ hne
    simp only [Function.onFun, Finset.disjoint_iff_ne]
    intro f hf g hg heq
    simp only [sortPreimage, Finset.mem_filter] at hf hg
    rw [heq] at hf
    exact hne (hf.2.symm.trans hg.2)
  -- piAntidiag univ n = disjoint union of sortPreimage mu over NPartitionsOfSize n
  have h_partition : Finset.piAntidiag (Finset.univ : Finset (Fin N)) n =
      (NPartitionsOfSize n).biUnion sortPreimage := by
    ext f
    simp only [Finset.mem_piAntidiag, Finset.mem_biUnion, ne_eq]
    constructor
    · intro ⟨hsum, _⟩
      let mu := sortTuple f
      use mu
      constructor
      · simp only [NPartitionsOfSize, Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset,
          Finset.mem_range]
        constructor
        · refine ⟨f, ?_, rfl⟩
          intro i
          have h1 : f i ≤ ∑ j, f j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          linarith
        · rw [sortTuple_size, hsum]
      · simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        constructor
        · intro i
          have hmu_size : mu.size = n := by rw [sortTuple_size, hsum]
          have h1 : f i ≤ ∑ j, f j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          linarith
        · rfl
    · intro ⟨mu, hmu, hf⟩
      simp only [NPartitionsOfSize, Finset.mem_filter] at hmu
      simp only [sortPreimage, Finset.mem_filter] at hf
      constructor
      · calc ∑ i, f i = (sortTuple f).size := (sortTuple_size f).symm
          _ = mu.size := by rw [hf.2]
          _ = n := hmu.2
      · intro i _; exact Finset.mem_univ i
  -- Step 5: Conclude
  rw [h_partition, Finset.sum_biUnion h_disjoint]
  rfl

/-- p_n = m_{(n,0,0,...,0)} when N > 0 and n > 0.
    (Proposition prop.sf.ehp-through-m (c))

    **Important**: This theorem requires `n > 0`. The case `n = 0` is FALSE when `N > 1`:
    - `psum 0 = ∑ i, X i ^ 0 = N` (the constant polynomial N)
    - `monomialSymm (singletonPartition 0 hN) = 1` (since the only tuple sorting to
      (0,...,0) is the zero tuple, and `monomialExp (0,...,0) = 1`)

    The TeX source (MonomialSymmetric.tex, line 133) states "For each n ∈ ℕ, we have
    p_n = m_{(n,0,0,...,0)}" which is mathematically incorrect for n = 0 when N > 1.

    The proof uses the fact that psum n = ∑ i, X i ^ n, and each term X i ^ n
    corresponds to the tuple (0,...,0,n,0,...,0) with n at position i.
    All N such tuples sort to the same N-partition (n, 0, 0, ..., 0).

    When n > 0, the sortPreimage of (n, 0, ..., 0) consists exactly of the N single
    tuples (0,...,0,n,0,...,0), giving the bijection needed for the proof.

    Label: prop.sf.ehp-through-m.c -/
theorem power_sum_eq_monomialSymm [DecidableEq (Fin N)] (n : ℕ) (hn : n ≠ 0) (hN : 0 < N) :
    psum (Fin N) R n = monomialSymm (singletonPartition n hN) := by
  -- psum n = ∑ i, X i ^ n
  --        = ∑ i, ∏ j, X j ^ (if j = i then n else 0)
  --        = ∑ i, monomialExp (singleTuple i n)
  -- The sortPreimage of (n, 0, ..., 0) consists exactly of the N single tuples
  -- So monomialSymm (n, 0, ..., 0) = ∑_{a ∈ sortPreimage} monomialExp a = ∑ i, monomialExp (singleTuple i n)
  simp only [psum, monomialSymm]
  -- Rewrite LHS using monomialExp_singleTuple
  conv_lhs =>
    arg 2
    ext i
    rw [← monomialExp_singleTuple (R := R) i n]
  -- Now goal is: ∑ i, monomialExp (singleTuple i n) = ∑ a ∈ sortPreimage ..., monomialExp a
  -- Use Finset.sum_bij to establish the bijection
  apply Finset.sum_bij (fun i _ => singleTuple i n)
  · -- singleTuple i n ∈ sortPreimage (singletonPartition n hN)
    intro i _
    exact singleTuple_mem_sortPreimage i n hN
  · -- Injectivity: singleTuple i n = singleTuple j n implies i = j
    intro i _ j _ hij
    by_contra hne
    -- singleTuple i n at position i is n, but singleTuple j n at position i is 0 (since i ≠ j)
    have h1 : singleTuple i n i = n := by simp [singleTuple]
    have h2 : singleTuple j n i = 0 := by simp [singleTuple, hne]
    rw [hij] at h1
    rw [h1] at h2
    exact hn h2
  · -- Surjectivity: every a ∈ sortPreimage is singleTuple i n for some i
    intro a ha
    obtain ⟨i, hi⟩ := mem_sortPreimage_singletonPartition_exists_singleTuple a n hn hN ha
    exact ⟨i, Finset.mem_univ i, hi.symm⟩
  · -- The function values are equal (trivially true since we're applying the same function)
    intro i _
    rfl

/-- The n = 0 case: p_0 = N while m_{(0,...,0)} = 1.

    This documents why `power_sum_eq_monomialSymm` requires `n ≠ 0`.
    When n = 0:
    - `psum 0 = ∑ i, X i ^ 0 = N` (constant polynomial)
    - `monomialSymm (singletonPartition 0 hN) = 1` (single monomial x^0 = 1)

    These are equal only when N = 1. -/
theorem psum_zero_eq_N : psum (Fin N) R 0 = N := by
  simp only [psum, pow_zero, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]

theorem monomialSymm_zero_partition_eq_one (hN : 0 < N) :
    monomialSymm (R := R) (singletonPartition 0 hN) = 1 := by
  -- The zero partition (0, 0, ..., 0) has sortPreimage = {(0, 0, ..., 0)}
  -- and monomialExp (0, ..., 0) = x^0 = 1
  -- Proof outline:
  -- 1. sortPreimage of (0,...,0) contains only the zero tuple because:
  --    - The size of (0,...,0) is 0
  --    - Each entry a_j must satisfy a_j < 0 + 1 = 1, so a_j = 0
  -- 2. monomialExp (0,...,0) = ∏_j X_j^0 = 1
  -- Step 1: singletonPartition 0 hN = 0
  have h_eq_zero : singletonPartition 0 hN = (0 : NPartition N) := by
    ext i
    simp only [singletonPartition, NPartition.zero_parts]
    simp
  rw [h_eq_zero]
  -- Step 2: sortPreimage 0 = {0}
  have h_sortTuple_zero : sortTuple (0 : Fin N → ℕ) = (0 : NPartition N) := by
    ext i
    simp only [sortTuple, NPartition.zero_parts, Pi.zero_apply]
    split_ifs with h
    · have hsorted_mem : ∀ x ∈ (Finset.univ.val.map (0 : Fin N → ℕ)).sort (· ≥ ·), x = 0 := by
        intro x hx
        rw [Multiset.mem_sort] at hx
        simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Pi.zero_apply] at hx
        obtain ⟨_, rfl⟩ := hx
        rfl
      exact hsorted_mem _ (List.get_mem _ ⟨i.val, h⟩)
    · rfl
  have h_preimage : sortPreimage (0 : NPartition N) = {0} := by
    ext a
    simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
    constructor
    · intro ⟨ha_range, _⟩
      ext i
      specialize ha_range i
      simp only [NPartition.zero_size, Finset.mem_range] at ha_range
      simp only [Pi.zero_apply]
      omega
    · intro ha
      constructor
      · intro i
        rw [ha, NPartition.zero_size, Pi.zero_apply]
        simp
      · rw [ha]
        exact h_sortTuple_zero
  -- Step 3: monomialSymm 0 = monomialExp 0 = 1
  simp only [monomialSymm, h_preimage, Finset.sum_singleton]
  exact monomialExp_zero

/-!
## Permutation action on polynomial coefficients (Proposition prop.sf.sigma-pol-coeff)
-/

/-- The coefficient of a monomial in σ · f equals the coefficient of the permuted
    monomial in f.
    (Proposition prop.sf.sigma-pol-coeff)

    [x₁^{a₁} x₂^{a₂} ⋯ x_N^{a_N}](σ · f) = [x₁^{a_{σ(1)}} x₂^{a_{σ(2)}} ⋯ x_N^{a_{σ(N)}}] f

    Label: prop.sf.sigma-pol-coeff -/
theorem sigma_coeff_permute (sigma : Perm (Fin N)) (f : MvPolynomial (Fin N) R)
    (a : Fin N → ℕ) :
    (rename sigma f).coeff (Finsupp.equivFunOnFinite.symm a) =
    f.coeff (Finsupp.equivFunOnFinite.symm (a ∘ sigma)) := by
  -- Write the exponent `a` as the image of `a ∘ sigma` under `sigma`, then use that
  -- `rename sigma` maps coefficients along the injective map `sigma`.
  classical
  have hA : Finsupp.equivFunOnFinite.symm a =
      Finsupp.mapDomain sigma (Finsupp.equivFunOnFinite.symm (a ∘ sigma)) := by
    ext i
    rw [Finsupp.mapDomain_equiv_apply]
    simp
  rw [hA, coeff_rename_mapDomain sigma sigma.injective]

/-!
## Basis theorem for monomial symmetric polynomials (Theorem thm.sf.m-basis)
-/

/-- The monomial symmetric polynomials are linearly independent.
    (Theorem thm.sf.m-basis (a), linear independence part)

    Label: thm.sf.m-basis.a.indep -/
theorem monomialSymm_linearIndependent (S : Finset (NPartition N)) :
    LinearIndependent R (fun mu : S => (monomialSymm mu.val : MvPolynomial (Fin N) R)) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg mu
  -- Extract the coefficient of mu.parts from the sum
  have key :
      (∑ nu : S, f nu • monomialSymm nu.val : MvPolynomial (Fin N) R).coeff
        (Finsupp.equivFunOnFinite.symm mu.val.parts) =
      (∑ nu : S, g nu • monomialSymm nu.val : MvPolynomial (Fin N) R).coeff
        (Finsupp.equivFunOnFinite.symm mu.val.parts) := by
    rw [hfg]
  simp only [coeff_sum, coeff_smul] at key
  -- The sum simplifies because only the term with nu = mu contributes
  have hf : ∑ nu : S, f nu • (monomialSymm nu.val : MvPolynomial (Fin N) R).coeff
      (Finsupp.equivFunOnFinite.symm mu.val.parts) = f mu := by
    rw [Finset.sum_eq_single_of_mem mu (Finset.mem_univ mu)]
    · simp [monomialSymm_coeff_self]
    · intro nu _ hne
      simp only [smul_eq_mul]
      have hne' : mu.val ≠ nu.val := fun heq => hne (Subtype.ext heq.symm)
      rw [monomialSymm_coeff_ne mu.val nu.val hne', mul_zero]
  have hg : ∑ nu : S, g nu • (monomialSymm nu.val : MvPolynomial (Fin N) R).coeff
      (Finsupp.equivFunOnFinite.symm mu.val.parts) = g mu := by
    rw [Finset.sum_eq_single_of_mem mu (Finset.mem_univ mu)]
    · simp [monomialSymm_coeff_self]
    · intro nu _ hne
      simp only [smul_eq_mul]
      have hne' : mu.val ≠ nu.val := fun heq => hne (Subtype.ext heq.symm)
      rw [monomialSymm_coeff_ne mu.val nu.val hne', mul_zero]
  rw [hf, hg] at key
  exact key

/-- Key: coeff is constant on orbits for symmetric polynomials.
    If f is symmetric and σ is a permutation, then coeff (σ · d) f = coeff d f. -/
lemma coeff_perm_eq_of_symmetric (f : MvPolynomial (Fin N) R) (hf : f.IsSymmetric)
    (d : Fin N →₀ ℕ) (σ : Perm (Fin N)) :
    f.coeff (Finsupp.mapDomain σ d) = f.coeff d := by
  have h1 : rename σ f = f := hf σ
  have key : (rename σ f).coeff (Finsupp.mapDomain σ d) = f.coeff d := by
    exact coeff_rename_mapDomain σ σ.injective f d
  rw [h1] at key
  exact key

/-- For symmetric f, support is closed under permutation. -/
lemma support_closed_under_perm (f : MvPolynomial (Fin N) R) (hf : f.IsSymmetric)
    (d : Fin N →₀ ℕ) (hd : d ∈ f.support) (σ : Perm (Fin N)) :
    Finsupp.mapDomain σ d ∈ f.support := by
  rw [mem_support_iff] at hd ⊢
  rw [coeff_perm_eq_of_symmetric f hf d σ]
  exact hd

/-- Partitioning a sum by a function. -/
private lemma sum_partition {α β M : Type*} [DecidableEq α] [DecidableEq β] [AddCommMonoid M]
    (s : Finset α) (f : α → β) (g : α → M) :
    ∑ x ∈ s, g x = ∑ y ∈ s.image f, ∑ x ∈ s.filter (fun x => f x = y), g x := by
  rw [← Finset.sum_biUnion]
  · congr 1
    ext x
    simp only [mem_biUnion, mem_image, mem_filter]
    constructor
    · intro hx
      exact ⟨f x, ⟨x, hx, rfl⟩, hx, rfl⟩
    · intro ⟨_, _, hx, _⟩
      exact hx
  · intro y1 _ y2 _ hne
    simp only [Function.onFun, Finset.disjoint_filter]
    intro x _ hx1
    simp only [hx1]
    exact hne

/-- sortTupleFinsupp applied to a Finsupp. -/
noncomputable def sortTupleFinsupp (d : Fin N →₀ ℕ) : NPartition N :=
  sortTuple (Finsupp.equivFunOnFinite d)

/-- sortTupleFinsupp is invariant under permutation. -/
lemma sortTupleFinsupp_perm (d : Fin N →₀ ℕ) (σ : Perm (Fin N)) :
    sortTupleFinsupp (Finsupp.mapDomain σ d) = sortTupleFinsupp d := by
  unfold sortTupleFinsupp
  have h : Finsupp.equivFunOnFinite (Finsupp.mapDomain σ d) =
           (Finsupp.equivFunOnFinite d) ∘ σ.symm := by
    ext i
    simp [Finsupp.mapDomain_equiv_apply]
  rw [h, sortTuple_comp_perm]

/-- Helper lemma for constructing permutations from equal fiber cardinalities. -/
private lemma fiber_equiv_val_eq {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α]
    (a b : α → β) (hcount : ∀ v, (Finset.univ.filter (fun i => a i = v)).card =
                                  (Finset.univ.filter (fun i => b i = v)).card)
    (v w : β) (hvw : v = w) (j : α)
    (hj_v : j ∈ Finset.univ.filter (fun k => b k = v))
    (hj_w : j ∈ Finset.univ.filter (fun k => b k = w)) :
    ((Finset.equivOfCardEq (hcount v)).symm ⟨j, hj_v⟩).val =
    ((Finset.equivOfCardEq (hcount w)).symm ⟨j, hj_w⟩).val := by
  subst hvw
  rfl

/-- Key combinatorial fact: if two functions from a finite type have the same
    multiset of values, then they differ by a permutation. -/
private lemma exists_perm_of_map_eq {α : Type*} [Fintype α] [DecidableEq α] {β : Type*} [DecidableEq β]
    (a b : α → β) (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ σ : Perm α, ∀ i, b i = a (σ i) := by
  classical
  have hcount : ∀ v, (Finset.univ.filter (fun i => a i = v)).card =
                     (Finset.univ.filter (fun i => b i = v)).card := by
    intro v
    have ha : (Finset.univ.filter (fun i => a i = v)).card = Multiset.count v (Finset.univ.val.map a) := by
      rw [Multiset.count_map]
      have h : Multiset.filter (fun a_1 => v = a a_1) Finset.univ.val =
               Multiset.filter (fun a_1 => a a_1 = v) Finset.univ.val := by
        congr 1; ext x; exact eq_comm
      rw [h]; rfl
    have hb : (Finset.univ.filter (fun i => b i = v)).card = Multiset.count v (Finset.univ.val.map b) := by
      rw [Multiset.count_map]
      have h : Multiset.filter (fun a_1 => v = b a_1) Finset.univ.val =
               Multiset.filter (fun a_1 => b a_1 = v) Finset.univ.val := by
        congr 1; ext x; exact eq_comm
      rw [h]; rfl
    rw [ha, hb, h]
  let fiber_equiv : ∀ v, (Finset.univ.filter (fun i => a i = v)) ≃
                         (Finset.univ.filter (fun i => b i = v)) :=
    fun v => Finset.equivOfCardEq (hcount v)
  let σ : α → α := fun i =>
    let hi : i ∈ Finset.univ.filter (fun j => b j = b i) := by simp
    ((fiber_equiv (b i)).symm ⟨i, hi⟩).val
  have hσ_prop : ∀ i, a (σ i) = b i := by
    intro i
    simp only [σ]
    have hi : i ∈ Finset.univ.filter (fun j => b j = b i) := by simp
    have hσi := ((fiber_equiv (b i)).symm ⟨i, hi⟩).prop
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσi
    exact hσi
  have hσ_inj : Function.Injective σ := by
    intro i j hij
    have hbi_eq_bj : b i = b j := by
      rw [← hσ_prop i, ← hσ_prop j, hij]
    have hi' : i ∈ Finset.univ.filter (fun k => b k = b i) := by simp
    have hj'' : j ∈ Finset.univ.filter (fun k => b k = b i) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, hbi_eq_bj.symm⟩
    have hinj := (fiber_equiv (b i)).symm.injective
    have heq : (⟨i, hi'⟩ : (Finset.univ.filter (fun k => b k = b i))) =
               (⟨j, hj''⟩ : (Finset.univ.filter (fun k => b k = b i))) := by
      apply hinj
      apply Subtype.ext
      simp only [σ] at hij
      have hbj_eq_bi : b j = b i := hbi_eq_bj.symm
      have h1 : ((fiber_equiv (b i)).symm ⟨i, hi'⟩).val = σ i := rfl
      have h2 : σ j = ((fiber_equiv (b j)).symm ⟨j, by simp⟩).val := rfl
      have h3 : ((fiber_equiv (b j)).symm ⟨j, by simp⟩).val =
                ((fiber_equiv (b i)).symm ⟨j, hj''⟩).val :=
        fiber_equiv_val_eq a b hcount (b j) (b i) hbj_eq_bi j (by simp) hj''
      calc ((fiber_equiv (b i)).symm ⟨i, hi'⟩).val
          = σ i := h1
        _ = σ j := hij
        _ = ((fiber_equiv (b j)).symm ⟨j, by simp⟩).val := h2
        _ = ((fiber_equiv (b i)).symm ⟨j, hj''⟩).val := h3
    simp only [Subtype.mk.injEq] at heq
    exact heq
  have hσ_bij : Function.Bijective σ := ⟨hσ_inj, Finite.surjective_of_injective hσ_inj⟩
  use Equiv.ofBijective σ hσ_bij
  intro i
  simp only [Equiv.ofBijective_apply]
  exact (hσ_prop i).symm

/-- If two tuples have the same sort, they have the same multiset of values. -/
private lemma sortTuple_eq_implies_multiset_eq (a b : Fin N → ℕ)
    (h : sortTuple a = sortTuple b) :
    (Finset.univ.val.map a) = (Finset.univ.val.map b) := by
  have hlen_a : ((Finset.univ.val.map a).sort (· ≥ ·)).length = N := by
    rw [Multiset.length_sort, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  have hlen_b : ((Finset.univ.val.map b).sort (· ≥ ·)).length = N := by
    rw [Multiset.length_sort, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  have h_parts : ∀ i : Fin N, (sortTuple a).parts i = (sortTuple b).parts i := by
    intro i
    rw [h]
  have h_sorted_eq : (Finset.univ.val.map a).sort (· ≥ ·) = (Finset.univ.val.map b).sort (· ≥ ·) := by
    apply List.ext_get
    · rw [hlen_a, hlen_b]
    · intro n h1 h2
      have hn : n < N := by rw [← hlen_a]; exact h1
      have hp := h_parts ⟨n, hn⟩
      simp only [sortTuple] at hp
      simp only [hlen_a, hn, ↓reduceDIte] at hp
      have h2' : n < ((Finset.univ.val.map b).sort (· ≥ ·)).length := by rw [hlen_b]; exact hn
      simp only [h2', ↓reduceDIte] at hp
      exact hp
  have ha : ↑((Finset.univ.val.map a).sort (· ≥ ·)) = (Finset.univ.val.map a) :=
    Multiset.sort_eq _ _
  have hb : ↑((Finset.univ.val.map b).sort (· ≥ ·)) = (Finset.univ.val.map b) :=
    Multiset.sort_eq _ _
  rw [← ha, ← hb, h_sorted_eq]

/-- Coefficients are equal for exponents with the same sort (for symmetric polynomials).
    This follows from the fact that two tuples with the same sort differ by a permutation,
    and symmetric polynomials have permutation-invariant coefficients.

    The proof requires the combinatorial fact that equal sorted multisets implies
    the existence of a permutation relating the two tuples. -/
lemma coeff_eq_of_same_sort (f : MvPolynomial (Fin N) R) (hf : f.IsSymmetric)
    (d₁ d₂ : Fin N →₀ ℕ) (h : sortTupleFinsupp d₁ = sortTupleFinsupp d₂) :
    f.coeff d₁ = f.coeff d₂ := by
  -- Step 1: sortTupleFinsupp equality implies multiset equality
  unfold sortTupleFinsupp at h
  have h_multiset_eq := sortTuple_eq_implies_multiset_eq _ _ h
  -- Step 2: There exists a permutation σ such that d₂ i = d₁ (σ i)
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq _ _ h_multiset_eq
  -- Step 3: d₂ = Finsupp.mapDomain σ.symm d₁
  have h_d₂_eq : d₂ = Finsupp.mapDomain σ.symm d₁ := by
    ext i
    have h1 : d₂ i = d₁ (σ i) := hσ i
    have h2 : (Finsupp.mapDomain σ.symm d₁) i = d₁ (σ i) := by
      rw [Finsupp.mapDomain_equiv_apply]
      simp
    rw [h1, ← h2]
  -- Step 4: Apply coeff_perm_eq_of_symmetric
  rw [h_d₂_eq]
  exact (coeff_perm_eq_of_symmetric f hf d₁ σ.symm).symm

/-- The monomial symmetric polynomials span the symmetric polynomials.
    (Theorem thm.sf.m-basis (a), spanning part)

    The proof proceeds by:
    1. Writing f as a sum of monomials grouped by their sort
    2. For symmetric f, all monomials with the same sort have the same coefficient
    3. Factoring out the common coefficient from each group
    4. Showing that the sum of monomials in each group equals monomialSymm μ

    Label: thm.sf.m-basis.a.span -/
theorem monomialSymm_spans :
    ∀ f : MvPolynomial (Fin N) R, f.IsSymmetric →
    f ∈ Submodule.span R (Set.range (fun mu : NPartition N => monomialSymm mu)) := by
  intro f hf
  -- Write f as sum of monomials
  have hf_sum : f = ∑ d ∈ f.support, monomial d (f.coeff d) := f.as_sum
  rw [hf_sum]
  -- Partition by sortTupleFinsupp
  rw [sum_partition f.support sortTupleFinsupp (fun d => monomial d (f.coeff d))]
  -- Show each partition class is in the span
  apply Submodule.sum_mem
  intro μ hμ
  -- Get a representative element from this partition class
  simp only [mem_image] at hμ
  obtain ⟨d₀, hd₀_mem, hd₀_sort⟩ := hμ
  -- All elements in this class have the same coefficient as d₀
  have hcoeff_eq : ∀ d ∈ f.support.filter (fun d => sortTupleFinsupp d = μ),
      f.coeff d = f.coeff d₀ := by
    intro d hd
    simp only [mem_filter] at hd
    rw [← hd₀_sort] at hd
    exact coeff_eq_of_same_sort f hf d d₀ hd.2
  -- Factor out the common coefficient
  have h_factor : ∑ d ∈ f.support.filter (fun d => sortTupleFinsupp d = μ), monomial d (f.coeff d) =
      f.coeff d₀ • ∑ d ∈ f.support.filter (fun d => sortTupleFinsupp d = μ), monomial d 1 := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [hcoeff_eq d hd, smul_monomial, smul_eq_mul, mul_one]
  rw [h_factor]
  apply Submodule.smul_mem
  -- The sum ∑_{d : sort d = μ, d ∈ support f} monomial d 1 equals monomialSymm μ
  -- for symmetric f. This is because:
  -- 1. For symmetric f, support is closed under permutation
  -- 2. Two Finsupps have the same sort iff they are permutations of each other
  -- 3. So if any d with sort μ is in support, ALL d with sort μ are in support
  -- 4. Therefore the filter set equals sortPreimage μ (converted to Finsupp)
  --
  -- We show the sum equals monomialSymm μ, then use subset_span.
  -- monomialSymm μ = ∑ a ∈ sortPreimage μ, monomialExp a
  --                = ∑ a ∈ sortPreimage μ, monomial (equivFunOnFinite.symm a) 1
  -- We establish a bijection between the filter set and sortPreimage μ.
  
  -- Helper: sortTupleFinsupp of equivFunOnFinite.symm a equals sortTuple a
  have h_sort_equiv : ∀ a : Fin N → ℕ, 
      sortTupleFinsupp (Finsupp.equivFunOnFinite.symm a) = sortTuple a := fun a => by
    unfold sortTupleFinsupp
    simp only [Equiv.apply_symm_apply]
  
  -- Helper: sortTupleFinsupp d = μ implies d.sum = μ.size
  have h_sum_eq_size : ∀ d : Fin N →₀ ℕ, sortTupleFinsupp d = μ → 
      d.sum (fun _ n => n) = μ.size := fun d hd => by
    have h1 : (sortTupleFinsupp d).size = d.sum (fun _ n => n) := by
      unfold sortTupleFinsupp
      rw [sortTuple_size]
      simp only [Finsupp.sum]
      have h : ∀ i : Fin N, Finsupp.equivFunOnFinite d i = d i := fun i => rfl
      simp_rw [h]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hx
      exact hx
    rw [hd] at h1
    exact h1.symm
  
  -- Helper: entries of a Finsupp are bounded by their sum
  have h_entry_le_sum : ∀ (d : Fin N →₀ ℕ) (i : Fin N), d i ≤ d.sum (fun _ n => n) := 
    fun d i => by
      by_cases hi : i ∈ d.support
      · exact Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
      · simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hi
        simp [hi]
  
  -- Helper: d in filter implies equivFunOnFinite d ∈ sortPreimage μ
  have h_filter_to_preimage : ∀ d ∈ f.support.filter (fun d => sortTupleFinsupp d = μ),
      Finsupp.equivFunOnFinite d ∈ sortPreimage μ := fun d hd => by
    simp only [mem_filter] at hd
    simp only [sortPreimage, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    constructor
    · intro i
      have h1 : d i ≤ d.sum (fun _ n => n) := h_entry_le_sum d i
      have h2 : d.sum (fun _ n => n) = μ.size := h_sum_eq_size d hd.2
      calc Finsupp.equivFunOnFinite d i = d i := rfl
        _ ≤ d.sum (fun _ n => n) := h1
        _ = μ.size := h2
        _ < μ.size + 1 := Nat.lt_succ_self _
    · unfold sortTupleFinsupp at hd
      exact hd.2
  
  -- Helper: a ∈ sortPreimage μ implies equivFunOnFinite.symm a ∈ filter
  have h_preimage_to_filter : ∀ a ∈ sortPreimage μ,
      Finsupp.equivFunOnFinite.symm a ∈ f.support.filter (fun d => sortTupleFinsupp d = μ) := 
    fun a ha => by
      simp only [mem_filter]
      constructor
      · -- Show equivFunOnFinite.symm a ∈ f.support
        -- This follows from: coeff (equivFunOnFinite.symm a) f = coeff d₀ f ≠ 0
        rw [mem_support_iff]
        have h_sort_eq : sortTupleFinsupp (Finsupp.equivFunOnFinite.symm a) = 
                         sortTupleFinsupp d₀ := by
          rw [h_sort_equiv]
          simp only [sortPreimage, Finset.mem_filter] at ha
          rw [ha.2, hd₀_sort]
        have h_coeff_eq := coeff_eq_of_same_sort f hf 
          (Finsupp.equivFunOnFinite.symm a) d₀ h_sort_eq
        rw [h_coeff_eq]
        rw [mem_support_iff] at hd₀_mem
        exact hd₀_mem
      · -- Show sortTupleFinsupp (equivFunOnFinite.symm a) = μ
        rw [h_sort_equiv]
        simp only [sortPreimage, Finset.mem_filter] at ha
        exact ha.2
  
  -- Now show the sum equals monomialSymm μ using sum_bij'
  have h_sum_eq : ∑ d ∈ f.support.filter (fun d => sortTupleFinsupp d = μ), 
      (monomial d (1 : R) : MvPolynomial (Fin N) R) = monomialSymm μ := by
    simp only [monomialSymm]
    symm
    exact Finset.sum_bij' 
      (fun a _ => Finsupp.equivFunOnFinite.symm a)
      (fun d _ => Finsupp.equivFunOnFinite d)
      h_preimage_to_filter
      h_filter_to_preimage
      (fun a _ => by simp)
      (fun d _ => by simp)
      (fun a _ => by rw [monomialExp_eq_monomial])
  
  have hmem : (monomialSymm μ : MvPolynomial (Fin N) R) ∈ 
      Submodule.span R (Set.range (fun mu : NPartition N => monomialSymm mu)) := 
    Submodule.subset_span ⟨μ, rfl⟩
  convert hmem using 1


/-- Any symmetric polynomial f can be written as
    f = ∑_μ ([x₁^{μ₁} x₂^{μ₂} ⋯ x_N^{μ_N}] f) m_μ
    (Theorem thm.sf.m-basis (b))

    Label: thm.sf.m-basis.b -/
theorem symm_eq_sum_coeff_monomialSymm (f : MvPolynomial (Fin N) R) (hf : f.IsSymmetric)
    (S : Finset (NPartition N)) (hS : ∀ mu : NPartition N, mu.size ≤ f.totalDegree → mu ∈ S) :
    f = ∑ mu ∈ S, (f.coeff (Finsupp.equivFunOnFinite.symm mu.parts)) • monomialSymm mu := by
  -- Helper: sortTupleFinsupp_parts
  have sortTupleFinsupp_parts : ∀ mu : NPartition N,
      sortTupleFinsupp (Finsupp.equivFunOnFinite.symm mu.parts) = mu := fun mu => by
    unfold sortTupleFinsupp
    simp only [Equiv.apply_symm_apply]
    exact sortTuple_of_NPartition mu
  -- Helper: sortTupleFinsupp_size
  have sortTupleFinsupp_size : ∀ d : Fin N →₀ ℕ,
      (sortTupleFinsupp d).size = d.sum (fun _ n => n) := fun d => by
    unfold sortTupleFinsupp
    rw [sortTuple_size]
    simp only [Finsupp.sum]
    have h : ∀ i : Fin N, Finsupp.equivFunOnFinite d i = d i := fun i => rfl
    simp_rw [h]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hx
    exact hx
  -- Helper: monomialSymm_coeff for general d
  have monomialSymm_coeff : ∀ (d : Fin N →₀ ℕ) (mu : NPartition N),
      (monomialSymm mu : MvPolynomial (Fin N) R).coeff d =
      if sortTupleFinsupp d = mu then 1 else 0 := fun d mu => by
    split_ifs with h
    · have hsort : sortTupleFinsupp d = sortTupleFinsupp (Finsupp.equivFunOnFinite.symm mu.parts) := by
        rw [h, sortTupleFinsupp_parts]
      have hcoeff := coeff_eq_of_same_sort (monomialSymm (R := R) mu) (monomialSymm_isSymmetric mu) d
          (Finsupp.equivFunOnFinite.symm mu.parts) hsort
      rw [hcoeff]
      exact monomialSymm_coeff_self mu
    · let nu := sortTupleFinsupp d
      have hnu : sortTupleFinsupp d = nu := rfl
      have hsort : sortTupleFinsupp d = sortTupleFinsupp (Finsupp.equivFunOnFinite.symm nu.parts) := by
        rw [hnu, sortTupleFinsupp_parts]
      have hcoeff := coeff_eq_of_same_sort (monomialSymm (R := R) mu) (monomialSymm_isSymmetric mu) d
          (Finsupp.equivFunOnFinite.symm nu.parts) hsort
      rw [hcoeff]
      exact monomialSymm_coeff_ne nu mu (fun heq => h (hnu.trans heq))
  -- Main proof: show both sides have the same coefficient for each exponent d
  ext1 d
  rw [coeff_sum]
  simp only [coeff_smul, smul_eq_mul]
  simp_rw [monomialSymm_coeff d]
  simp only [mul_ite, mul_one, mul_zero]
  let mu := sortTupleFinsupp d
  by_cases hmu : mu ∈ S
  · -- Case: μ ∈ S - the sum has exactly one nonzero term
    rw [Finset.sum_eq_single_of_mem mu hmu]
    · -- The term for μ gives the coefficient of d in f
      simp only [mu, ↓reduceIte]
      have hsort : sortTupleFinsupp d = sortTupleFinsupp (Finsupp.equivFunOnFinite.symm (sortTupleFinsupp d).parts) := by
        rw [sortTupleFinsupp_parts]
      exact coeff_eq_of_same_sort f hf d (Finsupp.equivFunOnFinite.symm (sortTupleFinsupp d).parts) hsort
    · -- All other terms are zero
      intro nu _ hne
      simp only [ite_eq_right_iff]
      intro heq
      exact absurd heq (Ne.symm hne)
  · -- Case: μ ∉ S - the coefficient must be 0
    -- First show the sum is 0
    have hsum_zero : ∑ x ∈ S, (if sortTupleFinsupp d = x then f.coeff (Finsupp.equivFunOnFinite.symm x.parts) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro nu hnu
      simp only [ite_eq_right_iff]
      intro heq
      exfalso
      have : mu = nu := heq
      rw [this] at hmu
      exact hmu hnu
    rw [hsum_zero]
    -- Show coeff d f = 0 by contradiction
    by_contra hcoeff_ne
    have hd_mem : d ∈ f.support := by rwa [mem_support_iff]
    have hdeg : d.sum (fun _ n => n) ≤ f.totalDegree := le_totalDegree hd_mem
    have hmu_size : mu.size = d.sum (fun _ n => n) := sortTupleFinsupp_size d
    have : mu.size ≤ f.totalDegree := by omega
    exact hmu (hS mu this)

/-- The submodule of homogeneous symmetric polynomials of degree n.
    (Theorem thm.sf.m-basis (c))

    𝒮_n = {homogeneous symmetric polynomials of degree n}

    Label: thm.sf.m-basis.c -/
def symmHomogeneous (N : ℕ) (R : Type*) [CommSemiring R] (n : ℕ) :
    Submodule R (MvPolynomial (Fin N) R) where
  carrier := {f | f.IsSymmetric ∧ f.IsHomogeneous n}
  add_mem' := by
    intro a b ⟨ha_symm, ha_hom⟩ ⟨hb_symm, hb_hom⟩
    exact ⟨ha_symm.add hb_symm, ha_hom.add hb_hom⟩
  zero_mem' := ⟨IsSymmetric.zero, MvPolynomial.isHomogeneous_zero (Fin N) R n⟩
  smul_mem' := by
    intro c f ⟨hf_symm, hf_hom⟩
    constructor
    · exact hf_symm.smul c
    · rw [Algebra.smul_def]
      exact hf_hom.C_mul c

/-- The monomial x^a is homogeneous of degree ∑ᵢ aᵢ. -/
private lemma monomialExp_isHomogeneous (a : Fin N → ℕ) :
    (monomialExp a : MvPolynomial (Fin N) R).IsHomogeneous (∑ i, a i) := by
  simp only [monomialExp]
  apply MvPolynomial.IsHomogeneous.prod
  intro i _
  have h1 : (X i : MvPolynomial (Fin N) R).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X R i
  have h2 := h1.pow (a i)
  convert h2 using 1
  ring

/-- The monomial symmetric polynomial m_μ is homogeneous of degree |μ|. -/
lemma monomialSymm_isHomogeneous (mu : NPartition N) :
    (monomialSymm mu : MvPolynomial (Fin N) R).IsHomogeneous mu.size := by
  simp only [monomialSymm]
  apply MvPolynomial.IsHomogeneous.sum
  intro a ha
  simp only [sortPreimage, Finset.mem_filter] at ha
  have heq : (sortTuple a).size = ∑ i, a i := sortTuple_size a
  rw [ha.2] at heq
  rw [heq]
  exact monomialExp_isHomogeneous a

/-- The homogeneous component of m_μ of degree n is m_μ if |μ| = n, and 0 otherwise. -/
private lemma homogeneousComponent_monomialSymm (mu : NPartition N) (n : ℕ) :
    homogeneousComponent n (monomialSymm (R := R) mu) =
    if mu.size = n then monomialSymm mu else 0 := by
  rw [homogeneousComponent_of_mem (monomialSymm_isHomogeneous mu)]
  split_ifs with h1 h2 h2 <;> first | rfl | omega

/-- The monomial symmetric polynomials of size n span 𝒮_n.
    (Theorem thm.sf.m-basis (d), spanning part)

    Label: thm.sf.m-basis.d.span -/
theorem monomialSymm_homogeneous_spans (n : ℕ) :
    ∀ f ∈ symmHomogeneous N R n,
    f ∈ Submodule.span R (Set.range (fun mu : {nu : NPartition N // nu.size = n} =>
      monomialSymm mu.val)) := by
  intro f hf
  obtain ⟨hf_symm, hf_hom⟩ := hf
  -- f is symmetric, so it's in the span of all monomialSymm
  have h := monomialSymm_spans f hf_symm
  -- Since f is homogeneous of degree n, homogeneousComponent n f = f
  have hf_comp : homogeneousComponent n f = f := by
    rw [homogeneousComponent_of_mem hf_hom]
    simp
  -- Apply homogeneousComponent n to get f in span of (homogeneousComponent n '' S)
  let S := Set.range (fun mu : NPartition N => (monomialSymm mu : MvPolynomial (Fin N) R))
  have h2 : f ∈ Submodule.span R ((homogeneousComponent n) '' S) := by
    rw [← hf_comp]
    have := Submodule.mem_map_of_mem (f := homogeneousComponent n) h
    rw [Submodule.map_span] at this
    exact this
  -- Now show that the image is contained in the span of the restricted range
  let T := Set.range (fun mu : {nu : NPartition N // nu.size = n} =>
    (monomialSymm mu.val : MvPolynomial (Fin N) R))
  have h3 : (homogeneousComponent n) '' S ⊆ (Submodule.span R T : Set (MvPolynomial (Fin N) R)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨mu, rfl⟩ := hy
    rw [homogeneousComponent_monomialSymm]
    split_ifs with hmu
    · -- mu.size = n, so monomialSymm mu is in the span
      exact Submodule.subset_span (Set.mem_range.mpr ⟨⟨mu, hmu⟩, rfl⟩)
    · -- mu.size ≠ n, so result is 0, which is in any submodule
      exact Submodule.zero_mem _
  have h4 : Submodule.span R ((homogeneousComponent n) '' S) ≤ Submodule.span R T := by
    apply Submodule.span_le.mpr h3
  exact h4 h2

/-- The monomial symmetric polynomials of size n are linearly independent.
    (Theorem thm.sf.m-basis (d), linear independence part)

    This follows from the fact that no two m_μ share any monomials, and each m_μ
    contains at least one monomial.

    Label: thm.sf.m-basis.d.indep -/
theorem monomialSymm_homogeneous_linearIndependent (n : ℕ) :
    LinearIndependent R (fun mu : {nu : NPartition N // nu.size = n} =>
      (monomialSymm mu.val : MvPolynomial (Fin N) R)) := by
  -- Use linearIndependent_iff'ₛ which works for semirings
  rw [linearIndependent_iff'ₛ]
  intro s f g hfg i hi
  -- Extract the coefficient of i.parts from the sum
  have key :
      (∑ j ∈ s, f j • monomialSymm j.val : MvPolynomial (Fin N) R).coeff
        (Finsupp.equivFunOnFinite.symm i.val.parts) =
      (∑ j ∈ s, g j • monomialSymm j.val : MvPolynomial (Fin N) R).coeff
        (Finsupp.equivFunOnFinite.symm i.val.parts) := by
    rw [hfg]
  simp only [coeff_sum, coeff_smul] at key
  have hf : ∑ j ∈ s, f j • (monomialSymm j.val : MvPolynomial (Fin N) R).coeff
      (Finsupp.equivFunOnFinite.symm i.val.parts) = f i := by
    rw [Finset.sum_eq_single_of_mem i hi]
    · simp [monomialSymm_coeff_self]
    · intro j hj hne
      simp only [smul_eq_mul]
      have hne' : i.val ≠ j.val := fun heq => hne (Subtype.ext heq.symm)
      rw [monomialSymm_coeff_ne i.val j.val hne', mul_zero]
  have hg : ∑ j ∈ s, g j • (monomialSymm j.val : MvPolynomial (Fin N) R).coeff
      (Finsupp.equivFunOnFinite.symm i.val.parts) = g i := by
    rw [Finset.sum_eq_single_of_mem i hi]
    · simp [monomialSymm_coeff_self]
    · intro j hj hne
      simp only [smul_eq_mul]
      have hne' : i.val ≠ j.val := fun heq => hne (Subtype.ext heq.symm)
      rw [monomialSymm_coeff_ne i.val j.val hne', mul_zero]
  rw [hf, hg] at key
  exact key

/-- Linear independence in a submodule follows from linear independence of the 
    coerced elements in the ambient module. -/
private lemma linearIndependent_submodule_of_linearIndependent 
    {S : Submodule R (MvPolynomial (Fin N) R)} {ι : Type*} (v : ι → S) 
    (hli : LinearIndependent R (fun i => (v i : MvPolynomial (Fin N) R))) :
    LinearIndependent R v := by
  rw [linearIndependent_iff'ₛ] at hli ⊢
  intro s f g hfg i hi
  have h : ∑ j ∈ s, f j • (v j : MvPolynomial (Fin N) R) = 
           ∑ j ∈ s, g j • (v j : MvPolynomial (Fin N) R) := by
    have := congrArg (Submodule.subtype S) hfg
    simp only [map_sum, map_smul, Submodule.coe_subtype] at this
    exact this
  exact hli s f g h i hi

/-- If elements of a submodule span the submodule (when coerced to the ambient module),
    then they span the submodule as a module. -/
private lemma span_eq_top_of_subtype_span
    {S : Submodule R (MvPolynomial (Fin N) R)} {ι : Type*} (v : ι → S) 
    (hsp : ∀ x : S, (x : MvPolynomial (Fin N) R) ∈ 
           Submodule.span R (Set.range (fun i => (v i : MvPolynomial (Fin N) R)))) :
    ⊤ ≤ Submodule.span R (Set.range v) := by
  intro x _
  specialize hsp x
  have key : Submodule.map (Submodule.subtype S) (Submodule.span R (Set.range v)) = 
             Submodule.span R (Set.range (fun i => (v i : MvPolynomial (Fin N) R))) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, Submodule.coe_subtype]
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  rw [← key] at hsp
  rw [Submodule.mem_map] at hsp
  obtain ⟨y, hy, hxy⟩ := hsp
  have hyx : y = x := Subtype.ext hxy
  rw [← hyx]
  exact hy

/-- monomialSymm maps into symmHomogeneous when the size matches. -/
private lemma monomialSymm_mem_symmHomogeneous' (mu : NPartition N) (n : ℕ) (h : mu.size = n) :
    (monomialSymm mu : MvPolynomial (Fin N) R) ∈ symmHomogeneous N R n := by
  constructor
  · exact monomialSymm_isSymmetric mu
  · rw [← h]
    exact monomialSymm_isHomogeneous mu

/-- The function that maps N-partitions of size n into the submodule of homogeneous 
    symmetric polynomials of degree n. -/
private noncomputable def monomialSymmRestricted (n : ℕ) :
    {nu : NPartition N // nu.size = n} → symmHomogeneous N R n :=
  fun mu => ⟨monomialSymm mu.val, monomialSymm_mem_symmHomogeneous' mu.val n mu.property⟩

/-- The monomial symmetric polynomials of size n form a basis of 𝒮_n.
    (Theorem thm.sf.m-basis (d))

    This combines linear independence (`monomialSymm_homogeneous_linearIndependent`)
    and spanning (`monomialSymm_homogeneous_spans`).

    Label: thm.sf.m-basis.d -/
noncomputable def monomialSymm_basis_homogeneous (n : ℕ) :
    Module.Basis {nu : NPartition N // nu.size = n} R (symmHomogeneous N R n) := by
  let v := monomialSymmRestricted (R := R) (N := N) n
  -- v is linearly independent
  have hli : LinearIndependent R v := by
    apply linearIndependent_submodule_of_linearIndependent
    convert monomialSymm_homogeneous_linearIndependent n; rfl
  -- v spans symmHomogeneous
  have hsp : ⊤ ≤ Submodule.span R (Set.range v) := by
    apply span_eq_top_of_subtype_span
    intro x
    obtain ⟨hx_symm, hx_hom⟩ := x.property
    have h := monomialSymm_homogeneous_spans n x.val ⟨hx_symm, hx_hom⟩
    convert h; rfl
  exact Module.Basis.mk hli hsp


end SymmetricFunctions

end AlgebraicCombinatorics
