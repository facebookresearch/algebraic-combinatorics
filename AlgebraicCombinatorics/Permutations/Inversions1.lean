/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Contributors. All rights reserved.
SPDX-License-Identifier: Apache-2.0

Inversions, length and Lehmer codes for permutations.

This file formalizes Section 1.3 (subsections on inversions and Lehmer codes) from

## Main definitions

* `Perm.inv` - the set of inversions of a permutation
* `Perm.invCount` - the number of inversions (length/Coxeter length)
* `Perm.nonInv` - the set of non-inversions (pairs where order is preserved)
* `Perm.lehmerEntry` - the Lehmer entry ℓ_i(σ) at position i
* `Perm.lehmerCode` - the Lehmer code of a permutation (as a function `Fin n → ℕ`)
* `Perm.Iic0` - the notation [m]_0 = {0, 1, ..., m} for integers
* `Perm.Iic0Nat` - the notation [m]_0 = {0, 1, ..., m} for natural numbers
* `lehmerCodeSet` - the set H_n of valid Lehmer codes
* `Perm.longestElement` - the longest element w₀ (reversal permutation)

## Main results

* `Perm.inv_one` - the identity has no inversions
* `Perm.invCount_one` - the identity has length 0
* `Perm.invCount_inv` - length is preserved under taking inverses
* `Perm.invCount_mul_le` - the triangle inequality for inversions
* `Perm.invCount_le_choose` - the length is at most n choose 2
* `Perm.invCount_eq_zero_iff` - length 0 iff identity
* `Perm.inv_longestElement` - the longest element has all pairs as inversions
* `Perm.invCount_longestElement` - the longest element has length n choose 2
* `Perm.invCount_longestElement_mul` - invCount (w₀ * σ) = card(nonInv σ)
* `Perm.invCount_longestElement_mul'` - invCount (w₀ * σ) = n choose 2 - invCount σ
* `Perm.invCount_eq_choose_iff` - length n choose 2 iff longest element
* `Perm.invCount_eq_sum_lehmerCode` - length equals sum of Lehmer code entries
* `Perm.lehmerCode_bijective` - the Lehmer code map is a bijection
* `card_lehmerCodeSet` - |H_n| = n!

## Design note: Namespace and duplication

This file uses the `AlgebraicCombinatorics.Perm` namespace for definitions like `inv`, `invCount`,
and `lehmerCode`. The file `Inversions2.lean` defines equivalent versions in the `Equiv.Perm`
namespace (`inversions`, `length`, `lehmerCode`) with bridge lemmas proving definitional equality:

* `Equiv.Perm.inversions_eq_inv` : `inversions σ = Perm.inv σ` (by `rfl`)
* `Equiv.Perm.length_eq_invCount` : `length σ = Perm.invCount σ` (by `rfl`)

**Which definitions to use:**
- Use `AlgebraicCombinatorics.Perm.inv`/`invCount` when working with basic inversion properties,
  Lehmer codes, and the longest element (this file)
- Use `Equiv.Perm.inversions`/`length` when working with reduced words, simple transpositions,
  and Coxeter-style arguments (Inversions2.lean)

The definitions are definitionally equal, so theorems from either file can be used interchangeably.

**Lehmer code representations:**
- `AlgebraicCombinatorics.Perm.lehmerCode : Equiv.Perm (Fin n) → (Fin n → ℕ)` (function)
- `Equiv.Perm.lehmerCode : Perm (Fin n) → List ℕ` (list, via `lehmerCode_toList`)

Both represent the same mathematical object; use whichever is more convenient for your application.

## References

-/

import Mathlib

set_option maxHeartbeats 400000

namespace AlgebraicCombinatorics

open Finset BigOperators

/-! ### Inversions and length -/

namespace Perm

variable {n : ℕ}

/--
An inversion of a permutation σ ∈ S_n is a pair (i, j) of elements of [n]
such that i < j and σ(i) > σ(j).

See Definition 1.3.1 (def.perm.invs) in the source.
-/
def inv (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.filter (fun p => p.1 < p.2 ∧ σ p.1 > σ p.2) Finset.univ

/--
The length (or Coxeter length) of a permutation σ is the number of inversions of σ.
This is denoted ℓ(σ) in the source.

See Definition 1.3.1 (def.perm.invs) part (b) in the source.
-/
def invCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (inv σ).card

/--
For any σ ∈ S_n, we have ℓ(σ) ∈ {0, 1, ..., n choose 2}.

See Proposition 1.3.3 (prop.perm.lengths-k-small-k) part (a) in the source.
-/
theorem invCount_le_choose (σ : Equiv.Perm (Fin n)) : invCount σ ≤ n.choose 2 := by
  -- The set of inversions is a subset of all pairs (i, j) with i < j
  -- and the latter has cardinality n choose 2
  unfold invCount inv
  have hcard : (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ).card = n.choose 2 := by
    have h1 : (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ).card =
              ∑ i : Fin n, (Finset.filter (fun j : Fin n => i < j) Finset.univ).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro i _
        apply Finset.card_bij'
          (i := fun p _ => p.2)
          (j := fun j _ => (i, j))
          (hi := fun ⟨a, b⟩ hab => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
            have heq : a = i := hab.2
            have hlt : a < b := hab.1
            rw [← heq]; exact hlt)
          (hj := fun j hj => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            exact ⟨hj, trivial⟩)
          (left_inv := fun ⟨a, b⟩ hab => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
            simp only [Prod.mk.injEq]
            exact ⟨hab.2.symm, trivial⟩)
          (right_inv := fun j hj => by simp)
      · intro x _; simp
    have h2 : ∀ i : Fin n, (Finset.filter (fun j : Fin n => i < j) Finset.univ).card =
        (Finset.Ioi i).card := by
      intro i
      congr 1
      ext j
      simp [Finset.mem_Ioi]
    have h3 : ∀ i : Fin n, (Finset.Ioi i).card = n - 1 - i.val := Fin.card_Ioi
    calc (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ).card
        = ∑ i : Fin n, (Finset.filter (fun j : Fin n => i < j) Finset.univ).card := h1
        _ = ∑ i : Fin n, (Finset.Ioi i).card := by simp only [h2]
        _ = ∑ i : Fin n, (n - 1 - i.val) := by simp only [h3]
        _ = n.choose 2 := by
            rw [Nat.choose_two_right]
            rw [Finset.sum_fin_eq_sum_range]
            conv_lhs =>
              arg 2
              ext i
              rw [show (if h : i < n then n - 1 - i else 0) = n - 1 - i by split_ifs with h <;> omega]
            rw [Finset.sum_range_reflect (fun i => i) n]
            rw [Finset.sum_range_id]
  calc (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.1 > σ p.2) Finset.univ).card
      ≤ (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ).card := by
          apply card_le_card
          intro p hp
          simp only [mem_filter, mem_univ, true_and] at hp ⊢
          exact hp.1
      _ = n.choose 2 := hcard

set_option backward.isDefEq.respectTransparency false in
/--
The only permutation σ ∈ S_n with ℓ(σ) = 0 is the identity map.

See Proposition 1.3.3 (prop.perm.lengths-k-small-k) part (b) in the source.
-/
theorem invCount_eq_zero_iff (σ : Equiv.Perm (Fin n)) : invCount σ = 0 ↔ σ = 1 := by
  constructor
  · -- If invCount = 0, then σ = 1
    intro h
    rw [invCount, Finset.card_eq_zero] at h
    -- No inversions means σ is strictly monotone
    have hσ : StrictMono σ := by
      intro a b hab
      by_contra hle
      push Not at hle
      have hne : σ a ≠ σ b := σ.injective.ne (ne_of_lt hab)
      have hgt : σ a > σ b := lt_of_le_of_ne hle hne.symm
      have hmem : (a, b) ∈ inv σ := by
        simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hab, hgt⟩
      rw [h] at hmem
      simp at hmem
    -- A strictly monotone permutation on Fin n must be the identity
    ext i
    simp only [Equiv.Perm.one_apply]
    by_contra hne
    have hne' : i ≠ σ i := fun heq => hne (congrArg Fin.val heq.symm)
    have hlt : i < σ i := lt_of_le_of_ne (hσ.id_le i) hne'
    -- Sum argument: ∑ j = ∑ σ(j) but j ≤ σ(j) with strict inequality at i
    have hsum : ∑ j : Fin n, (σ j).val = ∑ j : Fin n, j.val := Equiv.sum_comp σ (·.val)
    have hsum_lt : ∑ j : Fin n, j.val < ∑ j : Fin n, (σ j).val :=
      Finset.sum_lt_sum (fun j _ => hσ.id_le j) ⟨i, Finset.mem_univ i, hlt⟩
    omega
  · -- If σ = 1, then invCount = 0
    intro h
    rw [h, invCount, inv]
    simp only [Equiv.Perm.one_apply, Finset.card_eq_zero, filter_eq_empty_iff]
    intro ⟨i, j⟩ _
    simp only [not_and, not_lt]
    intro hij
    exact le_of_lt hij

set_option backward.isDefEq.respectTransparency false in
/--
The identity permutation has no inversions.

The identity preserves order, so there cannot be a pair (i, j) with i < j and 1(i) > 1(j).
-/
@[simp]
theorem inv_one : inv (1 : Equiv.Perm (Fin n)) = ∅ := by
  simp only [inv, Equiv.Perm.one_apply, filter_eq_empty_iff]
  intro ⟨i, j⟩ _
  simp only [not_and, not_lt]
  exact le_of_lt

/--
The identity permutation has length 0.

This follows directly from `inv_one`: the identity has no inversions.
-/
@[simp]
theorem invCount_one : invCount (1 : Equiv.Perm (Fin n)) = 0 := by
  simp only [invCount, inv_one, card_empty]

/--
The inversion count is preserved under taking inverses.

For a permutation σ, the pair (i, j) with i < j is an inversion of σ iff σ(i) > σ(j).
For σ⁻¹, the pair (a, b) with a < b is an inversion iff σ⁻¹(a) > σ⁻¹(b).
The map (a, b) ↦ (σ⁻¹(b), σ⁻¹(a)) gives a bijection between inversions of σ⁻¹ and σ.
-/
theorem invCount_inv (σ : Equiv.Perm (Fin n)) : invCount σ⁻¹ = invCount σ := by
  unfold invCount
  apply Finset.card_bij'
    (i := fun p _ => (σ⁻¹ p.2, σ⁻¹ p.1))  -- map (a, b) ∈ inv σ⁻¹ to (σ⁻¹ b, σ⁻¹ a) ∈ inv σ
    (j := fun p _ => (σ p.2, σ p.1))  -- inverse map
  · -- (a, b) ∈ inv σ⁻¹ implies (σ⁻¹ b, σ⁻¹ a) ∈ inv σ
    intro ⟨a, b⟩ hab
    simp only [inv, mem_filter, mem_univ, true_and] at hab ⊢
    obtain ⟨hab_lt, hab_gt⟩ := hab
    refine ⟨hab_gt, ?_⟩
    simp
    exact hab_lt
  · -- (i, j) ∈ inv σ implies (σ j, σ i) ∈ inv σ⁻¹
    intro ⟨i, j⟩ hij
    simp only [inv, mem_filter, mem_univ, true_and] at hij ⊢
    obtain ⟨hij_lt, hij_gt⟩ := hij
    refine ⟨hij_gt, ?_⟩
    simp
    exact hij_lt
  · -- left inverse
    intro ⟨a, b⟩ _
    simp
  · -- right inverse
    intro ⟨i, j⟩ _
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The inversion count of a product is bounded by the sum of inversion counts.
    This is not an equality in general (the triangle inequality for inversions). -/
theorem invCount_mul_le (σ τ : Equiv.Perm (Fin n)) :
    invCount (σ * τ) ≤ invCount σ + invCount τ := by
  -- An inversion (i, j) of σ * τ means i < j and (σ * τ)(i) > (σ * τ)(j)
  -- We'll show inv(σ * τ) ⊆ inv(τ) ∪ τ⁻¹ '' inv(σ) (roughly speaking)
  unfold invCount inv
  -- For each pair (i, j) with i < j:
  -- Case 1: τ(i) < τ(j) and σ(τ(i)) > σ(τ(j)) - this is an inversion of σ at (τ(i), τ(j))
  -- Case 2: τ(i) > τ(j) - this is an inversion of τ at (i, j)
  -- So inversions of σ * τ come from either inversions of τ or inversions of σ
  have h : (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ (σ * τ) p.1 > (σ * τ) p.2) Finset.univ)
      ⊆ (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ τ p.1 > τ p.2) Finset.univ)
        ∪ (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.1 > σ p.2) Finset.univ).image
            (fun p => (τ⁻¹ p.1, τ⁻¹ p.2)) := by
    intro ⟨i, j⟩ hij
    simp only [mem_filter, mem_univ, true_and, Equiv.Perm.coe_mul, Function.comp_apply] at hij
    obtain ⟨hij_lt, hij_gt⟩ := hij
    rw [mem_union]
    by_cases hτ : τ i > τ j
    · -- Case: τ(i) > τ(j), so (i, j) is an inversion of τ
      left
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨hij_lt, hτ⟩
    · -- Case: τ(i) ≤ τ(j), so we need τ(i) < τ(j) and (τ(i), τ(j)) is an inversion of σ
      push Not at hτ
      have hτ_lt : τ i < τ j := by
        cases hτ.lt_or_eq with
        | inl h => exact h
        | inr h => exact absurd (τ.injective h) (ne_of_lt hij_lt)
      right
      simp only [mem_image, mem_filter, mem_univ, true_and, Prod.mk.injEq]
      use (τ i, τ j)
      constructor
      · exact ⟨hτ_lt, hij_gt⟩
      · simp
  calc (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ (σ * τ) p.1 > (σ * τ) p.2) Finset.univ).card
      ≤ ((Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ τ p.1 > τ p.2) Finset.univ)
          ∪ (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.1 > σ p.2) Finset.univ).image
              (fun p => (τ⁻¹ p.1, τ⁻¹ p.2))).card := card_le_card h
      _ ≤ (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ τ p.1 > τ p.2) Finset.univ).card
          + ((Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.1 > σ p.2) Finset.univ).image
              (fun p => (τ⁻¹ p.1, τ⁻¹ p.2))).card := card_union_le _ _
      _ ≤ (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ τ p.1 > τ p.2) Finset.univ).card
          + (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.1 > σ p.2) Finset.univ).card := by
          apply Nat.add_le_add_left
          exact card_image_le
      _ = (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.1 > σ p.2) Finset.univ).card
          + (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ τ p.1 > τ p.2) Finset.univ).card := by
          ring

/--
The number of permutations σ ∈ S_n with ℓ(σ) = 0 is 1.

See Proposition 1.3.3 (prop.perm.lengths-k-small-k) part (b) in the source.
-/
theorem card_invCount_eq_zero :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => invCount σ = 0)).card = 1 := by
  have h : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => invCount σ = 0)) = {1} := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact invCount_eq_zero_iff σ
  rw [h]
  exact card_singleton 1

/--
The longest element w₀ ∈ S_n is the permutation with OLN n(n-1)(n-2)...21,
i.e., the reversal permutation.

Note: This is equivalent to `Fin.revPerm` from Mathlib. See `longestElement_eq_revPerm`.
-/
def longestElement (n : ℕ) : Equiv.Perm (Fin n) :=
  ⟨fun i => ⟨n - 1 - i.val, by omega⟩,
   fun i => ⟨n - 1 - i.val, by omega⟩,
   fun i => by simp [Fin.ext_iff]; omega,
   fun i => by simp [Fin.ext_iff]; omega⟩

/--
The longest element is equal to `Fin.revPerm` from Mathlib.
-/
theorem longestElement_eq_revPerm : longestElement n = Fin.revPerm := by
  ext i
  simp only [longestElement, Equiv.coe_fn_mk, Fin.revPerm_apply, Fin.rev]
  omega

set_option backward.isDefEq.respectTransparency false in
/--
The set of inversions of the longest element w₀ is exactly the set of all pairs (i, j)
with i < j. That is, every pair is an inversion.
-/
theorem inv_longestElement :
    inv (longestElement n) = Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ := by
  simp only [inv, longestElement]
  ext p
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro ⟨h1, _⟩; exact h1
  · intro h1; refine ⟨h1, ?_⟩
    simp only [Equiv.coe_fn_mk, Fin.mk_lt_mk]; omega

/--
The longest element w₀ ∈ S_n has length n choose 2, the maximum possible length.

This is because every pair (i, j) with i < j is an inversion of w₀, since w₀ reverses
the order of elements.

See Proposition 1.3.3 (prop.perm.lengths-k-small-k) part (c) in the source.
-/
@[simp]
theorem invCount_longestElement : invCount (longestElement n) = n.choose 2 := by
  simp only [invCount, inv_longestElement]
  rw [Nat.choose_two_right]
  have h1 : (filter (fun p : Fin n × Fin n => p.1 < p.2) univ).card =
           ∑ i : Fin n, (Finset.filter (fun j : Fin n => i < j) univ).card := by
    rw [card_eq_sum_ones, sum_filter, ← Finset.univ_product_univ, sum_product]
    congr 1; ext i; rw [card_eq_sum_ones, sum_filter]
  have h2 : ∀ i : Fin n, (Finset.filter (fun j : Fin n => i < j) univ).card = n - 1 - i.val := by
    intro i
    have : (Finset.filter (fun j : Fin n => i < j) univ) = (Finset.Ioi i) := by
      ext j; simp only [mem_filter, mem_univ, true_and, mem_Ioi]
    rw [this, Fin.card_Ioi]
  rw [h1]; simp_rw [h2]
  have h3 : ∑ i : Fin n, (n - 1 - i.val) = ∑ i ∈ Finset.range n, (n - 1 - i) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i)]
  rw [h3]
  have h4 : ∑ i ∈ Finset.range n, (n - 1 - i) = ∑ i ∈ Finset.range n, i := by
    conv_lhs => rw [← Finset.sum_range_reflect (fun i => n - 1 - i)]
    apply Finset.sum_congr rfl
    intro i hi; simp only [Finset.mem_range] at hi; omega
  rw [h4, Finset.sum_range_id]

set_option backward.isDefEq.respectTransparency false in
/--
The only permutation σ ∈ S_n with ℓ(σ) = n choose 2 is w₀.

See Proposition 1.3.3 (prop.perm.lengths-k-small-k) part (c) in the source.
-/
theorem invCount_eq_choose_iff (σ : Equiv.Perm (Fin n)) :
    invCount σ = n.choose 2 ↔ σ = longestElement n := by
  -- Define allPairs locally
  let allPairs : Finset (Fin n × Fin n) := Finset.filter (fun p => p.1 < p.2) Finset.univ
  -- Prove card_allPairs: the number of pairs (i,j) with i < j is n choose 2
  have card_allPairs : allPairs.card = n.choose 2 := by
    simp only [allPairs]
    rw [Nat.choose_two_right]
    have h1 : (filter (fun p : Fin n × Fin n => p.1 < p.2) univ).card =
             ∑ i : Fin n, (Finset.filter (fun j : Fin n => i < j) univ).card := by
      rw [card_eq_sum_ones, sum_filter, ← Finset.univ_product_univ, sum_product]
      congr 1; ext i; rw [card_eq_sum_ones, sum_filter]
    have h2 : ∀ i : Fin n, (Finset.filter (fun j : Fin n => i < j) univ).card = n - 1 - i.val := by
      intro i
      have : (Finset.filter (fun j : Fin n => i < j) univ) = (Finset.Ioi i) := by
        ext j; simp only [mem_filter, mem_univ, true_and, mem_Ioi]
      rw [this, Fin.card_Ioi]
    rw [h1]; simp_rw [h2]
    have h3 : ∑ i : Fin n, (n - 1 - i.val) = ∑ i ∈ Finset.range n, (n - 1 - i) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i)]
    rw [h3]
    have h4 : ∑ i ∈ Finset.range n, (n - 1 - i) = ∑ i ∈ Finset.range n, i := by
      conv_lhs => rw [← Finset.sum_range_reflect (fun i => n - 1 - i)]
      apply Finset.sum_congr rfl
      intro i hi; simp only [Finset.mem_range] at hi; omega
    rw [h4, Finset.sum_range_id]
  -- Prove inv_longestElement: for w₀, every pair (i,j) with i < j is an inversion
  have inv_longestElement : inv (longestElement n) = allPairs := by
    simp only [inv, longestElement, allPairs]
    ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro ⟨h1, _⟩; exact h1
    · intro h1; refine ⟨h1, ?_⟩
      simp only [Equiv.coe_fn_mk, Fin.mk_lt_mk]; omega
  -- Prove invCount_longestElement
  have invCount_longestElement : invCount (longestElement n) = n.choose 2 := by
    simp only [invCount]; rw [inv_longestElement, card_allPairs]
  -- Prove inv_subset_allPairs: inversions are always pairs with i < j
  have inv_subset_allPairs : ∀ τ : Equiv.Perm (Fin n), inv τ ⊆ allPairs := by
    intro τ p hp
    simp only [inv, allPairs] at hp ⊢
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    exact hp.1
  -- Prove inv_eq_allPairs_of_invCount_eq: max inversions means every pair is an inversion
  have inv_eq_allPairs_of_invCount_eq : ∀ τ : Equiv.Perm (Fin n),
      invCount τ = n.choose 2 → inv τ = allPairs := by
    intro τ h
    apply Finset.eq_of_subset_of_card_le (inv_subset_allPairs τ)
    simp only [invCount] at h
    rw [card_allPairs, h]
  -- Prove sigma_antitone_of_inv_eq_allPairs: if every pair is an inversion, σ is antitone
  have sigma_antitone_of_inv_eq_allPairs : ∀ τ : Equiv.Perm (Fin n),
      inv τ = allPairs → ∀ i j : Fin n, i < j → τ i > τ j := by
    intro τ h i j hij
    have : (i, j) ∈ allPairs := by
      simp only [allPairs, mem_filter, mem_univ, true_and]; exact hij
    rw [← h] at this
    simp only [inv, mem_filter, mem_univ, true_and] at this
    exact this.2
  -- Prove eq_longestElement_of_antitone: a strictly antitone permutation must be w₀
  have eq_longestElement_of_antitone : ∀ τ : Equiv.Perm (Fin n),
      (∀ i j : Fin n, i < j → τ i > τ j) → τ = longestElement n := by
    intro τ h
    ext i
    -- Key idea: count elements greater than τ(i) in two ways
    -- Way 1: #{j | τ(j) > τ(i)} = #{j | j < i} = i (since τ is antitone)
    have h1 : (Finset.filter (fun j : Fin n => τ j > τ i) univ).card = i.val := by
      have heq : (Finset.filter (fun j : Fin n => τ j > τ i) univ) =
                 (Finset.filter (fun j : Fin n => j < i) univ) := by
        ext j
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · intro hsj
          by_contra hji; push Not at hji
          rcases hji.lt_or_eq with hlt | heq'
          · have := h i j hlt; omega
          · subst heq'; exact lt_irrefl (τ i) hsj
        · intro hji; exact h j i hji
      rw [heq]
      have : (Finset.filter (fun j : Fin n => j < i) univ) = Finset.Iio i := by
        ext j; simp only [mem_filter, mem_univ, true_and, mem_Iio]
      rw [this, Fin.card_Iio]
    -- Way 2: #{j | τ(j) > τ(i)} = #{k | k > τ(i)} = n - 1 - τ(i) (since τ is bijective)
    have h2 : (Finset.filter (fun j : Fin n => τ j > τ i) univ).card = n - 1 - (τ i).val := by
      have heq : (Finset.filter (fun j : Fin n => τ j > τ i) univ) =
                 (Finset.filter (fun k : Fin n => k > τ i) univ).map τ.symm.toEmbedding := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply]
        constructor
        · intro hsj; use τ j; simp only [hsj, Equiv.symm_apply_apply, and_self]
        · intro ⟨k, hk, hkj⟩
          simp only [Equiv.symm_apply_eq] at hkj; rw [← hkj]; exact hk
      rw [heq, card_map]
      have : (Finset.filter (fun k : Fin n => k > τ i) univ) = Finset.Ioi (τ i) := by
        ext k; simp only [mem_filter, mem_univ, true_and, mem_Ioi]
      rw [this, Fin.card_Ioi]
    -- Combining: i = n - 1 - τ(i), so τ(i) = n - 1 - i
    rw [h1] at h2
    simp only [longestElement, Equiv.coe_fn_mk]; omega
  -- Main proof: combine the above
  constructor
  · intro h
    have h1 := inv_eq_allPairs_of_invCount_eq σ h
    have h2 := sigma_antitone_of_inv_eq_allPairs σ h1
    exact eq_longestElement_of_antitone σ h2
  · intro h
    rw [h]
    exact invCount_longestElement

/--
The number of permutations σ ∈ S_n with ℓ(σ) = n choose 2 is 1.

See Proposition 1.3.3 (prop.perm.lengths-k-small-k) part (c) in the source.
-/
theorem card_invCount_eq_choose :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => invCount σ = n.choose 2)).card = 1 := by
  have h : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => invCount σ = n.choose 2)) = {longestElement n} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact invCount_eq_choose_iff σ
  rw [h]
  exact Finset.card_singleton _

/-- inv (swap (castSucc i) (succ i)) = {(castSucc i, succ i)} for adjacent transpositions -/
private lemma inv_swap_adjacent {m : ℕ} (i : Fin m) :
    inv (Equiv.swap (Fin.castSucc i) (Fin.succ i)) = {(Fin.castSucc i, Fin.succ i)} := by
  ext ⟨a, b⟩
  simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · intro ⟨hab, hgt⟩
    by_cases ha : a = Fin.castSucc i
    · subst ha
      by_cases hb : b = Fin.succ i
      · exact ⟨rfl, hb⟩
      · by_cases hb' : b = Fin.castSucc i
        · exact absurd hab (hb' ▸ lt_irrefl _)
        · simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hb' hb] at hgt
          simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at hab hgt; omega
    · by_cases ha' : a = Fin.succ i
      · subst ha'
        simp only [Equiv.swap_apply_right] at hgt
        by_cases hb : b = Fin.castSucc i
        · simp only [hb, Equiv.swap_apply_left, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at hgt hab; omega
        · by_cases hb' : b = Fin.succ i
          · simp only [hb', Fin.lt_def, Fin.val_succ] at hab; omega
          · simp only [Equiv.swap_apply_of_ne_of_ne hb hb', Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at hab hgt; omega
      · simp only [Equiv.swap_apply_of_ne_of_ne ha ha'] at hgt
        by_cases hb : b = Fin.castSucc i
        · simp only [hb, Equiv.swap_apply_left, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at hab hgt; omega
        · by_cases hb' : b = Fin.succ i
          · simp only [hb', Equiv.swap_apply_right, Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at hab hgt; omega
          · simp only [Equiv.swap_apply_of_ne_of_ne hb hb', Fin.lt_def] at hab hgt; omega
  · intro ⟨ha, hb⟩; subst ha hb
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Fin.lt_def, Fin.val_succ, Fin.val_castSucc, and_self]; omega

private lemma invCount_swap_adjacent {m : ℕ} (i : Fin m) :
    invCount (Equiv.swap (Fin.castSucc i) (Fin.succ i)) = 1 := by
  simp only [invCount, inv_swap_adjacent, Finset.card_singleton]

/-- If invCount σ = 1 with unique inversion (a, b), then b.val = a.val + 1 (adjacent) -/
private lemma unique_inv_adjacent {m : ℕ} (σ : Equiv.Perm (Fin m)) (a b : Fin m)
    (hab : inv σ = {(a, b)}) : b.val = a.val + 1 := by
  have hinv : (a, b) ∈ inv σ := by rw [hab]; exact Finset.mem_singleton_self _
  simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and] at hinv
  obtain ⟨hab_lt, hab_gt⟩ := hinv
  by_contra hne
  have hgap : b.val > a.val + 1 := by omega
  have ⟨c, hac, hcb⟩ : ∃ c : Fin m, a < c ∧ c < b := by
    use ⟨a.val + 1, by omega⟩; simp only [Fin.lt_def]; omega
  rcases lt_trichotomy (σ c) (σ b) with hlt | heq | hgt
  · have hinv' : (a, c) ∈ inv σ := by
      simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hac, lt_trans hlt hab_gt⟩
    rw [hab] at hinv'; simp only [Finset.mem_singleton, Prod.mk.injEq] at hinv'
    exact (Fin.ne_of_lt hcb) hinv'.2
  · exact (Fin.ne_of_lt hcb) (σ.injective heq)
  · rcases lt_trichotomy (σ c) (σ a) with hlt' | heq' | hgt'
    · have hinv' : (a, c) ∈ inv σ := by
        simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hac, hlt'⟩
      rw [hab] at hinv'; simp only [Finset.mem_singleton, Prod.mk.injEq] at hinv'
      exact (Fin.ne_of_lt hcb) hinv'.2
    · exact (Fin.ne_of_lt hac) (σ.injective heq').symm
    · have hinv' : (c, b) ∈ inv σ := by
        simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hcb, hgt⟩
      rw [hab] at hinv'; simp only [Finset.mem_singleton, Prod.mk.injEq] at hinv'
      exact (Fin.ne_of_lt hac) hinv'.1.symm

set_option backward.isDefEq.respectTransparency false in
/-- If inv σ = {(a, b)} with adjacent a, b, then σ = swap a b -/
private lemma eq_swap_of_unique_adjacent_inv {m : ℕ} (σ : Equiv.Perm (Fin m)) (a b : Fin m)
    (hab : inv σ = {(a, b)}) (hadj : b.val = a.val + 1) : σ = Equiv.swap a b := by
  have hinv : (a, b) ∈ inv σ := by rw [hab]; exact Finset.mem_singleton_self _
  simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and] at hinv
  obtain ⟨hab_lt, hab_gt⟩ := hinv
  have hno_other_inv : ∀ x y : Fin m, x < y → (x, y) ≠ (a, b) → σ x < σ y := by
    intro x y hxy hne
    by_contra h; push Not at h
    have hne' : σ x ≠ σ y := σ.injective.ne (Fin.ne_of_lt hxy)
    have hgt : σ x > σ y := lt_of_le_of_ne h hne'.symm
    have hmem : (x, y) ∈ inv σ := by simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hxy, hgt⟩
    rw [hab] at hmem; simp only [Finset.mem_singleton] at hmem; exact hne hmem
  have hprod_inv_empty : ∀ p, p ∉ inv (σ * Equiv.swap a b) := by
    intro ⟨x, y⟩ hmem
    simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.coe_mul, Function.comp_apply] at hmem
    obtain ⟨hxy, hgt⟩ := hmem
    have hle : σ (Equiv.swap a b x) ≤ σ (Equiv.swap a b y) := by
      by_cases hxa : x = a
      · rw [hxa]
        by_cases hyb : y = b
        · rw [hyb]; simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]; exact le_of_lt hab_gt
        · by_cases hya : y = a
          · rw [hya] at hxy; rw [hxa] at hxy; exact absurd hxy (lt_irrefl a)
          · simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hya hyb]
            have hay_ne : (a, y) ≠ (a, b) := fun heq => hyb (Prod.mk.inj heq).2
            exact le_of_lt (lt_trans hab_gt (hno_other_inv a y (hxa ▸ hxy) hay_ne))
      · by_cases hxb : x = b
        · rw [hxb]; simp only [Equiv.swap_apply_right]
          by_cases hya : y = a
          · rw [hya, hxb] at hxy; simp only [Fin.lt_def] at hxy; omega
          · by_cases hyb : y = b
            · rw [hyb, hxb] at hxy; exact absurd hxy (lt_irrefl b)
            · simp only [Equiv.swap_apply_of_ne_of_ne hya hyb]
              have hby_ne : (b, y) ≠ (a, b) := fun heq => (Fin.ne_of_lt hab_lt) (Prod.mk.inj heq).1.symm
              have hσb_lt_σy := hno_other_inv b y (hxb ▸ hxy) hby_ne
              have ha_lt_y : a < y := lt_trans hab_lt (hxb ▸ hxy)
              by_cases hσa_le_σy : σ a ≤ σ y
              · exact hσa_le_σy
              · push Not at hσa_le_σy
                have hay_ne : (a, y) ≠ (a, b) := fun heq => hyb (Prod.mk.inj heq).2
                have hσa_lt_σy := hno_other_inv a y ha_lt_y hay_ne
                exact le_of_lt hσa_lt_σy
        · simp only [Equiv.swap_apply_of_ne_of_ne hxa hxb]
          by_cases hya : y = a
          · rw [hya]; simp only [Equiv.swap_apply_left]
            have hxa_ne : (x, a) ≠ (a, b) := fun heq => hxa (Prod.mk.inj heq).1
            have hσx_lt_σa := hno_other_inv x a (hya ▸ hxy) hxa_ne
            have hx_lt_b : x < b := lt_trans (hya ▸ hxy) hab_lt
            by_cases hσx_le_σb : σ x ≤ σ b
            · exact hσx_le_σb
            · push Not at hσx_le_σb
              have hxb_ne : (x, b) ≠ (a, b) := fun heq => hxa (Prod.mk.inj heq).1
              have hσx_lt_σb := hno_other_inv x b hx_lt_b hxb_ne
              exact le_of_lt hσx_lt_σb
          · by_cases hyb : y = b
            · rw [hyb]; simp only [Equiv.swap_apply_right]
              rcases lt_trichotomy x a with hx_lt_a | hx_eq_a | hx_gt_a
              · have hxa_ne : (x, a) ≠ (a, b) := fun heq => hxa (Prod.mk.inj heq).1
                have hσx_lt_σa := hno_other_inv x a hx_lt_a hxa_ne
                exact le_of_lt hσx_lt_σa
              · exact absurd hx_eq_a hxa
              · have hxv : x.val > a.val := hx_gt_a
                have hyv : x.val < b.val := hyb ▸ hxy
                omega
            · simp only [Equiv.swap_apply_of_ne_of_ne hya hyb]
              have hxy_ne : (x, y) ≠ (a, b) := fun heq => hxa (Prod.mk.inj heq).1
              exact le_of_lt (hno_other_inv x y hxy hxy_ne)
    exact (not_lt.mpr hle) hgt
  have hprod_inv : inv (σ * Equiv.swap a b) = ∅ := by
    rw [← Finset.card_eq_zero]
    by_contra hne; push Not at hne
    have ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    exact hprod_inv_empty p hp
  have hprod_id : σ * Equiv.swap a b = 1 := by
    rw [← invCount_eq_zero_iff]; simp only [invCount, hprod_inv, Finset.card_empty]
  calc σ = σ * 1 := by rw [mul_one]
    _ = σ * (Equiv.swap a b * Equiv.swap a b) := by rw [Equiv.swap_mul_self]
    _ = (σ * Equiv.swap a b) * Equiv.swap a b := by rw [mul_assoc]
    _ = 1 * Equiv.swap a b := by rw [hprod_id]
    _ = Equiv.swap a b := by rw [one_mul]

/--
If n ≥ 1, then the number of permutations σ ∈ S_n with ℓ(σ) = 1 is n - 1.
These are precisely the simple transpositions s_i.

See Proposition 1.3.3 (prop.perm.lengths-k-small-k) part (d) in the source.
-/
theorem card_invCount_eq_one (hn : 1 ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => invCount σ = 1)).card = n - 1 := by
  cases' n with m
  · omega
  · simp only [Nat.add_sub_cancel]
    let adjTrans : Finset (Equiv.Perm (Fin (m + 1))) :=
      (Finset.univ : Finset (Fin m)).image (fun i => Equiv.swap (Fin.castSucc i) (Fin.succ i))
    have h_sub : adjTrans ⊆ Finset.univ.filter (fun σ => invCount σ = 1) := by
      intro σ hσ
      simp only [adjTrans, Finset.mem_image, Finset.mem_univ, true_and] at hσ
      obtain ⟨i, hi⟩ := hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hi]; exact invCount_swap_adjacent i
    have h_sup : Finset.univ.filter (fun σ => invCount σ = 1) ⊆ adjTrans := by
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      simp only [adjTrans, Finset.mem_image, Finset.mem_univ, true_and]
      rw [invCount, Finset.card_eq_one] at hσ
      obtain ⟨⟨a, b⟩, hab⟩ := hσ
      have hinv : (a, b) ∈ inv σ := by rw [hab]; exact Finset.mem_singleton_self _
      simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and] at hinv
      obtain ⟨hab_lt, _⟩ := hinv
      have hadj := unique_inv_adjacent σ a b hab
      have ha_lt : a.val < m := by omega
      use ⟨a.val, ha_lt⟩
      have ha_eq : a = Fin.castSucc ⟨a.val, ha_lt⟩ := by ext; simp
      have hb_eq : b = Fin.succ ⟨a.val, ha_lt⟩ := by ext; simp [hadj]
      rw [ha_eq, hb_eq] at hab
      exact (eq_swap_of_unique_adjacent_inv σ _ _ hab (by simp)).symm
    have h_eq : Finset.univ.filter (fun σ => invCount σ = 1) = adjTrans := Finset.Subset.antisymm h_sup h_sub
    rw [h_eq]
    simp only [adjTrans]
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j hij; simp only at hij
      by_contra hne
      rcases lt_trichotomy i j with hlt | heq | hgt
      · have h1 : Equiv.swap (Fin.castSucc i) (Fin.succ i) (Fin.castSucc i) = Fin.succ i := by simp
        have h2 : Equiv.swap (Fin.castSucc j) (Fin.succ j) (Fin.castSucc i) = Fin.castSucc i := by
          apply Equiv.swap_apply_of_ne_of_ne
          · intro heq; exact hne (Fin.castSucc_injective _ heq)
          · intro heq; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at heq; omega
        have h3 : Equiv.swap (Fin.castSucc i) (Fin.succ i) (Fin.castSucc i) =
                  Equiv.swap (Fin.castSucc j) (Fin.succ j) (Fin.castSucc i) := by rw [hij]
        rw [h1, h2] at h3; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at h3; omega
      · exact hne heq
      · have h1 : Equiv.swap (Fin.castSucc j) (Fin.succ j) (Fin.castSucc j) = Fin.succ j := by simp
        have h2 : Equiv.swap (Fin.castSucc i) (Fin.succ i) (Fin.castSucc j) = Fin.castSucc j := by
          apply Equiv.swap_apply_of_ne_of_ne
          · intro heq; exact hne (Fin.castSucc_injective _ heq).symm
          · intro heq; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at heq; omega
        have h3 : Equiv.swap (Fin.castSucc j) (Fin.succ j) (Fin.castSucc j) =
                  Equiv.swap (Fin.castSucc i) (Fin.succ i) (Fin.castSucc j) := by rw [← hij]
        rw [h1, h2] at h3; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at h3; omega

/--
If n ≥ 2, then the number of permutations σ ∈ S_n with ℓ(σ) = 2 is (n-2)(n+1)/2.
These are precisely the products s_i s_j with 1 ≤ i < j < n, as well as
the products s_i s_{i-1} with i ∈ {2, 3, ..., n-1}.

See Proposition 1.3.3 (prop.perm.lengths-k-small-k) part (e) in the source.

**Proof Strategy:**

The permutations with exactly 2 inversions fall into three disjoint types:

1. **Type A (commuting transpositions):** s_i * s_j where j ≥ i + 2.
   Since |i - j| ≥ 2, these transpositions commute (s_i s_j = s_j s_i).
   Each contributes exactly one inversion, so the product has 2 inversions.
   Count: C(n-1, 2) - (n-2) = (n-3)(n-2)/2 (pairs minus adjacent pairs)

2. **Type B (3-cycles, forward):** s_i * s_{i+1} for i ∈ {0, ..., n-3}.
   This is the 3-cycle (i, i+1, i+2) in cycle notation.
   It has exactly 2 inversions: (i, i+2) and (i+1, i+2) in the permutation.
   Count: n-2

3. **Type C (3-cycles, backward):** s_{i+1} * s_i for i ∈ {0, ..., n-3}.
   This is the 3-cycle (i, i+2, i+1) in cycle notation.
   It has exactly 2 inversions: (i, i+1) and (i, i+2) in the permutation.
   Count: n-2

Total = (n-3)(n-2)/2 + (n-2) + (n-2) = (n-2)((n-3)/2 + 2) = (n-2)(n+1)/2

The proof requires:
- Showing each type has exactly 2 inversions
- Showing the three types are disjoint
- Showing every length-2 permutation is one of these types
- Computing the cardinality of each type

For small n:
- n = 2: (2-2)(2+1)/2 = 0. No length-2 permutations. ✓
- n = 3: (3-2)(3+1)/2 = 2. Type A: 0, Type B: 1, Type C: 1. ✓
- n = 4: (4-2)(4+1)/2 = 5. Type A: 1, Type B: 2, Type C: 2. ✓
-/

-- Helper lemma: s_i * s_j applied to castSucc i gives succ i (when i < j)
private lemma typeA_eval_at_first {m : ℕ} (i j : Fin (m + 1)) (hij : i < j) :
    (Equiv.swap (Fin.castSucc i) (Fin.succ i) *
     Equiv.swap (Fin.castSucc j) (Fin.succ j)) (Fin.castSucc i) = Fin.succ i := by
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  have hne1 : Fin.castSucc i ≠ Fin.castSucc j := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
  have hne2 : Fin.castSucc i ≠ Fin.succ j := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
  rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, Equiv.swap_apply_left]

-- Helper lemma: s_i * s_j applied to castSucc j gives succ j (when i < j)
private lemma typeA_eval_at_second {m : ℕ} (i j : Fin (m + 1)) (hij : i < j) :
    (Equiv.swap (Fin.castSucc i) (Fin.succ i) *
     Equiv.swap (Fin.castSucc j) (Fin.succ j)) (Fin.castSucc j) = Fin.succ j := by
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
  have hne1 : Fin.succ j ≠ Fin.castSucc i := by simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]; omega
  have hne2 : Fin.succ j ≠ Fin.succ i := by simp only [ne_eq, Fin.ext_iff, Fin.val_succ]; omega
  rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]

-- Helper lemma: inversions of Type A non-adjacent permutation (j > i + 1)
private lemma inv_typeA_nonadj {m : ℕ} (i j : Fin (m + 1)) (hgap : j.val > i.val + 1) :
    inv (Equiv.swap (Fin.castSucc i) (Fin.succ i) * Equiv.swap (Fin.castSucc j) (Fin.succ j)) =
    {(Fin.castSucc i, Fin.succ i), (Fin.castSucc j, Fin.succ j)} := by
  set τ := Equiv.swap (Fin.castSucc i) (Fin.succ i) * Equiv.swap (Fin.castSucc j) (Fin.succ j) with hτ_def
  have h_ci_ne_cj : Fin.castSucc i ≠ Fin.castSucc j := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
  have h_ci_ne_sj : Fin.castSucc i ≠ Fin.succ j := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
  have h_si_ne_cj : Fin.succ i ≠ Fin.castSucc j := by simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]; omega
  have h_si_ne_sj : Fin.succ i ≠ Fin.succ j := by simp only [ne_eq, Fin.ext_iff, Fin.val_succ]; omega
  have hτ_ci : τ (Fin.castSucc i) = Fin.succ i := by
    simp only [hτ_def, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne h_ci_ne_cj h_ci_ne_sj, Equiv.swap_apply_left]
  have hτ_si : τ (Fin.succ i) = Fin.castSucc i := by
    simp only [hτ_def, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne h_si_ne_cj h_si_ne_sj, Equiv.swap_apply_right]
  have hτ_cj : τ (Fin.castSucc j) = Fin.succ j := by
    simp only [hτ_def, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_sj.symm h_si_ne_sj.symm
  have hτ_sj : τ (Fin.succ j) = Fin.castSucc j := by
    simp only [hτ_def, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_right]
    exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_cj.symm h_si_ne_cj.symm
  have hτ_other : ∀ x, x ≠ Fin.castSucc i → x ≠ Fin.succ i → x ≠ Fin.castSucc j → x ≠ Fin.succ j → τ x = x := by
    intro x hx1 hx2 hx3 hx4
    simp only [hτ_def, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hx3 hx4, Equiv.swap_apply_of_ne_of_ne hx1 hx2]
  ext ⟨x, y⟩
  simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  have hci : (Fin.castSucc i).val = i.val := Fin.val_castSucc i
  have hsi : (Fin.succ i).val = i.val + 1 := Fin.val_succ i
  have hcj : (Fin.castSucc j).val = j.val := Fin.val_castSucc j
  have hsj : (Fin.succ j).val = j.val + 1 := Fin.val_succ j
  constructor
  · intro ⟨hxy, hgt⟩
    by_cases hx_ci : x = Fin.castSucc i
    · subst hx_ci
      by_cases hy_si : y = Fin.succ i
      · left; exact ⟨rfl, hy_si⟩
      · exfalso
        by_cases hy_cj : y = Fin.castSucc j
        · simp only [hτ_ci, hy_cj, hτ_cj, Fin.lt_def, hsi, hsj] at hgt; omega
        · by_cases hy_sj : y = Fin.succ j
          · simp only [hτ_ci, hy_sj, hτ_sj, Fin.lt_def, hsi, hcj] at hgt; omega
          · have hy_ne_ci : y ≠ Fin.castSucc i := by intro h; simp only [h, Fin.lt_def] at hxy; omega
            have hτy : τ y = y := hτ_other y hy_ne_ci hy_si hy_cj hy_sj
            simp only [hτ_ci, hτy, Fin.lt_def, hsi] at hgt hxy; omega
    · by_cases hx_si : x = Fin.succ i
      · exfalso; subst hx_si
        simp only [hτ_si, Fin.lt_def, hci] at hgt
        by_cases hy_ci : y = Fin.castSucc i
        · simp only [hy_ci, Fin.lt_def, hsi, hci] at hxy; omega
        · by_cases hy_si : y = Fin.succ i
          · simp only [hy_si, Fin.lt_def, hsi] at hxy; omega
          · by_cases hy_cj : y = Fin.castSucc j
            · simp only [hy_cj, hτ_cj, hsj] at hgt; omega
            · by_cases hy_sj : y = Fin.succ j
              · simp only [hy_sj, hτ_sj, hcj] at hgt; omega
              · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                simp only [hτy, Fin.lt_def] at hgt hxy; omega
      · by_cases hx_cj : x = Fin.castSucc j
        · subst hx_cj
          by_cases hy_sj : y = Fin.succ j
          · right; exact ⟨rfl, hy_sj⟩
          · exfalso
            by_cases hy_ci : y = Fin.castSucc i
            · simp only [hy_ci, Fin.lt_def, hci, hcj] at hxy; omega
            · by_cases hy_si : y = Fin.succ i
              · simp only [hy_si, Fin.lt_def, hsi, hcj] at hxy; omega
              · by_cases hy_cj : y = Fin.castSucc j
                · simp only [hy_cj, Fin.lt_def, hcj] at hxy; omega
                · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                  simp only [hτ_cj, hτy, Fin.lt_def, hsj] at hgt hxy; omega
        · exfalso
          by_cases hx_sj : x = Fin.succ j
          · subst hx_sj
            simp only [hτ_sj, Fin.lt_def, hcj] at hgt
            by_cases hy_ci : y = Fin.castSucc i
            · simp only [hy_ci, Fin.lt_def, hci, hsj] at hxy; omega
            · by_cases hy_si : y = Fin.succ i
              · simp only [hy_si, Fin.lt_def, hsi, hsj] at hxy; omega
              · by_cases hy_cj : y = Fin.castSucc j
                · simp only [hy_cj, Fin.lt_def, hcj, hsj] at hxy; omega
                · by_cases hy_sj : y = Fin.succ j
                  · simp only [hy_sj, Fin.lt_def, hsj] at hxy; omega
                  · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                    simp only [hτy, Fin.lt_def] at hgt hxy; omega
          · have hτx : τ x = x := hτ_other x hx_ci hx_si hx_cj hx_sj
            by_cases hy_ci : y = Fin.castSucc i
            · simp only [hy_ci, hτx, hτ_ci, Fin.lt_def, hsi] at hgt hxy; omega
            · by_cases hy_si : y = Fin.succ i
              · simp only [hy_si, hτx, hτ_si, Fin.lt_def, hci] at hgt hxy; omega
              · by_cases hy_cj : y = Fin.castSucc j
                · simp only [hy_cj, hτx, hτ_cj, Fin.lt_def, hsj] at hgt hxy; omega
                · by_cases hy_sj : y = Fin.succ j
                  · simp only [hy_sj, hτx, hτ_sj, Fin.lt_def, hcj] at hgt hxy; omega
                  · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                    simp only [hτx, hτy, Fin.lt_def] at hgt hxy; omega
  · intro h
    have h_ci_si : (Fin.castSucc i).val < (Fin.succ i).val := by simp
    have h_cj_sj : (Fin.castSucc j).val < (Fin.succ j).val := by simp
    rcases h with ⟨hx_eq, hy_eq⟩ | ⟨hx_eq, hy_eq⟩
    · subst hx_eq hy_eq
      constructor
      · exact Fin.mk_lt_mk.mpr h_ci_si
      · simp only [hτ_ci, hτ_si, Fin.lt_def, hsi, hci]; omega
    · subst hx_eq hy_eq
      constructor
      · exact Fin.mk_lt_mk.mpr h_cj_sj
      · simp only [hτ_cj, hτ_sj, Fin.lt_def, hsj, hcj]; omega

-- Helper lemma: injectivity of the typeA map
private lemma typeA_injOn (m : ℕ) :
    let pairsLt := Finset.filter (fun p : Fin (m + 1) × Fin (m + 1) => p.1 < p.2) Finset.univ
    Set.InjOn (fun (p : Fin (m + 1) × Fin (m + 1)) =>
      Equiv.swap (Fin.castSucc p.1) (Fin.succ p.1) *
      Equiv.swap (Fin.castSucc p.2) (Fin.succ p.2)) pairsLt := by
  intro pairsLt ⟨i, j⟩ hij ⟨i', j'⟩ hi'j' heq
  simp only [pairsLt, Finset.coe_filter, Set.mem_ofPred_eq] at hij hi'j'
  have hij' : i < j := hij.2; have hi'j'' : i' < j' := hi'j'.2
  simp only [Prod.mk.injEq]
  have hi_eq : i = i' := by
    by_contra hne; have heq' := congrFun (congrArg DFunLike.coe heq) (Fin.castSucc i)
    rw [typeA_eval_at_first i j hij'] at heq'
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hne1 : Fin.castSucc i ≠ Fin.castSucc i' := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
      have hne2 : Fin.castSucc i ≠ Fin.succ i' := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
      have hne3 : Fin.castSucc i ≠ Fin.castSucc j' := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
      have hne4 : Fin.castSucc i ≠ Fin.succ j' := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne3 hne4, Equiv.swap_apply_of_ne_of_ne hne1 hne2] at heq'
      simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at heq'; omega
    · have heq'' := congrFun (congrArg DFunLike.coe heq.symm) (Fin.castSucc i')
      rw [typeA_eval_at_first i' j' hi'j''] at heq''
      have hne1 : Fin.castSucc i' ≠ Fin.castSucc i := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
      have hne2 : Fin.castSucc i' ≠ Fin.succ i := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
      have hne3 : Fin.castSucc i' ≠ Fin.castSucc j := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
      have hne4 : Fin.castSucc i' ≠ Fin.succ j := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne3 hne4, Equiv.swap_apply_of_ne_of_ne hne1 hne2] at heq''
      simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at heq''; omega
  subst hi_eq
  have hne' : j ≠ j' → False := by
    intro hne; have heq' := congrFun (congrArg DFunLike.coe heq) (Fin.castSucc j)
    rw [typeA_eval_at_second i j hij'] at heq'
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hne1 : Fin.castSucc j ≠ Fin.castSucc j' := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
      have hne2 : Fin.castSucc j ≠ Fin.succ j' := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
      by_cases h : j.val = i.val + 1
      · simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2] at heq'
        have heq_cj : Fin.castSucc j = Fin.succ i := by simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, h]
        rw [heq_cj, Equiv.swap_apply_right] at heq'
        simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at heq'; omega
      · have hne3 : Fin.castSucc j ≠ Fin.castSucc i := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
        have hne4 : Fin.castSucc j ≠ Fin.succ i := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2, Equiv.swap_apply_of_ne_of_ne hne3 hne4] at heq'
        simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at heq'; omega
    · have heq'' := congrFun (congrArg DFunLike.coe heq.symm) (Fin.castSucc j')
      rw [typeA_eval_at_second i j' hi'j''] at heq''
      have hne1 : Fin.castSucc j' ≠ Fin.castSucc j := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
      have hne2 : Fin.castSucc j' ≠ Fin.succ j := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
      by_cases h : j'.val = i.val + 1
      · simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2] at heq''
        have heq_cj' : Fin.castSucc j' = Fin.succ i := by simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, h]
        rw [heq_cj', Equiv.swap_apply_right] at heq''
        simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at heq''; omega
      · have hne3 : Fin.castSucc j' ≠ Fin.castSucc i := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
        have hne4 : Fin.castSucc j' ≠ Fin.succ i := by simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2, Equiv.swap_apply_of_ne_of_ne hne3 hne4] at heq''
        simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at heq''; omega
  exact ⟨rfl, by by_contra hne; exact hne' hne⟩

-- Helper lemma: cardinality of pairsLt
private lemma card_pairsLt (m : ℕ) :
    (Finset.filter (fun p : Fin (m + 1) × Fin (m + 1) => p.1 < p.2) Finset.univ).card = (m + 1).choose 2 := by
  rw [Nat.choose_two_right]
  have h1 : (filter (fun p : Fin (m + 1) × Fin (m + 1) => p.1 < p.2) univ).card =
           ∑ i : Fin (m + 1), (Finset.filter (fun j : Fin (m + 1) => i < j) univ).card := by
    rw [card_eq_sum_ones, sum_filter, ← Finset.univ_product_univ, sum_product]
    congr 1; ext i; rw [card_eq_sum_ones, sum_filter]
  have h2 : ∀ i : Fin (m + 1), (Finset.filter (fun j : Fin (m + 1) => i < j) univ).card = m - i.val := by
    intro i
    have : (Finset.filter (fun j : Fin (m + 1) => i < j) univ) = (Finset.Ioi i) := by
      ext j; simp only [mem_filter, mem_univ, true_and, mem_Ioi]
    rw [this, Fin.card_Ioi]; omega
  rw [h1]; simp_rw [h2]
  have h3 : ∑ i : Fin (m + 1), (m - i.val) = ∑ i ∈ Finset.range (m + 1), (m - i) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => m - i)]
  rw [h3]
  have h4 : ∑ i ∈ Finset.range (m + 1), (m - i) = ∑ i ∈ Finset.range (m + 1), i := by
    conv_lhs => rw [← Finset.sum_range_reflect (fun i => m - i)]
    apply Finset.sum_congr rfl; intro i hi; simp only [Finset.mem_range] at hi; omega
  rw [h4, Finset.sum_range_id]

-- Helper lemma for the formula
private lemma formula_helper' (m : ℕ) :
    (m + 1).choose 2 + m = m * (m + 3) / 2 := by
  rw [Nat.choose_two_right]
  simp only [show m + 1 - 1 = m by omega]
  have heq : (m + 1) * m + 2 * m = m * (m + 3) := by ring
  have h3 : (m + 1) * m / 2 + m = ((m + 1) * m + 2 * m) / 2 := by
    rw [Nat.add_mul_div_left ((m + 1) * m) m (by omega : 0 < 2)]
  rw [h3, heq]

-- Helper lemma for counting Type B permutations
private lemma card_typeB_helper (m : ℕ) :
    let typeB : Finset (Equiv.Perm (Fin (m + 2))) :=
      (Finset.univ : Finset (Fin m)).image (fun i =>
        Equiv.swap (Fin.castSucc ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩)
                   (Fin.succ ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩) *
        Equiv.swap (Fin.castSucc ⟨i.val, Nat.lt_add_right 1 i.isLt⟩)
                   (Fin.succ ⟨i.val, Nat.lt_add_right 1 i.isLt⟩))
    typeB.card = m := by
  intro typeB
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    simp only at hij
    apply Fin.ext
    by_contra hne
    have h_or : i.val < j.val ∨ j.val < i.val := by
      rcases lt_trichotomy i.val j.val with h | h | h
      · left; exact h
      · exact absurd h hne
      · right; exact h
    rcases h_or with h | h
    · let x : Fin (m + 2) := ⟨i.val, Nat.lt_add_right 2 i.isLt⟩
      have hj_fix : (Equiv.swap (Fin.castSucc ⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩)
                                (Fin.succ ⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩) *
                     Equiv.swap (Fin.castSucc ⟨j.val, Nat.lt_add_right 1 j.isLt⟩)
                                (Fin.succ ⟨j.val, Nat.lt_add_right 1 j.isLt⟩)) x = x := by
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, x]
        have h1 : (⟨i.val, Nat.lt_add_right 2 i.isLt⟩ : Fin (m + 2)) ≠
                  Fin.castSucc (⟨j.val, Nat.lt_add_right 1 j.isLt⟩ : Fin (m + 1)) := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
        have h2 : (⟨i.val, Nat.lt_add_right 2 i.isLt⟩ : Fin (m + 2)) ≠
                  Fin.succ (⟨j.val, Nat.lt_add_right 1 j.isLt⟩ : Fin (m + 1)) := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_succ]; omega
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        have h3 : (⟨i.val, Nat.lt_add_right 2 i.isLt⟩ : Fin (m + 2)) ≠
                  Fin.castSucc (⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩ : Fin (m + 1)) := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
        have h4 : (⟨i.val, Nat.lt_add_right 2 i.isLt⟩ : Fin (m + 2)) ≠
                  Fin.succ (⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩ : Fin (m + 1)) := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_succ]; omega
        rw [Equiv.swap_apply_of_ne_of_ne h3 h4]
      have hi_move : (Equiv.swap (Fin.castSucc ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩)
                                 (Fin.succ ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩) *
                      Equiv.swap (Fin.castSucc ⟨i.val, Nat.lt_add_right 1 i.isLt⟩)
                                 (Fin.succ ⟨i.val, Nat.lt_add_right 1 i.isLt⟩)) x =
                     ⟨i.val + 2, Nat.add_lt_add_right i.isLt 2⟩ := by
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, x]
        have h1 : (⟨i.val, Nat.lt_add_right 2 i.isLt⟩ : Fin (m + 2)) =
                  Fin.castSucc (⟨i.val, Nat.lt_add_right 1 i.isLt⟩ : Fin (m + 1)) := by
          simp only [Fin.ext_iff, Fin.val_castSucc]
        rw [h1, Equiv.swap_apply_left]
        have h2 : Fin.succ (⟨i.val, Nat.lt_add_right 1 i.isLt⟩ : Fin (m + 1)) =
                  Fin.castSucc (⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩ : Fin (m + 1)) := by
          simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
        rw [h2, Equiv.swap_apply_left]
        simp only [Fin.ext_iff, Fin.val_succ]
      have heq := congrFun (congrArg DFunLike.coe hij) x
      rw [hi_move, hj_fix] at heq
      simp only [x] at heq
      have : i.val + 2 = i.val := Fin.mk.inj heq
      omega
    · let x : Fin (m + 2) := ⟨j.val, Nat.lt_add_right 2 j.isLt⟩
      have hi_fix : (Equiv.swap (Fin.castSucc ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩)
                                (Fin.succ ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩) *
                     Equiv.swap (Fin.castSucc ⟨i.val, Nat.lt_add_right 1 i.isLt⟩)
                                (Fin.succ ⟨i.val, Nat.lt_add_right 1 i.isLt⟩)) x = x := by
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, x]
        have h1 : (⟨j.val, Nat.lt_add_right 2 j.isLt⟩ : Fin (m + 2)) ≠
                  Fin.castSucc (⟨i.val, Nat.lt_add_right 1 i.isLt⟩ : Fin (m + 1)) := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
        have h2 : (⟨j.val, Nat.lt_add_right 2 j.isLt⟩ : Fin (m + 2)) ≠
                  Fin.succ (⟨i.val, Nat.lt_add_right 1 i.isLt⟩ : Fin (m + 1)) := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_succ]; omega
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        have h3 : (⟨j.val, Nat.lt_add_right 2 j.isLt⟩ : Fin (m + 2)) ≠
                  Fin.castSucc (⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩ : Fin (m + 1)) := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; omega
        have h4 : (⟨j.val, Nat.lt_add_right 2 j.isLt⟩ : Fin (m + 2)) ≠
                  Fin.succ (⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩ : Fin (m + 1)) := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_succ]; omega
        rw [Equiv.swap_apply_of_ne_of_ne h3 h4]
      have hj_move : (Equiv.swap (Fin.castSucc ⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩)
                                 (Fin.succ ⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩) *
                      Equiv.swap (Fin.castSucc ⟨j.val, Nat.lt_add_right 1 j.isLt⟩)
                                 (Fin.succ ⟨j.val, Nat.lt_add_right 1 j.isLt⟩)) x =
                     ⟨j.val + 2, Nat.add_lt_add_right j.isLt 2⟩ := by
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, x]
        have h1 : (⟨j.val, Nat.lt_add_right 2 j.isLt⟩ : Fin (m + 2)) =
                  Fin.castSucc (⟨j.val, Nat.lt_add_right 1 j.isLt⟩ : Fin (m + 1)) := by
          simp only [Fin.ext_iff, Fin.val_castSucc]
        rw [h1, Equiv.swap_apply_left]
        have h2 : Fin.succ (⟨j.val, Nat.lt_add_right 1 j.isLt⟩ : Fin (m + 1)) =
                  Fin.castSucc (⟨j.val + 1, Nat.add_lt_add_right j.isLt 1⟩ : Fin (m + 1)) := by
          simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
        rw [h2, Equiv.swap_apply_left]
        simp only [Fin.ext_iff, Fin.val_succ]
      have heq := congrFun (congrArg DFunLike.coe hij) x
      rw [hi_fix, hj_move] at heq
      simp only [x] at heq
      have : j.val = j.val + 2 := Fin.mk.inj heq
      omega

set_option backward.isDefEq.respectTransparency false in
theorem card_invCount_eq_two (hn : 2 ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => invCount σ = 2)).card =
    (n - 2) * (n + 1) / 2 := by
  cases' n with m
  · omega
  cases' m with m
  · omega
  -- Now n = m + 2 ≥ 2
  have hn' : m + 1 + 1 - 2 = m := by omega
  have hn'' : m + 1 + 1 + 1 = m + 3 := by omega
  simp only [hn', hn'']
  -- Define the index sets for the two types of permutations with invCount = 2
  -- Type A: s_i * s_j for i < j (products of simple transpositions)
  -- Type B: s_{i+1} * s_i for i (adjacent transpositions in reverse order)
  let pairsLt : Finset (Fin (m + 1) × Fin (m + 1)) :=
    Finset.filter (fun p => p.1 < p.2) Finset.univ
  let typeA : Finset (Equiv.Perm (Fin (m + 2))) :=
    pairsLt.image (fun p =>
      Equiv.swap (Fin.castSucc p.1) (Fin.succ p.1) *
      Equiv.swap (Fin.castSucc p.2) (Fin.succ p.2))
  let typeB : Finset (Equiv.Perm (Fin (m + 2))) :=
    (Finset.univ : Finset (Fin m)).image (fun i =>
      Equiv.swap (Fin.castSucc ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩)
                 (Fin.succ ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩) *
      Equiv.swap (Fin.castSucc ⟨i.val, Nat.lt_add_right 1 i.isLt⟩)
                 (Fin.succ ⟨i.val, Nat.lt_add_right 1 i.isLt⟩))
  -- The proof requires showing:
  -- 1. typeA ∪ typeB = {σ : invCount σ = 2}
  -- 2. typeA ∩ typeB = ∅ (disjoint)
  -- 3. |typeA| = (m+1 choose 2)
  -- 4. |typeB| = m
  have h_union : Finset.univ.filter (fun σ => invCount σ = 2) = typeA ∪ typeB := by
    -- Helper: invCount of typeA elements is 2
    have invCount_typeA : ∀ i j : Fin (m + 1), i < j →
        invCount (Equiv.swap (Fin.castSucc i) (Fin.succ i) *
                  Equiv.swap (Fin.castSucc j) (Fin.succ j)) = 2 := by
      intro i j hij
      -- Case split: j = i + 1 (adjacent) or j > i + 1 (non-adjacent)
      by_cases hadj : j.val = i.val + 1
      · -- Adjacent case: 3-cycle with inversions {(ci, sj), (si, sj)}
        have hci : (Fin.castSucc i).val = i.val := Fin.val_castSucc i
        have hsi : (Fin.succ i).val = i.val + 1 := Fin.val_succ i
        have hcj : (Fin.castSucc j).val = j.val := Fin.val_castSucc j
        have hsj : (Fin.succ j).val = j.val + 1 := Fin.val_succ j
        have h_si_eq_cj : Fin.succ i = Fin.castSucc j := by
          simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]; omega
        have h_ci_si : Fin.castSucc i < Fin.succ i := by omega
        have h_si_sj : Fin.succ i < Fin.succ j := by omega
        have h_ci_sj : Fin.castSucc i < Fin.succ j := by omega
        have h_ci_ne_si : Fin.castSucc i ≠ Fin.succ i := ne_of_lt h_ci_si
        have h_ci_ne_cj : Fin.castSucc i ≠ Fin.castSucc j := by rw [← h_si_eq_cj]; exact h_ci_ne_si
        have h_ci_ne_sj : Fin.castSucc i ≠ Fin.succ j := by
          intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at h; omega
        have h_si_ne_sj : Fin.succ i ≠ Fin.succ j := by
          intro h; simp only [Fin.ext_iff, Fin.val_succ] at h; omega
        set σ := Equiv.swap (Fin.castSucc i) (Fin.succ i) * Equiv.swap (Fin.castSucc j) (Fin.succ j) with hσ_def
        have hσ_ci : σ (Fin.castSucc i) = Fin.succ i := by
          simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
          rw [Equiv.swap_apply_of_ne_of_ne h_ci_ne_cj h_ci_ne_sj, Equiv.swap_apply_left]
        have hσ_si : σ (Fin.succ i) = Fin.succ j := by
          simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
          have step1 : (Equiv.swap (Fin.castSucc j) (Fin.succ j) : Equiv.Perm (Fin (m + 2))) (Fin.succ i) = Fin.succ j := by
            simp only [h_si_eq_cj, Equiv.swap_apply_left]
          rw [step1]
          exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_sj.symm h_si_ne_sj.symm
        have hσ_sj : σ (Fin.succ j) = Fin.castSucc i := by
          simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
          rw [Equiv.swap_apply_right, ← h_si_eq_cj, Equiv.swap_apply_right]
        have hσ_other : ∀ x, x ≠ Fin.castSucc i → x ≠ Fin.succ i → x ≠ Fin.succ j → σ x = x := by
          intro x hx1 hx2 hx3
          simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
          have hx2' : x ≠ Fin.castSucc j := h_si_eq_cj ▸ hx2
          rw [Equiv.swap_apply_of_ne_of_ne hx2' hx3, Equiv.swap_apply_of_ne_of_ne hx1 hx2]
        have hinv : inv σ = {(Fin.castSucc i, Fin.succ j), (Fin.succ i, Fin.succ j)} := by
          ext ⟨a, b⟩
          simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
          constructor
          · intro ⟨hab, hgt⟩
            by_cases ha_ci : a = Fin.castSucc i
            · subst ha_ci
              by_cases hb_si : b = Fin.succ i
              · simp only [hb_si, hσ_ci, hσ_si] at hgt; omega
              · by_cases hb_sj : b = Fin.succ j
                · left; exact ⟨rfl, hb_sj⟩
                · have hb_ne_ci : b ≠ Fin.castSucc i := by intro h; simp only [h] at hab; omega
                  have hσb : σ b = b := hσ_other b hb_ne_ci hb_si hb_sj
                  simp only [hσ_ci, hσb] at hgt; omega
            · by_cases ha_si : a = Fin.succ i
              · subst ha_si
                simp only [hσ_si] at hgt
                by_cases hb_ci : b = Fin.castSucc i
                · simp only [hb_ci] at hab; omega
                · by_cases hb_si : b = Fin.succ i
                  · simp only [hb_si] at hab; omega
                  · by_cases hb_sj : b = Fin.succ j
                    · right; exact ⟨rfl, hb_sj⟩
                    · have hσb : σ b = b := hσ_other b hb_ci hb_si hb_sj
                      simp only [hσb] at hgt hab; omega
              · by_cases ha_sj : a = Fin.succ j
                · subst ha_sj
                  simp only [hσ_sj] at hgt
                  by_cases hb_ci : b = Fin.castSucc i
                  · simp only [hb_ci] at hab; omega
                  · by_cases hb_si : b = Fin.succ i
                    · simp only [hb_si] at hab; omega
                    · by_cases hb_sj : b = Fin.succ j
                      · simp only [hb_sj] at hab; omega
                      · have hσb : σ b = b := hσ_other b hb_ci hb_si hb_sj
                        simp only [hσb] at hgt hab; omega
                · have hσa : σ a = a := hσ_other a ha_ci ha_si ha_sj
                  by_cases hb_ci : b = Fin.castSucc i
                  · simp only [hb_ci, hσa, hσ_ci] at hgt hab; omega
                  · by_cases hb_si : b = Fin.succ i
                    · simp only [hb_si, hσa, hσ_si] at hgt hab; omega
                    · by_cases hb_sj : b = Fin.succ j
                      · simp only [hb_sj, hσa, hσ_sj] at hgt hab; omega
                      · have hσb : σ b = b := hσ_other b hb_ci hb_si hb_sj
                        simp only [hσa, hσb] at hgt hab; omega
          · intro h
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨h_ci_sj, by simp only [hσ_ci, hσ_sj]; omega⟩
            · exact ⟨h_si_sj, by simp only [hσ_si, hσ_sj]; omega⟩
        simp only [invCount, hinv]
        have hne : (Fin.castSucc i, Fin.succ j) ≠ (Fin.succ i, Fin.succ j) := by
          simp only [Prod.ext_iff, ne_eq, not_and]
          intro h; exact absurd h h_ci_ne_si
        rw [Finset.card_pair hne]
      · -- Non-adjacent case: two disjoint swaps with inversions {(ci, si), (cj, sj)}
        have hgap : j.val > i.val + 1 := by have : i.val < j.val := hij; omega
        have hci : (Fin.castSucc i).val = i.val := Fin.val_castSucc i
        have hsi : (Fin.succ i).val = i.val + 1 := Fin.val_succ i
        have hcj : (Fin.castSucc j).val = j.val := Fin.val_castSucc j
        have hsj : (Fin.succ j).val = j.val + 1 := Fin.val_succ j
        have h_ci_si : Fin.castSucc i < Fin.succ i := by omega
        have h_cj_sj : Fin.castSucc j < Fin.succ j := by omega
        have h_sj_ne_ci : Fin.succ j ≠ Fin.castSucc i := by
          intro h; simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc] at h; omega
        have h_sj_ne_si : Fin.succ j ≠ Fin.succ i := by
          intro h; simp only [Fin.ext_iff, Fin.val_succ] at h; omega
        have h_cj_ne_ci : Fin.castSucc j ≠ Fin.castSucc i := by
          intro h; simp only [Fin.ext_iff, Fin.val_castSucc] at h; omega
        have h_cj_ne_si : Fin.castSucc j ≠ Fin.succ i := by
          intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at h; omega
        have h_ci_ne_cj : Fin.castSucc i ≠ Fin.castSucc j := h_cj_ne_ci.symm
        have h_ci_ne_sj : Fin.castSucc i ≠ Fin.succ j := h_sj_ne_ci.symm
        have h_si_ne_cj : Fin.succ i ≠ Fin.castSucc j := h_cj_ne_si.symm
        have h_si_ne_sj : Fin.succ i ≠ Fin.succ j := h_sj_ne_si.symm
        set σ := Equiv.swap (Fin.castSucc i) (Fin.succ i) * Equiv.swap (Fin.castSucc j) (Fin.succ j) with hσ_def
        have hσ_ci : σ (Fin.castSucc i) = Fin.succ i := by
          simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
          rw [Equiv.swap_apply_of_ne_of_ne h_ci_ne_cj h_ci_ne_sj, Equiv.swap_apply_left]
        have hσ_si : σ (Fin.succ i) = Fin.castSucc i := by
          simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
          rw [Equiv.swap_apply_of_ne_of_ne h_si_ne_cj h_si_ne_sj, Equiv.swap_apply_right]
        have hσ_cj : σ (Fin.castSucc j) = Fin.succ j := by
          simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
          rw [Equiv.swap_apply_left]
          exact Equiv.swap_apply_of_ne_of_ne h_sj_ne_ci h_sj_ne_si
        have hσ_sj : σ (Fin.succ j) = Fin.castSucc j := by
          simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
          rw [Equiv.swap_apply_right]
          exact Equiv.swap_apply_of_ne_of_ne h_cj_ne_ci h_cj_ne_si
        have hσ_other : ∀ x, x ≠ Fin.castSucc i → x ≠ Fin.succ i → x ≠ Fin.castSucc j → x ≠ Fin.succ j → σ x = x := by
          intro x hx1 hx2 hx3 hx4
          simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
          rw [Equiv.swap_apply_of_ne_of_ne hx3 hx4, Equiv.swap_apply_of_ne_of_ne hx1 hx2]
        have hinv : inv σ = {(Fin.castSucc i, Fin.succ i), (Fin.castSucc j, Fin.succ j)} := by
          ext ⟨a, b⟩
          simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
          constructor
          · intro ⟨hab, hgt⟩
            by_cases ha_ci : a = Fin.castSucc i
            · subst ha_ci
              by_cases hb_si : b = Fin.succ i
              · left; exact ⟨rfl, hb_si⟩
              · by_cases hb_cj : b = Fin.castSucc j
                · simp only [hσ_ci, hb_cj, hσ_cj] at hgt; omega
                · by_cases hb_sj : b = Fin.succ j
                  · simp only [hσ_ci, hb_sj, hσ_sj] at hgt; omega
                  · have hb_ne_ci : b ≠ Fin.castSucc i := by intro h; simp only [h] at hab; omega
                    have hσb : σ b = b := hσ_other b hb_ne_ci hb_si hb_cj hb_sj
                    simp only [hσ_ci, hσb] at hgt; omega
            · by_cases ha_si : a = Fin.succ i
              · subst ha_si
                simp only [hσ_si] at hgt
                by_cases hb_ci : b = Fin.castSucc i
                · simp only [hb_ci] at hab; omega
                · by_cases hb_si : b = Fin.succ i
                  · simp only [hb_si] at hab; omega
                  · by_cases hb_cj : b = Fin.castSucc j
                    · simp only [hb_cj, hσ_cj] at hgt; omega
                    · by_cases hb_sj : b = Fin.succ j
                      · simp only [hb_sj, hσ_sj] at hgt; omega
                      · have hσb : σ b = b := hσ_other b hb_ci hb_si hb_cj hb_sj
                        simp only [hσb] at hgt hab; omega
              · by_cases ha_cj : a = Fin.castSucc j
                · subst ha_cj
                  by_cases hb_sj : b = Fin.succ j
                  · right; exact ⟨rfl, hb_sj⟩
                  · by_cases hb_ci : b = Fin.castSucc i
                    · simp only [hb_ci] at hab; omega
                    · by_cases hb_si : b = Fin.succ i
                      · simp only [hb_si] at hab; omega
                      · by_cases hb_cj : b = Fin.castSucc j
                        · simp only [hb_cj] at hab; omega
                        · have hσb : σ b = b := hσ_other b hb_ci hb_si hb_cj hb_sj
                          simp only [hσ_cj, hσb] at hgt hab; omega
                · by_cases ha_sj : a = Fin.succ j
                  · subst ha_sj
                    simp only [hσ_sj] at hgt
                    by_cases hb_ci : b = Fin.castSucc i
                    · simp only [hb_ci] at hab; omega
                    · by_cases hb_si : b = Fin.succ i
                      · simp only [hb_si] at hab; omega
                      · by_cases hb_cj : b = Fin.castSucc j
                        · simp only [hb_cj] at hab; omega
                        · by_cases hb_sj : b = Fin.succ j
                          · simp only [hb_sj] at hab; omega
                          · have hσb : σ b = b := hσ_other b hb_ci hb_si hb_cj hb_sj
                            simp only [hσb] at hgt hab; omega
                  · have hσa : σ a = a := hσ_other a ha_ci ha_si ha_cj ha_sj
                    by_cases hb_ci : b = Fin.castSucc i
                    · simp only [hb_ci, hσa, hσ_ci] at hgt hab; omega
                    · by_cases hb_si : b = Fin.succ i
                      · simp only [hb_si, hσa, hσ_si] at hgt hab; omega
                      · by_cases hb_cj : b = Fin.castSucc j
                        · simp only [hb_cj, hσa, hσ_cj] at hgt hab; omega
                        · by_cases hb_sj : b = Fin.succ j
                          · simp only [hb_sj, hσa, hσ_sj] at hgt hab; omega
                          · have hσb : σ b = b := hσ_other b hb_ci hb_si hb_cj hb_sj
                            simp only [hσa, hσb] at hgt hab; omega
          · intro h
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨h_ci_si, by simp only [hσ_ci, hσ_si]; omega⟩
            · exact ⟨h_cj_sj, by simp only [hσ_cj, hσ_sj]; omega⟩
        simp only [invCount, hinv]
        have hne : (Fin.castSucc i, Fin.succ i) ≠ (Fin.castSucc j, Fin.succ j) := by
          simp only [Prod.ext_iff, Fin.ext_iff, ne_eq, not_and, Fin.val_castSucc, Fin.val_succ]
          intro h; omega
        rw [Finset.card_pair hne]
    -- Helper: invCount of typeB elements is 2
    have invCount_typeB : ∀ i : Fin m,
        invCount (Equiv.swap (Fin.castSucc ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩)
                             (Fin.succ ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩) *
                  Equiv.swap (Fin.castSucc ⟨i.val, Nat.lt_add_right 1 i.isLt⟩)
                             (Fin.succ ⟨i.val, Nat.lt_add_right 1 i.isLt⟩)) = 2 := by
      intro i
      -- TypeB is a 3-cycle: ci → si1, si → ci, si1 → si
      -- Inversions: {(ci, si), (ci, si1)}
      let i0 : Fin (m + 1) := ⟨i.val, Nat.lt_add_right 1 i.isLt⟩
      let i1 : Fin (m + 1) := ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩
      have h_si_eq_ci1 : Fin.succ i0 = Fin.castSucc i1 := by
        simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, i0, i1]
      have hci : (Fin.castSucc i0).val = i.val := Fin.val_castSucc i0
      have hsi : (Fin.succ i0).val = i.val + 1 := Fin.val_succ i0
      have hci1 : (Fin.castSucc i1).val = i.val + 1 := by simp [i1]
      have hsi1 : (Fin.succ i1).val = i.val + 2 := by simp [i1]
      have h_ci_si : Fin.castSucc i0 < Fin.succ i0 := by omega
      have h_si_si1 : Fin.succ i0 < Fin.succ i1 := by omega
      have h_ci_si1 : Fin.castSucc i0 < Fin.succ i1 := by omega
      have h_ci_ne_si : Fin.castSucc i0 ≠ Fin.succ i0 := ne_of_lt h_ci_si
      have h_ci_ne_ci1 : Fin.castSucc i0 ≠ Fin.castSucc i1 := by rw [← h_si_eq_ci1]; exact h_ci_ne_si
      have h_ci_ne_si1 : Fin.castSucc i0 ≠ Fin.succ i1 := by
        intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, i0, i1] at h; omega
      have h_si_ne_si1 : Fin.succ i0 ≠ Fin.succ i1 := by
        intro h; simp only [Fin.ext_iff, Fin.val_succ, i0, i1] at h; omega
      set σ := Equiv.swap (Fin.castSucc i1) (Fin.succ i1) * Equiv.swap (Fin.castSucc i0) (Fin.succ i0) with hσ_def
      have hσ_ci : σ (Fin.castSucc i0) = Fin.succ i1 := by
        simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
        rw [Equiv.swap_apply_left, h_si_eq_ci1, Equiv.swap_apply_left]
      have hσ_si : σ (Fin.succ i0) = Fin.castSucc i0 := by
        simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
        rw [Equiv.swap_apply_right]
        exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_ci1 h_ci_ne_si1
      have hσ_si1 : σ (Fin.succ i1) = Fin.succ i0 := by
        simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne h_ci_ne_si1.symm h_si_ne_si1.symm]
        rw [Equiv.swap_apply_right, ← h_si_eq_ci1]
      have hσ_other : ∀ x, x ≠ Fin.castSucc i0 → x ≠ Fin.succ i0 → x ≠ Fin.succ i1 → σ x = x := by
        intro x hx1 hx2 hx3
        simp only [hσ_def, Equiv.Perm.coe_mul, Function.comp_apply]
        have hx2' : x ≠ Fin.castSucc i1 := h_si_eq_ci1 ▸ hx2
        rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2, Equiv.swap_apply_of_ne_of_ne hx2' hx3]
      have hinv : inv σ = {(Fin.castSucc i0, Fin.succ i0), (Fin.castSucc i0, Fin.succ i1)} := by
        ext ⟨a, b⟩
        simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · intro ⟨hab, hgt⟩
          by_cases ha_ci : a = Fin.castSucc i0
          · subst ha_ci
            by_cases hb_si : b = Fin.succ i0
            · left; exact ⟨rfl, hb_si⟩
            · by_cases hb_si1 : b = Fin.succ i1
              · right; exact ⟨rfl, hb_si1⟩
              · have hb_ne_ci : b ≠ Fin.castSucc i0 := by intro h; simp only [h] at hab; omega
                have hσb : σ b = b := hσ_other b hb_ne_ci hb_si hb_si1
                simp only [hσ_ci, hσb] at hgt; omega
          · by_cases ha_si : a = Fin.succ i0
            · subst ha_si
              simp only [hσ_si] at hgt
              by_cases hb_ci : b = Fin.castSucc i0
              · simp only [hb_ci] at hab; omega
              · by_cases hb_si : b = Fin.succ i0
                · simp only [hb_si] at hab; omega
                · by_cases hb_si1 : b = Fin.succ i1
                  · simp only [hb_si1, hσ_si1] at hgt; omega
                  · have hσb : σ b = b := hσ_other b hb_ci hb_si hb_si1
                    simp only [hσb] at hgt hab; omega
            · by_cases ha_si1 : a = Fin.succ i1
              · subst ha_si1
                simp only [hσ_si1] at hgt
                by_cases hb_ci : b = Fin.castSucc i0
                · simp only [hb_ci] at hab; omega
                · by_cases hb_si : b = Fin.succ i0
                  · simp only [hb_si] at hab; omega
                  · by_cases hb_si1 : b = Fin.succ i1
                    · simp only [hb_si1] at hab; omega
                    · have hσb : σ b = b := hσ_other b hb_ci hb_si hb_si1
                      simp only [hσb] at hgt hab; omega
              · have hσa : σ a = a := hσ_other a ha_ci ha_si ha_si1
                by_cases hb_ci : b = Fin.castSucc i0
                · simp only [hb_ci, hσa, hσ_ci] at hgt hab; omega
                · by_cases hb_si : b = Fin.succ i0
                  · simp only [hb_si, hσa, hσ_si] at hgt hab; omega
                  · by_cases hb_si1 : b = Fin.succ i1
                    · simp only [hb_si1, hσa, hσ_si1] at hgt hab; omega
                    · have hσb : σ b = b := hσ_other b hb_ci hb_si hb_si1
                      simp only [hσa, hσb] at hgt hab; omega
        · intro h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨h_ci_si, by simp only [hσ_ci, hσ_si]; omega⟩
          · exact ⟨h_ci_si1, by simp only [hσ_ci, hσ_si1]; omega⟩
      simp only [invCount, hinv]
      have hne : (Fin.castSucc i0, Fin.succ i0) ≠ (Fin.castSucc i0, Fin.succ i1) := by
        simp only [Prod.ext_iff, ne_eq, not_and, true_implies]
        exact h_si_ne_si1
      rw [Finset.card_pair hne]
    -- Helper: every permutation with invCount = 2 is in typeA or typeB
    -- Helper lemma: if (a, b) is an inversion with gap > 1, the other inversion involves a middle element
    have two_inv_gap_constraint : ∀ (σ : Equiv.Perm (Fin (m + 2))) (a b c d : Fin (m + 2)),
        (a, b) ≠ (c, d) → inv σ = {(a, b), (c, d)} → a < b → b.val > a.val + 1 →
        (c = a ∧ a < d ∧ d < b) ∨ (d = b ∧ a < c ∧ c < b) := by
      intro σ a b c d hne hinv_eq hab_lt hgap
      have hab_inv : (a, b) ∈ inv σ := by rw [hinv_eq]; simp
      have hcd_inv : (c, d) ∈ inv σ := by rw [hinv_eq]; simp
      simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and] at hab_inv hcd_inv
      obtain ⟨_, hab_gt⟩ := hab_inv
      have he_exists : ∃ e : Fin (m + 2), a < e ∧ e < b := by
        use ⟨a.val + 1, by omega⟩; constructor <;> exact Fin.mk_lt_mk.mpr (by omega)
      obtain ⟨e, hae, heb⟩ := he_exists
      rcases lt_trichotomy (σ e) (σ a) with hea | hea | hea
      · have hae_inv : (a, e) ∈ inv σ := by simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hae, hea⟩
        rw [hinv_eq] at hae_inv; simp only [Finset.mem_insert, Finset.mem_singleton] at hae_inv
        rcases hae_inv with hae_eq_ab | hae_eq_cd
        · have he_eq : e = b := (Prod.mk.injEq a e a b).mp hae_eq_ab |>.2; rw [he_eq] at heb; exact absurd heb (lt_irrefl b)
        · left; have hc_eq : c = a := (Prod.mk.injEq a e c d).mp hae_eq_cd |>.1 |>.symm
          have he_eq : e = d := (Prod.mk.injEq a e c d).mp hae_eq_cd |>.2
          exact ⟨hc_eq, by rw [← he_eq]; exact hae, by rw [← he_eq]; exact heb⟩
      · exact absurd (σ.injective hea) (Fin.ne_of_lt hae).symm
      · rcases lt_trichotomy (σ e) (σ b) with heb' | heb' | heb'
        · have h3 : σ e > σ b := lt_trans hab_gt hea; exact absurd heb' (not_lt.mpr (le_of_lt h3))
        · exact absurd (σ.injective heb') (Fin.ne_of_lt heb)
        · have heb_inv : (e, b) ∈ inv σ := by simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨heb, heb'⟩
          rw [hinv_eq] at heb_inv; simp only [Finset.mem_insert, Finset.mem_singleton] at heb_inv
          rcases heb_inv with heb_eq_ab | heb_eq_cd
          · have he_eq : e = a := (Prod.mk.injEq e b a b).mp heb_eq_ab |>.1; rw [he_eq] at hae; exact absurd hae (lt_irrefl a)
          · right; have he_eq : e = c := (Prod.mk.injEq e b c d).mp heb_eq_cd |>.1
            have hb_eq : b = d := (Prod.mk.injEq e b c d).mp heb_eq_cd |>.2
            exact ⟨hb_eq.symm, by rw [← he_eq]; exact hae, by rw [← he_eq]; exact heb⟩
    -- Key lemma: permutations with same inversions are equal
    have perm_eq_of_inv_eq : ∀ (σ τ : Equiv.Perm (Fin (m + 2))), inv σ = inv τ → σ = τ := by
      intro σ τ h
      have h1 : inv (σ * τ⁻¹) = ∅ := by
        ext ⟨i, j⟩
        constructor
        · intro hij
          simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and,
                     Equiv.Perm.coe_mul, Function.comp_apply] at hij
          obtain ⟨hij_lt, hij_gt⟩ := hij
          set a := τ⁻¹ i
          set b := τ⁻¹ j
          have hτa : τ a = i := τ.apply_symm_apply i
          have hτb : τ b = j := τ.apply_symm_apply j
          have hτab : τ a < τ b := by rw [hτa, hτb]; exact hij_lt
          have hσab : σ a > σ b := hij_gt
          rcases lt_trichotomy a b with hab | hab | hab
          · have hmem_σ : (a, b) ∈ inv σ := by
              simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hab, hσab⟩
            have hmem_τ : (a, b) ∉ inv τ := by
              simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt]
              intro _; exact le_of_lt hτab
            rw [h] at hmem_σ; exact (hmem_τ hmem_σ).elim
          · have heq : i = j := by rw [← hτa, hab, hτb]
            exact ((Fin.ne_of_lt hij_lt) heq).elim
          · have hgt : τ b > τ a := by rw [hτb, hτa]; exact hij_lt
            have hmem_τ : (b, a) ∈ inv τ := by
              simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hab, hgt⟩
            have hmem_σ : (b, a) ∉ inv σ := by
              simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt]
              intro _; exact le_of_lt hσab
            rw [← h] at hmem_τ; exact (hmem_σ hmem_τ).elim
        · intro h; simp at h
      have h2 : invCount (σ * τ⁻¹) = 0 := by simp only [invCount, h1, Finset.card_empty]
      have h3 : σ * τ⁻¹ = 1 := by rw [invCount_eq_zero_iff] at h2; exact h2
      calc σ = σ * 1 := by rw [mul_one]
        _ = σ * (τ⁻¹ * τ) := by rw [inv_mul_cancel]
        _ = (σ * τ⁻¹) * τ := by rw [mul_assoc]
        _ = 1 * τ := by rw [h3]
        _ = τ := by rw [one_mul]
    have invCount_two_classification : ∀ σ : Equiv.Perm (Fin (m + 2)), invCount σ = 2 →
          (∃ i j : Fin (m + 1), i < j ∧ σ = Equiv.swap (Fin.castSucc i) (Fin.succ i) *
                                            Equiv.swap (Fin.castSucc j) (Fin.succ j)) ∨
          (∃ i : Fin m, σ = Equiv.swap (Fin.castSucc ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩)
                                       (Fin.succ ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩) *
                            Equiv.swap (Fin.castSucc ⟨i.val, Nat.lt_add_right 1 i.isLt⟩)
                                       (Fin.succ ⟨i.val, Nat.lt_add_right 1 i.isLt⟩)) := by
        intro σ hσ
        -- Get the two inversions
        obtain ⟨⟨a, b⟩, ⟨c, d⟩, hne, hinv_eq⟩ := Finset.card_eq_two.mp hσ
        have hab_inv : (a, b) ∈ inv σ := by rw [hinv_eq]; simp
        have hcd_inv : (c, d) ∈ inv σ := by rw [hinv_eq]; simp
        simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and] at hab_inv hcd_inv
        obtain ⟨hab_lt, hab_gt⟩ := hab_inv
        obtain ⟨hcd_lt, hcd_gt⟩ := hcd_inv
        -- Case split: do both inversions have gap 1?
        by_cases hboth_gap1 : b.val = a.val + 1 ∧ d.val = c.val + 1
        · -- Both have gap 1: Type A non-adjacent (adjacent is impossible)
          obtain ⟨hab_gap, hcd_gap⟩ := hboth_gap1
          have ha_ne_c : a ≠ c := by
            intro heq; subst heq
            have hb_eq_d : b = d := by ext; omega
            exact hne (by simp [hb_eq_d])
          -- Adjacent case (c = a + 1 or a = c + 1) is impossible
          have hnonadj : c.val ≠ a.val + 1 ∧ a.val ≠ c.val + 1 := by
            constructor <;> intro hadj
            · have hb_eq : b.val = a.val + 1 := hab_gap
              have hd_eq : d.val = a.val + 2 := by omega
              have h_trans : σ a > σ d := by
                have hb_eq_c : b = c := by ext; omega
                rw [hb_eq_c] at hab_gt
                exact lt_trans hcd_gt hab_gt
              have had_lt : a < d := by exact Fin.mk_lt_mk.mpr (by omega)
              have had_inv : (a, d) ∈ inv σ := by
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨had_lt, h_trans⟩
              rw [hinv_eq] at had_inv
              simp only [Finset.mem_insert, Finset.mem_singleton] at had_inv
              rcases had_inv with had_eq | had_eq
              · have : d = b := (Prod.mk.injEq a d a b).mp had_eq |>.2; omega
              · have : a = c := (Prod.mk.injEq a d c d).mp had_eq |>.1; omega
            · have hd_eq : d.val = c.val + 1 := hcd_gap
              have hb_eq : b.val = c.val + 2 := by omega
              have ha_eq_d : a = d := by ext; omega
              have hc_lt_a : c < a := by exact Nat.lt_of_add_lt_add_right (by omega : c.val + 1 < a.val + 1)
              have h_trans : σ c > σ b := by
                rw [ha_eq_d] at hab_gt
                exact lt_trans hab_gt hcd_gt
              have hcb_lt : c < b := lt_trans hc_lt_a hab_lt
              have hcb_inv : (c, b) ∈ inv σ := by
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hcb_lt, h_trans⟩
              rw [hinv_eq] at hcb_inv
              simp only [Finset.mem_insert, Finset.mem_singleton] at hcb_inv
              rcases hcb_inv with hcb_eq | hcb_eq
              · have : c = a := (Prod.mk.injEq c b a b).mp hcb_eq |>.1; omega
              · have : b = d := (Prod.mk.injEq c b c d).mp hcb_eq |>.2; omega
          -- Now classify as Type A non-adjacent
          rcases Nat.lt_trichotomy a.val c.val with ha_lt_c | ha_eq_c | hc_lt_a
          · left
            have hgap_ij : c.val > a.val + 1 := by omega
            have ha_bound : a.val < m + 1 := by omega
            have hc_bound : c.val < m + 1 := by omega
            use ⟨a.val, ha_bound⟩, ⟨c.val, hc_bound⟩
            constructor
            · exact ha_lt_c
            · -- Use perm_eq_of_inv_eq to show σ = τ where τ = swap(ci,si) * swap(cj,sj)
              set i : Fin (m + 1) := ⟨a.val, ha_bound⟩
              set j : Fin (m + 1) := ⟨c.val, hc_bound⟩
              have ha_eq_ci : a = Fin.castSucc i := by ext; rfl
              have hb_eq_si : b = Fin.succ i := by ext; simp only [Fin.val_succ, i]; omega
              have hc_eq_cj : c = Fin.castSucc j := by ext; rfl
              have hd_eq_sj : d = Fin.succ j := by ext; simp only [Fin.val_succ, j]; omega
              have h_ci_si : Fin.castSucc i < Fin.succ i := Fin.castSucc_lt_succ
              have h_cj_sj : Fin.castSucc j < Fin.succ j := Fin.castSucc_lt_succ
              have h_ci_ne_cj : Fin.castSucc i ≠ Fin.castSucc j := by
                intro h; have := Fin.castSucc_injective _ h; simp only [Fin.ext_iff, i, j] at this; omega
              have h_ci_ne_sj : Fin.castSucc i ≠ Fin.succ j := by
                intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, i, j] at h; omega
              have h_si_ne_cj : Fin.succ i ≠ Fin.castSucc j := by
                intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, i, j] at h; omega
              have h_si_ne_sj : Fin.succ i ≠ Fin.succ j := by
                intro h; have := Fin.succ_injective _ h; simp only [Fin.ext_iff, i, j] at this; omega
              set τ := Equiv.swap (Fin.castSucc i) (Fin.succ i) * Equiv.swap (Fin.castSucc j) (Fin.succ j)
              have hτ_ci : τ (Fin.castSucc i) = Fin.succ i := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_of_ne_of_ne h_ci_ne_cj h_ci_ne_sj, Equiv.swap_apply_left]
              have hτ_si : τ (Fin.succ i) = Fin.castSucc i := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_of_ne_of_ne h_si_ne_cj h_si_ne_sj, Equiv.swap_apply_right]
              have hτ_cj : τ (Fin.castSucc j) = Fin.succ j := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_left]
                exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_sj.symm h_si_ne_sj.symm
              have hτ_sj : τ (Fin.succ j) = Fin.castSucc j := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_right]
                exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_cj.symm h_si_ne_cj.symm
              have hτ_other : ∀ x, x ≠ Fin.castSucc i → x ≠ Fin.succ i → x ≠ Fin.castSucc j → x ≠ Fin.succ j → τ x = x := by
                intro x hx1 hx2 hx3 hx4
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_of_ne_of_ne hx3 hx4, Equiv.swap_apply_of_ne_of_ne hx1 hx2]
              have hinv_τ : inv τ = {(Fin.castSucc i, Fin.succ i), (Fin.castSucc j, Fin.succ j)} := by
                ext ⟨x, y⟩
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                constructor
                · intro ⟨hxy, hgt⟩
                  by_cases hx_ci : x = Fin.castSucc i
                  · subst hx_ci
                    by_cases hy_si : y = Fin.succ i
                    · left; exact ⟨rfl, hy_si⟩
                    · by_cases hy_cj : y = Fin.castSucc j
                      · simp only [hτ_ci, hy_cj, hτ_cj] at hgt; omega
                      · by_cases hy_sj : y = Fin.succ j
                        · simp only [hτ_ci, hy_sj, hτ_sj] at hgt; omega
                        · have hy_ne_ci : y ≠ Fin.castSucc i := by intro h; simp only [h] at hxy; omega
                          have hτy : τ y = y := hτ_other y hy_ne_ci hy_si hy_cj hy_sj
                          simp only [hτ_ci, hτy] at hgt; omega
                  · by_cases hx_si : x = Fin.succ i
                    · subst hx_si; simp only [hτ_si] at hgt
                      by_cases hy_ci : y = Fin.castSucc i
                      · simp only [hy_ci] at hxy; omega
                      · by_cases hy_si : y = Fin.succ i
                        · simp only [hy_si] at hxy; omega
                        · by_cases hy_cj : y = Fin.castSucc j
                          · simp only [hy_cj, hτ_cj] at hgt; omega
                          · by_cases hy_sj : y = Fin.succ j
                            · simp only [hy_sj, hτ_sj] at hgt; omega
                            · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                              simp only [hτy] at hgt hxy; omega
                    · by_cases hx_cj : x = Fin.castSucc j
                      · subst hx_cj
                        by_cases hy_sj : y = Fin.succ j
                        · right; exact ⟨rfl, hy_sj⟩
                        · by_cases hy_ci : y = Fin.castSucc i
                          · simp only [hy_ci] at hxy; omega
                          · by_cases hy_si : y = Fin.succ i
                            · simp only [hy_si] at hxy; omega
                            · by_cases hy_cj : y = Fin.castSucc j
                              · simp only [hy_cj] at hxy; omega
                              · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                                simp only [hτ_cj, hτy] at hgt hxy; omega
                      · by_cases hx_sj : x = Fin.succ j
                        · subst hx_sj; simp only [hτ_sj] at hgt
                          by_cases hy_ci : y = Fin.castSucc i
                          · simp only [hy_ci] at hxy; omega
                          · by_cases hy_si : y = Fin.succ i
                            · simp only [hy_si] at hxy; omega
                            · by_cases hy_cj : y = Fin.castSucc j
                              · simp only [hy_cj] at hxy; omega
                              · by_cases hy_sj : y = Fin.succ j
                                · simp only [hy_sj] at hxy; omega
                                · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                                  simp only [hτy] at hgt hxy; omega
                        · have hτx : τ x = x := hτ_other x hx_ci hx_si hx_cj hx_sj
                          by_cases hy_ci : y = Fin.castSucc i
                          · simp only [hy_ci, hτx, hτ_ci] at hgt hxy; omega
                          · by_cases hy_si : y = Fin.succ i
                            · simp only [hy_si, hτx, hτ_si] at hgt hxy; omega
                            · by_cases hy_cj : y = Fin.castSucc j
                              · simp only [hy_cj, hτx, hτ_cj] at hgt hxy; omega
                              · by_cases hy_sj : y = Fin.succ j
                                · simp only [hy_sj, hτx, hτ_sj] at hgt hxy; omega
                                · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                                  simp only [hτx, hτy] at hgt hxy; omega
                · intro h
                  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact ⟨h_ci_si, by simp only [hτ_ci, hτ_si]; omega⟩
                  · exact ⟨h_cj_sj, by simp only [hτ_cj, hτ_sj]; omega⟩
              apply perm_eq_of_inv_eq
              rw [hinv_eq, hinv_τ, ha_eq_ci, hb_eq_si, hc_eq_cj, hd_eq_sj]
          · exfalso; exact ha_ne_c (Fin.ext ha_eq_c)
          · left
            have hgap_ij : a.val > c.val + 1 := by omega
            have hc_bound : c.val < m + 1 := by omega
            have ha_bound : a.val < m + 1 := by omega
            use ⟨c.val, hc_bound⟩, ⟨a.val, ha_bound⟩
            constructor
            · exact hc_lt_a
            · -- Use perm_eq_of_inv_eq to show σ = τ where τ = swap(ci,si) * swap(cj,sj)
              -- Here i corresponds to c and j corresponds to a
              set i : Fin (m + 1) := ⟨c.val, hc_bound⟩
              set j : Fin (m + 1) := ⟨a.val, ha_bound⟩
              have hc_eq_ci : c = Fin.castSucc i := by ext; rfl
              have hd_eq_si : d = Fin.succ i := by ext; simp only [Fin.val_succ, i]; omega
              have ha_eq_cj : a = Fin.castSucc j := by ext; rfl
              have hb_eq_sj : b = Fin.succ j := by ext; simp only [Fin.val_succ, j]; omega
              have h_ci_si : Fin.castSucc i < Fin.succ i := Fin.castSucc_lt_succ
              have h_cj_sj : Fin.castSucc j < Fin.succ j := Fin.castSucc_lt_succ
              have h_ci_ne_cj : Fin.castSucc i ≠ Fin.castSucc j := by
                intro h; have := Fin.castSucc_injective _ h; simp only [Fin.ext_iff, i, j] at this; omega
              have h_ci_ne_sj : Fin.castSucc i ≠ Fin.succ j := by
                intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, i, j] at h; omega
              have h_si_ne_cj : Fin.succ i ≠ Fin.castSucc j := by
                intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, i, j] at h; omega
              have h_si_ne_sj : Fin.succ i ≠ Fin.succ j := by
                intro h; have := Fin.succ_injective _ h; simp only [Fin.ext_iff, i, j] at this; omega
              set τ := Equiv.swap (Fin.castSucc i) (Fin.succ i) * Equiv.swap (Fin.castSucc j) (Fin.succ j)
              have hτ_ci : τ (Fin.castSucc i) = Fin.succ i := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_of_ne_of_ne h_ci_ne_cj h_ci_ne_sj, Equiv.swap_apply_left]
              have hτ_si : τ (Fin.succ i) = Fin.castSucc i := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_of_ne_of_ne h_si_ne_cj h_si_ne_sj, Equiv.swap_apply_right]
              have hτ_cj : τ (Fin.castSucc j) = Fin.succ j := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_left]
                exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_sj.symm h_si_ne_sj.symm
              have hτ_sj : τ (Fin.succ j) = Fin.castSucc j := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_right]
                exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_cj.symm h_si_ne_cj.symm
              have hτ_other : ∀ x, x ≠ Fin.castSucc i → x ≠ Fin.succ i → x ≠ Fin.castSucc j → x ≠ Fin.succ j → τ x = x := by
                intro x hx1 hx2 hx3 hx4
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_of_ne_of_ne hx3 hx4, Equiv.swap_apply_of_ne_of_ne hx1 hx2]
              have hinv_τ : inv τ = {(Fin.castSucc i, Fin.succ i), (Fin.castSucc j, Fin.succ j)} := by
                ext ⟨x, y⟩
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                constructor
                · intro ⟨hxy, hgt⟩
                  by_cases hx_ci : x = Fin.castSucc i
                  · subst hx_ci
                    by_cases hy_si : y = Fin.succ i
                    · left; exact ⟨rfl, hy_si⟩
                    · by_cases hy_cj : y = Fin.castSucc j
                      · simp only [hτ_ci, hy_cj, hτ_cj] at hgt; omega
                      · by_cases hy_sj : y = Fin.succ j
                        · simp only [hτ_ci, hy_sj, hτ_sj] at hgt; omega
                        · have hy_ne_ci : y ≠ Fin.castSucc i := by intro h; simp only [h] at hxy; omega
                          have hτy : τ y = y := hτ_other y hy_ne_ci hy_si hy_cj hy_sj
                          simp only [hτ_ci, hτy] at hgt; omega
                  · by_cases hx_si : x = Fin.succ i
                    · subst hx_si; simp only [hτ_si] at hgt
                      by_cases hy_ci : y = Fin.castSucc i
                      · simp only [hy_ci] at hxy; omega
                      · by_cases hy_si : y = Fin.succ i
                        · simp only [hy_si] at hxy; omega
                        · by_cases hy_cj : y = Fin.castSucc j
                          · simp only [hy_cj, hτ_cj] at hgt; omega
                          · by_cases hy_sj : y = Fin.succ j
                            · simp only [hy_sj, hτ_sj] at hgt; omega
                            · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                              simp only [hτy] at hgt hxy; omega
                    · by_cases hx_cj : x = Fin.castSucc j
                      · subst hx_cj
                        by_cases hy_sj : y = Fin.succ j
                        · right; exact ⟨rfl, hy_sj⟩
                        · by_cases hy_ci : y = Fin.castSucc i
                          · simp only [hy_ci] at hxy; omega
                          · by_cases hy_si : y = Fin.succ i
                            · simp only [hy_si] at hxy; omega
                            · by_cases hy_cj : y = Fin.castSucc j
                              · simp only [hy_cj] at hxy; omega
                              · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                                simp only [hτ_cj, hτy] at hgt hxy; omega
                      · by_cases hx_sj : x = Fin.succ j
                        · subst hx_sj; simp only [hτ_sj] at hgt
                          by_cases hy_ci : y = Fin.castSucc i
                          · simp only [hy_ci] at hxy; omega
                          · by_cases hy_si : y = Fin.succ i
                            · simp only [hy_si] at hxy; omega
                            · by_cases hy_cj : y = Fin.castSucc j
                              · simp only [hy_cj] at hxy; omega
                              · by_cases hy_sj : y = Fin.succ j
                                · simp only [hy_sj] at hxy; omega
                                · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                                  simp only [hτy] at hgt hxy; omega
                        · have hτx : τ x = x := hτ_other x hx_ci hx_si hx_cj hx_sj
                          by_cases hy_ci : y = Fin.castSucc i
                          · simp only [hy_ci, hτx, hτ_ci] at hgt hxy; omega
                          · by_cases hy_si : y = Fin.succ i
                            · simp only [hy_si, hτx, hτ_si] at hgt hxy; omega
                            · by_cases hy_cj : y = Fin.castSucc j
                              · simp only [hy_cj, hτx, hτ_cj] at hgt hxy; omega
                              · by_cases hy_sj : y = Fin.succ j
                                · simp only [hy_sj, hτx, hτ_sj] at hgt hxy; omega
                                · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_cj hy_sj
                                  simp only [hτx, hτy] at hgt hxy; omega
                · intro h
                  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact ⟨h_ci_si, by simp only [hτ_ci, hτ_si]; omega⟩
                  · exact ⟨h_cj_sj, by simp only [hτ_cj, hτ_sj]; omega⟩
              apply perm_eq_of_inv_eq
              -- inv σ = {(a,b), (c,d)} = {(cj, sj), (ci, si)}
              rw [hinv_eq]
              have hswap : ({(a, b), (c, d)} : Finset _) = {(c, d), (a, b)} := by
                ext; simp [Finset.mem_insert, Finset.mem_singleton, or_comm]
              rw [hswap, hc_eq_ci, hd_eq_si, ha_eq_cj, hb_eq_sj, hinv_τ]
        · -- At least one has gap > 1: use two_inv_gap_constraint
          push Not at hboth_gap1
          by_cases hab_gap1 : b.val = a.val + 1
          · -- (a,b) has gap 1, (c,d) has gap > 1
            have hcd_gap : d.val > c.val + 1 := by omega
            have hne' : (c, d) ≠ (a, b) := hne.symm
            have hinv_eq' : inv σ = {(c, d), (a, b)} := by
              rw [hinv_eq]; ext; simp [Finset.mem_insert, Finset.mem_singleton, or_comm]
            rcases two_inv_gap_constraint σ c d a b hne' hinv_eq' hcd_lt hcd_gap with ⟨ha_eq_c, hcd', hdb⟩ | ⟨hb_eq_d, hca, hab'⟩
            · -- a = c: Type B (share first endpoint)
              right
              subst ha_eq_c
              -- After subst: inv σ = {(a, d), (a, b)} where b = a + 1 and b < d
              -- Need to show d = a + 2, then construct Type B witness
              have hd_eq : d.val = a.val + 2 := by
                by_contra hd_ne
                have hd_gt : d.val > a.val + 2 := by omega
                have he_bound : a.val + 2 < m + 2 := Nat.lt_trans hd_gt d.isLt
                set e : Fin (m + 2) := ⟨a.val + 2, he_bound⟩ with he_def
                have hae : a < e := by simp only [he_def, Fin.lt_def]; omega
                have hed : e < d := by simp only [he_def, Fin.lt_def]; omega
                have hae_not_inv : (a, e) ∉ inv σ := by
                  rw [hinv_eq']
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  intro h
                  rcases h with ⟨_, he_eq_d⟩ | ⟨_, he_eq_b⟩
                  · simp only [he_def, Fin.ext_iff] at he_eq_d; omega
                  · simp only [he_def, Fin.ext_iff] at he_eq_b; omega
                have hed_not_inv : (e, d) ∉ inv σ := by
                  rw [hinv_eq']
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  intro h
                  rcases h with ⟨he_eq_a, _⟩ | ⟨he_eq_a, _⟩
                  · simp only [he_def, Fin.ext_iff] at he_eq_a; omega
                  · simp only [he_def, Fin.ext_iff] at he_eq_a; omega
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hae_not_inv hed_not_inv
                have h1 : σ a ≤ σ e := hae_not_inv hae
                have h3 : σ e ≤ σ d := hed_not_inv hed
                exact not_lt.mpr (le_trans h1 h3) hcd_gt
              have ha_bound : a.val < m := by have := d.isLt; omega
              use ⟨a.val, ha_bound⟩
              apply perm_eq_of_inv_eq
              -- Set up correspondences
              set i : Fin m := ⟨a.val, ha_bound⟩
              set i0 : Fin (m + 1) := ⟨i.val, Nat.lt_add_right 1 i.isLt⟩
              set i1 : Fin (m + 1) := ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩
              have ha_eq_ci0 : a = Fin.castSucc i0 := by ext; simp [i, i0]
              have hb_eq_si0 : b = Fin.succ i0 := by ext; simp [i, i0, hab_gap1]
              have hd_eq_si1 : d = Fin.succ i1 := by ext; simp [i, i1, hd_eq]
              rw [hinv_eq', ha_eq_ci0, hb_eq_si0, hd_eq_si1]
              -- Type B inversions: {(ci0, si0), (ci0, si1)}
              have h_si_eq_ci1 : Fin.succ i0 = Fin.castSucc i1 := by
                simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, i0, i1]
              have h_ci_si : Fin.castSucc i0 < Fin.succ i0 := Fin.castSucc_lt_succ
              have h_ci_si1 : Fin.castSucc i0 < Fin.succ i1 := by
                simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, i0, i1]; omega
              have h_ci_ne_si : Fin.castSucc i0 ≠ Fin.succ i0 := ne_of_lt h_ci_si
              have h_ci_ne_ci1 : Fin.castSucc i0 ≠ Fin.castSucc i1 := by rw [← h_si_eq_ci1]; exact h_ci_ne_si
              have h_ci_ne_si1 : Fin.castSucc i0 ≠ Fin.succ i1 := by
                intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, i0, i1] at h; omega
              have h_si_ne_si1 : Fin.succ i0 ≠ Fin.succ i1 := by
                intro h; simp only [Fin.ext_iff, Fin.val_succ, i0, i1] at h; omega
              set τ := Equiv.swap (Fin.castSucc i1) (Fin.succ i1) * Equiv.swap (Fin.castSucc i0) (Fin.succ i0)
              have hτ_ci : τ (Fin.castSucc i0) = Fin.succ i1 := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_left, h_si_eq_ci1, Equiv.swap_apply_left]
              have hτ_si : τ (Fin.succ i0) = Fin.castSucc i0 := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_right]
                exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_ci1 h_ci_ne_si1
              have hτ_si1 : τ (Fin.succ i1) = Fin.succ i0 := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_of_ne_of_ne h_ci_ne_si1.symm h_si_ne_si1.symm]
                rw [Equiv.swap_apply_right, ← h_si_eq_ci1]
              have hτ_other : ∀ x, x ≠ Fin.castSucc i0 → x ≠ Fin.succ i0 → x ≠ Fin.succ i1 → τ x = x := by
                intro x hx1 hx2 hx3
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                have hx2' : x ≠ Fin.castSucc i1 := h_si_eq_ci1 ▸ hx2
                rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2, Equiv.swap_apply_of_ne_of_ne hx2' hx3]
              have hinv_τ : inv τ = {(Fin.castSucc i0, Fin.succ i0), (Fin.castSucc i0, Fin.succ i1)} := by
                ext ⟨x, y⟩
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                constructor
                · intro ⟨hxy, hgt⟩
                  by_cases hx_ci : x = Fin.castSucc i0
                  · subst hx_ci
                    by_cases hy_si : y = Fin.succ i0
                    · left; exact ⟨rfl, hy_si⟩
                    · by_cases hy_si1 : y = Fin.succ i1
                      · right; exact ⟨rfl, hy_si1⟩
                      · have hy_ne_ci : y ≠ Fin.castSucc i0 := by intro h; simp only [h] at hxy; omega
                        have hτy : τ y = y := hτ_other y hy_ne_ci hy_si hy_si1
                        simp only [hτ_ci, hτy] at hgt; omega
                  · by_cases hx_si : x = Fin.succ i0
                    · subst hx_si; simp only [hτ_si] at hgt
                      by_cases hy_ci : y = Fin.castSucc i0
                      · simp only [hy_ci] at hxy; omega
                      · by_cases hy_si : y = Fin.succ i0
                        · simp only [hy_si] at hxy; omega
                        · by_cases hy_si1 : y = Fin.succ i1
                          · simp only [hy_si1, hτ_si1] at hgt; omega
                          · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_si1
                            simp only [hτy] at hgt hxy; omega
                    · by_cases hx_si1 : x = Fin.succ i1
                      · subst hx_si1; simp only [hτ_si1] at hgt
                        by_cases hy_ci : y = Fin.castSucc i0
                        · simp only [hy_ci] at hxy; omega
                        · by_cases hy_si : y = Fin.succ i0
                          · simp only [hy_si] at hxy; omega
                          · by_cases hy_si1 : y = Fin.succ i1
                            · simp only [hy_si1] at hxy; omega
                            · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_si1
                              simp only [hτy] at hgt hxy; omega
                      · have hτx : τ x = x := hτ_other x hx_ci hx_si hx_si1
                        by_cases hy_ci : y = Fin.castSucc i0
                        · simp only [hy_ci, hτx, hτ_ci] at hgt hxy; omega
                        · by_cases hy_si : y = Fin.succ i0
                          · simp only [hy_si, hτx, hτ_si] at hgt hxy; omega
                          · by_cases hy_si1 : y = Fin.succ i1
                            · simp only [hy_si1, hτx, hτ_si1] at hgt hxy; omega
                            · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_si1
                              simp only [hτx, hτy] at hgt hxy; omega
                · intro h
                  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact ⟨h_ci_si, by simp only [hτ_ci, hτ_si]; omega⟩
                  · exact ⟨h_ci_si1, by simp only [hτ_ci, hτ_si1]; omega⟩
              rw [hinv_τ]
              ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
            · -- b = d: Type A adjacent (share second endpoint)
              left
              subst hb_eq_d
              -- Now inv σ = {(c, b), (a, b)} with c < a < b and b.val = a.val + 1
              -- First prove c.val = a.val - 1
              have hc_eq : c.val = a.val - 1 := by
                by_contra hc_ne
                have hc_lt : c.val < a.val - 1 := by have : c.val < a.val := hca; omega
                have he_bound : c.val + 1 < m + 2 := by have := a.isLt; omega
                set e : Fin (m + 2) := ⟨c.val + 1, he_bound⟩ with he_def
                have hce : c < e := by simp only [he_def, Fin.lt_def]; omega
                have hea : e < a := by simp only [he_def, Fin.lt_def]; omega
                have heb : e < b := lt_trans hea hab'
                have hcb_inv : (c, b) ∈ inv σ := by rw [hinv_eq']; simp
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and] at hcb_inv
                obtain ⟨_, hcb_gt⟩ := hcb_inv
                by_cases hce_inv : σ c > σ e
                · have hce_mem : (c, e) ∈ inv σ := by
                    simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hce, hce_inv⟩
                  rw [hinv_eq'] at hce_mem
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hce_mem
                  rcases hce_mem with ⟨_, he_eq_b⟩ | ⟨_, he_eq_b⟩
                  · simp only [he_def, Fin.ext_iff] at he_eq_b; omega
                  · simp only [he_def, Fin.ext_iff] at he_eq_b; omega
                · push Not at hce_inv
                  by_cases heb_inv : σ e > σ b
                  · have heb_mem : (e, b) ∈ inv σ := by
                      simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨heb, heb_inv⟩
                    rw [hinv_eq'] at heb_mem
                    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at heb_mem
                    rcases heb_mem with ⟨he_eq_c, _⟩ | ⟨he_eq_a, _⟩
                    · simp only [he_def, Fin.ext_iff] at he_eq_c; omega
                    · simp only [he_def, Fin.ext_iff] at he_eq_a; omega
                  · push Not at heb_inv
                    exact not_lt.mpr (le_trans hce_inv heb_inv) hcb_gt
              -- Construct Type A adjacent witness
              have ha_bound : a.val < m + 1 := by have := b.isLt; omega
              have hc_bound : c.val < m + 1 := by omega
              use ⟨c.val, hc_bound⟩, ⟨a.val, ha_bound⟩
              constructor
              · exact hca
              · set i : Fin (m + 1) := ⟨c.val, hc_bound⟩
                set j : Fin (m + 1) := ⟨a.val, ha_bound⟩
                have h_si_eq_cj : Fin.succ i = Fin.castSucc j := by
                  simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, i, j, hc_eq]; omega
                have hb_eq_sj : b = Fin.succ j := by simp only [Fin.ext_iff, Fin.val_succ, j, hab_gap1]
                have hc_eq_ci : c = Fin.castSucc i := by simp only [Fin.ext_iff, Fin.val_castSucc, i]
                have ha_eq_si : a = Fin.succ i := by rw [h_si_eq_cj]; simp only [Fin.ext_iff, Fin.val_castSucc, j]
                have h_ci_sj : Fin.castSucc i < Fin.succ j := by
                  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, i, j]; omega
                have h_si_sj : Fin.succ i < Fin.succ j := by
                  simp only [Fin.lt_def, Fin.val_succ, i, j, hc_eq]; omega
                have h_ci_ne_cj : Fin.castSucc i ≠ Fin.castSucc j := by
                  intro h; simp only [Fin.ext_iff, Fin.val_castSucc, i, j] at h; omega
                have h_ci_ne_sj : Fin.castSucc i ≠ Fin.succ j := by
                  intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, i, j] at h; omega
                have h_si_ne_sj : Fin.succ i ≠ Fin.succ j := by
                  intro h; simp only [Fin.ext_iff, Fin.val_succ, i, j, hc_eq] at h; omega
                have h_cj_ne_sj : Fin.castSucc j ≠ Fin.succ j := by
                  intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, j] at h; omega
                set τ := Equiv.swap (Fin.castSucc i) (Fin.succ i) * Equiv.swap (Fin.castSucc j) (Fin.succ j)
                have hτ_ci : τ (Fin.castSucc i) = Fin.succ i := by
                  simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                  rw [Equiv.swap_apply_of_ne_of_ne h_ci_ne_cj h_ci_ne_sj, Equiv.swap_apply_left]
                have hτ_si : τ (Fin.succ i) = Fin.succ j := by
                  simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                  rw [h_si_eq_cj, Equiv.swap_apply_left]
                  exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_sj.symm h_cj_ne_sj.symm
                have hτ_sj : τ (Fin.succ j) = Fin.castSucc i := by
                  simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                  rw [Equiv.swap_apply_right, ← h_si_eq_cj, Equiv.swap_apply_right]
                have hτ_other : ∀ x, x ≠ Fin.castSucc i → x ≠ Fin.succ i → x ≠ Fin.succ j → τ x = x := by
                  intro x hx1 hx2 hx3
                  simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                  have hx2' : x ≠ Fin.castSucc j := h_si_eq_cj ▸ hx2
                  rw [Equiv.swap_apply_of_ne_of_ne hx2' hx3, Equiv.swap_apply_of_ne_of_ne hx1 hx2]
                have hinv_τ : inv τ = {(Fin.castSucc i, Fin.succ j), (Fin.succ i, Fin.succ j)} := by
                  ext ⟨x, y⟩
                  simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  constructor
                  · intro ⟨hxy, hgt⟩
                    by_cases hx_ci : x = Fin.castSucc i
                    · subst hx_ci
                      by_cases hy_si : y = Fin.succ i
                      · simp only [hτ_ci, hy_si, hτ_si] at hgt; omega
                      · by_cases hy_sj : y = Fin.succ j
                        · left; exact ⟨rfl, hy_sj⟩
                        · have hy_ne_ci : y ≠ Fin.castSucc i := by intro h; simp only [h] at hxy; omega
                          have hτy : τ y = y := hτ_other y hy_ne_ci hy_si hy_sj
                          simp only [hτ_ci, hτy] at hgt; omega
                    · by_cases hx_si : x = Fin.succ i
                      · subst hx_si; simp only [hτ_si] at hgt
                        by_cases hy_ci : y = Fin.castSucc i
                        · simp only [hy_ci] at hxy; omega
                        · by_cases hy_si : y = Fin.succ i
                          · simp only [hy_si] at hxy; omega
                          · by_cases hy_sj : y = Fin.succ j
                            · right; exact ⟨rfl, hy_sj⟩
                            · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_sj
                              simp only [hτy] at hgt hxy; omega
                      · by_cases hx_sj : x = Fin.succ j
                        · subst hx_sj; simp only [hτ_sj] at hgt
                          by_cases hy_ci : y = Fin.castSucc i
                          · simp only [hy_ci] at hxy; omega
                          · by_cases hy_si : y = Fin.succ i
                            · simp only [hy_si] at hxy; omega
                            · by_cases hy_sj : y = Fin.succ j
                              · simp only [hy_sj] at hxy; omega
                              · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_sj
                                simp only [hτy] at hgt hxy; omega
                        · have hτx : τ x = x := hτ_other x hx_ci hx_si hx_sj
                          by_cases hy_ci : y = Fin.castSucc i
                          · simp only [hy_ci, hτx, hτ_ci] at hgt hxy; omega
                          · by_cases hy_si : y = Fin.succ i
                            · simp only [hy_si, hτx, hτ_si] at hgt hxy; omega
                            · by_cases hy_sj : y = Fin.succ j
                              · simp only [hy_sj, hτx, hτ_sj] at hgt hxy; omega
                              · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_sj
                                simp only [hτx, hτy] at hgt hxy; omega
                  · intro h
                    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact ⟨h_ci_sj, by simp only [hτ_ci, hτ_sj]; omega⟩
                    · exact ⟨h_si_sj, by simp only [hτ_si, hτ_sj]; omega⟩
                apply perm_eq_of_inv_eq
                rw [hinv_eq', hc_eq_ci, hb_eq_sj, ha_eq_si, hinv_τ]
          · -- (a,b) has gap > 1
            have hab_gap : b.val > a.val + 1 := by omega
            rcases two_inv_gap_constraint σ a b c d hne hinv_eq hab_lt hab_gap with ⟨hc_eq_a, had, hdb⟩ | ⟨hd_eq_b, hac, hcb⟩
            · -- c = a: Type B
              right
              subst hc_eq_a
              -- After subst: inv σ = {(c, b), (c, d)} where c < d < b and b.val > c.val + 1
              -- Note: after subst, `a` is replaced by `c` in hinv_eq, hab_lt, hab_gt, hab_gap
              -- Prove d.val = c.val + 1
              have hd_eq : d.val = c.val + 1 := by
                by_contra hd_ne
                have hd_gt : d.val > c.val + 1 := by omega
                have he_bound : c.val + 1 < m + 2 := by omega
                set e : Fin (m + 2) := ⟨c.val + 1, he_bound⟩ with he_def
                have hce : c < e := by simp only [he_def, Fin.lt_def]; omega
                have hed : e < d := by simp only [he_def, Fin.lt_def]; omega
                have hce_not_inv : (c, e) ∉ inv σ := by
                  rw [hinv_eq]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  intro h
                  rcases h with ⟨_, he_eq_b⟩ | ⟨_, he_eq_d⟩
                  · simp only [he_def, Fin.ext_iff] at he_eq_b; omega
                  · simp only [he_def, Fin.ext_iff] at he_eq_d; omega
                have hed_not_inv : (e, d) ∉ inv σ := by
                  rw [hinv_eq]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  intro h
                  rcases h with ⟨he_eq_c, _⟩ | ⟨he_eq_c, _⟩
                  · simp only [he_def, Fin.ext_iff] at he_eq_c; omega
                  · simp only [he_def, Fin.ext_iff] at he_eq_c; omega
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hce_not_inv hed_not_inv
                have h1 : σ c ≤ σ e := hce_not_inv hce
                have h3 : σ e ≤ σ d := hed_not_inv hed
                have hcd_inv : (c, d) ∈ inv σ := by rw [hinv_eq]; simp
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and] at hcd_inv
                exact not_lt.mpr (le_trans h1 h3) hcd_inv.2
              -- Prove b.val = c.val + 2
              have hb_eq : b.val = c.val + 2 := by
                by_contra hb_ne
                have hb_gt' : b.val > c.val + 2 := by omega
                have he_bound : c.val + 2 < m + 2 := by omega
                set e : Fin (m + 2) := ⟨c.val + 2, he_bound⟩ with he_def
                have hce : c < e := by simp only [he_def, Fin.lt_def]; omega
                have hde : d < e := by simp only [he_def, Fin.lt_def, hd_eq]; omega
                have heb : e < b := by simp only [he_def, Fin.lt_def]; omega
                have hce_not_inv : (c, e) ∉ inv σ := by
                  rw [hinv_eq]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  intro h
                  rcases h with ⟨_, he_eq_b⟩ | ⟨_, he_eq_d⟩
                  · simp only [he_def, Fin.ext_iff] at he_eq_b; omega
                  · simp only [he_def, Fin.ext_iff, hd_eq] at he_eq_d; omega
                have heb_not_inv : (e, b) ∉ inv σ := by
                  rw [hinv_eq]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  intro h
                  rcases h with ⟨he_eq_c, _⟩ | ⟨he_eq_c, _⟩
                  · simp only [he_def, Fin.ext_iff] at he_eq_c; omega
                  · simp only [he_def, Fin.ext_iff] at he_eq_c; omega
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hce_not_inv heb_not_inv
                have h1 : σ c ≤ σ e := hce_not_inv hce
                have h3 : σ e ≤ σ b := heb_not_inv heb
                exact not_lt.mpr (le_trans h1 h3) hab_gt
              -- Construct the Type B witness
              have hc_bound : c.val < m := by omega
              use ⟨c.val, hc_bound⟩
              apply perm_eq_of_inv_eq
              -- Set up correspondences
              set i : Fin m := ⟨c.val, hc_bound⟩
              set i0 : Fin (m + 1) := ⟨i.val, Nat.lt_add_right 1 i.isLt⟩
              set i1 : Fin (m + 1) := ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩
              have hc_eq_ci0 : c = Fin.castSucc i0 := by ext; simp [i, i0]
              have hd_eq_si0 : d = Fin.succ i0 := by ext; simp [i, i0, hd_eq]
              have hb_eq_si1 : b = Fin.succ i1 := by ext; simp [i, i1, hb_eq]
              rw [hinv_eq, hc_eq_ci0, hd_eq_si0, hb_eq_si1]
              -- Type B inversions: {(ci0, si1), (ci0, si0)}
              have h_si_eq_ci1 : Fin.succ i0 = Fin.castSucc i1 := by
                simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, i0, i1]
              have h_ci_si : Fin.castSucc i0 < Fin.succ i0 := Fin.castSucc_lt_succ
              have h_ci_si1 : Fin.castSucc i0 < Fin.succ i1 := by
                simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, i0, i1]; omega
              have h_ci_ne_si : Fin.castSucc i0 ≠ Fin.succ i0 := ne_of_lt h_ci_si
              have h_ci_ne_ci1 : Fin.castSucc i0 ≠ Fin.castSucc i1 := by rw [← h_si_eq_ci1]; exact h_ci_ne_si
              have h_ci_ne_si1 : Fin.castSucc i0 ≠ Fin.succ i1 := by
                intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, i0, i1] at h; omega
              have h_si_ne_si1 : Fin.succ i0 ≠ Fin.succ i1 := by
                intro h; simp only [Fin.ext_iff, Fin.val_succ, i0, i1] at h; omega
              set τ := Equiv.swap (Fin.castSucc i1) (Fin.succ i1) * Equiv.swap (Fin.castSucc i0) (Fin.succ i0)
              have hτ_ci : τ (Fin.castSucc i0) = Fin.succ i1 := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_left, h_si_eq_ci1, Equiv.swap_apply_left]
              have hτ_si : τ (Fin.succ i0) = Fin.castSucc i0 := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_right]
                exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_ci1 h_ci_ne_si1
              have hτ_si1 : τ (Fin.succ i1) = Fin.succ i0 := by
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                rw [Equiv.swap_apply_of_ne_of_ne h_ci_ne_si1.symm h_si_ne_si1.symm]
                rw [Equiv.swap_apply_right, ← h_si_eq_ci1]
              have hτ_other : ∀ x, x ≠ Fin.castSucc i0 → x ≠ Fin.succ i0 → x ≠ Fin.succ i1 → τ x = x := by
                intro x hx1 hx2 hx3
                simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                have hx2' : x ≠ Fin.castSucc i1 := h_si_eq_ci1 ▸ hx2
                rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2, Equiv.swap_apply_of_ne_of_ne hx2' hx3]
              have hinv_τ : inv τ = {(Fin.castSucc i0, Fin.succ i0), (Fin.castSucc i0, Fin.succ i1)} := by
                ext ⟨x, y⟩
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                constructor
                · intro ⟨hxy, hgt⟩
                  by_cases hx_ci : x = Fin.castSucc i0
                  · subst hx_ci
                    by_cases hy_si : y = Fin.succ i0
                    · left; exact ⟨rfl, hy_si⟩
                    · by_cases hy_si1 : y = Fin.succ i1
                      · right; exact ⟨rfl, hy_si1⟩
                      · have hy_ne_ci : y ≠ Fin.castSucc i0 := by intro h; simp only [h] at hxy; omega
                        have hτy : τ y = y := hτ_other y hy_ne_ci hy_si hy_si1
                        simp only [hτ_ci, hτy] at hgt; omega
                  · by_cases hx_si : x = Fin.succ i0
                    · subst hx_si; simp only [hτ_si] at hgt
                      by_cases hy_ci : y = Fin.castSucc i0
                      · simp only [hy_ci] at hxy; omega
                      · by_cases hy_si : y = Fin.succ i0
                        · simp only [hy_si] at hxy; omega
                        · by_cases hy_si1 : y = Fin.succ i1
                          · simp only [hy_si1, hτ_si1] at hgt; omega
                          · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_si1
                            simp only [hτy] at hgt hxy; omega
                    · by_cases hx_si1 : x = Fin.succ i1
                      · subst hx_si1; simp only [hτ_si1] at hgt
                        by_cases hy_ci : y = Fin.castSucc i0
                        · simp only [hy_ci] at hxy; omega
                        · by_cases hy_si : y = Fin.succ i0
                          · simp only [hy_si] at hxy; omega
                          · by_cases hy_si1 : y = Fin.succ i1
                            · simp only [hy_si1] at hxy; omega
                            · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_si1
                              simp only [hτy] at hgt hxy; omega
                      · have hτx : τ x = x := hτ_other x hx_ci hx_si hx_si1
                        by_cases hy_ci : y = Fin.castSucc i0
                        · simp only [hy_ci, hτx, hτ_ci] at hgt hxy; omega
                        · by_cases hy_si : y = Fin.succ i0
                          · simp only [hy_si, hτx, hτ_si] at hgt hxy; omega
                          · by_cases hy_si1 : y = Fin.succ i1
                            · simp only [hy_si1, hτx, hτ_si1] at hgt hxy; omega
                            · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_si1
                              simp only [hτx, hτy] at hgt hxy; omega
                · intro h
                  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact ⟨h_ci_si, by simp only [hτ_ci, hτ_si]; omega⟩
                  · exact ⟨h_ci_si1, by simp only [hτ_ci, hτ_si1]; omega⟩
              rw [hinv_τ]
              ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
            · -- d = b: Type A adjacent
              left
              subst hd_eq_b
              -- After subst: inv σ = {(a, d), (c, d)} where a < c < d and d.val > a.val + 1
              -- Note: after subst, `b` is replaced by `d` in hinv_eq, hab_lt, hab_gt, hab_gap
              -- Prove c.val = a.val + 1
              have hc_eq : c.val = a.val + 1 := by
                by_contra hc_ne
                have hc_gt : c.val > a.val + 1 := by omega
                have he_bound : a.val + 1 < m + 2 := by omega
                set e : Fin (m + 2) := ⟨a.val + 1, he_bound⟩ with he_def
                have hae : a < e := by simp only [he_def, Fin.lt_def]; omega
                have hec : e < c := by simp only [he_def, Fin.lt_def]; omega
                have hed : e < d := lt_trans hec hcb
                have hae_not_inv : (a, e) ∉ inv σ := by
                  rw [hinv_eq]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  intro h
                  rcases h with ⟨_, he_eq_d⟩ | ⟨ha_eq_c, _⟩
                  · simp only [he_def, Fin.ext_iff] at he_eq_d; omega
                  · simp only [Fin.ext_iff] at ha_eq_c; omega
                have hed_not_inv : (e, d) ∉ inv σ := by
                  rw [hinv_eq]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  intro h
                  rcases h with ⟨he_eq_a, _⟩ | ⟨he_eq_c, _⟩
                  · simp only [he_def, Fin.ext_iff] at he_eq_a; omega
                  · simp only [he_def, Fin.ext_iff] at he_eq_c; omega
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hae_not_inv hed_not_inv
                have h1 : σ a ≤ σ e := hae_not_inv hae
                have h3 : σ e ≤ σ d := hed_not_inv hed
                exact not_lt.mpr (le_trans h1 h3) hab_gt
              -- Prove d.val = a.val + 2
              have hd_eq : d.val = a.val + 2 := by
                by_contra hd_ne
                have hd_gt' : d.val > a.val + 2 := by omega
                have he_bound : a.val + 2 < m + 2 := by omega
                set e : Fin (m + 2) := ⟨a.val + 2, he_bound⟩ with he_def
                have hce : c < e := by simp only [he_def, Fin.lt_def, hc_eq]; omega
                have hed : e < d := by simp only [he_def, Fin.lt_def]; omega
                have hce_not_inv : (c, e) ∉ inv σ := by
                  rw [hinv_eq]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  intro h
                  rcases h with ⟨hc_eq_a, _⟩ | ⟨_, he_eq_d⟩
                  · simp only [Fin.ext_iff, hc_eq] at hc_eq_a; omega
                  · simp only [he_def, Fin.ext_iff] at he_eq_d; omega
                have hed_not_inv : (e, d) ∉ inv σ := by
                  rw [hinv_eq]
                  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  intro h
                  rcases h with ⟨he_eq_a, _⟩ | ⟨he_eq_c, _⟩
                  · simp only [he_def, Fin.ext_iff] at he_eq_a; omega
                  · simp only [he_def, Fin.ext_iff, hc_eq] at he_eq_c; omega
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hce_not_inv hed_not_inv
                have h1 : σ c ≤ σ e := hce_not_inv hce
                have h3 : σ e ≤ σ d := hed_not_inv hed
                have hcd_inv : (c, d) ∈ inv σ := by rw [hinv_eq]; simp
                simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and] at hcd_inv
                exact not_lt.mpr (le_trans h1 h3) hcd_inv.2
              -- Construct the Type A adjacent witness
              have ha_bound : a.val < m + 1 := by omega
              have hc_bound : c.val < m + 1 := by omega
              use ⟨a.val, ha_bound⟩, ⟨c.val, hc_bound⟩
              constructor
              · exact hac
              · apply perm_eq_of_inv_eq
                -- Set up correspondences
                set i : Fin (m + 1) := ⟨a.val, ha_bound⟩
                set j : Fin (m + 1) := ⟨c.val, hc_bound⟩
                have h_si_eq_cj : Fin.succ i = Fin.castSucc j := by
                  simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, i, j, hc_eq]
                have ha_eq_ci : a = Fin.castSucc i := by ext; simp [i]
                have hc_eq_sj_cast : c = Fin.succ i := by ext; simp [i, hc_eq]
                have hd_eq_sj : d = Fin.succ j := by ext; simp [j, hd_eq, hc_eq]
                rw [hinv_eq, ha_eq_ci, hc_eq_sj_cast, hd_eq_sj]
                -- Type A inversions: {(ci, sj), (si, sj)}
                have h_ci_sj : Fin.castSucc i < Fin.succ j := by
                  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, i, j]; omega
                have h_si_sj : Fin.succ i < Fin.succ j := by
                  simp only [Fin.lt_def, Fin.val_succ, i, j, hc_eq]; omega
                have h_ci_ne_cj : Fin.castSucc i ≠ Fin.castSucc j := by
                  intro h; simp only [Fin.ext_iff, Fin.val_castSucc, i, j] at h; omega
                have h_ci_ne_sj : Fin.castSucc i ≠ Fin.succ j := by
                  intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, i, j] at h; omega
                have h_si_ne_sj : Fin.succ i ≠ Fin.succ j := by
                  intro h; simp only [Fin.ext_iff, Fin.val_succ, i, j, hc_eq] at h; omega
                have h_cj_ne_sj : Fin.castSucc j ≠ Fin.succ j := by
                  intro h; simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, j] at h; omega
                set τ := Equiv.swap (Fin.castSucc i) (Fin.succ i) * Equiv.swap (Fin.castSucc j) (Fin.succ j)
                have hτ_ci : τ (Fin.castSucc i) = Fin.succ i := by
                  simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                  rw [Equiv.swap_apply_of_ne_of_ne h_ci_ne_cj h_ci_ne_sj, Equiv.swap_apply_left]
                have hτ_si : τ (Fin.succ i) = Fin.succ j := by
                  simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                  rw [h_si_eq_cj, Equiv.swap_apply_left]
                  exact Equiv.swap_apply_of_ne_of_ne h_ci_ne_sj.symm h_cj_ne_sj.symm
                have hτ_sj : τ (Fin.succ j) = Fin.castSucc i := by
                  simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                  rw [Equiv.swap_apply_right, ← h_si_eq_cj, Equiv.swap_apply_right]
                have hτ_other : ∀ x, x ≠ Fin.castSucc i → x ≠ Fin.succ i → x ≠ Fin.succ j → τ x = x := by
                  intro x hx1 hx2 hx3
                  simp only [τ, Equiv.Perm.coe_mul, Function.comp_apply]
                  have hx2' : x ≠ Fin.castSucc j := h_si_eq_cj ▸ hx2
                  rw [Equiv.swap_apply_of_ne_of_ne hx2' hx3, Equiv.swap_apply_of_ne_of_ne hx1 hx2]
                have hinv_τ : inv τ = {(Fin.castSucc i, Fin.succ j), (Fin.succ i, Fin.succ j)} := by
                  ext ⟨x, y⟩
                  simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
                  constructor
                  · intro ⟨hxy, hgt⟩
                    by_cases hx_ci : x = Fin.castSucc i
                    · subst hx_ci
                      by_cases hy_si : y = Fin.succ i
                      · simp only [hτ_ci, hy_si, hτ_si] at hgt; omega
                      · by_cases hy_sj : y = Fin.succ j
                        · left; exact ⟨rfl, hy_sj⟩
                        · have hy_ne_ci : y ≠ Fin.castSucc i := by intro h; simp only [h] at hxy; omega
                          have hτy : τ y = y := hτ_other y hy_ne_ci hy_si hy_sj
                          simp only [hτ_ci, hτy] at hgt; omega
                    · by_cases hx_si : x = Fin.succ i
                      · subst hx_si; simp only [hτ_si] at hgt
                        by_cases hy_ci : y = Fin.castSucc i
                        · simp only [hy_ci] at hxy; omega
                        · by_cases hy_si : y = Fin.succ i
                          · simp only [hy_si] at hxy; omega
                          · by_cases hy_sj : y = Fin.succ j
                            · right; exact ⟨rfl, hy_sj⟩
                            · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_sj
                              simp only [hτy] at hgt hxy; omega
                      · by_cases hx_sj : x = Fin.succ j
                        · subst hx_sj; simp only [hτ_sj] at hgt
                          by_cases hy_ci : y = Fin.castSucc i
                          · simp only [hy_ci] at hxy; omega
                          · by_cases hy_si : y = Fin.succ i
                            · simp only [hy_si] at hxy; omega
                            · by_cases hy_sj : y = Fin.succ j
                              · simp only [hy_sj] at hxy; omega
                              · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_sj
                                simp only [hτy] at hgt hxy; omega
                        · have hτx : τ x = x := hτ_other x hx_ci hx_si hx_sj
                          by_cases hy_ci : y = Fin.castSucc i
                          · simp only [hy_ci, hτx, hτ_ci] at hgt hxy; omega
                          · by_cases hy_si : y = Fin.succ i
                            · simp only [hy_si, hτx, hτ_si] at hgt hxy; omega
                            · by_cases hy_sj : y = Fin.succ j
                              · simp only [hy_sj, hτx, hτ_sj] at hgt hxy; omega
                              · have hτy : τ y = y := hτ_other y hy_ci hy_si hy_sj
                                simp only [hτx, hτy] at hgt hxy; omega
                  · intro h
                    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact ⟨h_ci_sj, by simp only [hτ_ci, hτ_sj]; omega⟩
                    · exact ⟨h_si_sj, by simp only [hτ_si, hτ_sj]; omega⟩
                rw [hinv_τ]
    -- Now prove the equality using the helpers
    apply Finset.Subset.antisymm
    · -- {σ : invCount σ = 2} ⊆ typeA ∪ typeB
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      simp only [Finset.mem_union]
      rcases invCount_two_classification σ hσ with ⟨i, j, hij, hσ_eq⟩ | ⟨i, hσ_eq⟩
      · left
        simp only [typeA, Finset.mem_image, Prod.exists]
        use i, j
        simp only [pairsLt, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hij, hσ_eq.symm⟩
      · right
        simp only [typeB, Finset.mem_image]
        use i
        simp only [Finset.mem_univ, true_and]
        exact hσ_eq.symm
    · -- typeA ∪ typeB ⊆ {σ : invCount σ = 2}
      intro σ hσ
      simp only [Finset.mem_union] at hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hσ with hA | hB
      · simp only [typeA, Finset.mem_image, Prod.exists] at hA
        obtain ⟨i, j, hij, hσ⟩ := hA
        simp only [pairsLt, Finset.mem_filter, Finset.mem_univ, true_and] at hij
        subst hσ
        exact invCount_typeA i j hij
      · simp only [typeB, Finset.mem_image] at hB
        obtain ⟨i, _, hσ⟩ := hB
        subst hσ
        exact invCount_typeB i
  have h_disjoint : Disjoint typeA typeB := by
    rw [Finset.disjoint_iff_ne]
    intro σA hσA σB hσB heq
    simp only [typeA, typeB, Finset.mem_image, Finset.mem_univ, true_and] at hσA hσB
    obtain ⟨⟨i, j⟩, hij, hσA_eq⟩ := hσA
    obtain ⟨k, hσB_eq⟩ := hσB
    simp only [pairsLt, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    subst hσA_eq hσB_eq
    have heq_fun := congrFun (congrArg DFunLike.coe heq)
    let x : Fin (m + 2) := ⟨k.val, Nat.lt_add_right 2 k.isLt⟩
    have hσB_x : (Equiv.swap (Fin.castSucc ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩)
                             (Fin.succ ⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩) *
                  Equiv.swap (Fin.castSucc ⟨k.val, Nat.lt_add_right 1 k.isLt⟩)
                             (Fin.succ ⟨k.val, Nat.lt_add_right 1 k.isLt⟩)) x =
                 ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩ := by
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, x]
      have h1 : (⟨k.val, Nat.lt_add_right 2 k.isLt⟩ : Fin (m + 2)) =
                Fin.castSucc (⟨k.val, Nat.lt_add_right 1 k.isLt⟩ : Fin (m + 1)) := by
        simp only [Fin.ext_iff, Fin.val_castSucc]
      rw [h1, Equiv.swap_apply_left]
      have h2 : Fin.succ (⟨k.val, Nat.lt_add_right 1 k.isLt⟩ : Fin (m + 1)) =
                Fin.castSucc (⟨k.val + 1, Nat.add_lt_add_right k.isLt 1⟩ : Fin (m + 1)) := by
        simp only [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
      rw [h2, Equiv.swap_apply_left]
      simp only [Fin.ext_iff, Fin.val_succ]
    have hσA_x : (Equiv.swap (Fin.castSucc i) (Fin.succ i) *
                 Equiv.swap (Fin.castSucc j) (Fin.succ j)) x ≠
                 ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩ := by
      intro heq'
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, x] at heq'
      by_cases hkj : k.val = j.val
      · have hx_eq_cj : (⟨k.val, Nat.lt_add_right 2 k.isLt⟩ : Fin (m + 2)) = Fin.castSucc j := by
          simp only [Fin.ext_iff, Fin.val_castSucc, hkj]
        rw [hx_eq_cj, Equiv.swap_apply_left] at heq'
        by_cases hji1 : j.val + 1 = i.val
        · omega
        · by_cases hji2 : j.val = i.val
          · omega
          · have hne1 : (Fin.succ j : Fin (m + 2)) ≠ Fin.castSucc i := by
              simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]; exact hji1
            have hne2 : (Fin.succ j : Fin (m + 2)) ≠ Fin.succ i := by
              simp only [ne_eq, Fin.ext_iff, Fin.val_succ]
              intro h; exact hji2 (by omega)
            rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2] at heq'
            simp only [Fin.ext_iff, Fin.val_succ] at heq'
            omega
      · by_cases hkj' : k.val = j.val + 1
        · have hx_eq_sj : (⟨k.val, Nat.lt_add_right 2 k.isLt⟩ : Fin (m + 2)) = Fin.succ j := by
            simp only [Fin.ext_iff, Fin.val_succ, hkj']
          rw [hx_eq_sj, Equiv.swap_apply_right] at heq'
          by_cases hji1 : j.val = i.val
          · omega
          · by_cases hji2 : j.val = i.val + 1
            · have hcj_eq_si : (Fin.castSucc j : Fin (m + 2)) = Fin.succ i := by
                simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, hji2]
              rw [hcj_eq_si, Equiv.swap_apply_right] at heq'
              simp only [Fin.ext_iff, Fin.val_castSucc] at heq'
              omega
            · have hne1 : (Fin.castSucc j : Fin (m + 2)) ≠ Fin.castSucc i := by
                simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; exact hji1
              have hne2 : (Fin.castSucc j : Fin (m + 2)) ≠ Fin.succ i := by
                simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
                intro h; omega
              rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2] at heq'
              simp only [Fin.ext_iff, Fin.val_castSucc] at heq'
              omega
        · have hne1 : (⟨k.val, Nat.lt_add_right 2 k.isLt⟩ : Fin (m + 2)) ≠ Fin.castSucc j := by
            simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; exact hkj
          have hne2 : (⟨k.val, Nat.lt_add_right 2 k.isLt⟩ : Fin (m + 2)) ≠ Fin.succ j := by
            simp only [ne_eq, Fin.ext_iff, Fin.val_succ]; exact hkj'
          rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2] at heq'
          by_cases hki : k.val = i.val
          · have hx_eq_ci : (⟨k.val, Nat.lt_add_right 2 k.isLt⟩ : Fin (m + 2)) = Fin.castSucc i := by
              simp only [Fin.ext_iff, Fin.val_castSucc, hki]
            rw [hx_eq_ci, Equiv.swap_apply_left] at heq'
            simp only [Fin.ext_iff, Fin.val_succ] at heq'
            omega
          · by_cases hki' : k.val = i.val + 1
            · have hx_eq_si : (⟨k.val, Nat.lt_add_right 2 k.isLt⟩ : Fin (m + 2)) = Fin.succ i := by
                simp only [Fin.ext_iff, Fin.val_succ, hki']
              rw [hx_eq_si, Equiv.swap_apply_right] at heq'
              simp only [Fin.ext_iff, Fin.val_castSucc] at heq'
              omega
            · have hne3 : (⟨k.val, Nat.lt_add_right 2 k.isLt⟩ : Fin (m + 2)) ≠ Fin.castSucc i := by
                simp only [ne_eq, Fin.ext_iff, Fin.val_castSucc]; exact hki
              have hne4 : (⟨k.val, Nat.lt_add_right 2 k.isLt⟩ : Fin (m + 2)) ≠ Fin.succ i := by
                simp only [ne_eq, Fin.ext_iff, Fin.val_succ]; exact hki'
              rw [Equiv.swap_apply_of_ne_of_ne hne3 hne4] at heq'
              simp only [Fin.ext_iff] at heq'
              omega
    have heq_at_x := heq_fun x
    rw [hσB_x] at heq_at_x
    exact hσA_x heq_at_x
  have h_cardA : typeA.card = (m + 1).choose 2 := by
    simp only [typeA]
    rw [Finset.card_image_of_injOn (typeA_injOn m)]
    exact card_pairsLt m
  have h_cardB : typeB.card = m := card_typeB_helper m
  rw [h_union, Finset.card_union_of_disjoint h_disjoint, h_cardA, h_cardB]
  exact formula_helper' m

/-! ### Helper lemmas for symmetry of length distribution -/

/--
The non-inversions of a permutation σ: pairs (i, j) with i < j and σ i < σ j.

This is the complement of `inv σ` within the set of ordered pairs.
The non-inversions are exactly the pairs where σ preserves the order.
-/
def nonInv (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.filter (fun p => p.1 < p.2 ∧ σ p.1 < σ p.2) Finset.univ

/-- The set of all pairs (i, j) with i < j -/
private def orderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.filter (fun p => p.1 < p.2) Finset.univ

/-- Inversions of w₀ * σ are exactly the non-inversions of σ -/
private lemma inv_longestElement_mul (σ : Equiv.Perm (Fin n)) :
    inv (longestElement n * σ) =
    Finset.filter (fun p => p.1 < p.2 ∧ σ p.1 < σ p.2) Finset.univ := by
  ext ⟨i, j⟩
  simp only [inv, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ⟨hij, hgt⟩
    refine ⟨hij, ?_⟩
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, longestElement, Equiv.coe_fn_mk,
               Fin.lt_def] at hgt ⊢
    omega
  · intro ⟨hij, hlt⟩
    refine ⟨hij, ?_⟩
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, longestElement, Equiv.coe_fn_mk,
               Fin.lt_def] at hlt ⊢
    omega

/-- inv and nonInv partition orderedPairs -/
private lemma inv_union_nonInv (σ : Equiv.Perm (Fin n)) :
    inv σ ∪ nonInv σ = orderedPairs n := by
  ext ⟨i, j⟩
  simp only [inv, nonInv, orderedPairs, Finset.mem_union, Finset.mem_filter,
             Finset.mem_univ, true_and]
  constructor
  · intro h
    cases h with
    | inl h => exact h.1
    | inr h => exact h.1
  · intro hij
    by_cases h : σ i > σ j
    · left; exact ⟨hij, h⟩
    · right
      push Not at h
      have hne : σ i ≠ σ j := σ.injective.ne (Fin.ne_of_lt hij)
      exact ⟨hij, lt_of_le_of_ne h hne⟩

private lemma inv_inter_nonInv (σ : Equiv.Perm (Fin n)) :
    inv σ ∩ nonInv σ = ∅ := by
  ext ⟨i, j⟩
  simp only [inv, nonInv, Finset.mem_inter, Finset.mem_filter,
             Finset.mem_univ, true_and]
  constructor
  · intro ⟨⟨_, hgt⟩, ⟨_, hlt⟩⟩
    exact (lt_irrefl _ (lt_trans hlt hgt)).elim
  · simp

/-- The number of ordered pairs is n choose 2 -/
private lemma card_orderedPairs : (orderedPairs n).card = n.choose 2 := by
  rw [orderedPairs]
  have h1 : 2 * (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ).card =
            (Finset.univ : Finset (Fin n)).offDiag.card := by
    have swap_bij : (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ).card =
                    (Finset.filter (fun p : Fin n × Fin n => p.1 > p.2) Finset.univ).card := by
      refine Finset.card_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro ⟨a, b⟩ hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hp
      · intro ⟨a, b⟩ hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hp
      · intro ⟨a, b⟩ _; rfl
      · intro ⟨a, b⟩ _; rfl
    have disjoint : Disjoint
        (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ)
        (Finset.filter (fun p : Fin n × Fin n => p.1 > p.2) Finset.univ) := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2
      exact (lt_irrefl _ (lt_trans h1 h2))
    have union : (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ) ∪
                 (Finset.filter (fun p : Fin n × Fin n => p.1 > p.2) Finset.univ) =
                 (Finset.univ : Finset (Fin n)).offDiag := by
      ext ⟨i, j⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_offDiag, ne_eq]
      constructor
      · intro h
        cases h with
        | inl h => exact Fin.ne_of_lt h
        | inr h => exact (Fin.ne_of_lt h).symm
      · intro h
        rcases lt_trichotomy i j with hlt | heq | hgt
        · left; exact hlt
        · exact absurd heq h
        · right; exact hgt
    calc 2 * (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ).card
        = (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ).card +
          (Finset.filter (fun p : Fin n × Fin n => p.1 > p.2) Finset.univ).card := by
          rw [swap_bij]; ring
      _ = ((Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ) ∪
           (Finset.filter (fun p : Fin n × Fin n => p.1 > p.2) Finset.univ)).card := by
          rw [Finset.card_union_of_disjoint disjoint]
      _ = (Finset.univ : Finset (Fin n)).offDiag.card := by rw [union]
  rw [Finset.offDiag_card, Finset.card_fin] at h1
  rw [Nat.choose_two_right]
  have h2 : n * n - n = n * (n - 1) := (Nat.mul_sub_one n n).symm
  rw [h2] at h1
  have h3 : n * (n - 1) = 2 * (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ).card := h1.symm
  exact (Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2) h3).symm

/-- invCount σ + card(nonInv σ) = n choose 2 -/
private lemma invCount_add_nonInv_card (σ : Equiv.Perm (Fin n)) :
    invCount σ + (nonInv σ).card = n.choose 2 := by
  have h1 := inv_union_nonInv σ
  have h2 := inv_inter_nonInv σ
  rw [← card_orderedPairs]
  rw [← h1]
  rw [Finset.card_union_of_disjoint]
  · rfl
  · rw [Finset.disjoint_iff_inter_eq_empty]
    exact h2

/--
The inversion count of `w₀ * σ` equals the number of non-inversions of `σ`.

This expresses a fundamental duality: multiplying by the longest element w₀
swaps inversions and non-inversions.
-/
theorem invCount_longestElement_mul (σ : Equiv.Perm (Fin n)) :
    invCount (longestElement n * σ) = (nonInv σ).card := by
  unfold invCount
  rw [inv_longestElement_mul]
  rfl

/--
The inversion count of `w₀ * σ` equals `n choose 2` minus the inversion count of `σ`.

This shows that multiplication by the longest element w₀ "complements" the length:
if σ has k inversions, then w₀ * σ has (n choose 2) - k inversions.
-/
@[simp]
theorem invCount_longestElement_mul' (σ : Equiv.Perm (Fin n)) :
    invCount (longestElement n * σ) = n.choose 2 - invCount σ := by
  rw [invCount_longestElement_mul]
  have h := invCount_add_nonInv_card σ
  omega

/--
The longest element w₀ is an involution: w₀ * w₀ = 1.

This follows from the fact that w₀ = Fin.revPerm and revPerm is an involution.
-/
@[simp]
theorem longestElement_mul_self : longestElement n * longestElement n = 1 := by
  ext i
  simp only [longestElement, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.coe_fn_mk,
             Equiv.Perm.coe_one, id_eq]
  omega

/--
The inverse of the longest element is itself: w₀⁻¹ = w₀.

This follows from `longestElement_mul_self`.
-/
@[simp]
theorem longestElement_inv : (longestElement n)⁻¹ = longestElement n := by
  have h := longestElement_mul_self (n := n)
  rw [← mul_right_inj (longestElement n)]
  simp only [mul_inv_cancel, h]

/--
Explicit computation of the longest element: w₀(i) = n - 1 - i.

This shows that w₀ reverses the order of elements.
-/
@[simp]
theorem longestElement_apply (i : Fin n) : longestElement n i = ⟨n - 1 - i.val, by omega⟩ := by
  simp only [longestElement, Equiv.coe_fn_mk]

/--
The number of σ ∈ S_n with ℓ(σ) = k equals the number with ℓ(σ) = (n choose 2) - k.
This is the symmetry of the length distribution.

See Proposition 1.3.3 (prop.perm.lengths-k-small-k) part (f) in the source.
-/
theorem card_invCount_symm (k : ℤ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => (invCount σ : ℤ) = k)).card =
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => (invCount σ : ℤ) = n.choose 2 - k)).card := by
  -- The bijection σ ↦ w₀ * σ maps permutations with invCount k to those with invCount (n choose 2) - k
  apply Finset.card_bij' (fun σ _ => longestElement n * σ) (fun σ _ => longestElement n * σ)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [invCount_longestElement_mul']
    have hle : invCount σ ≤ n.choose 2 := invCount_add_nonInv_card σ ▸ Nat.le_add_right _ _
    simp only [Int.ofNat_sub hle]
    omega
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [invCount_longestElement_mul']
    have hle : invCount σ ≤ n.choose 2 := invCount_add_nonInv_card σ ▸ Nat.le_add_right _ _
    simp only [Int.ofNat_sub hle]
    omega
  · intro σ _
    calc longestElement n * (longestElement n * σ)
        = (longestElement n * longestElement n) * σ := by group
      _ = 1 * σ := by rw [longestElement_mul_self]
      _ = σ := by rw [one_mul]
  · intro σ _
    calc longestElement n * (longestElement n * σ)
        = (longestElement n * longestElement n) * σ := by group
      _ = 1 * σ := by rw [longestElement_mul_self]
      _ = σ := by rw [one_mul]

/-! ### Lehmer codes -/

/-! #### The notation [m]_0 for {0, 1, ..., m}

See Definition 1.3.5 (def.perm.lehmer1) part (b) in the source.
-/

/--
For each m ∈ ℤ, we let [m]_0 denote the set {0, 1, ..., m}.
This is an empty set when m < 0.

See Definition 1.3.5 (def.perm.lehmer1) part (b) in the source.
-/
def Iic0 (m : ℤ) : Set ℕ := {n : ℕ | (n : ℤ) ≤ m}

/-- [m]_0 is empty when m < 0 -/
theorem Iic0_eq_empty_of_neg {m : ℤ} (hm : m < 0) : Iic0 m = ∅ := by
  ext n
  simp only [Iic0, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hn
  have : (n : ℤ) ≥ 0 := Int.natCast_nonneg n
  omega

/-- [m]_0 = {0, 1, ..., m} when m ≥ 0 -/
theorem Iic0_eq_Iic_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    Iic0 m = Set.Iic m.toNat := by
  ext n
  simp only [Iic0, Set.mem_ofPred_eq, Set.mem_Iic]
  constructor
  · intro hn
    have h : (n : ℤ).toNat ≤ m.toNat := Int.toNat_le_toNat hn
    simp only [Int.toNat_natCast] at h
    exact h
  · intro hn
    calc (n : ℤ) ≤ m.toNat := Int.ofNat_le.mpr hn
      _ = m := Int.toNat_of_nonneg hm

/-- The cardinality of [m]_0 is m + 1 when m ≥ 0 -/
theorem card_Iic0_of_nonneg {m : ℤ} (hm : 0 ≤ m) : (Iic0 m).ncard = m.toNat + 1 := by
  rw [Iic0_eq_Iic_of_nonneg hm]
  simp only [Set.ncard_Iic_nat]

/-- [m]_0 for natural numbers is just {0, 1, ..., m} -/
def Iic0Nat (m : ℕ) : Set ℕ := Set.Iic m

/-- [m]_0 for natural numbers equals the integer version -/
theorem Iic0Nat_eq_Iic0 (m : ℕ) : Iic0Nat m = Iic0 m := by
  ext n
  simp only [Iic0Nat, Set.mem_Iic, Iic0, Set.mem_ofPred_eq, Int.ofNat_le]

/-- The cardinality of [m]_0 for natural numbers is m + 1 -/
theorem card_Iic0Nat (m : ℕ) : (Iic0Nat m).ncard = m + 1 := by
  simp only [Iic0Nat, Set.ncard_Iic_nat]

/-- Membership characterization for [m]_0 -/
theorem mem_Iic0_iff {m : ℤ} {n : ℕ} : n ∈ Iic0 m ↔ (n : ℤ) ≤ m := by
  simp only [Iic0, Set.mem_ofPred_eq]

/-- Membership characterization for [m]_0 with natural numbers -/
theorem mem_Iic0Nat_iff {m n : ℕ} : n ∈ Iic0Nat m ↔ n ≤ m := by
  simp only [Iic0Nat, Set.mem_Iic]

end Perm

/-! #### Lehmer entry and Lehmer code definitions -/

namespace Perm

variable {n : ℕ}

/--
For σ ∈ S_n and i ∈ [n], we define ℓ_i(σ) as the number of j > i such that σ(i) > σ(j).
This counts how many elements to the right of position i are smaller than σ(i).

This is the canonical definition of Lehmer entry used throughout the project.
The equivalent formulation `i < j ∧ σ j < σ i` is provided by `lehmerEntry_eq_filter_lt`.

See Definition 1.3.5 (def.perm.lehmer1) part (a) in the source.
-/
def lehmerEntry (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  (Finset.filter (fun j : Fin n => i < j ∧ σ i > σ j) Finset.univ).card

/--
The Lehmer code of σ ∈ S_n is the n-tuple (ℓ_1(σ), ℓ_2(σ), ..., ℓ_n(σ)).

This is the canonical definition using a function type `Fin n → ℕ`.
For the list representation, use `lehmerCode_toList`.

See Definition 1.3.5 (def.perm.lehmer1) part (e) in the source.
-/
def lehmerCode (σ : Equiv.Perm (Fin n)) : Fin n → ℕ :=
  fun i => lehmerEntry σ i

/--
Each entry of a Lehmer code satisfies the bound ℓ_i(σ) ≤ n - i - 1.
This shows the Lehmer code map is well-defined into H_n.

See Definition 1.3.5 (def.perm.lehmer1) part (d) in the source.
-/
theorem lehmerEntry_le (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    lehmerEntry σ i ≤ n - 1 - i.val := by
  unfold lehmerEntry
  -- The filter is a subset of {j | i < j}, which has size n - 1 - i.val
  calc (Finset.filter (fun j : Fin n => i < j ∧ σ i > σ j) Finset.univ).card
      ≤ (Finset.filter (fun j : Fin n => i < j) Finset.univ).card := by
        apply Finset.card_le_card
        intro j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro ⟨hij, _⟩
        exact hij
    _ = (Finset.Ioi i).card := by
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
    _ = n - 1 - i.val := by
        simp only [Fin.card_Ioi]

/--
The length of σ equals the sum of its Lehmer code entries:
ℓ(σ) = ℓ_1(σ) + ℓ_2(σ) + ... + ℓ_n(σ).

See Proposition 1.3.6 (prop.perm.lehmer.l) in the source.
-/
theorem invCount_eq_sum_lehmerCode (σ : Equiv.Perm (Fin n)) :
    invCount σ = ∑ i : Fin n, lehmerEntry σ i := by
  -- The inversions of σ are pairs (i, j) with i < j and σ(i) > σ(j).
  -- The Lehmer entry at i counts j > i with σ(i) > σ(j).
  -- So the sum of Lehmer entries partitions the inversions by first coordinate.
  unfold invCount inv lehmerEntry
  rw [← card_sigma]
  apply card_bij (fun p _ => ⟨p.1, p.2⟩)
  · intro ⟨i, j⟩ hp
    simp only [mem_sigma, mem_univ, mem_filter, true_and] at hp ⊢
    exact hp
  · intro ⟨i, j⟩ _ ⟨i', j'⟩ _ heq
    simp only [Sigma.mk.inj_iff] at heq
    obtain ⟨h1, h2⟩ := heq
    subst h1
    simp only [heq_eq_eq] at h2
    subst h2
    rfl
  · intro ⟨i, j⟩ hj
    simp only [mem_sigma, mem_univ, mem_filter, true_and] at hj
    exact ⟨(i, j), by simp [hj], rfl⟩

/--
Alternative characterization of `lehmerEntry` using `σ j < σ i` instead of `σ i > σ j`.
These are equivalent conditions.
-/
theorem lehmerEntry_eq_filter_lt (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    lehmerEntry σ i = (Finset.filter (fun j : Fin n => i < j ∧ σ j < σ i) Finset.univ).card := by
  rfl

/--
The Lehmer code as a list representation.
This converts the function representation `Fin n → ℕ` to a `List ℕ`.
-/
def lehmerCode_toList (σ : Equiv.Perm (Fin n)) : List ℕ :=
  (List.finRange n).map (lehmerCode σ)

/--
The list representation of the Lehmer code has length n.
-/
theorem lehmerCode_toList_length (σ : Equiv.Perm (Fin n)) :
    (lehmerCode_toList σ).length = n := by
  simp [lehmerCode_toList]

/--
The i-th element of the list representation equals the function value.
-/
theorem lehmerCode_toList_get (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (lehmerCode_toList σ).get ⟨i.val, by simp [lehmerCode_toList]⟩ = lehmerCode σ i := by
  simp [lehmerCode_toList]

end Perm

/-! ### The set of Lehmer codes -/

/--
The set H_n of valid Lehmer codes. An n-tuple (j_1, ..., j_n) is in H_n
if and only if j_i ≤ n - i - 1 for each i ∈ [n].

This is [n-1]_0 × [n-2]_0 × ... × [0]_0.

See Definition 1.3.5 (def.perm.lehmer1) part (c) in the source.
-/
def lehmerCodeSet (n : ℕ) : Set (Fin n → ℕ) :=
  {f | ∀ i : Fin n, f i ≤ n - 1 - i.val}

/--
The Lehmer code of any permutation lies in H_n.
-/
theorem Perm.lehmerCode_mem_lehmerCodeSet {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Perm.lehmerCode σ ∈ lehmerCodeSet n := by
  intro i
  exact Perm.lehmerEntry_le σ i

-- Helper lemma for encard of Iic
private lemma encard_Iic_nat (b : ℕ) : (Set.Iic b).encard = b + 1 := by
  rw [← (Set.finite_Iic (α := ℕ) b).cast_ncard_eq]
  simp only [Set.ncard_Iic_nat]
  norm_cast

-- Helper lemma: product of (i.val + 1) over Fin n equals n!
private lemma prod_Fin_val_add_one (n : ℕ) : ∏ x : Fin n, (x.val + 1) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Nat.factorial_succ, Fin.val_last]
    rw [mul_comm]
    simp only [Fin.val_castSucc]
    rw [ih]

-- Helper lemma: product of (n - i.val) over Fin n equals n!
private lemma prod_Fin_sub_val (n : ℕ) : ∏ x : Fin n, (n - x.val : ℕ) = n.factorial := by
  have h : ∀ x : Fin n, (n - x.val : ℕ) = x.rev.val + 1 := by
    intro x
    simp only [Fin.rev]
    omega
  simp_rw [h]
  rw [Fintype.prod_equiv Fin.revPerm (fun x => x.rev.val + 1) (fun x => x.val + 1)
    (by simp [Fin.revPerm_apply])]
  exact prod_Fin_val_add_one n

/--
The set H_n has size n!.

See Definition 1.3.5 (def.perm.lehmer1) part (c) in the source.
-/
theorem card_lehmerCodeSet (n : ℕ) :
    (lehmerCodeSet n).ncard = n.factorial := by
  -- Express lehmerCodeSet as a pi set
  have h : lehmerCodeSet n = Set.pi Set.univ (fun i : Fin n => Set.Iic (n - 1 - i.val)) := by
    ext f
    simp only [lehmerCodeSet, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]
  rw [h]
  -- Show the pi set is finite
  have hfin : (Set.pi Set.univ (fun i : Fin n => Set.Iic (n - 1 - i.val))).Finite := by
    apply Set.Finite.pi
    intro i
    exact Set.finite_Iic (α := ℕ) (n - 1 - i.val)
  -- Convert ncard to encard and use encard_pi_eq_prod_encard
  rw [← Nat.cast_inj (R := ℕ∞), hfin.cast_ncard_eq]
  rw [Set.encard_pi_eq_prod_encard]
  simp_rw [encard_Iic_nat]
  -- Simplify the product
  have h2 : ∀ i : Fin n, (n - 1 - i.val + 1 : ℕ) = n - i.val := fun i => by omega
  have h3 : (∏ i : Fin n, (↑(n - 1 - i.val) + 1 : ℕ∞)) = ∏ i : Fin n, (↑(n - i.val) : ℕ∞) := by
    congr 1
    ext i
    rw [← h2 i]
    norm_cast
  rw [h3]
  norm_cast
  exact prod_Fin_sub_val n

-- Helper: the set of "remaining" elements at position i (not yet used in positions < i)
private def remainingSet {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun x => ∀ j : Fin n, j < i → σ j ≠ x)

-- Count elements smaller than x in the remaining set
private def countSmallerInRemaining {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) (x : Fin n) : ℕ :=
  ((remainingSet σ i).filter (· < x)).card

-- Key lemma: lehmerEntry equals the count of smaller remaining elements
private lemma lehmerEntry_eq_countSmaller {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    Perm.lehmerEntry σ i = countSmallerInRemaining σ i (σ i) := by
  unfold Perm.lehmerEntry countSmallerInRemaining remainingSet
  apply Finset.card_bij (fun j _ => σ j)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    refine ⟨?_, hj.2⟩
    intro k hk heq
    have : k ≠ j := fun h => by omega
    exact this (σ.injective heq)
  · intro j₁ hj₁ j₂ hj₂ heq
    exact σ.injective heq
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨σ.symm x, ?_, σ.apply_symm_apply x⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · by_contra h
      push Not at h
      have hsx : σ (σ.symm x) = x := σ.apply_symm_apply x
      rcases h.lt_or_eq with hlt | heq
      · exact hx.1 (σ.symm x) hlt hsx
      · rw [heq] at hsx
        exact (lt_irrefl x (hsx ▸ hx.2))
    · rw [σ.apply_symm_apply]
      exact hx.2

-- The main lemma: if prefix matches and lehmerEntry matches, then values match
private lemma eq_of_lehmerEntry_eq_and_prefix_eq {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (i : Fin n)
    (hprefix : ∀ j : Fin n, j < i → σ j = τ j)
    (hL : Perm.lehmerEntry σ i = Perm.lehmerEntry τ i) :
    σ i = τ i := by
  have hrem_eq : remainingSet σ i = remainingSet τ i := by
    ext x
    simp only [remainingSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j hj; rw [← hprefix j hj]; exact h j hj
    · intro h j hj; rw [hprefix j hj]; exact h j hj
  have hσ_mem : σ i ∈ remainingSet σ i := by
    simp only [remainingSet, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj heq
    have : j = i := σ.injective heq
    omega
  have hτ_mem : τ i ∈ remainingSet τ i := by
    simp only [remainingSet, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj heq
    have : j = i := τ.injective heq
    omega
  have hcount : countSmallerInRemaining σ i (σ i) = countSmallerInRemaining τ i (τ i) := by
    rw [← lehmerEntry_eq_countSmaller, ← lehmerEntry_eq_countSmaller, hL]
  rw [hrem_eq] at hσ_mem
  unfold countSmallerInRemaining at hcount
  rw [hrem_eq] at hcount
  by_contra hne
  rcases lt_trichotomy (σ i) (τ i) with hlt | heq | hgt
  · have hsub : ((remainingSet τ i).filter (· < σ i)) ⊂ ((remainingSet τ i).filter (· < τ i)) := by
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, lt_trans hx.2 hlt⟩
      · intro hall
        have hmem : σ i ∈ (remainingSet τ i).filter (· < τ i) := by
          rw [Finset.mem_filter]
          exact ⟨hσ_mem, hlt⟩
        have := hall hmem
        rw [Finset.mem_filter] at this
        exact (lt_irrefl (σ i)) this.2
    have := Finset.card_lt_card hsub
    omega
  · exact hne heq
  · have hsub : ((remainingSet τ i).filter (· < τ i)) ⊂ ((remainingSet τ i).filter (· < σ i)) := by
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, lt_trans hx.2 hgt⟩
      · intro hall
        have hmem : τ i ∈ (remainingSet τ i).filter (· < σ i) := by
          rw [Finset.mem_filter]
          exact ⟨hτ_mem, hgt⟩
        have := hall hmem
        rw [Finset.mem_filter] at this
        exact (lt_irrefl (τ i)) this.2
    have := Finset.card_lt_card hsub
    omega

/--
The Lehmer code map L : S_n → H_n is injective.

See Theorem 1.3.7 (thm.perm.lehmer.bij) in the source.
-/
theorem Perm.lehmerCode_injective (n : ℕ) :
    Function.Injective (fun σ : Equiv.Perm (Fin n) => Perm.lehmerCode σ) := by
  intro σ τ hL
  ext i
  have wf : WellFounded (fun (a b : Fin n) => a < b) := wellFounded_lt
  have := wf.induction i (fun i ih => by
    apply eq_of_lehmerEntry_eq_and_prefix_eq
    · intro j hj
      exact ih j hj
    · have := congr_fun hL i
      simp only [Perm.lehmerCode] at this
      exact this)
  simp [this]

/--
The Lehmer code map L : S_n → H_n is a bijection.

See Theorem 1.3.7 (thm.perm.lehmer.bij) in the source.
-/
theorem Perm.lehmerCode_bijective (n : ℕ) :
    Function.Bijective (fun σ : Equiv.Perm (Fin n) =>
      (⟨Perm.lehmerCode σ, Perm.lehmerCode_mem_lehmerCodeSet σ⟩ : lehmerCodeSet n)) := by
  -- The set H_n is finite (each entry is bounded)
  have hfinite : (lehmerCodeSet n).Finite := by
    apply Set.Finite.subset (s := {f : Fin n → ℕ | ∀ i, f i ∈ Set.Iic (n - 1 - i.val)})
    · exact Set.Finite.pi' (fun i => Set.finite_Iic _)
    · intro f hf
      simp only [Set.mem_ofPred_eq, Set.mem_Iic]
      exact hf
  haveI : Fintype (lehmerCodeSet n) := hfinite.fintype
  -- Bijective iff injective and equal cardinality
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · -- Injectivity follows from lehmerCode_injective
    exact fun σ τ h => Perm.lehmerCode_injective n (Subtype.mk.injEq _ _ _ _ ▸ h)
  · -- Cardinalities: |S_n| = n! = |H_n|
    rw [Fintype.card_perm, Fintype.card_fin]
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, card_lehmerCodeSet]

/-! ### Lexicographic order -/

/--
Lexicographic order on n-tuples of integers.
We say (a_1, ..., a_n) <_lex (b_1, ..., b_n) if there exists k ∈ [n]
such that a_k ≠ b_k and the smallest such k satisfies a_k < b_k.

Note: This is essentially `Pi.Lex (· < ·) (· < ·)` from Mathlib, specialized to `Fin n → ℤ`.
We define it directly here to match the source presentation.

See Definition 1.3.8 (def.perm.lehmer.lex-ord) in the source.
-/
def lexLt {n : ℕ} (a b : Fin n → ℤ) : Prop :=
  ∃ k : Fin n, (∀ i : Fin n, i < k → a i = b i) ∧ a k < b k

/--
The lexicographic order `lexLt` is equivalent to Mathlib's `Pi.Lex (· < ·) (· < ·)`.

This shows that our definition matches the standard Mathlib definition for
lexicographic order on pi types.
-/
theorem lexLt_eq_piLex {n : ℕ} (a b : Fin n → ℤ) :
    lexLt a b ↔ Pi.Lex (· < ·) (fun {_} => (· < ·)) a b := by
  simp only [lexLt, Pi.Lex]

/--
The lexicographic order is irreflexive: no tuple is lexicographically smaller than itself.

This is part of Definition 1.3.8 (def.perm.lehmer.lex-ord): `<_lex` is a strict order.
-/
theorem lexLt_irrefl {n : ℕ} (a : Fin n → ℤ) : ¬lexLt a a := by
  intro ⟨k, _, hk⟩
  exact lt_irrefl (a k) hk

/--
The lexicographic order is transitive.

This is part of Definition 1.3.8 (def.perm.lehmer.lex-ord): `<_lex` is a strict order.
-/
theorem lexLt_trans {n : ℕ} {a b c : Fin n → ℤ} (hab : lexLt a b) (hbc : lexLt b c) :
    lexLt a c := by
  obtain ⟨k₁, hk₁_eq, hk₁_lt⟩ := hab
  obtain ⟨k₂, hk₂_eq, hk₂_lt⟩ := hbc
  rcases lt_trichotomy k₁ k₂ with hk | hk | hk
  · -- k₁ < k₂: use k₁ as witness
    use k₁
    constructor
    · intro i hi
      exact (hk₁_eq i hi).trans (hk₂_eq i (hi.trans hk))
    · -- a k₁ < b k₁ and b k₁ = c k₁ (since k₁ < k₂)
      have hbc_eq : b k₁ = c k₁ := hk₂_eq k₁ hk
      rw [← hbc_eq]
      exact hk₁_lt
  · -- k₁ = k₂: use k₁ as witness
    subst hk
    use k₁
    constructor
    · intro i hi
      exact (hk₁_eq i hi).trans (hk₂_eq i hi)
    · exact hk₁_lt.trans hk₂_lt
  · -- k₂ < k₁: use k₂ as witness
    use k₂
    constructor
    · intro i hi
      exact (hk₁_eq i (hi.trans hk)).trans (hk₂_eq i hi)
    · -- a k₂ = b k₂ (since k₂ < k₁) and b k₂ < c k₂
      have hab_eq : a k₂ = b k₂ := hk₁_eq k₂ hk
      rw [hab_eq]
      exact hk₂_lt

/--
The lexicographic order is asymmetric: if a <_lex b, then not b <_lex a.

This is part of Definition 1.3.8 (def.perm.lehmer.lex-ord): `<_lex` is a strict order.
-/
theorem lexLt_asymm {n : ℕ} {a b : Fin n → ℤ} (hab : lexLt a b) : ¬lexLt b a := by
  intro hba
  have haa := lexLt_trans hab hba
  exact lexLt_irrefl a haa

/--
If a and b are two distinct n-tuples of integers, then either a <_lex b or b <_lex a.

See Proposition 1.3.9 (prop.perm.lehmer.lex-ord.total) in the source.
-/
theorem lexLt_trichotomous {n : ℕ} (a b : Fin n → ℤ) (hab : a ≠ b) :
    lexLt a b ∨ lexLt b a := by
  -- There exists some index where they differ
  have h : ∃ i, a i ≠ b i := Function.ne_iff.mp hab
  -- Find the minimal such index using well-founded recursion on Fin n
  have wf : WellFounded (fun (i j : Fin n) => i < j) := wellFounded_lt
  obtain ⟨k, hk_mem, hk_min⟩ := wf.has_min {i : Fin n | a i ≠ b i} h
  have hk : a k ≠ b k := hk_mem
  have hk_min' : ∀ i, i < k → a i = b i := by
    intro i hi
    by_contra h_ne
    exact hk_min i h_ne hi
  -- Now a k ≠ b k, so either a k < b k or a k > b k
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · left
    exact ⟨k, hk_min', hlt⟩
  · right
    exact ⟨k, fun i hi => (hk_min' i hi).symm, hgt⟩

/--
The lexicographic order is a strict total order on n-tuples of integers:
for any a, b, exactly one of `a = b`, `lexLt a b`, or `lexLt b a` holds.

This completes the proof that `<_lex` defines a strict total order on ℤⁿ.
See Definition 1.3.8 (def.perm.lehmer.lex-ord) in the source.
-/
theorem lexLt_strictTotalOrder {n : ℕ} (a b : Fin n → ℤ) :
    (a = b ∧ ¬lexLt a b ∧ ¬lexLt b a) ∨
    (a ≠ b ∧ lexLt a b ∧ ¬lexLt b a) ∨
    (a ≠ b ∧ ¬lexLt a b ∧ lexLt b a) := by
  by_cases hab : a = b
  · left
    exact ⟨hab, hab ▸ lexLt_irrefl a, hab ▸ lexLt_irrefl a⟩
  · rcases lexLt_trichotomous a b hab with h | h
    · right; left
      exact ⟨hab, h, lexLt_asymm h⟩
    · right; right
      exact ⟨hab, lexLt_asymm h, h⟩

/-- Alternative characterization of Lehmer entry:
ℓ_i(σ) = |{v < σ(i) : v ∉ σ({0, ..., i-1})}|

This is the number of elements smaller than σ(i) that haven't been "used" yet
(i.e., are not in the image of positions before i).

See the proof of Theorem 1.3.7 (thm.perm.lehmer.bij) in the source. -/
lemma Perm.lehmerEntry_eq_card_filter {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    Perm.lehmerEntry σ i =
    (Finset.filter (fun v : Fin n => v < σ i ∧ v ∉ Finset.image σ (Finset.filter (· < i) Finset.univ))
      Finset.univ).card := by
  unfold Perm.lehmerEntry
  apply Finset.card_bij (fun j _ => σ j)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    constructor
    · exact hj.2
    · intro hmem
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      obtain ⟨k, hk, hσk⟩ := hmem
      have h_eq : j = k := σ.injective hσk.symm
      omega
  · intro j₁ h₁ j₂ h₂ heq
    exact σ.injective heq
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    use σ⁻¹ v
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · by_contra h_not_lt
        push Not at h_not_lt
        rcases h_not_lt.lt_or_eq with h_lt | h_eq
        · apply hv.2
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨σ⁻¹ v, h_lt, ?_⟩
          exact Equiv.apply_symm_apply σ v
        · have hvi : v = σ i := by
            calc v = σ (σ⁻¹ v) := (Equiv.apply_symm_apply σ v).symm
              _ = σ i := by rw [h_eq]
          omega
      · have : σ (σ⁻¹ v) = v := Equiv.apply_symm_apply σ v
        rw [this]
        exact hv.1
    · exact Equiv.apply_symm_apply σ v

/-- If σ and τ agree on positions below k, then their images on those positions are equal.

This is a helper lemma for `Perm.lehmerCode_preserves_lexLt`. -/
private lemma image_eq_of_agree_below {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (k : Fin n)
    (h : ∀ i : Fin n, i < k → σ i = τ i) :
    Finset.image σ (Finset.filter (· < k) Finset.univ) =
    Finset.image τ (Finset.filter (· < k) Finset.univ) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, (h j hj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, h j hj⟩

/-- If σ and τ agree on positions up to and including i, then their Lehmer entries at i are equal.

This is Lemma lem.perm.lehmer.lex1 part (b) from the source. -/
private lemma lehmerEntry_eq_of_agree_on {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (i : Fin n)
    (h_agree : ∀ j : Fin n, j ≤ i → σ j = τ j) :
    Perm.lehmerEntry σ i = Perm.lehmerEntry τ i := by
  rw [Perm.lehmerEntry_eq_card_filter, Perm.lehmerEntry_eq_card_filter]
  have hσi_eq_τi : σ i = τ i := h_agree i (le_refl i)
  have himage_eq : Finset.image σ (Finset.filter (· < i) Finset.univ) =
                   Finset.image τ (Finset.filter (· < i) Finset.univ) := by
    apply image_eq_of_agree_below
    intro j hj
    exact h_agree j (le_of_lt hj)
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ⟨hv_lt, hv_not_in⟩
    constructor
    · rw [← hσi_eq_τi]; exact hv_lt
    · rw [← himage_eq]; exact hv_not_in
  · intro ⟨hv_lt, hv_not_in⟩
    constructor
    · rw [hσi_eq_τi]; exact hv_lt
    · rw [himage_eq]; exact hv_not_in

/-- If σ and τ agree on positions below k, and σ(k) < τ(k), then ℓ_k(σ) < ℓ_k(τ).

This is Lemma lem.perm.lehmer.lex1 part (c) from the source.
The key insight is that the set of "available" values below σ(k) is a proper subset
of those below τ(k), because σ(k) itself is available for τ but not for σ. -/
private lemma lehmerEntry_lt_of_agree_below_and_lt {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (k : Fin n)
    (h_agree : ∀ i : Fin n, i < k → σ i = τ i) (h_lt : σ k < τ k) :
    Perm.lehmerEntry σ k < Perm.lehmerEntry τ k := by
  rw [Perm.lehmerEntry_eq_card_filter, Perm.lehmerEntry_eq_card_filter]
  have himage_eq : Finset.image σ (Finset.filter (· < k) Finset.univ) =
                   Finset.image τ (Finset.filter (· < k) Finset.univ) := by
    apply image_eq_of_agree_below
    exact h_agree
  set S_σ := Finset.filter (fun v : Fin n => v < σ k ∧ v ∉ Finset.image σ (Finset.filter (· < k) Finset.univ)) Finset.univ with hS_σ_def
  set S_τ := Finset.filter (fun v : Fin n => v < τ k ∧ v ∉ Finset.image τ (Finset.filter (· < k) Finset.univ)) Finset.univ with hS_τ_def
  -- S_σ ⊆ S_τ because σ(k) < τ(k) and the images below k are equal
  have h_subset : S_σ ⊆ S_τ := by
    intro v hv
    rw [hS_σ_def, Finset.mem_filter] at hv
    rw [hS_τ_def, Finset.mem_filter]
    constructor
    · exact hv.1
    · constructor
      · exact hv.2.1.trans h_lt
      · rw [← himage_eq]; exact hv.2.2
  -- σ(k) is in S_τ (since σ(k) < τ(k) and σ(k) is not in the image below k)
  have h_σk_in_S_τ : σ k ∈ S_τ := by
    rw [hS_τ_def, Finset.mem_filter]
    constructor
    · exact Finset.mem_univ _
    · constructor
      · exact h_lt
      · rw [← himage_eq]
        intro hmem
        rw [Finset.mem_image] at hmem
        obtain ⟨j, hj, hσj⟩ := hmem
        rw [Finset.mem_filter] at hj
        have h_eq : k = j := σ.injective hσj.symm
        omega
  -- σ(k) is not in S_σ (since σ(k) is not < σ(k))
  have h_σk_notin_S_σ : σ k ∉ S_σ := by
    rw [hS_σ_def, Finset.mem_filter]
    push Not
    intro _ h_absurd
    exact absurd h_absurd (Nat.lt_irrefl _)
  -- Therefore S_σ is a proper subset of S_τ
  apply Finset.card_lt_card
  rw [Finset.ssubset_def]
  constructor
  · exact h_subset
  · intro h_eq
    have : σ k ∈ S_σ := h_eq h_σk_in_S_τ
    exact h_σk_notin_S_σ this

/--
If σ, τ ∈ S_n satisfy (σ(1), ..., σ(n)) <_lex (τ(1), ..., τ(n)),
then L(σ) <_lex L(τ).

**Proposition prop.perm.lehmer.lex** from the source.

The proof uses the alternative characterization of Lehmer entries:
ℓ_i(σ) counts elements smaller than σ(i) that are not in the image of positions before i.
If σ and τ agree on positions below k and σ(k) < τ(k), then:
- For i < k: ℓ_i(σ) = ℓ_i(τ) (since the images below i are equal and σ(i) = τ(i))
- At k: ℓ_k(σ) < ℓ_k(τ) (since σ(k) is available for τ but not for σ)
-/
theorem Perm.lehmerCode_preserves_lexLt {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (h : lexLt (fun i => (σ i).val) (fun i => (τ i).val)) :
    lexLt (fun i => (Perm.lehmerEntry σ i : ℤ)) (fun i => (Perm.lehmerEntry τ i : ℤ)) := by
  -- Unpack the hypothesis: there exists k such that σ and τ agree on [k-1] and σ(k) < τ(k)
  obtain ⟨k, h_agree, h_lt⟩ := h
  -- The same k witnesses the lexicographic ordering of Lehmer codes
  use k
  constructor
  · -- For i < k, we have ℓ_i(σ) = ℓ_i(τ)
    intro i hi
    have h_agree_le : ∀ j : Fin n, j ≤ i → σ j = τ j := by
      intro j hj
      have hji : j < k := lt_of_le_of_lt hj hi
      have h_eq_val : (σ j).val = (τ j).val := by
        simp only at h_agree
        exact Int.ofNat_inj.mp (h_agree j hji)
      exact Fin.ext h_eq_val
    have := lehmerEntry_eq_of_agree_on σ τ i h_agree_le
    simp only [Int.ofNat_inj]
    exact this
  · -- At position k, we have ℓ_k(σ) < ℓ_k(τ)
    have h_agree_fin : ∀ i : Fin n, i < k → σ i = τ i := by
      intro i hi
      have h_eq_val : (σ i).val = (τ i).val := by
        simp only at h_agree
        exact Int.ofNat_inj.mp (h_agree i hi)
      exact Fin.ext h_eq_val
    have h_lt_fin : σ k < τ k := by
      simp only [Fin.lt_def]
      exact Int.ofNat_lt.mp h_lt
    have := lehmerEntry_lt_of_agree_below_and_lt σ τ k h_agree_fin h_lt_fin
    simp only
    exact Int.ofNat_lt.mpr this

/-! ### Generating function for length -/

/-- Helper lemma: Lehmer code entry is strictly less than n - i. -/
theorem Perm.lehmerEntry_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    Perm.lehmerEntry σ i < n - i.val := by
  have h := Perm.lehmerEntry_le σ i
  have hi := i.isLt
  omega

/-- The Lehmer code finset: all functions f : Fin n → ℕ with f i < n - i. -/
private def lehmerCodeFinset (n : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun i : Fin n => Finset.range (n - i.val))

/-- Lehmer code of a permutation is in the Lehmer code finset. -/
private lemma lehmerCode_mem_lehmerCodeFinset {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Perm.lehmerCode σ ∈ lehmerCodeFinset n := by
  simp only [lehmerCodeFinset, Fintype.mem_piFinset, Finset.mem_range]
  intro i
  exact Perm.lehmerEntry_lt σ i

/-- The cardinality of the Lehmer code finset is n!. -/
private lemma card_lehmerCodeFinset (n : ℕ) : (lehmerCodeFinset n).card = n.factorial := by
  simp only [lehmerCodeFinset, Fintype.card_piFinset, Finset.card_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, tsub_zero]
    rw [Nat.factorial_succ]
    congr 1
    conv_lhs =>
      arg 2
      ext i
      rw [Fin.val_succ]
    simp only [Nat.add_sub_add_right]
    exact ih

/-- The image of the Lehmer code map. -/
private def lehmerCodeImage (n : ℕ) : Finset (Fin n → ℕ) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).image Perm.lehmerCode

/-- The image of the Lehmer code map is a subset of the Lehmer code finset. -/
private lemma lehmerCodeImage_subset (n : ℕ) : lehmerCodeImage n ⊆ lehmerCodeFinset n := by
  intro f hf
  simp only [lehmerCodeImage, Finset.mem_image, Finset.mem_univ, true_and] at hf
  obtain ⟨σ, rfl⟩ := hf
  exact lehmerCode_mem_lehmerCodeFinset σ

/-- The cardinality of the image of the Lehmer code map is n!. -/
private lemma card_lehmerCodeImage (n : ℕ) : (lehmerCodeImage n).card = n.factorial := by
  simp only [lehmerCodeImage, Finset.card_image_of_injective _ (Perm.lehmerCode_injective n)]
  simp [Fintype.card_perm]

/-- The image of the Lehmer code map equals the Lehmer code finset. -/
private lemma lehmerCodeImage_eq (n : ℕ) : lehmerCodeImage n = lehmerCodeFinset n := by
  apply Finset.eq_of_subset_of_card_le (lehmerCodeImage_subset n)
  rw [card_lehmerCodeImage, card_lehmerCodeFinset]

/--
The generating function for permutation lengths:
∑_{σ ∈ S_n} x^{ℓ(σ)} = [n]_x!

This equals the product (1+x)(1+x+x²)...(1+x+...+x^{n-1}).

See Proposition 1.3.4 (prop.perm.length.gf) in the source.
-/
theorem length_generating_function (n : ℕ) (x : ℕ) :
    ∑ σ : Equiv.Perm (Fin n), x ^ Perm.invCount σ =
    ∏ i ∈ Finset.range n, ∑ j ∈ Finset.range (i + 1), x ^ j := by
  -- Step 1: Replace invCount with sum of lehmerEntry
  conv_lhs =>
    congr
    · skip
    ext σ
    rw [Perm.invCount_eq_sum_lehmerCode]
  -- Step 2: Use x^(sum) = prod(x^)
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  -- Now LHS = ∑ σ, ∏ i, x ^ (lehmerEntry σ i)
  -- Step 3: Rewrite as sum over lehmerCodeFinset using the bijection
  have h1 : ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, x ^ Perm.lehmerEntry σ i =
            ∑ f ∈ lehmerCodeFinset n, ∏ i : Fin n, x ^ f i := by
    rw [← lehmerCodeImage_eq]
    simp only [lehmerCodeImage]
    rw [Finset.sum_image (fun σ _ τ _ h => Perm.lehmerCode_injective n h)]
    rfl
  rw [h1]
  -- Step 4: Use prod_univ_sum to convert sum over piFinset to product of sums
  rw [lehmerCodeFinset, ← Finset.prod_univ_sum]
  -- Step 5: Convert product over Fin n to product over range n
  rw [Fin.prod_univ_eq_prod_range (f := fun i => ∑ j ∈ Finset.range (n - i), x ^ j)]
  -- Step 6: Flip the product to match the target
  cases n with
  | zero => simp
  | succ n =>
    have h := @Finset.prod_flip ℕ _ n (fun i => ∑ j ∈ Finset.range (i + 1), x ^ j)
    rw [← h]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    have hle : i ≤ n := Nat.lt_succ_iff.mp hi
    have heq : n + 1 - i = n - i + 1 := by omega
    rw [heq]

end AlgebraicCombinatorics
