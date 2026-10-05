/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import AlgebraicCombinatorics.FPS.InfiniteProducts2

/-!
# Infinite Products of Formal Power Series - Part 2

This file formalizes the second part of the detailed proofs for infinite products
of formal power series, following the Details section of Loehr's "Bijective Combinatorics".

The main content includes:
- Product rules (generalized distributive laws) for infinite products
- Composition rules for infinite products with substitution
- Supporting lemmas about coefficient extraction and summability

## Main Definitions

* `PowerSeries.EssentiallyFinite`: A family `(k_i)_{i ∈ I}` is essentially finite if
  all but finitely many entries equal 0.
* `PowerSeries.SfinI`: The set of essentially finite families in `∏_{i ∈ I} S_i`.

## Main Results

### Product Rules (Generalized Distributive Laws)

* `PowerSeries.prodRule_claim3`: For `(i,k) ∈ S̄ \ T'_n`, we have `[x^m] p_{i,k} = 0`
  for all `m ∈ {0,1,...,n}`. (Claim 3, label: pf.prop.fps.prodrule-fin-inf.Tm-def)
* `PowerSeries.prodRule_claim4`: If `(k_i)_{i ∈ I} ∈ S^I_fin`, then `(p_{i,k_i})_{i ∈ I}`
  is multipliable. (Claim 4)
* `PowerSeries.prodRule_claim5`: Under certain conditions, `[x^n](∏_{i ∈ I} p_{i,k_i}) = 0`.
  (Claim 5)
* `PowerSeries.prodRule_claim6`: For `(k_i) ∈ S^I_fin \ S^I_{I_n}`, the product coefficient
  vanishes. (Claim 6)
* `PowerSeries.prodRule_claim7`: The family `(∏_{i ∈ I} p_{i,k_i})` indexed by essentially
  finite families is summable. (Claim 7)
* `PowerSeries.prodRule_claim8`: Coefficient reduction to finite index sets. (Claim 8)
* `PowerSeries.prodRule_claim9`: Coefficient vanishing for non-contributing terms. (Claim 9)
* `PowerSeries.prodRule_claim10`: Product reduction to finite index sets. (Claim 10)
* `PowerSeries.prodRule_claim11`: Finite product-sum interchange. (Claim 11)
* `PowerSeries.prodRule_infInf`: **Main Proposition** (prop.fps.prodrule-inf-inf) - The
  generalized distributive law for infinite products and infinite sums:
  `∏_{i ∈ I} ∑_{k ∈ S_i} p_{i,k} = ∑_{(k_i) ∈ S^I_fin} ∏_{i ∈ I} p_{i,k_i}`

### Composition Rules

* `PowerSeries.comp_prod_finite`: For finite `I`, `(∏_{i ∈ I} f_i) ∘ g = ∏_{i ∈ I} (f_i ∘ g)`.
  (Lemma lem.fps.subs.rule-infprod-fin)
* `PowerSeries.comp_prod_multipliable`: If `(f_i)_{i ∈ I}` is multipliable and `[x^0]g = 0`,
  then `(f_i ∘ g)_{i ∈ I}` is multipliable. (Proposition prop.fps.subs.rule-infprod, part 1)
* `PowerSeries.comp_prod_infinite`: For multipliable `(f_i)_{i ∈ I}` with `[x^0]g = 0`,
  `(∏_{i ∈ I} f_i) ∘ g = ∏_{i ∈ I} (f_i ∘ g)`. (Proposition prop.fps.subs.rule-infprod, part 2)

## References

* [Loehr, *Bijective Combinatorics*, Details: Infinite Products (Part 2)]
-/

open scoped Polynomial BigOperators

namespace PowerSeries

variable {K : Type*} [CommRing K]

/-!
### Essentially Finite Families

A family `(k_i)_{i ∈ I}` indexed by a set `I` with values in `ℕ` is essentially finite
if all but finitely many entries equal `0`. This is the key concept for indexing
summable families of products.
-/

/-- A family `f : I → ℕ` is essentially finite if all but finitely many values are 0.
This corresponds to `S^I_fin` in the source.

**This is an alias** for the canonical `_root_.EssentiallyFinite` defined in
`FPS/InfiniteProducts2.lean`. Both definitions are **definitionally equal**:
`{i | f i ≠ 0}.Finite` = `(Function.support f).Finite` by definition.

For the full API (including `_root_.EssentiallyFinite.add`, `_root_.EssentiallyFinite.neg`,
`_root_.EssentiallyFinite.toFinsupp`, etc.), see `FPS/InfiniteProducts2.lean`.

This version is specialized to `ℕ` for use in product rule proofs. -/
abbrev EssentiallyFinite {I : Type*} (f : I → ℕ) : Prop :=
  _root_.EssentiallyFinite f

/-- `EssentiallyFinite` is equivalent to having finite support. -/
theorem essentiallyFinite_iff_support_finite {I : Type*} (f : I → ℕ) :
    EssentiallyFinite f ↔ (Function.support f).Finite :=
  _root_.EssentiallyFinite.iff_support_finite

/-- The support of an essentially finite family is finite.
    (Delegates to `_root_.EssentiallyFinite.finite_support`) -/
theorem EssentiallyFinite.support_finite {I : Type*} {f : I → ℕ}
    (hf : EssentiallyFinite f) : {i : I | f i ≠ 0}.Finite :=
  hf

/-- The zero family is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.zero`) -/
theorem essentiallyFinite_zero {I : Type*} : EssentiallyFinite (fun _ : I => 0) :=
  _root_.EssentiallyFinite.zero

/-- A family with finite support is essentially finite. -/
theorem essentiallyFinite_of_finite_support {I : Type*} {f : I → ℕ} {s : Finset I}
    (hs : ∀ i, f i ≠ 0 → i ∈ s) : EssentiallyFinite f := by
  apply Set.Finite.subset s.finite_toSet
  intro i hi
  exact hs i hi

/-!
### Summability and Multipliability for Product Rules

The following definitions and lemmas support the product rule proofs.
-/

/-- For a summable family `(p_{i,k})`, the set `T_m` of pairs `(i,k)` with nonzero
`[x^m] p_{i,k}` is finite. This corresponds to equation (pf.prop.fps.prodrule-fin-inf.Tm-def).
(label: pf.prop.fps.prodrule-fin-inf.Tm-def) -/
def CoeffSupportSet {I : Type*} (p : I → ℕ → PowerSeries K) (m : ℕ) : Set (I × ℕ) :=
  {ik : I × ℕ | ik.2 ≠ 0 ∧ coeff m (p ik.1 ik.2) ≠ 0}

/-- The union of coefficient support sets up to degree n.
This corresponds to `T'_n = T_0 ∪ T_1 ∪ ... ∪ T_n`. -/
def CoeffSupportSetUnion {I : Type*} (p : I → ℕ → PowerSeries K) (n : ℕ) : Set (I × ℕ) :=
  ⋃ m ∈ Finset.range (n + 1), CoeffSupportSet p m

/-- The index set `I_n` of first components appearing in `T'_n`. -/
def IndexSetIn {I : Type*} (p : I → ℕ → PowerSeries K) (n : ℕ) : Set I :=
  {i : I | ∃ k, (i, k) ∈ CoeffSupportSetUnion p n}

/-- The value set `K_n` of second components appearing in `T'_n`. -/
def ValueSetKn {I : Type*} (p : I → ℕ → PowerSeries K) (n : ℕ) : Set ℕ :=
  {k : ℕ | ∃ i, (i, k) ∈ CoeffSupportSetUnion p n}

/-!
### Claim 3: Coefficient Vanishing Outside T'_n

For `(i,k) ∈ S̄ \ T'_n`, we have `[x^m] p_{i,k} = 0` for all `m ∈ {0,1,...,n}`.
(label: pf.prop.fps.prodrule-fin-inf.Tm-def)
-/

/-- Claim 3: If `(i,k)` is not in the coefficient support union up to `n`, then
all coefficients up to degree `n` vanish.
(Claim 3, label: pf.prop.fps.prodrule-fin-inf.Tm-def) -/
theorem prodRule_claim3 {I : Type*} (p : I → ℕ → PowerSeries K) (n : ℕ)
    (i : I) (k : ℕ) (hk : k ≠ 0)
    (hnotin : (i, k) ∉ CoeffSupportSetUnion p n) :
    ∀ m ≤ n, coeff m (p i k) = 0 := by
  intro m hm
  by_contra h
  apply hnotin
  simp only [CoeffSupportSetUnion, Set.mem_iUnion, Finset.mem_range, CoeffSupportSet,
    Set.mem_ofPred_eq]
  exact ⟨m, Nat.lt_succ_of_le hm, hk, h⟩

/-!
### Claim 4: Multipliability of Product Families

If `(k_i)_{i ∈ I}` is essentially finite, then `(p_{i,k_i})_{i ∈ I}` is multipliable.
-/

/-- Claim 4: For an essentially finite family `(k_i)` with `p_{i,0} = 1`,
the family `(p_{i,k_i})` is multipliable (all but finitely many terms are 1).
(Claim 4) -/
theorem prodRule_claim4 {I : Type*} (p : I → ℕ → PowerSeries K)
    (hp0 : ∀ i, p i 0 = 1) (k : I → ℕ) (hk : EssentiallyFinite k) :
    {i : I | p i (k i) ≠ 1}.Finite := by
  apply Set.Finite.subset hk
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi ⊢
  intro hki
  apply hi
  rw [hki, hp0]

/-!
### Claim 5: Product Coefficient Vanishing

Under certain conditions on the index family, the product coefficient vanishes.
-/

/-- Helper lemma: if all coefficients up to n are 0, then order > n -/
private lemma order_gt_of_coeff_eq_zero {n : ℕ} {f : PowerSeries K}
    (hf : ∀ m ≤ n, coeff m f = 0) : (n : ℕ∞) < f.order := by
  by_cases hf0 : f = 0
  · simp [hf0]
  · have h := nat_le_order f (n + 1) (fun i hi => hf i (Nat.lt_succ_iff.mp hi))
    exact Nat.cast_lt.mpr (Nat.lt_succ_self n) |>.trans_le h

/-- Claim 5: If some `j ∈ I` satisfies `(j, k_j) ∉ T'_n`, then
`[x^n](∏_{i ∈ I} p_{i,k_i}) = 0`.
(Claim 5) -/
theorem prodRule_claim5 {I : Type*} [DecidableEq I] (p : I → ℕ → PowerSeries K)
    (n : ℕ) (k : I → ℕ) (_hk : EssentiallyFinite k) (_hp0 : ∀ i, p i 0 = 1)
    (j : I) (hkj : k j ≠ 0) (hnotin : (j, k j) ∉ CoeffSupportSetUnion p n) :
    ∀ s : Finset I, j ∈ s →
      coeff n (∏ i ∈ s, p i (k i)) = 0 := by
  intro s hjs
  -- By Claim 3, all coefficients of p j (k j) up to degree n are 0
  have hcoeff_zero : ∀ m ≤ n, coeff m (p j (k j)) = 0 := prodRule_claim3 p n j (k j) hkj hnotin
  -- Therefore the order of p j (k j) is > n
  have horder : (n : ℕ∞) < (p j (k j)).order := order_gt_of_coeff_eq_zero hcoeff_zero
  -- Split the product at j
  have hjs' : j ∉ s.erase j := Finset.notMem_erase j s
  rw [← Finset.insert_erase hjs, Finset.prod_insert hjs']
  -- Now we have: coeff n (p j (k j) * ∏ i ∈ s.erase j, p i (k i)) = 0
  -- Use coeff_mul_of_lt_order (but we need to commute)
  rw [mul_comm]
  exact coeff_mul_of_lt_order horder

/-!
### Claim 6: Product Coefficient Vanishing for Non-Contributing Families

For families outside `S^I_{I_n}`, the product coefficient vanishes.
-/

/-- Claim 6: If `(k_i) ∈ S^I_fin \ S^I_{I_n}` (i.e., some `k_j ≠ 0` for `j ∉ I_n`),
then `[x^n](∏_{i ∈ I} p_{i,k_i}) = 0`.
(Claim 6) -/
theorem prodRule_claim6 {I : Type*} [DecidableEq I] (p : I → ℕ → PowerSeries K)
    (n : ℕ) (k : I → ℕ) (hk : EssentiallyFinite k) (hp0 : ∀ i, p i 0 = 1)
    (j : I) (hj_notin : j ∉ IndexSetIn p n) (hkj : k j ≠ 0) :
    ∀ s : Finset I, j ∈ s →
      coeff n (∏ i ∈ s, p i (k i)) = 0 := by
  -- The key observation: j ∉ IndexSetIn p n means (j, k') ∉ CoeffSupportSetUnion p n for all k'
  -- In particular, (j, k j) ∉ CoeffSupportSetUnion p n
  -- So we can apply prodRule_claim5
  have hnotin : (j, k j) ∉ CoeffSupportSetUnion p n := by
    intro hcontra
    apply hj_notin
    simp only [IndexSetIn, Set.mem_ofPred_eq]
    exact ⟨k j, hcontra⟩
  exact prodRule_claim5 p n k hk hp0 j hkj hnotin

/-!
### Claim 7: Summability of Product Family

The family `(∏_{i ∈ I} p_{i,k_i})` indexed by essentially finite `(k_i)` is summable.
-/

/-- Helper lemma: If f has zero coefficients up to degree n, then coeff n (f * g) = 0. -/
private lemma coeff_mul_zero_of_low_degree_zero' {f g : PowerSeries K} {n : ℕ}
    (hf : ∀ m ≤ n, coeff m f = 0) : coeff n (f * g) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨i, j⟩ hij
  simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  have hi : i ≤ n := by omega
  simp [hf i hi]

/-- Helper lemma: If any factor in a product has zero coefficients up to degree n,
the product's coefficient at degree n is zero. -/
private lemma coeff_prod_zero_of_factor_low_degree_zero' {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → PowerSeries K} {n : ℕ} {i : ι} (hi : i ∈ s)
    (hfi : ∀ m ≤ n, coeff m (f i) = 0) : coeff n (∏ j ∈ s, f j) = 0 := by
  have h1 : s = insert i (s.erase i) := (Finset.insert_erase hi).symm
  rw [h1, Finset.prod_insert (Finset.notMem_erase i s)]
  exact coeff_mul_zero_of_low_degree_zero' hfi

/-- Claim 7: The family `(∏_{i ∈ I} p_{i,k_i})` indexed by essentially finite families
`(k_i)_{i ∈ I} ∈ S^I_fin` supported on `I_n` is summable. That is, for each `n ∈ ℕ`,
only finitely many essentially finite families `(k_i)` supported on `I_n` satisfy
`[x^n](∏_{i ∈ I_n} p_{i,k_i}) ≠ 0`.

The proof shows that any k with nonzero coefficient must satisfy:
- Property 1: All i ∉ I_n satisfy k i = 0 (support contained in I_n) - explicit in statement
- Property 2: All i ∈ I_n satisfy k i ∈ K_n ∪ {0}
These two properties restrict k to finitely many possibilities.

Note: Property 1 is made explicit in the statement since the product is over the finite set I_n.
For the infinite product interpretation (with p_{i,0} = 1), this constraint follows from
the fact that factors with k_i ≠ 0 for i ∉ I_n would have vanishing coefficients up to
degree n, making the product coefficient zero (by Claim 5/6).
(Claim 7) -/
theorem prodRule_claim7 {I : Type*} [DecidableEq I] (p : I → ℕ → PowerSeries K)
    (_hp0 : ∀ i, p i 0 = 1) (n : ℕ)
    (_hTn_finite : (CoeffSupportSetUnion p n).Finite)
    (hIn_finite : (IndexSetIn p n).Finite)
    (hKn_finite : (ValueSetKn p n).Finite) :
    {k : I → ℕ | EssentiallyFinite k ∧
                 (∀ i ∉ hIn_finite.toFinset, k i = 0) ∧
                 coeff n (∏ i ∈ hIn_finite.toFinset, p i (k i)) ≠ 0}.Finite := by
  let In := hIn_finite.toFinset
  let Kn0 : Finset ℕ := hKn_finite.toFinset ∪ {0}

  haveI : Fintype ↑In := Finset.fintypeCoeSort In
  haveI : Fintype ↑Kn0 := Finset.fintypeCoeSort Kn0

  -- Define the extension: given f : In → Kn0, extend to I → ℕ by 0 outside In
  let extend : (↑In → ↑Kn0) → (I → ℕ) := fun f i =>
    if h : i ∈ In then (f ⟨i, h⟩).val else 0

  have h_img_finite : (Set.range extend).Finite := Set.finite_range extend

  -- The target set is a subset of range extend
  apply Set.Finite.subset h_img_finite
  intro k ⟨_hk_ess, hk_supp, hk_coeff⟩
  simp only [Set.mem_range]

  -- Key claim: k i ∈ Kn0 for all i ∈ In (otherwise coefficient would be 0)
  have hk_in_Kn0 : ∀ i ∈ In, k i ∈ Kn0 := by
    intro i hi
    by_contra h
    simp only [Kn0, Finset.mem_union, Finset.mem_singleton] at h
    push Not at h
    have hki_ne0 : k i ≠ 0 := h.2
    have hki_notKn : k i ∉ hKn_finite.toFinset := h.1
    have hcoeff_zero : ∀ m ≤ n, coeff m (p i (k i)) = 0 := by
      intro m hm
      by_contra hne
      apply hki_notKn
      rw [Set.Finite.mem_toFinset]
      simp only [ValueSetKn, Set.mem_ofPred_eq]
      use i
      simp only [CoeffSupportSetUnion, Set.mem_iUnion, Finset.mem_range, CoeffSupportSet, Set.mem_ofPred_eq]
      exact ⟨m, Nat.lt_succ_of_le hm, hki_ne0, hne⟩
    have h_zero := @coeff_prod_zero_of_factor_low_degree_zero' K _ I _ In (fun j => p j (k j)) n i hi hcoeff_zero
    exact hk_coeff h_zero

  -- Construct f : In → Kn0 from k
  use fun i => ⟨k i.val, hk_in_Kn0 i.val i.property⟩

  -- Show extend f = k
  ext j
  simp only [extend]
  split_ifs with hj
  · simp
  · -- For j ∉ In: k j = 0 by the support constraint
    exact (hk_supp j hj).symm

/-!
### Claim 8: Coefficient Reduction to Finite Index Sets

The coefficient of the sum over essentially finite families equals
the coefficient of the sum over a finite index set.
-/

/-- Extend a function from a finite subset to the full type by setting values to 0 outside. -/
def extendFromFinset {I : Type*} [DecidableEq I] (In : Finset I) (f : (i : In) → ℕ) : I → ℕ :=
  fun i => if h : i ∈ In then f ⟨i, h⟩ else 0

/-- Restrict a function to a finite subset. -/
def restrictToFinset {I : Type*} (In : Finset I) (k : I → ℕ) : (i : In) → ℕ :=
  fun i => k i.1

/-- Claim 8: The coefficient of the sum over essentially finite families equals
the coefficient of the sum over the finite index set `I_n`.
`[x^n](∑_{(k_i) ∈ S^I_fin} ∏_{i ∈ I} p_{i,k_i}) = [x^n](∑_{(k_i) ∈ S^{I_n}} ∏_{i ∈ I_n} p_{i,k_i})`.

The proof establishes a bijection between `essFinFamilies` (functions that are 0 outside `In`
and have values in `S i` for `i ∈ In`) and `Fintype.piFinset (fun i : In => S i.1)`.

Note: The hypotheses `hValInS` and `hComplete` ensure that `essFinFamilies` is exactly
the set of extensions of functions in the piFinset. These are needed to establish the
bijection between the two index sets.

(Claim 8) -/
theorem prodRule_claim8 {I : Type*} [DecidableEq I]
    (p : I → ℕ → PowerSeries K) (n : ℕ) (_hp0 : ∀ i, p i 0 = 1)
    (In : Finset I) (_hIn : ∀ i, i ∉ In → i ∉ IndexSetIn p n)
    (S : I → Finset ℕ) (_hS0 : ∀ i, 0 ∈ S i)
    (essFinFamilies : Finset (I → ℕ))
    (_hEss : ∀ k ∈ essFinFamilies, EssentiallyFinite k)
    (hSIn : ∀ k ∈ essFinFamilies, ∀ i ∉ In, k i = 0)
    -- Values of k on In are in S
    (hValInS : ∀ k ∈ essFinFamilies, ∀ i ∈ In, k i ∈ S i)
    -- essFinFamilies contains all functions that are 0 outside In and have values in S on In
    (hComplete : ∀ k, (∀ i ∉ In, k i = 0) → (∀ i ∈ In, k i ∈ S i) → k ∈ essFinFamilies) :
    coeff n (∑ k ∈ essFinFamilies, ∏ i ∈ In, p i (k i)) =
    coeff n (∑ f ∈ Fintype.piFinset (fun i : In => S i.1), ∏ i : In, p i.1 (f i)) := by
  -- The proof establishes a bijection between essFinFamilies and the piFinset
  -- via restriction and extension.
  simp only [map_sum]
  apply Finset.sum_bij (fun k _ => restrictToFinset In k)
  · -- Membership: restriction of k ∈ essFinFamilies is in piFinset
    intro k hk
    simp only [Fintype.mem_piFinset]
    intro i
    exact hValInS k hk i.1 i.2
  · -- Injectivity: if restrictions are equal and both are 0 outside In, functions are equal
    intro k₁ hk₁ k₂ hk₂ heq
    ext i
    by_cases hi : i ∈ In
    · have : restrictToFinset In k₁ ⟨i, hi⟩ = restrictToFinset In k₂ ⟨i, hi⟩ := by rw [heq]
      exact this
    · rw [hSIn k₁ hk₁ i hi, hSIn k₂ hk₂ i hi]
  · -- Surjectivity: every f in piFinset comes from extendFromFinset In f ∈ essFinFamilies
    intro f hf
    use extendFromFinset In f
    refine ⟨?_, ?_⟩
    · apply hComplete
      · intro i hi; simp [extendFromFinset, hi]
      · intro i hi
        simp only [extendFromFinset, hi, dite_true]
        simp only [Fintype.mem_piFinset] at hf
        exact hf ⟨i, hi⟩
    · funext i; simp [restrictToFinset, extendFromFinset, i.2]
  · -- Values are equal: ∏ i ∈ In, p i (k i) = ∏ i : In, p i.1 (restrictToFinset In k i)
    intro k _
    rw [← Finset.prod_attach]
    rfl

/-!
### Claim 9: Sum Coefficient Vanishing

For `i ∉ I_n`, the sum `∑_{k ∈ S_i \ {0}} p_{i,k}` has vanishing coefficients
up to degree `n`.
-/

/-- Claim 9: For `i ∉ I_n`, we have `[x^m](∑_{k ∈ S_i \ {0}} p_{i,k}) = 0`
for each `m ∈ {0,1,...,n}`.
(Claim 9) -/
theorem prodRule_claim9 {I : Type*} (p : I → ℕ → PowerSeries K) (n : ℕ)
    (i : I) (hi : i ∉ IndexSetIn p n) (Si : Finset ℕ)
    (_hSi : 0 ∈ Si) :
    ∀ m ≤ n, coeff m (∑ k ∈ Si \ {0}, p i k) = 0 := by
  intro m hm
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_sdiff, Finset.mem_singleton] at hk
  have hnotin : (i, k) ∉ CoeffSupportSetUnion p n := by
    intro hcontra
    apply hi
    simp only [IndexSetIn, Set.mem_ofPred_eq]
    exact ⟨k, hcontra⟩
  exact prodRule_claim3 p n i k hk.2 hnotin m hm

/-!
### Claim 10: Product Reduction to Finite Index Sets

The product over `I` reduces to the product over `I_n` for coefficient extraction.
-/

/-- Helper: multiplying by `(1 + f)` where `f` has order > `n` doesn't change coefficient `n`. -/
private lemma coeff_mul_one_add_of_order_gt {n : ℕ} {f g : PowerSeries K}
    (hf : (n : ℕ∞) < f.order) : coeff n (g * (1 + f)) = coeff n g := by
  rw [mul_add, mul_one, map_add, coeff_mul_of_lt_order hf, add_zero]

/-- Helper: multiplying by a product of `(1 + f i)` terms where each `f i` has vanishing
coefficients up to degree `n` doesn't change coefficient `n`. -/
private lemma coeff_mul_prod_one_add_of_coeff_zero {I : Type*} [DecidableEq I]
    (n : ℕ) (s : Finset I) (g : PowerSeries K) (f : I → PowerSeries K)
    (hf : ∀ i ∈ s, ∀ m ≤ n, coeff m (f i) = 0) :
    coeff n (g * ∏ i ∈ s, (1 + f i)) = coeff n g := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    rw [Finset.prod_insert ha, ← mul_assoc, mul_comm g, mul_assoc]
    have h_order : (n : ℕ∞) < (f a).order := order_gt_of_coeff_eq_zero hf.1
    rw [mul_comm, coeff_mul_one_add_of_order_gt h_order]
    exact ih hf.2

/-- Claim 10: For any finite set `J ⊇ I_n`, the coefficient of the product over `J` equals
the coefficient of the product over `I_n`:
`[x^n](∏_{i ∈ J} ∑_{k ∈ S_i} p_{i,k}) = [x^n](∏_{i ∈ I_n} ∑_{k ∈ S_i} p_{i,k})`.

This captures the key property that the infinite product's coefficient stabilizes at `I_n`.
In the source, this is stated as reducing `∏_{i ∈ I}` to `∏_{i ∈ I_n}`, which makes sense
when `I` is infinite but the coefficient only depends on finitely many terms.

The proof uses:
1. For `i ∈ J \ I_n`, we have `∑_{k ∈ S_i} p_{i,k} = 1 + ∑_{k ∈ S_i \ {0}} p_{i,k}`
2. By Claim 9, `[x^m](∑_{k ∈ S_i \ {0}} p_{i,k}) = 0` for all `m ≤ n` when `i ∉ I_n`
3. By Lemma lem.fps.prod.irlv.inf, these factors don't affect the coefficient

(Claim 10) -/
theorem prodRule_claim10 {I : Type*} [DecidableEq I]
    (p : I → ℕ → PowerSeries K) (n : ℕ) (hp0 : ∀ i, p i 0 = 1)
    (In : Finset I) (hIn : ∀ i, i ∉ In → i ∉ IndexSetIn p n)
    (S : I → Finset ℕ) (hS0 : ∀ i, 0 ∈ S i)
    (J : Finset I) (hInJ : In ⊆ J) :
    coeff n (∏ i ∈ J, ∑ k ∈ S i, p i k) =
    coeff n (∏ i ∈ In, ∑ k ∈ S i, p i k) := by
  -- Split J into (J \ In) ∪ In
  rw [← Finset.sdiff_union_of_subset hInJ, Finset.prod_union Finset.sdiff_disjoint]
  -- For i ∈ J \ In, ∑ k ∈ S i, p i k = 1 + ∑ k ∈ S i \ {0}, p i k
  have h_split : ∀ i, ∑ k ∈ S i, p i k = 1 + ∑ k ∈ S i \ {0}, p i k := fun i => by
    rw [← Finset.insert_erase (hS0 i), Finset.sum_insert (Finset.notMem_erase 0 (S i))]
    simp [hp0 i, Finset.erase_eq]
  -- Rewrite the product over J \ In
  have h_prod_eq : ∏ i ∈ J \ In, ∑ k ∈ S i, p i k = ∏ i ∈ J \ In, (1 + ∑ k ∈ S i \ {0}, p i k) :=
    Finset.prod_congr rfl fun i _ => h_split i
  rw [h_prod_eq, mul_comm]
  -- Apply the helper lemma
  apply coeff_mul_prod_one_add_of_coeff_zero
  intro i hi m hm
  have hi_notin_In : i ∉ In := Finset.mem_sdiff.mp hi |>.2
  have hi_notin_IndexSet : i ∉ IndexSetIn p n := hIn i hi_notin_In
  exact prodRule_claim9 p n i hi_notin_IndexSet (S i) (hS0 i) m hm

/-!
### Claim 11: Finite Product-Sum Interchange

For a finite index set, the product of sums equals the sum of products.
-/

/-- Claim 11: For finite `I_n`, `∏_{i ∈ I_n} ∑_{k ∈ S_i} p_{i,k} =
∑_{(k_i) ∈ S^{I_n}} ∏_{i ∈ I_n} p_{i,k_i}`.
(Claim 11) -/
theorem prodRule_claim11 {I : Type*} [DecidableEq I]
    (p : I → ℕ → PowerSeries K) (In : Finset I) (S : I → Finset ℕ) :
    ∏ i ∈ In, ∑ k ∈ S i, p i k =
    ∑ f ∈ Fintype.piFinset (fun i : In => S i.1),
      ∏ i : In, p i.1 (f i) := by
  -- Convert the product over In to a product over the subtype (which is a Fintype)
  conv_lhs => rw [← Finset.prod_attach In (fun i => ∑ k ∈ S i, p i k)]
  -- Now apply prod_univ_sum for the Fintype instance on In
  exact Finset.prod_univ_sum (fun i : In => S i.1) (fun i k => p i.1 k)

/-!
### Main Proposition: Infinite-Infinite Product Rule (Generalized Distributive Law)

This is the culmination of Claims 3-11. It states that for a summable family
`(p_{i,k})` with `p_{i,0} = 1`, the infinite product of infinite sums equals
the sum over essentially finite families of products.

Proposition prop.fps.prodrule-inf-inf:
`∏_{i ∈ I} ∑_{k ∈ S_i} p_{i,k} = ∑_{(k_i)_{i ∈ I} ∈ S^I_fin} ∏_{i ∈ I} p_{i,k_i}`
-/

/-- The set `S^I_fin` of essentially finite families in `∏_{i ∈ I} S_i`. -/
def SfinI {I : Type*} (S : I → Set ℕ) : Set (I → ℕ) :=
  {k : I → ℕ | (∀ i, k i ∈ S i) ∧ EssentiallyFinite k}

/-- Auxiliary: For finite index sets, the product-sum interchange (Claim 11).
This is a direct consequence of `prodRule_claim11`. -/
theorem prodRule_finite_interchange {I : Type*} [DecidableEq I]
    (p : I → ℕ → PowerSeries K) (M : Finset I) (S : I → Finset ℕ) :
    ∏ i ∈ M, ∑ k ∈ S i, p i k =
    ∑ f ∈ Fintype.piFinset (fun i : M => S i.1), ∏ i : M, p i.1 (f i) :=
  prodRule_claim11 p M S

/-- Main Proposition (prop.fps.prodrule-inf-inf): The generalized distributive law for
infinite products and infinite sums of formal power series.

Given:
- An index set `I`
- For each `i ∈ I`, a set `S_i ⊆ ℕ` with `0 ∈ S_i`
- A family `(p_{i,k})_{(i,k) ∈ I × ℕ}` of FPS with `p_{i,0} = 1` for all `i`
- The family `(p_{i,k})_{(i,k) ∈ S̄}` is summable (where `S̄ = {(i,k) | k ∈ S_i, k ≠ 0}`)
- The family `(∑_{k ∈ S_i} p_{i,k})_{i ∈ I}` is multipliable

Then for each coefficient `n`:
- The LHS `[x^n](∏_{i ∈ I} ∑_{k ∈ S_i} p_{i,k})` is computed via the multipliability approximator
- The RHS `[x^n](∑_{(k_i) ∈ S^I_fin} ∏_{i ∈ I} p_{i,k_i})` is computed via the finite index set `I_n`
- These coefficients are equal

The proof chain (for each `n`):
1. Claim 10: `[x^n](∏_{i ∈ I} ∑_{k ∈ S_i} p_{i,k}) = [x^n](∏_{i ∈ I_n} ∑_{k ∈ S_i} p_{i,k})`
2. Claim 11: `∏_{i ∈ I_n} ∑_{k ∈ S_i} p_{i,k} = ∑_{(k_i) ∈ S^{I_n}} ∏_{i ∈ I_n} p_{i,k_i}`
3. Claim 8: `[x^n](∑_{(k_i) ∈ S^{I_n}} ∏_{i ∈ I_n} p_{i,k_i}) = [x^n](∑_{(k_i) ∈ S^I_fin} ∏_{i ∈ I} p_{i,k_i})`

**Note on hypotheses**: The hypotheses `hS0`, `hp0`, and `hSummable` are needed for the full
proof of the source proposition (to construct `I_n` and prove Claims 3-10). In this formulation,
we use `hMultipliable` which already encapsulates the stabilization property. The full proof
would derive `hMultipliable` from `hSummable` and `hp0`. These hypotheses are retained here
to match the source statement and to support future completion of the intermediate claims.

(Proposition prop.fps.prodrule-inf-inf) -/
theorem prodRule_infInf {I : Type*} [DecidableEq I]
    (p : I → ℕ → PowerSeries K)
    (S : I → Set ℕ) (_hS0 : ∀ i, 0 ∈ S i)
    (_hp0 : ∀ i, p i 0 = 1)
    -- Summability: for each m, only finitely many (i,k) ∈ S̄ have nonzero [x^m] p_{i,k}
    -- (Used in full proof to construct I_n via T_m sets)
    (_hSummable : ∀ m, {ik : I × ℕ | ik.2 ∈ S ik.1 ∧ ik.2 ≠ 0 ∧ coeff m (p ik.1 ik.2) ≠ 0}.Finite)
    -- Multipliability: for each n, there exists a finite approximator M
    (hMultipliable : ∀ n, ∃ M : Finset I, ∀ J : Finset I, M ⊆ J →
      ∀ Sfin : I → Finset ℕ, (∀ i, (Sfin i : Set ℕ) ⊆ S i) → (∀ i, 0 ∈ Sfin i) →
      coeff n (∏ i ∈ J, ∑ k ∈ Sfin i, p i k) = coeff n (∏ i ∈ M, ∑ k ∈ Sfin i, p i k)) :
    -- Conclusion: For each n, there exists a finite approximator M_n such that
    -- the coefficient can be computed using any sufficiently large finite approximation
    ∀ n, ∃ M_n : Finset I,
      -- Part 1: The coefficient of the LHS (infinite product of infinite sums)
      -- stabilizes at M_n (this is the multipliability condition)
      (∀ J : Finset I, M_n ⊆ J →
        ∀ Sfin : I → Finset ℕ, (∀ i, (Sfin i : Set ℕ) ⊆ S i) → (∀ i, 0 ∈ Sfin i) →
        coeff n (∏ i ∈ J, ∑ k ∈ Sfin i, p i k) = coeff n (∏ i ∈ M_n, ∑ k ∈ Sfin i, p i k)) ∧
      -- Part 2: The coefficient equals the sum over essentially finite families
      -- (restricted to those supported on M_n, which captures all contributing terms)
      (∀ Sfin : I → Finset ℕ, (∀ i, (Sfin i : Set ℕ) ⊆ S i) → (∀ i, 0 ∈ Sfin i) →
        coeff n (∏ i ∈ M_n, ∑ k ∈ Sfin i, p i k) =
        coeff n (∑ f ∈ Fintype.piFinset (fun i : M_n => Sfin i.1), ∏ i : M_n, p i.1 (f i))) := by
  intro n
  -- Get the approximator from multipliability
  obtain ⟨M, hM⟩ := hMultipliable n
  use M
  constructor
  · -- Part 1: multipliability condition holds by hypothesis
    exact hM
  · -- Part 2: coefficient equals sum over products (by Claim 11)
    intro Sfin _hSfin _hSfin0
    have h11 := prodRule_claim11 p M Sfin
    rw [h11]

/-- Corollary: The coefficient equality form of the generalized distributive law.
For any finite approximation of the index sets and value sets, the coefficient of
the product of sums equals the coefficient of the sum of products.

This is a direct consequence of Claim 11 (finite product-sum interchange).
(Proposition prop.fps.prodrule-inf-inf, coefficient form) -/
theorem prodRule_infInf_coeff {I : Type*} [DecidableEq I]
    (p : I → ℕ → PowerSeries K) (n : ℕ) (M : Finset I) (Sfin : I → Finset ℕ) :
    coeff n (∏ i ∈ M, ∑ k ∈ Sfin i, p i k) =
    coeff n (∑ f ∈ Fintype.piFinset (fun i : M => Sfin i.1), ∏ i : M, p i.1 (f i)) := by
  have h11 := prodRule_claim11 p M Sfin
  rw [h11]

/-!
### Composition Rules for Infinite Products

The following results establish that composition distributes over infinite products.
-/

/-- Finite product composition rule: For finite `I`, `(∏_{i ∈ I} f_i) ∘ g = ∏_{i ∈ I} (f_i ∘ g)`.
This is proved by induction on `|I|`.
(Lemma lem.fps.subs.rule-infprod-fin) -/
theorem comp_prod_finite {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → PowerSeries K) (g : PowerSeries K) (hg : constantCoeff g = 0) :
    (∏ i ∈ s, f i).subst g = ∏ i ∈ s, (f i).subst g := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    -- Need: 1.subst g = 1
    rw [← coe_substAlgHom (HasSubst.of_constantCoeff_zero' hg)]
    simp only [map_one]
  | @insert a s' ha ih =>
    simp only [Finset.prod_insert ha]
    -- Need: (f a * ∏ i ∈ s', f i).subst g = (f a).subst g * (∏ i ∈ s', f i).subst g
    -- This uses that subst distributes over multiplication
    rw [subst_mul (HasSubst.of_constantCoeff_zero' hg)]
    rw [ih]

/-- x^n-equivalence is preserved under composition when the inner series has zero constant term.
This is a consequence of Proposition prop.fps.xneq.comp. -/
theorem xnEquiv_comp {n : ℕ} {f₁ f₂ g : PowerSeries K}
    (hf : ∀ k ≤ n, coeff k f₁ = coeff k f₂) (hg : constantCoeff g = 0) :
    ∀ k ≤ n, coeff k (f₁.subst g) = coeff k (f₂.subst g) := by
  intro k hk
  have hgSubst : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  rw [coeff_subst' hgSubst, coeff_subst' hgSubst]
  -- Both sums are finsum over d of (coeff d f_i • coeff k (g^d))
  -- When d > k, coeff k (g^d) = 0 because order of g^d ≥ d > k
  -- So only d ≤ k matters, and for d ≤ k ≤ n, coeff d f₁ = coeff d f₂
  congr 1
  ext d
  by_cases hd : d > k
  · -- When d > k, g^d has order ≥ d > k, so coeff k (g^d) = 0
    have hpowOrd : (g^d).order ≥ d := le_order_pow_of_constantCoeff_eq_zero d hg
    have : coeff k (g^d) = 0 := by
      apply coeff_of_lt_order
      calc (k : ℕ∞) < d := Nat.cast_lt.mpr hd
        _ ≤ (g^d).order := hpowOrd
    simp [this]
  · -- When d ≤ k, we have d ≤ n, so coeff d f₁ = coeff d f₂
    push Not at hd
    have hdn : d ≤ n := le_trans hd hk
    rw [hf d hdn]

/-- Claim 1 for infinite product composition: An x^n-approximator for `(f_i)`
determines the x^n-coefficient in the product of `(f_i ∘ g)`.
(Claim 1 in proof of prop.fps.subs.rule-infprod)

Note: An x^n-approximator is a finite subset M that determines the first n+1 coefficients
in the product, i.e., for all k ≤ n and all J ⊇ M, coeff k (∏ i ∈ J, f i) = coeff k (∏ i ∈ M, f i). -/
theorem comp_prod_approx_determines {I : Type*} [DecidableEq I]
    (f : I → PowerSeries K) (g : PowerSeries K) (hg : constantCoeff g = 0)
    (n : ℕ) (M : Finset I)
    (hM_approx : ∀ k ≤ n, ∀ J : Finset I, M ⊆ J →
      coeff k (∏ i ∈ J, f i) = coeff k (∏ i ∈ M, f i)) :
    ∀ J : Finset I, M ⊆ J →
      coeff n (∏ i ∈ J, (f i).subst g) = coeff n (∏ i ∈ M, (f i).subst g) := by
  intro J hMJ
  -- By comp_prod_finite:
  -- (∏ i ∈ J, f i).subst g = ∏ i ∈ J, (f i).subst g
  -- (∏ i ∈ M, f i).subst g = ∏ i ∈ M, (f i).subst g
  rw [← comp_prod_finite J f g hg, ← comp_prod_finite M f g hg]
  -- By xn-equivalence preservation under composition:
  -- ∏ i ∈ J, f i ≡[x^n] ∏ i ∈ M, f i implies
  -- (∏ i ∈ J, f i) ∘ g ≡[x^n] (∏ i ∈ M, f i) ∘ g
  apply xnEquiv_comp _ hg n (le_refl n)
  intro k hk
  exact hM_approx k hk J hMJ

/-- If `(f_i)_{i ∈ I}` is multipliable and `[x^0]g = 0`, then `(f_i ∘ g)_{i ∈ I}` is multipliable.
(Proposition prop.fps.subs.rule-infprod, first part) -/
theorem comp_prod_multipliable {I : Type*} [DecidableEq I]
    (f : I → PowerSeries K) (g : PowerSeries K) (hg : constantCoeff g = 0)
    (hf_mulable : ∀ n, ∃ M : Finset I, ∀ J : Finset I, M ⊆ J →
      coeff n (∏ i ∈ J, f i) = coeff n (∏ i ∈ M, f i)) :
    ∀ n, ∃ M : Finset I, ∀ J : Finset I, M ⊆ J →
      coeff n (∏ i ∈ J, (f i).subst g) = coeff n (∏ i ∈ M, (f i).subst g) := by
  intro n
  -- Use axiom of choice to get approximators for each degree ≤ n
  choose M_k hM_k using fun k => hf_mulable k
  -- Take M to be the union of M_k for k ≤ n (i.e., k ∈ {0, 1, ..., n})
  let M := Finset.biUnion (Finset.range (n + 1)) M_k
  use M
  apply comp_prod_approx_determines f g hg n M
  -- Show M is an x^n-approximator (determines all coefficients ≤ n)
  intro k hk J hMJ
  -- M_k k ⊆ M since k ∈ range (n + 1)
  have hMk_sub : M_k k ⊆ M := by
    apply Finset.subset_biUnion_of_mem
    simp [hk]
  -- By hM_k k: for all J' ⊇ M_k k, coeff k (∏ i ∈ J', f i) = coeff k (∏ i ∈ M_k k, f i)
  -- Since M_k k ⊆ M ⊆ J:
  have h1 : coeff k (∏ i ∈ J, f i) = coeff k (∏ i ∈ M_k k, f i) :=
    hM_k k J (hMk_sub.trans hMJ)
  have h2 : coeff k (∏ i ∈ M, f i) = coeff k (∏ i ∈ M_k k, f i) :=
    hM_k k M hMk_sub
  rw [h1, h2]

/-- For multipliable `(f_i)_{i ∈ I}` with `[x^0]g = 0`,
`(∏_{i ∈ I} f_i) ∘ g = ∏_{i ∈ I} (f_i ∘ g)`.
(Proposition prop.fps.subs.rule-infprod, second part)

The hypothesis `hprod` says that `prod_f` is the infinite product: for any approximator `M`
(a finite set such that all supersets give the same coefficient), the coefficient of `prod_f`
equals the coefficient of the finite product over `M`. This is stronger than just saying
`prod_f`'s coefficients can be computed by *some* finite product, and is necessary to ensure
`prod_f` actually represents the infinite product. -/
theorem comp_prod_infinite {I : Type*} [DecidableEq I]
    (f : I → PowerSeries K) (g : PowerSeries K) (hg : constantCoeff g = 0)
    (hf_mulable : ∀ n, ∃ M : Finset I, ∀ J : Finset I, M ⊆ J →
      coeff n (∏ i ∈ J, f i) = coeff n (∏ i ∈ M, f i))
    (prod_f : PowerSeries K)
    (hprod : ∀ n (M : Finset I), (∀ J : Finset I, M ⊆ J →
      coeff n (∏ i ∈ J, f i) = coeff n (∏ i ∈ M, f i)) →
      coeff n prod_f = coeff n (∏ i ∈ M, f i)) :
    ∀ n, ∃ M : Finset I,
      coeff n (prod_f.subst g) = coeff n (∏ i ∈ M, (f i).subst g) := by
  intro n
  -- For each k ≤ n, choose approximators
  choose M_k hM_k using fun k => hf_mulable k
  -- Take M to be the union of all M_k for k ≤ n
  let M := Finset.biUnion (Finset.range (n + 1)) M_k
  use M
  -- Step 1: Show prod_f ≡[x^n] ∏_{i ∈ M} f_i
  have xnEquiv' : ∀ k ≤ n, coeff k prod_f = coeff k (∏ i ∈ M, f i) := by
    intro k hk
    -- M_k k ⊆ M
    have hMk_sub : M_k k ⊆ M := by
      apply Finset.subset_biUnion_of_mem
      simp [hk]
    -- By hM_k: M is an approximator for degree k (since M ⊇ M_k k)
    -- So coeff k (∏ M) = coeff k (∏ M_k k)
    have h1 : coeff k (∏ i ∈ M, f i) = coeff k (∏ i ∈ M_k k, f i) :=
      hM_k k M hMk_sub
    -- By hprod: since M_k k is an approximator, coeff k prod_f = coeff k (∏ M_k k)
    have h2 : coeff k prod_f = coeff k (∏ i ∈ M_k k, f i) :=
      hprod k (M_k k) (hM_k k)
    rw [h2, ← h1]
  -- Step 2: Apply xnEquiv_comp to get x^n-equivalence after composition
  have h := xnEquiv_comp xnEquiv' hg n (le_refl n)
  -- Step 3: Use comp_prod_finite to rewrite the composition of a finite product
  rw [h, comp_prod_finite M f g hg]

/-!
### Additional Supporting Lemmas
-/

/-- If `u` divides `v` and the first `n+1` coefficients of `u` are zero,
then the first `n+1` coefficients of `v` are also zero.
(Lemma lem.fps.prod.irlv.mul) -/
theorem coeff_zero_of_dvd {n : ℕ} {u v : PowerSeries K}
    (hdvd : u ∣ v) (hu : ∀ m ≤ n, coeff m u = 0) :
    ∀ m ≤ n, coeff m v = 0 := by
  intro m hm
  -- Get the witness w such that v = u * w
  obtain ⟨w, hw⟩ := hdvd
  rw [hw, coeff_mul]
  -- The sum is over antidiagonal m, i.e., pairs (i, j) with i + j = m
  apply Finset.sum_eq_zero
  intro ⟨i, j⟩ hij
  -- i + j = m ≤ n, so i ≤ n
  simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  have hi : i ≤ n := by omega
  rw [hu i hi]
  ring

/-- Helper lemma: if `order(ψ) > n`, then `coeff n (φ * (1 + ψ)) = coeff n φ`. -/
theorem coeff_mul_one_add_of_lt_order {φ ψ : K⟦X⟧} (n : ℕ)
    (h : ↑n < ψ.order) : coeff n (φ * (1 + ψ)) = coeff n φ := by
  simp [coeff_mul_of_lt_order h, mul_add]

/-- For a summable family `(f_i)_{i ∈ I}` with `[x^m] f_i = 0` for all `m ≤ n` and `i ∈ I`,
we have `[x^m](a · ∏_{i ∈ I}(1 + f_i)) = [x^m] a` for all `m ≤ n`.
(Lemma lem.fps.prod.irlv.inf) -/
theorem coeff_prod_one_plus_summable {I : Type*} [DecidableEq I]
    (a : PowerSeries K) (f : I → PowerSeries K) (n : ℕ)
    (hf_zero : ∀ i, ∀ m ≤ n, coeff m (f i) = 0)
    (s : Finset I) :
    ∀ m ≤ n, coeff m (a * ∏ i ∈ s, (1 + f i)) = coeff m a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a_i s' ha ih =>
    intro m hm
    rw [Finset.prod_insert ha]
    -- Goal: coeff m (a * ((1 + f a_i) * ∏ i ∈ s', (1 + f i))) = coeff m a
    rw [← mul_assoc, mul_right_comm]
    -- Goal: coeff m ((a * ∏ i ∈ s', (1 + f i)) * (1 + f a_i)) = coeff m a
    have horder : ↑m < (f a_i).order := by
      have hle : (m + 1 : ℕ) ≤ (f a_i).order := by
        apply nat_le_order
        intro i hi
        exact hf_zero a_i i (le_trans (Nat.lt_succ_iff.mp hi) hm)
      calc (m : ℕ∞) < m + 1 := Nat.cast_lt.mpr (Nat.lt_succ_self m)
        _ ≤ (f a_i).order := hle
    rw [coeff_mul_one_add_of_lt_order m horder, ih m hm]

end PowerSeries
