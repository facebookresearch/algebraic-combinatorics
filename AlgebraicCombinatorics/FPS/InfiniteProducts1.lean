/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import AlgebraicCombinatorics.FPS.InfiniteProducts
import AlgebraicCombinatorics.FPS.XnEquivalence

/-!
# Infinite Products of Formal Power Series (Part 1)

This file formalizes detailed proofs about infinite products of formal power series,
following the "Details: Infinite products (part 1)" section of the source.

## Relationship with `InfiniteProducts.lean`

This file (`InfiniteProducts1.lean`) re-exports the canonical definitions from
`InfiniteProducts.lean` (in the `PowerSeries` namespace) into the `AlgebraicCombinatorics.FPS` namespace.
The definitions are **definitionally equal**:

* `AlgebraicCombinatorics.FPS.Multipliable` := `PowerSeries.Multipliable`
* `AlgebraicCombinatorics.FPS.infprod` := `PowerSeries.tprod`
* `AlgebraicCombinatorics.FPS.DeterminesCoeff a n U` := `PowerSeries.DeterminesCoeffInProd a U n`
* `AlgebraicCombinatorics.FPS.CoeffFinitelyDetermined` := `PowerSeries.CoeffFinitelyDeterminedInProd`
* `AlgebraicCombinatorics.FPS.IsXnApproximator a n U` := `PowerSeries.IsXnApproximator a U n`

The `PowerSeries` namespace versions are canonical and recommended for new code.
The `AlgebraicCombinatorics.FPS` aliases are provided for consistency with other "Details" files.

**Key difference:** This file contains a fully proved version of SW1 (`multipliable_fiber_prods`,
`infprod_eq_infprod_fiber`) with the invertibility hypothesis (`hinv : ∀ s, IsUnit (constantCoeff (a s))`).
The `InfiniteProducts.lean` file has both:
- Fully proved `multipliable_prod_fibers_inv` / `tprod_eq_tprod_fibers_inv` (with invertibility)
- Sorry'd `multipliable_prod_fibers` / `tprod_eq_tprod_fibers` (without invertibility)

This file is kept separate to:
1. Follow the structure of the TeX source (Details: Infinite products part 1)
2. Provide detailed proofs of specific propositions from the source
3. Use the `AlgebraicCombinatorics.FPS` namespace for consistency with other "Details" files

## Main Definitions

* `AlgebraicCombinatorics.FPS.IsXnApproximator`: Alias for `PowerSeries.IsXnApproximator` with swapped argument order.
  A finite subset `U ⊆ I` is an x^n-approximator for a family `(aᵢ)_{i∈I}` if it determines
  the first `n+1` coefficients of the infinite product. (Definition def.fps.xnappr)

* `AlgebraicCombinatorics.FPS.Multipliable`: Alias for `PowerSeries.Multipliable`.
  A family of FPSs is multipliable if each coefficient in the product is finitely determined.
  (Definition def.fps.multipliable)

* `AlgebraicCombinatorics.FPS.infprod`: Alias for `PowerSeries.tprod`.
  The infinite product of a multipliable family of FPSs. (Definition def.fps.multipliable (b))

## Main Results

### Proposition prop.fps.union-mulable
* `multipliable_of_subset`: If `(aᵢ)_{i∈I}` is multipliable and `J ⊆ I`, then both
  `(aᵢ)_{i∈J}` and `(aᵢ)_{i∈I\J}` are multipliable.
* `infprod_union_eq`: The infinite product over `I` equals the product of
  infinite products over `J` and `I \ J`.

### Proposition prop.fps.prod-mulable
* `multipliable_mul`: If `(aᵢ)` and `(bᵢ)` are multipliable, so is `(aᵢ · bᵢ)`.
* `infprod_mul_eq`: The infinite product of `(aᵢ · bᵢ)` equals the product of
  the infinite products.

### Lemma lem.fps.prod.irlv.cong-div
* `xnEquiv_div`: If `a ≡ b` and `c ≡ d` (mod x^{n+1}) with `c, d` invertible,
  then `a/c ≡ b/d` (mod x^{n+1}).

### Proposition prop.fps.div-mulable
* `multipliable_div`: If `(aᵢ)` and `(bᵢ)` are multipliable with each `bᵢ` invertible,
  then `(aᵢ/bᵢ)` is multipliable.
* `infprod_div_eq`: The infinite product of `(aᵢ/bᵢ)` equals the quotient of
  the infinite products.

### Lemma lem.fps.prods-mulable-subfams-appr
* `xnApproximator_inter`: If `U` is an x^n-approximator for `(aᵢ)_{i∈I}`,
  then `U ∩ J` is an x^n-approximator for `(aᵢ)_{i∈J}`.

### Lemma lem.fps.prods-mulable-rules.SW1.lem1
* `xnEquiv_finprod`: If each `cᵥ ≡ dᵥ` (mod x^{n+1}), then `∏_{v∈V} cᵥ ≡ ∏_{v∈V} dᵥ`.

### Proposition prop.fps.prods-mulable-rules.SW1
* `multipliable_fiber_prods`: Infinite products can be reindexed along a surjection,
  grouping terms by fibers.
* `infprod_eq_infprod_fiber`: The infinite product over the source equals the infinite
  product over the target of fiber products.

## References

* Source: AlgebraicCombinatorics/tex/Details/InfiniteProducts1.tex

## Implementation Notes

This file re-exports the canonical definitions from `PowerSeries` namespace into
`AlgebraicCombinatorics.FPS` namespace using `abbrev`. The definitions are definitionally equal,
so all theorems work seamlessly with either namespace.

The key insight is that a family is multipliable if for each coefficient index `n`,
there exists a finite "approximating" set that determines that coefficient.
-/

open scoped Polynomial
open PowerSeries Finset

namespace AlgebraicCombinatorics

namespace FPS

variable {K : Type*} [CommRing K]

/-!
## x^n-Equivalence (Local Notation)

We use `PowerSeries.XnEquiv` from `XnEquivalence.lean` for the underlying definition.
The notation `f ≡[x^n] g` is imported from `Limits.lean` (via `InfiniteProducts.lean`).
-/

/-!
## Lemma lem.fps.prod.irlv.cong-mul

If `a ≡ b` and `c ≡ d` (mod x^{n+1}), then `a·c ≡ b·d` (mod x^{n+1}).
This is used in the proof of Proposition prop.fps.prod-mulable.
-/

/-- If coefficients agree up to n, products agree up to n.
    (Lemma lem.fps.prod.irlv.cong-mul)
    Label: lem.fps.prod.irlv.cong-mul -/
theorem xnEquiv_mul_of_coeff_eq {n : ℕ} {a b c d : K⟦X⟧}
    (hab : ∀ m ≤ n, coeff m a = coeff m b)
    (hcd : ∀ m ≤ n, coeff m c = coeff m d) :
    ∀ m ≤ n, coeff m (a * c) = coeff m (b * d) :=
  PowerSeries.XnEquiv.mul hab hcd

/-!
## Lemma lem.fps.prod.irlv.cong-div

If `a ≡ b` and `c ≡ d` (mod x^{n+1}) with `c, d` invertible,
then `a/c ≡ b/d` (mod x^{n+1}).

This is the division analogue of lem.fps.prod.irlv.cong-mul.
-/

/-- If coefficients agree up to n for numerators and invertible denominators,
    quotients agree up to n.
    (Lemma lem.fps.prod.irlv.cong-div)
    Label: lem.fps.prod.irlv.cong-div -/
theorem xnEquiv_div {n : ℕ} {a b c d : K⟦X⟧}
    (hab : a ≡[x^n] b) (hcd : c ≡[x^n] d)
    (hc : IsUnit (constantCoeff c)) (hd : IsUnit (constantCoeff d)) :
    a * invOfUnit c hc.unit ≡[x^n] b * invOfUnit d hd.unit := by
  -- First, show that the inverses are x^n-equivalent
  have hinv : invOfUnit c hc.unit ≡[x^n] invOfUnit d hd.unit := by
    apply PowerSeries.XnEquiv.invOfUnit hc.unit hd.unit
    · exact IsUnit.unit_spec hc
    · exact IsUnit.unit_spec hd
    · exact hcd
  -- Then use that multiplication preserves x^n-equivalence
  exact PowerSeries.XnEquiv.mul hab hinv

/-!
## x^n-Approximators and Multipliable Families

The definitions below are aliases for the canonical `PowerSeries` versions.
They are provided for consistency with other "Details" files and to maintain
the argument order used in this file.
-/

/-- Alias for `PowerSeries.DeterminesCoeffInProd` with swapped argument order.
    A finite subset `U ⊆ I` determines the x^n-coefficient in the product of `(aᵢ)_{i∈I}`
    if for every finite subset `T` with `U ⊆ T ⊆ I`, the x^n-coefficient of `∏_{i∈T} aᵢ`
    equals that of `∏_{i∈U} aᵢ`.
    (Definition def.fps.infprod.coeff-det) -/
abbrev DeterminesCoeff {ι : Type*} (a : ι → K⟦X⟧) (n : ℕ) (U : Finset ι) : Prop :=
  PowerSeries.DeterminesCoeffInProd a U n

/-- Alias for `PowerSeries.IsXnApproximator` with swapped argument order.
    A finite subset `U ⊆ I` is an x^n-approximator for `(aᵢ)_{i∈I}` if it determines
    the first `n+1` coefficients in the product.
    (Definition def.fps.xnappr)
    Label: def.fps.xnappr -/
abbrev IsXnApproximator {ι : Type*} (a : ι → K⟦X⟧) (n : ℕ) (U : Finset ι) : Prop :=
  PowerSeries.IsXnApproximator a U n

/-- Alias for `PowerSeries.CoeffFinitelyDeterminedInProd`.
    The x^n-coefficient in the product of `(aᵢ)_{i∈I}` is finitely determined if
    there exists a finite subset that determines it.
    (Definition def.fps.infprod.coeff-det) -/
abbrev CoeffFinitelyDetermined {ι : Type*} (a : ι → K⟦X⟧) (n : ℕ) : Prop :=
  PowerSeries.CoeffFinitelyDeterminedInProd a n

/-- Alias for `PowerSeries.Multipliable`.
    A family `(aᵢ)_{i∈I}` of FPSs is multipliable if each coefficient in the product
    is finitely determined.
    (Definition def.fps.multipliable)
    Label: def.fps.multipliable -/
abbrev Multipliable {ι : Type*} (a : ι → K⟦X⟧) : Prop :=
  PowerSeries.Multipliable a

/-- If a family is multipliable, there exists an x^n-approximator for each n.
    (Lemma lem.fps.mulable.approx)
    Label: lem.fps.mulable.approx -/
theorem multipliable_exists_approximator {ι : Type*} {a : ι → K⟦X⟧}
    (h : Multipliable a) (n : ℕ) : ∃ U : Finset ι, IsXnApproximator a n U := by
  classical
  -- Take the union of approximators for coefficients 0, 1, ..., n
  let U := Finset.biUnion (Finset.range (n + 1)) (fun m => (h m).choose)
  use U
  intro m hm T hUT
  -- (h m).choose ⊆ U ⊆ T, so T and U give the same m-th coefficient
  have hmem : (h m).choose ⊆ U := fun i hi =>
    Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm), hi⟩
  calc coeff m (∏ i ∈ T, a i)
      = coeff m (∏ i ∈ (h m).choose, a i) := (h m).choose_spec T (hmem.trans hUT)
    _ = coeff m (∏ i ∈ U, a i) := ((h m).choose_spec U hmem).symm

/-!
## The Infinite Product

The infinite product definitions are aliases for the canonical `PowerSeries` versions.
-/

/-- Alias for `PowerSeries.tprodCoeff`.
    The n-th coefficient of the infinite product of a multipliable family.
    This is well-defined because the coefficient is finitely determined. -/
noncomputable abbrev infprodCoeff {ι : Type*} (a : ι → K⟦X⟧) (h : Multipliable a) (n : ℕ) : K :=
  PowerSeries.tprodCoeff a h n

/-- Alias for `PowerSeries.tprod`.
    The infinite product of a multipliable family of FPSs.
    (Definition def.fps.multipliable (b))
    Label: def.fps.multipliable -/
noncomputable abbrev infprod {ι : Type*} (a : ι → K⟦X⟧) (h : Multipliable a) : K⟦X⟧ :=
  PowerSeries.tprod a h

notation "∏∞ " => infprod

/-- The n-th coefficient of the infinite product equals that of any approximating
    finite product.
    (Proposition prop.fps.infprod-approx-xneq (a))
    Label: prop.fps.infprod-approx-xneq -/
theorem coeff_infprod_eq_coeff_finprod {ι : Type*} {a : ι → K⟦X⟧} {n : ℕ}
    (h : Multipliable a) {U : Finset ι} (hU : DeterminesCoeff a n U) :
    coeff n (infprod a h) = coeff n (∏ i ∈ U, a i) := by
  classical
  simp only [infprod, PowerSeries.tprod, coeff_mk, PowerSeries.tprodCoeff]
  -- Both (h n).choose and U determine the n-th coefficient, so they give the same value
  -- We use the union (h n).choose ∪ U to connect them
  have hchoose : DeterminesCoeff a n (h n).choose := (h n).choose_spec
  -- Apply hchoose to the union
  have eq1 : coeff n (∏ i ∈ (h n).choose ∪ U, a i) = coeff n (∏ i ∈ (h n).choose, a i) :=
    hchoose ((h n).choose ∪ U) (subset_union_left)
  -- Apply hU to the union
  have eq2 : coeff n (∏ i ∈ (h n).choose ∪ U, a i) = coeff n (∏ i ∈ U, a i) :=
    hU ((h n).choose ∪ U) (subset_union_right)
  -- Combine: coeff ... (h n).choose = coeff ... U
  rw [← eq1, eq2]

/-- If `U` is an x^n-approximator, the infinite product is x^n-equivalent to the
    finite product over `U`.
    (Proposition prop.fps.infprod-approx-xneq (b))
    Label: prop.fps.infprod-approx-xneq -/
theorem infprod_xnEquiv_finprod {ι : Type*} {a : ι → K⟦X⟧} {n : ℕ}
    (h : Multipliable a) {U : Finset ι} (hU : IsXnApproximator a n U) :
    infprod a h ≡[x^n] ∏ i ∈ U, a i := by
  intro m hm
  simp only [infprod, PowerSeries.tprod, coeff_mk, PowerSeries.tprodCoeff]
  have hdet : DeterminesCoeff a m (h m).choose := (h m).choose_spec
  have hUdet : DeterminesCoeff a m U := hU m hm
  -- Both (h m).choose and U determine the m-th coefficient
  -- Use the union of both sets to show they give the same value
  classical
  let T := (h m).choose ∪ U
  have hTdet1 : coeff m (∏ i ∈ T, a i) = coeff m (∏ i ∈ (h m).choose, a i) :=
    hdet T Finset.subset_union_left
  have hTdet2 : coeff m (∏ i ∈ T, a i) = coeff m (∏ i ∈ U, a i) :=
    hUdet T Finset.subset_union_right
  rw [← hTdet1, hTdet2]

/-!
## Lemma lem.fps.prods-mulable-subfams-appr

If `U` is an x^n-approximator for `(aᵢ)_{i∈I}` (a family of invertible FPSs),
then `U ∩ J` is an x^n-approximator for `(aᵢ)_{i∈J}`.

This lemma is used in the proof of `multipliable_of_subset`.
-/

/-- The intersection of an approximator with a subset gives an approximator for the subfamily.
    (Lemma lem.fps.prods-mulable-subfams-appr)
    Label: lem.fps.prods-mulable-subfams-appr

    Given `U` an x^n-approximator for `(aᵢ)_{i∈I}` and `J ⊆ I` (as a Finset),
    there exists an x^n-approximator for `(aᵢ)_{i∈J}` derived from `U ∩ J`. -/
theorem xnApproximator_inter {ι : Type*} [DecidableEq ι] {a : ι → K⟦X⟧} {n : ℕ}
    {U : Finset ι} {J : Finset ι}
    (hU : IsXnApproximator a n U)
    (hinv : ∀ i, IsUnit (constantCoeff (a i))) :
    ∃ M : Finset J, IsXnApproximator (fun i : J => a i) n M := by
  -- The approximator is essentially U ∩ J, viewed as a Finset of J
  use (U ∩ J).subtype (fun i => i ∈ J)
  intro m hm T hMT

  -- Relate products over subtypes to products over the original type
  have prod_M : ∏ i ∈ (U ∩ J).subtype (fun i => i ∈ J), a i.val = ∏ i ∈ (U ∩ J), a i := by
    apply Finset.prod_bij (fun x _ => x.val)
    · intro x hx; simp only [Finset.mem_subtype] at hx; exact hx
    · intro x _ y _ hxy; exact Subtype.ext hxy
    · intro b hb
      refine ⟨⟨b, Finset.mem_of_mem_inter_right hb⟩, ?_, rfl⟩
      simp only [Finset.mem_subtype]; exact hb
    · intro x _; rfl

  have prod_T : ∏ i ∈ T, a i.val = ∏ i ∈ T.map ⟨Subtype.val, Subtype.val_injective⟩, a i := by
    rw [Finset.prod_map]; rfl

  -- T' = T.map ... is T viewed as a Finset of ι
  let T' := T.map ⟨Subtype.val, Subtype.val_injective⟩
  have hT'_sub_J : ∀ x ∈ T', x ∈ J := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.property

  -- T' ∪ U ⊇ U, so hU applies
  have hU_sub : U ⊆ T' ∪ U := Finset.subset_union_right

  -- T' and U \ J are disjoint (since T' ⊆ J and U \ J ⊆ Jᶜ)
  have disj1 : Disjoint T' (U \ J) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy
    have hxJ : x ∈ J := hT'_sub_J x hx
    have hyJ : y ∉ J := Finset.mem_sdiff.mp hy |>.2
    intro heq
    rw [heq] at hxJ
    exact hyJ hxJ

  -- U ∩ J ⊆ T' (because M ⊆ T means U ∩ J ⊆ T')
  have hUJ_sub_T' : U ∩ J ⊆ T' := by
    intro x hx
    rw [Finset.mem_map]
    have hxJ : x ∈ J := Finset.mem_inter.mp hx |>.2
    have hxM : ⟨x, hxJ⟩ ∈ (U ∩ J).subtype (fun i => i ∈ J) := by
      simp only [Finset.mem_subtype]; exact hx
    have hxT : ⟨x, hxJ⟩ ∈ T := hMT hxM
    exact ⟨⟨x, hxJ⟩, hxT, rfl⟩

  -- T' ∪ U = T' ∪ (U \ J) (since U = (U ∩ J) ∪ (U \ J) and U ∩ J ⊆ T')
  have union_eq : T' ∪ U = T' ∪ (U \ J) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro h
      rcases h with hT' | hU
      · left; exact hT'
      · by_cases hxJ : x ∈ J
        · left; exact hUJ_sub_T' (Finset.mem_inter.mpr ⟨hU, hxJ⟩)
        · right; exact ⟨hU, hxJ⟩
    · intro h
      rcases h with hT' | ⟨hU, _⟩
      · left; exact hT'
      · right; exact hU

  have prod_union1 : ∏ i ∈ T' ∪ (U \ J), a i = (∏ i ∈ T', a i) * (∏ i ∈ U \ J, a i) :=
    Finset.prod_union disj1

  have disj2 : Disjoint (U ∩ J) (U \ J) :=
    Finset.disjoint_of_subset_left inter_subset_right disjoint_sdiff

  have U_eq : U = (U ∩ J) ∪ (U \ J) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hxJ : x ∈ J
      · left; exact ⟨hx, hxJ⟩
      · right; exact ⟨hx, hxJ⟩
    · intro h
      rcases h with ⟨hU, _⟩ | ⟨hU, _⟩ <;> exact hU

  have prod_U : ∏ i ∈ U, a i = (∏ i ∈ U ∩ J, a i) * (∏ i ∈ U \ J, a i) := by
    conv_lhs => rw [U_eq]
    exact Finset.prod_union disj2

  -- The product over U \ J is invertible
  have prod_UJ_inv : IsUnit (constantCoeff (∏ i ∈ U \ J, a i)) := by
    rw [map_prod]
    exact IsUnit.prod_iff.mpr (fun i _ => hinv i)

  let Q := ∏ i ∈ U \ J, a i
  let Q_inv := invOfUnit Q prod_UJ_inv.unit
  have hQ_mul_inv : Q * Q_inv = 1 := mul_invOfUnit Q prod_UJ_inv.unit rfl

  -- Prove x^m-equivalence using the approximator property
  have h_xn : (∏ i ∈ T', a i) * Q ≡[x^m] (∏ i ∈ U ∩ J, a i) * Q := by
    intro k hk
    have hk_n : k ≤ n := le_trans hk hm
    have eq_k : coeff k (∏ i ∈ T' ∪ U, a i) = coeff k (∏ i ∈ U, a i) :=
      hU k hk_n (T' ∪ U) hU_sub
    rw [union_eq, prod_union1, prod_U] at eq_k
    exact eq_k

  -- Cancel Q using multiplication by Q_inv
  have h_xn' : ∏ i ∈ T', a i ≡[x^m] ∏ i ∈ U ∩ J, a i := by
    have h1 : (∏ i ∈ T', a i) * Q * Q_inv ≡[x^m] (∏ i ∈ U ∩ J, a i) * Q * Q_inv := by
      apply PowerSeries.XnEquiv.mul h_xn
      exact PowerSeries.XnEquiv.refl m Q_inv
    simp only [mul_assoc, hQ_mul_inv, mul_one] at h1
    exact h1

  rw [prod_T, prod_M]
  exact h_xn' m le_rfl

/-!
## Proposition prop.fps.union-mulable (prop.fps.prods-mulable-subfams)

If `(aᵢ)_{i∈I}` is a multipliable family of invertible FPSs and `J ⊆ I`,
then both `(aᵢ)_{i∈J}` and `(aᵢ)_{i∈I\J}` are multipliable, and
`∏_{i∈I} aᵢ = (∏_{i∈J} aᵢ) · (∏_{i∈I\J} aᵢ)`.
-/

/-- Helper: constant coefficient of a finite product equals product of constant coefficients. -/
private lemma constantCoeff_prod' {ι : Type*} [DecidableEq ι] {S : Finset ι} {f : ι → K⟦X⟧} :
    constantCoeff (∏ i ∈ S, f i) = ∏ i ∈ S, constantCoeff (f i) := by
  simp only [map_prod]

/-- Helper: product of units is a unit. -/
private lemma isUnit_prod_of_isUnit' {ι : Type*} [DecidableEq ι] {S : Finset ι} {f : ι → K}
    (h : ∀ i ∈ S, IsUnit (f i)) : IsUnit (∏ i ∈ S, f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.prod_insert has]
    exact (h a (Finset.mem_insert_self a s)).mul (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Helper: if U is an x^n-approximator, products over extensions are x^n-equivalent to the base. -/
private lemma xnEquiv_of_isXnApproximator' {ι : Type*} [DecidableEq ι] {a : ι → K⟦X⟧} {n : ℕ}
    {U T : Finset ι} (hU : IsXnApproximator a n U) (hUT : U ⊆ T) :
    ∏ i ∈ T, a i ≡[x^n] ∏ i ∈ U, a i := by
  intro m hm
  exact hU m hm T hUT

/-- Helper: if A * P ≡ B * P (mod x^{n+1}) and P has invertible constant coeff, then A ≡ B. -/
private lemma xnEquiv_of_mul_xnEquiv_right' {n : ℕ} {A B P : K⟦X⟧}
    (h : A * P ≡[x^n] B * P) (hP : IsUnit (constantCoeff P)) :
    A ≡[x^n] B := by
  obtain ⟨u, hu⟩ := hP
  have hu' : constantCoeff P = u := hu.symm
  have step1 : A ≡[x^n] A * (P * invOfUnit P u) := by
    intro m hm
    rw [mul_invOfUnit P u hu', mul_one]
  have step2 : A * (P * invOfUnit P u) ≡[x^n] (A * P) * invOfUnit P u := by
    intro m hm
    ring_nf
  have step3 : (A * P) * invOfUnit P u ≡[x^n] (B * P) * invOfUnit P u := by
    apply PowerSeries.XnEquiv.mul h
    exact PowerSeries.XnEquiv.refl n _
  have step4 : (B * P) * invOfUnit P u ≡[x^n] B * (P * invOfUnit P u) := by
    intro m hm
    ring_nf
  have step5 : B * (P * invOfUnit P u) ≡[x^n] B := by
    intro m hm
    rw [mul_invOfUnit P u hu', mul_one]
  exact PowerSeries.XnEquiv.trans step1 (PowerSeries.XnEquiv.trans step2 (PowerSeries.XnEquiv.trans step3 (PowerSeries.XnEquiv.trans step4 step5)))

/-- Subfamilies of a multipliable family of invertible FPSs are multipliable.
    (Proposition prop.fps.union-mulable (a) / prop.fps.prods-mulable-subfams)
    Label: prop.fps.union-mulable

    Note: This is also known as `multipliable_subfamily` in the source.
    The proof uses `xnApproximator_inter` (lem.fps.prods-mulable-subfams-appr). -/
theorem multipliable_of_subset {ι : Type*} {a : ι → K⟦X⟧} {J : Set ι}
    (h : Multipliable a) (hinv : ∀ i, IsUnit (constantCoeff (a i))) :
    Multipliable (fun i : J => a i) := by
  classical
  intro n
  -- Construct an x^n-approximator by taking the union of determiners for all m ≤ n
  let U := Finset.biUnion (Finset.range (n + 1)) (fun m =>
    if hm : m ≤ n then (h m).choose else ∅)
  -- U is an x^n-approximator
  have hU_approx : IsXnApproximator a n U := by
    intro m hm T hUT
    have hUm_subset_U : (h m).choose ⊆ U := by
      intro i hi
      simp only [Finset.mem_biUnion, Finset.mem_range, U]
      use m
      constructor
      · omega
      · simp only [hm, dite_true]
        exact hi
    have hUm_subset_T : (h m).choose ⊆ T := hUm_subset_U.trans hUT
    have h1 := (h m).choose_spec T hUm_subset_T
    have h2 := (h m).choose_spec U hUm_subset_U
    rw [h1, h2]
  -- The determiner for the subfamily is U ∩ J
  let UJ := U.subtype (· ∈ J)
  use UJ
  intro T hUT
  -- Convert to products over ι
  let T' := T.map ⟨Subtype.val, Subtype.val_injective⟩
  let UJ' := U.filter (· ∈ J)
  let UnotJ := U.filter (· ∉ J)
  -- Products over subtypes equal products over images
  have prodT : ∏ i ∈ T, a i.val = ∏ i ∈ T', a i := by
    simp only [T', Finset.prod_map, Function.Embedding.coeFn_mk]
  have prodUJ : ∏ i ∈ UJ, a i.val = ∏ i ∈ UJ', a i := by
    have h1 : UJ.map ⟨Subtype.val, Subtype.val_injective⟩ = UJ' := by
      ext x
      simp only [UJ, UJ', Finset.mem_map, Finset.mem_subtype, Finset.mem_filter,
                 Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨y, hy⟩, hyU, rfl⟩; exact ⟨hyU, hy⟩
      · intro ⟨hxU, hxJ⟩; exact ⟨⟨x, hxJ⟩, hxU, rfl⟩
    rw [← h1, Finset.prod_map]
    simp only [Function.Embedding.coeFn_mk]
  -- T' ⊆ J and UnotJ ⊆ Jᶜ, so they're disjoint
  have hT'_subset_J : ∀ i ∈ T', i ∈ J := by
    intro i hi
    simp only [T', Finset.mem_map, Function.Embedding.coeFn_mk] at hi
    obtain ⟨⟨j, hj⟩, _, rfl⟩ := hi
    exact hj
  have disj_T'_UnotJ : Disjoint T' UnotJ := by
    rw [Finset.disjoint_left]
    intro i hiT' hiUnotJ
    simp only [UnotJ, Finset.mem_filter] at hiUnotJ
    exact hiUnotJ.2 (hT'_subset_J i hiT')
  have disj_UJ'_UnotJ : Disjoint UJ' UnotJ := by
    rw [Finset.disjoint_left]
    intro i hiUJ' hiUnotJ
    simp only [UJ', UnotJ, Finset.mem_filter] at hiUJ' hiUnotJ
    exact hiUnotJ.2 hiUJ'.2
  have union_UJ'_UnotJ : UJ' ∪ UnotJ = U := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, UJ', UnotJ]
    constructor
    · intro h'; rcases h' with ⟨hi, _⟩ | ⟨hi, _⟩ <;> exact hi
    · intro hi
      by_cases hiJ : i ∈ J
      · left; exact ⟨hi, hiJ⟩
      · right; exact ⟨hi, hiJ⟩
  -- UJ' ⊆ T'
  have UJ'_subset_T' : UJ' ⊆ T' := by
    intro i hi
    simp only [UJ', Finset.mem_filter] at hi
    simp only [T', Finset.mem_map, Function.Embedding.coeFn_mk]
    refine ⟨⟨i, hi.2⟩, ?_, rfl⟩
    apply hUT
    simp only [UJ, Finset.mem_subtype]
    exact hi.1
  have U_subset_T'_union_UnotJ : U ⊆ T' ∪ UnotJ := by
    intro i hi
    rw [← union_UJ'_UnotJ] at hi
    simp only [Finset.mem_union, UJ', UnotJ, Finset.mem_filter] at hi ⊢
    rcases hi with ⟨hiU, hiJ⟩ | ⟨hiU, hniJ⟩
    · left
      apply UJ'_subset_T'
      simp only [UJ', Finset.mem_filter]
      exact ⟨hiU, hiJ⟩
    · right
      exact ⟨hiU, hniJ⟩
  -- By x^n-approximator property: ∏ (T' ∪ UnotJ) ≡ ∏ U (mod x^{n+1})
  have equiv1 : ∏ i ∈ T' ∪ UnotJ, a i ≡[x^n] ∏ i ∈ U, a i :=
    xnEquiv_of_isXnApproximator' hU_approx U_subset_T'_union_UnotJ
  -- Rewrite products using disjoint unions
  have eq_T'_UnotJ : ∏ i ∈ T' ∪ UnotJ, a i = (∏ i ∈ T', a i) * (∏ i ∈ UnotJ, a i) :=
    Finset.prod_union disj_T'_UnotJ
  have eq_U : ∏ i ∈ U, a i = (∏ i ∈ UJ', a i) * (∏ i ∈ UnotJ, a i) := by
    rw [← union_UJ'_UnotJ, Finset.prod_union disj_UJ'_UnotJ]
  -- So: (∏ T') * (∏ UnotJ) ≡ (∏ UJ') * (∏ UnotJ) (mod x^{n+1})
  rw [eq_T'_UnotJ, eq_U] at equiv1
  -- ∏ UnotJ has invertible constant coefficient
  have hP_inv : IsUnit (constantCoeff (∏ i ∈ UnotJ, a i)) := by
    rw [constantCoeff_prod']
    apply isUnit_prod_of_isUnit'
    intro i _
    exact hinv i
  -- By cancellation: ∏ T' ≡ ∏ UJ' (mod x^{n+1})
  have equiv2 : ∏ i ∈ T', a i ≡[x^n] ∏ i ∈ UJ', a i :=
    xnEquiv_of_mul_xnEquiv_right' equiv1 hP_inv
  -- In particular, the n-th coefficients are equal
  calc coeff n (∏ i ∈ T, a i.val)
      = coeff n (∏ i ∈ T', a i) := by rw [prodT]
    _ = coeff n (∏ i ∈ UJ', a i) := equiv2 n le_rfl
    _ = coeff n (∏ i ∈ UJ, a i.val) := by rw [prodUJ]

/-- The infinite product splits over a disjoint union.
    (Proposition prop.fps.union-mulable (b))
    Label: prop.fps.union-mulable -/
theorem infprod_union_eq {ι : Type*} {a : ι → K⟦X⟧} {J : Set ι}
    (h : Multipliable a) (_hinv : ∀ i, IsUnit (constantCoeff (a i)))
    (hJ : Multipliable (fun i : J => a i))
    (hJc : Multipliable (fun i : ↑Jᶜ => a i)) :
    infprod a h = infprod (fun i : J => a i) hJ * infprod (fun i : ↑Jᶜ => a i) hJc := by
  classical
  ext n
  -- Build x^n-approximators for all three products from multipliable hypotheses
  let U := Finset.biUnion (Finset.range (n + 1)) (fun m => (h m).choose)
  have hU : IsXnApproximator a n U := by
    intro m hm T hT
    have hm_in_range : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    have h_sub : (h m).choose ⊆ U := Finset.subset_biUnion_of_mem (fun m => (h m).choose) hm_in_range
    have hdet : DeterminesCoeff a m (h m).choose := (h m).choose_spec
    have h1 : coeff m (∏ i ∈ T, a i) = coeff m (∏ i ∈ (h m).choose, a i) := hdet T (h_sub.trans hT)
    have h2 : coeff m (∏ i ∈ U, a i) = coeff m (∏ i ∈ (h m).choose, a i) := hdet U h_sub
    rw [h1, ← h2]
  let UJ := Finset.biUnion (Finset.range (n + 1)) (fun m => (hJ m).choose)
  have hUJ : IsXnApproximator (fun i : J => a i) n UJ := by
    intro m hm T hT
    have hm_in_range : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    have h_sub : (hJ m).choose ⊆ UJ := Finset.subset_biUnion_of_mem (fun m => (hJ m).choose) hm_in_range
    have hdet : DeterminesCoeff (fun i : J => a i) m (hJ m).choose := (hJ m).choose_spec
    have h1 : coeff m (∏ i ∈ T, (fun j : J => a j) i) = coeff m (∏ i ∈ (hJ m).choose, (fun j : J => a j) i) := hdet T (h_sub.trans hT)
    have h2 : coeff m (∏ i ∈ UJ, (fun j : J => a j) i) = coeff m (∏ i ∈ (hJ m).choose, (fun j : J => a j) i) := hdet UJ h_sub
    rw [h1, ← h2]
  let UJc := Finset.biUnion (Finset.range (n + 1)) (fun m => (hJc m).choose)
  have hUJc : IsXnApproximator (fun i : ↑Jᶜ => a i) n UJc := by
    intro m hm T hT
    have hm_in_range : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    have h_sub : (hJc m).choose ⊆ UJc := Finset.subset_biUnion_of_mem (fun m => (hJc m).choose) hm_in_range
    have hdet : DeterminesCoeff (fun i : ↑Jᶜ => a i) m (hJc m).choose := (hJc m).choose_spec
    have h1 : coeff m (∏ i ∈ T, (fun j : ↑Jᶜ => a j) i) = coeff m (∏ i ∈ (hJc m).choose, (fun j : ↑Jᶜ => a j) i) := hdet T (h_sub.trans hT)
    have h2 : coeff m (∏ i ∈ UJc, (fun j : ↑Jᶜ => a j) i) = coeff m (∏ i ∈ (hJc m).choose, (fun j : ↑Jᶜ => a j) i) := hdet UJc h_sub
    rw [h1, ← h2]
  -- Map UJ and UJc back to Finset ι and take union
  let UJ' : Finset ι := UJ.map ⟨Subtype.val, Subtype.val_injective⟩
  let UJc' : Finset ι := UJc.map ⟨Subtype.val, Subtype.val_injective⟩
  let W := U ∪ UJ' ∪ UJc'
  have hW_supset_U : U ⊆ W := subset_union_left.trans subset_union_left
  have hW_supset_UJ' : UJ' ⊆ W := subset_union_right.trans subset_union_left
  have hW_supset_UJc' : UJc' ⊆ W := subset_union_right
  -- W is an x^n-approximator for the full family
  have hW_approx : IsXnApproximator a n W := fun m hm T hT => by
    have h1 : coeff m (∏ i ∈ T, a i) = coeff m (∏ i ∈ U, a i) := hU m hm T (hW_supset_U.trans hT)
    have h2 : coeff m (∏ i ∈ W, a i) = coeff m (∏ i ∈ U, a i) := hU m hm W hW_supset_U
    rw [h1, ← h2]
  -- W.subtype (· ∈ J) is an x^n-approximator for J-subfamily
  have hWJ_approx : IsXnApproximator (fun i : J => a i) n (W.subtype (· ∈ J)) := fun m hm T hT => by
    have hUJ_sub : UJ ⊆ W.subtype (· ∈ J) := fun ⟨x, hx⟩ hxUJ => by
      simp only [mem_subtype]
      exact hW_supset_UJ' (mem_map.mpr ⟨⟨x, hx⟩, hxUJ, rfl⟩)
    have h1 : coeff m (∏ j ∈ T, (fun i : J => a i) j) = coeff m (∏ j ∈ UJ, (fun i : J => a i) j) := 
      hUJ m hm T (hUJ_sub.trans hT)
    have h2 : coeff m (∏ j ∈ W.subtype (· ∈ J), (fun i : J => a i) j) = coeff m (∏ j ∈ UJ, (fun i : J => a i) j) := 
      hUJ m hm (W.subtype (· ∈ J)) hUJ_sub
    rw [h1, ← h2]
  -- W.subtype (· ∈ Jᶜ) is an x^n-approximator for Jᶜ-subfamily
  have hWJc_approx : IsXnApproximator (fun i : ↑Jᶜ => a i) n (W.subtype (· ∈ Jᶜ)) := fun m hm T hT => by
    have hUJc_sub : UJc ⊆ W.subtype (· ∈ Jᶜ) := fun ⟨x, hx⟩ hxUJc => by
      simp only [mem_subtype]
      exact hW_supset_UJc' (mem_map.mpr ⟨⟨x, hx⟩, hxUJc, rfl⟩)
    have h1 : coeff m (∏ j ∈ T, (fun i : ↑Jᶜ => a i) j) = coeff m (∏ j ∈ UJc, (fun i : ↑Jᶜ => a i) j) := 
      hUJc m hm T (hUJc_sub.trans hT)
    have h2 : coeff m (∏ j ∈ W.subtype (· ∈ Jᶜ), (fun i : ↑Jᶜ => a i) j) = coeff m (∏ j ∈ UJc, (fun i : ↑Jᶜ => a i) j) := 
      hUJc m hm (W.subtype (· ∈ Jᶜ)) hUJc_sub
    rw [h1, ← h2]
  -- Main computation
  have h1 : coeff n (infprod a h) = coeff n (∏ i ∈ W, a i) := by
    simp only [infprod, PowerSeries.tprod, coeff_mk, PowerSeries.tprodCoeff]
    let V' := (h n).choose
    have hV' : DeterminesCoeff a n V' := (h n).choose_spec
    rw [← hV' (V' ∪ W) subset_union_left, (hW_approx n le_rfl) (V' ∪ W) subset_union_right]
  have h2 : ∏ i ∈ W, a i = (∏ i ∈ W.filter (· ∈ J), a i) * (∏ i ∈ W.filter (· ∉ J), a i) := by
    rw [← prod_union (disjoint_filter_filter_not W W (· ∈ J))]
    congr 1; exact (filter_union_filter_not_eq (· ∈ J) W).symm
  have h3 : ∏ i ∈ W.filter (· ∈ J), a i = ∏ j ∈ W.subtype (· ∈ J), (fun i : J => a i) j := by
    rw [← prod_subtype_eq_prod_filter]
  have h4 : ∏ i ∈ W.filter (· ∉ J), a i = ∏ j ∈ W.subtype (· ∈ Jᶜ), (fun i : ↑Jᶜ => a i) j := by
    conv_lhs => rw [← prod_subtype_eq_prod_filter]
    have heq : (W.subtype (· ∉ J)) = (W.subtype (· ∈ Jᶜ)) := by ext ⟨x, hx⟩; simp only [mem_subtype]
    simp only [heq]; rfl
  have h5 : ∀ m ≤ n, coeff m (infprod (fun i : J => a i) hJ) = 
      coeff m (∏ j ∈ W.subtype (· ∈ J), (fun i : J => a i) j) := by
    intro m hm
    simp only [infprod, PowerSeries.tprod, coeff_mk, PowerSeries.tprodCoeff]
    let V' := (hJ m).choose
    have hV' : DeterminesCoeff (fun i : J => a i) m V' := (hJ m).choose_spec
    rw [← hV' (V' ∪ W.subtype (· ∈ J)) subset_union_left, (hWJ_approx m hm) (V' ∪ W.subtype (· ∈ J)) subset_union_right]
  have h6 : ∀ m ≤ n, coeff m (infprod (fun i : ↑Jᶜ => a i) hJc) = 
      coeff m (∏ j ∈ W.subtype (· ∈ Jᶜ), (fun i : ↑Jᶜ => a i) j) := by
    intro m hm
    simp only [infprod, PowerSeries.tprod, coeff_mk, PowerSeries.tprodCoeff]
    let V' := (hJc m).choose
    have hV' : DeterminesCoeff (fun i : ↑Jᶜ => a i) m V' := (hJc m).choose_spec
    rw [← hV' (V' ∪ W.subtype (· ∈ Jᶜ)) subset_union_left, (hWJc_approx m hm) (V' ∪ W.subtype (· ∈ Jᶜ)) subset_union_right]
  have h7 : coeff n (infprod (fun i : J => a i) hJ * infprod (fun i : ↑Jᶜ => a i) hJc) = 
      coeff n ((∏ j ∈ W.subtype (· ∈ J), (fun i : J => a i) j) * (∏ j ∈ W.subtype (· ∈ Jᶜ), (fun i : ↑Jᶜ => a i) j)) := by
    simp only [coeff_mul]
    apply Finset.sum_congr rfl
    intro ⟨i, j⟩ hij
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [h5 i (by omega), h6 j (by omega)]
  rw [h1, h2, h3, h4, h7]

/-!
## Proposition prop.fps.prod-mulable

If `(aᵢ)_{i∈I}` and `(bᵢ)_{i∈I}` are multipliable families, then so is `(aᵢ · bᵢ)_{i∈I}`,
and `∏_{i∈I} (aᵢ · bᵢ) = (∏_{i∈I} aᵢ) · (∏_{i∈I} bᵢ)`.
-/

/-- Part (a): The pointwise product of multipliable families is multipliable.
    (Proposition prop.fps.prod-mulable (a))
    Label: prop.fps.prod-mulable -/
theorem multipliable_mul {ι : Type*} {a b : ι → K⟦X⟧}
    (ha : Multipliable a) (hb : Multipliable b) :
    Multipliable (fun i => a i * b i) := by
  intro n
  -- For each coefficient m ≤ n, we need approximators for a and b
  -- We build a single approximator that works for all m ≤ n
  classical
  -- Get determiners for all coefficients m ≤ n for both families
  let Ua := (Finset.range (n + 1)).biUnion (fun m => (ha m).choose)
  let Ub := (Finset.range (n + 1)).biUnion (fun m => (hb m).choose)
  let U := Ua ∪ Ub
  -- U determines coefficient n for the product family
  use U
  intro T hUT
  -- Key observation: ∏ (a_i * b_i) = (∏ a_i) * (∏ b_i)
  simp only [Finset.prod_mul_distrib]
  -- We need to show:
  -- coeff n ((∏ i ∈ T, a i) * (∏ i ∈ T, b i)) = coeff n ((∏ i ∈ U, a i) * (∏ i ∈ U, b i))
  --
  -- By coeff_mul, this reduces to showing that for all m ≤ n:
  -- - coeff m (∏ i ∈ T, a i) = coeff m (∏ i ∈ U, a i)
  -- - coeff (n-m) (∏ i ∈ T, b i) = coeff (n-m) (∏ i ∈ U, b i)
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨p, q⟩ hpq
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
  -- p + q = n, so p ≤ n and q ≤ n
  have hp : p ≤ n := by omega
  have hq : q ≤ n := by omega
  -- Ua determines coefficient p for a
  have ha_p_det : DeterminesCoeff a p (ha p).choose := (ha p).choose_spec
  have hUa_p_sub : (ha p).choose ⊆ Ua := by
    intro x hx
    rw [Finset.mem_biUnion]
    exact ⟨p, Finset.mem_range.mpr (Nat.lt_succ_of_le hp), hx⟩
  have hU_a_sub : Ua ⊆ U := Finset.subset_union_left
  have hU_p_det_a : DeterminesCoeff a p U := fun T' hT' => by
    have h1 := ha_p_det T' ((hUa_p_sub.trans hU_a_sub).trans hT')
    have h2 := ha_p_det U (hUa_p_sub.trans hU_a_sub)
    rw [h1, ← h2]
  -- Ub determines coefficient q for b
  have hb_q_det : DeterminesCoeff b q (hb q).choose := (hb q).choose_spec
  have hUb_q_sub : (hb q).choose ⊆ Ub := by
    intro x hx
    rw [Finset.mem_biUnion]
    exact ⟨q, Finset.mem_range.mpr (Nat.lt_succ_of_le hq), hx⟩
  have hU_b_sub : Ub ⊆ U := Finset.subset_union_right
  have hU_q_det_b : DeterminesCoeff b q U := fun T' hT' => by
    have h1 := hb_q_det T' ((hUb_q_sub.trans hU_b_sub).trans hT')
    have h2 := hb_q_det U (hUb_q_sub.trans hU_b_sub)
    rw [h1, ← h2]
  -- Now apply these to T and U
  have eq_a : coeff p (∏ i ∈ T, a i) = coeff p (∏ i ∈ U, a i) := hU_p_det_a T hUT
  have eq_b : coeff q (∏ i ∈ T, b i) = coeff q (∏ i ∈ U, b i) := hU_q_det_b T hUT
  rw [eq_a, eq_b]

/-- Part (b): The infinite product of pointwise products equals the product of
    infinite products.
    (Proposition prop.fps.prod-mulable (b))
    Label: prop.fps.prod-mulable -/
theorem infprod_mul_eq {ι : Type*} {a b : ι → K⟦X⟧}
    (ha : Multipliable a) (hb : Multipliable b)
    (hab : Multipliable (fun i => a i * b i)) :
    infprod (fun i => a i * b i) hab = infprod a ha * infprod b hb := by
  classical
  ext n
  -- Helper: if U determines coefficient m, and V ⊇ U, then V also determines coefficient m
  have DeterminesCoeff_of_superset : ∀ {c : ι → K⟦X⟧} {m : ℕ} {U V : Finset ι},
      DeterminesCoeff c m U → U ⊆ V → DeterminesCoeff c m V := by
    intro c m U V hU hUV T hT
    have h1 := hU T (Finset.Subset.trans hUV hT)
    have h2 := hU V hUV
    rw [h1, ← h2]
  -- Build the union of approximators for coefficients 0, 1, ..., n for each family
  let mkUnion := fun (c : ι → K⟦X⟧) (hc : Multipliable c) =>
    (Finset.range (n + 1)).biUnion (fun m => (hc m).choose)
  let Ua := mkUnion a ha
  let Ub := mkUnion b hb
  let Uab := mkUnion (fun i => a i * b i) hab
  let U := Ua ∪ Ub ∪ Uab
  -- Helper: mkUnion determines all coefficients m ≤ n
  have mkUnion_determines : ∀ {c : ι → K⟦X⟧} (hc : Multipliable c) {m : ℕ},
      m ≤ n → DeterminesCoeff c m (mkUnion c hc) := by
    intro c hc m hm
    apply DeterminesCoeff_of_superset (hc m).choose_spec
    intro x hx
    rw [Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm), hx⟩
  -- Subset relations
  have hUab_sub : Uab ⊆ U := Finset.subset_union_right
  have hUa_sub : Ua ⊆ U := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hUb_sub : Ub ⊆ U := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  -- U determines all coefficients m ≤ n for all three families
  have hU_det_ab : ∀ m ≤ n, DeterminesCoeff (fun i => a i * b i) m U := by
    intro m hm
    exact DeterminesCoeff_of_superset (mkUnion_determines hab hm) hUab_sub
  have hU_det_a : ∀ m ≤ n, DeterminesCoeff a m U := by
    intro m hm
    exact DeterminesCoeff_of_superset (mkUnion_determines ha hm) hUa_sub
  have hU_det_b : ∀ m ≤ n, DeterminesCoeff b m U := by
    intro m hm
    exact DeterminesCoeff_of_superset (mkUnion_determines hb hm) hUb_sub
  -- LHS: coefficient of the product of pointwise products
  have hLHS : coeff n (infprod (fun i => a i * b i) hab) = coeff n (∏ i ∈ U, (a i * b i)) :=
    coeff_infprod_eq_coeff_finprod hab (hU_det_ab n le_rfl)
  -- RHS: use coeff_mul and the fact that U determines all relevant coefficients
  have hRHS : coeff n (infprod a ha * infprod b hb) = coeff n ((∏ i ∈ U, a i) * (∏ i ∈ U, b i)) := by
    rw [coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro ⟨p, q⟩ hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    have hp : p ≤ n := by omega
    have hq : q ≤ n := by omega
    rw [coeff_infprod_eq_coeff_finprod ha (hU_det_a p hp),
        coeff_infprod_eq_coeff_finprod hb (hU_det_b q hq)]
  -- The finite product of pointwise products equals the product of finite products
  have hfinprod : ∏ i ∈ U, (a i * b i) = (∏ i ∈ U, a i) * (∏ i ∈ U, b i) := Finset.prod_mul_distrib
  rw [hLHS, hRHS, hfinprod]

/-!
## Proposition prop.fps.div-mulable

If `(aᵢ)_{i∈I}` and `(bᵢ)_{i∈I}` are multipliable families with each `bᵢ` invertible,
then `(aᵢ/bᵢ)_{i∈I}` is multipliable and
`∏_{i∈I} (aᵢ/bᵢ) = (∏_{i∈I} aᵢ) / (∏_{i∈I} bᵢ)`.
-/

/-- The pointwise quotient of multipliable families (with invertible denominators)
    is multipliable.
    (Proposition prop.fps.div-mulable (a))
    Label: prop.fps.div-mulable -/
theorem multipliable_div {ι : Type*} {a b : ι → K⟦X⟧}
    (ha : Multipliable a) (hb : Multipliable b)
    (hinv : ∀ i, IsUnit (constantCoeff (b i))) :
    Multipliable (fun i => a i * invOfUnit (b i) (hinv i).unit) := by
  classical
  intro n
  -- Get determiners for all coefficients m ≤ n for both families
  let Ua := (Finset.range (n + 1)).biUnion (fun m => (ha m).choose)
  let Ub := (Finset.range (n + 1)).biUnion (fun m => (hb m).choose)
  let U := Ua ∪ Ub
  -- U determines coefficient n for the quotient family
  use U
  intro T hUT
  -- Key observation: ∏ (a_i * b_i⁻¹) = (∏ a_i) * (∏ b_i)⁻¹ for finite products
  have h_isunit_prod : ∀ S : Finset ι, IsUnit (constantCoeff (∏ i ∈ S, b i)) := fun S => by
    rw [map_prod]
    exact IsUnit.prod_iff.mpr (fun i _ => hinv i)
  -- Now use the product formula
  simp only [Finset.prod_mul_distrib]
  -- We need to show:
  -- coeff n ((∏ i ∈ T, a i) * (∏ i ∈ T, invOfUnit (b i) _)) = coeff n ((∏ i ∈ U, a i) * (∏ i ∈ U, invOfUnit (b i) _))
  --
  -- By the convolution formula, this reduces to showing that for all m ≤ n:
  -- - coeff m (∏ i ∈ T, a i) = coeff m (∏ i ∈ U, a i)
  -- - coeff (n-m) (∏ i ∈ T, invOfUnit (b i) _) = coeff (n-m) (∏ i ∈ U, invOfUnit (b i) _)
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨p, q⟩ hpq
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
  -- p + q = n, so p ≤ n and q ≤ n
  have hp : p ≤ n := by omega
  have hq : q ≤ n := by omega
  -- Ua determines coefficient p for a
  have ha_p_det : DeterminesCoeff a p (ha p).choose := (ha p).choose_spec
  have hUa_p_sub : (ha p).choose ⊆ Ua := by
    intro x hx
    rw [Finset.mem_biUnion]
    exact ⟨p, Finset.mem_range.mpr (Nat.lt_succ_of_le hp), hx⟩
  have hU_a_sub : Ua ⊆ U := Finset.subset_union_left
  have hU_p_det_a : DeterminesCoeff a p U := fun T' hT' => by
    have h1 := ha_p_det T' ((hUa_p_sub.trans hU_a_sub).trans hT')
    have h2 := ha_p_det U (hUa_p_sub.trans hU_a_sub)
    rw [h1, ← h2]
  -- Ub determines coefficient q for b
  have hb_q_det : DeterminesCoeff b q (hb q).choose := (hb q).choose_spec
  have hUb_q_sub : (hb q).choose ⊆ Ub := by
    intro x hx
    rw [Finset.mem_biUnion]
    exact ⟨q, Finset.mem_range.mpr (Nat.lt_succ_of_le hq), hx⟩
  have hU_b_sub : Ub ⊆ U := Finset.subset_union_right
  have hU_q_det_b : DeterminesCoeff b q U := fun T' hT' => by
    have h1 := hb_q_det T' ((hUb_q_sub.trans hU_b_sub).trans hT')
    have h2 := hb_q_det U (hUb_q_sub.trans hU_b_sub)
    rw [h1, ← h2]
  -- Now apply these to T and U
  have eq_a : coeff p (∏ i ∈ T, a i) = coeff p (∏ i ∈ U, a i) := hU_p_det_a T hUT
  -- For the inverse products, we use that b products agree up to degree q,
  -- so their inverses also agree up to degree q
  have hb_eq : ∀ m ≤ q, coeff m (∏ i ∈ T, b i) = coeff m (∏ i ∈ U, b i) := by
    intro m hm
    have hm' : m ≤ n := le_trans hm hq
    -- (hb m).choose determines coeff m for b
    have hb_m_det : DeterminesCoeff b m (hb m).choose := (hb m).choose_spec
    have hUb_m_sub : (hb m).choose ⊆ Ub := by
      intro x hx
      rw [Finset.mem_biUnion]
      exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hm'), hx⟩
    have h1 := hb_m_det T ((hUb_m_sub.trans hU_b_sub).trans hUT)
    have h2 := hb_m_det U (hUb_m_sub.trans hU_b_sub)
    rw [h1, ← h2]
  -- IsUnit conditions for the products
  have hT_inv : IsUnit (constantCoeff (∏ i ∈ T, b i)) := h_isunit_prod T
  have hU_inv : IsUnit (constantCoeff (∏ i ∈ U, b i)) := h_isunit_prod U
  -- The inverses agree up to degree q
  have hinv_eq : ∀ m ≤ q, coeff m (invOfUnit (∏ i ∈ T, b i) hT_inv.unit) =
      coeff m (invOfUnit (∏ i ∈ U, b i) hU_inv.unit) := by
    intro m hm
    -- Use that if two FPS agree up to degree q and have the same unit constant term,
    -- their invOfUnit's also agree up to degree q
    have huv : (hT_inv.unit : K) = hU_inv.unit := by
      simp only [IsUnit.unit_spec]
      rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
      exact hb_eq 0 (Nat.zero_le q)
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      cases m with
      | zero =>
        rw [coeff_invOfUnit, coeff_invOfUnit, ite_eq_left rfl, ite_eq_left rfl]
        have huv' : hT_inv.unit⁻¹ = hU_inv.unit⁻¹ := by
          apply Units.ext
          show (hT_inv.unit⁻¹ : Kˣ).val = (hU_inv.unit⁻¹ : Kˣ).val
          calc (hT_inv.unit⁻¹ : Kˣ).val = Ring.inverse hT_inv.unit.val := (Ring.inverse_unit hT_inv.unit).symm
            _ = Ring.inverse hU_inv.unit.val := by rw [huv]
            _ = (hU_inv.unit⁻¹ : Kˣ).val := Ring.inverse_unit hU_inv.unit
        rw [huv']
      | succ k =>
        rw [coeff_invOfUnit, coeff_invOfUnit, ite_eq_right (Nat.succ_ne_zero k), ite_eq_right (Nat.succ_ne_zero k)]
        have huv' : hT_inv.unit⁻¹ = hU_inv.unit⁻¹ := by
          apply Units.ext
          show (hT_inv.unit⁻¹ : Kˣ).val = (hU_inv.unit⁻¹ : Kˣ).val
          calc (hT_inv.unit⁻¹ : Kˣ).val = Ring.inverse hT_inv.unit.val := (Ring.inverse_unit hT_inv.unit).symm
            _ = Ring.inverse hU_inv.unit.val := by rw [huv]
            _ = (hU_inv.unit⁻¹ : Kˣ).val := Ring.inverse_unit hU_inv.unit
        rw [huv']
        congr 1
        apply Finset.sum_congr rfl
        intro ⟨i, j⟩ hij
        simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
        split_ifs with hj
        · congr 1
          · exact hb_eq i (by omega)
          · exact ih j hj (by omega)
        · rfl
  -- Now show that the coefficients of the product of inverses agree
  -- Key: the product of inverses (∏ invOfUnit b_i) agrees with invOfUnit (∏ b_i) on coefficients
  have eq_inv : coeff q (∏ i ∈ T, invOfUnit (b i) (hinv i).unit) =
      coeff q (∏ i ∈ U, invOfUnit (b i) (hinv i).unit) := by
    -- Both sides equal coeff q of the inverse of the product
    -- Use that ∏ invOfUnit = invOfUnit ∏ (as power series, not just as values)
    -- Actually, we need a different approach: show both sides agree with hinv_eq
    -- The key is that (∏ invOfUnit b_i) * (∏ b_i) = 1, so ∏ invOfUnit b_i = invOfUnit (∏ b_i)
    -- But the units may differ. We use that the coefficients still agree.
    have hT_prod_inv : (∏ i ∈ T, invOfUnit (b i) (hinv i).unit) * (∏ i ∈ T, b i) = 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro i _
      rw [mul_comm]
      exact mul_invOfUnit (b i) (hinv i).unit ((hinv i).unit_spec.symm)
    have hU_prod_inv : (∏ i ∈ U, invOfUnit (b i) (hinv i).unit) * (∏ i ∈ U, b i) = 1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro i _
      rw [mul_comm]
      exact mul_invOfUnit (b i) (hinv i).unit ((hinv i).unit_spec.symm)
    -- Both ∏ invOfUnit b_i and invOfUnit (∏ b_i) are inverses of ∏ b_i
    -- Since inverses are unique, they're equal (as power series)
    have hT_eq_inv : ∏ i ∈ T, invOfUnit (b i) (hinv i).unit = invOfUnit (∏ i ∈ T, b i) hT_inv.unit := by
      have h1 : (∏ i ∈ T, invOfUnit (b i) (hinv i).unit) * (∏ i ∈ T, b i) = 1 := hT_prod_inv
      have h2 : invOfUnit (∏ i ∈ T, b i) hT_inv.unit * (∏ i ∈ T, b i) = 1 := by
        rw [mul_comm]
        exact mul_invOfUnit (∏ i ∈ T, b i) hT_inv.unit (hT_inv.unit_spec.symm)
      -- Both are left inverses of ∏ b_i, so they're equal
      calc ∏ i ∈ T, invOfUnit (b i) (hinv i).unit
          = (∏ i ∈ T, invOfUnit (b i) (hinv i).unit) * 1 := (mul_one _).symm
        _ = (∏ i ∈ T, invOfUnit (b i) (hinv i).unit) * ((∏ i ∈ T, b i) * invOfUnit (∏ i ∈ T, b i) hT_inv.unit) := by
            rw [mul_invOfUnit (∏ i ∈ T, b i) hT_inv.unit (hT_inv.unit_spec.symm)]
        _ = ((∏ i ∈ T, invOfUnit (b i) (hinv i).unit) * (∏ i ∈ T, b i)) * invOfUnit (∏ i ∈ T, b i) hT_inv.unit := by ring
        _ = 1 * invOfUnit (∏ i ∈ T, b i) hT_inv.unit := by rw [h1]
        _ = invOfUnit (∏ i ∈ T, b i) hT_inv.unit := one_mul _
    have hU_eq_inv : ∏ i ∈ U, invOfUnit (b i) (hinv i).unit = invOfUnit (∏ i ∈ U, b i) hU_inv.unit := by
      have h1 : (∏ i ∈ U, invOfUnit (b i) (hinv i).unit) * (∏ i ∈ U, b i) = 1 := hU_prod_inv
      calc ∏ i ∈ U, invOfUnit (b i) (hinv i).unit
          = (∏ i ∈ U, invOfUnit (b i) (hinv i).unit) * 1 := (mul_one _).symm
        _ = (∏ i ∈ U, invOfUnit (b i) (hinv i).unit) * ((∏ i ∈ U, b i) * invOfUnit (∏ i ∈ U, b i) hU_inv.unit) := by
            rw [mul_invOfUnit (∏ i ∈ U, b i) hU_inv.unit (hU_inv.unit_spec.symm)]
        _ = ((∏ i ∈ U, invOfUnit (b i) (hinv i).unit) * (∏ i ∈ U, b i)) * invOfUnit (∏ i ∈ U, b i) hU_inv.unit := by ring
        _ = 1 * invOfUnit (∏ i ∈ U, b i) hU_inv.unit := by rw [h1]
        _ = invOfUnit (∏ i ∈ U, b i) hU_inv.unit := one_mul _
    rw [hT_eq_inv, hU_eq_inv]
    exact hinv_eq q le_rfl
  rw [eq_a, eq_inv]


/-- The infinite product of pointwise quotients equals the quotient of infinite products.
    (Proposition prop.fps.div-mulable (b))
    Label: prop.fps.div-mulable

    Requires that the product of denominators has invertible constant coefficient. -/
theorem infprod_div_eq {ι : Type*} {a b : ι → K⟦X⟧}
    (ha : Multipliable a) (hb : Multipliable b)
    (hinv : ∀ i, IsUnit (constantCoeff (b i)))
    (hab : Multipliable (fun i => a i * invOfUnit (b i) (hinv i).unit))
    (hprod_inv : IsUnit (constantCoeff (infprod b hb))) :
    infprod (fun i => a i * invOfUnit (b i) (hinv i).unit) hab =
      infprod a ha * invOfUnit (infprod b hb) hprod_inv.unit := by
  classical
  -- Key: (a_i * b_i^{-1}) * b_i = a_i
  have h_ab_b_eq_a : ∀ i, (a i * invOfUnit (b i) (hinv i).unit) * b i = a i := fun i => by
    have hi : constantCoeff (b i) = (hinv i).unit := (hinv i).unit_spec.symm
    rw [mul_assoc, mul_comm (invOfUnit (b i) (hinv i).unit) (b i), mul_invOfUnit (b i) (hinv i).unit hi, mul_one]
  -- The family (a_i * b_i^{-1}) * b_i is the same as a_i
  have h_prod_eq : (fun i => (a i * invOfUnit (b i) (hinv i).unit) * b i) = a :=
    funext h_ab_b_eq_a
  -- Multipliability of the product family
  have hab_b : Multipliable (fun i => (a i * invOfUnit (b i) (hinv i).unit) * b i) := by
    rw [h_prod_eq]; exact ha
  -- infprod (ab⁻¹ * b) = infprod a
  have h_infprod_eq : infprod (fun i => (a i * invOfUnit (b i) (hinv i).unit) * b i) hab_b = infprod a ha := by
    congr 1
  -- infprod (ab⁻¹) * infprod b = infprod (ab⁻¹ * b) by infprod_mul_eq
  have h_mul : infprod (fun i => (a i * invOfUnit (b i) (hinv i).unit) * b i) hab_b =
      infprod (fun i => a i * invOfUnit (b i) (hinv i).unit) hab * infprod b hb :=
    infprod_mul_eq hab hb hab_b
  -- So infprod (ab⁻¹) * infprod b = infprod a
  have h_key : infprod (fun i => a i * invOfUnit (b i) (hinv i).unit) hab * infprod b hb = infprod a ha := by
    rw [← h_mul, h_infprod_eq]
  -- Since infprod b has invertible constant coeff, we can solve for infprod (ab⁻¹)
  have hconst : constantCoeff (infprod b hb) = hprod_inv.unit := hprod_inv.unit_spec.symm
  have hginv : (infprod b hb) * invOfUnit (infprod b hb) hprod_inv.unit = 1 :=
    mul_invOfUnit (infprod b hb) hprod_inv.unit hconst
  calc infprod (fun i => a i * invOfUnit (b i) (hinv i).unit) hab
      = infprod (fun i => a i * invOfUnit (b i) (hinv i).unit) hab * 1 := (mul_one _).symm
    _ = infprod (fun i => a i * invOfUnit (b i) (hinv i).unit) hab *
        ((infprod b hb) * invOfUnit (infprod b hb) hprod_inv.unit) := by rw [hginv]
    _ = (infprod (fun i => a i * invOfUnit (b i) (hinv i).unit) hab * (infprod b hb)) *
        invOfUnit (infprod b hb) hprod_inv.unit := by ring
    _ = infprod a ha * invOfUnit (infprod b hb) hprod_inv.unit := by rw [h_key]

/-!
## Lemma lem.fps.prods-mulable-rules.SW1.lem1

If each `cᵥ ≡ dᵥ` (mod x^{n+1}) for `v ∈ V` (finite), then `∏_{v∈V} cᵥ ≡ ∏_{v∈V} dᵥ`.

This is a restatement of part of Theorem thm.fps.xneq.props (f).
-/

/-- Finite products preserve x^n-equivalence.
    (Lemma lem.fps.prods-mulable-rules.SW1.lem1)
    Label: lem.fps.prods-mulable-rules.SW1.lem1 -/
theorem xnEquiv_finprod {ι : Type*} {n : ℕ} {V : Finset ι}
    {c d : ι → K⟦X⟧} (h : ∀ v ∈ V, c v ≡[x^n] d v) :
    ∏ v ∈ V, c v ≡[x^n] ∏ v ∈ V, d v := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    simp only [Finset.prod_insert has]
    apply PowerSeries.XnEquiv.mul
    · exact h a (Finset.mem_insert_self a s)
    · exact ih (fun v hv => h v (Finset.mem_insert_of_mem hv))

/-!
## Proposition prop.fps.prods-mulable-rules.SW1

Let `f : S → W` be a surjection. If `(aₛ)_{s∈S}` is a multipliable family such that
for each `w ∈ W`, the subfamily `(aₛ)_{s∈S, f(s)=w}` is multipliable, then:

(a) The family `(bᵥ)_{w∈W}` where `bᵥ = ∏_{s∈S, f(s)=w} aₛ` is multipliable.
(b) `∏_{s∈S} aₛ = ∏_{w∈W} bᵥ`.

This allows reindexing/grouping of infinite products.
-/

/-- For a surjection `f : S → W`, if the original family and all fiber families
    are multipliable, then the family of fiber products is multipliable.
    (Proposition prop.fps.prods-mulable-rules.SW1, Claim 1 setup)
    Label: prop.fps.prods-mulable-rules.SW1

    Note: The proof requires invertibility of each `a s` (i.e., `IsUnit (constantCoeff (a s))`).
    This is used in Claim 2 of the tex proof, which applies `lem.fps.prods-mulable-subfams-appr`
    to show that `U ∩ fiber_w` is an x^n-approximator for the fiber subfamily. -/
theorem multipliable_fiber_prods {S W : Type*} {a : S → K⟦X⟧} {f : S → W}
    (hS : Multipliable a)
    (hinv : ∀ s, IsUnit (constantCoeff (a s)))
    (hfiber : ∀ w : W, Multipliable (fun s : {s : S // f s = w} => a s.1)) :
    Multipliable (fun w => infprod (fun s : {s : S // f s = w} => a s.1) (hfiber w)) := by
  classical
  intro n
  -- Get an x^n-approximator U for the original family
  obtain ⟨U, hU⟩ := multipliable_exists_approximator hS n
  -- Use the image f(U) as our approximator for the fiber products family
  use U.image f
  intro T hT

  -- b_w = infprod over fiber of w
  let b : W → K⟦X⟧ := fun w => infprod (fun s : {s : S // f s = w} => a s.1) (hfiber w)

  -- Claim 2: For each w, b w ≡[x^n] ∏_{s ∈ U, f s = w} a_s
  have claim2 : ∀ w : W, b w ≡[x^n] ∏ s ∈ U.filter (fun s => f s = w), a s := by
    intro w
    -- The fiber subfamily at w
    let fiber_a : {s : S // f s = w} → K⟦X⟧ := fun s => a s.1
    -- U_fiber = U.filter (f s = w) as a Finset S
    let U_fiber : Finset S := U.filter (fun s => f s = w)
    -- Convert U_fiber to a Finset of the fiber subtype
    let U_fiber_sub : Finset {s : S // f s = w} := U_fiber.subtype (fun s => f s = w)

    -- Helper: convert between products over U_fiber and U_fiber_sub
    have prod_convert : ∏ s ∈ U_fiber, a s = ∏ s ∈ U_fiber_sub, fiber_a s := by
      apply Finset.prod_bij (fun s hs => ⟨s, (Finset.mem_filter.mp hs).2⟩)
      · intro s hs; simp only [Finset.mem_subtype, U_fiber_sub, U_fiber]; exact hs
      · intro s₁ _ s₂ _ h; exact Subtype.mk.inj h
      · intro ⟨s, hs_prop⟩ hs
        simp only [Finset.mem_subtype, U_fiber_sub, U_fiber] at hs
        exact ⟨s, hs, rfl⟩
      · intro s _; rfl

    have prod_convert' : ∏ s ∈ U_fiber_sub, fiber_a s = ∏ s ∈ U_fiber, a s := prod_convert.symm

    -- U_fiber_sub is an x^n-approximator for fiber_a
    have hU_fiber_approx : IsXnApproximator fiber_a n U_fiber_sub := by
      intro m hm T' hUT'
      let T'_S : Finset S := T'.map ⟨Subtype.val, Subtype.val_injective⟩

      have hT'_fiber : ∀ s ∈ T'_S, f s = w := by
        intro s hs
        rw [Finset.mem_map] at hs
        obtain ⟨⟨t, ht⟩, _, rfl⟩ := hs
        exact ht

      have prod_T' : ∏ s ∈ T', fiber_a s = ∏ s ∈ T'_S, a s := by
        rw [Finset.prod_map]; rfl

      have prod_U_sub : ∏ s ∈ U_fiber_sub, fiber_a s = ∏ s ∈ U_fiber, a s := prod_convert'

      have hU_fiber_sub_T'_S : U_fiber ⊆ T'_S := by
        intro s hs
        rw [Finset.mem_filter] at hs
        rw [Finset.mem_map]
        have hs_fiber : f s = w := hs.2
        have hs_U_fiber_sub : ⟨s, hs_fiber⟩ ∈ U_fiber_sub := by
          simp only [Finset.mem_subtype, U_fiber_sub, U_fiber, Finset.mem_filter]
          exact hs
        have hs_T' : ⟨s, hs_fiber⟩ ∈ T' := hUT' hs_U_fiber_sub
        exact ⟨⟨s, hs_fiber⟩, hs_T', rfl⟩

      let U_not_fiber : Finset S := U.filter (fun s => f s ≠ w)
      have disj : Disjoint T'_S U_not_fiber := by
        rw [Finset.disjoint_left]
        intro s hsT' hsU_not
        rw [Finset.mem_filter] at hsU_not
        exact hsU_not.2 (hT'_fiber s hsT')

      have U_eq : U = U_fiber ∪ U_not_fiber := by
        ext s
        simp only [Finset.mem_union, Finset.mem_filter, U_fiber, U_not_fiber]
        constructor
        · intro hs
          by_cases h : f s = w
          · left; exact ⟨hs, h⟩
          · right; exact ⟨hs, h⟩
        · intro h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h

      have disj' : Disjoint U_fiber U_not_fiber := by
        rw [Finset.disjoint_left]
        intro s hs1 hs2
        rw [Finset.mem_filter] at hs1 hs2
        exact hs2.2 hs1.2

      have union_eq : T'_S ∪ U = T'_S ∪ U_not_fiber := by
        ext s
        simp only [Finset.mem_union]
        constructor
        · intro h
          rcases h with hT' | hU
          · left; exact hT'
          · rw [U_eq] at hU
            simp only [Finset.mem_union] at hU
            rcases hU with hUf | hUnf
            · left; exact hU_fiber_sub_T'_S hUf
            · right; exact hUnf
        · intro h
          rcases h with hT' | hUnf
          · left; exact hT'
          · right; rw [U_eq]; exact Finset.mem_union_right _ hUnf

      have hU_sub : U ⊆ T'_S ∪ U := Finset.subset_union_right

      have h1 : coeff m (∏ s ∈ T'_S ∪ U, a s) = coeff m (∏ s ∈ U, a s) :=
        hU m hm (T'_S ∪ U) hU_sub

      have h2 : ∏ s ∈ T'_S ∪ U, a s = (∏ s ∈ T'_S, a s) * (∏ s ∈ U_not_fiber, a s) := by
        rw [union_eq, Finset.prod_union disj]

      have h3 : ∏ s ∈ U, a s = (∏ s ∈ U_fiber, a s) * (∏ s ∈ U_not_fiber, a s) := by
        rw [U_eq, Finset.prod_union disj']

      let Q := ∏ s ∈ U_not_fiber, a s
      have hQ_inv : IsUnit (constantCoeff Q) := by
        rw [map_prod]
        exact IsUnit.prod_iff.mpr (fun s _ => hinv s)

      have h5 : (∏ s ∈ T'_S, a s) ≡[x^m] (∏ s ∈ U_fiber, a s) := by
        apply xnEquiv_of_mul_xnEquiv_right' _ hQ_inv
        intro k hk
        have hk_n : k ≤ n := le_trans hk hm
        have h1' : coeff k (∏ s ∈ T'_S ∪ U, a s) = coeff k (∏ s ∈ U, a s) :=
          hU k hk_n (T'_S ∪ U) hU_sub
        have h2' : ∏ s ∈ T'_S ∪ U, a s = (∏ s ∈ T'_S, a s) * Q := by
          rw [union_eq, Finset.prod_union disj]
        have h3' : ∏ s ∈ U, a s = (∏ s ∈ U_fiber, a s) * Q := by
          rw [U_eq, Finset.prod_union disj']
        rw [h2', h3'] at h1'
        exact h1'

      rw [prod_T', prod_U_sub]
      exact h5 m le_rfl

    have h1 : b w ≡[x^n] ∏ s ∈ U_fiber_sub, fiber_a s := infprod_xnEquiv_finprod (hfiber w) hU_fiber_approx
    intro k hk
    have h2 := h1 k hk
    rw [prod_convert'] at h2
    exact h2

  -- Now we show that U.image f determines the n-th coefficient
  have h_T : ∏ w ∈ T, b w ≡[x^n] ∏ w ∈ T, (∏ s ∈ U.filter (fun s => f s = w), a s) := by
    apply xnEquiv_finprod
    intro w _
    exact claim2 w

  have h_fU : ∏ w ∈ U.image f, b w ≡[x^n] ∏ w ∈ U.image f, (∏ s ∈ U.filter (fun s => f s = w), a s) := by
    apply xnEquiv_finprod
    intro w _
    exact claim2 w

  have reindex : ∀ V : Finset W, U.image f ⊆ V →
      ∏ w ∈ V, (∏ s ∈ U.filter (fun s => f s = w), a s) = ∏ s ∈ U, a s := by
    intro V hV
    have h_empty : ∀ w ∈ V \ U.image f, U.filter (fun s => f s = w) = ∅ := by
      intro w hw
      rw [Finset.mem_sdiff, Finset.mem_image] at hw
      push Not at hw
      rw [Finset.eq_empty_iff_forall_notMem]
      intro s hs
      rw [Finset.mem_filter] at hs
      exact hw.2 s hs.1 hs.2
    have h_prod_empty : ∀ w ∈ V \ U.image f, ∏ s ∈ U.filter (fun s => f s = w), a s = 1 := by
      intro w hw
      rw [h_empty w hw]
      exact Finset.prod_empty

    have V_eq : V = U.image f ∪ (V \ U.image f) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hw
        by_cases h : w ∈ U.image f
        · left; exact h
        · right; exact ⟨hw, h⟩
      · intro h; rcases h with h | ⟨h, _⟩ <;> [exact hV h; exact h]

    have disj : Disjoint (U.image f) (V \ U.image f) := Finset.disjoint_sdiff

    rw [V_eq, Finset.prod_union disj]
    have h_one : ∏ w ∈ V \ U.image f, (∏ s ∈ U.filter (fun s => f s = w), a s) = 1 := by
      apply Finset.prod_eq_one
      intro w hw
      exact h_prod_empty w hw
    rw [h_one, mul_one]

    have hf_maps : ∀ s ∈ U, f s ∈ U.image f := fun s hs => Finset.mem_image_of_mem f hs
    exact Finset.prod_fiberwise_of_maps_to hf_maps a

  have h_T_reindex : ∏ w ∈ T, (∏ s ∈ U.filter (fun s => f s = w), a s) = ∏ s ∈ U, a s :=
    reindex T hT

  have h_fU_reindex : ∏ w ∈ U.image f, (∏ s ∈ U.filter (fun s => f s = w), a s) = ∏ s ∈ U, a s :=
    reindex (U.image f) (Finset.Subset.refl _)

  have h_T_equiv : ∏ w ∈ T, b w ≡[x^n] ∏ s ∈ U, a s := by
    calc ∏ w ∈ T, b w ≡[x^n] ∏ w ∈ T, (∏ s ∈ U.filter (fun s => f s = w), a s) := h_T
      _ = ∏ s ∈ U, a s := h_T_reindex

  have h_fU_equiv : ∏ w ∈ U.image f, b w ≡[x^n] ∏ s ∈ U, a s := by
    calc ∏ w ∈ U.image f, b w ≡[x^n] ∏ w ∈ U.image f, (∏ s ∈ U.filter (fun s => f s = w), a s) := h_fU
      _ = ∏ s ∈ U, a s := h_fU_reindex

  have h_T_coeff : coeff n (∏ w ∈ T, b w) = coeff n (∏ s ∈ U, a s) := h_T_equiv n le_rfl
  have h_fU_coeff : coeff n (∏ w ∈ U.image f, b w) = coeff n (∏ s ∈ U, a s) := h_fU_equiv n le_rfl
  rw [h_T_coeff, h_fU_coeff]

/-- For a surjection `f : S → W`, the infinite product over `S` equals the
    infinite product over `W` of fiber products.
    (Proposition prop.fps.prods-mulable-rules.SW1 (b))
    Label: prop.fps.prods-mulable-rules.SW1 -/
theorem infprod_eq_infprod_fiber {S W : Type*} {a : S → K⟦X⟧} {f : S → W}
    (hS : Multipliable a)
    (hinv : ∀ s, IsUnit (constantCoeff (a s)))
    (hfiber : ∀ w : W, Multipliable (fun s : {s : S // f s = w} => a s.1))
    (hW : Multipliable (fun w => infprod (fun s : {s : S // f s = w} => a s.1) (hfiber w))) :
    infprod a hS = infprod (fun w => infprod (fun s : {s : S // f s = w} => a s.1) (hfiber w)) hW := by
  classical
  ext n

  let b : W → K⟦X⟧ := fun w => infprod (fun s : {s : S // f s = w} => a s.1) (hfiber w)

  -- Build an x^n-approximator for the original family
  let U := (Finset.range (n + 1)).biUnion (fun m => (hS m).choose)

  have hU_approx : IsXnApproximator a n U := by
    intro m hm T hT
    have hm_in_range : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    have h_sub : (hS m).choose ⊆ U := Finset.subset_biUnion_of_mem (fun m => (hS m).choose) hm_in_range
    have hdet : DeterminesCoeff a m (hS m).choose := (hS m).choose_spec
    have h1 : coeff m (∏ i ∈ T, a i) = coeff m (∏ i ∈ (hS m).choose, a i) := hdet T (h_sub.trans hT)
    have h2 : coeff m (∏ i ∈ U, a i) = coeff m (∏ i ∈ (hS m).choose, a i) := hdet U h_sub
    rw [h1, ← h2]

  -- Similarly for the fiber products family
  let V := (Finset.range (n + 1)).biUnion (fun m => (hW m).choose)

  have hV_approx : IsXnApproximator b n V := by
    intro m hm T hT
    have hm_in_range : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    have h_sub : (hW m).choose ⊆ V := Finset.subset_biUnion_of_mem (fun m => (hW m).choose) hm_in_range
    have hdet : DeterminesCoeff b m (hW m).choose := (hW m).choose_spec
    have h1 : coeff m (∏ w ∈ T, b w) = coeff m (∏ w ∈ (hW m).choose, b w) := hdet T (h_sub.trans hT)
    have h2 : coeff m (∏ w ∈ V, b w) = coeff m (∏ w ∈ (hW m).choose, b w) := hdet V h_sub
    rw [h1, ← h2]

  -- Take the union W' = V ∪ U.image f
  let W' := V ∪ U.image f

  have hW'_approx : IsXnApproximator b n W' := by
    intro m hm T hT
    have h1 := hV_approx m hm T (subset_union_left.trans hT)
    have h2 := hV_approx m hm W' subset_union_left
    rw [h1, ← h2]

  -- LHS: infprod a hS ≡[x^n] ∏ s ∈ U, a s
  have hLHS : infprod a hS ≡[x^n] ∏ s ∈ U, a s := infprod_xnEquiv_finprod hS hU_approx

  -- RHS: infprod b hW ≡[x^n] ∏ w ∈ W', b w
  have hRHS : infprod b hW ≡[x^n] ∏ w ∈ W', b w := infprod_xnEquiv_finprod hW hW'_approx

  -- Key step: for each w ∈ W', show that b w ≡[x^n] ∏ s ∈ U.filter (f · = w), a s
  have h_fiber_equiv : ∀ w ∈ W', b w ≡[x^n] ∏ s ∈ U.filter (f · = w), a s := by
    intro w _ m hm

    -- Convert U.filter to a Finset of the fiber type
    let Uw_filter := U.filter (fun s => f s = w)
    let Uw : Finset {s : S // f s = w} :=
      Uw_filter.attach.map ⟨fun s => ⟨s.val, by
        have hs := s.property
        simp only [Uw_filter, Finset.mem_filter] at hs
        exact hs.2⟩,
        fun x y h => by simp only [Subtype.mk.injEq] at h; exact Subtype.ext h⟩

    -- Show Uw determines coeff m for the fiber subfamily
    have hUw_det : DeterminesCoeff (fun s : {s : S // f s = w} => a s.1) m Uw := by
      intro T hT
      let T' := T.map ⟨Subtype.val, Subtype.val_injective⟩
      let Uw' := U.filter (fun s => f s = w)

      have prodT : ∏ s ∈ T, a s.1 = ∏ s ∈ T', a s := by
        simp only [T']
        rw [Finset.prod_map]
        rfl
      have prodUw : ∏ s ∈ Uw, a s.1 = ∏ s ∈ Uw', a s := by
        simp only [Uw, Uw_filter, Uw']
        rw [Finset.prod_map]
        conv_rhs => rw [← Finset.prod_attach]
        apply Finset.prod_congr rfl
        intro s _
        rfl

      rw [prodT, prodUw]

      have hUw'_sub_T' : Uw' ⊆ T' := by
        intro s hs
        simp only [T', Finset.mem_map, Function.Embedding.coeFn_mk]
        have hs_U : s ∈ U := (Finset.mem_filter.mp hs).1
        have hs_prop : f s = w := (Finset.mem_filter.mp hs).2
        have h_in_Uw : ⟨s, hs_prop⟩ ∈ Uw := by
          simp only [Uw, Uw_filter, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
            true_and]
          refine ⟨⟨s, ?_⟩, rfl⟩
          simp only [Finset.mem_filter]
          exact ⟨hs_U, hs_prop⟩
        exact ⟨⟨s, hs_prop⟩, hT h_in_Uw, rfl⟩

      let U_not_w := U.filter (fun s => f s ≠ w)

      have disj1 : Disjoint Uw' U_not_w := by
        rw [Finset.disjoint_filter]
        intro s _ hfs hfs'
        exact hfs' hfs

      have disj2 : Disjoint T' U_not_w := by
        rw [Finset.disjoint_left]
        intro s hs1 hs2
        simp only [T', Finset.mem_map, Function.Embedding.coeFn_mk] at hs1
        obtain ⟨⟨s', hs'⟩, _, rfl⟩ := hs1
        simp only [U_not_w, Finset.mem_filter] at hs2
        exact hs2.2 hs'

      have hU_eq : U = Uw' ∪ U_not_w := by
        ext s
        simp only [Finset.mem_union, Finset.mem_filter, Uw', U_not_w]
        constructor
        · intro hs
          by_cases hfs : f s = w
          · left; exact ⟨hs, hfs⟩
          · right; exact ⟨hs, hfs⟩
        · intro h; rcases h with ⟨hs, _⟩ | ⟨hs, _⟩ <;> exact hs

      have hT'_union : T' ∪ U_not_w ⊇ U := by
        rw [hU_eq]; exact Finset.union_subset_union hUw'_sub_T' (Finset.Subset.refl _)

      have hUw'_union : Uw' ∪ U_not_w = U := hU_eq.symm

      have eq1 : coeff m (∏ s ∈ T' ∪ U_not_w, a s) = coeff m (∏ s ∈ U, a s) :=
        hU_approx m hm _ hT'_union
      have eq2 : coeff m (∏ s ∈ Uw' ∪ U_not_w, a s) = coeff m (∏ s ∈ U, a s) := by
        rw [hUw'_union]

      rw [Finset.prod_union disj2] at eq1
      rw [Finset.prod_union disj1] at eq2

      have h_inv : IsUnit (constantCoeff (∏ s ∈ U_not_w, a s)) := by
        rw [map_prod]
        exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun s _ => hinv s)

      have h_eq : (∏ s ∈ T', a s) * (∏ s ∈ U_not_w, a s) ≡[x^m]
                  (∏ s ∈ Uw', a s) * (∏ s ∈ U_not_w, a s) := by
        intro k hk
        have eq1' : coeff k (∏ s ∈ T' ∪ U_not_w, a s) = coeff k (∏ s ∈ U, a s) :=
          hU_approx k (hk.trans hm) _ hT'_union
        have eq2' : coeff k (∏ s ∈ Uw' ∪ U_not_w, a s) = coeff k (∏ s ∈ U, a s) := by
          rw [hUw'_union]
        rw [Finset.prod_union disj2] at eq1'
        rw [Finset.prod_union disj1] at eq2'
        rw [eq1', eq2']

      obtain ⟨u, hu⟩ := h_inv
      have hu' : constantCoeff (∏ s ∈ U_not_w, a s) = u := hu.symm
      let P := ∏ s ∈ U_not_w, a s
      let P_inv := invOfUnit P u
      have hP_mul_inv : P * P_inv = 1 := mul_invOfUnit P u hu'

      have h_cancel : ∏ s ∈ T', a s ≡[x^m] ∏ s ∈ Uw', a s := by
        have h1 : (∏ s ∈ T', a s) * P * P_inv ≡[x^m] (∏ s ∈ Uw', a s) * P * P_inv := by
          apply PowerSeries.XnEquiv.mul h_eq
          exact PowerSeries.XnEquiv.refl m P_inv
        simp only [mul_assoc, hP_mul_inv, mul_one] at h1
        exact h1

      exact h_cancel m le_rfl

    -- Now apply the determiner
    -- Note: b w = infprod (fun s : {s : S // f s = w} => a s.1) (hfiber w) by definition
    have h1 : coeff m (infprod (fun s : {s : S // f s = w} => a s.1) (hfiber w)) = coeff m (∏ s ∈ Uw, a s.1) :=
      coeff_infprod_eq_coeff_finprod (hfiber w) hUw_det
    -- b w = infprod ... so coeff m (b w) = coeff m (infprod ...)
    have hb_eq : b w = infprod (fun s : {s : S // f s = w} => a s.1) (hfiber w) := rfl
    rw [hb_eq, h1]

    -- And ∏ Uw = ∏ U.filter (f · = w)
    have h2 : ∏ s ∈ Uw, a s.1 = ∏ s ∈ U.filter (fun s => f s = w), a s := by
      simp only [Uw, Uw_filter]
      rw [Finset.prod_map]
      conv_rhs => rw [← Finset.prod_attach]
      apply Finset.prod_congr rfl
      intro s _
      rfl
    rw [h2]

  -- Reindex: ∏ s ∈ U, a s = ∏ w ∈ U.image f, (∏ s ∈ U.filter (f · = w), a s)
  have h_reindex : ∏ s ∈ U, a s = ∏ w ∈ U.image f, ∏ s ∈ U.filter (f · = w), a s := by
    rw [← Finset.prod_biUnion]
    · congr 1
      ext s
      simp only [mem_biUnion, mem_image, mem_filter]
      constructor
      · intro hs; exact ⟨f s, ⟨s, hs, rfl⟩, hs, rfl⟩
      · intro ⟨_, _, hs, _⟩; exact hs
    · intro w1 _ w2 _ hw
      simp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro s _ hsw1 hsw2
      rw [hsw1] at hsw2
      exact hw hsw2

  -- Extend to W': for w ∉ U.image f, the filter is empty so product is 1
  have h_extend : ∏ w ∈ U.image f, ∏ s ∈ U.filter (f · = w), a s =
      ∏ w ∈ W', ∏ s ∈ U.filter (f · = w), a s := by
    rw [← Finset.prod_subset (Finset.subset_union_right : U.image f ⊆ W')]
    intro w _ hnw
    rw [Finset.prod_eq_one]
    intro s hs
    simp only [mem_filter] at hs
    simp only [mem_image] at hnw
    push Not at hnw
    exact absurd hs.2 (hnw s hs.1)

  -- And: ∏ w ∈ W', b w ≡[x^n] ∏ w ∈ W', (∏ s ∈ U.filter (f · = w), a s)
  have h_prods_equiv : ∏ w ∈ W', b w ≡[x^n] ∏ w ∈ W', ∏ s ∈ U.filter (f · = w), a s := by
    apply xnEquiv_finprod
    intro w hw
    exact h_fiber_equiv w hw

  -- Final calculation
  calc coeff n (infprod a hS)
      = coeff n (∏ s ∈ U, a s) := hLHS n le_rfl
    _ = coeff n (∏ w ∈ U.image f, ∏ s ∈ U.filter (f · = w), a s) := by rw [h_reindex]
    _ = coeff n (∏ w ∈ W', ∏ s ∈ U.filter (f · = w), a s) := by rw [h_extend]
    _ = coeff n (∏ w ∈ W', b w) := (h_prods_equiv n le_rfl).symm
    _ = coeff n (infprod b hW) := (hRHS n le_rfl).symm

/-!
## Finite Families are Multipliable

A finite family of FPSs is always multipliable.
-/

/-- A finite family of FPSs is multipliable. -/
theorem multipliable_of_finite {ι : Type*} [Finite ι] (a : ι → K⟦X⟧) :
    Multipliable a := by
  intro n
  cases nonempty_fintype ι
  use Finset.univ
  intro T hT
  -- Since T ⊇ univ and T ⊆ univ (T is a Finset), we have T = univ
  have h : T = Finset.univ := by
    ext x
    constructor
    · intro _; exact Finset.mem_univ x
    · intro _; exact hT (Finset.mem_univ x)
  simp only [h]

/-- The infinite product of a finite family equals the finite product. -/
theorem infprod_of_finite {ι : Type*} [Fintype ι] (a : ι → K⟦X⟧) :
    infprod a (multipliable_of_finite a) = ∏ i : ι, a i := by
  ext n
  simp only [infprod, PowerSeries.tprod, coeff_mk, PowerSeries.tprodCoeff]
  -- The chosen approximating set and univ both give the same coefficient
  have hdet : DeterminesCoeff a n (multipliable_of_finite a n).choose :=
    (multipliable_of_finite a n).choose_spec
  -- Apply DeterminesCoeff with T = univ: since univ ⊇ chosen, the coefficients match
  exact (hdet Finset.univ (Finset.subset_univ _)).symm

/-!
## Constant Family

A constant family `(c)_{i∈I}` where `c` has constant term 1 is multipliable
if and only if `I` is finite or `c = 1`.
-/

/-- If all FPSs in a family are 1, the family is multipliable. -/
theorem multipliable_one {ι : Type*} : Multipliable (fun _ : ι => (1 : K⟦X⟧)) := by
  intro n
  use ∅
  intro T _
  simp

/-- The infinite product of the constant 1 family is 1. -/
theorem infprod_one {ι : Type*} :
    infprod (fun _ : ι => (1 : K⟦X⟧)) multipliable_one = 1 := by
  ext n
  simp only [infprod, PowerSeries.tprod, coeff_mk, PowerSeries.tprodCoeff]
  simp

end FPS

end AlgebraicCombinatorics
