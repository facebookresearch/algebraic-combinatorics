/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.FPS.Limits

/-!
# Infinite Products of Formal Power Series

This file formalizes the theory of infinite products of formal power series (FPS),
following the treatment in the source material (Section `sec.gf.prod`).

## Relationship with `InfiniteProducts1.lean`

This file (`InfiniteProducts.lean`) provides the primary API in the `PowerSeries` namespace.
The file `InfiniteProducts1.lean` provides an alternative formalization in the `AlgebraicCombinatorics.FPS`
namespace with **definitionally equivalent** definitions:

* `PowerSeries.Multipliable a` = `AlgebraicCombinatorics.FPS.Multipliable a`
* `PowerSeries.tprod a h` = `AlgebraicCombinatorics.FPS.infprod a h`
* `PowerSeries.DeterminesCoeffInProd a M n` = `AlgebraicCombinatorics.FPS.DeterminesCoeff a n M` (argument order)
* `PowerSeries.IsXnApproximator a M n` = `AlgebraicCombinatorics.FPS.IsXnApproximator a n M` (argument order)

The `PowerSeries` namespace versions are canonical and recommended for new code.

## Main Definitions

* `PowerSeries.DeterminesCoeffInProd`: A finite subset `M` determines the `x^n`-coefficient
  in the product of a family if adding more factors doesn't change that coefficient.
* `PowerSeries.CoeffFinitelyDeterminedInProd`: The `x^n`-coefficient is finitely determined
  if some finite subset determines it.
* `PowerSeries.Multipliable`: A family of FPS is multipliable if all coefficients in its
  product are finitely determined.
* `PowerSeries.tprod`: The infinite product of a multipliable family.
* `PowerSeries.IsXnApproximator`: A finite subset that determines the first `n+1` coefficients.

## Main Results

* `PowerSeries.multipliable_coeff_eq_of_determines`: The infinite product is well-defined.
* `PowerSeries.tprod_coeff`: The coefficient of the infinite product equals the coefficient
  of any determining finite partial product.
* `PowerSeries.multipliable_one_add_of_summable`: If `(f_i)` is summable, then `(1 + f_i)` is multipliable.
* `PowerSeries.multipliable_of_finite_ne_one`: If all but finitely many entries equal 1,
  the family is multipliable.
* `PowerSeries.multipliable_of_union`: Products can be split into subproducts.
* `PowerSeries.multipliable_mul`: Products of multipliable families are multipliable.
* `PowerSeries.multipliable_div`: Quotients of multipliable families (with invertible denominators).
* `PowerSeries.multipliable_subfamily`: Subfamilies of multipliable families of invertible FPS.
* `PowerSeries.multipliable_reindex`: Reindexing preserves multipliability.
* `PowerSeries.tprod_fubini`: Fubini rule for infinite products (I × J → I then J).
* `PowerSeries.tprod_fubini_J`: Fubini rule for infinite products (I × J → J then I).
* `PowerSeries.fubini_prod_invertible`: Fubini rule showing both row/column families are multipliable.

## References

* Source: `AlgebraicCombinatorics/tex/FPS/InfiniteProducts1.tex`
-/

open scoped BigOperators

namespace PowerSeries

variable {R : Type*} [CommRing R]
variable {I : Type*}

/-!
### Motivating Example: Binary Representation

The product `∏_{i ∈ ℕ} (1 + x^{2^i})` equals `1/(1-x)` in `R[[x]]`.
This relates to the unique binary representation of natural numbers.
(Label: eq.fps.prod.binary.2)
-/

/-- Helper: (1-a)(1+a) = 1 - a^2 for power series. -/
private lemma one_sub_mul_one_add (a : PowerSeries R) : (1 - a) * (1 + a) = 1 - a^2 := by ring

/-- Key induction: (1 - X) * ∏_{i=0}^m (1 + X^{2^i}) = 1 - X^{2^{m+1}}. -/
private theorem one_sub_X_mul_prod_eq (m : ℕ) :
    (1 - X) * ∏ i ∈ Finset.range (m + 1), (1 + (X : PowerSeries R) ^ (2 ^ i)) =
    1 - X ^ (2 ^ (m + 1)) := by
  induction m with
  | zero =>
    have : ∏ i ∈ Finset.range 1, (1 + (X : PowerSeries R) ^ (2 ^ i)) = 1 + X := by
      simp [Finset.range_one, pow_zero, pow_one]
    rw [this]
    ring
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih]
    have h : (1 - (X : PowerSeries R) ^ (2 ^ (n + 1))) * (1 + X ^ (2 ^ (n + 1))) =
             1 - X ^ (2 ^ (n + 2)) := by
      rw [one_sub_mul_one_add]
      congr 1
      rw [← pow_mul, ← pow_succ]
    exact h

/-- The product of `(1 + x^{2^i})` for `i` from `0` to `m` equals `(1 - x^{2^{m+1}}) / (1 - x)`.
This is the finite version of the binary product identity.
(Label: eq.fps.prod.binary.1) -/
theorem prod_one_add_pow_two_eq (m : ℕ) :
    ∏ i ∈ Finset.range (m + 1), (1 + (X : PowerSeries R) ^ (2 ^ i)) =
    (1 - X ^ (2 ^ (m + 1))) * invOfUnit (1 - X) 1 := by
  have h := one_sub_X_mul_prod_eq (R := R) m
  have hconst : constantCoeff (1 - (X : PowerSeries R)) = 1 := by simp
  calc ∏ i ∈ Finset.range (m + 1), (1 + (X : PowerSeries R) ^ (2 ^ i))
      = 1 * ∏ i ∈ Finset.range (m + 1), (1 + X ^ (2 ^ i)) := by ring
    _ = (invOfUnit (1 - X) 1 * (1 - X)) * ∏ i ∈ Finset.range (m + 1), (1 + X ^ (2 ^ i)) := by
        rw [invOfUnit_mul (1 - X) 1 hconst]
    _ = invOfUnit (1 - X) 1 * ((1 - X) * ∏ i ∈ Finset.range (m + 1), (1 + X ^ (2 ^ i))) := by ring
    _ = invOfUnit (1 - X) 1 * (1 - X ^ (2 ^ (m + 1))) := by rw [h]
    _ = (1 - X ^ (2 ^ (m + 1))) * invOfUnit (1 - X) 1 := by ring

/-!
### Definition of Coefficient Determination

Definition \ref{def.fps.determines-xn-coeff}
-/

/-- A finite subset `M` of `I` determines the `x^n`-coefficient in the product of
a family `(a_i)_{i ∈ I}` if for every finite superset `J` of `M`, the `x^n`-coefficient
of `∏_{i ∈ J} a_i` equals that of `∏_{i ∈ M} a_i`.
(Label: def.fps.determines-xn-coeff part (b)) -/
def DeterminesCoeffInProd (a : I → PowerSeries R) (M : Finset I) (n : ℕ) : Prop :=
  ∀ J : Finset I, M ⊆ J → (∏ i ∈ J, a i).coeff n = (∏ i ∈ M, a i).coeff n

/-- If `M₁` determines the `x^n` coefficient and `M₁ ⊆ M₂`, then `M₂` also determines it. -/
theorem determinesCoeffInProd_mono {a : I → PowerSeries R} {M₁ M₂ : Finset I} {n : ℕ}
    (h : DeterminesCoeffInProd a M₁ n) (hsub : M₁ ⊆ M₂) : DeterminesCoeffInProd a M₂ n := by
  intro J hJ
  have hM₁J : M₁ ⊆ J := hsub.trans hJ
  rw [h J hM₁J, h M₂ hsub]

/-- A finite subset `M` of `I` determines the `x^n`-coefficient in the sum of
a family `(a_i)_{i ∈ I}` if for every finite superset `J` of `M`, the `x^n`-coefficient
of `∑_{i ∈ J} a_i` equals that of `∑_{i ∈ M} a_i`.
(Label: def.fps.determines-xn-coeff part (a)) -/
def DeterminesCoeffInSum (a : I → PowerSeries R) (M : Finset I) (n : ℕ) : Prop :=
  ∀ J : Finset I, M ⊆ J → (∑ i ∈ J, a i).coeff n = (∑ i ∈ M, a i).coeff n

/-!
### Definition of Finitely Determined Coefficients

Definition \ref{def.fps.xn-coeff-fin-determined}
-/

/-- The `x^n`-coefficient in the product of `(a_i)_{i ∈ I}` is finitely determined
if there exists a finite subset `M` that determines it.
(Label: def.fps.xn-coeff-fin-determined part (b)) -/
def CoeffFinitelyDeterminedInProd (a : I → PowerSeries R) (n : ℕ) : Prop :=
  ∃ M : Finset I, DeterminesCoeffInProd a M n

/-- The `x^n`-coefficient in the sum of `(a_i)_{i ∈ I}` is finitely determined
if there exists a finite subset `M` that determines it.
(Label: def.fps.xn-coeff-fin-determined part (a)) -/
def CoeffFinitelyDeterminedInSum (a : I → PowerSeries R) (n : ℕ) : Prop :=
  ∃ M : Finset I, DeterminesCoeffInSum a M n

/-!
### API for Finitely Determined Coefficients

Basic lemmas for `CoeffFinitelyDeterminedInProd` and `CoeffFinitelyDeterminedInSum`.
(Label: def.fps.xn-coeff-fin-determined)
-/

/-- If `M₁` determines the `x^n` coefficient in a sum and `M₁ ⊆ M₂`, then `M₂` also determines it. -/
theorem determinesCoeffInSum_mono {a : I → PowerSeries R} {M₁ M₂ : Finset I} {n : ℕ}
    (h : DeterminesCoeffInSum a M₁ n) (hsub : M₁ ⊆ M₂) : DeterminesCoeffInSum a M₂ n := by
  intro J hJ
  have hM₁J : M₁ ⊆ J := hsub.trans hJ
  rw [h J hM₁J, h M₂ hsub]

/-- For a finite index set, every coefficient in a product is finitely determined.
(Label: def.fps.xn-coeff-fin-determined) -/
theorem coeffFinitelyDeterminedInProd_of_finite [Fintype I] (a : I → PowerSeries R) (n : ℕ) :
    CoeffFinitelyDeterminedInProd a n := by
  use Finset.univ
  intro J hJ
  have hJeq : J = Finset.univ := by
    ext x
    simp only [Finset.mem_univ, iff_true]
    exact hJ (Finset.mem_univ x)
  simp [hJeq]

/-- For a finite index set, every coefficient in a sum is finitely determined.
(Label: def.fps.xn-coeff-fin-determined) -/
theorem coeffFinitelyDeterminedInSum_of_finite [Fintype I] (a : I → PowerSeries R) (n : ℕ) :
    CoeffFinitelyDeterminedInSum a n := by
  use Finset.univ
  intro J hJ
  have hJeq : J = Finset.univ := by
    ext x
    simp only [Finset.mem_univ, iff_true]
    exact hJ (Finset.mem_univ x)
  simp [hJeq]

/-- The empty set determines the `x^n`-coefficient in a sum if and only if
all terms have zero `x^n`-coefficient.
(Label: def.fps.xn-coeff-fin-determined) -/
theorem determinesCoeffInSum_empty_iff (a : I → PowerSeries R) (n : ℕ) :
    DeterminesCoeffInSum a ∅ n ↔ ∀ i : I, (a i).coeff n = 0 := by
  constructor
  · intro h i
    have hJ : (∅ : Finset I) ⊆ {i} := Finset.empty_subset _
    have heq := h {i} hJ
    simp only [Finset.sum_singleton, Finset.sum_empty, map_zero] at heq
    exact heq
  · intro hall J _
    simp only [Finset.sum_empty, map_zero]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    exact hall i

/-- The empty set determines the `x^n`-coefficient in a product if and only if
the product of any finite subset has the same `x^n`-coefficient as 1.
(Label: def.fps.xn-coeff-fin-determined) -/
theorem determinesCoeffInProd_empty_iff (a : I → PowerSeries R) (n : ℕ) :
    DeterminesCoeffInProd a ∅ n ↔ ∀ J : Finset I, (∏ i ∈ J, a i).coeff n = (1 : PowerSeries R).coeff n := by
  constructor
  · intro h J
    have hJ : (∅ : Finset I) ⊆ J := Finset.empty_subset _
    have heq := h J hJ
    simp only [Finset.prod_empty] at heq
    exact heq
  · intro hall J _
    simp only [Finset.prod_empty]
    exact hall J

/-- The value of the finitely determined coefficient in a sum is unique:
for any two determining sets, the coefficient values agree.
(Label: def.fps.xn-coeff-fin-determined) -/
theorem coeffFinitelyDeterminedInSum_value_unique {a : I → PowerSeries R} {n : ℕ}
    {M₁ M₂ : Finset I}
    (hM₁ : DeterminesCoeffInSum a M₁ n) (hM₂ : DeterminesCoeffInSum a M₂ n) :
    (∑ i ∈ M₁, a i).coeff n = (∑ i ∈ M₂, a i).coeff n := by
  classical
  have hM₁_sub : M₁ ⊆ M₁ ∪ M₂ := Finset.subset_union_left
  have hM₂_sub : M₂ ⊆ M₁ ∪ M₂ := Finset.subset_union_right
  rw [← hM₁ (M₁ ∪ M₂) hM₁_sub, hM₂ (M₁ ∪ M₂) hM₂_sub]

/-- The value of the finitely determined coefficient in a product is unique:
for any two determining sets, the coefficient values agree.
(Label: def.fps.xn-coeff-fin-determined) -/
theorem coeffFinitelyDeterminedInProd_value_unique {a : I → PowerSeries R} {n : ℕ}
    {M₁ M₂ : Finset I}
    (hM₁ : DeterminesCoeffInProd a M₁ n) (hM₂ : DeterminesCoeffInProd a M₂ n) :
    (∏ i ∈ M₁, a i).coeff n = (∏ i ∈ M₂, a i).coeff n := by
  classical
  have hM₁_sub : M₁ ⊆ M₁ ∪ M₂ := Finset.subset_union_left
  have hM₂_sub : M₂ ⊆ M₁ ∪ M₂ := Finset.subset_union_right
  rw [← hM₁ (M₁ ∪ M₂) hM₁_sub, hM₂ (M₁ ∪ M₂) hM₂_sub]

/-- If all but finitely many terms have zero `x^n`-coefficient, then the
`x^n`-coefficient in the sum is finitely determined.
(Label: def.fps.xn-coeff-fin-determined) -/
theorem coeffFinitelyDeterminedInSum_of_finite_support (a : I → PowerSeries R) (n : ℕ)
    (h : {i : I | (a i).coeff n ≠ 0}.Finite) : CoeffFinitelyDeterminedInSum a n := by
  classical
  use h.toFinset
  intro J hJ
  rw [← Finset.sum_sdiff hJ, map_add]
  suffices hsuff : (∑ x ∈ J \ h.toFinset, a x).coeff n = 0 by simp [hsuff]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq, not_not] at hi
  exact hi.2

/-!
### Summability and Finite Determination

Proposition \ref{prop.fps.summable=fin-det}
-/

/-- A family of FPS is summable if and only if each coefficient in its sum is finitely determined.
(Label: prop.fps.summable=fin-det part (a)) -/
theorem summable_iff_coeff_finitely_determined (a : I → PowerSeries R) :
    (∀ n : ℕ, {i : I | (a i).coeff n ≠ 0}.Finite) ↔
    (∀ n : ℕ, CoeffFinitelyDeterminedInSum a n) := by
  classical
  constructor
  · -- Forward direction: if only finitely many have non-zero n-th coeff, then finitely determined
    intro hfin n
    -- Take M to be the finite set of indices with non-zero n-th coefficient
    let M := (hfin n).toFinset
    use M
    intro J hMJ
    -- The sum over J equals sum over M plus sum over J \ M
    rw [← Finset.sum_sdiff hMJ]
    simp only [map_add]
    -- The sum over J \ M has zero n-th coefficient
    suffices h : (∑ x ∈ J \ M, a x).coeff n = 0 by simp [h]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_sdiff] at hi
    have hnotM := hi.2
    have : i ∉ (hfin n).toFinset := hnotM
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ne_eq, not_not] at this
    exact this
  · -- Backward direction: if finitely determined, then only finitely many non-zero
    intro hdet n
    obtain ⟨M, hM⟩ := hdet n
    -- Show that any i ∉ M has (a i).coeff n = 0
    apply Set.Finite.subset M.finite_toSet
    intro i hi
    simp only [Finset.mem_coe]
    by_contra h
    -- Consider J = M ∪ {i}
    have hJ : M ⊆ insert i M := Finset.subset_insert i M
    have heq := hM (insert i M) hJ
    rw [Finset.sum_insert h, map_add] at heq
    simp only [Set.mem_setOf_eq, ne_eq] at hi
    -- heq says (a i).coeff n + (∑ M) = (∑ M), so (a i).coeff n = 0
    have hzero : (a i).coeff n = 0 := by
      have h1 : (a i).coeff n + (∑ x ∈ M, a x).coeff n = (∑ x ∈ M, a x).coeff n := heq
      calc (a i).coeff n = (a i).coeff n + (∑ x ∈ M, a x).coeff n - (∑ x ∈ M, a x).coeff n := by ring
        _ = (∑ x ∈ M, a x).coeff n - (∑ x ∈ M, a x).coeff n := by rw [h1]
        _ = 0 := by ring
    exact hi hzero

/-!
### Multipliability

Definition \ref{def.fps.multipliable}
-/

/-- A family `(a_i)_{i ∈ I}` of FPS is multipliable if for each `n ∈ ℕ`,
the `x^n`-coefficient in its product is finitely determined.
(Label: def.fps.multipliable part (a)) -/
def Multipliable (a : I → PowerSeries R) : Prop :=
  ∀ n : ℕ, CoeffFinitelyDeterminedInProd a n

/-- For a multipliable family, the `x^n`-coefficient of the infinite product
is well-defined: it equals the `x^n`-coefficient of any finite partial product
that determines it.
(Label: prop.fps.multipliable.prod-wd) -/
theorem multipliable_coeff_eq_of_determines {a : I → PowerSeries R} {M₁ M₂ : Finset I} {n : ℕ}
    (h₁ : DeterminesCoeffInProd a M₁ n) (h₂ : DeterminesCoeffInProd a M₂ n) :
    (∏ i ∈ M₁, a i).coeff n = (∏ i ∈ M₂, a i).coeff n := by
  classical
  -- Use M₁ ∪ M₂ as a common superset
  have hM₁_sub : M₁ ⊆ M₁ ∪ M₂ := Finset.subset_union_left
  have hM₂_sub : M₂ ⊆ M₁ ∪ M₂ := Finset.subset_union_right
  -- Apply h₁ and h₂ to the union
  have eq₁ := h₁ (M₁ ∪ M₂) hM₁_sub
  have eq₂ := h₂ (M₁ ∪ M₂) hM₂_sub
  -- eq₁ : (∏ i ∈ M₁ ∪ M₂, a i).coeff n = (∏ i ∈ M₁, a i).coeff n
  -- eq₂ : (∏ i ∈ M₁ ∪ M₂, a i).coeff n = (∏ i ∈ M₂, a i).coeff n
  rw [← eq₁, eq₂]

/-!
### The Infinite Product

Definition \ref{def.fps.multipliable} part (b)
-/

/-- For a multipliable family, the `n`-th coefficient of the infinite product.
This is the common value of `(∏ i ∈ M, a i).coeff n` for any finite `M` that
determines the `x^n`-coefficient.
(Label: def.fps.multipliable part (b)) -/
noncomputable def tprodCoeff (a : I → PowerSeries R) (ha : Multipliable a) (n : ℕ) : R :=
  (∏ i ∈ (ha n).choose, a i).coeff n

/-- The infinite product of a multipliable family of formal power series.
For a multipliable family `(a_i)_{i ∈ I}`, this is the FPS whose `x^n`-coefficient
equals the `x^n`-coefficient of any finite partial product that determines it.
(Label: def.fps.multipliable part (b)) -/
noncomputable def tprod (a : I → PowerSeries R) (ha : Multipliable a) : PowerSeries R :=
  PowerSeries.mk (fun n => tprodCoeff a ha n)

/-- The `n`-th coefficient of the infinite product equals the `n`-th coefficient of
any finite partial product that determines it.
(Label: def.fps.multipliable part (b)) -/
theorem tprod_coeff {a : I → PowerSeries R} (ha : Multipliable a) {M : Finset I} {n : ℕ}
    (hM : DeterminesCoeffInProd a M n) :
    (tprod a ha).coeff n = (∏ i ∈ M, a i).coeff n := by
  unfold tprod
  simp only [coeff_mk]
  unfold tprodCoeff
  exact multipliable_coeff_eq_of_determines (ha n).choose_spec hM

/-- For a finite family, the infinite product definition agrees with the finite product.
(Label: prop.fps.multipliable.prod-wd2) -/
theorem tprod_eq_finprod [Fintype I] (a : I → PowerSeries R) (ha : Multipliable a) :
    tprod a ha = ∏ i : I, a i := by
  ext n
  have huniv : DeterminesCoeffInProd a Finset.univ n := by
    intro J hJ
    have hJeq : J = Finset.univ := by
      ext x
      simp only [Finset.mem_univ, iff_true]
      exact hJ (Finset.mem_univ x)
    simp [hJeq]
  rw [tprod_coeff ha huniv]

/-!
### x^n-Approximators

Definition \ref{def.fps.infprod-approx}
-/

/-- A finite subset `M` is an `x^n`-approximator for a family `(a_i)_{i ∈ I}`
if it determines the first `n+1` coefficients (i.e., `x^0, x^1, ..., x^n`)
in the product.
(Label: def.fps.infprod-approx) -/
def IsXnApproximator (a : I → PowerSeries R) (M : Finset I) (n : ℕ) : Prop :=
  ∀ m ≤ n, DeterminesCoeffInProd a M m

/-- An `x^n`-approximator is also an `x^m`-approximator for any `m ≤ n`.
(Label: def.fps.infprod-approx) -/
theorem isXnApproximator_mono {a : I → PowerSeries R} {M : Finset I} {n m : ℕ}
    (hM : IsXnApproximator a M n) (hmn : m ≤ n) : IsXnApproximator a M m := by
  intro k hk
  exact hM k (le_trans hk hmn)

/-- If `M` is an `x^n`-approximator and `M ⊆ N`, then `N` is also an `x^n`-approximator.
(Label: def.fps.infprod-approx) -/
theorem isXnApproximator_superset {a : I → PowerSeries R} {M N : Finset I} {n : ℕ}
    (hM : IsXnApproximator a M n) (hMN : M ⊆ N) : IsXnApproximator a N n := by
  intro m hm
  exact determinesCoeffInProd_mono (hM m hm) hMN

/-- The empty set is an `x^n`-approximator if and only if all `a_i = 1`.
More precisely, if the family has all entries equal to 1, then ∅ is an approximator.
(Label: def.fps.infprod-approx) -/
theorem isXnApproximator_empty_of_forall_eq_one {a : I → PowerSeries R}
    (ha : ∀ i, a i = 1) (n : ℕ) : IsXnApproximator a ∅ n := by
  intro m _ J _
  simp only [Finset.prod_empty]
  have h : ∏ i ∈ J, a i = 1 := by
    apply Finset.prod_eq_one
    intro i _
    exact ha i
  rw [h]

/-- An `x^n`-approximator always determines the `x^n`-coefficient.
(Label: def.fps.infprod-approx) -/
theorem isXnApproximator_determines_coeff {a : I → PowerSeries R} {M : Finset I} {n : ℕ}
    (hM : IsXnApproximator a M n) : DeterminesCoeffInProd a M n :=
  hM n (le_refl n)

/-- For a multipliable family, there exists an `x^n`-approximator for each `n`.
(Label: lem.fps.mulable.approx) -/
theorem exists_xn_approximator [DecidableEq I] (a : I → PowerSeries R) (ha : Multipliable a) (n : ℕ) :
    ∃ M : Finset I, IsXnApproximator a M n := by
  -- For each m ≤ n, get a finite set that determines the x^m coefficient
  have hM : ∀ m ≤ n, ∃ M : Finset I, DeterminesCoeffInProd a M m := fun m _ => ha m
  -- Use classical choice to get the sets
  choose f hf using hM
  -- Take the union of all these sets
  let M := Finset.biUnion (Finset.range (n + 1)) (fun m => if h : m ≤ n then f m h else ∅)
  use M
  intro m hm
  -- Show M determines the x^m coefficient
  apply determinesCoeffInProd_mono (hf m hm)
  -- Show f m hm ⊆ M
  intro i hi
  simp only [M, Finset.mem_biUnion]
  refine ⟨m, ?_, ?_⟩
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  · simp [hm, hi]

/-!
### Lemmas on Irrelevant Factors

Lemma \ref{lem.fps.prod.irlv.1}
-/

/-- If `f` has zero coefficients for `x^0, ..., x^n`, then multiplying by `(1 + f)`
doesn't change the first `n+1` coefficients.
(Label: lem.fps.prod.irlv.1) -/
theorem coeff_mul_one_add_eq_of_coeff_zero {a f : PowerSeries R} {n : ℕ}
    (hf : ∀ m ≤ n, f.coeff m = 0) (m : ℕ) (hm : m ≤ n) :
    (a * (1 + f)).coeff m = a.coeff m := by
  -- Expand: a * (1 + f) = a + a * f
  rw [mul_add, mul_one]
  -- So (a * (1 + f)).coeff m = a.coeff m + (a * f).coeff m
  rw [(coeff m).map_add]
  -- It suffices to show (a * f).coeff m = 0
  suffices (a * f).coeff m = 0 by rw [this, add_zero]
  -- Use the convolution formula for multiplication
  rw [coeff_mul]
  -- Each term in the sum is 0 because f.coeff j = 0 for j ≤ m ≤ n
  apply Finset.sum_eq_zero
  intro ⟨i, j⟩ hij
  rw [Finset.mem_antidiagonal] at hij
  -- Since i + j = m and m ≤ n, we have j ≤ m ≤ n
  have hj : j ≤ n := by omega
  rw [hf j hj, mul_zero]

/-- Extension of the irrelevant factor lemma to finite products.
(Label: lem.fps.prod.irlv.fin) -/
theorem coeff_mul_prod_one_add_eq {a : PowerSeries R} {J : Finset I} {f : I → PowerSeries R}
    {n : ℕ} (hf : ∀ i ∈ J, ∀ m ≤ n, (f i).coeff m = 0) (m : ℕ) (hm : m ≤ n) :
    (a * ∏ i ∈ J, (1 + f i)).coeff m = a.coeff m := by
  classical
  -- Induction on J, generalizing a
  induction J using Finset.induction_on generalizing a with
  | empty => simp
  | insert j J hj ih =>
    rw [Finset.prod_insert hj]
    -- The goal is (a * ((1 + f j) * ∏ i ∈ J, (1 + f i))).coeff m = a.coeff m
    -- Rewrite using associativity
    rw [← mul_assoc]
    -- Now the goal is ((a * (1 + f j)) * ∏ i ∈ J, (1 + f i)).coeff m = a.coeff m
    have hfj : ∀ k ≤ n, (f j).coeff k = 0 := fun k hk => hf j (Finset.mem_insert_self j J) k hk
    -- Apply the induction hypothesis to (a * (1 + f j))
    have hf' : ∀ i ∈ J, ∀ k ≤ n, (f i).coeff k = 0 :=
      fun i hi k hk => hf i (Finset.mem_insert_of_mem hi) k hk
    rw [ih hf']
    -- Now apply the single-factor lemma
    exact coeff_mul_one_add_eq_of_coeff_zero hfj m hm

/-!
### Criterion for Multipliability

Theorem \ref{thm.fps.1+f-mulable}
-/

/-- If `(f_i)_{i ∈ I}` is a summable family of FPS, then `(1 + f_i)_{i ∈ I}` is multipliable.
This is the main criterion for multipliability.
(Label: thm.fps.1+f-mulable) -/
theorem multipliable_one_add_of_summable {f : I → PowerSeries R}
    (hf : ∀ n : ℕ, {i : I | (f i).coeff n ≠ 0}.Finite) :
    Multipliable (fun i => 1 + f i) := by
  classical
  intro n
  -- For each m ≤ n, get the finite set of indices with nonzero m-th coefficient
  let M_m : (m : ℕ) → (hm : m ≤ n) → Finset I := fun m _ => (hf m).toFinset
  -- Take the union of all these sets
  let M : Finset I := Finset.biUnion (Finset.range (n + 1)) fun m =>
    if h : m ≤ n then M_m m h else ∅
  use M
  intro J hMJ
  -- For i ∉ M, we have (f i).coeff m = 0 for all m ≤ n
  have h_zero : ∀ i ∈ J \ M, ∀ m ≤ n, (f i).coeff m = 0 := by
    intro i hi m hm
    simp only [Finset.mem_sdiff] at hi
    obtain ⟨_, hi_not_M⟩ := hi
    -- If (f i).coeff m ≠ 0, then i ∈ M_m m hm ⊆ M
    by_contra h_ne
    apply hi_not_M
    simp only [M, Finset.mem_biUnion, Finset.mem_range]
    refine ⟨m, Nat.lt_succ_of_le hm, ?_⟩
    simp only [hm, dite_true, M_m]
    rw [Set.Finite.mem_toFinset]
    exact h_ne
  -- Split J = M ∪ (J \ M)
  have hJ_split : J = M ∪ (J \ M) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hxM : x ∈ M
      · left; exact hxM
      · right; exact ⟨hx, hxM⟩
    · intro hx
      cases hx with
      | inl h => exact hMJ h
      | inr h => exact h.1
  have h_disj : Disjoint M (J \ M) := Finset.disjoint_sdiff
  -- Rewrite both products
  conv_lhs => rw [hJ_split, Finset.prod_union h_disj]
  -- The product over M is common to both sides
  -- The product over J \ M doesn't change coefficients up to n
  suffices h : ∀ m ≤ n, ((∏ i ∈ M, (1 + f i)) * ∏ i ∈ J \ M, (1 + f i)).coeff m =
      (∏ i ∈ M, (1 + f i)).coeff m by
    exact h n (le_refl n)
  intro m hm
  -- Apply the lemma: multiplying by ∏_{i ∈ J \ M} (1 + f_i) doesn't change first n+1 coeffs
  -- because for i ∈ J \ M, (f i).coeff k = 0 for all k ≤ n
  exact coeff_mul_prod_one_add_eq h_zero m hm

/-!
### Simple Criteria for Multipliability

Proposition \ref{prop.fps.1-mulable} and Remark \ref{rmk.fps.0-mulable}
-/

/-- If all but finitely many entries of a family equal `1`, the family is multipliable.
(Label: prop.fps.1-mulable) -/
theorem multipliable_of_finite_ne_one (a : I → PowerSeries R)
    (h : {i : I | a i ≠ 1}.Finite) : Multipliable a := by
  classical
  intro n
  use h.toFinset
  intro J hMJ
  -- Split J into M ∪ (J \ M) where elements in J \ M have a i = 1
  rw [show J = h.toFinset ∪ (J \ h.toFinset) by simp [Finset.union_sdiff_of_subset hMJ]]
  rw [Finset.prod_union (Finset.disjoint_sdiff)]
  -- For elements in J \ M, we have a i = 1 since they're not in {i | a i ≠ 1}
  have h_ones : ∏ i ∈ (J \ h.toFinset), a i = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have : i ∉ h.toFinset := Finset.mem_sdiff.mp hi |>.2
    rw [Set.Finite.mem_toFinset] at this
    simp only [Set.mem_setOf_eq, not_not] at this
    exact this
  rw [h_ones, mul_one]

/-- The constant 1 family is always multipliable.
The empty set determines all coefficients since `∏_{i ∈ ∅} 1 = 1`.
(Label: def.fps.multipliable) -/
@[simp]
theorem multipliable_const_one : Multipliable (fun _ : I => (1 : PowerSeries R)) := by
  intro n
  use ∅
  intro J _
  simp only [Finset.prod_const_one]

/-- The product of all 1s is 1.
(Label: def.fps.multipliable) -/
@[simp]
theorem tprod_const_one (h : Multipliable (fun _ : I => (1 : PowerSeries R)) := multipliable_const_one) :
    tprod (fun _ : I => (1 : PowerSeries R)) h = 1 := by
  ext n
  have hdet : DeterminesCoeffInProd (fun _ : I => (1 : PowerSeries R)) ∅ n := by
    intro J _
    simp only [Finset.prod_const_one]
  rw [tprod_coeff h hdet]
  simp only [Finset.prod_empty]

/-- For the empty index type, any family is trivially multipliable.
The empty set determines all coefficients since the product is 1.
(Label: def.fps.multipliable) -/
@[simp]
theorem multipliable_empty (a : Empty → PowerSeries R) : Multipliable a := by
  intro n
  use ∅
  intro J _
  congr 1
  apply Finset.prod_eq_one
  intro x _
  exact x.elim

/-- For the empty index type, the infinite product is 1.
(Label: def.fps.multipliable) -/
@[simp]
theorem tprod_empty (a : Empty → PowerSeries R)
    (h : Multipliable a := multipliable_empty a) :
    tprod a h = 1 := by
  ext n
  have hdet : DeterminesCoeffInProd a ∅ n := by
    intro J _
    congr 1
    apply Finset.prod_eq_one
    intro x _
    exact x.elim
  rw [tprod_coeff h hdet]
  simp only [Finset.prod_empty]

/-- For a singleton index type, any family is multipliable.
(Label: def.fps.multipliable) -/
@[simp]
theorem multipliable_singleton [Unique I] (a : I → PowerSeries R) : Multipliable a := by
  intro n
  use {default}
  intro J hJ
  have hJ_eq : J = {default} := by
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro _; exact Unique.eq_default x
    · intro h; subst h; exact hJ (Finset.mem_singleton_self default)
  simp [hJ_eq]

/-- For a singleton index type, the infinite product equals the single element.
(Label: def.fps.multipliable) -/
@[simp]
theorem tprod_singleton [Unique I] (a : I → PowerSeries R)
    (h : Multipliable a := multipliable_singleton a) :
    tprod a h = a default := by
  ext n
  have hdet : DeterminesCoeffInProd a {default} n := by
    intro J hJ
    have hJ_eq : J = {default} := by
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro _; exact Unique.eq_default x
      · intro h'; subst h'; exact hJ (Finset.mem_singleton_self default)
    simp [hJ_eq]
  rw [tprod_coeff h hdet]
  simp only [Finset.prod_singleton]

/-- If a family contains `0` as an entry, it is multipliable (and the product is `0`).
(Label: rmk.fps.0-mulable) -/
theorem multipliable_of_zero_mem (a : I → PowerSeries R) {j : I} (hj : a j = 0) :
    Multipliable a := by
  intro n
  use {j}
  intro J hJ
  have h1 : ∏ i ∈ J, a i = 0 := by
    apply Finset.prod_eq_zero (hJ (Finset.mem_singleton_self j))
    exact hj
  have h2 : ∏ i ∈ {j}, a i = 0 := by
    simp [hj]
  simp [h1, h2]

/-!
### The Binary Product Identity (Infinite Version)

This is the infinite version of the binary product identity, stating that
`∏_{i ∈ ℕ} (1 + x^{2^i}) = 1/(1-x)`.
(Label: eq.fps.prod.binary.2)
-/

/-- The family `(1 + x^{2^i})_{i ∈ ℕ}` is multipliable. -/
theorem multipliable_one_add_pow_two :
    Multipliable (fun i : ℕ => (1 : PowerSeries R) + X ^ (2 ^ i)) := by
  apply multipliable_one_add_of_summable
  intro n
  -- Need to show {i : ℕ | (X ^ 2 ^ i).coeff n ≠ 0}.Finite
  -- (X ^ 2^i).coeff n ≠ 0 iff n = 2^i
  -- For a given n, there is at most one i such that 2^i = n
  have h : {i : ℕ | (X ^ 2 ^ i : PowerSeries R).coeff n ≠ 0} ⊆ {i : ℕ | 2 ^ i = n} := by
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    simp only [coeff_X_pow] at hi
    split_ifs at hi with heq
    · exact heq.symm
    · exact (hi rfl).elim
  apply Set.Finite.subset _ h
  -- Now show {i : ℕ | 2 ^ i = n} is finite
  -- Since 2^i is injective, at most one i satisfies 2^i = n
  have inj : Function.Injective (fun i : ℕ => 2 ^ i) :=
    Nat.pow_right_injective (by omega : 2 > 1)
  -- The set is a subsingleton
  have hs : Set.Subsingleton {i : ℕ | 2 ^ i = n} := by
    intro x hx y hy
    simp only [Set.mem_setOf_eq] at hx hy
    exact inj (hx.trans hy.symm)
  exact hs.finite

/-- Helper lemma: multiplying by (1 + X^k) doesn't change coefficients < k. -/
private lemma coeff_mul_one_add_X_pow' [Nontrivial R] {f : R⟦X⟧} {k n : ℕ} (hk : n < k) :
    (f * (1 + X ^ k)).coeff n = f.coeff n := by
  simp only [mul_add, mul_one, map_add]
  have h : (f * X ^ k).coeff n = 0 := by
    rw [coeff_mul_of_lt_order]
    rw [order_X_pow]
    exact_mod_cast hk
  rw [h, add_zero]

/-- Helper lemma: Finset.range (n + 1) determines the n-th coefficient for the binary product family. -/
private lemma range_determines_coeff_one_add_pow_two' [Nontrivial R] (n : ℕ) :
    DeterminesCoeffInProd (fun i : ℕ => (1 : R⟦X⟧) + X ^ (2 ^ i))
      (Finset.range (n + 1)) n := by
  intro J hJ
  have hJeq : J = Finset.range (n + 1) ∪ (J \ Finset.range (n + 1)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hxn : x < n + 1
      · left; exact Finset.mem_range.mpr hxn
      · right; exact ⟨hx, fun h => hxn (Finset.mem_range.mp h)⟩
    · intro hx
      cases hx with
      | inl h => exact hJ (Finset.mem_range.mpr (Finset.mem_range.mp h))
      | inr h => exact h.1
  conv_lhs => rw [hJeq]
  rw [Finset.prod_union (Finset.disjoint_sdiff)]
  have hprod : ∀ S : Finset ℕ, (∀ i ∈ S, n + 1 ≤ i) →
      ((∏ i ∈ Finset.range (n + 1), ((1 : R⟦X⟧) + X ^ (2 ^ i))) *
       (∏ i ∈ S, ((1 : R⟦X⟧) + X ^ (2 ^ i)))).coeff n =
      (∏ i ∈ Finset.range (n + 1), ((1 : R⟦X⟧) + X ^ (2 ^ i))).coeff n := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.prod_empty, mul_one]
    | @insert a s hnotin ih =>
      intro hS
      rw [Finset.prod_insert hnotin]
      conv_lhs =>
        rw [mul_comm ((1 : R⟦X⟧) + X ^ (2 ^ a)) (∏ x ∈ s, _)]
        rw [← mul_assoc]
      have hk : n + 1 ≤ a := hS a (Finset.mem_insert_self a s)
      have h2k : n < 2 ^ a := by
        calc n < n + 1 := Nat.lt_succ_self n
          _ ≤ a := hk
          _ < 2 ^ a := Nat.lt_pow_self (by norm_num : 1 < 2)
      rw [coeff_mul_one_add_X_pow' h2k]
      apply ih
      intro i hi
      exact hS i (Finset.mem_insert_of_mem hi)
  apply hprod
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hi
  exact hi.2

/-- Helper lemma: (1 - X^k) * f has the same n-th coefficient as f when k > n. -/
private lemma coeff_one_sub_X_pow_mul' [Nontrivial R] {f : R⟦X⟧} {k n : ℕ} (hk : n < k) :
    ((1 - X ^ k) * f).coeff n = f.coeff n := by
  simp only [sub_mul, one_mul, map_sub]
  have h : (X ^ k * f).coeff n = 0 := by
    rw [mul_comm]
    rw [coeff_mul_of_lt_order]
    rw [order_X_pow]
    exact_mod_cast hk
  rw [h, sub_zero]

/-- The infinite product `∏_{i ∈ ℕ} (1 + x^{2^i})` equals `1/(1-x)`.
This relates to the unique binary representation of natural numbers:
each natural number can be written uniquely as a sum of distinct powers of 2.
(Label: eq.fps.prod.binary.2) -/
theorem tprod_one_add_pow_two_eq :
    tprod (fun i : ℕ => (1 : PowerSeries R) + X ^ (2 ^ i)) multipliable_one_add_pow_two =
    invOfUnit (1 - X) 1 := by
  -- Handle the subsingleton case first
  cases subsingleton_or_nontrivial R with
  | inl h => exact Subsingleton.elim _ _
  | inr h =>
    ext n
    -- Use tprod_coeff with M = Finset.range (n + 1)
    have hdet : DeterminesCoeffInProd (fun i : ℕ => (1 : R⟦X⟧) + X ^ (2 ^ i))
        (Finset.range (n + 1)) n := range_determines_coeff_one_add_pow_two' n
    rw [tprod_coeff multipliable_one_add_pow_two hdet]
    -- Now we need to show that the finite product has the same coefficient as invOfUnit (1 - X) 1
    rw [prod_one_add_pow_two_eq n]
    -- The finite product equals (1 - X^{2^{n+1}}) * invOfUnit (1 - X) 1
    -- Since 2^{n+1} > n, the coefficient n of this equals the coefficient n of invOfUnit (1 - X) 1
    have h2n : n < 2 ^ (n + 1) := by
      have hlt : n + 1 < 2 ^ (n + 1) := Nat.lt_pow_self (by norm_num : 1 < 2)
      omega
    exact coeff_one_sub_X_pow_mul' h2n

/-!
### Properties of Infinite Products

Proposition \ref{prop.fps.union-mulable}
-/

/-- If the subfamilies over `J` and `I \ J` are multipliable, then the entire family
is multipliable.
(Label: prop.fps.union-mulable part (a)) -/
theorem multipliable_of_union {a : I → PowerSeries R} {J : Set I}
    (hJ : Multipliable (fun i : J => a i))
    (hIJ : Multipliable (fun i : ↑(Set.univ \ J) => a i)) :
    Multipliable a := by
  classical
  intro n
  -- Get x^n-approximators for each subfamily
  obtain ⟨MJ, hMJ⟩ := exists_xn_approximator (fun i : J => a i) hJ n
  obtain ⟨MIJ, hMIJ⟩ := exists_xn_approximator (fun i : ↑(Set.univ \ J) => a i) hIJ n
  -- Map them to Finset I
  let MJ' : Finset I := MJ.map (Function.Embedding.subtype (· ∈ J))
  let MIJ' : Finset I := MIJ.map (Function.Embedding.subtype (· ∈ (Set.univ \ J)))
  -- The union should determine the coefficient
  use MJ' ∪ MIJ'
  intro K hK
  -- Split K into parts in J and not in J
  let KJ := K.filter (· ∈ J)
  let KIJ := K.filter (· ∉ J)
  -- Key: MJ' ⊆ KJ and MIJ' ⊆ KIJ
  have hMJ'_sub_KJ : MJ' ⊆ KJ := by
    intro x hx
    simp only [KJ, Finset.mem_filter]
    constructor
    · exact hK (Finset.mem_union_left _ hx)
    · simp only [MJ', Finset.mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
      exact hy
  have hMIJ'_sub_KIJ : MIJ' ⊆ KIJ := by
    intro x hx
    simp only [KIJ, Finset.mem_filter]
    constructor
    · exact hK (Finset.mem_union_right _ hx)
    · simp only [MIJ', Finset.mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
      simp only [Set.mem_diff, Set.mem_univ, true_and] at hy
      exact hy
  -- The products split
  have hK_prod : ∏ i ∈ K, a i = (∏ i ∈ KJ, a i) * (∏ i ∈ KIJ, a i) := by
    rw [← Finset.prod_union]
    · congr 1
      ext x
      simp only [KJ, KIJ, Finset.mem_union, Finset.mem_filter]
      tauto
    · simp only [KJ, KIJ, Finset.disjoint_filter]
      intros x _ hxJ hxnJ
      exact hxnJ hxJ
  -- M = MJ' ∪ MIJ' also splits
  have hM_disj : Disjoint MJ' MIJ' := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    simp only [MJ', Finset.mem_map, Function.Embedding.coe_subtype] at hx
    simp only [MIJ', Finset.mem_map, Function.Embedding.coe_subtype] at hy
    obtain ⟨⟨x', hx'⟩, _, hx_eq⟩ := hx
    obtain ⟨⟨y', hy'⟩, _, hy_eq⟩ := hy
    simp only [Set.mem_diff, Set.mem_univ, true_and] at hy'
    rw [← hx_eq, ← hy_eq] at hxy
    simp only at hxy
    rw [hxy] at hx'
    exact hy' hx'
  have hM_prod : ∏ i ∈ MJ' ∪ MIJ', a i = (∏ i ∈ MJ', a i) * (∏ i ∈ MIJ', a i) := by
    exact Finset.prod_union hM_disj
  -- Key: KJ.subtype (· ∈ J) ⊇ MJ as finsets over J
  have hMJ_sub : MJ ⊆ KJ.subtype (· ∈ J) := by
    intro x hx
    rw [Finset.mem_subtype]
    have hx_in_MJ' : (x : I) ∈ MJ' := by
      simp only [MJ', Finset.mem_map, Function.Embedding.coe_subtype]
      exact ⟨x, hx, rfl⟩
    have h := hMJ'_sub_KJ hx_in_MJ'
    simp only [KJ, Finset.mem_filter] at h ⊢
    exact h
  have hMIJ_sub : MIJ ⊆ KIJ.subtype (· ∈ (Set.univ \ J)) := by
    intro x hx
    rw [Finset.mem_subtype]
    have hx_in_MIJ' : (x : I) ∈ MIJ' := by
      simp only [MIJ', Finset.mem_map, Function.Embedding.coe_subtype]
      exact ⟨x, hx, rfl⟩
    have h := hMIJ'_sub_KIJ hx_in_MIJ'
    simp only [KIJ, Finset.mem_filter] at h ⊢
    exact h
  -- Products over KJ and MJ' are equal (as finsets over J)
  have hKJ_eq_subtype : ∏ i ∈ KJ, a i = ∏ i ∈ KJ.subtype (· ∈ J), a i := by
    conv_lhs => rw [show KJ = KJ.filter (· ∈ J) from by ext x; simp [KJ]]
    rw [← Finset.subtype_map (· ∈ J), Finset.prod_map]
    simp only [Function.Embedding.coe_subtype]
  have hKIJ_eq_subtype : ∏ i ∈ KIJ, a i = ∏ i ∈ KIJ.subtype (· ∈ (Set.univ \ J)), a i := by
    conv_lhs => rw [show KIJ = KIJ.filter (· ∈ (Set.univ \ J)) from by
      ext x; simp only [KIJ, Finset.mem_filter, Set.mem_diff, Set.mem_univ, true_and]; tauto]
    rw [← Finset.subtype_map (· ∈ (Set.univ \ J)), Finset.prod_map]
    simp only [Function.Embedding.coe_subtype]
  have hMJ'_eq_subtype : ∏ i ∈ MJ', a i = ∏ i ∈ MJ, a i := by
    simp only [MJ', Finset.prod_map, Function.Embedding.coe_subtype]
  have hMIJ'_eq_subtype : ∏ i ∈ MIJ', a i = ∏ i ∈ MIJ, a i := by
    simp only [MIJ', Finset.prod_map, Function.Embedding.coe_subtype]
  -- Now use the approximator property: for all m ≤ n, the m-th coefficient is determined
  have hJ_approx : ∀ m ≤ n, (∏ i ∈ KJ.subtype (· ∈ J), a i).coeff m = (∏ i ∈ MJ, a i).coeff m := by
    intro m hm
    exact hMJ m hm _ hMJ_sub
  have hIJ_approx : ∀ m ≤ n, (∏ i ∈ KIJ.subtype (· ∈ (Set.univ \ J)), a i).coeff m =
      (∏ i ∈ MIJ, a i).coeff m := by
    intro m hm
    exact hMIJ m hm _ hMIJ_sub
  -- Now we can show the n-th coefficient of the products are equal
  rw [hK_prod, hM_prod, hKJ_eq_subtype, hKIJ_eq_subtype, hMJ'_eq_subtype, hMIJ'_eq_subtype]
  -- The n-th coefficient of a product depends only on coefficients up to n
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  simp only [Finset.mem_antidiagonal] at hij
  have hi : i ≤ n := by omega
  have hj : j ≤ n := by omega
  rw [hJ_approx i hi, hIJ_approx j hj]

/-- The product over `I` equals the product of subproducts over `J` and `I \ J`.
(Label: prop.fps.union-mulable part (b)) -/
theorem tprod_eq_tprod_mul_tprod {a : I → PowerSeries R} {J : Set I}
    (ha : Multipliable a)
    (hJ : Multipliable (fun i : J => a i))
    (hIJ : Multipliable (fun i : ↑(Set.univ \ J) => a i)) :
    tprod a ha = tprod (fun i : J => a i) hJ * tprod (fun i : ↑(Set.univ \ J) => a i) hIJ := by
  classical
  ext n
  -- Get x^n-approximators for each subfamily
  obtain ⟨MJ, hMJ⟩ := exists_xn_approximator (fun i : J => a i) hJ n
  obtain ⟨MIJ, hMIJ⟩ := exists_xn_approximator (fun i : ↑(Set.univ \ J) => a i) hIJ n
  -- Map them to Finset I
  let MJ' : Finset I := MJ.map (Function.Embedding.subtype (· ∈ J))
  let MIJ' : Finset I := MIJ.map (Function.Embedding.subtype (· ∈ (Set.univ \ J)))
  -- M = MJ' ∪ MIJ' determines the coefficient for the full product
  have hM_disj : Disjoint MJ' MIJ' := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    simp only [MJ', Finset.mem_map, Function.Embedding.coe_subtype] at hx
    simp only [MIJ', Finset.mem_map, Function.Embedding.coe_subtype] at hy
    obtain ⟨⟨x', hx'⟩, _, hx_eq⟩ := hx
    obtain ⟨⟨y', hy'⟩, _, hy_eq⟩ := hy
    simp only [Set.mem_diff, Set.mem_univ, true_and] at hy'
    rw [← hx_eq, ← hy_eq] at hxy
    simp only at hxy
    rw [hxy] at hx'
    exact hy' hx'
  have hMJ'_eq : ∏ i ∈ MJ', a i = ∏ i ∈ MJ, a i := by
    simp only [MJ', Finset.prod_map, Function.Embedding.coe_subtype]
  have hMIJ'_eq : ∏ i ∈ MIJ', a i = ∏ i ∈ MIJ, a i := by
    simp only [MIJ', Finset.prod_map, Function.Embedding.coe_subtype]
  -- Show MJ' ∪ MIJ' determines the n-th coefficient
  have hM_det : DeterminesCoeffInProd a (MJ' ∪ MIJ') n := by
    intro K hK
    let KJ := K.filter (· ∈ J)
    let KIJ := K.filter (· ∉ J)
    have hMJ'_sub_KJ : MJ' ⊆ KJ := by
      intro x hx
      simp only [KJ, Finset.mem_filter]
      constructor
      · exact hK (Finset.mem_union_left _ hx)
      · simp only [MJ', Finset.mem_map, Function.Embedding.coe_subtype] at hx
        obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
        exact hy
    have hMIJ'_sub_KIJ : MIJ' ⊆ KIJ := by
      intro x hx
      simp only [KIJ, Finset.mem_filter]
      constructor
      · exact hK (Finset.mem_union_right _ hx)
      · simp only [MIJ', Finset.mem_map, Function.Embedding.coe_subtype] at hx
        obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
        simp only [Set.mem_diff, Set.mem_univ, true_and] at hy
        exact hy
    have hK_prod : ∏ i ∈ K, a i = (∏ i ∈ KJ, a i) * (∏ i ∈ KIJ, a i) := by
      rw [← Finset.prod_union]
      · congr 1
        ext x
        simp only [KJ, KIJ, Finset.mem_union, Finset.mem_filter]
        tauto
      · simp only [KJ, KIJ, Finset.disjoint_filter]
        intros x _ hxJ hxnJ
        exact hxnJ hxJ
    have hM_prod : ∏ i ∈ MJ' ∪ MIJ', a i = (∏ i ∈ MJ', a i) * (∏ i ∈ MIJ', a i) := by
      exact Finset.prod_union hM_disj
    have hMJ_sub : MJ ⊆ KJ.subtype (· ∈ J) := by
      intro x hx
      rw [Finset.mem_subtype]
      have hx_in_MJ' : (x : I) ∈ MJ' := by
        simp only [MJ', Finset.mem_map, Function.Embedding.coe_subtype]
        exact ⟨x, hx, rfl⟩
      have h := hMJ'_sub_KJ hx_in_MJ'
      simp only [KJ, Finset.mem_filter] at h ⊢
      exact h
    have hMIJ_sub : MIJ ⊆ KIJ.subtype (· ∈ (Set.univ \ J)) := by
      intro x hx
      rw [Finset.mem_subtype]
      have hx_in_MIJ' : (x : I) ∈ MIJ' := by
        simp only [MIJ', Finset.mem_map, Function.Embedding.coe_subtype]
        exact ⟨x, hx, rfl⟩
      have h := hMIJ'_sub_KIJ hx_in_MIJ'
      simp only [KIJ, Finset.mem_filter] at h ⊢
      exact h
    have hKJ_eq_subtype : ∏ i ∈ KJ, a i = ∏ i ∈ KJ.subtype (· ∈ J), a i := by
      conv_lhs => rw [show KJ = KJ.filter (· ∈ J) from by ext x; simp [KJ]]
      rw [← Finset.subtype_map (· ∈ J), Finset.prod_map]
      simp only [Function.Embedding.coe_subtype]
    have hKIJ_eq_subtype : ∏ i ∈ KIJ, a i = ∏ i ∈ KIJ.subtype (· ∈ (Set.univ \ J)), a i := by
      conv_lhs => rw [show KIJ = KIJ.filter (· ∈ (Set.univ \ J)) from by
        ext x; simp only [KIJ, Finset.mem_filter, Set.mem_diff, Set.mem_univ, true_and]; tauto]
      rw [← Finset.subtype_map (· ∈ (Set.univ \ J)), Finset.prod_map]
      simp only [Function.Embedding.coe_subtype]
    have hJ_approx : ∀ m ≤ n, (∏ i ∈ KJ.subtype (· ∈ J), a i).coeff m = (∏ i ∈ MJ, a i).coeff m := by
      intro m hm
      exact hMJ m hm _ hMJ_sub
    have hIJ_approx : ∀ m ≤ n, (∏ i ∈ KIJ.subtype (· ∈ (Set.univ \ J)), a i).coeff m =
        (∏ i ∈ MIJ, a i).coeff m := by
      intro m hm
      exact hMIJ m hm _ hMIJ_sub
    rw [hK_prod, hM_prod, hKJ_eq_subtype, hKIJ_eq_subtype, hMJ'_eq, hMIJ'_eq]
    rw [coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro ⟨i, j⟩ hij
    simp only [Finset.mem_antidiagonal] at hij
    have hi : i ≤ n := by omega
    have hj : j ≤ n := by omega
    rw [hJ_approx i hi, hIJ_approx j hj]
  -- Now use tprod_coeff
  rw [tprod_coeff ha hM_det]
  rw [Finset.prod_union hM_disj]
  rw [hMJ'_eq, hMIJ'_eq]
  rw [coeff_mul]
  have hJ_coeff : ∀ m ≤ n, (tprod (fun i : J => a i) hJ).coeff m = (∏ i ∈ MJ, a i).coeff m := by
    intro m hm
    exact tprod_coeff hJ (hMJ m hm)
  have hIJ_coeff : ∀ m ≤ n, (tprod (fun i : ↑(Set.univ \ J) => a i) hIJ).coeff m =
      (∏ i ∈ MIJ, a i).coeff m := by
    intro m hm
    exact tprod_coeff hIJ (hMIJ m hm)
  rw [coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  simp only [Finset.mem_antidiagonal] at hij
  have hi : i ≤ n := by omega
  have hj : j ≤ n := by omega
  rw [hJ_coeff i hi, hIJ_coeff j hj]

/-!
### Product Rule for Multipliable Families

Proposition \ref{prop.fps.prod-mulable}
-/

/-- If `(a_i)` and `(b_i)` are multipliable, then so is `(a_i * b_i)`.
(Label: prop.fps.prod-mulable part (a))

The proof follows the detailed proof in Section sec.details.gf.prod:
1. Get x^n-approximators U and V for families a and b respectively
2. Let M = U ∪ V
3. Show M determines the x^n coefficient for (a_i * b_i)
4. Use the fact that if two pairs of FPS agree up to degree n,
   their products also agree up to degree n -/
theorem multipliable_mul {a b : I → PowerSeries R}
    (ha : Multipliable a) (hb : Multipliable b) :
    Multipliable (fun i => a i * b i) := by
  classical
  intro n
  -- Get x^n-approximators for a and b
  obtain ⟨U, hU⟩ := exists_xn_approximator a ha n
  obtain ⟨V, hV⟩ := exists_xn_approximator b hb n
  -- Let M = U ∪ V
  let M := U ∪ V
  use M
  intro J hJ
  -- We need to show: (∏ i ∈ J, a i * b i).coeff n = (∏ i ∈ M, a i * b i).coeff n
  -- Use the fact that ∏ i ∈ S, a i * b i = (∏ i ∈ S, a i) * (∏ i ∈ S, b i)
  simp only [Finset.prod_mul_distrib]
  -- Now we need: ((∏ J, a) * (∏ J, b)).coeff n = ((∏ M, a) * (∏ M, b)).coeff n
  -- U ⊆ M and V ⊆ M
  have hUM : U ⊆ M := Finset.subset_union_left
  have hVM : V ⊆ M := Finset.subset_union_right
  -- M ⊆ J, so U ⊆ J and V ⊆ J
  have hUJ : U ⊆ J := hUM.trans hJ
  have hVJ : V ⊆ J := hVM.trans hJ
  -- For all m ≤ n: (∏ J, a).coeff m = (∏ M, a).coeff m
  have ha_eq : ∀ m ≤ n, (∏ i ∈ J, a i).coeff m = (∏ i ∈ M, a i).coeff m := by
    intro m hm
    calc (∏ i ∈ J, a i).coeff m
        = (∏ i ∈ U, a i).coeff m := hU m hm J hUJ
      _ = (∏ i ∈ M, a i).coeff m := (hU m hm M hUM).symm
  -- For all m ≤ n: (∏ J, b).coeff m = (∏ M, b).coeff m
  have hb_eq : ∀ m ≤ n, (∏ i ∈ J, b i).coeff m = (∏ i ∈ M, b i).coeff m := by
    intro m hm
    calc (∏ i ∈ J, b i).coeff m
        = (∏ i ∈ V, b i).coeff m := hV m hm J hVJ
      _ = (∏ i ∈ M, b i).coeff m := (hV m hm M hVM).symm
  -- Apply the convolution formula: the n-th coefficient of a product depends only on coefficients up to n
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  simp only [Finset.mem_antidiagonal] at hij
  congr 1
  · exact ha_eq i (by omega)
  · exact hb_eq j (by omega)

/-- The product of `(a_i * b_i)` equals the product of products.
(Label: prop.fps.prod-mulable part (b)) -/
theorem tprod_mul_eq_mul_tprod {a b : I → PowerSeries R}
    (ha : Multipliable a) (hb : Multipliable b)
    (hab : Multipliable (fun i => a i * b i) := multipliable_mul ha hb) :
    tprod (fun i => a i * b i) hab = tprod a ha * tprod b hb := by
  classical
  ext n
  -- Get x^n-approximators for a, b
  obtain ⟨U, hU⟩ := exists_xn_approximator a ha n
  obtain ⟨V, hV⟩ := exists_xn_approximator b hb n
  -- Let M = U ∪ V
  let M := U ∪ V
  have hUM : U ⊆ M := Finset.subset_union_left
  have hVM : V ⊆ M := Finset.subset_union_right
  -- M is also an x^n-approximator for a and for b (since it contains U and V)
  have hM_a : IsXnApproximator a M n := by
    intro m hm J hMJ
    calc (∏ i ∈ J, a i).coeff m
        = (∏ i ∈ U, a i).coeff m := hU m hm J (hUM.trans hMJ)
      _ = (∏ i ∈ M, a i).coeff m := (hU m hm M hUM).symm
  have hM_b : IsXnApproximator b M n := by
    intro m hm J hMJ
    calc (∏ i ∈ J, b i).coeff m
        = (∏ i ∈ V, b i).coeff m := hV m hm J (hVM.trans hMJ)
      _ = (∏ i ∈ M, b i).coeff m := (hV m hm M hVM).symm
  -- Use the approximator property: tprod's coefficients match the finite product's coefficients
  have ha_eq : ∀ m ≤ n, (tprod a ha).coeff m = (∏ i ∈ M, a i).coeff m := by
    intro m hm
    exact tprod_coeff ha (hM_a m hm)
  have hb_eq : ∀ m ≤ n, (tprod b hb).coeff m = (∏ i ∈ M, b i).coeff m := by
    intro m hm
    exact tprod_coeff hb (hM_b m hm)
  -- For the product (a_i * b_i), M is also an x^n-approximator
  have hM_ab : IsXnApproximator (fun i => a i * b i) M n := by
    intro m hm J hMJ
    simp only [Finset.prod_mul_distrib]
    have ha_J_M : ∀ k ≤ m, (∏ i ∈ J, a i).coeff k = (∏ i ∈ M, a i).coeff k := by
      intro k hk
      exact hM_a k (le_trans hk hm) J hMJ
    have hb_J_M : ∀ k ≤ m, (∏ i ∈ J, b i).coeff k = (∏ i ∈ M, b i).coeff k := by
      intro k hk
      exact hM_b k (le_trans hk hm) J hMJ
    -- The m-th coefficient of a product is ∑_{k=0}^m (coeff k of first) * (coeff (m-k) of second)
    simp only [coeff_mul]
    apply Finset.sum_congr rfl
    intro ⟨k₁, k₂⟩ hk
    simp only [Finset.mem_antidiagonal] at hk
    have hk₁ : k₁ ≤ m := by omega
    have hk₂ : k₂ ≤ m := by omega
    rw [ha_J_M k₁ hk₁, hb_J_M k₂ hk₂]
  -- Now compute
  have hab_eq : (tprod (fun i => a i * b i) hab).coeff n = (∏ i ∈ M, (fun i => a i * b i) i).coeff n :=
    tprod_coeff hab (hM_ab n (le_refl n))
  rw [hab_eq]
  simp only [Finset.prod_mul_distrib]
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨k₁, k₂⟩ hk
  simp only [Finset.mem_antidiagonal] at hk
  have hk₁ : k₁ ≤ n := by omega
  have hk₂ : k₂ ≤ n := by omega
  rw [← ha_eq k₁ hk₁, ← hb_eq k₂ hk₂]

/-!
### Division Rule for Multipliable Families

Proposition \ref{prop.fps.div-mulable}
-/

/-- If `(a_i)` and `(b_i)` are multipliable and each `b_i` is invertible,
then `(a_i / b_i)` is multipliable.
(Label: prop.fps.div-mulable part (a))

The proof is similar to multipliable_mul, using the additional fact that
if two FPS agree up to degree n and both have invertible constant terms,
then their Ring.inverses also agree up to degree n. -/
theorem multipliable_div {a b : I → PowerSeries R}
    (ha : Multipliable a) (hb : Multipliable b)
    (hb_inv : ∀ i, IsUnit ((b i).coeff 0)) :
    Multipliable (fun i => a i * Ring.inverse (b i)) := by
  classical
  intro n
  -- Get x^n-approximators for a and b
  obtain ⟨U, hU⟩ := exists_xn_approximator a ha n
  obtain ⟨V, hV⟩ := exists_xn_approximator b hb n
  -- Let M = U ∪ V
  let M := U ∪ V
  use M
  intro J hJ
  -- We need to show: (∏ i ∈ J, a i * Ring.inverse (b i)).coeff n = (∏ i ∈ M, a i * Ring.inverse (b i)).coeff n
  -- Use the finite product formula (inline proof)
  have hprod_inv : ∀ S : Finset I, (∏ i ∈ S, a i * Ring.inverse (b i)) =
      (∏ i ∈ S, a i) * Ring.inverse (∏ i ∈ S, b i) := by
    intro S
    rw [Finset.prod_mul_distrib]
    congr 1
    induction S using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.prod_empty, Ring.inverse_one]
    | insert x s hxs IH =>
      rw [Finset.prod_insert hxs, Finset.prod_insert hxs]
      rw [Ring.mul_inverse_rev, IH]
      ring
  rw [hprod_inv J, hprod_inv M]
  -- U ⊆ M and V ⊆ M
  have hUM : U ⊆ M := Finset.subset_union_left
  have hVM : V ⊆ M := Finset.subset_union_right
  -- M ⊆ J, so U ⊆ J and V ⊆ J
  have hUJ : U ⊆ J := hUM.trans hJ
  have hVJ : V ⊆ J := hVM.trans hJ
  -- For all m ≤ n: (∏ J, a).coeff m = (∏ M, a).coeff m
  have ha_eq : ∀ m ≤ n, (∏ i ∈ J, a i).coeff m = (∏ i ∈ M, a i).coeff m := by
    intro m hm
    calc (∏ i ∈ J, a i).coeff m
        = (∏ i ∈ U, a i).coeff m := hU m hm J hUJ
      _ = (∏ i ∈ M, a i).coeff m := (hU m hm M hUM).symm
  -- For all m ≤ n: (∏ J, b).coeff m = (∏ M, b).coeff m
  have hb_eq : ∀ m ≤ n, (∏ i ∈ J, b i).coeff m = (∏ i ∈ M, b i).coeff m := by
    intro m hm
    calc (∏ i ∈ J, b i).coeff m
        = (∏ i ∈ V, b i).coeff m := hV m hm J hVJ
      _ = (∏ i ∈ M, b i).coeff m := (hV m hm M hVM).symm
  -- IsUnit conditions for the products (inline proof)
  have hconst_prod : ∀ S : Finset I, constantCoeff (∏ i ∈ S, b i) = ∏ i ∈ S, constantCoeff (b i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert x s hxs IH => simp only [Finset.prod_insert hxs, map_mul, IH]
  have hprod_b_J : IsUnit (constantCoeff (∏ i ∈ J, b i)) := by
    rw [hconst_prod]
    apply Finset.prod_induction _ (fun x => IsUnit x) (fun _ _ => IsUnit.mul) isUnit_one
    intro i _
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hb_inv i
  have hprod_b_M : IsUnit (constantCoeff (∏ i ∈ M, b i)) := by
    rw [hconst_prod]
    apply Finset.prod_induction _ (fun x => IsUnit x) (fun _ _ => IsUnit.mul) isUnit_one
    intro i _
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hb_inv i
  -- For all m ≤ n: (Ring.inverse (∏ J, b)).coeff m = (Ring.inverse (∏ M, b)).coeff m
  -- This follows from the fact that if two FPS agree up to degree n and have invertible
  -- constant terms, their Ring.inverses also agree up to degree n.
  -- The full proof is in coeff_Ring_inverse_eq_of_coeff_eq below.
  have hinv_eq : ∀ m ≤ n, (Ring.inverse (∏ i ∈ J, b i)).coeff m = (Ring.inverse (∏ i ∈ M, b i)).coeff m := by
    -- First, show Ring.inverse equals invOfUnit for units
    have hφ_eq : Ring.inverse (∏ i ∈ J, b i) = invOfUnit (∏ i ∈ J, b i) hprod_b_J.unit := by
      have hφ_unit : IsUnit (∏ i ∈ J, b i) := isUnit_iff_constantCoeff.mpr hprod_b_J
      have hmul : (∏ i ∈ J, b i) * invOfUnit (∏ i ∈ J, b i) hprod_b_J.unit = 1 := by
        apply mul_invOfUnit; simp [IsUnit.unit_spec]
      calc Ring.inverse (∏ i ∈ J, b i) = Ring.inverse (∏ i ∈ J, b i) * 1 := (mul_one _).symm
        _ = Ring.inverse (∏ i ∈ J, b i) * ((∏ i ∈ J, b i) * invOfUnit (∏ i ∈ J, b i) hprod_b_J.unit) := by rw [hmul]
        _ = (Ring.inverse (∏ i ∈ J, b i) * (∏ i ∈ J, b i)) * invOfUnit (∏ i ∈ J, b i) hprod_b_J.unit := by ring
        _ = 1 * invOfUnit (∏ i ∈ J, b i) hprod_b_J.unit := by rw [Ring.inverse_mul_cancel (∏ i ∈ J, b i) hφ_unit]
        _ = invOfUnit (∏ i ∈ J, b i) hprod_b_J.unit := one_mul _
    have hψ_eq : Ring.inverse (∏ i ∈ M, b i) = invOfUnit (∏ i ∈ M, b i) hprod_b_M.unit := by
      have hψ_unit : IsUnit (∏ i ∈ M, b i) := isUnit_iff_constantCoeff.mpr hprod_b_M
      have hmul : (∏ i ∈ M, b i) * invOfUnit (∏ i ∈ M, b i) hprod_b_M.unit = 1 := by
        apply mul_invOfUnit; simp [IsUnit.unit_spec]
      calc Ring.inverse (∏ i ∈ M, b i) = Ring.inverse (∏ i ∈ M, b i) * 1 := (mul_one _).symm
        _ = Ring.inverse (∏ i ∈ M, b i) * ((∏ i ∈ M, b i) * invOfUnit (∏ i ∈ M, b i) hprod_b_M.unit) := by rw [hmul]
        _ = (Ring.inverse (∏ i ∈ M, b i) * (∏ i ∈ M, b i)) * invOfUnit (∏ i ∈ M, b i) hprod_b_M.unit := by ring
        _ = 1 * invOfUnit (∏ i ∈ M, b i) hprod_b_M.unit := by rw [Ring.inverse_mul_cancel (∏ i ∈ M, b i) hψ_unit]
        _ = invOfUnit (∏ i ∈ M, b i) hprod_b_M.unit := one_mul _
    rw [hφ_eq, hψ_eq]
    -- Now prove the units are equal
    have huv : (hprod_b_J.unit : R) = hprod_b_M.unit := by
      simp only [IsUnit.unit_spec]
      rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
      exact hb_eq 0 (Nat.zero_le n)
    -- Now prove coefficients of invOfUnit agree using strong induction
    intro m hm
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      cases m with
      | zero =>
        rw [coeff_invOfUnit, coeff_invOfUnit, if_pos rfl, if_pos rfl]
        have huv' : hprod_b_J.unit⁻¹ = hprod_b_M.unit⁻¹ := by
          apply Units.ext
          show (hprod_b_J.unit⁻¹ : Rˣ).val = (hprod_b_M.unit⁻¹ : Rˣ).val
          calc (hprod_b_J.unit⁻¹ : Rˣ).val = Ring.inverse hprod_b_J.unit.val := (Ring.inverse_unit hprod_b_J.unit).symm
            _ = Ring.inverse hprod_b_M.unit.val := by rw [huv]
            _ = (hprod_b_M.unit⁻¹ : Rˣ).val := Ring.inverse_unit hprod_b_M.unit
        rw [huv']
      | succ k =>
        rw [coeff_invOfUnit, coeff_invOfUnit, if_neg (Nat.succ_ne_zero k), if_neg (Nat.succ_ne_zero k)]
        have huv' : hprod_b_J.unit⁻¹ = hprod_b_M.unit⁻¹ := by
          apply Units.ext
          show (hprod_b_J.unit⁻¹ : Rˣ).val = (hprod_b_M.unit⁻¹ : Rˣ).val
          calc (hprod_b_J.unit⁻¹ : Rˣ).val = Ring.inverse hprod_b_J.unit.val := (Ring.inverse_unit hprod_b_J.unit).symm
            _ = Ring.inverse hprod_b_M.unit.val := by rw [huv]
            _ = (hprod_b_M.unit⁻¹ : Rˣ).val := Ring.inverse_unit hprod_b_M.unit
        rw [huv']
        congr 1
        apply Finset.sum_congr rfl
        intro ⟨i, j⟩ hij
        simp only [Finset.mem_antidiagonal] at hij
        split_ifs with hj
        · congr 1
          · exact hb_eq i (by omega)
          · exact ih j hj (by omega)
        · rfl
  -- Apply the convolution formula: the n-th coefficient of a product depends only on coefficients up to n
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  simp only [Finset.mem_antidiagonal] at hij
  congr 1
  · exact ha_eq i (by omega)
  · exact hinv_eq j (by omega)

/-- Key fact: for finite products, inverse distributes (for commutative rings). -/
private lemma finset_prod_inverse [DecidableEq I] {M : Finset I} {b : I → PowerSeries R} :
    Ring.inverse (∏ i ∈ M, b i) = ∏ i ∈ M, Ring.inverse (b i) := by
  induction M using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Ring.inverse_one]
  | insert x s hxs IH =>
    rw [Finset.prod_insert hxs, Finset.prod_insert hxs]
    rw [Ring.mul_inverse_rev, IH]
    ring

/-- For finite products with multiplication by inverses. -/
private lemma finset_prod_mul_inverse [DecidableEq I] {M : Finset I} {a b : I → PowerSeries R} :
    (∏ i ∈ M, a i * Ring.inverse (b i)) = (∏ i ∈ M, a i) * Ring.inverse (∏ i ∈ M, b i) := by
  rw [Finset.prod_mul_distrib, finset_prod_inverse]

/-- If two power series agree up to degree n and have invertible constant terms,
then their Ring.inverses also agree up to degree n. -/
private lemma coeff_invOfUnit_eq_of_coeff_eq {φ ψ : R⟦X⟧} {u : Rˣ} {v : Rˣ} (n : ℕ)
    (huv : (u : R) = v)
    (hφψ : ∀ m ≤ n, φ.coeff m = ψ.coeff m) :
    ∀ m ≤ n, (invOfUnit φ u).coeff m = (invOfUnit ψ v).coeff m := by
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero =>
      rw [coeff_invOfUnit, coeff_invOfUnit, if_pos rfl, if_pos rfl]
      have : u⁻¹ = v⁻¹ := by
        apply Units.ext
        show (u⁻¹ : Rˣ).val = (v⁻¹ : Rˣ).val
        calc (u⁻¹ : Rˣ).val = Ring.inverse u.val := (Ring.inverse_unit u).symm
          _ = Ring.inverse v.val := by rw [huv]
          _ = (v⁻¹ : Rˣ).val := Ring.inverse_unit v
      rw [this]
    | succ k =>
      rw [coeff_invOfUnit, coeff_invOfUnit, if_neg (Nat.succ_ne_zero k), if_neg (Nat.succ_ne_zero k)]
      have huv' : u⁻¹ = v⁻¹ := by
        apply Units.ext
        show (u⁻¹ : Rˣ).val = (v⁻¹ : Rˣ).val
        calc (u⁻¹ : Rˣ).val = Ring.inverse u.val := (Ring.inverse_unit u).symm
          _ = Ring.inverse v.val := by rw [huv]
          _ = (v⁻¹ : Rˣ).val := Ring.inverse_unit v
      rw [huv']
      congr 1
      apply Finset.sum_congr rfl
      intro ⟨i, j⟩ hij
      simp only [Finset.mem_antidiagonal] at hij
      split_ifs with hj
      · congr 1
        · exact hφψ i (by omega)
        · exact ih j hj (by omega)
      · rfl

/-- Corollary for Ring.inverse: if power series agree up to degree n, their inverses do too. -/
private lemma coeff_Ring_inverse_eq_of_coeff_eq {φ ψ : R⟦X⟧} (n : ℕ)
    (hφ : IsUnit (constantCoeff φ))
    (hψ : IsUnit (constantCoeff ψ))
    (hφψ : ∀ m ≤ n, φ.coeff m = ψ.coeff m) :
    ∀ m ≤ n, (Ring.inverse φ).coeff m = (Ring.inverse ψ).coeff m := by
  have hφ_eq : Ring.inverse φ = invOfUnit φ hφ.unit := by
    have hφ_unit : IsUnit φ := isUnit_iff_constantCoeff.mpr hφ
    have hmul : φ * invOfUnit φ hφ.unit = 1 := by apply mul_invOfUnit; simp [IsUnit.unit_spec]
    calc Ring.inverse φ = Ring.inverse φ * 1 := (mul_one _).symm
      _ = Ring.inverse φ * (φ * invOfUnit φ hφ.unit) := by rw [hmul]
      _ = (Ring.inverse φ * φ) * invOfUnit φ hφ.unit := by ring
      _ = 1 * invOfUnit φ hφ.unit := by rw [Ring.inverse_mul_cancel φ hφ_unit]
      _ = invOfUnit φ hφ.unit := one_mul _
  have hψ_eq : Ring.inverse ψ = invOfUnit ψ hψ.unit := by
    have hψ_unit : IsUnit ψ := isUnit_iff_constantCoeff.mpr hψ
    have hmul : ψ * invOfUnit ψ hψ.unit = 1 := by apply mul_invOfUnit; simp [IsUnit.unit_spec]
    calc Ring.inverse ψ = Ring.inverse ψ * 1 := (mul_one _).symm
      _ = Ring.inverse ψ * (ψ * invOfUnit ψ hψ.unit) := by rw [hmul]
      _ = (Ring.inverse ψ * ψ) * invOfUnit ψ hψ.unit := by ring
      _ = 1 * invOfUnit ψ hψ.unit := by rw [Ring.inverse_mul_cancel ψ hψ_unit]
      _ = invOfUnit ψ hψ.unit := one_mul _
  rw [hφ_eq, hψ_eq]
  have huv : (hφ.unit : R) = hψ.unit := by
    simp only [IsUnit.unit_spec]
    rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
    exact hφψ 0 (Nat.zero_le n)
  exact coeff_invOfUnit_eq_of_coeff_eq n huv hφψ

/-- Coefficients of products agree if factors agree up to that degree. -/
private lemma coeff_mul_eq_of_coeff_eq' {φ₁ φ₂ ψ₁ ψ₂ : R⟦X⟧} (n : ℕ)
    (h₁ : ∀ m ≤ n, φ₁.coeff m = ψ₁.coeff m)
    (h₂ : ∀ m ≤ n, φ₂.coeff m = ψ₂.coeff m) :
    ∀ m ≤ n, (φ₁ * φ₂).coeff m = (ψ₁ * ψ₂).coeff m := by
  intro m hm
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  simp only [Finset.mem_antidiagonal] at hij
  congr 1
  · exact h₁ i (by omega)
  · exact h₂ j (by omega)

/-- Constant coefficient of finite product. -/
private lemma constantCoeff_prod [DecidableEq I] {M : Finset I} {c : I → PowerSeries R} :
    constantCoeff (∏ i ∈ M, c i) = ∏ i ∈ M, constantCoeff (c i) := by
  induction M using Finset.induction_on with
  | empty => simp
  | insert x s hxs IH => simp only [Finset.prod_insert hxs, map_mul, IH]

/-- IsUnit of constant coefficient of finite product. -/
private lemma isUnit_constantCoeff_prod [DecidableEq I] {M : Finset I} {c : I → PowerSeries R}
    (h : ∀ i ∈ M, IsUnit (constantCoeff (c i))) :
    IsUnit (constantCoeff (∏ i ∈ M, c i)) := by
  rw [constantCoeff_prod]
  induction M using Finset.induction_on with
  | empty => simp
  | insert x s hxs IH =>
    rw [Finset.prod_insert hxs]
    exact IsUnit.mul (h x (Finset.mem_insert_self x s)) (IH (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The product of `(a_i / b_i)` equals the quotient of products.
(Label: prop.fps.div-mulable part (b)) -/
theorem tprod_div_eq_div_tprod {a b : I → PowerSeries R}
    (ha : Multipliable a) (hb : Multipliable b)
    (hb_inv : ∀ i, IsUnit ((b i).coeff 0))
    (hab : Multipliable (fun i => a i * Ring.inverse (b i)) := multipliable_div ha hb hb_inv) :
    tprod (fun i => a i * Ring.inverse (b i)) hab =
    tprod a ha * Ring.inverse (tprod b hb) := by
  classical
  ext n
  -- Use x^n-approximators to get finite sets that determine all coefficients up to n
  obtain ⟨Ma, hMa⟩ := exists_xn_approximator a ha n
  obtain ⟨Mb, hMb⟩ := exists_xn_approximator b hb n
  obtain ⟨Mab, hMab⟩ := exists_xn_approximator (fun i => a i * Ring.inverse (b i)) hab n
  -- Take the union
  let M := Ma ∪ Mb ∪ Mab
  have hMa' : Ma ⊆ M := Finset.subset_union_left.trans Finset.subset_union_left
  have hMb' : Mb ⊆ M := Finset.subset_union_right.trans Finset.subset_union_left
  have hMab' : Mab ⊆ M := Finset.subset_union_right
  -- M is an approximator for all three families
  have hM_a : IsXnApproximator a M n := fun m hm J hJ =>
    (hMa m hm J (hMa'.trans hJ)).trans (hMa m hm M hMa').symm
  have hM_b : IsXnApproximator b M n := fun m hm J hJ =>
    (hMb m hm J (hMb'.trans hJ)).trans (hMb m hm M hMb').symm
  have hM_ab : IsXnApproximator (fun i => a i * Ring.inverse (b i)) M n := fun m hm J hJ =>
    (hMab m hm J (hMab'.trans hJ)).trans (hMab m hm M hMab').symm
  -- The LHS coefficient
  rw [tprod_coeff hab (hM_ab n (le_refl n))]
  -- Apply the finite product formula
  rw [finset_prod_mul_inverse]
  -- Get coefficient agreement for all m ≤ n
  have ha_eq : ∀ m ≤ n, (∏ i ∈ M, a i).coeff m = (tprod a ha).coeff m :=
    fun m hm => (tprod_coeff ha (hM_a m hm)).symm
  have hb_eq : ∀ m ≤ n, (∏ i ∈ M, b i).coeff m = (tprod b hb).coeff m :=
    fun m hm => (tprod_coeff hb (hM_b m hm)).symm
  -- IsUnit conditions
  have hprod_b : IsUnit (constantCoeff (∏ i ∈ M, b i)) := by
    apply isUnit_constantCoeff_prod
    intro i _; rw [← coeff_zero_eq_constantCoeff_apply]; exact hb_inv i
  have htprod_b : IsUnit (constantCoeff (tprod b hb)) := by
    rw [← coeff_zero_eq_constantCoeff_apply, ← hb_eq 0 (Nat.zero_le n), coeff_zero_eq_constantCoeff_apply]
    exact hprod_b
  -- Inverse coefficient agreement
  have hinv_eq : ∀ m ≤ n, (Ring.inverse (∏ i ∈ M, b i)).coeff m = (Ring.inverse (tprod b hb)).coeff m :=
    coeff_Ring_inverse_eq_of_coeff_eq n hprod_b htprod_b hb_eq
  -- Final step: use product coefficient lemma
  exact coeff_mul_eq_of_coeff_eq' n ha_eq hinv_eq n (le_refl n)

/-!
### Subfamilies of Multipliable Families

Remark \ref{rmk.fps.subfamily-not-mulable} shows that not every subfamily of a
multipliable family is multipliable. However, for invertible FPS, this holds.

Proposition \ref{prop.fps.prods-mulable-subfams}
-/

/-- Helper: finite product of invertible FPS is invertible. -/
private lemma isUnit_coeff_zero_prod {a : I → PowerSeries R} {M : Finset I}
    (h : ∀ i ∈ M, IsUnit ((a i).coeff 0)) :
    IsUnit ((∏ i ∈ M, a i).coeff 0) := by
  classical
  simp only [coeff_zero_eq_constantCoeff, map_prod]
  induction M using Finset.induction_on with
  | empty => simp
  | insert j s' hj ih =>
    rw [Finset.prod_insert hj]
    have h1 : IsUnit (constantCoeff (a j)) := by
      simp only [← coeff_zero_eq_constantCoeff]
      exact h j (Finset.mem_insert_self j s')
    have h2 : IsUnit (∏ x ∈ s', constantCoeff (a x)) := by
      apply ih
      intro i hi
      exact h i (Finset.mem_insert_of_mem hi)
    exact h1.mul h2

/-- Helper: isUnit implies invertible as FPS. -/
private lemma isUnit_prod_of_forall_isUnit_coeff {a : I → PowerSeries R} {M : Finset I}
    (h : ∀ i ∈ M, IsUnit ((a i).coeff 0)) :
    IsUnit (∏ i ∈ M, a i) := by
  rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff]
  exact isUnit_coeff_zero_prod h

/-- Helper: if M determines coefficient n, then any superset also determines it. -/
private lemma DeterminesCoeffInProd.superset' {a : I → PowerSeries R} {M N : Finset I} {n : ℕ}
    (hM : DeterminesCoeffInProd a M n) (hMN : M ⊆ N) :
    DeterminesCoeffInProd a N n := by
  intro J hNJ
  have hMJ : M ⊆ J := hMN.trans hNJ
  calc (∏ i ∈ J, a i).coeff n = (∏ i ∈ M, a i).coeff n := hM J hMJ
    _ = (∏ i ∈ N, a i).coeff n := (hM N hMN).symm

/-- Helper: if M determines coefficient n for the full family,
then for any supersets K₁, K₂ of M, (∏ K₁).coeff n = (∏ K₂).coeff n. -/
private lemma coeff_eq_of_both_contain_determining {a : I → PowerSeries R} {M K₁ K₂ : Finset I} {n : ℕ}
    (hM : DeterminesCoeffInProd a M n) (hMK₁ : M ⊆ K₁) (hMK₂ : M ⊆ K₂) :
    (∏ i ∈ K₁, a i).coeff n = (∏ i ∈ K₂, a i).coeff n := by
  calc (∏ i ∈ K₁, a i).coeff n = (∏ i ∈ M, a i).coeff n := hM K₁ hMK₁
    _ = (∏ i ∈ K₂, a i).coeff n := (hM K₂ hMK₂).symm

/-- Helper: if (A * P).coeff m = (B * P).coeff m for all m ≤ n and P.coeff 0 is a unit,
then A.coeff m = B.coeff m for all m ≤ n. This is useful for "canceling" a common factor
when comparing products that differ only in one fiber. -/
private lemma coeff_eq_of_mul_eq_unit {A B P : PowerSeries R} {n : ℕ}
    (hP : IsUnit (P.coeff 0))
    (h : ∀ m ≤ n, (A * P).coeff m = (B * P).coeff m) :
    ∀ m ≤ n, A.coeff m = B.coeff m := by
  obtain ⟨u, hu⟩ := hP
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ k ih =>
    have hk : k ≤ n := hm
    have hsk := h k hk
    simp only [coeff_mul] at hsk
    -- The sums over p.2 > 0 are equal by IH
    have hrest : ∑ p ∈ (Finset.antidiagonal k).filter (fun p => 0 < p.2), A.coeff p.1 * P.coeff p.2 =
        ∑ p ∈ (Finset.antidiagonal k).filter (fun p => 0 < p.2), B.coeff p.1 * P.coeff p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
      have hp1 : p.1 < k := by omega
      rw [ih p.1 hp1 (le_trans (le_of_lt hp1) hk)]
    -- Split the sums
    have hsplit : ∀ (C : PowerSeries R),
        ∑ p ∈ Finset.antidiagonal k, C.coeff p.1 * P.coeff p.2 =
        C.coeff k * P.coeff 0 +
        ∑ p ∈ (Finset.antidiagonal k).filter (fun p => 0 < p.2), C.coeff p.1 * P.coeff p.2 := by
      intro C
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.antidiagonal k) (fun p => 0 < p.2), add_comm]
      congr 1
      -- The sum over p.2 = 0 is just the (k, 0) term
      have h1 : (Finset.antidiagonal k).filter (fun p => ¬ 0 < p.2) = {(k, 0)} := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_antidiagonal, not_lt, Nat.le_zero,
          Finset.mem_singleton]
        constructor
        · intro ⟨hp, hj⟩; ext <;> simp [hj] at hp ⊢; omega
        · intro hp; simp [hp]
      rw [h1]
      simp
    rw [hsplit A, hsplit B, hrest] at hsk
    have heq : A.coeff k * P.coeff 0 = B.coeff k * P.coeff 0 := add_right_cancel hsk
    rw [← hu] at heq
    -- Use that u is a unit to cancel
    have this : A.coeff k * u = B.coeff k * u := heq
    calc A.coeff k = A.coeff k * 1 := by ring
      _ = A.coeff k * (u * u⁻¹) := by rw [Units.mul_inv]
      _ = A.coeff k * u * u⁻¹ := by ring
      _ = B.coeff k * u * u⁻¹ := by rw [this]
      _ = B.coeff k * (u * u⁻¹) := by ring
      _ = B.coeff k * 1 := by rw [Units.mul_inv]
      _ = B.coeff k := by ring

/-- Key lemma: If U is an x^n-approximator for the full family, and all FPS are invertible,
then U ∩ J is an x^n-approximator for the subfamily J.
This is Lemma lem.fps.prods-mulable-subfams-appr from the tex source.
The invertibility assumption is essential for this lemma. -/
lemma isXnApproximator_inter_subfamily {a : I → PowerSeries R}
    {U : Finset I} {n : ℕ}
    (hU : IsXnApproximator a U n)
    (ha_inv : ∀ i, IsUnit ((a i).coeff 0))
    (J : Set I) :
    IsXnApproximator (fun i : J => a i) 
      (U.preimage (Subtype.val) (Subtype.val_injective.injOn)) n := by
  classical
  intro m hm K hK
  let U_J : Finset J := U.preimage (Subtype.val) (Subtype.val_injective.injOn)
  let K_I : Finset I := K.map ⟨Subtype.val, Subtype.val_injective⟩
  let U_J_I : Finset I := U_J.map ⟨Subtype.val, Subtype.val_injective⟩
  
  have hK_eq : ∏ i ∈ K, a i = ∏ i ∈ K_I, a i := by simp only [K_I, Finset.prod_map]; rfl
  have hU_J_eq : ∏ i ∈ U_J, a i = ∏ i ∈ U_J_I, a i := by simp only [U_J_I, Finset.prod_map]; rfl
  
  rw [hK_eq, hU_J_eq]
  
  have hU_J_I_eq : U_J_I = U.filter (· ∈ J) := by
    ext x
    simp only [U_J_I, U_J, Finset.mem_map, Finset.mem_preimage, Finset.mem_filter]
    constructor
    · intro ⟨j, hj, hjeq⟩; subst hjeq; exact ⟨hj, j.property⟩
    · intro ⟨hxU, hxJ⟩; exact ⟨⟨x, hxJ⟩, hxU, rfl⟩
  
  have hK_I_sub_J : ∀ x ∈ K_I, x ∈ J := by
    intro x hx
    simp only [K_I, Finset.mem_map] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact j.property
  
  have hU_J_sub_K : U_J_I ⊆ K_I := by
    intro x hx
    simp only [U_J_I, K_I, Finset.mem_map] at hx ⊢
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨j, hK hj, rfl⟩
  
  have h_sdiff_eq : U \ K_I = U \ U_J_I := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · intro ⟨hxU, hxK⟩
      refine ⟨hxU, fun hxUJ => hxK ?_⟩
      exact hU_J_sub_K hxUJ
    · intro ⟨hxU, hxUJ⟩
      refine ⟨hxU, fun hxK => hxUJ ?_⟩
      rw [hU_J_I_eq, Finset.mem_filter]
      exact ⟨hxU, hK_I_sub_J x hxK⟩
  
  have hP_eq : ∏ i ∈ U \ K_I, a i = ∏ i ∈ U \ U_J_I, a i := by rw [h_sdiff_eq]
  
  have hP_unit : IsUnit ((∏ i ∈ U \ K_I, a i).coeff 0) := 
    isUnit_coeff_zero_prod (fun i _ => ha_inv i)
  
  have h_eq_all : ∀ k ≤ n, ((∏ i ∈ K_I, a i) * (∏ i ∈ U \ K_I, a i)).coeff k =
      ((∏ i ∈ U_J_I, a i) * (∏ i ∈ U \ K_I, a i)).coeff k := by
    intro k hk
    have hM_decomp : K_I ∪ U = K_I ∪ (U \ K_I) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    have hM'_decomp : U_J_I ∪ U = U_J_I ∪ (U \ U_J_I) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
    have hM_disj : Disjoint K_I (U \ K_I) := Finset.disjoint_sdiff
    have hM'_disj : Disjoint U_J_I (U \ U_J_I) := Finset.disjoint_sdiff
    have hM_prod : ∏ i ∈ K_I ∪ U, a i = (∏ i ∈ K_I, a i) * (∏ i ∈ U \ K_I, a i) := by
      rw [hM_decomp, Finset.prod_union hM_disj]
    have hM'_prod : ∏ i ∈ U_J_I ∪ U, a i = (∏ i ∈ U_J_I, a i) * (∏ i ∈ U \ U_J_I, a i) := by
      rw [hM'_decomp, Finset.prod_union hM'_disj]
    have hM_eq : (∏ i ∈ K_I ∪ U, a i).coeff k = (∏ i ∈ U, a i).coeff k := 
      hU k hk (K_I ∪ U) Finset.subset_union_right
    have hM'_eq : (∏ i ∈ U_J_I ∪ U, a i).coeff k = (∏ i ∈ U, a i).coeff k := 
      hU k hk (U_J_I ∪ U) Finset.subset_union_right
    rw [hM_prod] at hM_eq
    rw [hM'_prod, ← hP_eq] at hM'_eq
    rw [hM_eq, ← hM'_eq]
  
  exact coeff_eq_of_mul_eq_unit hP_unit h_eq_all m hm

/-- If `(a_i)_{i ∈ I}` is a multipliable family of invertible FPS, then any
subfamily is also multipliable.
(Label: prop.fps.prods-mulable-subfams) -/
theorem multipliable_subfamily {a : I → PowerSeries R}
    (ha : Multipliable a)
    (ha_inv : ∀ i, IsUnit ((a i).coeff 0))
    (J : Set I) :
    Multipliable (fun i : J => a i) := by
  classical
  intro n
  -- Get determining sets for coefficients 0, 1, ..., n and take their union
  choose M_k hM_k using fun k => ha k
  let M := Finset.biUnion (Finset.range (n + 1)) M_k

  -- M determines all coefficients up to n
  have hM_all : ∀ k ≤ n, DeterminesCoeffInProd a M k := by
    intro k hk
    apply (hM_k k).superset'
    intro x hx
    simp only [M, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨k, Nat.lt_succ_of_le hk, hx⟩

  -- The determining set for the subfamily is the intersection with J
  let M_J : Finset J := M.preimage (Subtype.val) (fun _ _ _ _ h => Subtype.val_injective h)
  use M_J
  intro N hMN

  -- Convert N and M_J to Finsets of I
  let N_I : Finset I := N.map ⟨Subtype.val, Subtype.val_injective⟩
  let M_J_I : Finset I := M_J.map ⟨Subtype.val, Subtype.val_injective⟩

  have hN_eq : ∏ i ∈ N, a i = ∏ i ∈ N_I, a i := by simp only [N_I, Finset.prod_map]; rfl
  have hMJ_eq : ∏ i ∈ M_J, a i = ∏ i ∈ M_J_I, a i := by simp only [M_J_I, Finset.prod_map]; rfl

  rw [hN_eq, hMJ_eq]

  -- Let K = M ∪ N_I, K' = M ∪ M_J_I (both contain M)
  let K := M ∪ N_I
  let K' := M ∪ M_J_I
  have hMK : M ⊆ K := Finset.subset_union_left
  have hMK' : M ⊆ K' := Finset.subset_union_left

  -- Decompose K and K'
  have hK_decomp : K = N_I ∪ (M \ N_I) := by ext x; simp only [K, Finset.mem_union, Finset.mem_sdiff]; tauto
  have hK'_decomp : K' = M_J_I ∪ (M \ M_J_I) := by ext x; simp only [K', Finset.mem_union, Finset.mem_sdiff]; tauto

  have hK_disj : Disjoint N_I (M \ N_I) := Finset.disjoint_sdiff
  have hK'_disj : Disjoint M_J_I (M \ M_J_I) := Finset.disjoint_sdiff

  have hK_prod : ∏ i ∈ K, a i = (∏ i ∈ N_I, a i) * (∏ i ∈ M \ N_I, a i) := by
    rw [hK_decomp, Finset.prod_union hK_disj]

  have hK'_prod : ∏ i ∈ K', a i = (∏ i ∈ M_J_I, a i) * (∏ i ∈ M \ M_J_I, a i) := by
    rw [hK'_decomp, Finset.prod_union hK'_disj]

  -- M_J_I ⊆ N_I (since M_J ⊆ N)
  have hMJ_sub_N : M_J_I ⊆ N_I := by
    intro x hx
    simp only [M_J_I, N_I, Finset.mem_map] at hx ⊢
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨j, hMN hj, rfl⟩

  -- M_J_I = M ∩ J (as finsets of I)
  have hMJ_I_eq : M_J_I = M.filter (· ∈ J) := by
    ext x
    simp only [M_J_I, M_J, Finset.mem_map, Finset.mem_preimage, Finset.mem_filter]
    constructor
    · intro ⟨j, hj, hjeq⟩; subst hjeq; exact ⟨hj, j.property⟩
    · intro ⟨hxM, hxJ⟩; exact ⟨⟨x, hxJ⟩, hxM, rfl⟩

  -- N_I ⊆ J (all elements of N_I come from J)
  have hN_I_sub_J : ∀ x ∈ N_I, x ∈ J := by
    intro x hx
    simp only [N_I, Finset.mem_map] at hx
    obtain ⟨j, _, rfl⟩ := hx
    exact j.property

  -- Key: M \ N_I = M \ M_J_I
  have h_sdiff_eq : M \ N_I = M \ M_J_I := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · intro ⟨hxM, hxN⟩; exact ⟨hxM, fun hxMJ => hxN (hMJ_sub_N hxMJ)⟩
    · intro ⟨hxM, hxMJ⟩
      refine ⟨hxM, fun hxN => hxMJ ?_⟩
      rw [hMJ_I_eq, Finset.mem_filter]
      exact ⟨hxM, hN_I_sub_J x hxN⟩

  -- The complement product is invertible
  have h_compl_unit : IsUnit (∏ i ∈ M \ N_I, a i) :=
    isUnit_prod_of_forall_isUnit_coeff (fun i _ => ha_inv i)

  obtain ⟨u, hu⟩ := h_compl_unit

  -- Express products in terms of K, K' and u
  have hN_I_eq : ∏ i ∈ N_I, a i = (∏ i ∈ K, a i) * ↑u⁻¹ := by
    have h1 : (∏ i ∈ N_I, a i) * ↑u = ∏ i ∈ K, a i := by rw [hK_prod, ← hu]
    have h2 : ↑u * ↑u⁻¹ = (1 : PowerSeries R) := Units.mul_inv u
    calc ∏ i ∈ N_I, a i
        = (∏ i ∈ N_I, a i) * 1 := by ring
      _ = (∏ i ∈ N_I, a i) * (↑u * ↑u⁻¹) := by rw [h2]
      _ = ((∏ i ∈ N_I, a i) * ↑u) * ↑u⁻¹ := by ring
      _ = (∏ i ∈ K, a i) * ↑u⁻¹ := by rw [h1]

  have hMJ_I_eq' : ∏ i ∈ M_J_I, a i = (∏ i ∈ K', a i) * ↑u⁻¹ := by
    have h1 : (∏ i ∈ M_J_I, a i) * ↑u = ∏ i ∈ K', a i := by
      rw [hK'_prod, ← h_sdiff_eq, ← hu]
    have h2 : ↑u * ↑u⁻¹ = (1 : PowerSeries R) := Units.mul_inv u
    calc ∏ i ∈ M_J_I, a i
        = (∏ i ∈ M_J_I, a i) * 1 := by ring
      _ = (∏ i ∈ M_J_I, a i) * (↑u * ↑u⁻¹) := by rw [h2]
      _ = ((∏ i ∈ M_J_I, a i) * ↑u) * ↑u⁻¹ := by ring
      _ = (∏ i ∈ K', a i) * ↑u⁻¹ := by rw [h1]

  -- Final step: both have the same n-th coefficient
  rw [hN_I_eq, hMJ_I_eq']
  simp only [coeff_mul]
  -- The sums are equal because for each (i, j) with i + j = n:
  -- (∏ K).coeff i = (∏ K').coeff i (since both contain M which determines all coeffs up to n)
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  simp only [Finset.mem_antidiagonal] at hij
  congr 1
  -- (∏ K).coeff i = (∏ K').coeff i follows from hM_all since i ≤ n
  have hi_le_n : i ≤ n := by omega
  exact coeff_eq_of_both_contain_determining (hM_all i hi_le_n) hMK hMK'

/-!
### Reindexing

Proposition \ref{prop.fps.prods-mulable-rules.reindex}
-/

/-- Reindexing a multipliable family via a bijection preserves multipliability.
(Label: prop.fps.prods-mulable-rules.reindex) -/
theorem multipliable_reindex {S T : Type*} {f : S → T} (hf : Function.Bijective f)
    {a : T → PowerSeries R} (ha : Multipliable a) :
    Multipliable (a ∘ f) := by
  intro n
  -- Get the determining set for a
  obtain ⟨M_T, hM_T⟩ := ha n
  -- Use preimage of M_T as our determining set
  let e := Equiv.ofBijective f hf
  let M_S := M_T.preimage f (hf.injective.injOn)
  use M_S
  intro J_S hJ_S
  -- Image of J_S under f
  let J_T := J_S.map ⟨f, hf.injective⟩
  -- Show M_T ⊆ J_T
  have h_subset : M_T ⊆ J_T := by
    intro t ht
    rw [Finset.mem_map]
    have : f (e.symm t) = t := Equiv.apply_symm_apply e t
    use e.symm t
    constructor
    · apply hJ_S
      simp only [Finset.mem_preimage, M_S]
      rw [this]
      exact ht
    · exact this
  -- Use the fact that M_T determines the coefficient
  have h1 : (∏ i ∈ J_T, a i).coeff n = (∏ i ∈ M_T, a i).coeff n := hM_T J_T h_subset
  -- Relate products over J_S and J_T
  have h2 : ∏ s ∈ J_S, (a ∘ f) s = ∏ t ∈ J_T, a t := by
    simp only [Function.comp_apply, J_T]
    rw [Finset.prod_map]
    rfl
  -- Relate products over M_S and M_T
  have h3 : ∏ s ∈ M_S, (a ∘ f) s = ∏ t ∈ M_T, a t := by
    simp only [Function.comp_apply, M_S]
    rw [Finset.prod_preimage_of_bij]
    -- Need to prove Set.BijOn f (f ⁻¹' ↑M_T) ↑M_T
    constructor
    · -- MapsTo
      intro s hs
      exact hs
    · constructor
      · -- InjOn
        exact hf.injective.injOn
      · -- SurjOn
        intro t ht
        use e.symm t
        constructor
        · rw [Set.mem_preimage]
          have : f (e.symm t) = t := Equiv.apply_symm_apply e t
          rw [this]
          exact ht
        · exact Equiv.apply_symm_apply e t
  rw [h2, h3, h1]

/-- Reindexing a multipliable family via a bijection preserves the product.
(Label: prop.fps.prods-mulable-rules.reindex) -/
theorem tprod_reindex {S T : Type*} {f : S → T} (hf : Function.Bijective f)
    {a : T → PowerSeries R} (ha : Multipliable a)
    (haf : Multipliable (a ∘ f) := multipliable_reindex hf ha) :
    tprod (a ∘ f) haf = tprod a ha := by
  classical
  ext n
  -- Get a determining set for a
  obtain ⟨M, hM⟩ := ha n
  -- The preimage is a determining set for a ∘ f
  have hM_preimage : DeterminesCoeffInProd (a ∘ f) (M.preimage f hf.injective.injOn) n := by
    intro J hJ
    have h1 : ∏ i ∈ M.preimage f hf.injective.injOn, (a ∘ f) i = ∏ i ∈ M, a i := by
      simp only [Function.comp_apply]
      apply Finset.prod_preimage f M hf.injective.injOn
      intro t _ ht
      exact (ht (hf.surjective t)).elim
    have h2 : ∏ i ∈ J, (a ∘ f) i = ∏ i ∈ J.image f, a i := by
      rw [Finset.prod_image]
      · simp only [Function.comp_apply]
      · exact fun _ _ _ _ h => hf.injective h
    rw [h2, h1]
    apply hM
    intro t ht
    rw [Finset.mem_image]
    obtain ⟨s, hs⟩ := hf.surjective t
    use s
    constructor
    · apply hJ
      rw [Finset.mem_preimage, hs]
      exact ht
    · exact hs
  -- Use tprod_coeff
  rw [tprod_coeff haf hM_preimage, tprod_coeff ha hM]
  -- Now show the finite products are equal
  simp only [Function.comp_apply]
  congr 1
  apply Finset.prod_preimage f M hf.injective.injOn
  intro t _ ht
  exact (ht (hf.surjective t)).elim

/-!
### Breaking Products into Subproducts

Proposition \ref{prop.fps.prods-mulable-rules.SW1}
-/

/-- The family of subproducts indexed by fibers is multipliable.
(Label: prop.fps.prods-mulable-rules.SW1)

This theorem proves that if a family `(a_s)_{s ∈ S}` of power series is multipliable,
and each fiber `{s : f s = w}` gives a multipliable subfamily, then the family of
fiber products `(tprod_{s : f s = w} a_s)_{w ∈ W}` is also multipliable.

**Note:** The TeX source proof uses Lemma lem.fps.prods-mulable-subfams-appr which
requires invertibility. This Lean proof uses a different approach that avoids the
invertibility assumption: instead of showing each fiber's tprod is x^n-equivalent to 1
(which requires invertibility to "cancel" other fibers), we directly relate the outer
product to the full product via unions of fiber approximators. -/
theorem multipliable_prod_fibers {S W : Type*} {f : S → W} {a : S → PowerSeries R}
    (ha : Multipliable a)
    (ha_fibers : ∀ w : W, Multipliable (fun s : {s : S // f s = w} => a s)) :
    Multipliable (fun w : W => tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)) := by
  classical
  intro n
  -- Get an x^n-approximator U for the full product
  obtain ⟨U, hU⟩ := exists_xn_approximator a ha n
  -- The image f(U) is our candidate for the outer product
  let W_U := U.image f
  use W_U
  intro J hJ
  -- Key lemma: if two families agree on coefficients up to n, their products agree on coeff ≤ n.
  have prod_coeff_eq_of_coeff_eq : ∀ (T : Finset W)
      (t t' : W → PowerSeries R) (m : ℕ) (_ : m ≤ n),
      (∀ i ∈ T, ∀ k ≤ n, (t i).coeff k = (t' i).coeff k) →
      (∏ i ∈ T, t i).coeff m = (∏ i ∈ T, t' i).coeff m := by
    intro T t t' m hm h
    revert hm h
    induction T using Finset.induction_on generalizing m with
    | empty => intro _ _; simp
    | insert x s hxs ih =>
      intro hm h
      rw [Finset.prod_insert hxs, Finset.prod_insert hxs]
      have hx : ∀ k ≤ n, (t x).coeff k = (t' x).coeff k := fun k hk =>
        h x (Finset.mem_insert_self x s) k hk
      have hs : ∀ i ∈ s, ∀ k ≤ n, (t i).coeff k = (t' i).coeff k := fun i hi k hk =>
        h i (Finset.mem_insert_of_mem hi) k hk
      simp only [coeff_mul]
      apply Finset.sum_congr rfl
      intro ⟨i, j⟩ hij
      simp only [Finset.mem_antidiagonal] at hij
      rw [hx i (by omega), ih j (by omega) hs]
  -- For each w, get an x^n-approximator for fiber w that contains U ∩ fiber(w)
  have h_get_approx : ∀ w, ∃ M_w : Finset {s : S // f s = w},
      IsXnApproximator (fun s : {s : S // f s = w} => a s) M_w n ∧
      (U.filter (fun s => f s = w)).subtype (fun s => f s = w) ⊆ M_w := by
    intro w
    obtain ⟨M₀, hM₀⟩ := exists_xn_approximator (fun s : {s : S // f s = w} => a s) (ha_fibers w) n
    let fiberU := (U.filter (fun s => f s = w)).subtype (fun s => f s = w)
    use M₀ ∪ fiberU
    exact ⟨isXnApproximator_superset hM₀ Finset.subset_union_left, Finset.subset_union_right⟩
  choose M_w hM_w using h_get_approx
  -- tprod(fiber w) and ∏_{s ∈ M_w w} a(s) agree on all coefficients up to n
  have h_tprod_eq : ∀ w, ∀ m ≤ n,
      (tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff m =
      (∏ s ∈ M_w w, a s).coeff m := fun w m hm => tprod_coeff (ha_fibers w) ((hM_w w).1 m hm)
  -- The union ⋃_{w ∈ W_U} (M_w w) contains U
  have h_union_contains_U : U ⊆ W_U.biUnion (fun w => (M_w w).map ⟨Subtype.val, Subtype.val_injective⟩) := by
    intro s hs
    simp only [Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk]
    use f s
    constructor
    · exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    · refine ⟨⟨s, rfl⟩, ?_, rfl⟩
      apply (hM_w (f s)).2
      simp only [Finset.mem_subtype, Finset.mem_filter]
      exact ⟨hs, trivial⟩
  have h_union_J_contains_U : U ⊆ J.biUnion (fun w => (M_w w).map ⟨Subtype.val, Subtype.val_injective⟩) := by
    intro s hs
    have h := h_union_contains_U hs
    simp only [Finset.mem_biUnion] at h ⊢
    obtain ⟨w, hw, hs'⟩ := h
    exact ⟨w, hJ hw, hs'⟩
  -- Key step: relate product of tprods to product over S
  have h_prod_eq : ∀ T : Finset W,
      (∏ w ∈ T, tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff n =
      (∏ w ∈ T, ∏ s ∈ M_w w, a s).coeff n := by
    intro T
    apply prod_coeff_eq_of_coeff_eq T _ _ n (le_refl n)
    intro w _ m hm
    exact h_tprod_eq w m hm
  -- Disjoint union: fibers are disjoint
  have h_fibers_disjoint : ∀ w₁ w₂ : W, w₁ ≠ w₂ →
      Disjoint ((M_w w₁).map ⟨Subtype.val, Subtype.val_injective⟩)
               ((M_w w₂).map ⟨Subtype.val, Subtype.val_injective⟩) := by
    intro w₁ w₂ hne
    simp only [Finset.disjoint_iff_ne, Finset.mem_map, Function.Embedding.coeFn_mk]
    intro s₁ ⟨⟨_, h1⟩, _, rfl⟩ s₂ ⟨⟨_, h2⟩, _, rfl⟩ heq
    subst heq
    exact hne (h1.symm.trans h2)
  have h_prod_biUnion : ∀ T : Finset W,
      (∏ w ∈ T, ∏ s ∈ M_w w, a s) =
      ∏ s ∈ T.biUnion (fun w => (M_w w).map ⟨Subtype.val, Subtype.val_injective⟩), a s := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert w T' hw ih =>
      rw [Finset.prod_insert hw, ih]
      rw [Finset.biUnion_insert]
      rw [Finset.prod_union]
      · congr 1
        rw [Finset.prod_map]
        simp only [Function.Embedding.coeFn_mk]
      · simp only [Finset.disjoint_biUnion_right]
        intro w' hw'
        exact h_fibers_disjoint w w' (ne_of_mem_of_not_mem hw' hw).symm
  -- Now combine everything
  rw [h_prod_eq J, h_prod_biUnion J]
  rw [h_prod_eq W_U, h_prod_biUnion W_U]
  rw [hU n (le_refl n) _ h_union_J_contains_U]
  rw [hU n (le_refl n) _ h_union_contains_U]

/-- The family of subproducts indexed by fibers is multipliable (invertible case).
(Label: prop.fps.prods-mulable-rules.SW1)

This is a version of `multipliable_prod_fibers` with an invertibility assumption that
enables a complete proof. The tex source proof implicitly uses invertibility through
Lemma `lem.fps.prods-mulable-subfams-appr`.

When all FPS in the family have unit constant term, we can use `coeff_eq_of_mul_eq_unit`
to cancel common factors and relate fiber products. -/
theorem multipliable_prod_fibers_inv {S W : Type*} {f : S → W} {a : S → PowerSeries R}
    (ha : Multipliable a)
    (ha_inv : ∀ s, IsUnit ((a s).coeff 0))
    (ha_fibers : ∀ w : W, Multipliable (fun s : {s : S // f s = w} => a s)
      := fun w => multipliable_subfamily ha ha_inv {s | f s = w}) :
    Multipliable (fun w : W => tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)) := by
  classical
  intro n
  -- Get an x^n-approximator U for the full product
  obtain ⟨U, hU⟩ := exists_xn_approximator a ha n
  -- The image f(U) is our candidate for the outer product
  let W_U := U.image f
  use W_U
  intro J hJ
  -- Key helper: if b is x^n-equivalent to 1, then (a * b).coeff m = a.coeff m for all m ≤ n
  have coeff_mul_xn_equiv_one : ∀ {a b : PowerSeries R},
      (∀ m ≤ n, b.coeff m = (1 : PowerSeries R).coeff m) →
      ∀ m ≤ n, (a * b).coeff m = a.coeff m := by
    intro a b hb m hm
    have hb0 : b.coeff 0 = 1 := by simpa using hb 0 (Nat.zero_le n)
    have hbk : ∀ k, 1 ≤ k → k ≤ m → b.coeff k = 0 := by
      intro k hk1 hkm
      have := hb k (le_trans hkm hm)
      simp only [coeff_one] at this
      split_ifs at this with h
      · exact absurd h (Nat.one_le_iff_ne_zero.mp hk1)
      · exact this
    simp only [coeff_mul]
    conv_rhs => rw [← mul_one (a.coeff m), ← hb0]
    rw [Finset.sum_eq_single (m, 0)]
    · intro p hp hne
      simp only [Finset.mem_antidiagonal] at hp
      obtain ⟨i, j⟩ := p
      by_cases hj0 : j = 0
      · subst hj0; simp at hp; simp [hp] at hne
      · have hj_pos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
        rw [hbk j hj_pos (by omega)]; ring
    · intro hne; simp at hne
  -- The fiber of U over w
  let fiberFinset : (w : W) → Finset {s : S // f s = w} := fun w =>
    (U.filter (fun s => f s = w)).subtype (fun s => f s = w)
  -- For each w, fiberFinset w determines the first n+1 coefficients for the fiber product
  -- Key insight: use the full product approximator and invertibility to cancel other fibers.
  have h_fiber_determines : ∀ w : W, ∀ m ≤ n,
      DeterminesCoeffInProd (fun s : {s : S // f s = w} => a s) (fiberFinset w) m := by
    intro w m hm K hK
    -- Embed K into S
    let K' : Finset S := K.map ⟨Subtype.val, Subtype.val_injective⟩
    -- K' only contains elements mapping to w
    have hK'_fiber : ∀ s ∈ K', f s = w := fun s hs => by
      simp only [K', Finset.mem_map, Function.Embedding.coeFn_mk] at hs
      obtain ⟨⟨t, ht⟩, _, rfl⟩ := hs
      exact ht
    -- K' ⊇ U.filter (f s = w) since K ⊇ fiberFinset w
    have hK'_contains : U.filter (fun s => f s = w) ⊆ K' := by
      intro s hs
      simp only [Finset.mem_filter] at hs
      have hmem : (⟨s, hs.2⟩ : {s : S // f s = w}) ∈ fiberFinset w := by
        simp only [fiberFinset, Finset.mem_subtype, Finset.mem_filter]
        exact hs
      simp only [K', Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨⟨s, hs.2⟩, hK hmem, rfl⟩
    -- The product over K equals the product over K' (reindexing)
    have h_prod_K_K' : ∏ s ∈ K, a s = ∏ s ∈ K', a s := by
      apply Finset.prod_bij (fun s _ => s.val)
      · intro s hs
        simp only [K', Finset.mem_map, Function.Embedding.coeFn_mk]
        exact ⟨s, hs, rfl⟩
      · intro s₁ _ s₂ _ h; exact Subtype.val_injective h
      · intro s hs
        simp only [K', Finset.mem_map, Function.Embedding.coeFn_mk] at hs
        obtain ⟨t, ht, rfl⟩ := hs
        exact ⟨t, ht, rfl⟩
      · intro s _; rfl
    -- Similarly for fiberFinset w
    have h_prod_fiber : ∏ s ∈ fiberFinset w, a s = ∏ s ∈ U.filter (fun s => f s = w), a s := by
      apply Finset.prod_bij (fun s _ => s.val)
      · intro s hs
        simp only [fiberFinset, Finset.mem_subtype, Finset.mem_filter] at hs
        exact Finset.mem_filter.mpr hs
      · intro s₁ _ s₂ _ h; exact Subtype.val_injective h
      · intro s hs
        simp only [Finset.mem_filter] at hs
        refine ⟨⟨s, hs.2⟩, ?_, rfl⟩
        simp only [fiberFinset, Finset.mem_subtype, Finset.mem_filter]
        exact hs
      · intro s _; rfl
    rw [h_prod_K_K', h_prod_fiber]
    -- Now we need: (∏ K').coeff m = (∏ U.filter w).coeff m
    -- Strategy: decompose the full product by fibers and use cancellation
    let U_w := U.filter (fun s => f s = w)
    let U_other := U.filter (fun s => f s ≠ w)
    -- U = U_w ∪ U_other (disjoint)
    have hU_decomp : U = U_w ∪ U_other := by
      ext s
      simp only [U_w, U_other, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hs; by_cases hfs : f s = w <;> [left; right] <;> exact ⟨hs, by assumption⟩
      · intro h; rcases h with ⟨hs, _⟩ | ⟨hs, _⟩ <;> exact hs
    have hU_disj : Disjoint U_w U_other := by
      simp only [U_w, U_other, Finset.disjoint_filter]
      intro s _ h1 h2; exact h2 h1
    -- K' ∪ U_other contains U (since K' ⊇ U_w)
    have hK'_U_other_contains_U : U ⊆ K' ∪ U_other := by
      rw [hU_decomp]
      intro s hs
      simp only [Finset.mem_union] at hs ⊢
      rcases hs with hs | hs
      · left; exact hK'_contains hs
      · right; exact hs
    -- K' and U_other are disjoint (K' maps to w, U_other doesn't)
    have hK'_U_other_disj : Disjoint K' U_other := by
      simp only [Finset.disjoint_iff_ne]
      intro s₁ hs₁ s₂ hs₂
      have h1 := hK'_fiber s₁ hs₁
      simp only [U_other, Finset.mem_filter] at hs₂
      intro heq; subst heq; exact hs₂.2 h1
    -- Decompose products
    have h_prod_K'_U_other : ∏ s ∈ K' ∪ U_other, a s = (∏ s ∈ K', a s) * (∏ s ∈ U_other, a s) :=
      Finset.prod_union hK'_U_other_disj
    have h_prod_U_decomp : ∏ s ∈ U, a s = (∏ s ∈ U_w, a s) * (∏ s ∈ U_other, a s) := by
      rw [hU_decomp, Finset.prod_union hU_disj]
    -- The product over U_other has unit constant term
    have h_U_other_unit : IsUnit ((∏ s ∈ U_other, a s).coeff 0) :=
      isUnit_coeff_zero_prod (fun i _ => ha_inv i)
    -- Use coeff_eq_of_mul_eq_unit to cancel (∏ U_other)
    have h_coeff_eq : ∀ k ≤ n, ((∏ s ∈ K', a s) * (∏ s ∈ U_other, a s)).coeff k =
        ((∏ s ∈ U_w, a s) * (∏ s ∈ U_other, a s)).coeff k := by
      intro k hk
      calc ((∏ s ∈ K', a s) * (∏ s ∈ U_other, a s)).coeff k
        _ = (∏ s ∈ K' ∪ U_other, a s).coeff k := by rw [h_prod_K'_U_other]
        _ = (∏ s ∈ U, a s).coeff k := hU k hk (K' ∪ U_other) hK'_U_other_contains_U
        _ = ((∏ s ∈ U_w, a s) * (∏ s ∈ U_other, a s)).coeff k := by rw [h_prod_U_decomp]
    exact coeff_eq_of_mul_eq_unit h_U_other_unit h_coeff_eq m hm
  -- For each w, tprod_w has the same first n+1 coeffs as the finite product
  have h_tprod_approx : ∀ w : W, ∀ m ≤ n,
      (tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff m =
      (∏ s ∈ fiberFinset w, a s).coeff m := by
    intro w m hm
    exact tprod_coeff (ha_fibers w) (h_fiber_determines w m hm)
  -- For w ∉ W_U, fiberFinset w = ∅
  have h_empty : ∀ w ∉ W_U, fiberFinset w = ∅ := by
    intro w hw
    simp only [fiberFinset, Finset.subtype_eq_empty]
    intro s hs heq
    rw [Finset.mem_filter] at heq
    exact hw (Finset.mem_image.mpr ⟨s, heq.1, hs⟩)
  -- For w ∉ W_U, tprod_w is x^n-equivalent to 1
  have h_one : ∀ w ∉ W_U, ∀ m ≤ n,
      (tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff m =
      (1 : PowerSeries R).coeff m := by
    intro w hw m hm
    rw [h_tprod_approx w m hm, h_empty w hw]; simp
  -- Split J = W_U ∪ (J \ W_U)
  have hJ_split : J = W_U ∪ (J \ W_U) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx; by_cases hxU : x ∈ W_U <;> [left; right] <;> [exact hxU; exact ⟨hx, hxU⟩]
    · intro hx; rcases hx with hx | ⟨hx, _⟩ <;> [exact hJ hx; exact hx]
  rw [hJ_split, Finset.prod_union (Finset.disjoint_sdiff)]
  -- The product over J \ W_U is x^n-equivalent to 1
  have h_prod_one : ∀ m ≤ n, (∏ w ∈ J \ W_U,
      tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff m =
      (1 : PowerSeries R).coeff m := by
    intro m hm
    have aux : ∀ T : Finset W, T ⊆ J \ W_U → ∀ k ≤ n,
        (∏ w ∈ T, tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff k =
        (1 : PowerSeries R).coeff k := by
      intro T hT
      induction T using Finset.induction_on with
      | empty => intro k _; simp
      | insert x s hxs hrec =>
        intro k hk
        rw [Finset.prod_insert hxs]
        have hx_in : x ∈ J \ W_U := hT (Finset.mem_insert_self x s)
        have hs_sub : s ⊆ J \ W_U := fun y hy => hT (Finset.mem_insert_of_mem hy)
        have hrec' := hrec hs_sub
        rw [coeff_mul_xn_equiv_one hrec' k hk]
        exact h_one x (Finset.mem_sdiff.mp hx_in).2 k hk
    exact aux (J \ W_U) (Finset.Subset.refl _) m hm
  exact coeff_mul_xn_equiv_one h_prod_one n (le_refl n)

/-- A multipliable product can be broken into subproducts indexed by a map.
(Label: prop.fps.prods-mulable-rules.SW1)

This theorem states that if `(a_s)_{s ∈ S}` is a multipliable family of FPS, then the infinite
product can be computed by first grouping elements by their image under `f : S → W`, computing
the infinite product within each fiber, and then taking the infinite product of those results.

**Proof approach:** Rather than trying to show that `U ∩ fiber(w)` determines the coefficient
in the fiber product (which requires invertibility to "cancel" other fibers), we use proper
approximators `M_w` for each fiber from `ha_fibers`, and relate everything through the full
product approximator. This approach follows `multipliable_prod_fibers`. -/
theorem tprod_eq_tprod_fibers {S W : Type*} {f : S → W} {a : S → PowerSeries R}
    (ha : Multipliable a)
    (ha_fibers : ∀ w : W, Multipliable (fun s : {s : S // f s = w} => a s))
    (ha_outer : Multipliable (fun w : W => tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w))
      := multipliable_prod_fibers ha ha_fibers) :
    tprod a ha = tprod (fun w : W => tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w))
      ha_outer := by
  classical
  -- Extensionality: suffices to show coefficients are equal
  ext n
  -- Get an x^n-approximator U for the full product
  obtain ⟨U, hU⟩ := exists_xn_approximator a ha n
  -- The image f(U) serves as an approximator for the outer product
  let W_U := U.image f
  -- The fiber of U over w (as a finset of the subtype)
  let fiberFinset : (w : W) → Finset {s : S // f s = w} := fun w =>
    (U.filter (fun s => f s = w)).subtype (fun s => f s = w)
  -- Key insight: Use proper approximators M_w from ha_fibers instead of fiberFinset w.
  -- This avoids the invertibility requirement of the tex proof.
  -- For each w, get an x^n-approximator for fiber w that contains fiberFinset w
  have h_get_approx : ∀ w, ∃ M_w : Finset {s : S // f s = w},
      IsXnApproximator (fun s : {s : S // f s = w} => a s) M_w n ∧
      fiberFinset w ⊆ M_w := by
    intro w
    obtain ⟨M₀, hM₀⟩ := exists_xn_approximator (fun s : {s : S // f s = w} => a s) (ha_fibers w) n
    use M₀ ∪ fiberFinset w
    exact ⟨isXnApproximator_superset hM₀ Finset.subset_union_left, Finset.subset_union_right⟩
  choose M_w hM_w using h_get_approx
  -- tprod(fiber w) and ∏_{s ∈ M_w w} a(s) agree on all coefficients up to n
  have h_tprod_eq : ∀ w, ∀ m ≤ n,
      (tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff m =
      (∏ s ∈ M_w w, a s).coeff m := fun w m hm => tprod_coeff (ha_fibers w) ((hM_w w).1 m hm)
  -- Helper: products preserve coefficient equality on first n+1 coefficients
  have prod_coeff_eq_of_coeff_eq : ∀ (T : Finset W)
      (t t' : W → PowerSeries R) (m : ℕ) (_ : m ≤ n),
      (∀ i ∈ T, ∀ k ≤ n, (t i).coeff k = (t' i).coeff k) →
      (∏ i ∈ T, t i).coeff m = (∏ i ∈ T, t' i).coeff m := by
    intro T t t' m hm h
    revert hm h
    induction T using Finset.induction_on generalizing m with
    | empty => intro _ _; simp
    | insert x s hxs ih =>
      intro hm h
      rw [Finset.prod_insert hxs, Finset.prod_insert hxs]
      have hx : ∀ k ≤ n, (t x).coeff k = (t' x).coeff k := fun k hk =>
        h x (Finset.mem_insert_self x s) k hk
      have hs : ∀ i ∈ s, ∀ k ≤ n, (t i).coeff k = (t' i).coeff k := fun i hi k hk =>
        h i (Finset.mem_insert_of_mem hi) k hk
      simp only [coeff_mul]
      apply Finset.sum_congr rfl
      intro ⟨i, j⟩ hij
      simp only [Finset.mem_antidiagonal] at hij
      rw [hx i (by omega), ih j (by omega) hs]
  -- The union ⋃_{w ∈ W_U} (M_w w) contains U
  have h_union_contains_U : U ⊆ W_U.biUnion (fun w => (M_w w).map ⟨Subtype.val, Subtype.val_injective⟩) := by
    intro s hs
    simp only [Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk]
    use f s
    constructor
    · exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    · refine ⟨⟨s, rfl⟩, ?_, rfl⟩
      apply (hM_w (f s)).2
      simp only [fiberFinset, Finset.mem_subtype, Finset.mem_filter]
      exact ⟨hs, trivial⟩
  -- Key step: relate product of tprods to product over S
  have h_prod_eq : ∀ T : Finset W,
      (∏ w ∈ T, tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff n =
      (∏ w ∈ T, ∏ s ∈ M_w w, a s).coeff n := by
    intro T
    apply prod_coeff_eq_of_coeff_eq T _ _ n (le_refl n)
    intro w _ m hm
    exact h_tprod_eq w m hm
  -- Disjoint union: fibers are disjoint
  have h_fibers_disjoint : ∀ w₁ w₂ : W, w₁ ≠ w₂ →
      Disjoint ((M_w w₁).map ⟨Subtype.val, Subtype.val_injective⟩)
               ((M_w w₂).map ⟨Subtype.val, Subtype.val_injective⟩) := by
    intro w₁ w₂ hne
    simp only [Finset.disjoint_iff_ne, Finset.mem_map, Function.Embedding.coeFn_mk]
    intro s₁ ⟨⟨_, h1⟩, _, rfl⟩ s₂ ⟨⟨_, h2⟩, _, rfl⟩ heq
    subst heq
    exact hne (h1.symm.trans h2)
  have h_prod_biUnion : ∀ T : Finset W,
      (∏ w ∈ T, ∏ s ∈ M_w w, a s) =
      ∏ s ∈ T.biUnion (fun w => (M_w w).map ⟨Subtype.val, Subtype.val_injective⟩), a s := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert w T' hw ih =>
      rw [Finset.prod_insert hw, ih]
      rw [Finset.biUnion_insert]
      rw [Finset.prod_union]
      · congr 1
        rw [Finset.prod_map]
        simp only [Function.Embedding.coeFn_mk]
      · simp only [Finset.disjoint_biUnion_right]
        intro w' hw'
        exact h_fibers_disjoint w w' (ne_of_mem_of_not_mem hw' hw).symm
  -- W_U determines the outer coefficient
  have hW_U_det : DeterminesCoeffInProd
      (fun w : W => tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)) W_U n := by
    intro J hJ
    have h_union_J_contains_U : U ⊆ J.biUnion (fun w => (M_w w).map ⟨Subtype.val, Subtype.val_injective⟩) := by
      intro s hs
      have h := h_union_contains_U hs
      simp only [Finset.mem_biUnion] at h ⊢
      obtain ⟨w, hw, hs'⟩ := h
      exact ⟨w, hJ hw, hs'⟩
    rw [h_prod_eq J, h_prod_biUnion J]
    rw [h_prod_eq W_U, h_prod_biUnion W_U]
    rw [hU n (le_refl n) _ h_union_J_contains_U]
    rw [hU n (le_refl n) _ h_union_contains_U]
  -- Now combine everything
  rw [tprod_coeff ha (hU n (le_refl n))]
  rw [tprod_coeff ha_outer hW_U_det]
  rw [h_prod_eq W_U, h_prod_biUnion W_U]
  exact (hU n (le_refl n) _ h_union_contains_U).symm

/-- A multipliable product can be broken into subproducts indexed by a map (invertible case).
(Label: prop.fps.prods-mulable-rules.SW1)

This is a version of `tprod_eq_tprod_fibers` with an invertibility assumption that
enables a complete proof. The tex source proof implicitly uses invertibility through
Lemma `lem.fps.prods-mulable-subfams-appr`.

When all FPS in the family have unit constant term, we can use `coeff_eq_of_mul_eq_unit`
to cancel common factors and relate fiber products. -/
theorem tprod_eq_tprod_fibers_inv {S W : Type*} {f : S → W} {a : S → PowerSeries R}
    (ha : Multipliable a)
    (ha_inv : ∀ s, IsUnit ((a s).coeff 0))
    (ha_fibers : ∀ w : W, Multipliable (fun s : {s : S // f s = w} => a s)
      := fun w => multipliable_subfamily ha ha_inv {s | f s = w})
    (ha_outer : Multipliable (fun w : W => tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w))
      := multipliable_prod_fibers_inv ha ha_inv ha_fibers) :
    tprod a ha = tprod (fun w : W => tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w))
      ha_outer := by
  classical
  -- Extensionality: suffices to show coefficients are equal
  ext n
  -- Get an x^n-approximator U for the full product
  obtain ⟨U, hU⟩ := exists_xn_approximator a ha n
  -- The image f(U) serves as an approximator for the outer product
  let W_U := U.image f
  -- Key helper: if b is x^n-equivalent to 1, then (a * b).coeff m = a.coeff m for all m ≤ n
  have coeff_mul_xn_equiv_one : ∀ {a b : PowerSeries R},
      (∀ m ≤ n, b.coeff m = (1 : PowerSeries R).coeff m) →
      ∀ m ≤ n, (a * b).coeff m = a.coeff m := by
    intro a b hb m hm
    have hb0 : b.coeff 0 = 1 := by simpa using hb 0 (Nat.zero_le n)
    have hbk : ∀ k, 1 ≤ k → k ≤ m → b.coeff k = 0 := by
      intro k hk1 hkm
      have := hb k (le_trans hkm hm)
      simp only [coeff_one] at this
      split_ifs at this with h
      · exact absurd h (Nat.one_le_iff_ne_zero.mp hk1)
      · exact this
    simp only [coeff_mul]
    conv_rhs => rw [← mul_one (a.coeff m), ← hb0]
    rw [Finset.sum_eq_single (m, 0)]
    · intro p hp hne
      simp only [Finset.mem_antidiagonal] at hp
      obtain ⟨i, j⟩ := p
      by_cases hj0 : j = 0
      · subst hj0; simp at hp; simp [hp] at hne
      · have hj_pos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
        rw [hbk j hj_pos (by omega)]; ring
    · intro hne; simp at hne
  -- The fiber of U over w (as a finset of the subtype)
  let fiberFinset : (w : W) → Finset {s : S // f s = w} := fun w =>
    (U.filter (fun s => f s = w)).subtype (fun s => f s = w)
  -- For w ∉ W_U, fiberFinset w = ∅
  have h_empty : ∀ w ∉ W_U, fiberFinset w = ∅ := by
    intro w hw
    simp only [fiberFinset, Finset.subtype_eq_empty]
    intro s hs heq
    rw [Finset.mem_filter] at heq
    exact hw (Finset.mem_image.mpr ⟨s, heq.1, hs⟩)
  -- For w ∉ W_U, the fiber product is 1
  have h_fiber_empty : ∀ w ∉ W_U, ∏ s ∈ fiberFinset w, a s = 1 := by
    intro w hw; rw [h_empty w hw]; simp
  -- The finite product over U.filter (f s = w) equals the product over fiberFinset w
  have h_fiber_prod_eq : ∀ w, ∏ s ∈ U.filter (fun s => f s = w), a s = ∏ s ∈ fiberFinset w, a s := by
    intro w
    apply Finset.prod_bij (fun s hs => ⟨s, (Finset.mem_filter.mp hs).2⟩)
    · intro s hs
      simp only [fiberFinset, Finset.mem_subtype, Finset.mem_filter]
      exact Finset.mem_filter.mp hs
    · intro s₁ hs₁ s₂ hs₂ heq
      exact congrArg Subtype.val heq
    · intro ⟨s, hs⟩ hs_mem
      simp only [fiberFinset, Finset.mem_subtype, Finset.mem_filter] at hs_mem
      exact ⟨s, Finset.mem_filter.mpr ⟨hs_mem.1, hs⟩, rfl⟩
    · intro s hs; rfl
  -- For each w, fiberFinset w determines the first n+1 coefficients for the fiber product
  have h_fiber_determines : ∀ w : W, ∀ m ≤ n,
      DeterminesCoeffInProd (fun s : {s : S // f s = w} => a s) (fiberFinset w) m := by
    intro w m hm K hK
    -- Embed K into S
    let K' : Finset S := K.map ⟨Subtype.val, Subtype.val_injective⟩
    -- K' contains exactly elements mapping to w
    have hK'_fiber : ∀ s ∈ K', f s = w := fun s hs => by
      simp only [K', Finset.mem_map, Function.Embedding.coeFn_mk] at hs
      obtain ⟨⟨t, ht⟩, _, rfl⟩ := hs
      exact ht
    -- K' ⊇ U.filter (f s = w) since K ⊇ fiberFinset w
    have hK'_contains : U.filter (fun s => f s = w) ⊆ K' := by
      intro s hs
      simp only [Finset.mem_filter] at hs
      have hmem : (⟨s, hs.2⟩ : {s : S // f s = w}) ∈ fiberFinset w := by
        simp only [fiberFinset, Finset.mem_subtype, Finset.mem_filter]
        exact hs
      simp only [K', Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨⟨s, hs.2⟩, hK hmem, rfl⟩
    -- The product over K equals the product over K' (reindexing)
    have h_prod_K_K' : ∏ s ∈ K, a s = ∏ s ∈ K', a s := by
      apply Finset.prod_bij (fun s _ => s.val)
      · intro s hs
        simp only [K', Finset.mem_map, Function.Embedding.coeFn_mk]
        exact ⟨s, hs, rfl⟩
      · intro s₁ _ s₂ _ h; exact Subtype.val_injective h
      · intro s hs
        simp only [K', Finset.mem_map, Function.Embedding.coeFn_mk] at hs
        obtain ⟨t, ht, rfl⟩ := hs
        exact ⟨t, ht, rfl⟩
      · intro s _; rfl
    -- Similarly for fiberFinset w
    have h_prod_fiber : ∏ s ∈ fiberFinset w, a s = ∏ s ∈ U.filter (fun s => f s = w), a s := by
      apply Finset.prod_bij (fun s _ => s.val)
      · intro s hs
        simp only [fiberFinset, Finset.mem_subtype, Finset.mem_filter] at hs
        exact Finset.mem_filter.mpr hs
      · intro s₁ _ s₂ _ h; exact Subtype.val_injective h
      · intro s hs
        simp only [Finset.mem_filter] at hs
        refine ⟨⟨s, hs.2⟩, ?_, rfl⟩
        simp only [fiberFinset, Finset.mem_subtype, Finset.mem_filter]
        exact hs
      · intro s _; rfl
    rw [h_prod_K_K', h_prod_fiber]
    -- Now we need: (∏ K').coeff m = (∏ U.filter w).coeff m
    -- Strategy: decompose the full product by fibers and use cancellation
    let U_w := U.filter (fun s => f s = w)
    let U_other := U.filter (fun s => f s ≠ w)
    -- U = U_w ∪ U_other (disjoint)
    have hU_decomp : U = U_w ∪ U_other := by
      ext s
      simp only [U_w, U_other, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hs; by_cases hfs : f s = w <;> [left; right] <;> exact ⟨hs, by assumption⟩
      · intro h; rcases h with ⟨hs, _⟩ | ⟨hs, _⟩ <;> exact hs
    have hU_disj : Disjoint U_w U_other := by
      simp only [U_w, U_other, Finset.disjoint_filter]
      intro s _ h1 h2; exact h2 h1
    -- K' ∪ U_other contains U (since K' ⊇ U_w)
    have hK'_U_other_contains_U : U ⊆ K' ∪ U_other := by
      rw [hU_decomp]
      intro s hs
      simp only [Finset.mem_union] at hs ⊢
      rcases hs with hs | hs
      · left; exact hK'_contains hs
      · right; exact hs
    -- K' and U_other are disjoint (K' maps to w, U_other doesn't)
    have hK'_U_other_disj : Disjoint K' U_other := by
      simp only [Finset.disjoint_iff_ne]
      intro s₁ hs₁ s₂ hs₂
      have h1 := hK'_fiber s₁ hs₁
      simp only [U_other, Finset.mem_filter] at hs₂
      intro heq; subst heq; exact hs₂.2 h1
    -- Decompose products
    have h_prod_K'_U_other : ∏ s ∈ K' ∪ U_other, a s = (∏ s ∈ K', a s) * (∏ s ∈ U_other, a s) :=
      Finset.prod_union hK'_U_other_disj
    have h_prod_U_decomp : ∏ s ∈ U, a s = (∏ s ∈ U_w, a s) * (∏ s ∈ U_other, a s) := by
      rw [hU_decomp, Finset.prod_union hU_disj]
    -- The product over U_other has unit constant term
    have h_U_other_unit : IsUnit ((∏ s ∈ U_other, a s).coeff 0) :=
      isUnit_coeff_zero_prod (fun i _ => ha_inv i)
    -- Use coeff_eq_of_mul_eq_unit to cancel (∏ U_other)
    have h_coeff_eq : ∀ k ≤ n, ((∏ s ∈ K', a s) * (∏ s ∈ U_other, a s)).coeff k =
        ((∏ s ∈ U_w, a s) * (∏ s ∈ U_other, a s)).coeff k := by
      intro k hk
      calc ((∏ s ∈ K', a s) * (∏ s ∈ U_other, a s)).coeff k
        _ = (∏ s ∈ K' ∪ U_other, a s).coeff k := by rw [h_prod_K'_U_other]
        _ = (∏ s ∈ U, a s).coeff k := hU k hk (K' ∪ U_other) hK'_U_other_contains_U
        _ = ((∏ s ∈ U_w, a s) * (∏ s ∈ U_other, a s)).coeff k := by rw [h_prod_U_decomp]
    exact coeff_eq_of_mul_eq_unit h_U_other_unit h_coeff_eq m hm
  have h_tprod_approx : ∀ w : W, ∀ m ≤ n,
      (tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff m =
      (∏ s ∈ fiberFinset w, a s).coeff m := by
    intro w m hm; exact tprod_coeff (ha_fibers w) (h_fiber_determines w m hm)
  -- For w ∉ W_U, tprod_w is x^n-equivalent to 1
  have h_one : ∀ w ∉ W_U, ∀ m ≤ n,
      (tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff m =
      (1 : PowerSeries R).coeff m := by
    intro w hw m hm
    rw [h_tprod_approx w m hm, h_fiber_empty w hw]
  -- Use tprod_coeff to relate LHS to finite product
  rw [tprod_coeff ha (hU n (le_refl n))]
  -- Decompose the product over U into fiber products
  have h_decomp : ∏ s ∈ U, a s = ∏ w ∈ W_U, ∏ s ∈ U.filter (fun s => f s = w), a s := by
    rw [← Finset.prod_biUnion]
    · congr 1; ext s
      simp only [Finset.mem_biUnion, Finset.mem_filter, W_U]
      constructor
      · intro hs
        refine ⟨f s, ?_, hs, rfl⟩
        exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
      · intro ⟨_, _, hs, _⟩; exact hs
    · intro w1 _ w2 _ hne
      simp only [Function.onFun, Finset.disjoint_filter]
      intro s _ hs1 hs2; exact hne (hs1.symm.trans hs2)
  rw [h_decomp]
  -- W_U determines the outer coefficient
  have hW_U_det : DeterminesCoeffInProd
      (fun w : W => tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)) W_U n := by
    intro J hJ
    have hJ_split : J = W_U ∪ (J \ W_U) := by
      ext x; simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hx; by_cases hxU : x ∈ W_U <;> [left; right] <;> [exact hxU; exact ⟨hx, hxU⟩]
      · intro hx; rcases hx with hx | ⟨hx, _⟩ <;> [exact hJ hx; exact hx]
    rw [hJ_split, Finset.prod_union (Finset.disjoint_sdiff)]
    have h_prod_one : ∀ m ≤ n, (∏ w ∈ J \ W_U,
        tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff m =
        (1 : PowerSeries R).coeff m := by
      intro m hm
      have aux : ∀ T : Finset W, T ⊆ J \ W_U → ∀ k ≤ n,
          (∏ w ∈ T, tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff k =
          (1 : PowerSeries R).coeff k := by
        intro T hT
        induction T using Finset.induction_on with
        | empty => intro k _; simp
        | insert x s hxs hrec =>
          intro k hk
          rw [Finset.prod_insert hxs]
          have hx_in : x ∈ J \ W_U := hT (Finset.mem_insert_self x s)
          have hs_sub : s ⊆ J \ W_U := fun y hy => hT (Finset.mem_insert_of_mem hy)
          have hrec' := hrec hs_sub
          rw [coeff_mul_xn_equiv_one hrec' k hk]
          exact h_one x (Finset.mem_sdiff.mp hx_in).2 k hk
      exact aux (J \ W_U) (Finset.Subset.refl _) m hm
    exact coeff_mul_xn_equiv_one h_prod_one n (le_refl n)
  -- Use multipliable_coeff_eq_of_determines
  rw [tprod_coeff ha_outer hW_U_det]
  -- Now show the finite products have the same n-th coefficient
  -- Key: for each w ∈ W_U, the factors agree on first n+1 coefficients
  have h_factors_agree : ∀ w ∈ W_U, ∀ m ≤ n,
      (∏ s ∈ U.filter (fun s => f s = w), a s).coeff m =
      (tprod (fun s : {s : S // f s = w} => a s) (ha_fibers w)).coeff m := by
    intro w _ m hm
    rw [h_fiber_prod_eq w, h_tprod_approx w m hm]
  -- The n-th coefficient of a product depends only on the first n+1 coefficients of factors
  have h_prod_coeff_eq_gen : ∀ (T : Finset W) (g₁ g₂ : W → PowerSeries R),
      (∀ w ∈ T, ∀ m ≤ n, (g₁ w).coeff m = (g₂ w).coeff m) →
      ∀ k ≤ n, (∏ w ∈ T, g₁ w).coeff k = (∏ w ∈ T, g₂ w).coeff k := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro g₁ g₂ _ k _; simp
    | insert x s hxs hrec =>
      intro g₁ g₂ hg k hk
      rw [Finset.prod_insert hxs, Finset.prod_insert hxs]
      have hx : ∀ m ≤ n, (g₁ x).coeff m = (g₂ x).coeff m := hg x (Finset.mem_insert_self x s)
      have hs : ∀ w ∈ s, ∀ m ≤ n, (g₁ w).coeff m = (g₂ w).coeff m :=
        fun w hw => hg w (Finset.mem_insert_of_mem hw)
      simp only [coeff_mul]
      apply Finset.sum_congr rfl
      intro ⟨i, j⟩ hij
      simp only [Finset.mem_antidiagonal] at hij
      have hi : i ≤ k := by omega
      have hj : j ≤ k := by omega
      rw [hx i (le_trans hi hk)]
      congr 1
      exact hrec g₁ g₂ hs j (le_trans hj hk)
  have h_prod_coeff_eq : ∀ (T : Finset W) (g₁ g₂ : W → PowerSeries R),
      (∀ w ∈ T, ∀ m ≤ n, (g₁ w).coeff m = (g₂ w).coeff m) →
      (∏ w ∈ T, g₁ w).coeff n = (∏ w ∈ T, g₂ w).coeff n := by
    intro T g₁ g₂ hg
    exact h_prod_coeff_eq_gen T g₁ g₂ hg n (le_refl n)
  exact h_prod_coeff_eq W_U _ _ h_factors_agree

/-!
### Fubini Rule for Infinite Products

Proposition \ref{prop.fps.prods-mulable-rules.fubini1}
-/

/-- Congruence lemma for tprod: equal families have equal products. -/
private theorem tprod_congr {S : Type*} {a b : S → PowerSeries R} (hab : a = b)
    (ha : Multipliable a) (hb : Multipliable b) :
    tprod a ha = tprod b hb := by
  subst hab
  rfl

/-- The fiber of `Prod.fst : I × J → I` at `i` is equivalent to `J`. -/
private def fiberEquiv (I J : Type*) (i : I) : {p : I × J // Prod.fst p = i} ≃ J where
  toFun := fun ⟨p, _⟩ => p.2
  invFun := fun j => ⟨(i, j), rfl⟩
  left_inv := fun ⟨⟨i', j⟩, hp⟩ => by
    simp only [Subtype.mk.injEq, Prod.mk.injEq, and_true]
    exact hp.symm
  right_inv := fun _ => rfl

/-- The tprod over a fiber of `Prod.fst` equals the tprod over `J`. -/
private lemma tprod_fiber_eq_tprod {I J : Type*} (a : I × J → PowerSeries R) (i : I)
    (ha_fiber : Multipliable (fun s : {p : I × J // Prod.fst p = i} => a s.val))
    (ha_I_i : Multipliable (fun j => a (i, j))) :
    tprod (fun s : {p : I × J // Prod.fst p = i} => a s.val) ha_fiber =
    tprod (fun j => a (i, j)) ha_I_i := by
  have h : (fun s : {p : I × J // Prod.fst p = i} => a s.val) =
           (fun j => a (i, j)) ∘ (fiberEquiv I J i) := by
    ext ⟨⟨i', j⟩, hp⟩
    simp only [Function.comp_apply, fiberEquiv] at hp ⊢
    congr 1
    ext; simp [hp]
  have hbij : Function.Bijective (fiberEquiv I J i) := (fiberEquiv I J i).bijective
  have hmult : Multipliable ((fun j => a (i, j)) ∘ (fiberEquiv I J i)) := by
    rw [← h]
    exact ha_fiber
  calc tprod (fun s : {p : I × J // Prod.fst p = i} => a s.val) ha_fiber
      = tprod ((fun j => a (i, j)) ∘ (fiberEquiv I J i)) hmult := by
        apply tprod_congr h
    _ = tprod (fun j => a (i, j)) ha_I_i := by
        exact tprod_reindex hbij ha_I_i

/-- Fubini rule: the iterated product over `I` then `J` is multipliable.
(Label: prop.fps.prods-mulable-rules.fubini1) -/
theorem multipliable_tprod_fubini {I J : Type*} {a : I × J → PowerSeries R}
    (ha : Multipliable a)
    (ha_I : ∀ i : I, Multipliable (fun j => a (i, j))) :
    Multipliable (fun i : I => tprod (fun j => a (i, j)) (ha_I i)) := by
  -- Define the projection f : I × J → I
  let f : I × J → I := Prod.fst
  -- For each i, the fiber {s : I × J // f s = i} is equivalent to J
  -- Define the bijection from fiber to J
  have he : ∀ i : I, Function.Bijective
      (fun (x : {s : I × J // f s = i}) => x.val.snd : {s : I × J // f s = i} → J) := by
    intro i
    constructor
    · intro ⟨⟨i1, j1⟩, h1⟩ ⟨⟨i2, j2⟩, h2⟩ heq
      simp only [f] at h1 h2
      subst h1 h2
      simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
      exact heq
    · intro j
      exact ⟨⟨⟨i, j⟩, rfl⟩, rfl⟩
  -- For each i, the fiber family is multipliable
  have ha_fibers : ∀ i : I, Multipliable (fun s : {s : I × J // f s = i} => a s) := by
    intro i
    let e : {s : I × J // f s = i} → J := fun x => x.val.snd
    have heq : (fun s : {s : I × J // f s = i} => a s) = (fun j => a (i, j)) ∘ e := by
      ext ⟨⟨i', j⟩, hi'⟩
      simp only [Function.comp_apply, e, f] at *
      subst hi'
      rfl
    rw [heq]
    exact multipliable_reindex (he i) (ha_I i)
  -- For each i, the tprod over fiber equals tprod over J
  have htprod_eq : ∀ i : I,
      tprod (fun s : {s : I × J // f s = i} => a s) (ha_fibers i) =
      tprod (fun j => a (i, j)) (ha_I i) := by
    intro i
    let e : {s : I × J // f s = i} → J := fun x => x.val.snd
    have heq : (fun s : {s : I × J // f s = i} => a s) = (fun j => a (i, j)) ∘ e := by
      ext ⟨⟨i', j⟩, hi'⟩
      simp only [Function.comp_apply, e, f] at *
      subst hi'
      rfl
    have h := tprod_reindex (he i) (ha_I i)
    have h2 : tprod (fun s : {s : I × J // f s = i} => a s) (ha_fibers i) =
              tprod ((fun j => a (i, j)) ∘ e) (multipliable_reindex (he i) (ha_I i)) := by
      congr 1
    rw [h2, h]
  -- Apply multipliable_prod_fibers and convert
  have h := multipliable_prod_fibers ha ha_fibers
  have hfam_eq : (fun i : I => tprod (fun j => a (i, j)) (ha_I i)) =
      (fun i : I => tprod (fun s : {s : I × J // f s = i} => a s) (ha_fibers i)) := by
    funext i
    exact (htprod_eq i).symm
  rw [hfam_eq]
  exact h

/-- Fubini rule: products over `I × J` can be computed as iterated products.
(Label: prop.fps.prods-mulable-rules.fubini1) -/
theorem tprod_fubini {I J : Type*} {a : I × J → PowerSeries R}
    (ha : Multipliable a)
    (ha_I : ∀ i : I, Multipliable (fun j => a (i, j)))
    (_ha_J : ∀ j : J, Multipliable (fun i => a (i, j)))
    (ha_outer_I : Multipliable (fun i : I => tprod (fun j => a (i, j)) (ha_I i))
      := multipliable_tprod_fubini ha ha_I) :
    tprod a ha = tprod (fun i : I => tprod (fun j => a (i, j)) (ha_I i)) ha_outer_I := by
  -- Step 1: Show that for each i, the fiber family is multipliable
  have ha_fibers : ∀ i : I, Multipliable (fun s : {p : I × J // Prod.fst p = i} => a s.val) := by
    intro i
    have h : (fun s : {p : I × J // Prod.fst p = i} => a s.val) =
             (fun j => a (i, j)) ∘ (fiberEquiv I J i) := by
      ext ⟨⟨i', j⟩, hp⟩
      simp only [Function.comp_apply, fiberEquiv] at hp ⊢
      congr 1
      ext; simp [hp]
    rw [h]
    exact multipliable_reindex (fiberEquiv I J i).bijective (ha_I i)
  -- Step 2: Apply tprod_eq_tprod_fibers with f = Prod.fst
  have h1 := tprod_eq_tprod_fibers (f := Prod.fst) ha ha_fibers
  -- Step 3: Show that the outer family of fiber tprods equals the outer family of J tprods
  have h2 : (fun i : I => tprod (fun s : {p : I × J // Prod.fst p = i} => a s.val) (ha_fibers i)) =
            (fun i : I => tprod (fun j => a (i, j)) (ha_I i)) := by
    funext i
    exact tprod_fiber_eq_tprod a i (ha_fibers i) (ha_I i)
  -- Step 4: Use congruence to conclude
  rw [h1]
  apply tprod_congr h2

/-- The fiber of `Prod.snd : I × J → J` at `j` is equivalent to `I`. -/
private def fiberEquivSnd (I J : Type*) (j : J) : {p : I × J // Prod.snd p = j} ≃ I where
  toFun := fun ⟨p, _⟩ => p.1
  invFun := fun i => ⟨(i, j), rfl⟩
  left_inv := fun ⟨⟨i, j'⟩, hp⟩ => by
    simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
    exact hp.symm
  right_inv := fun _ => rfl

/-- The tprod over a fiber of `Prod.snd` equals the tprod over `I`. -/
private lemma tprod_fiber_eq_tprod_snd {I J : Type*} (a : I × J → PowerSeries R) (j : J)
    (ha_fiber : Multipliable (fun s : {p : I × J // Prod.snd p = j} => a s.val))
    (ha_J_j : Multipliable (fun i => a (i, j))) :
    tprod (fun s : {p : I × J // Prod.snd p = j} => a s.val) ha_fiber =
    tprod (fun i => a (i, j)) ha_J_j := by
  have h : (fun s : {p : I × J // Prod.snd p = j} => a s.val) =
           (fun i => a (i, j)) ∘ (fiberEquivSnd I J j) := by
    ext ⟨⟨i, j'⟩, hp⟩
    simp only [Function.comp_apply, fiberEquivSnd]
    -- hp : j' = j, so (i, j') = (i, j)
    subst hp
    rfl
  have hbij : Function.Bijective (fiberEquivSnd I J j) := (fiberEquivSnd I J j).bijective
  have hmult : Multipliable ((fun i => a (i, j)) ∘ (fiberEquivSnd I J j)) := by
    rw [← h]
    exact ha_fiber
  calc tprod (fun s : {p : I × J // Prod.snd p = j} => a s.val) ha_fiber
      = tprod ((fun i => a (i, j)) ∘ (fiberEquivSnd I J j)) hmult := by
        apply tprod_congr h
    _ = tprod (fun i => a (i, j)) ha_J_j := by
        exact tprod_reindex hbij ha_J_j

/-- Fubini rule (J-first version): the iterated product over `J` then `I` is multipliable.
(Label: prop.fps.prods-mulable-rules.fubini1) -/
theorem multipliable_tprod_fubini_J {I J : Type*} {a : I × J → PowerSeries R}
    (ha : Multipliable a)
    (ha_J : ∀ j : J, Multipliable (fun i => a (i, j))) :
    Multipliable (fun j : J => tprod (fun i => a (i, j)) (ha_J j)) := by
  -- Define the projection f : I × J → J
  let f : I × J → J := Prod.snd
  -- For each j, the fiber {s : I × J // f s = j} is equivalent to I
  have he : ∀ j : J, Function.Bijective
      (fun (x : {s : I × J // f s = j}) => x.val.fst : {s : I × J // f s = j} → I) := by
    intro j
    constructor
    · intro ⟨⟨i1, j1⟩, h1⟩ ⟨⟨i2, j2⟩, h2⟩ heq
      simp only [f] at h1 h2
      subst h1 h2
      simp only [Subtype.mk.injEq, Prod.mk.injEq, and_true]
      exact heq
    · intro i
      exact ⟨⟨⟨i, j⟩, rfl⟩, rfl⟩
  -- For each j, the fiber family is multipliable
  have ha_fibers : ∀ j : J, Multipliable (fun s : {s : I × J // f s = j} => a s) := by
    intro j
    let e : {s : I × J // f s = j} → I := fun x => x.val.fst
    have heq : (fun s : {s : I × J // f s = j} => a s) = (fun i => a (i, j)) ∘ e := by
      ext ⟨⟨i, j'⟩, hj'⟩
      simp only [Function.comp_apply, e, f] at *
      subst hj'
      rfl
    rw [heq]
    exact multipliable_reindex (he j) (ha_J j)
  -- For each j, the tprod over fiber equals tprod over I
  have htprod_eq : ∀ j : J,
      tprod (fun s : {s : I × J // f s = j} => a s) (ha_fibers j) =
      tprod (fun i => a (i, j)) (ha_J j) := by
    intro j
    let e : {s : I × J // f s = j} → I := fun x => x.val.fst
    have heq : (fun s : {s : I × J // f s = j} => a s) = (fun i => a (i, j)) ∘ e := by
      ext ⟨⟨i, j'⟩, hj'⟩
      simp only [Function.comp_apply, e, f] at *
      subst hj'
      rfl
    have h := tprod_reindex (he j) (ha_J j)
    have h2 : tprod (fun s : {s : I × J // f s = j} => a s) (ha_fibers j) =
              tprod ((fun i => a (i, j)) ∘ e) (multipliable_reindex (he j) (ha_J j)) := by
      congr 1
    rw [h2, h]
  -- Apply multipliable_prod_fibers and convert
  have h := multipliable_prod_fibers ha ha_fibers
  have hfam_eq : (fun j : J => tprod (fun i => a (i, j)) (ha_J j)) =
      (fun j : J => tprod (fun s : {s : I × J // f s = j} => a s) (ha_fibers j)) := by
    funext j
    exact (htprod_eq j).symm
  rw [hfam_eq]
  exact h

/-- Fubini rule (J-first version): products over `I × J` can be computed as iterated products
over `J` then `I`.
(Label: prop.fps.prods-mulable-rules.fubini1) -/
theorem tprod_fubini_J {I J : Type*} {a : I × J → PowerSeries R}
    (ha : Multipliable a)
    (ha_J : ∀ j : J, Multipliable (fun i => a (i, j)))
    (ha_outer_J : Multipliable (fun j : J => tprod (fun i => a (i, j)) (ha_J j))
      := multipliable_tprod_fubini_J ha ha_J) :
    tprod a ha = tprod (fun j : J => tprod (fun i => a (i, j)) (ha_J j)) ha_outer_J := by
  -- Step 1: Show that for each j, the fiber family is multipliable
  have ha_fibers : ∀ j : J, Multipliable (fun s : {p : I × J // Prod.snd p = j} => a s.val) := by
    intro j
    have h : (fun s : {p : I × J // Prod.snd p = j} => a s.val) =
             (fun i => a (i, j)) ∘ (fiberEquivSnd I J j) := by
      ext ⟨⟨i, j'⟩, hp⟩
      simp only [Function.comp_apply, fiberEquivSnd]
      subst hp
      rfl
    rw [h]
    exact multipliable_reindex (fiberEquivSnd I J j).bijective (ha_J j)
  -- Step 2: Apply tprod_eq_tprod_fibers with f = Prod.snd
  have h1 := tprod_eq_tprod_fibers (f := Prod.snd) ha ha_fibers
  -- Step 3: Show that the outer family of fiber tprods equals the outer family of I tprods
  have h2 : (fun j : J => tprod (fun s : {p : I × J // Prod.snd p = j} => a s.val) (ha_fibers j)) =
            (fun j : J => tprod (fun i => a (i, j)) (ha_J j)) := by
    funext j
    exact tprod_fiber_eq_tprod_snd a j (ha_fibers j) (ha_J j)
  -- Step 4: Use congruence to conclude
  rw [h1]
  apply tprod_congr h2

/-- Full Fubini rule: products over `I × J` can be computed as iterated products in either order.

This combines both directions of the Fubini rule:
- `∏_{(i,j) ∈ I × J} a_{(i,j)} = ∏_{i ∈ I} ∏_{j ∈ J} a_{(i,j)}`
- `∏_{(i,j) ∈ I × J} a_{(i,j)} = ∏_{j ∈ J} ∏_{i ∈ I} a_{(i,j)}`

(Label: prop.fps.prods-mulable-rules.fubini1) -/
theorem tprod_fubini_full {I J : Type*} {a : I × J → PowerSeries R}
    (ha : Multipliable a)
    (ha_I : ∀ i : I, Multipliable (fun j => a (i, j)))
    (ha_J : ∀ j : J, Multipliable (fun i => a (i, j)))
    (ha_outer_I : Multipliable (fun i : I => tprod (fun j => a (i, j)) (ha_I i))
      := multipliable_tprod_fubini ha ha_I)
    (ha_outer_J : Multipliable (fun j : J => tprod (fun i => a (i, j)) (ha_J j))
      := multipliable_tprod_fubini_J ha ha_J) :
    tprod (fun i : I => tprod (fun j => a (i, j)) (ha_I i)) ha_outer_I =
    tprod a ha ∧
    tprod a ha =
    tprod (fun j : J => tprod (fun i => a (i, j)) (ha_J j)) ha_outer_J := by
  constructor
  · exact (tprod_fubini ha ha_I ha_J).symm
  · exact tprod_fubini_J ha ha_J

/-- Fubini rule for invertible FPS: no additional multipliability assumptions needed.
(Label: prop.fps.prods-mulable-rules.fubini) -/
theorem fubini_prod_invertible {I J : Type*} {a : I × J → PowerSeries R}
    (ha : Multipliable a)
    (ha_inv : ∀ p, IsUnit ((a p).coeff 0)) :
    (∀ i : I, Multipliable (fun j => a (i, j))) ∧
    (∀ j : J, Multipliable (fun i => a (i, j))) := by
  constructor
  · intro i
    have h : Multipliable (fun p : {p : I × J // p.1 = i} => a p) :=
      multipliable_subfamily ha ha_inv {p : I × J | p.1 = i}
    let f : J → {p : I × J // p.1 = i} := fun j => ⟨(i, j), rfl⟩
    have hf : Function.Bijective f := ⟨
      fun j1 j2 hj => congrArg (fun x => x.val.2) hj,
      fun ⟨⟨i', j⟩, hi'⟩ => ⟨j, by ext; exact hi'.symm; rfl⟩⟩
    convert multipliable_reindex hf h using 1
  · intro j
    have h : Multipliable (fun p : {p : I × J // p.2 = j} => a p) :=
      multipliable_subfamily ha ha_inv {p : I × J | p.2 = j}
    let f : I → {p : I × J // p.2 = j} := fun i => ⟨(i, j), rfl⟩
    have hf : Function.Bijective f := ⟨
      fun i1 i2 hi => congrArg (fun x => x.val.1) hi,
      fun ⟨⟨i, j'⟩, hj'⟩ => ⟨i, by ext; rfl; exact hj'.symm⟩⟩
    convert multipliable_reindex hf h using 1

/-!
### Approximator Properties

Proposition \ref{prop.fps.infprod-approx-xneq}
-/

/-- If `M` is an `x^n`-approximator, then any finite superset `J` gives the same
first `n+1` coefficients.
(Label: prop.fps.infprod-approx-xneq part (a)) -/
theorem xn_approximator_superset {a : I → PowerSeries R} {M : Finset I} {n : ℕ}
    (hM : IsXnApproximator a M n) {J : Finset I} (hMJ : M ⊆ J) (m : ℕ) (hm : m ≤ n) :
    (∏ i ∈ J, a i).coeff m = (∏ i ∈ M, a i).coeff m := by
  exact hM m hm J hMJ

/-- For a multipliable family, the infinite product's coefficients match those of any approximator.
(Label: prop.fps.infprod-approx-xneq part (b)) -/
theorem tprod_coeff_eq_approximator {a : I → PowerSeries R}
    (ha : Multipliable a) {M : Finset I} {n : ℕ}
    (hM : IsXnApproximator a M n) (m : ℕ) (hm : m ≤ n) :
    (tprod a ha).coeff m = (∏ i ∈ M, a i).coeff m :=
  tprod_coeff ha (hM m hm)

/-!
### Approximator Properties in terms of x^n-equivalence

Proposition \ref{prop.fps.infprod-approx-xneq}

These are the same results as above, but stated using the `xnEquiv` relation
(which says two FPS agree on coefficients 0 through n).

Note: The `xnEquiv` definition and basic lemmas (`xnEquiv_refl`, `xnEquiv_symm`, `xnEquiv_trans`)
are imported from `AlgebraicCombinatorics.FPS.Limits`.
-/

/-- If `M` is an `x^n`-approximator, then any finite superset `J` gives an x^n-equivalent
finite product.
(Label: prop.fps.infprod-approx-xneq part (a))

This is the x^n-equivalence form of the approximator property: for any finite
`J ⊇ M`, we have `∏_{i∈J} a_i ≡[x^n] ∏_{i∈M} a_i`. -/
theorem xn_approximator_superset_xnEquiv {a : I → PowerSeries R} {M : Finset I} {n : ℕ}
    (hM : IsXnApproximator a M n) {J : Finset I} (hMJ : M ⊆ J) :
    (∏ i ∈ J, a i) ≡[x^n] (∏ i ∈ M, a i) := fun m hm =>
  xn_approximator_superset hM hMJ m hm

/-- For a multipliable family, the infinite product is x^n-equivalent to the product
over any x^n-approximator.
(Label: prop.fps.infprod-approx-xneq part (b))

This is the x^n-equivalence form: if `M` is an x^n-approximator for a multipliable
family `(a_i)_{i∈I}`, then `∏_{i∈I} a_i ≡[x^n] ∏_{i∈M} a_i`. -/
theorem tprod_xnEquiv_approximator {a : I → PowerSeries R}
    (ha : Multipliable a) {M : Finset I} {n : ℕ}
    (hM : IsXnApproximator a M n) :
    (tprod a ha) ≡[x^n] (∏ i ∈ M, a i) := fun m hm =>
  tprod_coeff_eq_approximator ha hM m hm

/-!
### Limits of initial partial products

The converse to `coeffStabilizesTo_partial_prod` uses the general notion
`PowerSeries.Multipliable`.  In particular, no normalization of the constant
coefficients is needed: a finite initial segment (or, for example, a zero
factor) may absorb later factors without those factors themselves being
congruent to `1`.
-/

/-- If all sufficiently long initial partial products are `x^n`-equivalent,
then the corresponding initial segment determines the `x^n`-coefficient in
the product over every finite superset. -/
private lemma determinesCoeffInProd_range_of_partial_prod_xnEquiv
    {f : ℕ → PowerSeries R} {lim : PowerSeries R} {n N : ℕ}
    (hN : ∀ i ≥ N, (∏ j ∈ Finset.range (i + 1), f j) ≡[x^n] lim) :
    DeterminesCoeffInProd f (Finset.range (N + 1)) n := by
  intro J hMJ
  have hbase : (∏ i ∈ Finset.range (N + 1), f i) ≡[x^n] lim := hN N (by omega)
  have hfactor : ∀ j, N < j →
      (∏ i ∈ Finset.range (N + 1), f i) * f j ≡[x^n]
        (∏ i ∈ Finset.range (N + 1), f i) := by
    intro j hj
    have hj_pos : 0 < j := by omega
    have hprev : (∏ i ∈ Finset.range j, f i) ≡[x^n] lim := by
      simpa [Nat.sub_add_cancel hj_pos] using hN (j - 1) (by omega)
    have hnext : (∏ i ∈ Finset.range (j + 1), f i) ≡[x^n] lim := hN j (by omega)
    have hstep :
        (∏ i ∈ Finset.range j, f i) * f j ≡[x^n] lim * f j :=
      hprev.mul (XnEquiv.refl n (f j))
    rw [← Finset.prod_range_succ] at hstep
    have hlim_mul : lim * f j ≡[x^n] lim := hstep.symm.trans hnext
    exact (hbase.mul (XnEquiv.refl n (f j))).trans (hlim_mul.trans hbase.symm)
  let S := J \ Finset.range (N + 1)
  have hS : ∀ j ∈ S, N < j := by
    intro j hj
    simp only [S, Finset.mem_sdiff, Finset.mem_range] at hj
    omega
  have hextra_aux : ∀ T : Finset ℕ, T ⊆ S →
      (∏ i ∈ Finset.range (N + 1), f i) * (∏ j ∈ T, f j) ≡[x^n]
        (∏ i ∈ Finset.range (N + 1), f i) := by
    classical
    intro T hTS
    induction T using Finset.induction_on with
    | empty => simp
    | @insert j T hjT ih =>
        rw [Finset.prod_insert hjT]
        have hreorder :
            (∏ i ∈ Finset.range (N + 1), f i) * (f j * ∏ x ∈ T, f x) =
              ((∏ i ∈ Finset.range (N + 1), f i) * ∏ x ∈ T, f x) * f j := by
          ring
        rw [hreorder]
        exact (ih (fun x hx => hTS (by simp [hx]))).mul (XnEquiv.refl n (f j)) |>.trans
          (hfactor j (hS j (hTS (by simp))))
  have hextra :
      (∏ i ∈ Finset.range (N + 1), f i) * (∏ j ∈ S, f j) ≡[x^n]
        (∏ i ∈ Finset.range (N + 1), f i) :=
    hextra_aux S (fun _ h => h)
  have hdecomp : J = Finset.range (N + 1) ∪ S := by
    ext j
    simp only [S, Finset.mem_union, Finset.mem_range, Finset.mem_sdiff]
    constructor
    · intro hj
      by_cases hjN : j < N + 1
      · exact Or.inl hjN
      · exact Or.inr ⟨hj, hjN⟩
    · rintro (hj | ⟨hj, _⟩)
      · exact hMJ (Finset.mem_range.mpr hj)
      · exact hj
  rw [hdecomp, Finset.prod_union]
  · exact hextra n (le_refl n)
  · apply Finset.disjoint_left.mpr
    intro j hjRange hjS
    exact (Finset.mem_sdiff.mp hjS).2 hjRange

/-- If the sequence of initial partial products converges coefficientwise,
then the family is multipliable in the source's finitely-determined sense.
(Theorem 7.5.13, label: `thm.fps.lim.prod-lim-conv`) -/
theorem multipliable_of_coeffStabilizesTo_partial_prod
    {f : ℕ → PowerSeries R} {lim : PowerSeries R}
    (h : CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) lim) :
    Multipliable f := by
  intro n
  obtain ⟨N, hN⟩ := exists_xnEquiv_of_coeffStabilizesTo h n
  exact ⟨Finset.range (N + 1),
    determinesCoeffInProd_range_of_partial_prod_xnEquiv hN⟩

/-- If the sequence of initial partial products converges coefficientwise,
its limit is the general infinite product.  No condition on the factors'
constant coefficients is required.
(Theorem 7.5.13, label: `thm.fps.lim.prod-lim-conv`) -/
theorem tprod_eq_of_coeffStabilizesTo_partial_prod
    {f : ℕ → PowerSeries R} {lim : PowerSeries R}
    (h : CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) lim) :
    tprod f (multipliable_of_coeffStabilizesTo_partial_prod h) = lim := by
  ext n
  obtain ⟨N, hN⟩ := exists_xnEquiv_of_coeffStabilizesTo h n
  rw [tprod_coeff (multipliable_of_coeffStabilizesTo_partial_prod h)
    (determinesCoeffInProd_range_of_partial_prod_xnEquiv hN)]
  exact hN N (by omega) n (le_refl n)

end PowerSeries
