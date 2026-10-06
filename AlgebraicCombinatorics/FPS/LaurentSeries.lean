/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
import AlgebraicCombinatorics.LaurentSeries

/-!
# Laurent Power Series

This file formalizes properties of Laurent polynomials and Laurent power series,
following Section `\ref{sec.details.gf.laure}` of the source material.

## Overview

Laurent polynomials are formal sums `∑_{i ∈ ℤ} aᵢ xⁱ` where only finitely many coefficients
are nonzero. Laurent power series are formal sums where the sequence of negative-indexed
coefficients is essentially finite (i.e., only finitely many negative powers appear).

In Mathlib:
- Laurent polynomials are `LaurentPolynomial R` (notation `R[T;T⁻¹]`), implemented as
  `AddMonoidAlgebra R ℤ`
- Laurent series are `LaurentSeries R` (notation `R⸨X⸩`), implemented as `HahnSeries ℤ R`

## Main Results

### Laurent Polynomials (Theorem thm.fps.laure.laupol-ring)
- `LaurentPolynomial` forms a commutative `K`-algebra with `x` invertible
- Multiplication by `x` shifts coefficients: `x · a = (aₙ₋₁)_{n∈ℤ}` (Lemma lem.fps.laure.xa)
- For each `k ∈ ℤ`, we have `xᵏ = (δᵢ,ₖ)_{i∈ℤ}` (Proposition prop.fps.laure.xk)
- Every Laurent polynomial can be written as `∑ aᵢ xⁱ` (`eq_sum_T`)

### Laurent Series (Theorem thm.fps.laure.lauser-ring)
- `LaurentSeries` forms a commutative `K`-algebra with `x` invertible
- The product of two Laurent series is again a Laurent series (closure under multiplication)
- Every Laurent series can be written as `∑_{i∈ℤ} aᵢ xⁱ` (Proposition prop.fps.laure.a=sumaixi)

## References

- Source: `AlgebraicCombinatorics/tex/Details/LaurentSeries.tex`
- Labels: `thm.fps.laure.laupol-ring`, `lem.fps.laure.xa`, `prop.fps.laure.xk`,
  `prop.fps.laure.a=sumaixi`, `thm.fps.laure.lauser-ring`
-/

open scoped LaurentPolynomial Polynomial
open LaurentPolynomial HahnSeries

noncomputable section

namespace AlgebraicCombinatorics.FPS.Laurent

/-!
## Section: Laurent Polynomials

A Laurent polynomial over a commutative ring `K` is a formal sum `∑_{i ∈ ℤ} aᵢ xⁱ`
where only finitely many coefficients `aᵢ` are nonzero.

In Mathlib, `LaurentPolynomial R` is defined as `AddMonoidAlgebra R ℤ`, i.e., finitely
supported functions `ℤ →₀ R`. The variable is denoted `T` to distinguish from polynomials.
-/

/-!
## Definition: Laurent Polynomials (def.fps.laure.laupol)

This section formalizes Definition \ref{def.fps.laure.laupol} from the source material.

A Laurent polynomial over K is an essentially finite family (aₙ)_{n∈ℤ}, i.e., a function
ℤ → K with finite support. The set K[x^±] of all Laurent polynomials forms a K-submodule
of the doubly infinite power series K[[x^±]].

Multiplication is defined by convolution:
  (a · b)_n = ∑_{i∈ℤ} aᵢ · b_{n-i}

The indeterminate x is defined as x = (δ_{i,1})_{i∈ℤ}, i.e., the sequence with 1 at
position 1 and 0 elsewhere.

In Mathlib, Laurent polynomials are represented as `LaurentPolynomial K = AddMonoidAlgebra K ℤ`,
whose coefficient function `p.coeff : ℤ →₀ K` is finitely supported. This matches the
definition of essentially finite families.
-/

section LaurentPolynomialDefinition

variable {K : Type*} [CommRing K]

/-- **Definition of Laurent polynomials** (Definition def.fps.laure.laupol)

A Laurent polynomial over K is an essentially finite family (aₙ)_{n∈ℤ}, represented
in Mathlib as `LaurentPolynomial K = AddMonoidAlgebra K ℤ`, with coefficients `p.coeff : ℤ →₀ K`.

This definition captures the key property: only finitely many coefficients are nonzero. -/
abbrev LaurentPoly (K : Type*) [CommRing K] := K[T;T⁻¹]

/-- Laurent polynomials are essentially finite families: they have finite support. -/
theorem laurentPoly_finite_support (p : LaurentPoly K) : (p.coeff.support : Set ℤ).Finite :=
  p.coeff.support.finite_toSet

/-- The coefficient function of a Laurent polynomial. -/
def laurentPoly_coeff (p : LaurentPoly K) (n : ℤ) : K := p.coeff n

/-- **Multiplication of Laurent polynomials is convolution**.
(Part of Definition def.fps.laure.laupol)

The product (a · b)_n = ∑_{i∈ℤ} aᵢ · b_{n-i}.

In Mathlib, this is the standard multiplication on `AddMonoidAlgebra K ℤ`. -/
theorem laurentPoly_mul_coeff (a b : LaurentPoly K) (n : ℤ) :
    (a * b).coeff n = ∑ i ∈ a.coeff.support, a.coeff i * b.coeff (n - i) := by
  classical
  simp only [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro i _
  have key : ∀ x, (if i + x = n then a.coeff i * b.coeff x else 0) =
             (if x = n - i then a.coeff i * b.coeff x else 0) := fun x => by
    by_cases h : i + x = n
    · have hx : x = n - i := by linarith
      simp [hx]
    · have hx : ¬(x = n - i) := fun hx => h (by linarith)
      simp [h, hx]
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  by_cases h : n - i ∈ b.coeff.support
  · simp [h]
  · simp only [Finsupp.mem_support_iff, not_not] at h
    simp [h]

/-- **The indeterminate x in Laurent polynomials**.
(Part of Definition def.fps.laure.laupol)

The element x = (δ_{i,1})_{i∈ℤ} is the sequence with 1 at position 1 and 0 elsewhere.
In Mathlib notation, this is `T 1`. -/
def laurentPoly_X : LaurentPoly K := T 1

/-- The indeterminate x has coefficient 1 at position 1 and 0 elsewhere. -/
@[simp]
theorem laurentPoly_X_coeff (n : ℤ) :
    (laurentPoly_X (K := K)).coeff n = if n = 1 then 1 else 0 := by
  simp only [laurentPoly_X]
  rw [T_apply]
  by_cases h : n = 1
  · simp [h]
  · simp [h, Ne.symm h]

/-- **The unity element in Laurent polynomials**.
(Part of Theorem thm.fps.laure.laupol-ring)

The unity is 1 = (δ_{i,0})_{i∈ℤ}, i.e., the sequence with 1 at position 0 and 0 elsewhere. -/
@[simp]
theorem laurentPoly_one_coeff (n : ℤ) :
    (1 : LaurentPoly K).coeff n = if n = 0 then 1 else 0 := by
  show (T 0 : K[T;T⁻¹]).coeff n = _
  rw [T_apply]
  by_cases h : n = 0
  · simp [h]
  · simp [h, Ne.symm h]

/-- The unity element equals T(0). -/
theorem laurentPoly_one_eq_T_zero : (1 : LaurentPoly K) = T 0 := rfl

/-- **Laurent polynomials form a K-module**.
(Part of Definition def.fps.laure.laupol)

The set K[x^±] is a K-submodule of K[[x^±]]. In Mathlib, this is captured by the
Module instance on LaurentPolynomial. -/
def laurentPoly_module : Module K (LaurentPoly K) := inferInstance

/-- Scalar multiplication on Laurent polynomials acts coefficientwise.
(Part of Definition def.fps.laure.laupol) -/
theorem laurentPoly_smul_coeff (c : K) (p : LaurentPoly K) (n : ℤ) :
    (c • p).coeff n = c * p.coeff n := rfl

/-- Addition on Laurent polynomials is coefficientwise.
(Part of Definition def.fps.laure.laupol) -/
theorem laurentPoly_add_coeff (p q : LaurentPoly K) (n : ℤ) :
    (p + q).coeff n = p.coeff n + q.coeff n :=
  Finsupp.add_apply p.coeff q.coeff n

/-- The zero Laurent polynomial has all coefficients zero. -/
theorem laurentPoly_zero_coeff (n : ℤ) : (0 : LaurentPoly K).coeff n = 0 :=
  Finsupp.zero_apply

/-- **The support of a Laurent polynomial is finite**.
(Key property from Definition def.fps.laure.laupol)

This is the essential finiteness condition: only finitely many coefficients are nonzero. -/
theorem laurentPoly_support_finite (p : LaurentPoly K) :
    {n : ℤ | p.coeff n ≠ 0}.Finite := by
  convert p.coeff.support.finite_toSet
  ext n
  simp [Finsupp.mem_support_iff]

/-- The support of a Laurent polynomial is exactly the support of its coefficient `Finsupp`. -/
theorem laurentPoly_support_eq (p : LaurentPoly K) :
    {n : ℤ | p.coeff n ≠ 0} = ↑p.coeff.support := by
  ext n
  simp [Finsupp.mem_support_iff]

/-- **Construction of Laurent polynomials from finite data**.

Any finitely supported function ℤ → K gives a Laurent polynomial. -/
def laurentPoly_ofFinsupp (f : ℤ →₀ K) : LaurentPoly K := AddMonoidAlgebra.ofCoeff f

/-- The coefficients of a Laurent polynomial constructed from a finsupp are the same. -/
theorem laurentPoly_ofFinsupp_coeff (f : ℤ →₀ K) (n : ℤ) :
    (laurentPoly_ofFinsupp f).coeff n = f n := rfl

/-- **Single term Laurent polynomial**.

The Laurent polynomial with a single term `a · x^k` is represented as `Finsupp.single k a`. -/
def laurentPoly_single (k : ℤ) (a : K) : LaurentPoly K := AddMonoidAlgebra.single k a

/-- The coefficient of a single-term Laurent polynomial. -/
theorem laurentPoly_single_coeff (k : ℤ) (a : K) (n : ℤ) :
    (laurentPoly_single k a).coeff n = if n = k then a else 0 := by
  simp only [laurentPoly_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h1 h2
  · rfl
  · omega
  · omega
  · rfl

/-- A single-term Laurent polynomial equals C(a) * T(k). -/
theorem laurentPoly_single_eq_C_mul_T (k : ℤ) (a : K) :
    laurentPoly_single k a = C a * T k := by
  simp only [laurentPoly_single, single_eq_C_mul_T]

/-- **Laurent polynomials are the essentially finite families**.

This theorem explicitly states that Laurent polynomials (via `p.coeff : ℤ →₀ K`) are exactly
the essentially finite families (aₙ)_{n∈ℤ}, formalizing Definition def.fps.laure.laupol. -/
theorem laurentPoly_iff_essentiallyFinite (f : ℤ → K) :
    (∃ p : LaurentPoly K, ∀ n, p.coeff n = f n) ↔ {n : ℤ | f n ≠ 0}.Finite := by
  constructor
  · intro ⟨p, hp⟩
    have h := laurentPoly_support_finite p
    have heq : {n : ℤ | f n ≠ 0} = {n : ℤ | p.coeff n ≠ 0} := by
      ext n
      simp only [Set.mem_ofPred_eq]
      rw [hp n]
    rw [heq]
    exact h
  · intro hf
    refine ⟨AddMonoidAlgebra.ofCoeff ⟨hf.toFinset, fun n => f n, ?_⟩, fun n => rfl⟩
    intro n
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ne_eq]

end LaurentPolynomialDefinition

section LaurentPolynomialBasics

variable {K : Type*} [CommRing K]

/-- **Laurent polynomials form a commutative K-algebra**.
(Theorem thm.fps.laure.laupol-ring, label: thm.fps.laure.laupol-ring)

This is the key structural result: `K[T;T⁻¹]` is a commutative ring with `T` invertible. -/
def laurentPolynomial_commRing : CommRing K[T;T⁻¹] := inferInstance

def laurentPolynomial_algebra : Algebra K K[T;T⁻¹] := inferInstance

/-- The variable `T` in Laurent polynomials is a unit (invertible).
(Part of Theorem thm.fps.laure.laupol-ring) -/
theorem T_isUnit : IsUnit (T 1 : K[T;T⁻¹]) := by
  refine ⟨⟨T 1, T (-1), ?_, ?_⟩, rfl⟩
  · have h := T_add (R := K) 1 (-1)
    simp only [add_neg_cancel] at h
    exact h.symm
  · have h := T_add (R := K) (-1) 1
    simp only [neg_add_cancel] at h
    exact h.symm

/-- The inverse of `T` is `T⁻¹ = T(-1)`.
(Part of Theorem thm.fps.laure.laupol-ring) -/
theorem T_inv : (T 1 : K[T;T⁻¹]) * T (-1) = 1 := by
  have h := T_add (R := K) 1 (-1)
  simp only [add_neg_cancel] at h
  exact h.symm

/-- `T(-1) * T = 1`.
(Part of Theorem thm.fps.laure.laupol-ring) -/
theorem T_neg_one_mul_T : (T (-1) : K[T;T⁻¹]) * T 1 = 1 := by
  have h := T_add (R := K) (-1) 1
  simp only [neg_add_cancel] at h
  exact h.symm

end LaurentPolynomialBasics

/-!
## Section: Multiplication by T shifts coefficients

This section proves the analogue of Lemma `lem.fps.xa` for Laurent polynomials:
multiplication by `T` shifts coefficients by 1.
-/

section ShiftByT

variable {K : Type*} [CommRing K]

/-- **Multiplication by T shifts coefficients down by 1**.
(Lemma lem.fps.laure.xa, label: lem.fps.laure.xa)

If `a = (aₙ)_{n∈ℤ}` is a Laurent polynomial, then `T · a = (aₙ₋₁)_{n∈ℤ}`.
In other words, the coefficient at position `n` in `T * a` equals the coefficient
at position `n - 1` in `a`. -/
theorem T_mul_coeff (a : K[T;T⁻¹]) (n : ℤ) :
    (T 1 * a : K[T;T⁻¹]).coeff n = a.coeff (n - 1) := by
  simp only [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  ring_nf

/-- **Multiplication by T⁻¹ shifts coefficients up by 1**.
(Lemma lem.fps.laure.xa, label: lem.fps.laure.xa)

If `a = (aₙ)_{n∈ℤ}` is a Laurent polynomial, then `T⁻¹ · a = (aₙ₊₁)_{n∈ℤ}`.
In other words, the coefficient at position `n` in `T(-1) * a` equals the coefficient
at position `n + 1` in `a`. -/
theorem T_neg_one_mul_coeff (a : K[T;T⁻¹]) (n : ℤ) :
    (T (-1) * a : K[T;T⁻¹]).coeff n = a.coeff (n + 1) := by
  simp only [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  ring_nf

/-- Multiplication on the right by T also shifts coefficients. -/
theorem mul_T_coeff (a : K[T;T⁻¹]) (n : ℤ) :
    (a * T 1 : K[T;T⁻¹]).coeff n = a.coeff (n - 1) := by
  rw [mul_comm, T_mul_coeff]

/-- Multiplication on the right by T⁻¹ also shifts coefficients. -/
theorem mul_T_neg_one_coeff (a : K[T;T⁻¹]) (n : ℤ) :
    (a * T (-1) : K[T;T⁻¹]).coeff n = a.coeff (n + 1) := by
  rw [mul_comm, T_neg_one_mul_coeff]

end ShiftByT

/-!
## Section: Powers of T

This section proves that `Tᵏ = (δᵢ,ₖ)_{i∈ℤ}` for all `k ∈ ℤ`, the analogue of
Proposition `prop.fps.xk` for Laurent polynomials.
-/

section PowersOfT

variable {K : Type*} [CommRing K]

/-- **The k-th power of T is the unit sequence at k**.
(Proposition prop.fps.laure.xk, label: prop.fps.laure.xk)

For each `k ∈ ℤ`, the Laurent polynomial `T(k)` has coefficient 1 at position k
and 0 everywhere else. -/
theorem T_coeff_eq (k : ℤ) (i : ℤ) :
    (T k : K[T;T⁻¹]).coeff i = if i = k then 1 else 0 := by
  rw [T_apply]
  by_cases h : k = i
  · simp [h]
  · simp [h, Ne.symm h]

/-- `T(k)` is the Kronecker delta at k, restated. -/
theorem T_eq_single (k : ℤ) : (T k : K[T;T⁻¹]) = AddMonoidAlgebra.single k 1 := rfl

/-- The product `T(m) * T(n) = T(m + n)` follows from the group structure. -/
theorem T_mul_T (m n : ℤ) : (T m : K[T;T⁻¹]) * T n = T (m + n) :=
  (T_add m n).symm

/-- For natural number powers, `(T 1)^n = T n`.
(Part of Proposition prop.fps.laure.xk) -/
theorem T_one_pow (n : ℕ) : (T 1 : K[T;T⁻¹]) ^ n = T n := by
  rw [T_pow]
  simp

/-- Helper lemma: the unit associated to `T 1` has inverse `T (-1)`. -/
private lemma isUnit_T_one_unit_eq :
    (isUnit_T (R := K) 1).unit =
    ⟨T 1, T (-1), by rw [← T_add]; simp, by rw [← T_add]; simp⟩ := by
  ext
  simp [IsUnit.unit_spec]

/-- **The k-th power of x equals T(k) for all integers k**.
(Proposition prop.fps.laure.xk, label: prop.fps.laure.xk)

This is the key result showing that `x^k = (δᵢ,ₖ)_{i∈ℤ}` for all `k ∈ ℤ`.
Since `T 1` represents `x` and `T k` represents the Kronecker delta at k,
this theorem shows that integer powers of x give the expected sequences.

For natural number powers, this follows from `T_pow`. For negative powers,
we use the fact that `T 1` is a unit with inverse `T (-1)`. -/
theorem T_one_zpow (k : ℤ) : (↑((isUnit_T (R := K) 1).unit ^ k) : K[T;T⁻¹]) = T k := by
  induction k using Int.induction_on with
  | zero =>
    simp only [zpow_zero, Units.val_one]
    rfl
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ih, IsUnit.unit_spec, ← T_add]
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ih]
    have hinv : ((isUnit_T (R := K) 1).unit⁻¹ : K[T;T⁻¹]ˣ).val = T (-1) := by
      rw [isUnit_T_one_unit_eq]
      simp
    rw [hinv, ← T_add]
    norm_cast

/-- Corollary: The coefficient of `x^k` at position `i` is `δᵢ,ₖ`.
(Proposition prop.fps.laure.xk, restated in terms of coefficients) -/
theorem T_one_zpow_coeff (k i : ℤ) :
    ((isUnit_T (R := K) 1).unit ^ k : K[T;T⁻¹]ˣ).val.coeff i = if i = k then 1 else 0 := by
  rw [T_one_zpow, T_coeff_eq]

end PowersOfT

/-!
## Section: Representation as sums

Every Laurent polynomial can be written as a finite sum `∑ aᵢ Tⁱ`.
-/

section Representation

variable {K : Type*} [CommRing K]

/-- **Every Laurent polynomial is a sum of monomials**.

Any Laurent polynomial `a` can be written as `∑_{i ∈ support(a)} aᵢ · Tⁱ`. -/
theorem eq_sum_T (a : K[T;T⁻¹]) :
    a = a.coeff.support.sum fun i => C (a.coeff i) * T i := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single a]
  apply Finset.sum_congr rfl
  intro i _
  exact single_eq_C_mul_T (a.coeff i) i

/-- Alternative form: every Laurent polynomial is a sum over its support. -/
theorem eq_sum_single (a : K[T;T⁻¹]) :
    a = a.coeff.support.sum fun i => AddMonoidAlgebra.single i (a.coeff i) :=
  (AddMonoidAlgebra.sum_coeff_single a).symm

end Representation

/-!
## Section: Laurent Series

Laurent series are formal power series with finitely many negative exponents.
In Mathlib, they are implemented as `HahnSeries ℤ R`, which are functions `ℤ → R`
with well-founded support.

The key result (Theorem thm.fps.laure.lauser-ring) is that Laurent series form
a commutative K-algebra, and in particular that the product of two Laurent series
is again a Laurent series.
-/

section LaurentSeriesBasics

variable {K : Type*} [CommRing K]

/-- **Laurent series form a commutative K-algebra**.
(Theorem thm.fps.laure.lauser-ring, label: thm.fps.laure.lauser-ring)

This is the key structural result for Laurent series. -/
def laurentSeries_commRing : CommRing (LaurentSeries K) := inferInstance

def laurentSeries_algebra : Algebra K (LaurentSeries K) := inferInstance

/-- The variable `X` in Laurent series (as single 1 1) is a unit. -/
theorem LaurentSeries_X_isUnit : IsUnit (HahnSeries.single (1 : ℤ) (1 : K)) := by
  refine ⟨⟨single 1 1, single (-1) 1, ?_, ?_⟩, rfl⟩
  all_goals simp only [single_mul_single, add_neg_cancel, neg_add_cancel, mul_one]; rfl

/-- A summable family of single Hahn series indexed by the support of a given Laurent series.
This is used to express a Laurent series as an infinite sum of monomials. -/
def singleFamily (x : LaurentSeries K) : SummableFamily ℤ K x.support where
  toFun := fun ⟨g, _⟩ => single g (x.coeff g)
  isPWO_iUnion_support' := by
    refine x.isPWO_support.mono ?_
    intro g hg
    simp only [Set.mem_iUnion] at hg
    obtain ⟨⟨g', hg'⟩, hg''⟩ := hg
    simp only [mem_support] at hg''
    by_cases h : x.coeff g' = 0
    · simp [h] at hg''
    · have hsingle : (single g' (x.coeff g')).coeff g ≠ 0 := hg''
      rw [coeff_single] at hsingle
      split_ifs at hsingle with heq
      · subst heq
        exact hg'
      · contradiction
  finite_co_support' := fun g => by
    by_cases hg : x.coeff g = 0
    · convert Set.finite_empty
      ext ⟨g', _⟩
      simp only [Set.mem_ofPred_eq, coeff_single, Set.mem_empty_iff_false, iff_false]
      intro h
      split_ifs at h with heq
      · subst heq
        exact h hg
      · exact h rfl
    · have hg_supp : g ∈ x.support := by simpa [mem_support] using hg
      refine Set.Finite.subset (Set.finite_singleton ⟨g, hg_supp⟩) ?_
      intro ⟨g', hg'⟩ h
      simp only [Set.mem_ofPred_eq, coeff_single, ne_eq] at h
      simp only [Set.mem_singleton_iff, Subtype.mk.injEq]
      split_ifs at h with heq
      · exact heq.symm
      · contradiction

/-- **Every Laurent series is a sum of monomials**.
(Proposition prop.fps.laure.a=sumaixi, label: prop.fps.laure.a=sumaixi)

Any Laurent series `a` can be written as `∑_{i ∈ ℤ} aᵢ · xⁱ` where the sum
is taken over the support of `a`. This is the infinite sum version of `eq_sum_T`
for Laurent polynomials.

In Mathlib notation, we express this using `SummableFamily.hsum`, which represents
a formal infinite sum of Hahn series. -/
theorem laurentSeries_eq_hsum_single (x : LaurentSeries K) :
    x = (singleFamily x).hsum := by
  ext n
  simp only [SummableFamily.coeff_hsum]
  by_cases hn : x.coeff n = 0
  · -- If x.coeff n = 0, then the finsum is also 0
    rw [hn]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro ⟨g, hg⟩
    simp only [singleFamily, SummableFamily.coe_mk, coeff_single]
    split_ifs with heq
    · subst heq
      exact hn
    · rfl
  · -- If x.coeff n ≠ 0, then n is in the support
    have hn_supp : n ∈ x.support := by simpa [mem_support] using hn
    rw [finsum_eq_single (fun i => (singleFamily x i).coeff n) ⟨n, hn_supp⟩]
    · simp [singleFamily]
    · intro ⟨g, hg⟩ hne
      simp only [singleFamily, SummableFamily.coe_mk, coeff_single]
      simp only [ne_eq, Subtype.mk.injEq] at hne
      split_ifs with heq
      · exact (hne heq.symm).elim
      · rfl

/-- The coefficient version of `laurentSeries_eq_hsum_single`:
the n-th coefficient of a Laurent series equals the finsum of the n-th coefficients
of the single monomials. -/
theorem laurentSeries_coeff_eq_finsum_single (x : LaurentSeries K) (n : ℤ) :
    x.coeff n = ∑ᶠ (i : x.support), (single (i : ℤ) (x.coeff i)).coeff n := by
  conv_lhs => rw [laurentSeries_eq_hsum_single x]
  rfl

end LaurentSeriesBasics

/-!
## Section: Closure of Laurent Series under Multiplication

The main technical content of Theorem thm.fps.laure.lauser-ring is showing that
the product of two Laurent series is again a Laurent series. This requires showing
that if `(a_{-1}, a_{-2}, ...)` and `(b_{-1}, b_{-2}, ...)` are essentially finite,
then so is the corresponding sequence for the product.
-/

section MultiplicationClosure

variable {K : Type*} [CommRing K]

/-- The order of a nonzero Laurent series is the smallest index with nonzero coefficient. -/
def laurentOrder (f : LaurentSeries K) : ℤ := f.order

/-- If `f` and `g` are nonzero Laurent series with orders `p` and `q` respectively,
then `f * g` has order at least `p + q`.

This is the key lemma showing closure under multiplication.
(Part of proof of Theorem thm.fps.laure.lauser-ring) -/
theorem order_mul_ge (f g : LaurentSeries K) :
    f.orderTop + g.orderTop ≤ (f * g).orderTop :=
  HahnSeries.orderTop_add_le_mul

/-- The product of two Laurent series has coefficients zero below the sum of their orders.

This formalizes the key step in the proof: if `aᵢ = 0` for `i < p` and `bⱼ = 0` for `j < q`,
then `cₙ = 0` for `n < p + q`.
(Part of proof of Theorem thm.fps.laure.lauser-ring) -/
theorem coeff_mul_eq_zero_of_lt_order (f g : LaurentSeries K) (n : ℤ)
    (hn : n < f.order + g.order) (hf : f ≠ 0) (hg : g ≠ 0) : (f * g).coeff n = 0 := by
  by_cases hfg : f * g = 0
  · simp [hfg]
  · apply HahnSeries.coeff_eq_zero_of_lt_order
    have h := HahnSeries.orderTop_add_le_mul (x := f) (y := g)
    rw [HahnSeries.orderTop_of_ne_zero hf, HahnSeries.orderTop_of_ne_zero hg,
        HahnSeries.orderTop_of_ne_zero hfg] at h
    norm_cast at h
    rw [HahnSeries.order_of_ne hf, HahnSeries.order_of_ne hg] at hn
    rw [HahnSeries.order_of_ne hfg]
    exact lt_of_lt_of_le hn h

end MultiplicationClosure

/-!
## Section: Embedding of Power Series into Laurent Series

Power series embed into Laurent series via the natural map that sends
`∑_{n≥0} aₙ xⁿ` to the same series viewed as a Laurent series with
zero coefficients for negative indices.
-/

section PowerSeriesEmbedding

variable {K : Type*} [CommRing K]

/-- Power series embed into Laurent series.
(Implicit in the source material) -/
def powerSeriesToLaurent : PowerSeries K →+* LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K

/-- The embedding preserves the ring structure. -/
theorem powerSeriesToLaurent_injective : Function.Injective (powerSeriesToLaurent (K := K)) :=
  HahnSeries.ofPowerSeries_injective

/-- Coefficients are preserved for non-negative indices. -/
theorem coeff_powerSeriesToLaurent (f : PowerSeries K) (n : ℕ) :
    (powerSeriesToLaurent f).coeff n = PowerSeries.coeff n f :=
  LaurentSeries.coeff_coe_powerSeries f n

end PowerSeriesEmbedding

/-!
## Section: Embedding of Laurent Polynomials into Laurent Series

Laurent polynomials embed into Laurent series.
-/

section LaurentPolynomialEmbedding

variable {K : Type*} [CommRing K]

/-- A Laurent polynomial can be viewed as a Laurent series.

This is the inclusion `K[T;T⁻¹] → K⸨X⸩`. -/
def laurentPolynomialToSeries (p : K[T;T⁻¹]) : LaurentSeries K where
  coeff := p.coeff
  isPWO_support' := by
    apply Set.Finite.isPWO
    exact Finsupp.hasFiniteSupport p.coeff

/-- The embedding is additive. -/
theorem laurentPolynomialToSeries_add (p q : K[T;T⁻¹]) :
    laurentPolynomialToSeries (p + q) =
    laurentPolynomialToSeries p + laurentPolynomialToSeries q := by
  ext n
  simp only [laurentPolynomialToSeries, HahnSeries.coeff_add', Pi.add_apply]
  rfl

/-- The embedding sends 0 to 0. -/
theorem laurentPolynomialToSeries_zero :
    laurentPolynomialToSeries (0 : K[T;T⁻¹]) = 0 := by
  ext n
  simp only [laurentPolynomialToSeries, HahnSeries.coeff_zero]
  rfl

/-- The embedding sends 1 to 1. -/
theorem laurentPolynomialToSeries_one :
    laurentPolynomialToSeries (1 : K[T;T⁻¹]) = 1 := by
  ext n
  rw [HahnSeries.coeff_one]
  show (1 : K[T;T⁻¹]).coeff n = _
  rw [laurentPoly_one_coeff]
  congr

set_option backward.isDefEq.respectTransparency false in
/-- The embedding is multiplicative. -/
theorem laurentPolynomialToSeries_mul (p q : K[T;T⁻¹]) :
    laurentPolynomialToSeries (p * q) =
    laurentPolynomialToSeries p * laurentPolynomialToSeries q := by
  ext n
  simp only [laurentPolynomialToSeries]
  rw [HahnSeries.coeff_mul]
  -- The HahnSeries antidiagonal equals the filtered product of supports
  have hs_eq : Finset.antidiagonal
      (laurentPolynomialToSeries p).isPWO_support
      (laurentPolynomialToSeries q).isPWO_support n =
      (p.coeff.support ×ˢ q.coeff.support).filter (fun ij => ij.1 + ij.2 = n) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_antidiagonal, Finsupp.mem_support_iff,
               Finset.mem_filter, Finset.mem_product, laurentPolynomialToSeries]
    tauto
  rw [hs_eq]
  classical
  simp only [AddMonoidAlgebra.coeff_mul, Finsupp.sum, Finset.sum_filter, Finset.sum_product]

/-- The embedding preserves coefficients. -/
theorem laurentPolynomialToSeries_coeff (p : K[T;T⁻¹]) (n : ℤ) :
    (laurentPolynomialToSeries p).coeff n = p.coeff n := rfl

end LaurentPolynomialEmbedding

/-!
## Section: Binary Representation Uniqueness

This section proves that every natural number has a unique binary representation,
which is Theorem `thm.fps.laure.binary-rep-uniq` in the source material.

A binary representation of `n ∈ ℕ` is an essentially finite sequence `(bᵢ)_{i ∈ ℕ}` with
`bᵢ ∈ {0, 1}` such that `n = ∑_{i ∈ ℕ} bᵢ · 2^i`.

In Mathlib, this is captured by the equivalence `Finset.equivBitIndices : ℕ ≃ Finset ℕ`,
where a finset `s ⊆ ℕ` represents the binary sequence with `bᵢ = 1` iff `i ∈ s`.
-/

section BinaryRepresentation

open Finset in
/-- **Binary Representation Definition**.

A binary representation of `n` is a finset `s ⊆ ℕ` such that `n = ∑_{i ∈ s} 2^i`.
This is equivalent to specifying which bits are 1 in the binary expansion.

The essentially finite sequence `(bᵢ)_{i ∈ ℕ}` from the textbook corresponds to
`bᵢ = 1` if `i ∈ s`, and `bᵢ = 0` otherwise. -/
def BinaryRepresentation (n : ℕ) (s : Finset ℕ) : Prop :=
  n = ∑ i ∈ s, 2 ^ i

/-- Every natural number has a binary representation.
(Existence part of Theorem thm.fps.laure.binary-rep-uniq) -/
theorem exists_binaryRepresentation (n : ℕ) : ∃ s : Finset ℕ, BinaryRepresentation n s :=
  ⟨n.bitIndices.toFinset, by simp [BinaryRepresentation, List.sum_toFinset _ Nat.bitIndices_nodup]⟩

/-- The binary representation is unique.
(Uniqueness part of Theorem thm.fps.laure.binary-rep-uniq) -/
theorem binaryRepresentation_unique {n : ℕ} {s t : Finset ℕ}
    (hs : BinaryRepresentation n s) (ht : BinaryRepresentation n t) : s = t := by
  simp only [BinaryRepresentation] at hs ht
  exact Finset.geomSum_injective (by norm_num : 2 ≤ 2) (hs.symm.trans ht)

/-- **Unique Binary Representation Theorem**.
(Theorem thm.fps.laure.binary-rep-uniq, label: thm.fps.laure.binary-rep-uniq)

Each natural number `n` has a unique binary representation. More precisely, there exists
a unique finset `s ⊆ ℕ` such that `n = ∑_{i ∈ s} 2^i`.

This is a fundamental result that motivates the study of Laurent series: when trying to
prove the analogous result for balanced ternary representations (where coefficients can
be -1, 0, or 1), we need to work with negative powers of the base, which leads naturally
to Laurent series. -/
theorem binaryRepresentation_exists_unique (n : ℕ) :
    ∃! s : Finset ℕ, BinaryRepresentation n s := by
  use n.bitIndices.toFinset
  constructor
  · simp [BinaryRepresentation, List.sum_toFinset _ Nat.bitIndices_nodup]
  · intro t ht
    simp only [BinaryRepresentation] at ht
    have h1 : n = ∑ i ∈ n.bitIndices.toFinset, 2 ^ i := by
      simp [List.sum_toFinset _ Nat.bitIndices_nodup]
    exact Finset.geomSum_injective (by norm_num : 2 ≤ 2) (ht.symm.trans h1)

/-- The canonical binary representation of `n` is `n.bitIndices.toFinset`. -/
def canonicalBinaryRep (n : ℕ) : Finset ℕ := n.bitIndices.toFinset

/-- The canonical binary representation satisfies the defining property. -/
theorem canonicalBinaryRep_spec (n : ℕ) : BinaryRepresentation n (canonicalBinaryRep n) := by
  simp [BinaryRepresentation, canonicalBinaryRep, List.sum_toFinset _ Nat.bitIndices_nodup]

/-- The canonical binary representation is the unique one. -/
theorem canonicalBinaryRep_eq_of_binaryRepresentation {n : ℕ} {s : Finset ℕ}
    (hs : BinaryRepresentation n s) : s = canonicalBinaryRep n :=
  binaryRepresentation_unique hs (canonicalBinaryRep_spec n)

/-- **Bijection between ℕ and Finset ℕ via binary representation**.

This equivalence maps `n` to its binary representation (as a finset of indices where
the binary digit is 1), and conversely maps a finset `s` to `∑_{i ∈ s} 2^i`.

This is the formalization of the bijection implicit in Theorem thm.fps.laure.binary-rep-uniq. -/
def binaryRepEquiv : ℕ ≃ Finset ℕ := Finset.equivBitIndices

/-- The equivalence sends `n` to its canonical binary representation. -/
theorem binaryRepEquiv_apply (n : ℕ) : binaryRepEquiv n = canonicalBinaryRep n := rfl

/-- The inverse of the equivalence computes the sum `∑_{i ∈ s} 2^i`. -/
theorem binaryRepEquiv_symm_apply (s : Finset ℕ) : binaryRepEquiv.symm s = ∑ i ∈ s, 2 ^ i := rfl

/-- Round-trip: converting to binary representation and back gives the original number. -/
theorem binaryRepEquiv_left_inv (n : ℕ) : binaryRepEquiv.symm (binaryRepEquiv n) = n :=
  binaryRepEquiv.symm_apply_apply n

/-- Round-trip: converting from binary representation and back gives the original finset. -/
theorem binaryRepEquiv_right_inv (s : Finset ℕ) : binaryRepEquiv (binaryRepEquiv.symm s) = s :=
  binaryRepEquiv.apply_symm_apply s

end BinaryRepresentation

/-!
## Section: Balanced Ternary Representation Uniqueness

This section proves Theorem `thm.fps.laure.balanced-tern-rep-uniq`: Every integer
has a unique balanced ternary representation.

A **balanced ternary representation** of an integer `n` is an essentially finite
sequence `(b_i)_{i∈ℕ}` with `b_i ∈ {-1, 0, 1}` such that `n = ∑_{i∈ℕ} b_i · 3^i`.

The proof uses Laurent polynomials and the key identity:
  `∏_{i=0}^{k} (1 + x^{3^i} + x^{-3^i}) = ∑_{|n| ≤ M_k} x^n`
where `M_k = 3^0 + 3^1 + ... + 3^k = (3^{k+1} - 1) / 2`.

Comparing coefficients shows that each integer in `[-M_k, M_k]` has exactly one
k-bounded balanced ternary representation. Taking `k → ∞` gives the full result.
-/

section BalancedTernaryRepresentation

open Finset

/-- The set of balanced ternary digits {-1, 0, 1}. -/
def btDigits : Finset ℤ := {-1, 0, 1}

theorem btDigits_card : btDigits.card = 3 := by decide

theorem mem_btDigits_iff (b : ℤ) : b ∈ btDigits ↔ b = -1 ∨ b = 0 ∨ b = 1 := by
  simp [btDigits]

/-- **Balanced Ternary Representation Definition**.
(Definition def.fps.laure.balanced-tern, label: def.fps.laure.balanced-tern)

A balanced ternary representation of an integer `n` is a finitely supported
function `f : ℕ → ℤ` with values in {-1, 0, 1} such that `n = ∑_i f(i) · 3^i`.

Unlike binary representations (where digits are 0 or 1), balanced ternary
allows digits to be -1, 0, or 1. This enables direct representation of
negative integers without a separate sign. -/
structure BalancedTernaryRep (n : ℤ) where
  /-- The digit function -/
  digits : ℕ →₀ ℤ
  /-- All digits are in {-1, 0, 1} -/
  digits_range : ∀ i, digits i ∈ btDigits
  /-- The value equals n -/
  sum_eq : ∑ i ∈ digits.support, digits i * (3 : ℤ) ^ i = n

/-- The value of a finitely supported balanced ternary representation. -/
def balancedTernaryValue (f : ℕ →₀ ℤ) : ℤ :=
  ∑ i ∈ f.support, f i * (3 : ℤ) ^ i

/-- A k-bounded balanced ternary representation is a function `f : Fin (k+1) → {-1, 0, 1}`.

These are representations where `f(i) = 0` for all `i > k`. -/
def kBoundedBTReps (k : ℕ) : Finset (Fin (k + 1) → ℤ) :=
  Fintype.piFinset (fun _ => btDigits)

/-- The value of a k-bounded balanced ternary representation. -/
def kBoundedBTValue (k : ℕ) (f : Fin (k + 1) → ℤ) : ℤ :=
  ∑ i : Fin (k + 1), f i * (3 : ℤ) ^ (i : ℕ)

/-- The number of k-bounded balanced ternary representations is 3^{k+1}. -/
theorem card_kBoundedBTReps (k : ℕ) : (kBoundedBTReps k).card = 3 ^ (k + 1) := by
  unfold kBoundedBTReps
  rw [Fintype.card_piFinset]
  simp [Finset.prod_const, btDigits_card]

/-- The maximum absolute value representable with k+1 balanced ternary digits:
    `M_k = 3^0 + 3^1 + ... + 3^k = (3^{k+1} - 1) / 2` -/
def maxBT (k : ℕ) : ℕ := ∑ i ∈ range (k + 1), 3 ^ i

/-- Key identity: `2 * M_k + 1 = 3^{k+1}`. -/
theorem maxBT_eq (k : ℕ) : 2 * maxBT k + 1 = 3 ^ (k + 1) := by
  unfold maxBT
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, mul_add]
    calc 2 * ∑ x ∈ range (n + 1), 3 ^ x + 2 * 3 ^ (n + 1) + 1
        = (2 * ∑ x ∈ range (n + 1), 3 ^ x + 1) + 2 * 3 ^ (n + 1) := by ring
      _ = 3 ^ (n + 1) + 2 * 3 ^ (n + 1) := by rw [ih]
      _ = 3 * 3 ^ (n + 1) := by ring
      _ = 3 ^ (n + 1 + 1) := by ring_nf

/-- The set of integers from -M to M. -/
def Icc_symm (M : ℕ) : Finset ℤ := Icc (-(M : ℤ)) (M : ℤ)

/-- The cardinality of `Icc (-M) M` is `2M + 1`. -/
theorem card_Icc_symm (M : ℕ) : (Icc_symm M).card = 2 * M + 1 := by
  unfold Icc_symm
  rw [Int.card_Icc]
  omega

/-- Cardinality of `Icc_symm (maxBT k)` equals `3^{k+1}`. -/
theorem card_Icc_symm_maxBT (k : ℕ) : (Icc_symm (maxBT k)).card = 3 ^ (k + 1) := by
  rw [card_Icc_symm, maxBT_eq]

/-- Helper for the bounds: sum of 3^i over Fin (k+1) equals sum over range (k+1). -/
theorem sum_pow_three_Fin_eq_range (k : ℕ) :
    (∑ i : Fin (k + 1), (3 : ℤ) ^ (i : ℕ)) = ∑ i ∈ range (k + 1), (3 : ℤ) ^ i :=
  Fin.sum_univ_eq_sum_range (fun i => (3 : ℤ) ^ i) (k + 1)

/-- The value of any k-bounded representation is in `[-M_k, M_k]`. -/
theorem kBoundedBTValue_mem_Icc (k : ℕ) (f : Fin (k + 1) → ℤ) (hf : f ∈ kBoundedBTReps k) :
    kBoundedBTValue k f ∈ Icc_symm (maxBT k) := by
  unfold kBoundedBTValue Icc_symm maxBT
  simp only [mem_Icc]
  have hf' : ∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1 := fun i => by
    simp only [kBoundedBTReps, Fintype.mem_piFinset] at hf
    exact (mem_btDigits_iff _).mp (hf i)
  constructor
  · -- Lower bound: -M_k ≤ value
    have h : ∑ i : Fin (k + 1), (-1 : ℤ) * (3 : ℤ) ^ (i : ℕ) ≤ ∑ i : Fin (k + 1), f i * (3 : ℤ) ^ (i : ℕ) := by
      apply sum_le_sum
      intro i _
      have h3pos : (0 : ℤ) < (3 : ℤ) ^ (i : ℕ) := pow_pos (by norm_num) _
      rcases hf' i with hi | hi | hi <;> simp only [hi] <;> linarith
    have heq : ∑ i : Fin (k + 1), (-1 : ℤ) * (3 : ℤ) ^ (i : ℕ) = -(∑ i : Fin (k + 1), (3 : ℤ) ^ (i : ℕ)) := by
      rw [← sum_neg_distrib]
      congr 1
      ext i
      ring
    rw [heq, sum_pow_three_Fin_eq_range] at h
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
    exact h
  · -- Upper bound: value ≤ M_k
    have h : ∑ i : Fin (k + 1), f i * (3 : ℤ) ^ (i : ℕ) ≤ ∑ i : Fin (k + 1), (1 : ℤ) * (3 : ℤ) ^ (i : ℕ) := by
      apply sum_le_sum
      intro i _
      have h3pos : (0 : ℤ) < (3 : ℤ) ^ (i : ℕ) := pow_pos (by norm_num) _
      rcases hf' i with hi | hi | hi <;> simp only [hi] <;> linarith
    have heq : ∑ i : Fin (k + 1), (1 : ℤ) * (3 : ℤ) ^ (i : ℕ) = ∑ i : Fin (k + 1), (3 : ℤ) ^ (i : ℕ) := by
      congr 1
      ext i
      ring
    rw [heq, sum_pow_three_Fin_eq_range] at h
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
    exact h

/-- If two balanced ternary representations have the same value, they are equal.

This is the key injectivity lemma for balanced ternary representations.
The proof uses a mod 3 argument at each digit position:
- The lowest digit determines the value mod 3
- Subtracting the lowest digit and dividing by 3 gives a smaller representation
- By strong induction, the remaining digits must also be equal. -/
private lemma balanced_ternary_injective (k : ℕ) (f g : Fin (k + 1) → ℤ)
    (hf : ∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1)
    (hg : ∀ i, g i = -1 ∨ g i = 0 ∨ g i = 1)
    (hfg : ∑ i : Fin (k + 1), f i * (3 : ℤ) ^ (i : ℕ) =
           ∑ i : Fin (k + 1), g i * (3 : ℤ) ^ (i : ℕ)) :
    f = g := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      ext i
      fin_cases i
      have h1 : (∑ i : Fin 1, f i * (3 : ℤ) ^ (i : ℕ)) = f 0 := by simp
      have h2 : (∑ i : Fin 1, g i * (3 : ℤ) ^ (i : ℕ)) = g 0 := by simp
      rw [h1, h2] at hfg
      exact hfg
    | succ n =>
      have h0 : f 0 = g 0 := by
        have hf_mod : (∑ i : Fin (n + 2), f i * (3 : ℤ) ^ (i : ℕ)) % 3 = f 0 % 3 := by
          have : ∑ i : Fin (n + 2), f i * (3 : ℤ) ^ (i : ℕ) = f 0 +
                 ∑ i : Fin (n + 1), f i.succ * (3 : ℤ) ^ (i.val + 1) := by
            rw [Fin.sum_univ_succ]
            simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
          rw [this]
          have hdiv : (3 : ℤ) ∣ ∑ i : Fin (n + 1), f i.succ * (3 : ℤ) ^ (i.val + 1) := by
            apply dvd_sum
            intro i _
            rw [pow_succ]
            exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
          obtain ⟨c, hc⟩ := hdiv
          rw [hc]
          omega
        have hg_mod : (∑ i : Fin (n + 2), g i * (3 : ℤ) ^ (i : ℕ)) % 3 = g 0 % 3 := by
          have : ∑ i : Fin (n + 2), g i * (3 : ℤ) ^ (i : ℕ) = g 0 +
                 ∑ i : Fin (n + 1), g i.succ * (3 : ℤ) ^ (i.val + 1) := by
            rw [Fin.sum_univ_succ]
            simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
          rw [this]
          have hdiv : (3 : ℤ) ∣ ∑ i : Fin (n + 1), g i.succ * (3 : ℤ) ^ (i.val + 1) := by
            apply dvd_sum
            intro i _
            rw [pow_succ]
            exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
          obtain ⟨c, hc⟩ := hdiv
          rw [hc]
          omega
        rw [hfg] at hf_mod
        have hmod_eq : f 0 % 3 = g 0 % 3 := hf_mod.symm.trans hg_mod
        rcases hf 0 with hf0 | hf0 | hf0 <;> rcases hg 0 with hg0 | hg0 | hg0 <;>
          simp only [hf0, hg0] at hmod_eq ⊢ <;> omega
      ext ⟨i, hi⟩
      cases i with
      | zero => exact h0
      | succ j =>
        let f' : Fin (n + 1) → ℤ := fun i => f i.succ
        let g' : Fin (n + 1) → ℤ := fun i => g i.succ
        have hf' : ∀ i, f' i = -1 ∨ f' i = 0 ∨ f' i = 1 := fun i => hf i.succ
        have hg' : ∀ i, g' i = -1 ∨ g' i = 0 ∨ g' i = 1 := fun i => hg i.succ
        have hfg' : ∑ i : Fin (n + 1), f' i * (3 : ℤ) ^ (i : ℕ) =
                    ∑ i : Fin (n + 1), g' i * (3 : ℤ) ^ (i : ℕ) := by
          have hsum_f : ∑ i : Fin (n + 2), f i * (3 : ℤ) ^ (i : ℕ) =
                        f 0 + 3 * ∑ i : Fin (n + 1), f' i * (3 : ℤ) ^ (i : ℕ) := by
            rw [Fin.sum_univ_succ]
            simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, f']
            rw [mul_sum]
            congr 1
            apply sum_congr rfl
            intro i _
            ring
          have hsum_g : ∑ i : Fin (n + 2), g i * (3 : ℤ) ^ (i : ℕ) =
                        g 0 + 3 * ∑ i : Fin (n + 1), g' i * (3 : ℤ) ^ (i : ℕ) := by
            rw [Fin.sum_univ_succ]
            simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, g']
            rw [mul_sum]
            congr 1
            apply sum_congr rfl
            intro i _
            ring
          rw [hsum_f, hsum_g, h0] at hfg
          linarith
        have heq : f' = g' := ih n (by omega) f' g' hf' hg' hfg'
        have hj : j < n + 1 := by omega
        have : f' ⟨j, hj⟩ = g' ⟨j, hj⟩ := congrFun heq ⟨j, hj⟩
        simp only [f', g'] at this
        convert this using 2 <;> rfl

/-- kBoundedBTValue is injective on kBoundedBTReps. -/
theorem kBoundedBTValue_injective_on (k : ℕ) :
    Set.InjOn (kBoundedBTValue k) (kBoundedBTReps k : Set (Fin (k + 1) → ℤ)) := by
  intro f hf g hg hfg
  have hf' : ∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1 := fun i => by
    have : f ∈ kBoundedBTReps k := hf
    simp only [kBoundedBTReps, Fintype.mem_piFinset] at this
    exact (mem_btDigits_iff _).mp (this i)
  have hg' : ∀ i, g i = -1 ∨ g i = 0 ∨ g i = 1 := fun i => by
    have : g ∈ kBoundedBTReps k := hg
    simp only [kBoundedBTReps, Fintype.mem_piFinset] at this
    exact (mem_btDigits_iff _).mp (this i)
  exact balanced_ternary_injective k f g hf' hg' hfg

/-- **Each integer in `[-M_k, M_k]` has a unique k-bounded balanced ternary representation**.

This is the finite version of the balanced ternary uniqueness theorem.

The proof uses a cardinality argument:
- There are `3^{k+1}` k-bounded representations (`card_kBoundedBTReps`)
- The target set `Icc_symm (maxBT k)` has cardinality `3^{k+1}` (`card_Icc_symm_maxBT`)
- Each representation maps to a value in the target set (`kBoundedBTValue_mem_Icc`)
- By the pigeonhole principle, the map is a bijection

(Part of Theorem thm.fps.laure.balanced-tern-rep-uniq) -/
theorem kBounded_unique (k : ℕ) (n : ℤ) (hn : n ∈ Icc_symm (maxBT k)) :
    ∃! f ∈ kBoundedBTReps k, kBoundedBTValue k f = n := by
  -- The map from kBoundedBTReps to Icc_symm is a bijection by cardinality
  have h_card_eq : (kBoundedBTReps k).card = (Icc_symm (maxBT k)).card := by
    rw [card_kBoundedBTReps, card_Icc_symm_maxBT]
  have h_image_subset : (kBoundedBTReps k).image (kBoundedBTValue k) ⊆ Icc_symm (maxBT k) := by
    intro x hx
    simp only [mem_image] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    exact kBoundedBTValue_mem_Icc k f hf
  -- The image has the same cardinality as kBoundedBTReps because the map is injective
  have h_card_image : ((kBoundedBTReps k).image (kBoundedBTValue k)).card = (kBoundedBTReps k).card := by
    rw [card_image_of_injOn (kBoundedBTValue_injective_on k)]
  -- So the image equals Icc_symm
  have h_image_eq : (kBoundedBTReps k).image (kBoundedBTValue k) = Icc_symm (maxBT k) := by
    apply eq_of_subset_of_card_le h_image_subset
    rw [h_card_image, h_card_eq]
  -- Existence: n is in the image
  have h_exists : ∃ f ∈ kBoundedBTReps k, kBoundedBTValue k f = n := by
    rw [← h_image_eq] at hn
    simp only [mem_image] at hn
    exact hn
  -- Uniqueness: from injectivity
  obtain ⟨f, hf_mem, hf_val⟩ := h_exists
  use f
  constructor
  · exact ⟨hf_mem, hf_val⟩
  · intro g ⟨hg_mem, hg_val⟩
    exact (kBoundedBTValue_injective_on k hf_mem hg_mem (hf_val.trans hg_val.symm)).symm

/-- Helper to convert a k-bounded representation to a Finsupp. -/
noncomputable def kBoundedToFinsupp (k : ℕ) (f : Fin (k + 1) → ℤ) : ℕ →₀ ℤ :=
  Finsupp.onFinset (range (k + 1)) (fun i => if h : i < k + 1 then f ⟨i, h⟩ else 0)
    (fun i hi => by
      simp only [mem_range, ne_eq] at hi ⊢
      by_contra h
      push Not at h
      exact hi (dite_eq_right (not_lt.mpr h)))

theorem kBoundedToFinsupp_apply (k : ℕ) (f : Fin (k + 1) → ℤ) (i : ℕ) (hi : i < k + 1) :
    kBoundedToFinsupp k f i = f ⟨i, hi⟩ := by
  simp only [kBoundedToFinsupp, Finsupp.onFinset_apply, hi, dite_true]

theorem kBoundedToFinsupp_apply_of_ge (k : ℕ) (f : Fin (k + 1) → ℤ) (i : ℕ) (hi : k + 1 ≤ i) :
    kBoundedToFinsupp k f i = 0 := by
  simp only [kBoundedToFinsupp, Finsupp.onFinset_apply]
  simp only [not_lt.mpr hi, dite_false]

/-- The sum over kBoundedToFinsupp equals kBoundedBTValue. -/
theorem kBoundedToFinsupp_sum (k : ℕ) (f : Fin (k + 1) → ℤ) :
    ∑ i ∈ (kBoundedToFinsupp k f).support, (kBoundedToFinsupp k f) i * (3 : ℤ) ^ i = kBoundedBTValue k f := by
  unfold kBoundedBTValue
  have hsup : (kBoundedToFinsupp k f).support ⊆ range (k + 1) := by
    intro i hi
    simp only [Finsupp.mem_support_iff] at hi
    by_contra h
    simp only [mem_range, not_lt] at h
    rw [kBoundedToFinsupp_apply_of_ge k f i h] at hi
    exact hi rfl
  rw [sum_subset hsup]
  · rw [sum_range (fun i => (kBoundedToFinsupp k f) i * (3 : ℤ) ^ i)]
    apply sum_congr rfl
    intro i _
    rw [kBoundedToFinsupp_apply k f i i.isLt]
  · intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi]
    ring

/-- **Every integer has a balanced ternary representation**.
(Existence part of Theorem thm.fps.laure.balanced-tern-rep-uniq)

For any integer n, we can find k large enough that |n| ≤ M_k, then use
the k-bounded existence result. -/
theorem balancedTernary_exists (n : ℤ) : Nonempty (BalancedTernaryRep n) := by
  -- Find k such that |n| ≤ maxBT k
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (|n| : ℤ) ≤ maxBT k := by
    use n.natAbs
    have h3 : n.natAbs ≤ maxBT n.natAbs := by
      unfold maxBT
      have h1 : n.natAbs < 3 ^ n.natAbs :=
        Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left (by norm_num : 2 ≤ 3) n.natAbs)
      have h2 : (3 : ℕ) ^ n.natAbs ≤ ∑ i ∈ range (n.natAbs + 1), 3 ^ i := by
        apply single_le_sum (fun i _ => Nat.zero_le _)
        exact mem_range.mpr (Nat.lt_succ_self _)
      omega
    simp only [Int.abs_eq_natAbs]
    exact Int.ofNat_le.mpr h3
  -- Show that n ∈ Icc_symm (maxBT k)
  have hn_mem : n ∈ Icc_symm (maxBT k) := by
    simp only [Icc_symm, mem_Icc]
    constructor
    · calc -(maxBT k : ℤ) ≤ -|n| := by omega
        _ ≤ n := neg_abs_le n
    · calc n ≤ |n| := le_abs_self n
        _ ≤ maxBT k := hk
  -- Use kBounded_unique to get existence
  obtain ⟨f, ⟨hf_mem, hf_val⟩, _⟩ := kBounded_unique k n hn_mem
  -- Convert f to a BalancedTernaryRep
  let digits : ℕ →₀ ℤ := kBoundedToFinsupp k f
  have hdigits_range : ∀ i, digits i ∈ btDigits := by
    intro i
    by_cases hi : i < k + 1
    · rw [kBoundedToFinsupp_apply k f i hi]
      simp only [kBoundedBTReps, Fintype.mem_piFinset] at hf_mem
      exact hf_mem ⟨i, hi⟩
    · rw [kBoundedToFinsupp_apply_of_ge k f i (by omega)]
      simp [btDigits]
  have hsum_eq : ∑ i ∈ digits.support, digits i * (3 : ℤ) ^ i = n := by
    rw [kBoundedToFinsupp_sum k f, hf_val]
  exact ⟨⟨digits, hdigits_range, hsum_eq⟩⟩

/-- Key lemma: 2 * ∑_{i<k} 3^i < 3^k. -/
theorem two_sum_lt_pow_three (k : ℕ) : 2 * ∑ i ∈ range k, (3 : ℤ) ^ i < 3 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, pow_succ]
    have h : 2 * ∑ x ∈ range n, (3 : ℤ) ^ x < 3 ^ n := ih
    nlinarith [pow_nonneg (by norm_num : (0 : ℤ) ≤ 3) n]

/-- The sum over a superset equals the sum over the support (for finitely supported functions). -/
theorem sum_eq_sum_support' (f : ℕ →₀ ℤ) (s : Finset ℕ) (hs : f.support ⊆ s) :
    ∑ i ∈ s, f i * (3 : ℤ) ^ i = ∑ i ∈ f.support, f i * (3 : ℤ) ^ i := by
  symm
  apply sum_subset hs
  intro i _ hi
  simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hi
  simp [hi]

/-- If a, b ∈ {-1, 0, 1} and a ≠ b, then |a - b| ≥ 1. -/
theorem btDigits_diff_abs_ge_one {a b : ℤ} (ha : a ∈ btDigits) (hb : b ∈ btDigits) (hab : a ≠ b) :
    |a - b| ≥ 1 := by
  simp only [btDigits, mem_insert, mem_singleton] at ha hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp only [ha, hb] at hab ⊢ <;> try norm_num
  all_goals exact absurd rfl hab

/-- If a, b ∈ {-1, 0, 1}, then |a - b| ≤ 2. -/
theorem btDigits_diff_abs_le_two {a b : ℤ} (ha : a ∈ btDigits) (hb : b ∈ btDigits) :
    |a - b| ≤ 2 := by
  simp only [btDigits, mem_insert, mem_singleton] at ha hb
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
    simp only [ha, hb] <;> norm_num

/-- Two finitely supported functions with values in btDigits and the same weighted sum are equal. -/
theorem btDigits_sum_unique (f g : ℕ →₀ ℤ) 
    (hf : ∀ i, f i ∈ btDigits) (hg : ∀ i, g i ∈ btDigits)
    (hsum : ∑ i ∈ f.support, f i * (3 : ℤ) ^ i = ∑ i ∈ g.support, g i * (3 : ℤ) ^ i) :
    f = g := by
  by_contra hne
  have hdiff : ∃ i, f i ≠ g i := by
    by_contra hall
    push Not at hall
    exact hne (Finsupp.ext hall)
  let S := f.support ∪ g.support
  have hf_sum : ∑ i ∈ S, f i * (3 : ℤ) ^ i = ∑ i ∈ f.support, f i * (3 : ℤ) ^ i := 
    sum_eq_sum_support' f S (subset_union_left)
  have hg_sum : ∑ i ∈ S, g i * (3 : ℤ) ^ i = ∑ i ∈ g.support, g i * (3 : ℤ) ^ i := 
    sum_eq_sum_support' g S (subset_union_right)
  have hdiff_sum : ∑ i ∈ S, (f i - g i) * (3 : ℤ) ^ i = 0 := by
    have : ∑ i ∈ S, (f i - g i) * (3 : ℤ) ^ i = 
           ∑ i ∈ S, f i * (3 : ℤ) ^ i - ∑ i ∈ S, g i * (3 : ℤ) ^ i := by
      rw [← sum_sub_distrib]
      congr 1
      ext i
      ring
    rw [this, hf_sum, hg_sum, hsum, sub_self]
  let D := S.filter (fun i => f i ≠ g i)
  have hD_nonempty : D.Nonempty := by
    obtain ⟨i, hi⟩ := hdiff
    use i
    simp only [D, mem_filter, S, mem_union, Finsupp.mem_support_iff, ne_eq]
    constructor
    · by_contra h
      push Not at h
      exact hi (h.1.trans h.2.symm)
    · exact hi
  let k := D.max' hD_nonempty
  have hk_mem : k ∈ D := max'_mem D hD_nonempty
  have hk_diff : f k ≠ g k := (mem_filter.mp hk_mem).2
  have hk_max : ∀ i ∈ D, i ≤ k := fun i hi => le_max' D i hi
  have hk_agree : ∀ i ∈ S, k < i → f i = g i := by
    intro i hi hki
    by_contra h
    have : i ∈ D := by simp only [D, mem_filter]; exact ⟨hi, h⟩
    have : i ≤ k := hk_max i this
    omega
  have hk_in_S : k ∈ S := (mem_filter.mp hk_mem).1
  have hsum_eq : ∑ i ∈ S, (f i - g i) * (3 : ℤ) ^ i = 
                 ∑ i ∈ S.filter (· ≤ k), (f i - g i) * (3 : ℤ) ^ i := by
    symm
    apply sum_subset (filter_subset _ _)
    intro i hi hni
    simp only [mem_filter, not_and, not_le] at hni
    have hik : k < i := hni hi
    simp only [hk_agree i hi hik, sub_self, zero_mul]
  rw [hsum_eq] at hdiff_sum
  have hk_in_filter : k ∈ S.filter (· ≤ k) := by
    simp only [mem_filter, le_refl, and_true]
    exact hk_in_S
  have hk_not_in_erase : k ∉ (S.filter (· ≤ k)).erase k := by
    simp only [mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
  rw [← insert_erase hk_in_filter, sum_insert hk_not_in_erase] at hdiff_sum
  have herase_subset : (S.filter (· ≤ k)).erase k ⊆ range k := by
    intro i hi
    simp only [mem_erase, mem_filter] at hi
    simp only [mem_range]
    omega
  have hbound : |∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i| ≤ 
                2 * ∑ i ∈ range k, (3 : ℤ) ^ i := by
    calc |∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i|
        ≤ ∑ i ∈ (S.filter (· ≤ k)).erase k, |(f i - g i) * (3 : ℤ) ^ i| := abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ (S.filter (· ≤ k)).erase k, |f i - g i| * (3 : ℤ) ^ i := by
          congr 1; ext i
          rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℤ) < 3)]
      _ ≤ ∑ i ∈ (S.filter (· ≤ k)).erase k, 2 * (3 : ℤ) ^ i := by
          apply sum_le_sum
          intro i _
          have h := btDigits_diff_abs_le_two (hf i) (hg i)
          have h3pos : (0 : ℤ) < 3 ^ i := pow_pos (by norm_num) i
          nlinarith
      _ ≤ ∑ i ∈ range k, 2 * (3 : ℤ) ^ i := by
          apply sum_le_sum_of_subset_of_nonneg herase_subset
          intro i _ _
          have h3pos : (0 : ℤ) < 3 ^ i := pow_pos (by norm_num) i
          linarith
      _ = 2 * ∑ i ∈ range k, (3 : ℤ) ^ i := by rw [mul_sum]
  have hk_eq : (f k - g k) * (3 : ℤ) ^ k = 
               -∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i := by
    linarith
  have habs_eq : |(f k - g k) * (3 : ℤ) ^ k| = 
                 |∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i| := by
    rw [hk_eq, abs_neg]
  have hfk_gk_bound : |f k - g k| ≥ 1 := btDigits_diff_abs_ge_one (hf k) (hg k) hk_diff
  have hlower : |(f k - g k) * (3 : ℤ) ^ k| ≥ (3 : ℤ) ^ k := by
    rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℤ) < 3)]
    have h3k_pos : (0 : ℤ) < 3 ^ k := pow_pos (by norm_num) k
    nlinarith
  have hupper : |∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i| < (3 : ℤ) ^ k := by
    calc |∑ i ∈ (S.filter (· ≤ k)).erase k, (f i - g i) * (3 : ℤ) ^ i|
        ≤ 2 * ∑ i ∈ range k, (3 : ℤ) ^ i := hbound
      _ < (3 : ℤ) ^ k := two_sum_lt_pow_three k
  rw [habs_eq] at hlower
  linarith

/-- **The balanced ternary representation is unique**.
(Uniqueness part of Theorem thm.fps.laure.balanced-tern-rep-uniq)

If two balanced ternary representations have the same value, they must be equal. -/
theorem balancedTernary_unique (n : ℤ) (r1 r2 : BalancedTernaryRep n) :
    r1.digits = r2.digits := by
  apply btDigits_sum_unique
  · exact r1.digits_range
  · exact r2.digits_range
  · rw [r1.sum_eq, r2.sum_eq]

/-- **Unique Balanced Ternary Representation Theorem**.
(Theorem thm.fps.laure.balanced-tern-rep-uniq, label: thm.fps.laure.balanced-tern-rep-uniq)

Each integer `n` has a unique balanced ternary representation. More precisely, there exists
a unique finitely supported function `f : ℕ → ℤ` with values in {-1, 0, 1} such that
`n = ∑_{i ∈ support(f)} f(i) · 3^i`.

This theorem generalizes the binary representation uniqueness to allow negative digits,
which enables representing negative integers directly (without a separate sign).

The proof uses Laurent polynomials and the key identity:
  `∏_{i=0}^{k} (1 + x^{3^i} + x^{-3^i}) = ∑_{|n| ≤ M_k} x^n`
where `M_k = 3^0 + 3^1 + ... + 3^k = (3^{k+1} - 1) / 2`.

Comparing coefficients shows that each integer in `[-M_k, M_k]` has exactly one
k-bounded balanced ternary representation. Taking `k → ∞` gives the full result.

Historical note: Balanced ternary representations were used in the Soviet Setun computer
(1960s/70s). The uniqueness theorem goes back to Fibonacci. -/
theorem balancedTernary_exists_unique (n : ℤ) :
    ∃! f : ℕ →₀ ℤ, (∀ i, f i ∈ btDigits) ∧ balancedTernaryValue f = n := by
  obtain ⟨rep⟩ := balancedTernary_exists n
  use rep.digits
  constructor
  · exact ⟨rep.digits_range, rep.sum_eq⟩
  · intro f ⟨hf_range, hf_sum⟩
    let rep2 : BalancedTernaryRep n := ⟨f, hf_range, hf_sum⟩
    exact balancedTernary_unique n rep2 rep

end BalancedTernaryRepresentation

/-!
## Section: Equivalence with Alternative Balanced Ternary Representation

This section establishes the equivalence between the `BalancedTernaryRep` structure
defined in this file (using `ℕ →₀ ℤ` with `btDigits` constraint) and the 
`AlgebraicCombinatorics.BalancedTernaryRepresentation` structure defined in 
`LaurentSeries.lean` (using an inductive `BalancedTernaryDigit` type).

Both representations capture the same mathematical concept: balanced ternary 
representations of integers. The equivalence theorems below show that:
1. Any `BalancedTernaryRepresentation` can be converted to a `BalancedTernaryRep`
2. Any `BalancedTernaryRep` can be converted to a `BalancedTernaryRepresentation`  
3. These conversions are inverses of each other (up to the digit representation)

This provides a bridge between the two equivalent formulations.
-/

section BalancedTernaryEquivalence

-- Alias for the type from LaurentSeries.lean for clarity
abbrev BTRep := AlgebraicCombinatorics.BalancedTernaryRepresentation
abbrev BTDigit := AlgebraicCombinatorics.BalancedTernaryDigit

/-- The existing `BalancedTernaryDigit.toInt` maps into `btDigits`. -/
theorem BTDigit.toInt_mem_btDigits (d : BTDigit) : d.toInt ∈ btDigits := by
  cases d <;> simp [AlgebraicCombinatorics.BalancedTernaryDigit.toInt, btDigits]

/-- Convert an integer in `btDigits` to a `BalancedTernaryDigit`. -/
def btDigitOfInt (z : ℤ) : BTDigit :=
  if z = -1 then .negOne
  else if z = 0 then .zero
  else .one

@[simp]
theorem btDigitOfInt_toInt (z : ℤ) (hz : z ∈ btDigits) : 
    (btDigitOfInt z).toInt = z := by
  simp only [btDigits, Finset.mem_insert, Finset.mem_singleton] at hz
  simp only [btDigitOfInt]
  rcases hz with hz | hz | hz <;> 
    simp [hz, AlgebraicCombinatorics.BalancedTernaryDigit.toInt]

@[simp]
theorem toInt_btDigitOfInt (d : BTDigit) : btDigitOfInt d.toInt = d := by
  cases d <;> simp [btDigitOfInt, AlgebraicCombinatorics.BalancedTernaryDigit.toInt]

/-- `btDigitOfInt 0 = zero` -/
@[simp]
theorem btDigitOfInt_zero : 
    btDigitOfInt 0 = AlgebraicCombinatorics.BalancedTernaryDigit.zero := by 
  simp [btDigitOfInt]

/-- `btDigitOfInt z ≠ 0` iff `z ≠ 0` (for `z ∈ btDigits`) -/
theorem btDigitOfInt_ne_zero_iff (z : ℤ) (hz : z ∈ btDigits) : 
    btDigitOfInt z ≠ 0 ↔ z ≠ 0 := by
  simp only [btDigits, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hz | hz | hz <;> simp [hz, btDigitOfInt]; rfl

/-- Convert a `BTRep` (inductive style from `LaurentSeries.lean`) 
to a `BalancedTernaryRep` (Finsupp style). -/
noncomputable def BTRep.toFinsupp {n : ℤ} (r : BTRep n) : BalancedTernaryRep n where
  digits := {
    support := r.finite_support.toFinset
    toFun := fun i => (r.digits i).toInt
    mem_support_toFun := by
      intro i
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
                 AlgebraicCombinatorics.BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero, ne_eq]
  }
  digits_range := fun i => BTDigit.toInt_mem_btDigits _
  sum_eq := by
    simp only [Finsupp.coe_mk]
    have h := r.sum_eq
    rw [finsum_eq_sum_of_support_subset _ (s := r.finite_support.toFinset)] at h
    · convert h using 1
    · intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
      intro heq
      apply hi
      simp only [heq, AlgebraicCombinatorics.BalancedTernaryDigit.toInt_zero, zero_mul]

/-- Convert a `BalancedTernaryRep` (Finsupp style) to a 
`BTRep` (inductive style from `LaurentSeries.lean`). -/
noncomputable def BalancedTernaryRep.toInductive {n : ℤ} (r : BalancedTernaryRep n) : BTRep n where
  digits := fun i => btDigitOfInt (r.digits i)
  finite_support := by
    have h : {i | btDigitOfInt (r.digits i) ≠ 0} ⊆ r.digits.support := by
      intro i hi
      simp only [Set.mem_ofPred_eq] at hi
      simp only [Finset.mem_coe, Finsupp.mem_support_iff]
      rw [btDigitOfInt_ne_zero_iff _ (r.digits_range i)] at hi
      exact hi
    exact r.digits.support.finite_toSet.subset h
  sum_eq := by
    have h := r.sum_eq
    rw [finsum_eq_sum_of_support_subset _ (s := r.digits.support)]
    · convert h using 2 with i _
      rw [btDigitOfInt_toInt _ (r.digits_range i)]
    · intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro hz
      apply hi
      rw [hz, btDigitOfInt_zero]
      simp [AlgebraicCombinatorics.BalancedTernaryDigit.toInt]

/-- **Round-trip equivalence**: Converting from the inductive representation to Finsupp 
and back gives the same digits (as `BalancedTernaryDigit` values). -/
theorem BTRep.toFinsupp_toInductive_digits {n : ℤ} (r : BTRep n) :
    r.toFinsupp.toInductive.digits = r.digits := by
  ext i
  simp only [BalancedTernaryRep.toInductive, BTRep.toFinsupp, Finsupp.coe_mk, toInt_btDigitOfInt]

/-- **Round-trip equivalence**: Converting from Finsupp representation to inductive 
and back gives the same digits (as integer values in the Finsupp). -/
theorem BalancedTernaryRep.toInductive_toFinsupp_digits {n : ℤ} (r : BalancedTernaryRep n) :
    r.toInductive.toFinsupp.digits = r.digits := by
  ext i
  simp only [BTRep.toFinsupp, BalancedTernaryRep.toInductive, Finsupp.coe_mk, 
             btDigitOfInt_toInt _ (r.digits_range i)]

/-- The two balanced ternary representations are semantically equivalent: 
they both represent the same integer. -/
theorem balancedTernary_representations_equiv (n : ℤ) :
    (∃ _ : BalancedTernaryRep n, True) ↔ (∃ _ : BTRep n, True) := by
  constructor
  · intro ⟨r, _⟩
    exact ⟨r.toInductive, trivial⟩
  · intro ⟨r, _⟩
    exact ⟨r.toFinsupp, trivial⟩

/-- Type equivalence between the two balanced ternary representations.
This shows the types `BalancedTernaryRep n` and `AlgebraicCombinatorics.BalancedTernaryRepresentation n`
are equivalent (bijective correspondence). -/
noncomputable def balancedTernary_equiv (n : ℤ) : BalancedTernaryRep n ≃ BTRep n where
  toFun := BalancedTernaryRep.toInductive
  invFun := BTRep.toFinsupp
  left_inv r := by
    have h := r.toInductive_toFinsupp_digits
    cases r with | mk digits _ _ =>
    simp only [BTRep.toFinsupp, BalancedTernaryRep.toInductive] at h ⊢
    congr 1
  right_inv r := by
    have h := r.toFinsupp_toInductive_digits
    cases r with | mk digits _ _ =>
    simp only [BalancedTernaryRep.toInductive, BTRep.toFinsupp] at h ⊢
    congr 1

end BalancedTernaryEquivalence

end AlgebraicCombinatorics.FPS.Laurent

end
