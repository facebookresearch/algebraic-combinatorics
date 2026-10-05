/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.FPSDefinition

/-!
# Derivatives of Formal Power Series

This file formalizes the theory of derivatives of formal power series (FPS) from
`AlgebraicCombinatorics/tex/FPS/Derivatives.tex`.

## Main Results

The derivative of a formal power series `f = ∑ fₙ xⁿ` is defined as `f' = ∑ n · fₙ · x^(n-1)`.

Mathlib already provides `PowerSeries.derivative` as a derivation on `R⟦X⟧`. We document
the correspondence with the textbook theorems and provide any additional results.

### Derivative Rules (Theorem thm.fps.deriv.rules)

* **(a)** `(f + g)' = f' + g'` — `derivative_add`
* **(b)** Summable families: `(∑ fᵢ)' = ∑ fᵢ'` — `derivative_sum`, `derivative_summableFPSSum`
* **(c)** `(c · f)' = c · f'` — `derivative_smul`, `derivative_C_mul`
* **(d)** `(f · g)' = f' · g + f · g'` — `derivative_mul` (Leibniz rule)
* **(e)** `(f / g)' = (f' · g - f · g') / g²` — `derivative_div` (quotient rule)
* **(f)** `(g^n)' = n · g^(n-1) · g'` — `derivative_pow'` (power rule)
* **(g)** `(f ∘ g)' = (f' ∘ g) · g'` — `derivative_comp` (chain rule)
* **(h)** If `f' = g'`, then `f - g` is constant — `derivative_eq_imp_diff_const`

## References

* Mathlib: `Mathlib.RingTheory.PowerSeries.Derivative`
* Source: `AlgebraicCombinatorics/tex/FPS/Derivatives.tex`

-/

open PowerSeries Polynomial
open AlgebraicCombinatorics.FPS (SummableFPS summableFPSSum coeff_summableFPSSum)

namespace AlgebraicCombinatorics.FPS

/-!
## Definition of Derivative

The derivative of a formal power series is already defined in Mathlib as
`PowerSeries.derivative : Derivation R R⟦X⟧ R⟦X⟧`.

For `f = ∑ fₙ xⁿ`, we have `f' = ∑ (n+1) · f_{n+1} · xⁿ`, or equivalently,
the n-th coefficient of `f'` is `(n+1) · f_{n+1}`.

This matches Definition def.fps.deriv from the source.
-/

section Definition

variable {R : Type*} [CommSemiring R]

/-!
### Definition def.fps.deriv

For `f = ∑ fₙ xⁿ`, the textbook defines `f' := ∑_{n>0} n · fₙ · x^{n-1}`.

Reindexing with m = n-1 (so n = m+1), this becomes:
`f' = ∑_{m≥0} (m+1) · f_{m+1} · x^m`

This is exactly the coefficient formula of `PowerSeries.derivative` in Mathlib:
`d⁄dX f = mk (fun n => coeff (n + 1) f * (n + 1))`

The derivative is then packaged as a `Derivation R R⟦X⟧ R⟦X⟧`.
-/

/-- **Definition def.fps.deriv**: The n-th coefficient of the derivative of f
equals (n+1) times the (n+1)-th coefficient of f.

This is `PowerSeries.coeff_derivative` in Mathlib. -/
theorem coeff_derivative_eq (f : R⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (d⁄dX f) = PowerSeries.coeff (n + 1) f * (n + 1) :=
  PowerSeries.coeff_derivative f n

/-- **Definition def.fps.deriv**: The derivative expressed in terms of `mk`.

For `f = ∑ fₙ xⁿ`, the textbook defines `f' := ∑_{n>0} n · fₙ · x^{n-1}`.
Reindexing gives `f' = mk (fun m => (m+1) * f_{m+1})`. -/
theorem derivative_eq_mk (f : R⟦X⟧) :
    d⁄dX f = PowerSeries.mk (fun n => (n + 1) * PowerSeries.coeff (n + 1) f) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, mul_comm]

/-- The derivative operation is exactly the coefficient formula
`mk (fun n => coeff (n + 1) f * (n + 1))`. -/
theorem derivative_eq_derivativeFun (f : R⟦X⟧) :
    d⁄dX f = PowerSeries.mk (fun n => PowerSeries.coeff (n + 1) f * (n + 1)) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk]

/-- Alternative characterization: the coefficient of xⁿ in f' is (n+1) · f_{n+1}.
This is the "shift and multiply" form of the derivative. -/
theorem derivative_coeff_formula (f : R⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (d⁄dX f) = (n + 1) * PowerSeries.coeff (n + 1) f := by
  rw [PowerSeries.coeff_derivative, mul_comm]

/-- The derivative of X^(n+1) is (n+1) * X^n. This is a convenient form for induction. -/
@[simp]
theorem derivative_X_pow_succ (n : ℕ) :
    d⁄dX ((PowerSeries.X : R⟦X⟧) ^ (n + 1)) = (n + 1 : R) • PowerSeries.X ^ n := by
  ext m
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_X_pow, PowerSeries.coeff_smul,
      PowerSeries.coeff_X_pow]
  by_cases h : m + 1 = n + 1
  · simp only [h, ↓reduceIte]
    have : m = n := by omega
    simp [this]
  · simp only [h, ↓reduceIte]
    have : m ≠ n := by omega
    simp [this]

/-- Derivative of X^n for n > 0. -/
theorem derivative_X_pow_of_pos {n : ℕ} (hn : 0 < n) :
    d⁄dX ((PowerSeries.X : R⟦X⟧) ^ n) = (n : R) • PowerSeries.X ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  simp only [derivative_X_pow_succ, Nat.succ_sub_one, Nat.cast_succ]

end Definition

/-!
## Theorem thm.fps.deriv.rules: Derivative Rules

We document the correspondence between the textbook theorems and Mathlib.
-/

section DerivativeRules

variable {R : Type*} [CommSemiring R]

/-!
### Part (a): Additivity

`(f + g)' = f' + g'`

This is automatic since `derivative` is a `Derivation`, hence an additive map.
-/

/-- **Theorem thm.fps.deriv.rules (a)**: Derivative is additive. -/
theorem derivative_add (f g : R⟦X⟧) : d⁄dX (f + g) = d⁄dX f + d⁄dX g :=
  map_add (d⁄dX) f g

/-- Derivative of negation: `(-f)' = -f'`. -/
@[simp]
theorem derivative_neg {R : Type*} [CommRing R] (f : R⟦X⟧) : d⁄dX (-f) = -d⁄dX f :=
  map_neg (d⁄dX) f

/-- Derivative of subtraction: `(f - g)' = f' - g'`. -/
@[simp]
theorem derivative_sub {R : Type*} [CommRing R] (f g : R⟦X⟧) :
    d⁄dX (f - g) = d⁄dX f - d⁄dX g :=
  map_sub (d⁄dX) f g

/-!
### Part (b): Summable Families

If `(fᵢ)_{i ∈ I}` is a summable family of FPSs, then `(∑ fᵢ)' = ∑ fᵢ'`.

We first state it for finite sums (which follows from additivity), then for
infinite summable families (where summability means that for each coefficient
index, only finitely many family members have nonzero coefficient).
-/

/-- **Theorem thm.fps.deriv.rules (b)** (finite version):
Derivative commutes with finite sums. -/
theorem derivative_sum {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧) :
    d⁄dX (∑ i ∈ s, f i) = ∑ i ∈ s, d⁄dX (f i) :=
  map_sum (d⁄dX) f s

-- Note: SummableFPS and summableFPSSum are imported from FPSDefinition.lean
-- The following uses the canonical definitions from that file.
-- These require [CommRing R] rather than [CommSemiring R]

variable {R' : Type*} [CommRing R']

/-- If (fᵢ) is a summable family, then (fᵢ') is also summable. -/
theorem summableFPS_derivative {ι : Type*} (f : ι → R'⟦X⟧) (hf : SummableFPS f) :
    SummableFPS (fun i => d⁄dX (f i)) := by
  intro n
  have h := hf (n + 1)
  apply Set.Finite.subset h
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi ⊢
  rw [PowerSeries.coeff_derivative] at hi
  intro hcontra
  apply hi
  rw [hcontra, zero_mul]

/-- **Theorem thm.fps.deriv.rules (b)** (infinite version):
Derivative commutes with infinite summable sums.

If (fᵢ)_{i ∈ I} is a summable family of FPSs, then (fᵢ')_{i ∈ I} is summable
and (∑ fᵢ)' = ∑ fᵢ'. -/
theorem derivative_summableFPSSum {ι : Type*} (f : ι → R'⟦X⟧) (hf : SummableFPS f) :
    d⁄dX (summableFPSSum f hf) =
      summableFPSSum (fun i => d⁄dX (f i)) (summableFPS_derivative f hf) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_derivative, coeff_summableFPSSum, coeff_summableFPSSum]
  -- Need: (∑ᶠ i, coeff (n + 1) (f i)) * (n + 1) = ∑ᶠ i, coeff n (d⁄dX R' (f i))
  -- coeff n (d⁄dX R' (f i)) = coeff (n + 1) (f i) * (n + 1)
  have heq : ∀ i, coeff n (d⁄dX (f i)) = coeff (n + 1) (f i) * (n + 1) := fun i =>
    PowerSeries.coeff_derivative (f i) n
  simp_rw [heq]
  -- Now need: (∑ᶠ i, coeff (n + 1) (f i)) * (n + 1) = ∑ᶠ i, coeff (n + 1) (f i) * (n + 1)
  have hsupport : (Function.support (fun i => coeff (n + 1) (f i))).Finite := hf (n + 1)
  rw [finsum_mul' _ _ hsupport]

/-!
### Part (c): Scalar Multiplication

`(c · f)' = c · f'`

This is automatic since `derivative` is an `R`-linear map.
-/

/-- **Theorem thm.fps.deriv.rules (c)**: Derivative commutes with scalar multiplication. -/
theorem derivative_smul (c : R) (f : R⟦X⟧) : d⁄dX (c • f) = c • d⁄dX f :=
  (d⁄dX).map_smul c f

/-- Variant with `C c * f` instead of `c • f`. -/
theorem derivative_C_mul (c : R) (f : R⟦X⟧) :
    d⁄dX (PowerSeries.C c * f) = PowerSeries.C c * d⁄dX f := by
  rw [← PowerSeries.smul_eq_C_mul, ← PowerSeries.smul_eq_C_mul, derivative_smul]

/-!
### Part (d): Leibniz Rule (Product Rule)

`(f · g)' = f' · g + f · g'`

This is the defining property of a derivation.
-/

/-- **Theorem thm.fps.deriv.rules (d)**: Leibniz rule for power series. -/
theorem derivative_mul (f g : R⟦X⟧) :
    d⁄dX (f * g) = d⁄dX f * g + f * d⁄dX g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

/-!
### Part (e): Quotient Rule

`(f / g)' = (f' · g - f · g') / g²` for invertible `g`.

In Mathlib, this is expressed using `PowerSeries.derivative_inv'` for fields,
or `PowerSeries.derivative_inv` for units.
-/

variable {K : Type*} [Field K]

/-- **Theorem thm.fps.deriv.rules (e)**: Quotient rule for power series.

Note: In Mathlib, this is stated as `(f⁻¹)' = -f⁻¹² · f'`.
The full quotient rule follows from combining this with Leibniz. -/
theorem derivative_div (f g : K⟦X⟧) (hg : constantCoeff g ≠ 0) :
    d⁄dX (f * g⁻¹) = (d⁄dX f * g - f * d⁄dX g) * g⁻¹ ^ 2 := by
  have hg_unit : g * g⁻¹ = 1 := g.mul_inv_cancel hg
  have hg_unit' : g⁻¹ * g = 1 := g.inv_mul_cancel hg
  rw [derivative_mul, derivative_inv']
  have h1 : d⁄dX f * g⁻¹ + f * (-(g⁻¹ ^ 2) * d⁄dX g)
          = d⁄dX f * g⁻¹ - f * g⁻¹ ^ 2 * d⁄dX g := by ring
  rw [h1]
  have h2 : d⁄dX f * g⁻¹ = d⁄dX f * g⁻¹ ^ 2 * g := by
    rw [sq, mul_assoc, mul_assoc, ← mul_assoc g⁻¹ g⁻¹ g]
    rw [mul_assoc g⁻¹, hg_unit', mul_one]
  rw [h2]
  ring

/-!
### Part (f): Power Rule

`(g^n)' = n · g^(n-1) · g'`

This is `PowerSeries.derivative_pow` in Mathlib.
-/

variable {A : Type*} [CommRing A]

/-- **Theorem thm.fps.deriv.rules (f)**: Power rule for power series. -/
theorem derivative_pow' (g : A⟦X⟧) (n : ℕ) :
    d⁄dX (g ^ n) = n * g ^ (n - 1) * d⁄dX g :=
  PowerSeries.derivative_pow g n

/-!
### Part (g): Chain Rule

`(f ∘ g)' = (f' ∘ g) · g'` when composition is defined.

In Mathlib, composition is `PowerSeries.subst`, and this is `PowerSeries.derivative_subst`.
The condition for substitution is that `g` has nilpotent constant term (which includes
the case when `[x⁰]g = 0`).
-/

/-- **Theorem thm.fps.deriv.rules (g)**: Chain rule for power series.

This holds when `g` has nilpotent constant coefficient (in particular when `[x⁰]g = 0`). -/
theorem derivative_comp (f g : A⟦X⟧) (hg : HasSubst g) :
    d⁄dX (f.subst g) = (d⁄dX f).subst g * d⁄dX g :=
  @PowerSeries.derivative_subst A _ f g hg

/-!
### Part (h): Uniqueness of Antiderivatives

If `f' = g'` and `K` is a ℚ-algebra, then `f - g` is constant.

In Mathlib, this is `PowerSeries.derivative.ext` (with the converse direction:
if derivatives and constant terms match, then the series are equal).
-/

/-- **Theorem thm.fps.deriv.rules (h)**: Two power series with equal derivatives
differ by a constant.

Note: Mathlib states this as: if `f' = g'` and `f₀ = g₀`, then `f = g`.
We state the equivalent: if `f' = g'`, then `f - g` has zero derivative,
hence is constant (all higher coefficients are zero). -/
theorem derivative_eq_imp_diff_const {R : Type*} [CommRing R] [IsAddTorsionFree R]
    {f g : R⟦X⟧} (h : d⁄dX f = d⁄dX g) :
    ∀ n : ℕ, n ≠ 0 → PowerSeries.coeff n (f - g) = 0 := by
  intro n hn
  have heq : PowerSeries.coeff (n - 1) (d⁄dX f) = PowerSeries.coeff (n - 1) (d⁄dX g) := by
    rw [h]
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at heq
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at heq
  rw [map_sub]
  rw [mul_comm, mul_comm (PowerSeries.coeff n g)] at heq
  cases n with
  | zero => exact absurd rfl hn
  | succ m =>
    simp only [Nat.add_sub_cancel] at heq
    rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul,
        smul_right_inj (Nat.succ_ne_zero m)] at heq
    exact sub_eq_zero.mpr heq

/-- Equivalent formulation: if two power series have equal derivatives and equal
constant terms, they are equal. This is `PowerSeries.derivative.ext` in Mathlib. -/
theorem eq_of_derivative_eq_of_constantCoeff_eq {R : Type*} [CommRing R] [IsAddTorsionFree R]
    {f g : R⟦X⟧} (hD : d⁄dX f = d⁄dX g) (hc : constantCoeff f = constantCoeff g) :
    f = g :=
  PowerSeries.derivative.ext hD hc

end DerivativeRules

/-!
## Additional Results

Some useful consequences and special cases.
-/

section Additional

variable {R : Type*} [CommSemiring R]

/-- Derivative of zero is zero. -/
@[simp]
theorem derivative_zero : d⁄dX (0 : R⟦X⟧) = 0 :=
  map_zero (d⁄dX)

/-- Derivative of a constant is zero. -/
@[simp]
theorem derivative_C (c : R) : d⁄dX (PowerSeries.C c) = 0 :=
  PowerSeries.derivative_C

/-- Derivative of X is 1. -/
@[simp]
theorem derivative_X : d⁄dX (X : R⟦X⟧) = 1 :=
  PowerSeries.derivative_X

/-- Derivative of 1 is 0. -/
@[simp]
theorem derivative_one : d⁄dX (1 : R⟦X⟧) = 0 :=
  Derivation.map_one_eq_zero (d⁄dX)

/-- The derivative of a polynomial viewed as a power series equals
the polynomial derivative viewed as a power series. -/
theorem derivative_coe_polynomial (p : R[X]) :
    d⁄dX (p : R⟦X⟧) = (Polynomial.derivative p : R⟦X⟧) :=
  PowerSeries.derivative_coe p

end Additional

end AlgebraicCombinatorics.FPS
