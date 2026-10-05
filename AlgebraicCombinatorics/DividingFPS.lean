/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# Dividing Formal Power Series

This file formalizes the content from `DividingFPS.tex`, covering:
- Inverses in commutative rings (uniqueness, notation)
- Characterization of invertible FPSs
- Newton's binomial formula for FPSs
- Upper negation formula for binomial coefficients
- Division by `x` for FPSs with vanishing constant term
- Various lemmas about coefficients and multiples

## Main Results

- `fps_invertible_iff_constantCoeff`: An FPS is invertible iff its constant term is invertible
- `fps_invertible_iff_constantCoeff_ne_zero`: Over a field, an FPS is invertible iff its
  constant term is nonzero
- `binomUpperNegation`: The upper negation formula `C(-n,k) = (-1)^k * C(k+n-1,k)`
- `fps_onePlusX_inv`: Formula for `(1+x)^{-1}` as a power series
- `fps_onePlusX_pow_neg`: Formula for `(1+x)^{-n}` for natural `n`
- `fps_newtonBinomial`: Newton's binomial formula `(1+x)^n = Σ C(n,k) x^k`
- `PowerSeries.divByX`: Division by `x` for FPSs with zero constant term
- Various lemmas about coefficients and multiples of FPSs

## References

* Grinberg, Darij. "Algebraic Combinatorics" (lecture notes)

## Tags

formal power series, inverses, binomial coefficients, Newton's binomial formula
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCombinatorics

/-! ### Section: Conventions

We identify each element `a ∈ K` with the constant FPS `(a, 0, 0, 0, ...)`.
In Mathlib, this is handled via the ring homomorphism `algebraMap K (PowerSeries K)`.
-/

variable {K : Type*} [CommRing K]

/-- The constant FPS corresponding to an element of the base ring.
This is `algebraMap K (PowerSeries K)` in Mathlib. -/
abbrev constFPS (a : K) : PowerSeries K := algebraMap K (PowerSeries K) a

/-! ### Section: Inverses in commutative rings

The uniqueness of inverses and notation for fractions are standard in Mathlib.
We recall the key facts here for reference.
-/

/-- **Theorem (thm.commring.inverse-uni)**: In a commutative ring, inverses are unique.
If `a * b = 1` and `a * c = 1`, then `b = c`.
This follows from Mathlib's `left_inv_eq_right_inv`. -/
theorem inverse_unique {L : Type*} [CommRing L] {a b c : L}
    (hb : a * b = 1) (hc : a * c = 1) : b = c := by
  have hb' : b * a = 1 := by rw [mul_comm]; exact hb
  exact left_inv_eq_right_inv hb' hc

/-- Variant of `inverse_unique`: if `a` is a unit, any element `b` with `a * b = 1`
equals the canonical inverse `ha.unit⁻¹`. -/
theorem inverse_unique_of_isUnit {L : Type*} [CommRing L] {a : L} (ha : IsUnit a)
    {b : L} (hb : a * b = 1) : b = ha.unit⁻¹ := by
  have : a * ↑ha.unit⁻¹ = 1 := IsUnit.mul_val_inv ha
  exact inverse_unique hb this

/-! ### Section: Properties of inverses and fractions (prop.commring.fracs.1)

**Proposition (prop.commring.fracs.1)**: Let `L` be a commutative ring. Then:
- **(a)** Any invertible element `a ∈ L` satisfies `a⁻¹ = 1/a`.
- **(b)** For any invertible elements `a, b ∈ L`, the element `ab` is invertible as well,
  and satisfies `(ab)⁻¹ = b⁻¹a⁻¹ = a⁻¹b⁻¹`.
- **(c)** If `a ∈ L` is invertible, and if `n ∈ ℤ` is arbitrary, then `a^{-n} = (a⁻¹)^n = (a^n)⁻¹`.
- **(d)** Laws of exponents hold for negative exponents as well.
- **(e)** Laws of fractions hold: `b/a + d/c = (bc + ad)/(ac)` and `(b/a) · (d/c) = (bd)/(ac)`.
- **(f)** Division undoes multiplication: `c/a = b` iff `c = ab`.

In Mathlib, these are mostly standard lemmas for `Units` and `IsUnit`.
-/

section PropCommringFracs1

variable {L : Type*} [CommRing L]

/-- **Proposition (prop.commring.fracs.1a)**: For an invertible element `a`,
    the inverse `a⁻¹` equals `1/a` (i.e., `1 * a⁻¹`).
    This is essentially definitional in Mathlib. -/
theorem fracs1_inv_eq_one_mul_inv (u : Lˣ) : (u⁻¹ : Lˣ) = 1 * u⁻¹ := by
  simp

/-- **Proposition (prop.commring.fracs.1b)**: If `a` and `b` are invertible,
    then `a * b` is invertible. -/
theorem fracs1_isUnit_mul {a b : L} (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a * b) :=
  ha.mul hb

/-- **Proposition (prop.commring.fracs.1b)**: `(a * b)⁻¹ = b⁻¹ * a⁻¹` for units. -/
theorem fracs1_mul_inv_rev (u v : Lˣ) : (u * v)⁻¹ = v⁻¹ * u⁻¹ :=
  mul_inv_rev u v

/-- **Proposition (prop.commring.fracs.1b)**: In a commutative ring,
    `(a * b)⁻¹ = a⁻¹ * b⁻¹` for units. -/
theorem fracs1_mul_inv_comm (u v : Lˣ) : (u * v)⁻¹ = u⁻¹ * v⁻¹ := by
  rw [mul_inv_rev, mul_comm]

/-- **Proposition (prop.commring.fracs.1c)**: For a unit `u` and integer `n`,
    `u^{-n} = (u⁻¹)^n`. -/
theorem fracs1_zpow_neg_eq_inv_zpow (u : Lˣ) (n : ℤ) : u ^ (-n) = u⁻¹ ^ n := by
  rw [zpow_neg, inv_zpow]

/-- **Proposition (prop.commring.fracs.1c)**: For a unit `u` and integer `n`,
    `u^{-n} = (u^n)⁻¹`. -/
theorem fracs1_zpow_neg_eq_zpow_inv (u : Lˣ) (n : ℤ) : u ^ (-n) = (u ^ n)⁻¹ :=
  zpow_neg u n

/-- **Proposition (prop.commring.fracs.1d)**: `a^{n+m} = a^n * a^m` for all integers `n, m`. -/
theorem fracs1_zpow_add (u : Lˣ) (n m : ℤ) : u ^ (n + m) = u ^ n * u ^ m :=
  zpow_add u n m

/-- **Proposition (prop.commring.fracs.1d)**: `(a * b)^n = a^n * b^n` for all integers `n`. -/
theorem fracs1_mul_zpow (u v : Lˣ) (n : ℤ) : (u * v) ^ n = u ^ n * v ^ n :=
  mul_zpow u v n

/-- **Proposition (prop.commring.fracs.1d)**: `(a^n)^m = a^{nm}` for all integers `n, m`. -/
theorem fracs1_zpow_mul (u : Lˣ) (n m : ℤ) : (u ^ n) ^ m = u ^ (n * m) :=
  (zpow_mul u n m).symm

/-- Division notation for units: `b / a` means `b * a⁻¹`.
    This formalizes the notation `b/a` for `a` invertible in the text. -/
def divByUnit (b : L) (a : Lˣ) : L := b * (a⁻¹ : Lˣ)

/-- Local notation for division by a unit. -/
scoped notation:70 b " /ᵤ " a => divByUnit b a

/-- **Proposition (prop.commring.fracs.1e)**: `b/a + d/c = (bc + ad)/(ac)`. -/
theorem fracs1_div_add_div (a c : Lˣ) (b d : L) :
    (b /ᵤ a) + (d /ᵤ c) = (b * (c : L) + (a : L) * d) /ᵤ (a * c) := by
  unfold divByUnit
  simp only [Units.val_mul, mul_inv_rev]
  have ha : (↑a⁻¹ : L) * (↑a : L) = 1 := by simp
  have hc : (↑c⁻¹ : L) * (↑c : L) = 1 := by simp
  have hcomm : (↑a⁻¹ : L) * (↑c⁻¹ : L) = (↑c⁻¹ : L) * (↑a⁻¹ : L) := by ring
  calc b * ↑a⁻¹ + d * ↑c⁻¹
      = b * ↑a⁻¹ * (↑c⁻¹ * ↑c) + (↑a⁻¹ * ↑a) * d * ↑c⁻¹ := by rw [ha, hc]; ring
    _ = b * (↑a⁻¹ * ↑c⁻¹) * ↑c + ↑a * d * (↑a⁻¹ * ↑c⁻¹) := by ring
    _ = (b * ↑c + ↑a * d) * (↑a⁻¹ * ↑c⁻¹) := by ring
    _ = (b * ↑c + ↑a * d) * (↑c⁻¹ * ↑a⁻¹) := by rw [hcomm]

/-- **Proposition (prop.commring.fracs.1e)**: `(b/a) * (d/c) = (bd)/(ac)`. -/
theorem fracs1_div_mul_div (a c : Lˣ) (b d : L) :
    (b /ᵤ a) * (d /ᵤ c) = (b * d) /ᵤ (a * c) := by
  unfold divByUnit
  simp only [Units.val_mul, mul_inv_rev]
  ring

/-- **Proposition (prop.commring.fracs.1f)**: `c/a = b` iff `c = a * b`. -/
theorem fracs1_div_eq_iff (a : Lˣ) (b c : L) :
    (c /ᵤ a) = b ↔ c = (a : L) * b := by
  unfold divByUnit
  constructor
  · intro h
    calc c = c * (↑a⁻¹ * ↑a) := by simp
         _ = (c * ↑a⁻¹) * ↑a := by ring
         _ = b * ↑a := by rw [h]
         _ = ↑a * b := by ring
  · intro h
    rw [h]
    have : (↑a : L) * (↑a⁻¹ : L) = 1 := by simp
    calc ↑a * b * ↑a⁻¹ = b * (↑a * ↑a⁻¹) := by ring
                     _ = b * 1 := by rw [this]
                     _ = b := by ring

end PropCommringFracs1

/-! ### Section: Inverses in K[[x]]

**Proposition (prop.fps.invertible)**: An FPS `a` is invertible in `K[[x]]` if and only if
its constant term `[x^0] a` is invertible in `K`.

This is `PowerSeries.isUnit_iff_constantCoeff` in Mathlib.
-/

/-- An FPS is invertible iff its constant term is invertible.
  Label: prop.fps.invertible -/
theorem fps_invertible_iff_constantCoeff (a : PowerSeries K) :
    IsUnit a ↔ IsUnit (a.constantCoeff) :=
  PowerSeries.isUnit_iff_constantCoeff

/-- **Corollary (cor.fps.invertible.field)**: Over a field, an FPS is invertible
iff its constant term is nonzero.
Label: cor.fps.invertible.field -/
theorem fps_invertible_iff_constantCoeff_ne_zero {F : Type*} [Field F] (a : PowerSeries F) :
    IsUnit a ↔ a.constantCoeff ≠ 0 := by
  rw [fps_invertible_iff_constantCoeff]
  exact isUnit_iff_ne_zero

/-! ### Section: Coefficient formulas for inverses

Explicit formulas for the coefficients of the inverse of an FPS.
-/

/-- The constant term of the inverse of an FPS equals the inverse of its constant term.
This is a direct corollary of Mathlib's `PowerSeries.constantCoeff_inv`.
Label: fps_inv_coeff_zero -/
theorem fps_inv_coeff_zero {F : Type*} [Field F] (f : PowerSeries F) :
    PowerSeries.coeff 0 f⁻¹ = (PowerSeries.coeff 0 f)⁻¹ := by
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_inv]

/-- Recurrence for coefficients of the inverse of an FPS.
For n > 0: `[x^n]f⁻¹ = -(f₀)⁻¹ · ∑_{k=1}^n f_k · [x^{n-k}]f⁻¹`

This is a reformulation of Mathlib's `PowerSeries.coeff_inv` that expresses the
recurrence in terms of a sum over `Finset.range (n + 1)` with shifted indices,
which matches the standard textbook formula.

The recurrence shows that each coefficient of `f⁻¹` can be computed from:
- The constant term `f₀` (which must be nonzero for `f` to be invertible)
- The coefficients `f₁, f₂, ..., f_n` of `f`
- The previously computed coefficients `[x^0]f⁻¹, [x^1]f⁻¹, ..., [x^{n-1}]f⁻¹`

Label: fps_inv_coeff_succ -/
theorem fps_inv_coeff_succ {F : Type*} [Field F] (f : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff (n + 1) f⁻¹ =
      -(PowerSeries.coeff 0 f)⁻¹ *
        ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff (k + 1) f *
          PowerSeries.coeff (n - k) f⁻¹ := by
  -- Use Mathlib's coeff_inv
  rw [PowerSeries.coeff_inv]
  simp only [Nat.succ_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_eq_constantCoeff]
  -- Need to show the sums are equal
  congr 1
  -- Use the antidiagonal to range conversion
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
    if j < n + 1 then PowerSeries.coeff i f * PowerSeries.coeff j f⁻¹ else 0) (n + 1)]
  -- Split off k=0 term (which is 0) and reindex the rest
  have h0 : (0 : ℕ) ∈ Finset.range (n + 2) := Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_erase_add _ _ h0]
  simp only [Nat.sub_zero]
  -- The k=0 term: if n+1 < n+1 then ... else 0 = 0
  have h0_eq : (if n + 1 < n + 1 then PowerSeries.coeff 0 f * PowerSeries.coeff (n + 1) f⁻¹
      else 0) = 0 := by simp
  rw [h0_eq, add_zero]
  have herase : (Finset.range (n + 2)).erase 0 = Finset.Icc 1 (n + 1) := by
    ext x
    simp only [Finset.mem_erase, ne_eq, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [herase]
  -- Icc 1 (n+1) = image (· + 1) (range (n+1))
  have hIcc : Finset.Icc 1 (n + 1) = Finset.image (· + 1) (Finset.range (n + 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨h1, h2⟩
      use x - 1
      omega
    · intro ⟨y, hy, hxy⟩
      omega
  rw [hIcc, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    have hcond : n + 1 - (k + 1) < n + 1 := by omega
    simp only [hcond, ↓reduceIte]
    have hsub : n + 1 - (k + 1) = n - k := by omega
    rw [hsub]
  · intro x _ y _ hxy
    exact Nat.succ_injective hxy

/-- Helper lemma: For an invertible FPS `f`, the unit inverse `hf.unit⁻¹` equals `f⁻¹`.
This connects the `IsUnit` formulation with the direct inverse. -/
lemma fps_isUnit_inv_eq_inv {F : Type*} [Field F] (f : PowerSeries F) (hf : IsUnit f) :
    (↑hf.unit⁻¹ : PowerSeries F) = f⁻¹ := by
  have hfeq : (↑hf.unit : PowerSeries F) = f := IsUnit.unit_spec hf
  have hne : PowerSeries.constantCoeff f ≠ 0 := by
    rw [PowerSeries.isUnit_iff_constantCoeff] at hf
    exact isUnit_iff_ne_zero.mp hf
  have hmul : f * ↑hf.unit⁻¹ = 1 := by
    calc f * ↑hf.unit⁻¹ = ↑hf.unit * ↑hf.unit⁻¹ := by rw [hfeq]
         _ = ↑(hf.unit * hf.unit⁻¹) := by rfl
         _ = ↑(1 : (PowerSeries F)ˣ) := by rw [mul_inv_cancel]
         _ = 1 := by rfl
  symm
  rw [PowerSeries.inv_eq_iff_mul_eq_one hne, mul_comm]
  exact hmul

/-- The constant term of the inverse of an invertible FPS equals the inverse of its constant term.
This is the `IsUnit` version of `fps_inv_coeff_zero`.
Label: fps_inv_coeff_zero_isUnit -/
theorem fps_inv_coeff_zero_isUnit {F : Type*} [Field F] (f : PowerSeries F) (hf : IsUnit f) :
    PowerSeries.coeff 0 (↑hf.unit⁻¹ : PowerSeries F) = (PowerSeries.coeff 0 f)⁻¹ := by
  rw [fps_isUnit_inv_eq_inv f hf, fps_inv_coeff_zero]

/-- Recurrence for coefficients of the inverse of an invertible FPS.
This is the `IsUnit` version of `fps_inv_coeff_succ`.
Label: fps_inv_coeff_succ_isUnit -/
theorem fps_inv_coeff_succ_isUnit {F : Type*} [Field F] (f : PowerSeries F) (hf : IsUnit f) (n : ℕ) :
    PowerSeries.coeff (n + 1) (↑hf.unit⁻¹ : PowerSeries F) =
      -(PowerSeries.coeff 0 f)⁻¹ *
        ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff (k + 1) f *
          PowerSeries.coeff (n - k) (↑hf.unit⁻¹ : PowerSeries F) := by
  simp only [fps_isUnit_inv_eq_inv f hf, fps_inv_coeff_succ]

/-! ### Section: Newton's binomial formula

We prove Newton's binomial formula: `(1+x)^n = Σ_{k ∈ ℕ} C(n,k) x^k` for all `n ∈ ℤ`.
-/

/-- **Proposition (prop.fps.invertible.1+x)**: The FPS `1+x` is invertible, with inverse
`1 - x + x^2 - x^3 + ...`.
Label: prop.fps.invertible.1+x -/
theorem fps_onePlusX_isUnit : IsUnit (1 + PowerSeries.X : PowerSeries K) := by
  rw [fps_invertible_iff_constantCoeff]
  simp [PowerSeries.constantCoeff_X]

/-- The inverse of `1+x` is `Σ_{n ∈ ℕ} (-1)^n x^n`.
Note: This requires `K` to be a field to have `Inv` instance on `PowerSeries K`.
Label: prop.fps.invertible.1+x -/
theorem fps_onePlusX_inv {F : Type*} [Field F] :
    (1 + PowerSeries.X : PowerSeries F)⁻¹ = PowerSeries.mk fun n => (-1 : F) ^ n := by
  -- (1 - X)⁻¹ = mk 1 (the power series with all coefficients 1)
  have h1 : (1 - PowerSeries.X : PowerSeries F)⁻¹ = PowerSeries.mk 1 := by
    have hc : PowerSeries.constantCoeff (1 - PowerSeries.X : PowerSeries F) ≠ 0 := by simp
    symm
    rw [PowerSeries.eq_inv_iff_mul_eq_one hc]
    exact PowerSeries.mk_one_mul_one_sub_eq_one F
  -- rescale (-1) maps (1 - X) to (1 + X)
  have h2 : PowerSeries.rescale (-1 : F) (1 - PowerSeries.X : PowerSeries F) = 1 + PowerSeries.X := by
    ext n
    simp only [PowerSeries.coeff_rescale, map_sub, map_one, PowerSeries.coeff_one]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, PowerSeries.coeff_X]
      split_ifs with h
      · simp [h]
      · have hn : n ≠ 0 := by omega
        simp [PowerSeries.coeff_X, hn]
  -- rescale preserves inverses (as a ring homomorphism)
  have h3 : PowerSeries.rescale (-1 : F) ((1 - PowerSeries.X : PowerSeries F)⁻¹) =
      (PowerSeries.rescale (-1 : F) (1 - PowerSeries.X))⁻¹ := by
    have hc : PowerSeries.constantCoeff (1 - PowerSeries.X : PowerSeries F) ≠ 0 := by simp
    have hc' : PowerSeries.constantCoeff (PowerSeries.rescale (-1 : F) (1 - PowerSeries.X)) ≠ 0 := by
      rw [h2]; simp
    symm
    rw [PowerSeries.inv_eq_iff_mul_eq_one hc', ← (PowerSeries.rescale (-1 : F)).map_mul,
        PowerSeries.inv_mul_cancel _ hc]
    simp
  -- Combine: (1+X)⁻¹ = rescale(-1)((1-X)⁻¹) = rescale(-1)(mk 1) = mk ((-1)^n)
  rw [← h2, ← h3, h1]
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_mk, Pi.one_apply, mul_one]

/-- **Theorem (thm.binom.upneg-n)**: Upper negation formula for binomial coefficients.
For `r` in a BinomialRing `R` and `k ∈ ℕ`, we have `C(-r, k) = (-1)^k * C(r+k-1, k)`.

Note: In Mathlib, generalized binomial coefficients are defined via `Ring.choose`
for `BinomialRing`s. This generalizes the classical formula for `n ∈ ℂ`.
Label: thm.binom.upneg-n -/
theorem binomUpperNegation {R : Type*} [CommRing R] [BinomialRing R] [NatPowAssoc R]
    (r : R) (k : ℕ) :
    Ring.choose (-r) k = (-1 : R) ^ k * Ring.choose (r + k - 1) k := by
  rw [Ring.choose_neg]
  simp only [Int.negOnePow_def, zpow_natCast, Units.smul_def, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one]
  ring

/-- Specialization of `binomUpperNegation` to integers.
For `n ∈ ℤ` and `k ∈ ℕ`, we have `C(-n, k) = (-1)^k * C(k+n-1, k)`.
Label: thm.binom.upneg-n -/
theorem binomUpperNegation_int (n : ℤ) (k : ℕ) :
    Ring.choose (-n) k = (-1 : ℤ) ^ k * Ring.choose (k + n - 1) k := by
  have := binomUpperNegation (R := ℤ) n k
  convert this using 2
  ring_nf

/-- **Proposition (prop.fps.anti-newton-binom)**: For each `n ∈ ℕ`, we have
`(1+x)^{-n} = Σ_{k ∈ ℕ} (-1)^k * C(n+k-1, k) * x^k`.

Note: We express this using the inverse since PowerSeries over a general ring
doesn't have integer power operations.
Label: prop.fps.anti-newton-binom -/
theorem fps_onePlusX_pow_neg {F : Type*} [Field F] [BinomialRing F] (n : ℕ) :
    ((1 + PowerSeries.X : PowerSeries F)⁻¹) ^ n =
      PowerSeries.mk fun k => (-1 : F) ^ k * Ring.choose ((n : ℤ) + k - 1) k := by
  -- Step 1: Show (1+X)^{-1} = binomialSeries F (-1)
  have h_base : (1 + PowerSeries.X : PowerSeries F)⁻¹ = PowerSeries.binomialSeries F (-1 : ℤ) := by
    -- Use rescale relationship: rescale (-1) transforms (1-X) to (1+X)
    have h1 : PowerSeries.rescale (-1 : F) (1 - PowerSeries.X : PowerSeries F) = 1 + PowerSeries.X := by
      ext n
      simp only [PowerSeries.coeff_rescale, map_sub, map_one, PowerSeries.coeff_one]
      cases n with
      | zero => simp
      | succ n =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, PowerSeries.coeff_X]
        split_ifs with h
        · simp [h]
        · have : n ≠ 0 := by omega
          simp [PowerSeries.coeff_X, this]
    have h2 : PowerSeries.rescale (-1 : F) (PowerSeries.invOneSubPow F 1).val =
        PowerSeries.binomialSeries F (-1 : ℤ) := PowerSeries.rescale_neg_one_invOneSubPow 1
    have h3 : (PowerSeries.invOneSubPow F 1).val = (1 - PowerSeries.X : PowerSeries F)⁻¹ := by
      rw [PowerSeries.invOneSubPow_eq_inv_one_sub_pow]
      simp only [pow_one]
      have hunit : IsUnit (1 - PowerSeries.X : PowerSeries F) := by
        rw [PowerSeries.isUnit_iff_constantCoeff]
        simp
      have hc : (1 - PowerSeries.X : PowerSeries F).constantCoeff ≠ 0 := by
        rwa [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero] at hunit
      rw [MvPowerSeries.eq_inv_iff_mul_eq_one hc]
      rw [mul_comm]
      exact (Units.mkOfMulEqOne (1 - PowerSeries.X) (PowerSeries.mk 1)
        (Eq.trans (mul_comm _ _) (PowerSeries.mk_one_mul_one_sub_eq_one F))).val_inv
    rw [← h2, h3]
    have h4 : IsUnit (1 - PowerSeries.X : PowerSeries F) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp
    -- Show rescale preserves inverses
    have h5 : PowerSeries.rescale (-1 : F) ((1 - PowerSeries.X : PowerSeries F)⁻¹) =
        (PowerSeries.rescale (-1 : F) (1 - PowerSeries.X))⁻¹ := by
      have hf' : IsUnit (PowerSeries.rescale (-1 : F) (1 - PowerSeries.X)) := by
        rw [PowerSeries.isUnit_iff_constantCoeff] at h4 ⊢
        convert h4 using 1
        rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale, pow_zero, one_mul,
          PowerSeries.coeff_zero_eq_constantCoeff]
      have hfc : (1 - PowerSeries.X : PowerSeries F).constantCoeff ≠ 0 := by
        rwa [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero] at h4
      have hfc' : (PowerSeries.rescale (-1 : F) (1 - PowerSeries.X)).constantCoeff ≠ 0 := by
        rwa [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero] at hf'
      have h : PowerSeries.rescale (-1 : F) (1 - PowerSeries.X) *
          PowerSeries.rescale (-1 : F) ((1 - PowerSeries.X)⁻¹) = 1 := by
        rw [← map_mul]
        have : (1 - PowerSeries.X) * (1 - PowerSeries.X : PowerSeries F)⁻¹ = 1 := by
          rw [mul_comm]
          exact MvPowerSeries.inv_mul_cancel _ hfc
        rw [this]
        simp
      rw [MvPowerSeries.eq_inv_iff_mul_eq_one hfc']
      rw [mul_comm]
      exact h
    rw [h5, h1]
  -- Step 2: Show ((1+X)^{-1})^n = binomialSeries F (-n) by induction
  have h_pow : ((1 + PowerSeries.X : PowerSeries F)⁻¹) ^ n =
      PowerSeries.binomialSeries F (-(n : ℤ)) := by
    induction n with
    | zero =>
      simp [PowerSeries.binomialSeries_zero]
    | succ n ih =>
      rw [pow_succ, ih, h_base]
      rw [← PowerSeries.binomialSeries_add]
      congr 1
      omega
  -- Step 3: Convert binomialSeries F (-n) to the explicit formula using Ring.choose_neg
  rw [h_pow]
  ext k
  simp only [PowerSeries.binomialSeries_coeff, PowerSeries.coeff_mk]
  rw [Ring.choose_neg]
  simp only [Int.smul_one_eq_cast]
  have h1 : ((Int.negOnePow k) • Ring.choose ((n : ℤ) + k - 1) k : ℤ) =
      Int.negOnePow k * Ring.choose ((n : ℤ) + k - 1) k := zsmul_eq_mul _ _
  rw [h1]
  push_cast
  congr 1
  simp [Int.negOnePow]

/-- **Corollary (cor.fps.anti-newton-binom-2)**: For each `n ∈ ℕ`, we have
`(1+x)^{-n} = Σ_{k ∈ ℕ} C(-n, k) * x^k`.
Label: cor.fps.anti-newton-binom-2 -/
theorem fps_onePlusX_pow_neg' {F : Type*} [Field F] [BinomialRing F] (n : ℕ) :
    ((1 + PowerSeries.X : PowerSeries F)⁻¹) ^ n =
      PowerSeries.mk fun k => (Ring.choose (-(n : ℤ)) k : F) := by
  -- First, note that (Ring.choose (-(n : ℤ)) k : F) means Ring.choose computed in F
  -- with argument -(n : F)
  -- The RHS equals binomialSeries F (-(n : ℤ))
  have h_coeff : PowerSeries.binomialSeries F (-(n : ℤ)) =
      PowerSeries.mk fun k => (Ring.choose (-(n : ℤ)) k : F) := by
    ext k
    simp only [PowerSeries.binomialSeries_coeff, PowerSeries.coeff_mk]
    -- LHS: (Ring.choose (-(n : ℤ)) k : ℤ) • (1 : F)
    -- RHS: Ring.choose (-(n : F)) k
    rw [zsmul_one]
    -- Use map_choose to relate Ring.choose in ℤ to Ring.choose in F
    have h := Ring.map_choose (algebraMap ℤ F) (-(n : ℤ)) k
    simp only [map_neg, map_natCast] at h
    convert h using 2
    all_goals simp
  -- binomialSeries F (n : ℤ) = (1 + X)^n
  have h_nat : PowerSeries.binomialSeries F (n : ℤ) =
      (1 + PowerSeries.X : PowerSeries F) ^ n :=
    PowerSeries.binomialSeries_nat (R := ℤ) (A := F) n
  -- binomialSeries satisfies: binomialSeries n * binomialSeries (-n) = 1
  have h_mul : PowerSeries.binomialSeries F (n : ℤ) *
      PowerSeries.binomialSeries F (-(n : ℤ)) = 1 := by
    rw [← PowerSeries.binomialSeries_add]
    simp
  -- So (1+X)^n * binomialSeries F (-(n : ℤ)) = 1
  rw [h_nat] at h_mul
  -- This means binomialSeries F (-(n : ℤ)) = ((1+X)^n)⁻¹
  have h_const : PowerSeries.constantCoeff ((1 + PowerSeries.X : PowerSeries F) ^ n) ≠ 0 := by
    simp [PowerSeries.constantCoeff_X]
  have h_inv : PowerSeries.binomialSeries F (-(n : ℤ)) =
      ((1 + PowerSeries.X : PowerSeries F) ^ n)⁻¹ := by
    symm
    rw [PowerSeries.inv_eq_iff_mul_eq_one h_const, mul_comm]
    exact h_mul
  -- And ((1+X)^n)⁻¹ = ((1+X)⁻¹)^n
  have h_inv_pow : ((1 + PowerSeries.X : PowerSeries F) ^ n)⁻¹ =
      ((1 + PowerSeries.X : PowerSeries F)⁻¹) ^ n := by
    have h_const' : PowerSeries.constantCoeff (1 + PowerSeries.X : PowerSeries F) ≠ 0 := by
      simp [PowerSeries.constantCoeff_X]
    rw [PowerSeries.inv_eq_iff_mul_eq_one h_const, ← mul_pow]
    have h_inv_mul : (1 + PowerSeries.X : PowerSeries F)⁻¹ * (1 + PowerSeries.X) = 1 :=
      PowerSeries.inv_mul_cancel (1 + PowerSeries.X) h_const'
    rw [h_inv_mul]
    simp
  rw [← h_coeff, h_inv, h_inv_pow]

/-- Helper lemma: coefficient of a natural number cast to PowerSeries. -/
private lemma coeff_natCast_fps {R : Type*} [CommRing R] (k j : ℕ) :
    (PowerSeries.coeff k) (↑j : PowerSeries R) = if k = 0 then j else 0 := by
  have natcast_eq_smul : (↑j : PowerSeries R) = (j : R) • 1 := by
    induction j with
    | zero => simp
    | succ j ih => simp [ih, add_smul]
  rw [natcast_eq_smul]
  simp only [PowerSeries.coeff_smul, PowerSeries.coeff_one]
  split_ifs with hk <;> simp

/-- **Theorem (thm.fps.newton-binom)**: Newton's binomial formula.
For each `n ∈ ℕ`, we have `(1+x)^n = Σ_{k ∈ ℕ} C(n,k) x^k`.

Note: For non-negative integers, this follows from the standard binomial theorem.
Label: thm.fps.newton-binom -/
theorem fps_newtonBinomial_nat {R : Type*} [CommRing R] (n : ℕ) :
    (1 + PowerSeries.X : PowerSeries R) ^ n =
      PowerSeries.mk fun k => if k ≤ n then (n.choose k : R) else 0 := by
  ext m
  simp only [PowerSeries.coeff_mk]
  rw [add_pow]
  simp only [one_pow, one_mul]
  rw [map_sum]
  conv_lhs =>
    arg 2
    ext x
    rw [PowerSeries.coeff_X_pow_mul']
  simp_rw [coeff_natCast_fps]
  simp only [Nat.cast_ite, Nat.cast_zero]
  by_cases hm : m ≤ n
  · -- Case m ≤ n: sum has one nonzero term at x = n - m
    simp only [hm, ↓reduceIte]
    rw [Finset.sum_eq_single (n - m)]
    · -- Main term
      simp only [Nat.sub_sub_self hm, le_refl, ↓reduceIte, Nat.sub_self]
      rw [Nat.choose_symm hm]
    · -- Other terms are zero
      intro x hx_mem hx
      by_cases h : n - x ≤ m
      · simp only [h, ↓reduceIte]
        by_cases h2 : m - (n - x) = 0
        · exfalso
          have heq : n - x = m := by omega
          have hx' : x ≤ n := by
            simp [Finset.mem_range] at hx_mem
            omega
          have : x = n - m := by omega
          exact hx this
        · simp [h2]
      · simp [h]
    · -- x = n - m is in range
      intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · -- Case m > n: all terms are zero
    simp only [hm, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro x hx
    simp [Finset.mem_range] at hx
    simp only [Nat.sub_le_iff_le_add]
    have : m - (n - x) ≠ 0 := by omega
    simp [this]

/-- Newton's binomial formula for negative integer exponents over a field.
The inverse of `(1+x)^n` equals `Σ C(-n,k) x^k`.
Label: thm.fps.newton-binom -/
theorem fps_newtonBinomial_neg {F : Type*} [Field F] [BinomialRing F] (n : ℕ) :
    ((1 + PowerSeries.X : PowerSeries F)⁻¹) ^ n =
      PowerSeries.mk fun k => (Ring.choose (-(n : ℤ)) k : F) :=
  fps_onePlusX_pow_neg' n

/-! ### Section: Dividing by x

**Definition (def.fps.div-by-x)**: For an FPS `a = (a_0, a_1, a_2, ...)` with `a_0 = 0`,
we define `a/x` to be the FPS `(a_1, a_2, a_3, ...)`.
-/

/-- Division of an FPS by `x`, defined when the constant term is zero.
Given `a = (a_0, a_1, a_2, ...)` with `a_0 = 0`, returns `(a_1, a_2, a_3, ...)`.
Label: def.fps.div-by-x -/
def PowerSeries.divByX (a : PowerSeries K) (_ : a.constantCoeff = 0) : PowerSeries K :=
  PowerSeries.mk fun n => a.coeff (n + 1)

/-- The coefficient of `x^n` in `a/x` is the coefficient of `x^{n+1}` in `a`. -/
@[simp]
theorem PowerSeries.coeff_divByX (a : PowerSeries K) (ha : a.constantCoeff = 0) (n : ℕ) :
    (PowerSeries.divByX a ha).coeff n = a.coeff (n + 1) := by
  simp [PowerSeries.divByX]

/-- **Proposition (prop.fps.div-by-x-inverts)**: `a = x * b` iff
`a` has zero constant term and `b = a/x`.
Label: prop.fps.div-by-x-inverts -/
theorem fps_eq_X_mul_iff (a b : PowerSeries K) :
    a = PowerSeries.X * b ↔ (a.constantCoeff = 0 ∧
      ∃ h : a.constantCoeff = 0, b = PowerSeries.divByX a h) := by
  constructor
  · intro heq
    constructor
    · simp [heq, PowerSeries.constantCoeff_X]
    · have hconst : a.constantCoeff = 0 := by simp [heq, PowerSeries.constantCoeff_X]
      use hconst
      ext n
      rw [PowerSeries.coeff_divByX]
      rw [heq]
      simp [PowerSeries.coeff_succ_X_mul]
  · intro ⟨hconst, h, heq⟩
    rw [heq]
    ext n
    cases n with
    | zero =>
      simp only [PowerSeries.coeff_zero_eq_constantCoeff, hconst]
      simp [PowerSeries.constantCoeff_X]
    | succ n =>
      simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_divByX]

/-- `X * b` has zero constant term.
Label: prop.fps.div-by-x-inverts (helper) -/
@[simp]
theorem fps_X_mul_constantCoeff_zero (b : PowerSeries K) :
    (PowerSeries.X * b).constantCoeff = 0 := by
  simp [PowerSeries.constantCoeff_X]

/-- If `a.constantCoeff = 0`, then `a = X * (a/x)`.
Label: prop.fps.div-by-x-inverts (helper) -/
theorem fps_eq_X_mul_divByX (a : PowerSeries K) (ha : a.constantCoeff = 0) :
    a = PowerSeries.X * PowerSeries.divByX a ha := by
  rw [fps_eq_X_mul_iff]
  exact ⟨ha, ha, rfl⟩

/-- `(X * b) / X = b`.
Label: prop.fps.div-by-x-inverts (helper) -/
theorem fps_divByX_X_mul (b : PowerSeries K) :
    PowerSeries.divByX (PowerSeries.X * b) (fps_X_mul_constantCoeff_zero b) = b := by
  ext n
  rw [PowerSeries.coeff_divByX, PowerSeries.coeff_succ_X_mul]

/-- **Lemma (lem.fps.g=xh)**: If an FPS `a` has zero constant term, then
there exists an FPS `h` such that `a = x * h`.
Label: lem.fps.g=xh -/
theorem fps_exists_X_mul_of_constantCoeff_zero (a : PowerSeries K) (ha : a.constantCoeff = 0) :
    ∃ h : PowerSeries K, a = PowerSeries.X * h := by
  refine ⟨PowerSeries.divByX a ha, ?_⟩
  ext n
  cases n with
  | zero =>
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, ha]
    simp
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_divByX]

/-! ### Section: A few lemmas

Various lemmas about coefficients and multiples of FPSs.
-/

/-- **Lemma (lem.fps.first-n-coeffs-of-xna)**: The first `k` coefficients of `x^k * a` are zero.
Label: lem.fps.first-n-coeffs-of-xna -/
theorem fps_coeff_X_pow_mul_eq_zero (k : ℕ) (a : PowerSeries K) (m : ℕ) (hm : m < k) :
    (PowerSeries.X ^ k * a).coeff m = 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hm]

/-- **Lemma (lem.fps.muls-of-xn)**: The first `k` coefficients of `f` are zero iff
`f` is a multiple of `x^k`.
Label: lem.fps.muls-of-xn -/
theorem fps_first_k_coeffs_zero_iff_X_pow_dvd (k : ℕ) (f : PowerSeries K) :
    (∀ m < k, f.coeff m = 0) ↔ PowerSeries.X ^ k ∣ f := by
  exact PowerSeries.X_pow_dvd_iff.symm

/-- A multiple of `g` is an FPS of the form `g * a`. -/
def PowerSeries.isMultipleOf (f g : PowerSeries K) : Prop := g ∣ f

/-- **Lemma (lem.fps.prod.irlv.fg)**: If the first `n+1` coefficients of `f` and `g` agree,
then the first `n+1` coefficients of `a*f` and `a*g` agree.
Label: lem.fps.prod.irlv.fg -/
theorem fps_coeff_mul_eq_of_coeff_eq (a f g : PowerSeries K) (n : ℕ)
    (h : ∀ m ≤ n, f.coeff m = g.coeff m) :
    ∀ m ≤ n, (a * f).coeff m = (a * g).coeff m := by
  intro m hm
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ⟨i, j⟩ hij
  -- For (i, j) in antidiagonal m, we have i + j = m
  simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  -- So j ≤ m ≤ n
  have hj : j ≤ n := by omega
  rw [h j hj]

/-- **Lemma (lem.fps.prod.irlv.mul)**: If `v` is a multiple of `u`, and the first `n+1`
coefficients of `u` are zero, then the first `n+1` coefficients of `v` are zero.
Label: lem.fps.prod.irlv.mul -/
theorem fps_coeff_zero_of_multiple (u v : PowerSeries K) (n : ℕ)
    (hdvd : u ∣ v) (hu : ∀ m ≤ n, u.coeff m = 0) :
    ∀ m ≤ n, v.coeff m = 0 := by
  intro m hm
  -- Since u ∣ v, there exists a such that v = u * a
  obtain ⟨a, hva⟩ := hdvd
  rw [hva, PowerSeries.coeff_mul]
  -- The coefficient is a sum over antidiagonal m
  apply Finset.sum_eq_zero
  intro p hp
  -- p is in antidiagonal m means p.1 + p.2 = m
  simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  -- Since p.1 + p.2 = m ≤ n, we have p.1 ≤ n
  have hp1 : p.1 ≤ n := by omega
  -- So u.coeff p.1 = 0
  rw [hu p.1 hp1, zero_mul]

/-- **Lemma (lem.fps.prod.irlv.cong-mul)**: If the first `n+1` coefficients of `a` and `b`
agree, and the first `n+1` coefficients of `c` and `d` agree, then the first `n+1`
coefficients of `a*c` and `b*d` agree.
Label: lem.fps.prod.irlv.cong-mul -/
theorem fps_coeff_mul_eq_of_both_coeff_eq (a b c d : PowerSeries K) (n : ℕ)
    (hab : ∀ m ≤ n, a.coeff m = b.coeff m)
    (hcd : ∀ m ≤ n, c.coeff m = d.coeff m) :
    ∀ m ≤ n, (a * c).coeff m = (b * d).coeff m := by
  intro m hm
  -- Step 1: (a * c).coeff m = (a * d).coeff m
  have step1 : (a * c).coeff m = (a * d).coeff m := fps_coeff_mul_eq_of_coeff_eq a c d n hcd m hm
  -- Step 2: (a * d).coeff m = (b * d).coeff m
  -- We need to use commutativity: a * d = d * a, b * d = d * b
  have step2_aux : (d * a).coeff m = (d * b).coeff m := fps_coeff_mul_eq_of_coeff_eq d a b n hab m hm
  have step2 : (a * d).coeff m = (b * d).coeff m := by
    rw [mul_comm a d, mul_comm b d]
    exact step2_aux
  -- Combine
  rw [step1, step2]

end AlgebraicCombinatorics

end
