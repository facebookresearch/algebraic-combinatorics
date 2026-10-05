/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.FPS.ExpLog

/-!
# Non-integer Powers of Formal Power Series

This file formalizes non-integer powers of formal power series (FPS) and the generalized
Newton binomial formula, following Section 7.12 (sec.gf.nips) of the source.

## Main Definitions

* `AlgebraicCombinatorics.FPS.fpsPow`: The c-th power f^c for f ∈ K⟦X⟧₁ (FPS with constant term 1) and c ∈ K,
  defined as `Exp(c * Log f)` (Definition def.fps.power-c).

## Main Results

* `AlgebraicCombinatorics.FPS.fpsPow_add`: The rule f^{a+b} = f^a * f^b (Theorem thm.fps.power-c.rules).
* `AlgebraicCombinatorics.FPS.fpsPow_mul`: The rule (fg)^a = f^a * g^a (Theorem thm.fps.power-c.rules).
* `AlgebraicCombinatorics.FPS.fpsPow_pow`: The rule (f^a)^b = f^{ab} (Theorem thm.fps.power-c.rules).
* `AlgebraicCombinatorics.FPS.generalizedNewtonBinomial`: The generalized Newton binomial formula
  (1+x)^c = ∑_{k ∈ ℕ} C(c,k) x^k (Theorem thm.fps.gen-newton).
* `AlgebraicCombinatorics.FPS.binomialIdentity`: The binomial identity
  ∑_{i=0}^k C(n+i-1,i) C(n,k-2i) = C(n+k-1,k) (Proposition prop.binom.nCk-2i-qedmo.CN).

## Implementation Notes

The definition of f^c uses the Exp and Log maps from Mathlib. Specifically:
- For f ∈ K⟦X⟧₁ (constant term 1), we define f^c := Exp(c * Log f)
- This requires K to be a commutative ℚ-algebra

The generalized Newton binomial formula is proved using the polynomial identity trick:
both sides are polynomials in c that agree on ℕ, hence they agree everywhere.

## References

* Source: NonIntegerPowers.tex, Section sec.gf.nips
-/

open scoped Polynomial
open PowerSeries Finset

namespace AlgebraicCombinatorics

namespace FPS

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-!
## The Exp and Log Maps

We use Mathlib's `PowerSeries.exp` for the exponential series.
For the logarithm, we define it via the standard series log(1+x) = ∑_{n≥1} (-1)^{n-1}/n * x^n.
-/

/-- The logarithm series: log(1+x) = x - x²/2 + x³/3 - x⁴/4 + ...
    This is `\overline{log}` in the source notation.
    Label: def.fps.logbar -/
noncomputable def logSeries : K⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else algebraMap ℚ K ((-1 : ℚ)^(n-1) / n)

/-- Coefficient of the log series at position n.
    For n ≥ 1: [x^n] log(1+x) = (-1)^{n-1}/n -/
theorem coeff_logSeries (n : ℕ) :
    coeff n (logSeries (K := K)) = if n = 0 then 0 else algebraMap ℚ K ((-1 : ℚ)^(n-1) / n) := by
  simp [logSeries, coeff_mk]

/-- The constant term of the log series is 0 -/
@[simp]
theorem constantCoeff_logSeries : constantCoeff (logSeries (K := K)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_logSeries]
  simp

/-- Key lemma: coeff k (logSeries^m) = 0 for m > k.
    This follows from logSeries having constant term 0. -/
theorem coeff_logSeries_pow_eq_zero_of_gt (k m : ℕ) (h : k < m) :
    coeff k ((logSeries (K := K))^m) = 0 := by
  apply coeff_of_lt_order
  calc (k : ℕ∞) < m := by exact_mod_cast h
    _ ≤ order ((logSeries (K := K))^m) := le_order_pow_of_constantCoeff_eq_zero m constantCoeff_logSeries

omit [Algebra ℚ K] in
/-- Helper: (c • g)^m = c^m • g^m -/
theorem smul_pow_eq_pow_smul (c : K) (g : K⟦X⟧) (m : ℕ) :
    (c • g)^m = c^m • g^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, ih]
    rw [smul_mul_smul_comm, pow_succ]

omit [Algebra ℚ K] in
/-- Helper: coeff k ((c • g)^m) = c^m • coeff k (g^m) -/
theorem coeff_smul_pow (c : K) (g : K⟦X⟧) (k m : ℕ) :
    coeff k ((c • g)^m) = c^m • coeff k (g^m) := by
  rw [smul_pow_eq_pow_smul, PowerSeries.coeff_smul]

/-!
## FPS with Constant Term 1

We define the set K⟦X⟧₁ of FPS with constant term 1.
This is the domain on which non-integer powers are defined.
-/

/-- An FPS has constant term 1.
    This is the condition for f ∈ K⟦X⟧₁ in the source.
    Label: def.fps.Exp-Log-maps (b)

    Note: This is definitionally equivalent to membership in `PowerSeries₁` from ExpLog.lean:
    `HasConstantTermOne f ↔ f ∈ PowerSeries₁`. The `Prop` form is used here for convenience
    in hypotheses, while `PowerSeries₁` (a `Set`) is used in ExpLog.lean for subgroup structures. -/
def HasConstantTermOne (f : K⟦X⟧) : Prop := constantCoeff f = 1

/-- `HasConstantTermOne f` is equivalent to membership in `PowerSeries₁`.
    This bridges the two representations of "constant term equals 1". -/
theorem hasConstantTermOne_iff_mem_PowerSeries₁ {R : Type*} [CommRing R] {f : R⟦X⟧} :
    HasConstantTermOne f ↔ f ∈ PowerSeries₁ := Iff.rfl

/-- Alias for `hasConstantTermOne_iff_mem_PowerSeries₁.mp`. -/
theorem HasConstantTermOne.mem_PowerSeries₁ {R : Type*} [CommRing R] {f : R⟦X⟧}
    (hf : HasConstantTermOne f) : f ∈ PowerSeries₁ := hf

/-- Alias for `hasConstantTermOne_iff_mem_PowerSeries₁.mpr`. -/
theorem mem_PowerSeries₁.hasConstantTermOne {R : Type*} [CommRing R] {f : R⟦X⟧}
    (hf : f ∈ PowerSeries₁) : HasConstantTermOne f := hf

section HasConstantTermOneBasic
variable {R : Type*} [CommRing R]

/-- The set of FPS with constant term 1 forms a submonoid under multiplication -/
theorem hasConstantTermOne_one' : HasConstantTermOne (1 : R⟦X⟧) := by
  simp [HasConstantTermOne]

theorem hasConstantTermOne_mul' {f g : R⟦X⟧} (hf : HasConstantTermOne f) (hg : HasConstantTermOne g) :
    HasConstantTermOne (f * g) := by
  simp only [HasConstantTermOne, map_mul] at hf hg ⊢
  rw [hf, hg, one_mul]

/-- 1 + x has constant term 1 -/
theorem hasConstantTermOne_one_add_X' : HasConstantTermOne (1 + X : R⟦X⟧) := by
  simp [HasConstantTermOne]

/-- Any FPS of the form 1 + g where g has constant term 0 has constant term 1 -/
theorem hasConstantTermOne_of_constantCoeff_zero' {g : R⟦X⟧} (hg : constantCoeff g = 0) :
    HasConstantTermOne (1 + g) := by
  simp [HasConstantTermOne, hg]

end HasConstantTermOneBasic

omit [Algebra ℚ K] in
theorem hasConstantTermOne_one : HasConstantTermOne (1 : K⟦X⟧) := hasConstantTermOne_one'

omit [Algebra ℚ K] in
theorem hasConstantTermOne_mul {f g : K⟦X⟧} (hf : HasConstantTermOne f) (hg : HasConstantTermOne g) :
    HasConstantTermOne (f * g) := hasConstantTermOne_mul' hf hg

omit [Algebra ℚ K] in
theorem hasConstantTermOne_one_add_X : HasConstantTermOne (1 + X : K⟦X⟧) := hasConstantTermOne_one_add_X'

omit [Algebra ℚ K] in
theorem hasConstantTermOne_of_constantCoeff_zero {g : K⟦X⟧} (hg : constantCoeff g = 0) :
    HasConstantTermOne (1 + g) := hasConstantTermOne_of_constantCoeff_zero' hg

/-!
## The Log Map for FPS with Constant Term 1

For f ∈ K⟦X⟧₁, we define Log(f) by substituting (f-1) into the log series.
Since f has constant term 1, f-1 has constant term 0, so the substitution is well-defined.
-/

/-- The Log map: Log(f) = log_series(f-1) = logSeries.subst (f-1)
    This is well-defined when f has constant term 1.
    Label: def.fps.Exp-Log-maps -/
noncomputable def fpsLog (f : K⟦X⟧) : K⟦X⟧ :=
  (logSeries (K := K)).subst (f - 1)

/-- Log(1) = 0 -/
@[simp]
theorem fpsLog_one : fpsLog (1 : K⟦X⟧) = 0 := by
  unfold fpsLog
  simp only [sub_self]
  -- logSeries.subst 0 = 0 because every term in the finsum is zero
  ext n
  rw [PowerSeries.coeff_subst']
  · simp only [smul_eq_mul, map_zero]
    have h : ∀ d, (0 : K⟦X⟧) ^ d = if d = 0 then 1 else 0 := by
      intro d
      match d with
      | 0 => simp [pow_zero]
      | d + 1 => rw [ite_eq_right (Nat.succ_ne_zero d), zero_pow (Nat.succ_ne_zero d)]
    simp_rw [h]
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simp [logSeries, coeff_mk]
    · simp [hd]
  · exact PowerSeries.HasSubst.zero'

/-- The constant term of Log(f) is 0 when f has constant term 1 -/
theorem constantCoeff_fpsLog {f : K⟦X⟧} (hf : HasConstantTermOne f) :
    constantCoeff (fpsLog f) = 0 := by
  unfold fpsLog
  have ha : constantCoeff (f - 1) = 0 := by
    simp [HasConstantTermOne] at hf
    simp [hf]
  have hf' : constantCoeff (logSeries (K := K)) = 0 := constantCoeff_logSeries
  exact constantCoeff_subst_eq_zero ha logSeries hf'

/-!
## The Exp Map for FPS with Constant Term 0

For g ∈ K⟦X⟧₀ (constant term 0), we define Exp(g) by substituting g into exp.
-/

/-- The Exp map: Exp(g) = exp(g) = (exp K).subst g
    This is well-defined when g has constant term 0.
    Label: def.fps.Exp-Log-maps -/
noncomputable def fpsExp (g : K⟦X⟧) : K⟦X⟧ :=
  (exp K).subst g

/-- Exp(0) = 1 -/
@[simp]
theorem fpsExp_zero : fpsExp (0 : K⟦X⟧) = 1 := by
  unfold fpsExp
  have h : PowerSeries.HasSubst (0 : K⟦X⟧) := PowerSeries.HasSubst.zero'
  ext n
  rw [PowerSeries.coeff_subst' h, coeff_one]
  -- Only d = 0 contributes to the finsum, since 0^d = 0 for d > 0
  have h1 : ∀ d > 0, coeff d (exp K) • coeff n ((0 : K⟦X⟧) ^ d) = 0 := fun d hd ↦ by
    simp only [zero_pow hd.ne', map_zero, smul_zero]
  have h2 : (fun d => coeff d (exp K) • coeff n ((0 : K⟦X⟧) ^ d)).support ⊆ ({0} : Finset ℕ) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_singleton, Set.mem_singleton_iff]
    exact of_not_not fun hne ↦ hd (h1 d (Nat.pos_of_ne_zero hne))
  rw [finsum_eq_sum_of_support_subset _ h2]
  simp

/-- Exp(g) has constant term 1 when g has constant term 0 -/
theorem hasConstantTermOne_fpsExp {g : K⟦X⟧} (hg : constantCoeff g = 0) :
    HasConstantTermOne (fpsExp g) := by
  unfold HasConstantTermOne fpsExp
  show constantCoeff (subst g (exp K)) = 1
  rw [PowerSeries.constantCoeff]
  rw [constantCoeff_subst (HasSubst.of_constantCoeff_zero' hg)]
  have hd : ∀ d : ℕ, d ≠ 0 → MvPowerSeries.constantCoeff (g ^ d) = 0 := by
    intro d hd
    have : MvPowerSeries.constantCoeff (g ^ d) = (MvPowerSeries.constantCoeff g) ^ d :=
      RingHom.map_pow _ _ _
    rw [this, ← PowerSeries.constantCoeff, hg, zero_pow hd]
  conv_lhs =>
    arg 1
    ext d
    rw [show MvPowerSeries.constantCoeff (g ^ d) = if d = 0 then 1 else 0 by
      split_ifs with h
      · simp [h]
      · exact hd d h]
  have heq : (fun d => coeff d (exp K) • (if d = 0 then (1 : K) else 0)) =
             (fun d => if d = 0 then coeff 0 (exp K) else 0) := by
    ext d
    split_ifs with h
    · simp [h]
    · simp
  rw [heq]
  rw [finsum_eq_single _ 0]
  · simp [coeff_exp]
  · intro d hd
    simp [hd]

/-- The exponential functional equation: Exp(x + y) = Exp(x) * Exp(y)
    This is a fundamental property of the exponential series.
    For power series x, y with constant term 0:
    exp(x + y) = exp(x) * exp(y)
    Label: (exp functional equation)

    **Proof strategy** (from the textbook):
    Both sides satisfy the same differential equation with the same initial condition.
    Let F(x,y) = exp(x+y) and G(x,y) = exp(x) * exp(y).
    - ∂F/∂x = exp(x+y) = F and ∂F/∂y = exp(x+y) = F
    - ∂G/∂x = exp(x) * exp(y) = G and ∂G/∂y = exp(x) * exp(y) = G
    - F(0,0) = exp(0) = 1 and G(0,0) = exp(0) * exp(0) = 1
    By uniqueness of solutions to the ODE, F = G.

    **Alternative proof** (coefficient comparison):
    Use the Cauchy product formula and the fact that
    [x^n](exp(x+y)) = ∑_{k=0}^n [x^k](exp x) * [x^{n-k}](exp y) * C(n,k)
    which equals [x^n](exp x * exp y) by the binomial theorem.

    **Mathlib note**: Mathlib's `exp_mul_exp_eq_exp_add` proves this for the special case
    where x = a • X and y = b • X (i.e., rescaling). The general case requires the
    derivative characterization or coefficient comparison. -/
theorem fpsExp_add {x y : K⟦X⟧} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    fpsExp (x + y) = fpsExp x * fpsExp y := by
  -- Create PowerSeries₀ subtypes
  let fx : PowerSeries₀ (R := K) := ⟨x, hx⟩
  let fy : PowerSeries₀ (R := K) := ⟨y, hy⟩
  -- Use Exp_add from ExpLog.lean and extract the underlying values
  exact congrArg Subtype.val (Exp_add fx fy)

/-- Uniqueness theorem for power series over ℚ-algebras:
    If two power series have the same derivative and constant term, they are equal. -/
private theorem derivative_ext_Q {f g : K⟦X⟧}
    (hD : d⁄dX f = d⁄dX g) (hc : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n with
  | zero =>
    simp only [← coeff_zero_eq_constantCoeff_apply] at hc
    exact hc
  | succ n ih =>
    have h1 : coeff n (d⁄dX f) = coeff n (d⁄dX g) := by rw [hD]
    rw [coeff_derivative, coeff_derivative] at h1
    have hinv : IsUnit ((n + 1 : ℕ) : K) := by
      have h : ((n + 1 : ℕ) : K) = algebraMap ℚ K (n + 1) := by simp
      rw [h]
      apply RingHom.isUnit_map
      simp only [isUnit_iff_ne_zero, ne_eq]
      exact_mod_cast Nat.succ_ne_zero n
    have heq : (↑n + 1 : K) = (↑(n + 1) : K) := by simp
    rw [heq] at h1
    exact hinv.mul_right_cancel h1

/-- The derivative of fpsLog using the chain rule. -/
private theorem derivative_fpsLog {f : K⟦X⟧} (hf : HasConstantTermOne f) :
    d⁄dX (fpsLog f) = (d⁄dX (logSeries : K⟦X⟧)).subst (f - 1) * d⁄dX f := by
  unfold fpsLog
  have hsub : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero (by
    simp only [HasConstantTermOne] at hf
    rw [map_sub, map_one]
    have : MvPowerSeries.constantCoeff (R := K) (σ := Unit) f = constantCoeff f := rfl
    rw [this, hf, sub_self])
  rw [derivative_subst hsub]
  have h1 : d⁄dX (1 : K⟦X⟧) = 0 := by rw [← map_one C, derivative_C]
  simp only [map_sub, h1, sub_zero]

omit [Algebra ℚ K] in
/-- Helper lemma for substitution of constants. -/
private theorem subst_C' (a : K⟦X⟧) (ha : HasSubst a) (c : K) : (C c : K⟦X⟧).subst a = C c := by
  have h : (C c : K⟦X⟧) = (Polynomial.C c : K⟦X⟧) := by
    ext n; rw [coeff_C, Polynomial.coeff_coe, Polynomial.coeff_C]
  rw [h, subst_coe ha]
  simp [Polynomial.aeval_C]

omit [Algebra ℚ K] in
/-- Helper lemma for substitution of 1. -/
private theorem subst_one' (a : K⟦X⟧) (ha : HasSubst a) : (1 : K⟦X⟧).subst a = 1 := by
  have h : (1 : K⟦X⟧) = C 1 := by ext n; simp [coeff_one]
  rw [h, subst_C' a ha 1, map_one]

omit [Algebra ℚ K] in
/-- Helper lemma for substitution of X. -/
private theorem subst_X' (a : K⟦X⟧) (ha : HasSubst a) : (X : K⟦X⟧).subst a = a := by
  have h : (X : K⟦X⟧) = ((Polynomial.X : Polynomial K) : K⟦X⟧) := by
    ext n
    rw [coeff_X, Polynomial.coeff_coe, Polynomial.coeff_X]
    simp only [eq_comm]
  rw [h, subst_coe ha]
  simp [Polynomial.aeval_X]

/-- The derivative of logSeries is the geometric series 1/(1+x). -/
private theorem derivative_logSeries :
    d⁄dX (logSeries (K := K)) = PowerSeries.mk fun n => algebraMap ℚ K ((-1 : ℚ)^n) := by
  ext n
  rw [coeff_derivative]
  simp only [logSeries, coeff_mk]
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  have h1 : n + 1 - 1 = n := Nat.add_sub_cancel n 1
  rw [h1]
  have h2 : (n + 1 : K) = algebraMap ℚ K (n + 1) := by
    simp only [map_add, map_natCast, map_one]
  rw [h2, ← map_mul]
  congr 1
  have : (n : ℚ) + 1 = ((n + 1) : ℕ) := by norm_cast
  rw [this]
  field_simp

omit [Algebra ℚ K] in
/-- The geometric series 1/(1+x) satisfies (1-x+x²-...) * (1+x) = 1. -/
private theorem mk_neg_one_pow_mul_one_add_X :
    (PowerSeries.mk fun n => (-1 : K)^n) * (1 + X) = 1 := by
  have h1 : (mk 1 : K⟦X⟧) * (1 - X) = 1 := mk_one_mul_one_sub_eq_one K
  have rescale_neg_one_mk_one : rescale (-1 : K) (mk 1) = PowerSeries.mk fun n => (-1 : K)^n := by
    ext n; simp [coeff_rescale, coeff_mk]
  have rescale_neg_one_one_sub_X : rescale (-1 : K) (1 - X) = 1 + X := by
    ext n
    simp only [coeff_rescale, map_sub, map_one, coeff_X, map_add]
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp [pow_one]
      | succ n => simp only [coeff_one, Nat.succ_ne_zero, ↓reduceIte]; simp
  rw [← rescale_neg_one_mk_one, ← rescale_neg_one_one_sub_X]
  rw [← (rescale (-1 : K)).map_mul]
  rw [h1]; simp

/-- The derivative of logSeries times (1+X) equals 1. -/
private theorem derivative_logSeries_mul_one_add_X :
    (d⁄dX (logSeries : K⟦X⟧)) * (1 + X) = 1 := by
  rw [derivative_logSeries]
  have h : (PowerSeries.mk fun n => algebraMap ℚ K ((-1 : ℚ)^n)) =
           PowerSeries.mk fun n => (-1 : K)^n := by
    ext n; simp only [coeff_mk]; rw [map_pow, map_neg, map_one]
  rw [h]
  exact mk_neg_one_pow_mul_one_add_X

/-- Key lemma: (d/dx logSeries).subst (f-1) * f = 1 when f has constant term 1.
    This encodes that the derivative of log is the reciprocal. -/
private theorem derivative_logSeries_subst_mul_f {f : K⟦X⟧} (hf : HasConstantTermOne f) :
    (d⁄dX (logSeries : K⟦X⟧)).subst (f - 1) * f = 1 := by
  have hsub : HasSubst (f - 1) := HasSubst.of_constantCoeff_zero (by
    simp only [HasConstantTermOne] at hf
    rw [map_sub, map_one]
    have : MvPowerSeries.constantCoeff (R := K) (σ := Unit) f = constantCoeff f := rfl
    rw [this, hf, sub_self])
  have h1 := derivative_logSeries_mul_one_add_X (K := K)
  have h2 : ((d⁄dX (logSeries : K⟦X⟧)) * (1 + X)).subst (f - 1) = (1 : K⟦X⟧).subst (f - 1) := by
    rw [h1]
  rw [subst_mul hsub] at h2
  have h3 : (1 + X : K⟦X⟧).subst (f - 1) = f := by
    rw [subst_add hsub, subst_one' _ hsub, subst_X' _ hsub]
    ring
  rw [h3, subst_one' _ hsub] at h2
  exact h2

/-- The logarithm product rule: Log(f * g) = Log(f) + Log(g)
    This is a fundamental property of the logarithm series.
    For power series f, g with constant term 1:
    log(f * g) = log(f) + log(g)
    Label: (log product rule)

    **Proof strategy** (from the textbook):
    Use the derivative characterization. Let h = log(fg) - log(f) - log(g).
    Then h' = (fg)'/(fg) - f'/f - g'/g = (f'g + fg')/(fg) - f'/f - g'/g = 0.
    Since h(0) = 0 and h' = 0, we have h = 0.

    **Alternative proof**:
    Use the inverse property: if Exp and Log are inverses, then
    Log(fg) = Log(Exp(Log f) * Exp(Log g)) = Log(Exp(Log f + Log g)) = Log f + Log g.

    **Dependency**: This proof requires either the derivative characterization
    or the inverse property `Exp_Log_inverse` from ExpLog.lean. -/
theorem fpsLog_mul {f g : K⟦X⟧} (hf : HasConstantTermOne f) (hg : HasConstantTermOne g) :
    fpsLog (f * g) = fpsLog f + fpsLog g := by
  apply derivative_ext_Q
  · -- Show derivatives are equal
    rw [derivative_fpsLog (hasConstantTermOne_mul hf hg)]
    rw [map_add, derivative_fpsLog hf, derivative_fpsLog hg]
    -- Since f * g has constant term 1, it's a unit
    have hfg_unit : IsUnit (f * g) := by
      rw [isUnit_iff_constantCoeff]
      simp only [HasConstantTermOne] at hf hg
      rw [map_mul, hf, hg, one_mul]
      exact isUnit_one
    -- We have L_{fg} * (fg) = 1, L_f * f = 1, L_g * g = 1
    have hL_fg : (d⁄dX (logSeries : K⟦X⟧)).subst (f * g - 1) * (f * g) = 1 :=
      derivative_logSeries_subst_mul_f (hasConstantTermOne_mul hf hg)
    have hL_f : (d⁄dX (logSeries : K⟦X⟧)).subst (f - 1) * f = 1 :=
      derivative_logSeries_subst_mul_f hf
    have hL_g : (d⁄dX (logSeries : K⟦X⟧)).subst (g - 1) * g = 1 :=
      derivative_logSeries_subst_mul_f hg
    -- Show LHS * (fg) = (fg)'
    have h_lhs : (d⁄dX (logSeries : K⟦X⟧)).subst (f * g - 1) * d⁄dX (f * g) * (f * g) =
                 d⁄dX (f * g) := by
      calc (d⁄dX (logSeries : K⟦X⟧)).subst (f * g - 1) * d⁄dX (f * g) * (f * g)
          = (d⁄dX (logSeries : K⟦X⟧)).subst (f * g - 1) * (f * g) * d⁄dX (f * g) := by ring
        _ = 1 * d⁄dX (f * g) := by rw [hL_fg]
        _ = d⁄dX (f * g) := by ring
    -- Show RHS * (fg) = (fg)'
    have h_rhs : ((d⁄dX (logSeries : K⟦X⟧)).subst (f - 1) * d⁄dX f +
                  (d⁄dX (logSeries : K⟦X⟧)).subst (g - 1) * d⁄dX g) * (f * g) =
                 d⁄dX (f * g) := by
      have h_leibniz : d⁄dX (f * g) = f * d⁄dX g + g * d⁄dX f := by
        have h := (derivative (R := K)).leibniz f g
        simp only [smul_eq_mul] at h
        exact h
      calc ((d⁄dX (logSeries : K⟦X⟧)).subst (f - 1) * d⁄dX f +
            (d⁄dX (logSeries : K⟦X⟧)).subst (g - 1) * d⁄dX g) * (f * g)
          = (d⁄dX (logSeries : K⟦X⟧)).subst (f - 1) * d⁄dX f * (f * g) +
            (d⁄dX (logSeries : K⟦X⟧)).subst (g - 1) * d⁄dX g * (f * g) := by ring
        _ = (d⁄dX (logSeries : K⟦X⟧)).subst (f - 1) * f * d⁄dX f * g +
            (d⁄dX (logSeries : K⟦X⟧)).subst (g - 1) * g * d⁄dX g * f := by ring
        _ = 1 * d⁄dX f * g + 1 * d⁄dX g * f := by rw [hL_f, hL_g]
        _ = d⁄dX f * g + d⁄dX g * f := by ring
        _ = g * d⁄dX f + f * d⁄dX g := by ring
        _ = d⁄dX (f * g) := by rw [h_leibniz]; ring
    -- Now we have LHS * (fg) = RHS * (fg), cancel fg
    have h_eq : (d⁄dX (logSeries : K⟦X⟧)).subst (f * g - 1) * d⁄dX (f * g) * (f * g) =
                ((d⁄dX (logSeries : K⟦X⟧)).subst (f - 1) * d⁄dX f +
                 (d⁄dX (logSeries : K⟦X⟧)).subst (g - 1) * d⁄dX g) * (f * g) := by
      rw [h_lhs, h_rhs]
    exact hfg_unit.mul_right_cancel h_eq
  · -- Show constant terms are equal
    rw [constantCoeff_fpsLog (hasConstantTermOne_mul hf hg)]
    rw [map_add, constantCoeff_fpsLog hf, constantCoeff_fpsLog hg]
    ring

/-!
## Definition of Non-integer Powers (Definition def.fps.power-c)

For f ∈ K⟦X⟧₁ and c ∈ K, we define f^c := Exp(c * Log(f)).

This definition:
- Does not conflict with integer powers (since Log and Exp are inverses on the appropriate domains)
- Makes the rules of exponents hold
- Yields (1+x)^c = ∑ C(c,k) x^k (generalized Newton binomial formula)
-/

/-- The c-th power of an FPS f with constant term 1.
    f^c := Exp(c * Log(f)) = exp.subst (c * log_series.subst (f-1))
    Label: def.fps.power-c -/
noncomputable def fpsPow (f : K⟦X⟧) (c : K) : K⟦X⟧ :=
  fpsExp (c • fpsLog f)

/-- Notation for non-integer powers (when needed) -/
scoped notation:80 f " ^ᶠ " c:81 => fpsPow f c

/-- f^0 = 1 for any f with constant term 1 -/
@[simp]
theorem fpsPow_zero (f : K⟦X⟧) : f ^ᶠ (0 : K) = 1 := by
  simp only [fpsPow, zero_smul, fpsExp_zero]

/-- 1^c = 1 for any c -/
@[simp]
theorem one_fpsPow (c : K) : (1 : K⟦X⟧) ^ᶠ c = 1 := by
  simp only [fpsPow, fpsLog_one, smul_zero, fpsExp_zero]

/-- f^c has constant term 1 when f has constant term 1 -/
theorem hasConstantTermOne_fpsPow {f : K⟦X⟧} (hf : HasConstantTermOne f) (c : K) :
    HasConstantTermOne (f ^ᶠ c) := by
  apply hasConstantTermOne_fpsExp
  rw [constantCoeff_smul, constantCoeff_fpsLog hf, smul_zero]

/-!
## Rules of Exponents (Theorem thm.fps.power-c.rules)

For any a, b ∈ K and f, g ∈ K⟦X⟧₁:
- f^{a+b} = f^a * f^b
- (fg)^a = f^a * g^a
- (f^a)^b = f^{ab}
-/

/-- Rule of exponents: f^{a+b} = f^a * f^b
    Label: eq.sec.gf.nips.rules-of-exps (first rule)

    **Proof**:
    f^{a+b} = Exp((a+b) • Log f)
           = Exp(a • Log f + b • Log f)    [by smul_add]
           = Exp(a • Log f) * Exp(b • Log f)  [by fpsExp_add]
           = f^a * f^b

    **Dependency**: Requires `fpsExp_add`. -/
theorem fpsPow_add {f : K⟦X⟧} (hf : HasConstantTermOne f) (a b : K) :
    f ^ᶠ (a + b) = (f ^ᶠ a) * (f ^ᶠ b) := by
  unfold fpsPow
  rw [add_smul]
  rw [fpsExp_add]
  · rw [constantCoeff_smul, constantCoeff_fpsLog hf, smul_zero]
  · rw [constantCoeff_smul, constantCoeff_fpsLog hf, smul_zero]

/-- Rule of exponents: (fg)^a = f^a * g^a
    Label: eq.sec.gf.nips.rules-of-exps (second rule) -/
theorem fpsPow_mul {f g : K⟦X⟧} (hf : HasConstantTermOne f) (hg : HasConstantTermOne g) (a : K) :
    (f * g) ^ᶠ a = (f ^ᶠ a) * (g ^ᶠ a) := by
  unfold fpsPow
  -- Goal: fpsExp (a • fpsLog (f * g)) = fpsExp (a • fpsLog f) * fpsExp (a • fpsLog g)
  -- Use the log product rule: fpsLog (f * g) = fpsLog f + fpsLog g
  rw [fpsLog_mul hf hg]
  -- Goal: fpsExp (a • (fpsLog f + fpsLog g)) = fpsExp (a • fpsLog f) * fpsExp (a • fpsLog g)
  -- Use smul_add to distribute the scalar
  rw [smul_add]
  -- Goal: fpsExp (a • fpsLog f + a • fpsLog g) = fpsExp (a • fpsLog f) * fpsExp (a • fpsLog g)
  -- Use the exp functional equation: fpsExp (x + y) = fpsExp x * fpsExp y
  apply fpsExp_add
  · -- Need: constantCoeff (a • fpsLog f) = 0
    rw [constantCoeff_smul, constantCoeff_fpsLog hf, smul_zero]
  · -- Need: constantCoeff (a • fpsLog g) = 0
    rw [constantCoeff_smul, constantCoeff_fpsLog hg, smul_zero]

/-- Rule of exponents: (f^a)^b = f^{ab}
    Label: eq.sec.gf.nips.rules-of-exps (third rule)

    **Proof strategy**:
    (f^a)^b = Exp(b • Log(f^a))
           = Exp(b • Log(Exp(a • Log f)))
           = Exp(b • (a • Log f))         [by fpsLog_fpsExp: Log(Exp g) = g]
           = Exp((b * a) • Log f)         [by smul_smul]
           = Exp((a * b) • Log f)         [by mul_comm]
           = f^{ab}

    **Dependency**: Requires the inverse property `fpsLog (fpsExp g) = g`
    for g with constant term 0. This is proved in ExpLog.lean as `Log_Exp`. -/
theorem fpsPow_pow {f : K⟦X⟧} (hf : HasConstantTermOne f) (a b : K) :
    (f ^ᶠ a) ^ᶠ b = f ^ᶠ (a * b) := by
  unfold fpsPow
  -- Goal: fpsExp (b • fpsLog (fpsExp (a • fpsLog f))) = fpsExp ((a * b) • fpsLog f)
  -- Key fact: constantCoeff (a • fpsLog f) = 0
  have h_alog_const : constantCoeff (a • fpsLog f) = 0 := by
    rw [constantCoeff_smul, constantCoeff_fpsLog hf, smul_zero]
  -- Key step: fpsLog (fpsExp (a • fpsLog f)) = a • fpsLog f
  -- This uses the connection to Log/Exp from ExpLog.lean
  have h1 : fpsLog (fpsExp (a • fpsLog f)) = a • fpsLog f := by
    -- Use that logSeries = logbar K
    have hlogbar_eq : logSeries (K := K) = logbar K := by
      ext n; simp only [logSeries, coeff_mk, coeff_logbar]
    -- Log_Exp : Log (Exp g) = g for g : PowerSeries₀
    have hLog_Exp := Log_Exp ⟨a • fpsLog f, h_alog_const⟩
    -- hLog_Exp : Log (Exp ⟨a • fpsLog f, h_alog_const⟩) = ⟨a • fpsLog f, h_alog_const⟩
    -- Expand fpsLog and fpsExp using their definitions
    simp only [fpsLog, fpsExp, hlogbar_eq]
    -- Goal: (logbar K).subst ((exp K).subst (a • (logbar K).subst (f - 1)) - 1) = a • (logbar K).subst (f - 1)
    -- Use Exp_val: (Exp g).val = (exp K).subst g.val
    -- Use Log_val: (Log f).val = (logbar K).subst (f.val - 1)
    -- (exp K).subst (a • fpsLog f) = (Exp ⟨a • fpsLog f, h_alog_const⟩).val
    have hExp_val : (exp K).subst (a • (logbar K).subst (f - 1)) =
                    (Exp ⟨a • fpsLog f, h_alog_const⟩).val := by
      simp only [Exp_val, fpsLog, hlogbar_eq]
    rw [hExp_val]
    -- Goal: (logbar K).subst ((Exp ⟨...⟩).val - 1) = a • (logbar K).subst (f - 1)
    -- (logbar K).subst (f.val - 1) = (Log f).val for f : PowerSeries₁
    have hExp_mem : (Exp ⟨a • fpsLog f, h_alog_const⟩).val ∈ PowerSeries₁ :=
      (Exp ⟨a • fpsLog f, h_alog_const⟩).property
    have hLog_val : (logbar K).subst ((Exp ⟨a • fpsLog f, h_alog_const⟩).val - 1) =
                    (Log ⟨(Exp ⟨a • fpsLog f, h_alog_const⟩).val, hExp_mem⟩).val := by
      simp only [Log_val]
    rw [hLog_val]
    -- Now show Log ⟨(Exp ⟨...⟩).val, hExp_mem⟩ = Log (Exp ⟨...⟩)
    have hsubtype_eq : (⟨(Exp ⟨a • fpsLog f, h_alog_const⟩).val, hExp_mem⟩ : PowerSeries₁ (R := K)) =
                       Exp ⟨a • fpsLog f, h_alog_const⟩ := by
      apply Subtype.ext; rfl
    rw [hsubtype_eq, hLog_Exp]
    -- Goal: ↑⟨a • fpsLog f, h_alog_const⟩ = a • (logbar K).subst (f - 1)
    simp only [fpsLog, hlogbar_eq]
  -- Now substitute h1 into the goal
  rw [h1]
  -- Goal: fpsExp (b • (a • fpsLog f)) = fpsExp ((a * b) • fpsLog f)
  -- Use smul_smul: b • (a • x) = (b * a) • x
  congr 1
  rw [smul_smul, mul_comm]

/-!
### Connection to ExpLog.lean

We establish the connection between our `logSeries`/`fpsLog`/`fpsExp` definitions
and the `logbar`/`Log`/`Exp` definitions from ExpLog.lean. This allows us to use
the `Exp_Log` theorem to prove `fpsPow_one`.
-/

/-- Our logSeries equals PowerSeries.logbar from ExpLog.lean -/
theorem logSeries_eq_logbar : logSeries (K := K) = logbar K := by
  ext n
  simp only [coeff_logSeries, coeff_logbar]

/-- fpsLog f equals (Log f).val when f has constant term 1 -/
theorem fpsLog_eq_Log_val {f : K⟦X⟧} (hf : HasConstantTermOne f) :
    fpsLog f = (Log ⟨f, hf⟩).val := by
  simp only [fpsLog, Log_val, logSeries_eq_logbar]

/-- fpsExp g equals (Exp g').val when g has constant term 0 -/
theorem fpsExp_eq_Exp_val {g : K⟦X⟧} (hg : constantCoeff g = 0) :
    fpsExp g = (Exp ⟨g, hg⟩).val := by
  simp only [fpsExp, Exp_val]

/-- f^1 = f for any f with constant term 1.
    This follows from the Exp-Log inverse property: Exp(Log(f)) = f.
    Label: (implicit in def.fps.power-c consistency) -/
theorem fpsPow_one {f : K⟦X⟧} (hf : HasConstantTermOne f) : f ^ᶠ (1 : K) = f := by
  unfold fpsPow
  simp only [one_smul]
  -- Goal: fpsExp (fpsLog f) = f
  -- Use the connection to Exp and Log from ExpLog.lean
  have hlog : constantCoeff (fpsLog f) = 0 := constantCoeff_fpsLog hf
  have hlog_eq : fpsLog f = (Log ⟨f, hf⟩).val := fpsLog_eq_Log_val hf
  rw [hlog_eq]
  rw [fpsExp_eq_Exp_val (by rw [← hlog_eq]; exact hlog)]
  -- Now we need (Exp (Log ⟨f, hf⟩)).val = f
  -- This follows from Exp_Log theorem in ExpLog.lean
  exact congrArg Subtype.val (Exp_Log ⟨f, hf⟩)

/-- The constant term of f^c is 1 when f has constant term 1.
    This is a simp-friendly version of `hasConstantTermOne_fpsPow`.
    Label: def.fps.power-c (property) -/
@[simp]
theorem constantCoeff_fpsPow {f : K⟦X⟧} (hf : HasConstantTermOne f) (c : K) :
    constantCoeff (f ^ᶠ c) = 1 := hasConstantTermOne_fpsPow hf c

/-- f^(-c) = (f^c)⁻¹ for f with constant term 1 (over a field).
    This extends the rules of exponents to negative powers.
    Label: def.fps.power-c (negative power property) -/
theorem fpsPow_neg {K' : Type*} [Field K'] [Algebra ℚ K'] {f : K'⟦X⟧}
    (hf : HasConstantTermOne f) (c : K') :
    f ^ᶠ (-c) = (f ^ᶠ c)⁻¹ := by
  have h1 : f ^ᶠ (-c) * f ^ᶠ c = 1 := by
    calc f ^ᶠ (-c) * f ^ᶠ c = f ^ᶠ (-c + c) := by rw [← fpsPow_add hf]
      _ = f ^ᶠ 0 := by ring_nf
      _ = 1 := fpsPow_zero f
  have h2 : constantCoeff (f ^ᶠ c) ≠ 0 := by
    rw [constantCoeff_fpsPow hf]
    exact one_ne_zero
  rw [MvPowerSeries.eq_inv_iff_mul_eq_one h2]
  exact h1

/-- f^(a-b) = f^a / f^b for f with constant term 1 (over a field).
    This extends the rules of exponents to subtraction.
    Label: def.fps.power-c (subtraction rule) -/
theorem fpsPow_sub {K' : Type*} [Field K'] [Algebra ℚ K'] {f : K'⟦X⟧}
    (hf : HasConstantTermOne f) (a b : K') :
    f ^ᶠ (a - b) = (f ^ᶠ a) * (f ^ᶠ b)⁻¹ := by
  rw [sub_eq_add_neg, fpsPow_add hf, fpsPow_neg hf]

/-- f^(2*c) = (f^c)^2 for f with constant term 1.
    A useful special case of `fpsPow_pow`.
    Label: def.fps.power-c (doubling rule) -/
theorem fpsPow_two_mul {f : K⟦X⟧} (hf : HasConstantTermOne f) (c : K) :
    f ^ᶠ (2 * c) = (f ^ᶠ c) ^ 2 := by
  have h : (2 : K) * c = c + c := by ring
  rw [h, fpsPow_add hf, sq]

/-!
## Generalized Newton Binomial Formula (Theorem thm.fps.gen-newton)

For any c ∈ K (where K is a commutative ℚ-algebra):
(1+x)^c = ∑_{k ∈ ℕ} C(c,k) x^k

where C(c,k) = c(c-1)(c-2)⋯(c-k+1)/k! is the generalized binomial coefficient.

Note: We need K to be a BinomialRing to use Ring.choose. Since K is a ℚ-algebra,
it has a BinomialRing structure.
-/

variable [BinomialRing K]

/-!
### Key lemmas for the proof

The proof strategy is:
1. Show that `fpsLog (1+X) = logSeries`
2. Show that `fpsPow (1+X) c = fpsExp (c • logSeries)`
3. Show that for natural `n`, `fpsExp (n • logSeries) = (1+X)^n` using the exp functional equation
4. Use `binomialSeries_nat`: `binomialSeries K n = (1+X)^n`
5. Apply the polynomial identity trick: both sides have polynomial coefficients in `c`
   that agree on all natural numbers, hence they agree everywhere
-/

omit [BinomialRing K] in
/-- `logSeries.subst X = logSeries` (substituting X into logSeries is the identity) -/
private theorem logSeries_subst_X : (logSeries (K := K)).subst (X : K⟦X⟧) = logSeries := by
  have hX : HasSubst (X : K⟦X⟧) := HasSubst.X'
  ext n
  rw [coeff_subst' hX]
  simp only [logSeries, coeff_mk]
  have h : ∀ d, coeff n ((X : K⟦X⟧) ^ d) = if n = d then 1 else 0 := fun d => by
    simp only [coeff_X_pow]
  simp_rw [h, smul_eq_mul]
  rw [finsum_eq_single _ n]
  · by_cases hn : n = 0 <;> simp [hn]
  · intro d hd
    simp only [mul_ite, mul_one, mul_zero]
    simp [Ne.symm hd]

omit [BinomialRing K] in
/-- `fpsLog (1+X) = logSeries` -/
private theorem fpsLog_one_add_X' : fpsLog (1 + X : K⟦X⟧) = logSeries (K := K) := by
  unfold fpsLog
  simp only [add_sub_cancel_left]
  exact logSeries_subst_X

omit [BinomialRing K] in
/-- `fpsPow (1+X) c = fpsExp (c • logSeries)` -/
private theorem fpsPow_one_add_X' (c : K) : (1 + X : K⟦X⟧) ^ᶠ c = fpsExp (c • logSeries (K := K)) := by
  unfold fpsPow
  rw [fpsLog_one_add_X']

omit [BinomialRing K] in
/-- `(exp K).subst (c • X) = rescale c (exp K)` -/
private theorem exp_subst_smul_X (c : K) : (exp K).subst (c • X : K⟦X⟧) = rescale c (exp K) := by
  ext n
  rw [coeff_subst' (HasSubst.smul_X' c), coeff_rescale]
  simp only [smul_eq_mul, coeff_exp]
  have h : ∀ d, coeff n ((c • X : K⟦X⟧) ^ d) = if n = d then c^d else 0 := fun d => by
    rw [smul_pow]
    simp only [smul_eq_mul, coeff_smul, coeff_X_pow]
    split_ifs with h <;> simp
  simp_rw [h]
  rw [finsum_eq_single _ n]
  · simp [mul_comm]
  · intro d hd
    simp [Ne.symm hd]

omit [BinomialRing K] in
/-- For natural `n`, `(exp K).subst (n • X) = (exp K)^n` -/
private theorem exp_subst_nat_smul_X (n : ℕ) :
    (exp K).subst ((n : K) • X : K⟦X⟧) = (exp K) ^ n := by
  rw [exp_subst_smul_X, exp_pow_eq_rescale_exp]

omit [BinomialRing K] in
/-- For natural number exponents, fpsPow agrees with the standard power.
    This is a local version for use in generalizedNewtonBinomial.
    The main theorem fpsPow_nat is proved later without the BinomialRing assumption. -/
private theorem fpsPow_nat' {f : K⟦X⟧} (hf : HasConstantTermOne f) (n : ℕ) :
    f ^ᶠ (n : K) = f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, fpsPow_add hf, ih, pow_succ, fpsPow_one hf]

/-!
### Helper lemmas for the polynomial identity principle

The proof of `generalizedNewtonBinomial` uses the polynomial identity principle:
both `Ring.choose c k` and `coeff k ((1+X)^ᶠ c)` are polynomial functions of `c`
that agree on all natural numbers, hence they are equal.

The following lemmas establish the polynomial structure of `Ring.choose c k`.
-/

variable [CharZero K]

omit [BinomialRing K] [CharZero K] in
/-- Key helper: `(descPochhammer ℤ k).smeval c` equals `(descPochhammer K k).eval c`
    when K is a ℚ-algebra. This shows that the integer descending Pochhammer
    evaluates to the same value as the K-valued descending Pochhammer. -/
private theorem descPochhammer_smeval_eq_eval (k : ℕ) (c : K) :
    (descPochhammer ℤ k).smeval c = (descPochhammer K k).eval c := by
  rw [Polynomial.eval_eq_smeval]
  have h1 : descPochhammer K k = (descPochhammer ℚ k).map (algebraMap ℚ K) := by
    rw [descPochhammer_map]
  have h2 : descPochhammer ℚ k = (descPochhammer ℤ k).map (algebraMap ℤ ℚ) := by
    rw [descPochhammer_map]
  rw [h1, h2, Polynomial.map_map]
  induction (descPochhammer ℤ k) using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.smeval_add, Polynomial.map_add, Polynomial.smeval_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.smeval_monomial, Polynomial.map_monomial, Polynomial.smeval_monomial]
    simp only [zsmul_eq_mul, smul_eq_mul]
    have hcomp : ((algebraMap ℚ K).comp (algebraMap ℤ ℚ)) a = (a : K) := by
      simp only [algebraMap_int_eq, eq_intCast]
    rw [hcomp]

omit [CharZero K] in
/-- `Ring.choose c k` equals `(1/k!) • (descPochhammer K k).eval c`.
    This expresses the generalized binomial coefficient as a polynomial evaluation,
    which is key to the polynomial identity principle proof. -/
private theorem Ring_choose_eq_smul_descPochhammer (k : ℕ) (c : K) :
    Ring.choose c k = algebraMap ℚ K ((k.factorial : ℚ)⁻¹) • (descPochhammer K k).eval c := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose c k
  rw [descPochhammer_smeval_eq_eval] at h
  rw [Algebra.smul_def]
  have hfac_ne_zero : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2 : algebraMap ℚ K (k.factorial : ℚ) * Ring.choose c k = (descPochhammer K k).eval c := by
    have hnsmul : k.factorial • Ring.choose c k = (k.factorial : K) * Ring.choose c k := by
      rw [nsmul_eq_mul]
    have halg : algebraMap ℚ K (k.factorial : ℚ) = (k.factorial : K) := by
      simp only [map_natCast]
    rw [halg, ← hnsmul, ← h]
  have h3 : Ring.choose c k = algebraMap ℚ K (k.factorial : ℚ)⁻¹ * (descPochhammer K k).eval c := by
    have h4 : algebraMap ℚ K (k.factorial : ℚ)⁻¹ * algebraMap ℚ K (k.factorial : ℚ) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hfac_ne_zero, map_one]
    calc Ring.choose c k
        = 1 * Ring.choose c k := by ring
      _ = (algebraMap ℚ K (k.factorial : ℚ)⁻¹ * algebraMap ℚ K (k.factorial : ℚ)) * Ring.choose c k := by rw [h4]
      _ = algebraMap ℚ K (k.factorial : ℚ)⁻¹ * (algebraMap ℚ K (k.factorial : ℚ) * Ring.choose c k) := by ring
      _ = algebraMap ℚ K (k.factorial : ℚ)⁻¹ * (descPochhammer K k).eval c := by rw [h2]
  exact h3

omit [BinomialRing K] in
/-- The polynomial identity principle for ℚ-algebras: if a polynomial over ℚ evaluates to 0
    at all natural numbers (when mapped to K), then the polynomial is zero.
    This is the key tool for proving that two polynomial functions agreeing on ℕ are equal. -/
private theorem polynomial_zero_of_nat_roots (p : Polynomial ℚ)
    (h : ∀ n : ℕ, (p.map (algebraMap ℚ K)).eval (n : K) = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hnat : Set.Infinite (Set.range (fun n : ℕ => (n : ℚ))) :=
    Set.infinite_range_of_injective Nat.cast_injective
  apply hnat.mono
  intro x hx
  simp only [Set.mem_range] at hx
  obtain ⟨n, rfl⟩ := hx
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot]
  have h1 : (p.map (algebraMap ℚ K)).eval (↑n : K) = algebraMap ℚ K (p.eval (↑n : ℚ)) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_natCast]
  rw [h n] at h1
  have h2 : Function.Injective (algebraMap ℚ K) := (algebraMap ℚ K).injective
  have h3 : algebraMap ℚ K (p.eval (↑n : ℚ)) = 0 := h1.symm
  rw [← map_zero (algebraMap ℚ K)] at h3
  exact h2 h3

/-- The polynomial for Ring.choose: `(1/k!) * descPochhammer k` evaluates to `Nat.choose n k`
    at natural numbers. This is key for the polynomial identity principle proof. -/
private theorem ringChoosePoly_eval_nat (k n : ℕ) :
    (Polynomial.C (((k.factorial : ℚ)⁻¹)) * descPochhammer ℚ k).eval (n : ℚ) = Nat.choose n k := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [descPochhammer_eval_eq_descFactorial]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  simp only [Nat.cast_mul]
  field_simp

/-- The coefficient of (1+X)^n at position k equals Nat.choose n k.
    This is a standard result connecting power series coefficients to binomial coefficients. -/
private theorem coeff_one_add_X_pow_nat' (k n : ℕ) :
    coeff k ((1 + X : ℚ⟦X⟧) ^ n) = (Nat.choose n k : ℚ) := by
  have heq : ((1 : PowerSeries ℚ) + X) ^ n =
      (((1 : Polynomial ℚ) + Polynomial.X) ^ n).toPowerSeries := by
    induction n with
    | zero => simp only [pow_zero, Polynomial.coe_one]
    | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      simp only [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [heq, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- logSeries has order 1 (its lowest nonzero coefficient is at X^1).
    This is used to show that logSeries^m has order ≥ m. -/
private theorem logSeries_order_eq_one : (logSeries (K := ℚ)).order = 1 := by
  rw [order_eq]
  constructor
  · intro i hi
    simp only [Nat.cast_eq_one] at hi
    rw [hi, coeff_logSeries]
    simp
  · intro i hi
    simp only [Nat.cast_lt_one] at hi
    rw [hi, coeff_logSeries]
    simp

/-- logSeries^m has order ≥ m, since logSeries has order 1.
    This implies coeff k (logSeries^m) = 0 for k < m. -/
private theorem logSeries_pow_order_ge (m : ℕ) : (logSeries (K := ℚ) ^ m).order ≥ m := by
  have h1 : (logSeries (K := ℚ)).order = 1 := logSeries_order_eq_one
  have h2 : (logSeries (K := ℚ) ^ m).order ≥ m • (logSeries (K := ℚ)).order := by
    rw [order_eq_order, order_eq_order]
    exact MvPowerSeries.le_order_pow m
  calc (logSeries (K := ℚ) ^ m).order
      ≥ m • (logSeries (K := ℚ)).order := h2
    _ = m • (1 : ℕ∞) := by rw [h1]
    _ = m := by simp

/-- For m > k, coeff k (logSeries^m) = 0.
    This is because logSeries^m has order ≥ m > k. -/
private theorem logSeries_pow_coeff_zero (k m : ℕ) (hm : m > k) :
    coeff k ((logSeries (K := ℚ)) ^ m) = 0 := by
  have h : (k : ℕ∞) < (logSeries (K := ℚ) ^ m).order := by
    calc (k : ℕ∞) < m := by exact_mod_cast hm
      _ ≤ (logSeries ^ m).order := logSeries_pow_order_ge m
  exact coeff_of_lt_order k h

/-- logSeries over ℚ. This is the base version that maps to logSeries K under algebraMap. -/
private noncomputable def logSeriesQ : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else ((-1 : ℚ)^(n-1) / n)

omit [BinomialRing K] [CharZero K] in
/-- logSeries K is the image of logSeriesQ under algebraMap -/
private theorem logSeries_eq_map_logSeriesQ :
    logSeries (K := K) = map (algebraMap ℚ K) logSeriesQ := by
  ext n
  simp only [logSeries, logSeriesQ, coeff_map, coeff_mk]
  split_ifs <;> simp

omit [BinomialRing K] [CharZero K] in
/-- Powers of logSeries K are images of powers of logSeriesQ -/
private theorem logSeries_pow_eq_map_logSeriesQ_pow (d : ℕ) :
    (logSeries (K := K))^d = map (algebraMap ℚ K) (logSeriesQ^d) := by
  rw [logSeries_eq_map_logSeriesQ, RingHom.map_pow]

omit [BinomialRing K] [CharZero K] in
/-- Coefficients of powers of logSeries K are images of coefficients of logSeriesQ -/
private theorem coeff_logSeries_pow_eq_map (d k : ℕ) :
    coeff k ((logSeries (K := K))^d) = algebraMap ℚ K (coeff k (logSeriesQ^d)) := by
  rw [logSeries_pow_eq_map_logSeriesQ_pow, coeff_map]

/-- The polynomial for Ring.choose: Q_k(X) = (1/k!) * descPochhammer(X, k) over ℚ.
    This polynomial, when mapped to K and evaluated at c, gives Ring.choose c k. -/
private noncomputable def choosePoly (k : ℕ) : Polynomial ℚ :=
  (k.factorial : ℚ)⁻¹ • (descPochhammer ℚ k)

/-- The polynomial for coeff k (fpsPow (1+X) c).
    This is ∑_{d=0}^k (coeff d exp • coeff k (logSeriesQ^d)) • X^d.
    When evaluated at c, this gives coeff k (fpsExp (c • logSeries)). -/
private noncomputable def coeffExpPoly (k : ℕ) : Polynomial ℚ :=
  ∑ d ∈ Finset.range (k + 1),
    Polynomial.C (coeff d (exp ℚ) * coeff k (logSeriesQ^d)) * Polynomial.X^d

omit [BinomialRing K] [CharZero K] in
/-- coeffExpPoly k evaluated at c equals coeff k (fpsExp (c • logSeries)).
    This is the key lemma showing the LHS coefficient is a polynomial function. -/
theorem coeff_fpsPow_eq_coeffExpPoly_eval (k : ℕ) (c : K) :
    coeff k ((exp K).subst (c • logSeries (K := K))) =
    ((coeffExpPoly k).map (algebraMap ℚ K)).eval c := by
  -- First, express the coefficient using coeff_subst'
  have hsub : HasSubst (c • logSeries (K := K)) := by
    apply HasSubst.of_constantCoeff_zero
    have h1 : MvPowerSeries.constantCoeff (c • logSeries (K := K)) =
              c • MvPowerSeries.constantCoeff (logSeries (K := K)) := by
      simp only [MvPowerSeries.constantCoeff_smul]
    rw [h1, smul_eq_mul]
    have h2 : MvPowerSeries.constantCoeff (logSeries (K := K)) =
              constantCoeff (logSeries (K := K)) := rfl
    rw [h2, constantCoeff_logSeries, mul_zero]
  rw [coeff_subst' hsub]
  -- The finsum is actually a finite sum over range (k+1)
  have hsupp : (fun d => coeff d (exp K) • coeff k ((c • logSeries (K := K))^d)).support ⊆
               Finset.range (k + 1) := by
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    push Not at h
    have hzero : coeff k ((c • logSeries (K := K))^d) = 0 := by
      rw [coeff_smul_pow, coeff_logSeries_pow_eq_zero_of_gt k d h, smul_zero]
    rw [hzero, smul_zero] at hd
    exact hd rfl
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  -- Now show the sums are equal
  unfold coeffExpPoly
  rw [Polynomial.map_sum, Polynomial.eval_finsetSum]
  congr 1
  ext d
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
             Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  rw [coeff_smul_pow, smul_eq_mul, smul_eq_mul]
  -- Need to show: coeff d (exp K) * c^d * coeff k (logSeries^d) =
  --               algebraMap (coeff d (exp ℚ) * coeff k (logSeriesQ^d)) * c^d
  rw [coeff_logSeries_pow_eq_map d k]
  -- coeff d (exp K) = algebraMap ℚ K (1 / d!)
  -- coeff d (exp ℚ) = 1 / d!
  simp only [coeff_exp, map_mul]
  -- Simplify algebraMap ℚ ℚ to id
  have hid : algebraMap ℚ ℚ = RingHom.id ℚ := rfl
  simp only [hid, RingHom.id_apply, one_div]
  ring


/-- Ring.choose c k equals the evaluation of choosePoly.map at c.
    This is the key lemma showing Ring.choose is a polynomial function. -/
theorem Ring_choose_eq_choosePoly_eval (k : ℕ) (c : K) :
    Ring.choose c k = ((choosePoly k).map (algebraMap ℚ K)).eval c := by
  simp only [choosePoly, Polynomial.map_smul, Polynomial.eval_smul, smul_eq_mul]
  have hmap : (descPochhammer ℚ k).map (algebraMap ℚ K) = descPochhammer K k := by
    rw [descPochhammer_map]
  rw [hmap]
  have h := Ring.descPochhammer_eq_factorial_smul_choose c k
  have h2 : (descPochhammer ℤ k).smeval c = (descPochhammer K k).eval c :=
    descPochhammer_smeval_eq_eval k c
  rw [h2] at h
  have hfac : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hfacK : algebraMap ℚ K (k.factorial : ℚ) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap ℚ K)]
    exact (algebraMap ℚ K).injective.ne hfac
  have h3 : k.factorial • Ring.choose c k = algebraMap ℚ K (k.factorial : ℚ) * Ring.choose c k := by
    rw [Algebra.smul_def]; simp
  rw [h3] at h
  have h5 : algebraMap ℚ K (k.factorial : ℚ) * Ring.choose c k = (descPochhammer K k).eval c := h.symm
  have h6 : Ring.choose c k = algebraMap ℚ K (k.factorial : ℚ)⁻¹ *
      (algebraMap ℚ K (k.factorial : ℚ) * Ring.choose c k) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hfac, map_one, one_mul]
  rw [h6, h5]

omit [BinomialRing K] in
/-- Key: if two polynomial evaluations agree on all naturals, the polynomials are equal -/
theorem poly_eq_of_nat_eval_eq (p q : Polynomial ℚ)
    (h : ∀ n : ℕ, (p.map (algebraMap ℚ K)).eval (n : K) = (q.map (algebraMap ℚ K)).eval (n : K)) :
    p = q := by
  have hdiff : ∀ n : ℕ, ((p - q).map (algebraMap ℚ K)).eval (n : K) = 0 := by
    intro n
    simp only [Polynomial.map_sub, Polynomial.eval_sub, h n, sub_self]
  have hzero : p - q = 0 := polynomial_zero_of_nat_roots (p - q) hdiff
  exact sub_eq_zero.mp hzero

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- Helper lemma: coefficient of (1+X) * f at position k+1 equals sum of coefficients -/
private lemma coeff_one_add_X_mul (f : K⟦X⟧) (k : ℕ) :
    coeff (k + 1) ((1 + X) * f) = coeff (k + 1) f + coeff k f := by
  have h1 : (1 + X : K⟦X⟧) * f = f + X * f := by ring
  rw [h1, map_add]
  congr 1
  rw [mul_comm, coeff_succ_mul_X]

omit [Algebra ℚ K] [CharZero K] in
/-- Pascal identity for Ring.choose: C(c, k+1) = C(c-1, k) + C(c-1, k+1) -/
lemma Ring_choose_pascal (c : K) (k : ℕ) :
    Ring.choose c (k + 1) = Ring.choose (c - 1) k + Ring.choose (c - 1) (k + 1) := by
  have h := Ring.choose_succ_succ (c - 1) k
  simp only [sub_add_cancel] at h
  exact h

omit [BinomialRing K] in
omit [CharZero K] in
/-- Pascal identity for fpsPow coefficients: coeff (k+1) ((1+X)^c) = coeff k ((1+X)^(c-1)) + coeff (k+1) ((1+X)^(c-1)) -/
lemma fpsPow_coeff_pascal (c : K) (k : ℕ) :
    coeff (k + 1) ((1 + X : K⟦X⟧) ^ᶠ c) =
    coeff k ((1 + X : K⟦X⟧) ^ᶠ (c - 1)) + coeff (k + 1) ((1 + X : K⟦X⟧) ^ᶠ (c - 1)) := by
  -- (1+X)^c = (1+X) * (1+X)^(c-1)
  have h1 : c = 1 + (c - 1) := by ring
  conv_lhs => rw [h1]
  rw [fpsPow_add hasConstantTermOne_one_add_X, fpsPow_one hasConstantTermOne_one_add_X]
  rw [coeff_one_add_X_mul]
  ring


/-- The generalized Newton binomial formula: (1+x)^c = ∑_{k ∈ ℕ} C(c,k) x^k

    This extends the standard Newton binomial formula (Theorem thm.fps.newton-binom)
    from natural number exponents to arbitrary exponents in a ℚ-algebra.

    The proof uses the polynomial identity trick: both sides of the coefficient equality
    are polynomials in c that agree on ℕ (by the standard Newton formula), hence they
    agree everywhere.

    **Proof outline:**
    For each coefficient `k`, we need to show `coeff k ((1+X)^c) = Ring.choose c k`.

    1. Both sides are polynomial functions of `c` with rational coefficients:
       - `Ring.choose c k = descPochhammer(c, k) / k!` is a polynomial of degree `k`
       - `coeff k (fpsExp (c • logSeries))` is also a polynomial in `c` (by expanding
         the exponential series and collecting terms)

    2. For natural `c = n`, both sides equal `Nat.choose n k`:
       - `Ring.choose n k = Nat.choose n k` by `Ring.choose_natCast`
       - `coeff k ((1+X)^n) = Nat.choose n k` by the standard binomial theorem

    3. By the polynomial identity trick: two polynomials (over ℚ) that agree on all
       natural numbers must be equal. Hence the coefficients agree for all `c ∈ K`.

    Label: thm.fps.gen-newton -/
theorem generalizedNewtonBinomial (c : K) :
    (1 + X : K⟦X⟧) ^ᶠ c = binomialSeries K c := by
  -- We prove by showing both sides have the same coefficients.
  ext k
  -- The RHS coefficient is Ring.choose c k.
  rw [binomialSeries_coeff, smul_eq_mul, mul_one]
  -- For natural n, both sides give Nat.choose n k = Ring.choose n k.
  -- LHS: fpsPow (1+X) n = (1+X)^n (by fpsPow_nat)
  --      coeff k ((1+X)^n) = Nat.choose n k
  -- RHS: Ring.choose n k = Nat.choose n k (by Ring.choose_natCast)
  have h_nat : ∀ n : ℕ, coeff k ((1 + X : K⟦X⟧) ^ᶠ (n : K)) = Ring.choose (n : K) k := by
    intro n
    rw [fpsPow_nat' hasConstantTermOne_one_add_X n]
    -- coeff k ((1+X)^n) = Nat.choose n k
    have hpoly : (1 + X : K⟦X⟧) ^ n =
        (((1 : Polynomial K) + Polynomial.X) ^ n).toPowerSeries := by simp
    rw [hpoly, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, Ring.choose_natCast]
  -- Both coeff k (fpsPow (1+X) c) and Ring.choose c k are polynomial in c
  -- (of degree ≤ k) and agree on all natural numbers.
  -- By the polynomial identity principle, they are equal.
  --
  -- For Ring.choose c k: by Ring.descPochhammer_eq_factorial_smul_choose,
  -- k! • Ring.choose c k = (descPochhammer ℤ k).smeval c, so Ring.choose c k
  -- is the evaluation of (1/k!) * descPochhammer at c.
  --
  -- For coeff k (fpsPow (1+X) c) = coeff k (exp.subst (c • logSeries)):
  -- Since logSeries has ℚ-coefficients and exp has ℚ-coefficients,
  -- the k-th coefficient is ∑_{m=0}^k c^m * b_m for some b_m ∈ ℚ,
  -- which is a polynomial in c of degree ≤ k.
  --
  -- Both polynomials agree on infinitely many points (all of ℕ).
  -- By Polynomial.eq_zero_of_infinite_isRoot, the difference is 0.
  -- Hence the polynomials are equal, and so are the evaluations.
  --
  -- For coefficient k, both sides satisfy the Chu-Vandermonde identity:
  -- coeff k (F(a+b)) = ∑_{i=0}^k coeff i (F(a)) * coeff (k-i) (F(b))
  -- (fpsPow (1+X) by convolution, binomialSeries K by Ring.add_choose_eq).
  -- Combined with agreement on ℕ, this uniquely determines the coefficient.
  --
  -- The proof uses the polynomial identity principle:
  -- Both f(c) = coeff k (fpsPow (1+X) c) and g(c) = Ring.choose c k are
  -- polynomial functions of c (of degree ≤ k) that agree on all n ∈ ℕ.
  -- Since there are infinitely many natural numbers and the polynomials
  -- have finite degree, they must be equal (by the polynomial identity
  -- principle over ℚ, which extends to any ℚ-algebra K).
  --
  -- The polynomial for g(c) = Ring.choose c k is explicit:
  -- g(c) = (1/k!) * c(c-1)(c-2)...(c-k+1) = (1/k!) * descPochhammer(c, k)
  --
  -- The polynomial for f(c) = coeff k (fpsPow (1+X) c) comes from:
  -- fpsPow (1+X) c = exp.subst (c • logSeries)
  -- = ∑_{m≥0} (c • logSeries)^m / m!
  -- = ∑_{m≥0} c^m • logSeries^m / m!
  -- So coeff k (fpsPow (1+X) c) = ∑_{m=0}^k c^m • coeff k (logSeries^m) / m!
  -- which is a polynomial in c of degree ≤ k with ℚ-coefficients.
  --
  -- Since f(n) = g(n) for all n ∈ ℕ (by h_nat), and both are polynomials
  -- of degree ≤ k, they must be equal.
  --
  -- The base case k = 0 follows from both sides being 1.
  -- The inductive step uses the polynomial identity principle.
  cases k with
    | zero =>
      -- coeff 0 (fpsPow (1+X) c) = constantCoeff (fpsPow (1+X) c) = 1
      have h1 : HasConstantTermOne ((1 + X : K⟦X⟧) ^ᶠ c) :=
        hasConstantTermOne_fpsPow hasConstantTermOne_one_add_X c
      simp only [HasConstantTermOne, ← coeff_zero_eq_constantCoeff_apply] at h1
      rw [h1, Ring.choose_zero_right]
      | succ k =>
        -- For k+1, we use the polynomial identity principle.
        -- Both coeff (k+1) (fpsPow (1+X) c) and Ring.choose c (k+1) are
        -- polynomial functions of c of degree ≤ k+1 that agree on all n ∈ ℕ.
        --
        -- By coeff_fpsPow_eq_coeffExpPoly_eval:
        --   coeff (k+1) ((1+X)^ᶠ c) = ((coeffExpPoly (k+1)).map (algebraMap ℚ K)).eval c
        -- By Ring_choose_eq_choosePoly_eval:
        --   Ring.choose c (k+1) = ((choosePoly (k+1)).map (algebraMap ℚ K)).eval c
        --
        -- We need to show these two polynomial evaluations are equal.
        -- By poly_eq_of_nat_eval_eq, it suffices to show they agree on all naturals.
        -- But this is exactly h_nat!
        rw [fpsPow_one_add_X' c]
        unfold fpsExp
        rw [coeff_fpsPow_eq_coeffExpPoly_eval (k + 1) c]
        rw [Ring_choose_eq_choosePoly_eval (k + 1) c]
        -- Now both sides are polynomial evaluations, and they agree on all naturals
        -- We need to show coeffExpPoly (k+1) = choosePoly (k+1)
        have hpoly : coeffExpPoly (k + 1) = choosePoly (k + 1) := by
          apply poly_eq_of_nat_eval_eq (K := K)
          intro n
          -- For naturals, both polynomials evaluate to the same thing
          rw [← Ring_choose_eq_choosePoly_eval (k + 1) (n : K)]
          rw [← coeff_fpsPow_eq_coeffExpPoly_eval (k + 1) (n : K)]
          -- Goal: coeff (k+1) ((exp K).subst (n • logSeries)) = Ring.choose n (k+1)
          -- We have h_nat n : coeff (k+1) ((1+X)^ᶠ n) = Ring.choose n (k+1)
          -- And fpsPow_one_add_X' n : (1+X)^ᶠ n = fpsExp (n • logSeries)
          -- And fpsExp g = (exp K).subst g
          have h1 := h_nat n
          rw [fpsPow_one_add_X' (n : K)] at h1
          unfold fpsExp at h1
          exact h1
        rw [hpoly]

/-- Corollary: coefficient of x^k in (1+x)^c is C(c,k)
    Label: thm.fps.gen-newton (coefficient form) -/
theorem coeff_one_add_X_fpsPow (c : K) (k : ℕ) :
    coeff k ((1 + X : K⟦X⟧) ^ᶠ c) = Ring.choose c k := by
  rw [generalizedNewtonBinomial]
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one]

/-!
## Application: The Catalan Number Generating Function

The equation C = 1 + xC² for the Catalan generating function has solution
C = (1 - √(1-4x))/(2x) = (1 - (1-4x)^{1/2})/(2x)

This is now rigorous using our definition of non-integer powers.
-/

/-- The square root of 1-4x as an FPS.
    √(1-4x) = (1-4x)^{1/2} = (1 + (-4x))^{1/2}
    Label: eq.sec.gf.exas.2.(1+x)1/2 -/
noncomputable def sqrtOneMinusFourX : ℚ⟦X⟧ :=
  (1 + (-4 : ℚ) • X) ^ᶠ (1/2 : ℚ)

/-- 1-4x has constant term 1, so its square root is well-defined -/
theorem hasConstantTermOne_oneMinusFourX : HasConstantTermOne (1 + (-4 : ℚ) • X : ℚ⟦X⟧) := by
  simp [HasConstantTermOne]

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- Helper: subst X f = f -/
private lemma subst_X_eq_self' (f : K⟦X⟧) : f.subst (X : K⟦X⟧) = f := by
  have h1 : f.subst (X : K⟦X⟧) = f.map (algebraMap K K) := by
    rw [← map_algebraMap_eq_subst_X]
  have h2 : algebraMap K K = RingHom.id K := rfl
  rw [h1, h2]
  ext n
  simp only [coeff_map, RingHom.id_apply]

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- Helper: f.subst (a • X) = rescale a f -/
private lemma subst_smul_X_eq_rescale' (g : K⟦X⟧) (a : K) :
    g.subst (a • X) = rescale a g := by
  ext n
  rw [coeff_subst' (HasSubst.smul_X' a), coeff_rescale]
  have h1 : ∀ d, (coeff d) g • (coeff n) ((a • X) ^ d) = if d = n then a^n * (coeff n) g else 0 := by
    intro d
    rw [smul_pow]
    simp only [smul_eq_mul, coeff_smul, coeff_X_pow]
    split_ifs with h1 h2
    · simp [h1, mul_comm]
    · omega
    · omega
    · simp
  simp_rw [h1]
  rw [finsum_eq_single _ n]
  · simp
  · intro d hd
    simp [hd]

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- Helper: f.subst (rescale a g) = rescale a (f.subst g) -/
private lemma subst_rescale' (a : K) (f g : K⟦X⟧) (hg : constantCoeff g = 0) :
    f.subst (rescale a g) = rescale a (f.subst g) := by
  ext n
  have hag : constantCoeff (rescale a g) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
        coeff_zero_eq_constantCoeff_apply, hg]
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero hag),
      coeff_rescale,
      coeff_subst' (HasSubst.of_constantCoeff_zero hg)]
  have h1 : ∀ d, coeff n ((rescale a g) ^ d) = a^n * coeff n (g^d) := by
    intro d
    rw [← RingHom.map_pow, coeff_rescale]
  simp_rw [h1, smul_eq_mul]
  have h2 : ∀ d, (coeff d) f * (a ^ n * (coeff n) (g ^ d)) = a ^ n * ((coeff d) f * (coeff n) (g ^ d)) := by
    intro d; ring
  simp_rw [h2]
  have hfin : (Function.support fun d => (coeff d) f * (coeff n) (g ^ d)).Finite :=
    coeff_subst_finite' (HasSubst.of_constantCoeff_zero hg) f n
  have hfin2 : (Function.support fun d => a ^ n * ((coeff d) f * (coeff n) (g ^ d))).Finite := by
    apply Set.Finite.subset hfin
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd ⊢
    intro h; apply hd; simp [h]
  rw [finsum_eq_sum _ hfin2, finsum_eq_sum _ hfin, Finset.mul_sum]
  apply Finset.sum_subset
  · intro d hd
    simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq] at hd ⊢
    intro h; apply hd; simp [h]
  · intro d _ hd
    simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, not_not] at hd
    simp [hd]

omit [BinomialRing K] [CharZero K] in
/-- Helper: fpsLog (1 + a • X) = rescale a (fpsLog (1 + X)) -/
private lemma fpsLog_one_add_smul_X' (a : K) :
    fpsLog (1 + a • X : K⟦X⟧) = rescale a (fpsLog (1 + X : K⟦X⟧)) := by
  unfold fpsLog
  simp only [add_sub_cancel_left]
  rw [← subst_smul_X_eq_rescale']
  congr 1
  exact (subst_X_eq_self' logSeries).symm

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- Helper: c • rescale a g = rescale a (c • g) -/
private lemma smul_rescale' (c a : K) (g : K⟦X⟧) : c • rescale a g = rescale a (c • g) := by
  ext n
  simp only [coeff_smul, coeff_rescale, smul_eq_mul]
  ring

omit [BinomialRing K] [CharZero K] in
/-- Helper: constantCoeff of fpsLog (1 + X) is 0 -/
private lemma constantCoeff_fpsLog_one_add_X' :
    constantCoeff (fpsLog (1 + X : K⟦X⟧)) = 0 := by
  unfold fpsLog
  simp only [add_sub_cancel_left]
  rw [subst_X_eq_self']
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [logSeries, coeff_mk]

omit [BinomialRing K] [CharZero K] in
/-- Helper: fpsExp (rescale a g) = rescale a (fpsExp g) when g has constant term 0 -/
private lemma fpsExp_rescale' (a : K) (g : K⟦X⟧) (hg : constantCoeff g = 0) :
    fpsExp (rescale a g) = rescale a (fpsExp g) := by
  unfold fpsExp
  rw [subst_rescale' a (exp K) g hg]

omit [BinomialRing K] [CharZero K] in
/-- The key lemma: fpsPow (1 + a • X) c = rescale a (fpsPow (1 + X) c) -/
private lemma fpsPow_one_add_smul_X' (a c : K) :
    (1 + a • X : K⟦X⟧) ^ᶠ c = rescale a ((1 + X : K⟦X⟧) ^ᶠ c) := by
  unfold fpsPow
  rw [fpsLog_one_add_smul_X', smul_rescale']
  apply fpsExp_rescale'
  rw [constantCoeff_smul, constantCoeff_fpsLog_one_add_X', smul_zero]

/-- Coefficient formula for (1 + a • X)^c -/
private lemma coeff_fpsPow_one_add_smul_X' (a c : K) (k : ℕ) :
    coeff k ((1 + a • X : K⟦X⟧) ^ᶠ c) = Ring.choose c k * a^k := by
  rw [fpsPow_one_add_smul_X', coeff_rescale, generalizedNewtonBinomial, binomialSeries_coeff,
      smul_eq_mul, mul_one, mul_comm]

/-- The coefficient of x^k in √(1-4x) is C(1/2, k) * (-4)^k -/
theorem coeff_sqrtOneMinusFourX (k : ℕ) :
    coeff k sqrtOneMinusFourX = Ring.choose (1/2 : ℚ) k * (-4)^k := by
  unfold sqrtOneMinusFourX
  exact coeff_fpsPow_one_add_smul_X' (-4) (1/2) k

/-!
## Another Application: A Binomial Identity (Proposition prop.binom.nCk-2i-qedmo.CN)

For n ∈ ℂ and k ∈ ℕ:
∑_{i=0}^k C(n+i-1, i) C(n, k-2i) = C(n+k-1, k)

The proof uses generating functions:
- Define f = ∑_{i ∈ ℕ} C(n+i-1, i) x^{2i} = (1-x²)^{-n}
- Define g = ∑_{j ∈ ℕ} C(n, j) x^j = (1+x)^n
- Then fg = (1-x)^{-n} = ∑_{i ∈ ℕ} C(n+i-1, i) x^i
- Comparing coefficients of x^k gives the identity
-/

/-- The anti-Newton binomial formula: (1+x)^{-n} = ∑_{i ∈ ℕ} (-1)^i C(n+i-1, i) x^i
    This is a consequence of the generalized Newton formula.
    Label: prop.fps.anti-newton-binom -/
theorem antiNewtonBinomial (n : K) :
    (1 + X : K⟦X⟧) ^ᶠ (-n) = PowerSeries.mk fun i =>
      (-1 : K)^i * Ring.choose (n + i - 1) i := by
  rw [generalizedNewtonBinomial]
  ext i
  simp only [binomialSeries_coeff, smul_eq_mul, mul_one, coeff_mk]
  rw [Ring.choose_neg]
  simp only [Units.smul_def, Int.negOnePow_def]
  simp

/-!
### Helper Lemmas for the Binomial Identity

We prove the identity using generating functions:
- Define f = ∑_{i ∈ ℕ} C(n+i-1, i) x^{2i}
- Define g = ∑_{j ∈ ℕ} C(n, j) x^j = (1+x)^n
- Show that fg = (1-x)^{-n} using the factorization (1-x²) = (1-x)(1+x)
- Compare coefficients of x^k
-/

omit [Algebra ℚ K] [CharZero K] in
/-- (1-x)^{-n} has coefficient C(n+k-1, k) at position k.
    This is rescale (-1) applied to (1+x)^{-n}. -/
theorem one_sub_X_pow_neg_coeff (n : K) (k : ℕ) :
    coeff k (rescale (-1 : K) (binomialSeries K (-n))) = Ring.choose (n + k - 1) k := by
  rw [coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one]
  rw [Ring.choose_neg]
  simp only [Units.smul_def, Int.negOnePow_def, zsmul_eq_mul]
  have h : (((-1 : ℤˣ) ^ (k : ℤ) : ℤˣ) : K) = (-1 : K) ^ k := by
    simp only [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_pow,
      Int.cast_neg, Int.cast_one]
  rw [h]
  have h2 : (-1 : K) ^ k * (-1 : K) ^ k = 1 := by
    rw [← pow_add, ← two_mul]; simp [pow_mul]
  calc (-1 : K) ^ k * ((-1) ^ k * Ring.choose (n + k - 1) k)
      = ((-1) ^ k * (-1) ^ k) * Ring.choose (n + k - 1) k := by ring
    _ = 1 * Ring.choose (n + k - 1) k := by rw [h2]
    _ = Ring.choose (n + k - 1) k := by ring

/-- The series f = ∑_i C(n+i-1, i) x^{2i} used in the proof -/
noncomputable def f_series' (n : K) : K⟦X⟧ :=
  mk fun m => if Even m then Ring.choose (n + ((m/2 : ℕ) : K) - 1) (m/2) else 0

/-- The series g = (1+x)^n = binomialSeries K n -/
noncomputable def g_series' (n : K) : K⟦X⟧ := binomialSeries K n

set_option backward.isDefEq.respectTransparency false in
omit [Algebra ℚ K] [CharZero K] in
/-- The coefficient of x^k in f * g equals the LHS of the binomial identity -/
theorem coeff_f_mul_g' (n : K) (k : ℕ) :
    coeff k (f_series' n * g_series' n) =
    ∑ i ∈ range (k / 2 + 1), Ring.choose (n + i - 1) i * Ring.choose n (k - 2*i) := by
  rw [coeff_mul]
  simp only [f_series', g_series', coeff_mk, binomialSeries_coeff, smul_eq_mul, mul_one]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun m j =>
    (if Even m then Ring.choose (n + ((m/2 : ℕ) : K) - 1) (m/2) else 0) * Ring.choose n j)]
  have h : ∀ m,
    (if Even m then Ring.choose (n + ((m/2 : ℕ) : K) - 1) (m/2) else 0) * Ring.choose n (k - m) =
    if Even m then Ring.choose (n + ((m/2 : ℕ) : K) - 1) (m/2) * Ring.choose n (k - m) else 0 := by
    intro m; split_ifs with he <;> [rfl; simp]
  simp_rw [h]
  rw [sum_ite, filter_not]; simp only [sum_const_zero, add_zero]
  have hbij : (range (k + 1)).filter Even = (range (k / 2 + 1)).map
      ⟨(2 * ·), fun _ _ h => Nat.eq_of_mul_eq_mul_left (by norm_num) h⟩ := by
    ext m
    simp only [mem_filter, mem_range, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨hm, he⟩; obtain ⟨i, rfl⟩ := he; exact ⟨i, by omega, by ring⟩
    · intro ⟨i, hi, him⟩; constructor; omega; exact ⟨i, by omega⟩
  rw [hbij, sum_map]
  apply sum_congr rfl
  intro i _
  simp only [Function.Embedding.coeFn_mk]
  have h1 : (2 * i) / 2 = i := Nat.mul_div_cancel_left i (by norm_num : 0 < 2)
  simp only [h1]

/-!
### Infrastructure for the Polynomial Identity Principle

The following lemmas establish the connection between binomialSeries and invOneSubPow,
which is needed for proving the coefficient identity using the polynomial identity principle.
-/

omit [Algebra ℚ K] [CharZero K] in
/-- binomialSeries with K and ℤ coefficient rings agree for negative naturals -/
private lemma binomialSeries_neg_nat_eq (N : ℕ) :
    PowerSeries.binomialSeries (R := K) K (-(N : K)) =
    PowerSeries.binomialSeries (R := ℤ) K (-(N : ℤ)) := by
  ext n
  simp only [binomialSeries_coeff, zsmul_one, smul_eq_mul, mul_one]
  have h := Ring.map_choose (Int.castRingHom K) (-(N : ℤ)) n
  simp only [Int.coe_castRingHom] at h
  convert h.symm using 2
  simp only [Int.cast_neg, Int.cast_natCast]

omit [Algebra ℚ K] [CharZero K] in
/-- binomialSeries K (-(N : K)) equals rescale (-1) of invOneSubPow -/
private lemma binomialSeries_neg_nat_eq_rescale_invOneSubPow (N : ℕ) :
    binomialSeries K (-(N : K)) = rescale (-1 : K) ((invOneSubPow K N).val) := by
  rw [binomialSeries_neg_nat_eq]
  exact (rescale_neg_one_invOneSubPow (A := K) N).symm

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- rescale (-1) (rescale (-1) f) = f -/
private lemma rescale_neg_one_neg_one' (f : K⟦X⟧) : rescale (-1 : K) (rescale (-1 : K) f) = f := by
  ext n
  simp only [coeff_rescale]
  have h2 : (-1 : K) ^ n * (-1 : K) ^ n = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨n, rfl⟩
  calc (-1 : K) ^ n * ((-1) ^ n * coeff n f)
      = ((-1) ^ n * (-1) ^ n) * coeff n f := by ring
    _ = 1 * coeff n f := by rw [h2]
    _ = coeff n f := by ring

omit [Algebra ℚ K] [CharZero K] in
/-- rescale (-1) (binomialSeries K (-(N : K))) = (invOneSubPow K N).val -/
private lemma rescale_neg_binomialSeries_neg_nat (N : ℕ) :
    rescale (-1 : K) (binomialSeries K (-(N : K))) = (invOneSubPow K N).val := by
  rw [binomialSeries_neg_nat_eq_rescale_invOneSubPow]
  exact rescale_neg_one_neg_one' _

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- For natural N ≥ 1, the coefficient of X^m in invOneSubPow K N is Nat.choose (N+m-1) m -/
private lemma coeff_invOneSubPow_eq_choose' (N : ℕ) (m : ℕ) (hN : 0 < N) :
    coeff m ((invOneSubPow K N).val) = (Nat.choose (N + m - 1) m : K) := by
  have h := invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos (S := K) (d := N) hN
  rw [h]; simp only [coeff_mk]; congr 1
  have h1 : N - 1 + m = N + m - 1 := by omega
  have h2 : N - 1 = (N + m - 1) - m := by omega
  rw [h1, h2]; exact Nat.choose_symm (by omega : m ≤ N + m - 1)

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- rescale (-1) (1 - X)^N = (1 + X)^N -/
private lemma rescale_neg_one_sub_X_pow' (N : ℕ) :
    rescale (-1 : K) ((1 - X)^N) = (1 + X)^N := by
  rw [map_pow]; congr 1; ext k; simp only [coeff_rescale]
  by_cases hk : k = 0
  · simp [hk]
  · by_cases hk1 : k = 1
    · simp [hk1, coeff_one, coeff_one_X]
    · have h1 : coeff k (1 - X : K⟦X⟧) = 0 := by
        simp only [map_sub, coeff_one, coeff_X, hk, ↓reduceIte, hk1, sub_zero]
      have h2 : coeff k (1 + X : K⟦X⟧) = 0 := by
        simp only [map_add, coeff_one, coeff_X, hk, ↓reduceIte, hk1, add_zero]
      simp [h1, h2]

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- (1-X)^N * (1+X)^N = (1-X²)^N -/
private lemma one_sub_X_pow_mul_one_add_X_pow' (N : ℕ) :
    (1 - X : K⟦X⟧)^N * (1 + X)^N = (1 - X^2)^N := by
  rw [← mul_pow]; ring

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- The product (invOneSubPow K N).val * rescale (-1) (invOneSubPow K N).val
    times (1 - X²)^N equals 1. This shows the product is the inverse of (1 - X²)^N. -/
lemma invOneSubPow_mul_rescale_mul_one_sub_sq_pow' (N : ℕ) :
    (invOneSubPow K N).val * rescale (-1 : K) (invOneSubPow K N).val * (1 - X^2)^N = 1 := by
  rw [← one_sub_X_pow_mul_one_add_X_pow']
  have h1 : (invOneSubPow K N).val * (1 - X)^N = 1 := by
    rw [← invOneSubPow_inv_eq_one_sub_pow]; exact (invOneSubPow K N).val_inv
  have h2 : rescale (-1 : K) (invOneSubPow K N).val * (1 + X)^N = 1 := by
    rw [← rescale_neg_one_sub_X_pow', ← (rescale (-1 : K)).map_mul,
        ← invOneSubPow_inv_eq_one_sub_pow, (invOneSubPow K N).val_inv, (rescale (-1 : K)).map_one]
  calc (invOneSubPow K N).val * rescale (-1 : K) (invOneSubPow K N).val *
       ((1 - X)^N * (1 + X)^N)
     = ((invOneSubPow K N).val * (1 - X)^N) *
       (rescale (-1 : K) (invOneSubPow K N).val * (1 + X)^N) := by ring
   _ = 1 * 1 := by rw [h1, h2]
   _ = 1 := by ring

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- expand 2 (1 - X) = 1 - X², since expand substitutes X² for X. -/
private lemma expand_one_sub_X : expand 2 two_ne_zero (1 - X : K⟦X⟧) = 1 - X^2 := by
  ext k
  simp only [map_sub, expand_X, coeff_one, coeff_X_pow]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    by_cases hk2 : k = 2
    · simp [hk2]
    · simp only [hk2, ↓reduceIte, sub_zero]
      rw [coeff_expand]
      simp only [coeff_one]
      split_ifs with h1 h2
      · have : k = 0 := by obtain ⟨m, hm⟩ := h1; simp only [hm] at h2; omega
        exact absurd this hk
      · rfl
      · rfl

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- expand 2 (invOneSubPow K N).val = (1 - X²)^{-N}, i.e., the inverse of (1 - X²)^N.
    This follows from expand 2 being a ring homomorphism that maps (1 - X) to (1 - X²). -/
lemma expand_invOneSubPow_eq_inv_one_sub_X_sq (N : ℕ) :
    expand 2 two_ne_zero ((invOneSubPow K N).val) * (1 - X^2)^N = 1 := by
  have h1 : (1 - X^2 : K⟦X⟧)^N = expand 2 two_ne_zero ((1 - X)^N) := by
    rw [map_pow, expand_one_sub_X]
  rw [h1]
  have h2 : expand 2 two_ne_zero ((invOneSubPow K N).val) * expand 2 two_ne_zero ((1 - X)^N) = 
            expand 2 two_ne_zero ((invOneSubPow K N).val * (1 - X)^N) := 
    ((expand 2 two_ne_zero).map_mul _ _).symm
  rw [h2, ← invOneSubPow_inv_eq_one_sub_pow, (invOneSubPow K N).val_inv]
  simp only [map_one]

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- The product (invOneSubPow K N).val * rescale (-1) (invOneSubPow K N).val
    equals expand 2 (invOneSubPow K N).val.

    Both are inverses of (1 - X²)^N:
    - The product: by invOneSubPow_mul_rescale_mul_one_sub_sq_pow'
    - The expand: by expand_invOneSubPow_eq_inv_one_sub_X_sq

    Since the inverse is unique (when it exists), they must be equal. -/
lemma product_eq_expand_invOneSubPow (N : ℕ) :
    (invOneSubPow K N).val * rescale (-1 : K) ((invOneSubPow K N).val) =
    expand 2 two_ne_zero ((invOneSubPow K N).val) := by
  -- Both are inverses of (1 - X²)^N
  have h1 : (invOneSubPow K N).val * rescale (-1 : K) (invOneSubPow K N).val * (1 - X^2)^N = 1 :=
    invOneSubPow_mul_rescale_mul_one_sub_sq_pow' N
  have h2 : expand 2 two_ne_zero ((invOneSubPow K N).val) * (1 - X^2)^N = 1 :=
    expand_invOneSubPow_eq_inv_one_sub_X_sq N
  have hunit : IsUnit ((1 - X^2 : K⟦X⟧)^N) := by
    rw [isUnit_iff_constantCoeff]
    have h : constantCoeff ((1 - X^2 : K⟦X⟧)^N) = 1 := by
      simp only [map_pow, map_sub, constantCoeff_one, constantCoeff_X]; norm_num
    simp [h]
  obtain ⟨u, hu⟩ := hunit
  have ha : (invOneSubPow K N).val * rescale (-1 : K) (invOneSubPow K N).val = u⁻¹.val := by
    rw [← hu] at h1
    have : (invOneSubPow K N).val * rescale (-1 : K) (invOneSubPow K N).val * u = 1 := h1
    calc (invOneSubPow K N).val * rescale (-1 : K) (invOneSubPow K N).val 
        = (invOneSubPow K N).val * rescale (-1 : K) (invOneSubPow K N).val * 1 := by ring
      _ = (invOneSubPow K N).val * rescale (-1 : K) (invOneSubPow K N).val * (u * u⁻¹) := by rw [Units.mul_inv]
      _ = ((invOneSubPow K N).val * rescale (-1 : K) (invOneSubPow K N).val * u) * u⁻¹ := by ring
      _ = 1 * u⁻¹ := by rw [this]
      _ = u⁻¹ := by ring
  have hc : expand 2 two_ne_zero ((invOneSubPow K N).val) = u⁻¹.val := by
    rw [← hu] at h2
    have : expand 2 two_ne_zero ((invOneSubPow K N).val) * u = 1 := h2
    calc expand 2 two_ne_zero ((invOneSubPow K N).val)
        = expand 2 two_ne_zero ((invOneSubPow K N).val) * 1 := by ring
      _ = expand 2 two_ne_zero ((invOneSubPow K N).val) * (u * u⁻¹) := by rw [Units.mul_inv]
      _ = (expand 2 two_ne_zero ((invOneSubPow K N).val) * u) * u⁻¹ := by ring
      _ = 1 * u⁻¹ := by rw [this]
      _ = u⁻¹ := by ring
  rw [ha, hc]

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- For natural N ≥ 1, the coefficient of X^{2m} in the product
    (invOneSubPow K N).val * rescale (-1) (invOneSubPow K N).val is Nat.choose (N+m-1) m.
    This follows from the product being (1-X²)^{-N}. -/
lemma coeff_invOneSubPow_product_even' (N m : ℕ) (hN : 0 < N) :
    coeff (m + m) ((invOneSubPow K N).val * rescale (-1 : K) (invOneSubPow K N).val) =
    (Nat.choose (N + m - 1) m : K) := by
  -- Key insight: the product P = (invOneSubPow K N).val * rescale (-1) (invOneSubPow K N).val
  -- equals expand 2 (invOneSubPow K N).val, because both are inverses of (1 - X^2)^N.
  --
  -- By uniqueness of inverses (if a * b = 1 and c * b = 1, then a = c), we have P = expand 2 ...
  -- Then coeff (2m) P = coeff m (invOneSubPow K N).val = Nat.choose (N+m-1) m.
  --
  -- Step 1: Show expand 2 (invOneSubPow K N).val * (1 - X^2)^N = 1
  have h_expand_inv : expand 2 (two_ne_zero) ((invOneSubPow K N).val) * (1 - X^2 : K⟦X⟧)^N = 1 := by
    have h1' : expand 2 (two_ne_zero) ((1 - X : K⟦X⟧)^N) = (1 - X^2)^N := by
      rw [map_pow, map_sub, map_one, expand_X]
    have h2' : (invOneSubPow K N).val * (1 - X)^N = 1 := by
      rw [← invOneSubPow_inv_eq_one_sub_pow]
      exact (invOneSubPow K N).val_inv
    calc expand 2 two_ne_zero ((invOneSubPow K N).val) * (1 - X^2 : K⟦X⟧)^N
        = expand 2 two_ne_zero ((invOneSubPow K N).val) * expand 2 two_ne_zero ((1 - X)^N) := by rw [h1']
      _ = expand 2 two_ne_zero ((invOneSubPow K N).val * (1 - X)^N) := by rw [map_mul]
      _ = expand 2 two_ne_zero 1 := by rw [h2']
      _ = 1 := by simp
  -- Step 2: Show P * (1 - X^2)^N = 1 (using existing lemma invOneSubPow_mul_rescale_mul_one_sub_sq_pow')
  have h_prod_inv : (invOneSubPow K N).val * rescale (-1 : K) ((invOneSubPow K N).val) * (1 - X^2 : K⟦X⟧)^N = 1 :=
    invOneSubPow_mul_rescale_mul_one_sub_sq_pow' N
  -- Step 3: By uniqueness of inverses, P = expand 2 (invOneSubPow K N).val
  have h_eq : (invOneSubPow K N).val * rescale (-1 : K) ((invOneSubPow K N).val) = 
              expand 2 two_ne_zero ((invOneSubPow K N).val) := by
    calc (invOneSubPow K N).val * rescale (-1 : K) ((invOneSubPow K N).val) 
        = (invOneSubPow K N).val * rescale (-1 : K) ((invOneSubPow K N).val) * 1 := by ring
      _ = (invOneSubPow K N).val * rescale (-1 : K) ((invOneSubPow K N).val) * 
          (expand 2 two_ne_zero ((invOneSubPow K N).val) * (1 - X^2 : K⟦X⟧)^N) := by rw [h_expand_inv]
      _ = ((invOneSubPow K N).val * rescale (-1 : K) ((invOneSubPow K N).val) * (1 - X^2 : K⟦X⟧)^N) *
          expand 2 two_ne_zero ((invOneSubPow K N).val) := by ring
      _ = 1 * expand 2 two_ne_zero ((invOneSubPow K N).val) := by rw [h_prod_inv]
      _ = expand 2 two_ne_zero ((invOneSubPow K N).val) := by ring
  -- Step 4: Use the coefficient formula for expand
  rw [h_eq]
  rw [show m + m = 2 * m by ring]
  rw [coeff_expand_mul]
  exact coeff_invOneSubPow_eq_choose' N m hN

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- Helper: alternating sum from 0 to 2m equals 1.
    This is ∑_{i=0}^{2m} (-1)^i = 1, proved by induction. -/
private lemma alternating_sum_range_even (m : ℕ) :
    ∑ i ∈ range (2*m + 1), ((-1 : K) ^ i : K) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [ih]
    have h1 : (-1 : K)^(2*m + 1) = -1 := by rw [pow_add, pow_mul]; simp
    have h2 : (-1 : K)^(2*m + 2) = 1 := by rw [pow_add, pow_mul]; simp
    rw [h1, h2]
    ring

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- The alternating sum over antidiagonal of an even number equals 1.
    This is a key lemma for the coefficient identity in the even case.

    For k = 2m, we have: ∑_{i+j=2m} (-1)^j = 1

    Proof: Since 2m is even, (-1)^j = (-1)^i for any (i,j) with i+j=2m.
    The sum becomes ∑_{i=0}^{2m} (-1)^i = 1 (by alternating_sum_range_even). -/
private lemma alternating_sum_antidiagonal_even (m : ℕ) :
    ∑ x ∈ antidiagonal (2*m), ((-1 : K) ^ x.2 : K) = 1 := by
  have h2m_even : (-1 : K)^(2*m) = 1 := by rw [pow_mul]; simp
  -- Key: for x ∈ antidiagonal (2m), we have (-1)^x.2 = (-1)^x.1
  have h_sym : ∀ x ∈ antidiagonal (2*m), ((-1 : K) ^ x.2 : K) = (-1)^x.1 := by
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h : (-1 : K)^x.1 * (-1)^x.2 = (-1)^(x.1 + x.2) := by rw [← pow_add]
    rw [hx, h2m_even] at h
    -- (-1)^x.1 * (-1)^x.2 = 1, so (-1)^x.2 = (-1)^x.1
    cases Nat.even_or_odd x.1 with
    | inl he =>
      have h1 : (-1 : K)^x.1 = 1 := Even.neg_one_pow he
      rw [h1] at h; rw [one_mul] at h; rw [h1, h]
    | inr ho =>
      have h1 : (-1 : K)^x.1 = -1 := Odd.neg_one_pow ho
      rw [h1] at h
      -- -1 * (-1)^x.2 = 1 means (-1)^x.2 = -1
      have h2 : (-1 : K)^x.2 = -1 := by
        have h3 : (-1 : K) * ((-1) * (-1)^x.2) = (-1) * 1 := by rw [h]
        simp only [neg_mul, one_mul, neg_neg, mul_one] at h3
        exact h3
      rw [h1, h2]
  rw [sum_congr rfl h_sym]
  -- Convert to range sum and apply the helper lemma
  have h_range : ∑ x ∈ antidiagonal (2*m), ((-1 : K) ^ x.1 : K) =
                 ∑ i ∈ range (2*m + 1), ((-1 : K) ^ i : K) := by
    rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i _ => ((-1 : K) ^ i : K))]
  rw [h_range]
  exact alternating_sum_range_even m

omit [BinomialRing K] [CharZero K] in
/-- Helper: 2 * x = 0 implies x = 0 in a ℚ-algebra.
    This is used in the pairing argument for odd coefficients. -/
private lemma eq_zero_of_two_mul_eq_zero (x : K) (h : 2 * x = 0) : x = 0 := by
  have h1 : (2 : ℚ)⁻¹ * 2 = 1 := by norm_num
  have h3 : (algebraMap ℚ K (2 : ℚ)⁻¹) * (algebraMap ℚ K 2) = 1 := by
    rw [← map_mul, h1, map_one]
  have h4 : (algebraMap ℚ K (2 : ℚ)) = (2 : K) := by simp only [map_ofNat]
  rw [h4] at h3
  calc x = 1 * x := by ring
    _ = ((algebraMap ℚ K (2 : ℚ)⁻¹) * 2) * x := by rw [h3]
    _ = (algebraMap ℚ K (2 : ℚ)⁻¹) * (2 * x) := by ring
    _ = (algebraMap ℚ K (2 : ℚ)⁻¹) * 0 := by rw [h]
    _ = 0 := by ring

omit [Algebra ℚ K] [CharZero K] in
/-- The coefficient of X^{2m} in expand 2 (rescale (-1) (binomialSeries K (-n)))
    equals Ring.choose (n + m - 1) m.
    
    This provides a direct formula for the even coefficients of (1-X²)^{-n}. -/
private lemma coeff_expand_rescale_neg_binomialSeries (n : K) (m : ℕ) :
    coeff (2 * m) (expand 2 two_ne_zero (rescale (-1 : K) (binomialSeries K (-n)))) = 
    Ring.choose (n + m - 1) m := by
  rw [coeff_expand_mul]
  simp only [coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one]
  -- Now we have (-1)^m * Ring.choose (-n) m = Ring.choose (n + m - 1) m
  rw [Ring.choose_neg]
  simp only [Units.smul_def, Int.negOnePow_def, zsmul_eq_mul]
  have h : ∀ k : ℕ, (((-1 : ℤˣ) ^ (k : ℤ) : ℤˣ) : K) = (-1 : K) ^ k := by
    intro k
    simp only [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [h]
  ring_nf
  have h2 : (-1 : K) ^ (m * 2) = 1 := by
    rw [pow_mul]
    have : ((-1 : K) ^ m) ^ 2 = 1 := by
      cases Nat.even_or_odd m with
      | inl he => rw [Even.neg_one_pow he]; ring
      | inr ho => rw [Odd.neg_one_pow ho]; ring
    exact this
  rw [h2]
  ring

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- rescale (-1) (1-X) = 1+X -/
private lemma rescale_neg_one_one_sub_X :
    rescale (-1 : K) (1 - X : K⟦X⟧) = 1 + X := by
  ext n
  simp only [coeff_rescale, map_sub, map_one, coeff_X, coeff_one, map_add]
  by_cases hn : n = 0
  · simp [hn]
  · by_cases hn1 : n = 1
    · simp [hn1]
    · simp only [hn, hn1, ↓reduceIte, mul_zero, zero_sub, neg_zero, add_zero]

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- (1-X)^N * invOneSubPow K N = 1 -/
private lemma one_sub_X_pow_mul_invOneSubPow (N : ℕ) :
    (1 - X : K⟦X⟧)^N * (invOneSubPow K N).val = 1 := by
  have h := (invOneSubPow K N).inv_val
  rw [invOneSubPow_inv_eq_one_sub_pow] at h
  exact h

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- (1+X)^N * rescale (-1) (invOneSubPow K N) = 1 -/
private lemma one_add_X_pow_mul_rescale_invOneSubPow (N : ℕ) :
    (1 + X : K⟦X⟧)^N * rescale (-1 : K) ((invOneSubPow K N).val) = 1 := by
  calc (1 + X : K⟦X⟧)^N * rescale (-1 : K) ((invOneSubPow K N).val)
      = rescale (-1 : K) ((1 - X)^N) * rescale (-1 : K) ((invOneSubPow K N).val) := by
        rw [RingHom.map_pow, rescale_neg_one_one_sub_X]
    _ = rescale (-1 : K) ((1 - X)^N * (invOneSubPow K N).val) := by rw [map_mul]
    _ = rescale (-1 : K) 1 := by rw [one_sub_X_pow_mul_invOneSubPow]
    _ = 1 := by simp

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- (1-X²)^N = (1-X)^N * (1+X)^N -/
private lemma one_sub_X_sq_pow (N : ℕ) :
    (1 - X^2 : K⟦X⟧)^N = (1 - X)^N * (1 + X)^N := by
  rw [← mul_pow]; congr 1; ring

omit [Algebra ℚ K] [BinomialRing K] [CharZero K] in
/-- The product (invOneSubPow K N).val * rescale (-1) (invOneSubPow K N).val 
    is the inverse of (1-X²)^N -/
private lemma one_sub_X_sq_pow_mul_prod (N : ℕ) :
    (1 - X^2 : K⟦X⟧)^N * ((invOneSubPow K N).val * rescale (-1 : K) ((invOneSubPow K N).val)) = 1 := by
  calc (1 - X^2 : K⟦X⟧)^N * ((invOneSubPow K N).val * rescale (-1 : K) ((invOneSubPow K N).val))
      = (1 - X)^N * (1 + X)^N * (invOneSubPow K N).val * rescale (-1 : K) ((invOneSubPow K N).val) := by 
        rw [one_sub_X_sq_pow]; ring
    _ = ((1 - X)^N * (invOneSubPow K N).val) * ((1 + X)^N * rescale (-1 : K) ((invOneSubPow K N).val)) := by ring
    _ = 1 * 1 := by rw [one_sub_X_pow_mul_invOneSubPow, one_add_X_pow_mul_rescale_invOneSubPow]
    _ = 1 := by ring

/-- The key product identity: f * g = (1-x)^{-n}

This is the algebraic identity (1-x²)^{-n} * (1+x)^n = (1-x)^{-n}.
The proof uses the factorization (1-x²) = (1-x)(1+x):
  (1-x²)^{-n} * (1+x)^n = (1-x)^{-n} * (1+x)^{-n} * (1+x)^n = (1-x)^{-n}

Note: This requires showing that f_series' n represents (1-x²)^{-n}, which
follows from the anti-Newton binomial formula with the substitution x → -x². -/
theorem key_product_identity' (n : K) :
    f_series' n * g_series' n = rescale (-1 : K) (binomialSeries K (-n)) := by
  -- The proof uses the algebraic identity:
  -- f_series' n = (1-x²)^{-n}  [substitution x → -x² in (1+x)^{-n}]
  -- g_series' n = (1+x)^n
  -- (1-x²)^{-n} * (1+x)^n = (1-x)^{-n} * (1+x)^{-n} * (1+x)^n = (1-x)^{-n}
  --                       = rescale (-1) (binomialSeries K (-n))
  --
  -- Step 1: Show f_series' n = (1 - X²)^ᶠ (-n) = rescale (-1) (binomialSeries K (-n)) * binomialSeries K (-n)
  -- Step 2: Then f_series' n * g_series' n = ... * binomialSeries K n = rescale (-1) (binomialSeries K (-n))
  --
  -- Key algebraic facts:
  -- (1 - X²) = (1 - X) * (1 + X)
  -- (1 - X)^ᶠ c = rescale (-1) (binomialSeries K c)  [by fpsPow_one_add_smul_X']
  -- (1 + X)^ᶠ c = binomialSeries K c  [by generalizedNewtonBinomial]
  -- (f * g)^ᶠ a = f^ᶠ a * g^ᶠ a  [by fpsPow_mul]
  --
  -- First, establish helper lemmas
  have h_one_sub_X : (1 - X : K⟦X⟧) = 1 + (-1 : K) • X := by
    simp only [neg_smul, one_smul, sub_eq_add_neg]
  have h_one_sub_X_sq : (1 - X^2 : K⟦X⟧) = (1 - X) * (1 + X) := by ring
  have h_const_one_sub_X : HasConstantTermOne (1 - X : K⟦X⟧) := by simp [HasConstantTermOne]
  -- (1 - X)^ᶠ (-n) = rescale (-1) (binomialSeries K (-n))
  have h_fpsPow_one_sub_X : (1 - X : K⟦X⟧) ^ᶠ (-n) = rescale (-1 : K) (binomialSeries K (-n)) := by
    rw [h_one_sub_X, fpsPow_one_add_smul_X', generalizedNewtonBinomial]
  -- (1 - X²)^ᶠ (-n) = (1 - X)^ᶠ (-n) * (1 + X)^ᶠ (-n)
  have h_fpsPow_one_sub_X_sq : (1 - X^2 : K⟦X⟧) ^ᶠ (-n) =
      rescale (-1 : K) (binomialSeries K (-n)) * binomialSeries K (-n) := by
    rw [h_one_sub_X_sq, fpsPow_mul h_const_one_sub_X hasConstantTermOne_one_add_X,
        h_fpsPow_one_sub_X, generalizedNewtonBinomial]
  -- f_series' n = (1 - X²)^ᶠ (-n)
  -- This requires showing the coefficients match.
  -- The coefficient of (1 - X²)^ᶠ (-n) at position k is:
  --   if Even k then Ring.choose (n + k/2 - 1) (k/2) else 0
  -- This matches f_series' n by definition.
  --
  -- The coefficient identity follows from the algebraic identity:
  -- (1-X)^{-n} * (1+X)^{-n} = (1-X²)^{-n}
  -- where (1-X²)^{-n} = ∑_m C(n+m-1,m) X^{2m} (by anti-Newton binomial with substitution X → X²)
  have h_f_series_eq : f_series' n = (1 - X^2 : K⟦X⟧) ^ᶠ (-n) := by
    rw [h_fpsPow_one_sub_X_sq]
    ext k
    simp only [f_series', coeff_mk, coeff_mul, coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one]
    -- The coefficient of the RHS is ∑_{i+j=k} (-1)^i * C(-n,i) * C(-n,j)
    -- Using Ring.choose_neg: C(-n,m) = (-1)^m * C(n+m-1,m)
    -- So the sum becomes ∑_{i+j=k} (-1)^i * (-1)^i * C(n+i-1,i) * (-1)^j * C(n+j-1,j)
    --                  = ∑_{i+j=k} C(n+i-1,i) * (-1)^j * C(n+j-1,j)
    -- For k odd: this is 0 (terms cancel pairwise since i and k-i have opposite parities)
    -- For k = 2m: this is C(n+m-1,m) (by the convolution identity for (1-X²)^{-n})
    by_cases hk : Even k
    · -- k is even: coefficient is C(n + k/2 - 1, k/2)
      obtain ⟨m, hm⟩ := hk
      subst hm
      have h_even : Even (m + m) := ⟨m, rfl⟩
      rw [ite_eq_left h_even]
      have h_div : (m + m) / 2 = m := by omega
      rw [h_div]
      -- The coefficient identity: ∑_{i+j=2m} (-1)^i * C(-n,i) * C(-n,j) = C(n+m-1,m)
      -- This follows from (1-X)^{-n} * (1+X)^{-n} = (1-X²)^{-n} = ∑_m C(n+m-1,m) X^{2m}
      --
      -- Step 1: Transform using Ring.choose_neg
      -- (-1)^i * C(-n,i) * C(-n,j) = (-1)^j * C(n+i-1, i) * C(n+j-1, j)
      have h_negOnePow_cast : ∀ k : ℕ, (((-1 : ℤˣ) ^ (k : ℤ) : ℤˣ) : K) = (-1 : K) ^ k := by
        intro k
        simp only [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
          Int.cast_pow, Int.cast_neg, Int.cast_one]
      have h_neg_one_sq : ∀ k : ℕ, (-1 : K) ^ (k * 2) = 1 := by
        intro k
        have h : ((-1 : K) ^ k) ^ 2 = 1 := by
          cases Nat.even_or_odd k with
          | inl he => rw [Even.neg_one_pow he]; ring
          | inr ho => rw [Odd.neg_one_pow ho]; ring
        rw [← pow_mul] at h; convert h using 1
      have h_transform : ∀ x ∈ antidiagonal (m + m),
          (-1 : K) ^ x.1 * Ring.choose (-n) x.1 * Ring.choose (-n) x.2 =
          (-1 : K) ^ x.2 * Ring.choose (n + x.1 - 1) x.1 * Ring.choose (n + x.2 - 1) x.2 := by
        intro x hx
        rw [Ring.choose_neg, Ring.choose_neg]
        simp only [Units.smul_def, Int.negOnePow_def, zsmul_eq_mul]
        rw [h_negOnePow_cast, h_negOnePow_cast]
        ring_nf
        rw [h_neg_one_sq]
        ring
      rw [Finset.sum_congr rfl h_transform]
      -- Step 2: Express as coefficient of product of power series
      -- f = (1-X)^{-n} has coeff k = C(n+k-1, k)
      -- g = (1+X)^{-n} has coeff k = (-1)^k * C(n+k-1, k)
      let f' : K⟦X⟧ := rescale (-1 : K) (binomialSeries K (-n))
      let g' : K⟦X⟧ := binomialSeries K (-n)
      have h_neg_one_pow_mul_choose : ∀ k : ℕ,
          (-1 : K) ^ k * Ring.choose (-n) k = Ring.choose (n + k - 1) k := by
        intro k
        rw [Ring.choose_neg]
        simp only [Units.smul_def, Int.negOnePow_def, zsmul_eq_mul]
        rw [h_negOnePow_cast]; ring_nf; rw [h_neg_one_sq]; ring
      have hf'_coeff : ∀ k, coeff k f' = Ring.choose (n + k - 1) k := by
        intro k
        simp only [f', coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one]
        exact h_neg_one_pow_mul_choose k
      have hg'_coeff : ∀ k, coeff k g' = (-1 : K) ^ k * Ring.choose (n + k - 1) k := by
        intro k
        simp only [g', binomialSeries_coeff, smul_eq_mul, mul_one]
        rw [Ring.choose_neg]
        simp only [Units.smul_def, Int.negOnePow_def, zsmul_eq_mul]
        rw [h_negOnePow_cast]
      have h_sum_eq_coeff : ∑ x ∈ antidiagonal (m + m),
          (-1 : K) ^ x.2 * Ring.choose (n + x.1 - 1) x.1 * Ring.choose (n + x.2 - 1) x.2 =
          coeff (m + m) (f' * g') := by
        rw [coeff_mul]
        apply Finset.sum_congr rfl
        intro x hx
        rw [hf'_coeff, hg'_coeff]
        ring
      rw [h_sum_eq_coeff]
      -- Step 3: f' * g' = (1-X)^{-n} * (1+X)^{-n} = (1-X²)^{-n}
      -- coeff (2m) of (1-X²)^{-n} = C(-n, m) * (-1)^m = C(n+m-1, m)
      --
      -- The proof uses the polynomial identity principle:
      -- Both coeff (m+m) (f' * g') and Ring.choose (n + m - 1) m are
      -- polynomial functions of n of degree ≤ m, and they agree on ℕ.
      --
      -- For natural N:
      --   LHS = coeff (2m) ((1-X)^{-N} * (1+X)^{-N}) = coeff (2m) ((1-X²)^{-N})
      --       = C(N+m-1, m) = Nat.choose (N+m-1) m
      --   RHS = Ring.choose (N + m - 1) m = Nat.choose (N+m-1) m
      --
      -- By the polynomial identity principle (same technique as generalizedNewtonBinomial),
      -- they agree for all n ∈ K.
      --
      -- The combinatorial interpretation: (1-X²)^{-N} = (1/(1-X²))^N = (∑_k X^{2k})^N
      -- The coefficient of X^{2m} counts ways to write m as sum of N non-negative integers,
      -- which is C(N+m-1, m) by stars-and-bars.
      --
      -- The base case m = 0:
      cases m with
      | zero =>
        -- coeff 0 (f' * g') = coeff 0 f' * coeff 0 g' = 1 * 1 = 1
        -- Ring.choose (n - 1) 0 = 1
        simp only [Nat.cast_zero, add_zero]
        rw [coeff_mul]
        simp only [Finset.Nat.antidiagonal_zero, sum_singleton]
        rw [hf'_coeff, hg'_coeff]
        simp only [Ring.choose_zero_right, pow_zero, mul_one]
        | succ m =>
          -- For m > 0, use the polynomial identity principle
          -- Both sides are polynomial functions of n that agree on ℕ
          -- This is the same technique needed for generalizedNewtonBinomial
          --
          -- The key insight: both sides satisfy the same recurrence relation
          -- and have the same initial values, so they must be equal.
          --
          -- Both sides are polynomial functions of n that agree on all natural numbers.
          -- By the polynomial identity principle, they must be equal.
          --
          -- PROOF SKETCH FOR NATURAL NUMBERS N:
          -- We need: coeff (2(m+1)) ((1-X)^{-N} * (1+X)^{-N}) = Nat.choose (N+m) (m+1)
          --
          -- Key facts:
          -- 1. (1-X)^{-N} * (1+X)^{-N} = ((1-X)(1+X))^{-N} = (1-X²)^{-N}
          -- 2. (1-X²)^{-N} = (1/(1-X²))^N = (∑_{k≥0} X^{2k})^N
          -- 3. coeff (2m) of (∑_{k≥0} X^{2k})^N = #{ways to write m as sum of N non-neg integers}
          --    = Nat.choose (N+m-1) m (stars and bars)
          --
          -- For m+1: coeff (2(m+1)) = Nat.choose (N+(m+1)-1) (m+1) = Nat.choose (N+m) (m+1)
          -- RHS: Ring.choose (N + (m+1) - 1) (m+1) = Nat.choose (N+m) (m+1)
          --
          -- Note: The goal is Ring.choose (n + m.succ - 1) m.succ = coeff (m.succ + m.succ) (f' * g')
          -- Define the functions accordingly
          let coeffFn : K → K := fun n => coeff (m.succ + m.succ) (rescale (-1 : K) (binomialSeries K (-n)) * binomialSeries K (-n))
          let chooseFn : K → K := fun n => Ring.choose (n + m.succ - 1) m.succ
          -- Show they agree on natural numbers
          have h_agree : ∀ N : ℕ, coeffFn N = chooseFn N := by
            intro N
            simp only [coeffFn, chooseFn]
            -- Convert binomialSeries to invOneSubPow using the established lemmas
            rw [rescale_neg_binomialSeries_neg_nat, binomialSeries_neg_nat_eq_rescale_invOneSubPow]
            -- Now the goal is: coeff (m.succ + m.succ) (invOneSubPow * rescale (-1) invOneSubPow) = Ring.choose (N + m) (m + 1)
            cases N with
            | zero =>
              -- For N = 0, invOneSubPow K 0 = 1, so the product is 1 * rescale (-1) 1 = 1
              simp only [Nat.cast_zero]
              have h0 : (invOneSubPow K 0).val = 1 := by
                rw [invOneSubPow_zero]; simp
              rw [h0]
              simp only [map_one, mul_one, coeff_one, Nat.succ_eq_add_one]
              -- Goal: (if m + 1 + (m + 1) = 0 then 1 else 0) = Ring.choose (0 + ↑(m + 1) - 1) (m + 1)
              -- LHS = 0 (since m + 1 + (m + 1) ≠ 0), RHS = Ring.choose m (m+1) = 0
              have h_ne : m + 1 + (m + 1) ≠ 0 := by omega
              simp only [h_ne, ↓reduceIte, zero_add]
              have h1 : (↑(m + 1) : K) - 1 = m := by
                simp only [Nat.cast_add, Nat.cast_one]; ring
              rw [h1, Ring.choose_natCast]
              simp only [Nat.choose_succ_self, Nat.cast_zero]
            | succ N' =>
              -- For N ≥ 1, use coeff_invOneSubPow_product_even'
              have hN : 0 < N'.succ := Nat.succ_pos N'
              rw [coeff_invOneSubPow_product_even' N'.succ m.succ hN]
              -- Now show Nat.choose (N'.succ + m.succ - 1) m.succ = Ring.choose (N'.succ + m.succ - 1) m.succ
              have hcast : (N'.succ : K) + ↑m.succ - 1 = ↑(N'.succ + m.succ - 1) := by
                simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
                have h : N' + 1 + (m + 1) - 1 = N' + m + 1 := by omega
                simp only [h, Nat.cast_add, Nat.cast_one]
                ring
              rw [hcast, Ring.choose_natCast]
          -- Both sides are polynomial functions of n
          -- The RHS: Ring.choose (n + m) (m+1) = (1/(m+1)!) * descPochhammer(n+m, m+1)
          -- The LHS: coeff (2(m+1)) (f' * g') is a convolution, hence polynomial
          --
          -- By the polynomial identity principle, since they agree on ℕ, they agree everywhere
          --
          -- The formal proof constructs explicit polynomials over ℚ and uses
          -- Polynomial.eq_of_infinite_eval_eq, then maps to K
          --
          -- For now, we use the polynomial identity principle directly:
          -- Both coeffFn and chooseFn are polynomial functions of n that agree on all N ∈ ℕ
          -- Hence coeffFn = chooseFn, and in particular coeffFn n = chooseFn n
          have h_eq : coeffFn = chooseFn := by
            -- Both coeffFn and chooseFn are polynomial functions of n that agree on all N ∈ ℕ.
            -- By the polynomial identity principle, they must be equal.
            --
            -- The proof proceeds by showing both are evaluations of polynomials over ℚ.
            -- chooseFn n = Ring.choose (n + m.succ - 1) m.succ = eval of choosePoly (m.succ) shifted
            -- coeffFn n = sum of products of Ring.choose values = eval of sum of products of choosePoly
            --
            -- Since they agree on ℕ (h_agree), the polynomials are equal, hence the functions are equal.
            funext c
            -- We use the fact that Ring.choose is determined by its values on naturals.
            -- Both sides are polynomial functions of c, and they agree on all N ∈ ℕ.
            -- By Ring.choose_unique_of_nat_agree (or similar), they must be equal.
            --
            -- Direct approach: show the difference is a polynomial that vanishes on all naturals.
            -- Define the difference function
            let diffFn : K → K := fun n => coeffFn n - chooseFn n
            -- diffFn vanishes on all naturals
            have h_diff_nat : ∀ N : ℕ, diffFn N = 0 := fun N => by simp [diffFn, h_agree N]
            -- Both coeffFn and chooseFn can be expressed as polynomial evaluations.
            -- Their difference is also a polynomial evaluation.
            -- A polynomial that vanishes on infinitely many points is zero.
            --
            -- For chooseFn: Ring_choose_eq_choosePoly_eval gives the polynomial.
            -- For coeffFn: it's a finite sum of products of Ring.choose values,
            -- each of which is a polynomial evaluation. So coeffFn is also a polynomial evaluation.
            --
            -- The detailed proof requires constructing these polynomials explicitly.
            -- For now, we observe that both sides are polynomial functions of degree ≤ m.succ.
            -- They agree on m.succ + 1 points (0, 1, ..., m.succ), which is enough to determine them.
            --
            -- Actually, we need infinitely many points for the polynomial identity principle.
            -- Since they agree on ALL natural numbers, the polynomials must be equal.
            --
            -- The formal proof uses polynomial_zero_of_nat_roots on the difference polynomial.
            -- But constructing the difference polynomial explicitly is complex.
            --
            -- Alternative: use the fact that K is a ℚ-algebra, so polynomial functions
            -- are uniquely determined by their values on ℕ (which embeds into K).
            --
            -- For the formal proof, we note that:
            -- 1. chooseFn c = Ring.choose (c + m.succ - 1) m.succ
            --    = ((choosePoly m.succ).comp (X + m.succ - 1)).map (algebraMap ℚ K)).eval c
            -- 2. coeffFn c = ∑_{i+j=2m+2} (-1)^i Ring.choose (c+i-1) i * Ring.choose (-c) j
            --    This is also a polynomial evaluation (sum of products of polynomial evaluations).
            --
            -- The polynomial identity principle then gives coeffFn = chooseFn.
            --
            -- Both coeffFn and chooseFn are polynomial functions of c.
            -- chooseFn c = Ring.choose (c + m) (m + 1) is a polynomial in c.
            -- coeffFn c is a finite sum of products of Ring.choose values, hence polynomial.
            --
            -- Define the polynomial for Ring.choose (c + k - 1) k:
            -- For k = 0: Ring.choose (c - 1) 0 = 1
            -- For k ≥ 1: Ring.choose (c + k - 1) k = (choosePoly k).comp (X + C (k - 1)) evaluated at c
            let shiftedChoosePoly : ℕ → Polynomial ℚ := fun k =>
              if k = 0 then 1 else (choosePoly k).comp (Polynomial.X + Polynomial.C ((k : ℚ) - 1))
            -- The polynomial for coeffFn:
            let coeffFnPoly : Polynomial ℚ :=
              ∑ x ∈ antidiagonal (m.succ + m.succ),
                ((-1 : ℚ) ^ x.2) • (shiftedChoosePoly x.1 * shiftedChoosePoly x.2)
            -- The polynomial for chooseFn:
            let chooseFnPoly : Polynomial ℚ :=
              (choosePoly m.succ).comp (Polynomial.X + Polynomial.C (m : ℚ))
            -- Key: Ring.choose (c + k - 1) k = (shiftedChoosePoly k).map ... |>.eval c
            have h_shifted : ∀ k : ℕ, ∀ c : K,
                Ring.choose (c + (k : K) - 1) k = ((shiftedChoosePoly k).map (algebraMap ℚ K)).eval c := by
              intro k c'
              simp only [shiftedChoosePoly]
              split_ifs with hk
              · subst hk
                simp only [Nat.cast_zero, add_zero, Ring.choose_zero_right,
                           Polynomial.map_one, Polynomial.eval_one]
              · simp only [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
                           Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
                have hcast : c' + (k : K) - 1 = c' + algebraMap ℚ K ((k : ℚ) - 1) := by
                  simp only [map_sub, map_natCast, map_one]; ring
                rw [hcast]
                exact Ring_choose_eq_choosePoly_eval k (c' + algebraMap ℚ K ((k : ℚ) - 1))
            -- Key: chooseFn c = (chooseFnPoly.map ...).eval c
            have h_chooseFn_poly : ∀ c' : K,
                chooseFn c' = (chooseFnPoly.map (algebraMap ℚ K)).eval c' := by
              intro c'
              simp only [chooseFn, chooseFnPoly]
              simp only [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
                         Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
              have hcast : c' + m.succ - 1 = c' + algebraMap ℚ K (m : ℚ) := by
                simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, map_natCast]
                ring
              rw [hcast]
              exact Ring_choose_eq_choosePoly_eval m.succ (c' + algebraMap ℚ K (m : ℚ))
            -- Key: coeffFn c = (coeffFnPoly.map ...).eval c
            have h_coeffFn_poly : ∀ c' : K,
                coeffFn c' = (coeffFnPoly.map (algebraMap ℚ K)).eval c' := by
              intro c'
              simp only [coeffFn, coeffFnPoly]
              rw [coeff_mul]
              simp only [Polynomial.map_sum, Polynomial.eval_finsetSum]
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Polynomial.map_smul, Polynomial.eval_smul, smul_eq_mul]
              simp only [Polynomial.map_mul, Polynomial.eval_mul]
              -- LHS: coeff x.1 (rescale (-1) (binomialSeries K (-c'))) * coeff x.2 (binomialSeries K (-c'))
              -- = (-1)^x.1 * Ring.choose (-c') x.1 * Ring.choose (-c') x.2
              have h1 : coeff x.1 (rescale (-1 : K) (binomialSeries K (-c'))) =
                        (-1 : K)^x.1 * Ring.choose (-c') x.1 := by
                simp only [coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one]
              have h2 : coeff x.2 (binomialSeries K (-c')) = Ring.choose (-c') x.2 := by
                simp only [binomialSeries_coeff, smul_eq_mul, mul_one]
              rw [h1, h2]
              -- Using Ring.choose_neg: Ring.choose (-c') k = (-1)^k * Ring.choose (c' + k - 1) k
              rw [Ring.choose_neg, Ring.choose_neg]
              simp only [Units.smul_def, Int.negOnePow_def, zsmul_eq_mul]
              have h_negOnePow_cast : ∀ k : ℕ, (((-1 : ℤˣ) ^ (k : ℤ) : ℤˣ) : K) = (-1 : K) ^ k := by
                intro k
                simp only [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
                  Int.cast_pow, Int.cast_neg, Int.cast_one]
              rw [h_negOnePow_cast, h_negOnePow_cast]
              -- Now we have: (-1)^x.1 * ((-1)^x.1 * Ring.choose (c'+x.1-1) x.1) * ((-1)^x.2 * Ring.choose (c'+x.2-1) x.2)
              --            = algebraMap ℚ K ((-1)^x.2) * (shiftedChoosePoly x.1).map...|>.eval c' * ...
              have h_neg_one_sq : ∀ k : ℕ, (-1 : K) ^ (k * 2) = 1 := by
                intro k
                rw [pow_mul]
                cases Nat.even_or_odd k with
                | inl he => rw [Even.neg_one_pow he]; ring
                | inr ho => rw [Odd.neg_one_pow ho]; ring
              rw [h_shifted x.1 c', h_shifted x.2 c']
              simp only [map_pow, map_neg, map_one]
              ring_nf
              rw [h_neg_one_sq]
              ring
            -- Now use poly_eq_of_nat_eval_eq to show coeffFnPoly = chooseFnPoly
            have h_poly_eq : coeffFnPoly = chooseFnPoly := by
              apply poly_eq_of_nat_eval_eq (K := K)
              intro N
              rw [← h_coeffFn_poly (N : K), ← h_chooseFn_poly (N : K)]
              exact h_agree N
            -- Conclude coeffFn = chooseFn
            -- Note: coeffFn and chooseFn are let-bindings, so we need to unfold them
            have h_final : coeffFn c = chooseFn c := by
              rw [h_coeffFn_poly c, h_chooseFn_poly c, h_poly_eq]
            exact h_final
          -- The goal is: Ring.choose (n + m.succ - 1) m.succ = coeff (m.succ + m.succ) (f' * g')
          -- which is: chooseFn n = coeffFn n
          -- By h_eq, coeffFn = chooseFn, so coeffFn n = chooseFn n
          -- Hence chooseFn n = coeffFn n by symmetry
          exact (congrFun h_eq n).symm
    · -- k is odd: coefficient is 0
      rw [ite_eq_right hk]
      -- For k odd, the sum ∑_{i+j=k} (-1)^i * C(-n,i) * C(-n,j) = 0
      -- Proof: pair (i, k-i) with (k-i, i). Their sum involves (-1)^i + (-1)^{k-i}.
      -- Since k is odd, i and k-i have opposite parities, so (-1)^i + (-1)^{k-i} = 0.
      have hodd : Odd k := Nat.not_even_iff_odd.mp hk
      have hsym : ∀ x ∈ antidiagonal k,
          (-1 : K) ^ x.1 * Ring.choose (-n) x.1 * Ring.choose (-n) x.2 +
          (-1 : K) ^ x.2 * Ring.choose (-n) x.2 * Ring.choose (-n) x.1 = 0 := by
        intro x hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        have h : (-1 : K) ^ x.1 + (-1 : K) ^ x.2 = 0 := by
          have hsum_odd : Odd (x.1 + x.2) := by rw [hx]; exact hodd
          rw [Nat.odd_add] at hsum_odd
          by_cases h1 : Odd x.1
          · have h2 : Even x.2 := hsum_odd.mp h1
            rw [Odd.neg_one_pow h1, Even.neg_one_pow h2]; ring
          · have h1' : Even x.1 := Nat.not_odd_iff_even.mp h1
            have h2 : Odd x.2 := by
              rw [← Nat.not_even_iff_odd]; intro h2'; exact h1 (hsum_odd.mpr h2')
            rw [Even.neg_one_pow h1', Odd.neg_one_pow h2]; ring
        calc (-1 : K) ^ x.1 * Ring.choose (-n) x.1 * Ring.choose (-n) x.2 +
             (-1 : K) ^ x.2 * Ring.choose (-n) x.2 * Ring.choose (-n) x.1
           = Ring.choose (-n) x.1 * Ring.choose (-n) x.2 * ((-1) ^ x.1 + (-1) ^ x.2) := by ring
         _ = Ring.choose (-n) x.1 * Ring.choose (-n) x.2 * 0 := by rw [h]
         _ = 0 := by ring
      have hswap : ∑ x ∈ antidiagonal k, (-1 : K) ^ x.1 * Ring.choose (-n) x.1 * Ring.choose (-n) x.2 =
                   ∑ x ∈ antidiagonal k, (-1 : K) ^ x.2 * Ring.choose (-n) x.2 * Ring.choose (-n) x.1 := by
        have := @Finset.Nat.sum_antidiagonal_swap K _ k
          (fun p => (-1 : K) ^ p.2 * Ring.choose (-n) p.2 * Ring.choose (-n) p.1)
        simp only [Prod.fst_swap, Prod.snd_swap] at this
        exact this
      have h2sum : 2 * ∑ x ∈ antidiagonal k, (-1 : K) ^ x.1 * Ring.choose (-n) x.1 * Ring.choose (-n) x.2 = 0 := by
        calc 2 * ∑ x ∈ antidiagonal k, (-1 : K) ^ x.1 * Ring.choose (-n) x.1 * Ring.choose (-n) x.2
            = ∑ x ∈ antidiagonal k, (-1 : K) ^ x.1 * Ring.choose (-n) x.1 * Ring.choose (-n) x.2 +
              ∑ x ∈ antidiagonal k, (-1 : K) ^ x.1 * Ring.choose (-n) x.1 * Ring.choose (-n) x.2 := by ring
          _ = ∑ x ∈ antidiagonal k, (-1 : K) ^ x.1 * Ring.choose (-n) x.1 * Ring.choose (-n) x.2 +
              ∑ x ∈ antidiagonal k, (-1 : K) ^ x.2 * Ring.choose (-n) x.2 * Ring.choose (-n) x.1 := by rw [hswap]
          _ = ∑ x ∈ antidiagonal k, ((-1 : K) ^ x.1 * Ring.choose (-n) x.1 * Ring.choose (-n) x.2 +
              (-1 : K) ^ x.2 * Ring.choose (-n) x.2 * Ring.choose (-n) x.1) := by rw [← Finset.sum_add_distrib]
          _ = ∑ x ∈ antidiagonal k, 0 := by
              apply Finset.sum_congr rfl; intro x hx; exact hsym x hx
          _ = 0 := by simp
      have h2_inv : IsUnit (2 : K) := by
        have : IsUnit (algebraMap ℚ K 2) := by apply (algebraMap ℚ K).isUnit_map; norm_num
        simp only [map_ofNat] at this; exact this
      rw [mul_comm] at h2sum
      exact (h2_inv.mul_left_eq_zero.mp h2sum).symm
  -- Now complete the proof
  rw [h_f_series_eq, h_fpsPow_one_sub_X_sq, g_series', mul_assoc]
  -- binomialSeries K (-n) * binomialSeries K n = 1
  have h_binom_inv : binomialSeries K (-n) * binomialSeries K n = 1 := by
    rw [← binomialSeries_add, neg_add_cancel, binomialSeries_zero]
  rw [h_binom_inv, mul_one]

/-- The binomial identity: ∑_{i=0}^{⌊k/2⌋} C(n+i-1, i) C(n, k-2i) = C(n+k-1, k)

This is proved using generating functions and the generalized Newton formula.
Note: The sum is restricted to i ≤ k/2 (equivalently, 2i ≤ k) because when 2i > k,
the binomial coefficient C(n, k-2i) should be 0 (as k-2i would be negative).
Using ℕ subtraction directly would incorrectly give C(n, 0) = 1 for those terms.
Label: prop.binom.nCk-2i-qedmo.CN -/
theorem binomialIdentity (n : K) (k : ℕ) :
    ∑ i ∈ range (k / 2 + 1), Ring.choose (n + i - 1) i * Ring.choose n (k - 2*i) =
    Ring.choose (n + k - 1) k := by
  calc ∑ i ∈ range (k / 2 + 1), Ring.choose (n + i - 1) i * Ring.choose n (k - 2*i)
      = coeff k (f_series' n * g_series' n) := (coeff_f_mul_g' n k).symm
    _ = coeff k (rescale (-1 : K) (binomialSeries K (-n))) := by rw [key_product_identity']
    _ = Ring.choose (n + k - 1) k := one_sub_X_pow_neg_coeff n k

/-!
## Consistency with Integer Powers

Our definition of f^c agrees with the standard definition when c is a natural number.
-/

omit [BinomialRing K] in
/-- For natural number exponents, fpsPow agrees with the standard power.
    This shows our definition is consistent with integer powers.
    Label: (consistency claim after def.fps.power-c) -/
theorem fpsPow_nat {f : K⟦X⟧} (hf : HasConstantTermOne f) (n : ℕ) :
    f ^ᶠ (n : K) = f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, fpsPow_add hf, ih, pow_succ, fpsPow_one hf]

omit [BinomialRing K] in
/-- For integer exponents, fpsPow agrees with the standard power (when f is invertible).
    For negative integers, this requires f to be invertible (which holds when constantCoeff f ≠ 0).
    Label: (consistency claim after def.fps.power-c) -/
theorem fpsPow_int {K' : Type*} [Field K'] [Algebra ℚ K'] {f : K'⟦X⟧}
    (hf : HasConstantTermOne f) (n : ℤ) :
    f ^ᶠ (n : K') = if n ≥ 0 then f ^ n.toNat else (f ^ (-n).toNat)⁻¹ := by
  by_cases hn : n ≥ 0
  · -- Case n ≥ 0
    simp only [hn, ↓reduceIte]
    have h_cast : (n : K') = (n.toNat : K') := by
      have h : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
      calc (n : K') = ((n.toNat : ℤ) : K') := by rw [h]
        _ = (n.toNat : K') := Int.cast_natCast n.toNat
    rw [h_cast]
    exact fpsPow_nat hf n.toNat
  · -- Case n < 0
    simp only [hn, ↓reduceIte]
    push Not at hn
    have hpos : 0 ≤ -n := le_of_lt (Int.neg_pos.mpr hn)
    have h_cast : ((-n) : K') = ((-n).toNat : K') := by
      have h : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg hpos
      show -(n : K') = ((-n).toNat : K')
      have h2 : (n : K') = -(((-n).toNat : ℕ) : K') := by
        calc (n : K') = ((-(-n)) : K') := by ring
          _ = - -((n : ℤ) : K') := by ring
          _ = -(((-n) : ℤ) : K') := by simp only [Int.cast_neg, neg_neg]
          _ = -(((-n).toNat : ℤ) : K') := by rw [h]
          _ = -(((-n).toNat : ℕ) : K') := by norm_cast
      rw [h2]; ring
    have step1 : f ^ᶠ (n : K') * f ^ᶠ ((-n) : K') = 1 := by
      have h1 : ((-n) : K') = -(n : K') := by ring
      rw [h1]
      calc f ^ᶠ (n : K') * f ^ᶠ (-(n : K'))
          = f ^ᶠ ((n : K') + (-(n : K'))) := by rw [← fpsPow_add hf]
        _ = f ^ᶠ (0 : K') := by ring_nf
        _ = 1 := fpsPow_zero f
    have step2 : f ^ᶠ ((-n) : K') = f ^ (-n).toNat := by
      rw [h_cast]
      exact fpsPow_nat hf (-n).toNat
    rw [step2] at step1
    have hconst : constantCoeff (f ^ (-n).toNat) ≠ 0 := by
      simp only [map_pow, HasConstantTermOne] at hf ⊢
      rw [hf]
      simp only [one_pow, ne_eq, one_ne_zero, not_false_eq_true]
    rw [MvPowerSeries.eq_inv_iff_mul_eq_one hconst]
    exact step1

/-!
## The Proof Method: Polynomial Identity Trick

The proof of the generalized Newton formula uses the "polynomial identity trick":
If two polynomials (with rational coefficients) agree on all natural numbers,
they must be equal as polynomials, and hence agree on all values in any ℚ-algebra.

This is formalized in Mathlib as polynomial equality from infinitely many roots.
-/

/-- The polynomial identity trick: If a polynomial has infinitely many roots, it is zero.
    This is the key lemma used in the proof of the generalized Newton formula.

    Note: This requires `CharZero R` to ensure that the natural numbers are distinct when
    coerced to R. Without this assumption, the theorem is false: for example, in `ZMod 2`,
    the polynomial `x(x-1)` evaluates to 0 at all natural numbers but is nonzero.

    Label: (polynomial identity trick in proof of thm.fps.gen-newton) -/
theorem polynomial_identity_trick {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (p : Polynomial R) (h : ∀ n : ℕ, p.eval (n : R) = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  -- The set of roots contains all natural numbers (as elements of R)
  have hnat : Set.Infinite (Set.range (fun n : ℕ => (n : R))) :=
    Set.infinite_range_of_injective Nat.cast_injective
  have hsub : Set.range (fun n : ℕ => (n : R)) ⊆ { x | p.IsRoot x } := by
    intro x hx
    simp only [Set.mem_range] at hx
    obtain ⟨n, rfl⟩ := hx
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, h n]
  exact hnat.mono hsub

end FPS

end AlgebraicCombinatorics
