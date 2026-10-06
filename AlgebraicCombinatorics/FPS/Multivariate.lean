/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# Multivariate Formal Power Series

This file formalizes the material from Section `sec.gf.multivar` on multivariate formal power
series (FPSs).

## Main Content

Multivariate FPSs are FPSs in several variables. Their theory is mostly analogous to the theory
of univariate FPSs, but requires more subscripts. In Mathlib, multivariate formal power series
are defined as `MvPowerSeries σ R := (σ →₀ ℕ) → R`, where `σ` is the index set of variables.

### Key concepts from the source:

- **Bivariate FPSs**: FPSs in two variables `x` and `y` have the form `∑_{i,j∈ℕ} a_{i,j} x^i y^j`.
  In Mathlib, this is `MvPowerSeries (Fin 2) R`.

- **Multiplication**: For any two FPSs `a` and `b` and any `n ∈ ℕ^k`:
  `[x^n](ab) = ∑_{i+j=n} [x^i]a · [x^j]b`
  This is already captured by `MvPowerSeries.coeff_mul`.

- **Indeterminates**: The indeterminate `x_i` is defined as the family with a single `1` at
  position `(0,...,0,1,0,...,0)` (with `1` in the `i`-th position).
  This is `MvPowerSeries.X i` in Mathlib.

- **Partial derivatives**: Instead of one derivative, there are `k` partial derivatives
  (one for each variable).

## Main Results

- `embedUnivInBiv`: Embedding of sequences of univariate power series into bivariate power series
- `eq_of_embedUnivInBiv_eq`: Proposition `prop.fps.mulvar.comp-y-coeff` -
  if `∑_k f_k y^k = ∑_k g_k y^k` in `K[[x,y]]`, then `f_k = g_k` for each `k`.
- `binomialGenFun_eq`: The generating function identity
  `∑_{n,k∈ℕ} C(n,k) x^n y^k = 1/(1-x(1+y))`
- `binomialGenFun_xyk_eq`: Equation `eq.fps.mulvar.exa1.xyk` - the intermediate bivariate equation
- `sum_choose_pow_eq`: Equation `eq.fps.mulvar.exa1.res1` - the univariate identity derived from
  comparing coefficients
- `partialDeriv`: Partial derivative of a multivariate power series
- `partialDeriv_mul`: The product rule for partial derivatives

## References

* Section `sec.gf.multivar` of the source text

## TODO

The source notes that this section needs more details.
-/

open MvPowerSeries Finset BigOperators Finsupp

variable {R : Type*} [CommSemiring R]

namespace AlgebraicCombinatorics

/-!
### Notation for multivariate power series rings

The `K`-algebra of all FPSs in `k` variables `x₁, x₂, ..., xₖ` over `K` is denoted
by `K[[x₁, x₂, ..., xₖ]]` in the source. In Mathlib, this is `MvPowerSeries (Fin k) K`.
-/

/-- The algebra of formal power series in `k` variables over `R`.
    This corresponds to `K[[x₁, x₂, ..., xₖ]]` in the source notation. -/
abbrev FPS (k : ℕ) (R : Type*) [CommSemiring R] := MvPowerSeries (Fin k) R

/-- The algebra of formal power series in 2 variables (bivariate).
    This corresponds to `K[[x, y]]` in the source. -/
abbrev BivFPS (R : Type*) [CommSemiring R] := MvPowerSeries (Fin 2) R

/-- The first variable `x` in a bivariate power series ring. -/
noncomputable def BivFPS.x : BivFPS R := MvPowerSeries.X 0

/-- The second variable `y` in a bivariate power series ring. -/
noncomputable def BivFPS.y : BivFPS R := MvPowerSeries.X 1

/-!
### Embedding univariate power series into bivariate power series

To formalize Proposition `prop.fps.mulvar.comp-y-coeff`, we need to embed sequences of
univariate power series into bivariate power series. Given a sequence `f : ℕ → PowerSeries R`,
we define the bivariate power series `∑_k f_k y^k` whose coefficient at `x^n y^k` is the
coefficient of `x^n` in `f_k`.
-/

/-- Embedding of a sequence of univariate power series `f : ℕ → PowerSeries R` into a
    bivariate power series `∑_k f_k y^k` in `K[[x, y]]`.

    The coefficient of `x^n y^k` in the result is the coefficient of `x^n` in `f_k`. -/
noncomputable def embedUnivInBiv (f : ℕ → PowerSeries R) : BivFPS R :=
  fun nm => (f (nm 1)).coeff (nm 0)

/-- The coefficient of `x^n y^k` in `embedUnivInBiv f` is the coefficient of `x^n` in `f k`. -/
@[simp]
theorem coeff_embedUnivInBiv (f : ℕ → PowerSeries R) (n k : ℕ) :
    (embedUnivInBiv f) (Finsupp.single 0 n + Finsupp.single 1 k) = (f k).coeff n := by
  unfold embedUnivInBiv
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
  congr 1 <;> simp

/-- **Proposition `prop.fps.mulvar.comp-y-coeff`**: If two sequences of univariate power series
    `f` and `g` satisfy `∑_k f_k y^k = ∑_k g_k y^k` in `K[[x,y]]`, then `f_k = g_k` for each `k`.

    This is the key tool for "comparing coefficients in front of `y^k`" to extract
    univariate identities from bivariate manipulations. -/
theorem eq_of_embedUnivInBiv_eq (f g : ℕ → PowerSeries R)
    (h : embedUnivInBiv f = embedUnivInBiv g) :
    f = g := by
  funext k
  ext n
  have h1 : (embedUnivInBiv f) (Finsupp.single 0 n + Finsupp.single 1 k) =
            (embedUnivInBiv g) (Finsupp.single 0 n + Finsupp.single 1 k) := by rw [h]
  rw [coeff_embedUnivInBiv, coeff_embedUnivInBiv] at h1
  exact h1

/-!
### Example: Binomial generating function

The source derives the following identity using bivariate power series:

```
∑_{n,k∈ℕ} C(n,k) x^n y^k = 1/(1 - x(1+y))
```

From this, by comparing coefficients of `y^k`, one obtains the univariate identity:
```
x^k / (1-x)^{k+1} = ∑_{n∈ℕ} C(n,k) x^n  for each k ∈ ℕ
```

This is equation `eq.fps.mulvar.exa1.res1` in the source.
-/

/-- The generating function for binomial coefficients as a bivariate power series:
    `∑_{n,k∈ℕ} C(n,k) x^n y^k`. -/
noncomputable def binomialGenFun : BivFPS ℚ :=
  fun nm => (nm 0).choose (nm 1)

/-- The closed form `1/(1 - x(1+y))` for the binomial generating function. -/
noncomputable def binomialGenFunClosedForm : BivFPS ℚ :=
  MvPowerSeries.invOfUnit (1 - BivFPS.x * (1 + BivFPS.y)) 1

/-- The binomial generating function equals its closed form.
    `∑_{n,k∈ℕ} C(n,k) x^n y^k = 1/(1 - x(1+y))`

    This is the main computation in the example from the source. -/
theorem binomialGenFun_eq : binomialGenFun = binomialGenFunClosedForm := by
  -- Helper lemmas for index manipulation
  have single_0_1_le_iff : ∀ nm : Fin 2 →₀ ℕ, single (0 : Fin 2) 1 ≤ nm ↔ 1 ≤ nm 0 :=
    fun nm => Finsupp.single_le_iff
  have single_01_11_le_iff : ∀ nm : Fin 2 →₀ ℕ,
      single (0 : Fin 2) 1 + single 1 1 ≤ nm ↔ 1 ≤ nm 0 ∧ 1 ≤ nm 1 := fun nm => by
    constructor
    · intro h
      constructor
      · have := h 0; simp at this; exact this
      · have := h 1; simp at this; exact this
    · intro ⟨h0, h1⟩ i
      fin_cases i <;> simp [h0, h1]
  have sub_single_0_1_eval : ∀ nm : Fin 2 →₀ ℕ,
      (nm - single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 0 = nm 0 - 1 ∧
      (nm - single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 1 = nm 1 := fun nm => by simp [Finsupp.coe_tsub]
  have sub_single_01_11_eval : ∀ nm : Fin 2 →₀ ℕ,
      (nm - (single (0 : Fin 2) 1 + single 1 1) : Fin 2 →₀ ℕ) 0 = nm 0 - 1 ∧
      (nm - (single (0 : Fin 2) 1 + single 1 1) : Fin 2 →₀ ℕ) 1 = nm 1 - 1 :=
    fun nm => by simp [Finsupp.coe_tsub]
  -- Pascal's identity in the form C(n,k) = C(n-1,k-1) + C(n-1,k) for n,k ≥ 1
  have pascal_identity : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      n.choose k = (n - 1).choose (k - 1) + (n - 1).choose k := fun n k hn hk => by
    have h1 : (n - 1).succ = n := Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    have h2 : (k - 1).succ = k := Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
    rw [← h1, ← h2]; exact Nat.choose_succ_succ (n - 1) (k - 1)
  -- Constant coefficient of the denominator 1 - x*(1+y) is 1
  have constantCoeff_denom : constantCoeff (1 - BivFPS.x * (1 + BivFPS.y) : BivFPS ℚ) = 1 := by
    simp only [BivFPS.x, BivFPS.y, map_sub, map_mul, map_add, constantCoeff_one, constantCoeff_X,
      add_zero]; ring
  -- Main coefficient calculation: coeff of (1 - x*(1+y)) * binomialGenFun at nm
  -- Using: (1 - x - xy) * f = f - x*f - xy*f
  -- coeff at (n,k) is C(n,k) - C(n-1,k) - C(n-1,k-1) = 0 for n≥1 (by Pascal)
  -- and C(0,k) = δ_{k,0} for n=0
  have coeff_denom_mul : ∀ nm : Fin 2 →₀ ℕ,
      coeff nm ((1 - BivFPS.x * (1 + BivFPS.y)) * binomialGenFun) = if nm = 0 then 1 else 0 := by
    intro nm
    simp only [BivFPS.x, BivFPS.y, sub_mul, one_mul, mul_add, mul_one, map_sub]
    rw [add_mul]; simp only [map_add]
    have hf : coeff nm binomialGenFun = (nm 0).choose (nm 1) := rfl
    have hxf : coeff nm (X 0 * binomialGenFun) =
        if 1 ≤ nm 0 then ((nm 0 - 1).choose (nm 1) : ℚ) else 0 := by
      rw [X, coeff_monomial_mul, one_mul]; simp only [single_0_1_le_iff]
      split_ifs with h
      · have heval := sub_single_0_1_eval nm
        show binomialGenFun (nm - _) = _
        unfold binomialGenFun
        simp only [heval.1, heval.2]
      · rfl
    have hxyf : coeff nm (X 0 * X 1 * binomialGenFun) =
        if 1 ≤ nm 0 ∧ 1 ≤ nm 1 then ((nm 0 - 1).choose (nm 1 - 1) : ℚ) else 0 := by
      rw [X, X, monomial_mul_monomial, one_mul, coeff_monomial_mul, one_mul]
      simp only [single_01_11_le_iff]
      split_ifs with h
      · have heval := sub_single_01_11_eval nm
        show binomialGenFun (nm - _) = _
        unfold binomialGenFun
        simp only [heval.1, heval.2]
      · rfl
    rw [hf, hxf, hxyf]
    by_cases h0 : nm 0 = 0
    · have hle : ¬(1 ≤ nm 0) := by omega
      simp only [hle, ↓reduceIte, false_and]
      by_cases h1 : nm 1 = 0
      · simp only [h0, h1, Nat.choose_self, Nat.cast_one]
        have : nm = 0 := by ext i; fin_cases i <;> simp [h0, h1]
        simp [this]
      · have hne : nm ≠ 0 := by intro heq; rw [heq] at h1; simp at h1
        simp only [hne, ↓reduceIte]
        rw [Nat.choose_eq_zero_of_lt]; simp; simp [h0]; omega
    · have h0' : 1 ≤ nm 0 := Nat.one_le_iff_ne_zero.mpr h0
      simp only [h0', ↓reduceIte, true_and]
      have hne : nm ≠ 0 := by intro heq; rw [heq] at h0; simp at h0
      simp only [hne, ↓reduceIte]
      by_cases h1 : nm 1 = 0
      · simp only [h1, Nat.choose_zero_right, Nat.cast_one]; norm_num
      · have h1' : 1 ≤ nm 1 := Nat.one_le_iff_ne_zero.mpr h1
        simp only [h1', ↓reduceIte]
        have pascal := pascal_identity (nm 0) (nm 1) h0' h1'
        simp only [pascal, Nat.cast_add]; ring
  -- The product (1 - x*(1+y)) * binomialGenFun equals 1
  have denom_mul_eq_one : (1 - BivFPS.x * (1 + BivFPS.y)) * binomialGenFun = 1 := by
    ext nm; rw [coeff_denom_mul, coeff_one]
  -- Conclude using uniqueness of inverse in power series ring
  have hne : constantCoeff (1 - BivFPS.x * (1 + BivFPS.y) : BivFPS ℚ) ≠ 0 := by
    rw [constantCoeff_denom]; exact one_ne_zero
  have h1 : binomialGenFunClosedForm = (1 - BivFPS.x * (1 + BivFPS.y))⁻¹ := by
    unfold binomialGenFunClosedForm
    rw [MvPowerSeries.invOfUnit_eq' _ 1 constantCoeff_denom]
  have h2 : binomialGenFun = (1 - BivFPS.x * (1 + BivFPS.y))⁻¹ := by
    rw [MvPowerSeries.eq_inv_iff_mul_eq_one hne, mul_comm]
    exact denom_mul_eq_one
  rw [h1, h2]

/-- The inverse of `1 - X` in `ℚ⟦X⟧` equals the power series with all coefficients 1. -/
lemma one_sub_X_inv_eq_mk_one : (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ = PowerSeries.mk 1 := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · exact PowerSeries.mk_one_mul_one_sub_eq_one ℚ
  · simp [PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_X]

/-- The univariate identity `X^k * (1-X)⁻¹^(k+1) = ∑_n C(n,k) X^n`.
    This is used to prove `binomialGenFun_xyk_eq`. -/
lemma X_pow_mul_inv_one_sub_pow_eq_mk_choose (k : ℕ) :
    (PowerSeries.X : PowerSeries ℚ) ^ k * (1 - PowerSeries.X)⁻¹ ^ (k + 1) =
    PowerSeries.mk (fun n => (n.choose k : ℚ)) := by
  ext n
  rw [one_sub_X_inv_eq_mk_one, PowerSeries.mk_one_pow_eq_mk_choose_add ℚ k]
  rw [PowerSeries.coeff_X_pow_mul']
  simp only [PowerSeries.coeff_mk]
  split_ifs with h
  · congr 1
    rw [Nat.add_sub_cancel' h]
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le h)]
    simp

/-- **Equation `eq.fps.mulvar.exa1.xyk`**: The intermediate bivariate identity
    `∑_{k∈ℕ} x^k/(1-x)^{k+1} y^k = ∑_{k∈ℕ} (∑_{n∈ℕ} C(n,k) x^n) y^k`

    expressed as equality of embedded univariate sequences. The left side is the
    sequence `k ↦ x^k/(1-x)^{k+1}` and the right side is `k ↦ ∑_{n∈ℕ} C(n,k) x^n`.

    This equation is used to derive `eq.fps.mulvar.exa1.res1` by comparing coefficients. -/
theorem binomialGenFun_xyk_eq :
    embedUnivInBiv (fun k => (PowerSeries.X : PowerSeries ℚ) ^ k *
                            (1 - PowerSeries.X)⁻¹ ^ (k + 1)) =
    embedUnivInBiv (fun k => PowerSeries.mk (fun n => (n.choose k : ℚ))) := by
  congr 1
  funext k
  exact X_pow_mul_inv_one_sub_pow_eq_mk_choose k

/-- **Equation `eq.fps.mulvar.exa1.res1`**: The generating function identity
    `x^k / (1-x)^{k+1} = ∑_{n∈ℕ} C(n,k) x^n` for each `k ∈ ℕ`.

    This is derived from the bivariate identity by comparing coefficients of `y^k`. -/
theorem sum_choose_pow_eq (k : ℕ) :
    (PowerSeries.X : PowerSeries ℚ) ^ k * (1 - PowerSeries.X)⁻¹ ^ (k + 1) =
    PowerSeries.mk (fun n => (n.choose k : ℚ)) := by
  have h := eq_of_embedUnivInBiv_eq _ _ binomialGenFun_xyk_eq
  exact congrFun h k

/-!
### Partial Derivatives

The source mentions that multivariate FPSs have `k` partial derivatives (one for each variable).
This section provides the basic infrastructure for partial derivatives.

In Mathlib, more general derivation theory is available via `MvPowerSeries.derivation`.
Here we provide a direct definition that matches the source's description:
for `f = ∑_m a_m x^m`, we have `∂f/∂x_i = ∑_m m_i · a_m · x^{m - e_i}`.
-/

/-- The partial derivative of a multivariate power series with respect to variable `i`.
    For `f = ∑_m a_m x^m`, we have `∂f/∂x_i = ∑_m m_i · a_m · x^{m - e_i}`
    where `e_i` is the `i`-th standard basis vector. -/
noncomputable def partialDeriv {σ : Type*} [DecidableEq σ] (i : σ) :
    MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun f := fun m =>
    let m' := m + Finsupp.single i 1
    (m' i : R) * MvPowerSeries.coeff m' f
  map_add' f g := by
    funext m
    simp only [map_add, mul_add]
    rfl
  map_smul' c f := by
    funext m
    simp only [RingHom.id_apply, smul_eq_mul, map_smul]
    change _ = c * _
    ring

/-- The coefficient of `partialDeriv i f` at `m` is `(m + single i 1) i * coeff (m + single i 1) f`. -/
lemma coeff_partialDeriv {σ : Type*} [DecidableEq σ] (i : σ) (f : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (partialDeriv i f) = (DFunLike.coe (m + Finsupp.single i 1) i : R) * coeff (m + Finsupp.single i 1) f := by
  simp only [partialDeriv, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The map `(a, b) ↦ (a + single i 1, b)` gives a bijection from `antidiagonal m` to
    the subset of `antidiagonal (m + single i 1)` where `single i 1 ≤ a`. -/
lemma antidiag_shift_fst {σ : Type*} [DecidableEq σ] (i : σ) (m : σ →₀ ℕ) :
    (antidiagonal m).map ⟨fun p => (p.1 + Finsupp.single i 1, p.2), fun p q h => by
      simp only [Prod.mk.injEq] at h
      have h1 : p.1 = q.1 := add_right_cancel h.1
      have h2 : p.2 = q.2 := h.2
      ext <;> simp [h1, h2]⟩ =
    (antidiagonal (m + Finsupp.single i 1)).filter (fun p => Finsupp.single i 1 ≤ p.1) := by
  ext ⟨a, b⟩
  simp only [mem_map, mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
    Function.Embedding.coeFn_mk, Prod.mk.injEq,
    Prod.exists]
  constructor
  · rintro ⟨a', b', hab, rfl, rfl⟩
    constructor
    · rw [add_comm a', add_assoc, hab, add_comm]
    · exact le_add_left le_rfl
  · rintro ⟨hab, hle⟩
    refine ⟨a - Finsupp.single i 1, b, ?_, ?_, rfl⟩
    · have : a - Finsupp.single i 1 + b + Finsupp.single i 1 = m + Finsupp.single i 1 := by
        rw [add_comm (a - _), add_assoc, tsub_add_cancel_of_le hle, add_comm, hab]
      exact add_right_cancel this
    · rw [tsub_add_cancel_of_le hle]

set_option backward.isDefEq.respectTransparency false in
/-- The map `(a, b) ↦ (a, b + single i 1)` gives a bijection from `antidiagonal m` to
    the subset of `antidiagonal (m + single i 1)` where `single i 1 ≤ b`. -/
lemma antidiag_shift_snd {σ : Type*} [DecidableEq σ] (i : σ) (m : σ →₀ ℕ) :
    (antidiagonal m).map ⟨fun p => (p.1, p.2 + Finsupp.single i 1), fun p q h => by
      simp only [Prod.mk.injEq] at h
      have h1 : p.1 = q.1 := h.1
      have h2 : p.2 = q.2 := add_right_cancel h.2
      ext <;> simp [h1, h2]⟩ =
    (antidiagonal (m + Finsupp.single i 1)).filter (fun p => Finsupp.single i 1 ≤ p.2) := by
  ext ⟨a, b⟩
  simp only [mem_map, mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
    Function.Embedding.coeFn_mk, Prod.mk.injEq,
    Prod.exists]
  constructor
  · rintro ⟨a', b', hab, rfl, rfl⟩
    constructor
    · rw [← add_assoc, hab, add_comm]
    · exact le_add_left le_rfl
  · rintro ⟨hab, hle⟩
    refine ⟨a, b - Finsupp.single i 1, ?_, rfl, ?_⟩
    · have : a + (b - Finsupp.single i 1) + Finsupp.single i 1 = m + Finsupp.single i 1 := by
        rw [add_assoc, tsub_add_cancel_of_le hle, hab]
      exact add_right_cancel this
    · rw [tsub_add_cancel_of_le hle]

/-- Terms where `p.1 i = 0` contribute zero to the first derivative sum. -/
lemma sum_filter_zero_fst {σ : Type*} [DecidableEq σ] (i : σ) (m : σ →₀ ℕ)
    (f g : MvPowerSeries σ R) :
    ∑ p ∈ (antidiagonal (m + Finsupp.single i 1)).filter (fun p => ¬(Finsupp.single i (1 : ℕ) ≤ p.1)),
      (p.1 i : R) * coeff p.1 f * coeff p.2 g = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finsupp.single_le_iff,
    not_le] at hp
  have : p.1 i = 0 := by omega
  simp [this]

/-- Terms where `p.2 i = 0` contribute zero to the second derivative sum. -/
lemma sum_filter_zero_snd {σ : Type*} [DecidableEq σ] (i : σ) (m : σ →₀ ℕ)
    (f g : MvPowerSeries σ R) :
    ∑ p ∈ (antidiagonal (m + Finsupp.single i 1)).filter (fun p => ¬(Finsupp.single i (1 : ℕ) ≤ p.2)),
      coeff p.1 f * ((p.2 i : R) * coeff p.2 g) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finsupp.single_le_iff,
    not_le] at hp
  have : p.2 i = 0 := by omega
  simp [this]

set_option backward.isDefEq.respectTransparency false in
/-- The partial derivative satisfies the product rule. -/
theorem partialDeriv_mul {σ : Type*} [DecidableEq σ] (i : σ)
    (f g : MvPowerSeries σ R) :
    partialDeriv i (f * g) = partialDeriv i f * g + f * partialDeriv i g := by
  ext m
  rw [coeff_partialDeriv, coeff_mul, map_add, coeff_mul, coeff_mul]
  simp only [coeff_partialDeriv]
  set m' := m + Finsupp.single i 1 with hm'
  -- Distribute the scalar over the sum
  rw [Finset.mul_sum]
  -- Split each term: (m' i) * f(a) * g(b) = (a i) * f(a) * g(b) + f(a) * (b i) * g(b)
  -- because m' i = a i + b i for (a, b) ∈ antidiagonal m'
  have hsplit : ∀ p ∈ antidiagonal m',
      (DFunLike.coe m' i : R) * (coeff p.1 f * coeff p.2 g) =
      (p.1 i : R) * coeff p.1 f * coeff p.2 g + coeff p.1 f * ((p.2 i : R) * coeff p.2 g) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have : DFunLike.coe m' i = p.1 i + p.2 i := by
      rw [← hp]; simp only [Finsupp.coe_add, Pi.add_apply]
    rw [this]; push_cast; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- Reindex using the bijections: terms with p.1 i = 0 or p.2 i = 0 vanish
  have eq1 : ∑ x ∈ antidiagonal m', (x.1 i : R) * coeff x.1 f * coeff x.2 g =
             ∑ x ∈ antidiagonal m, (DFunLike.coe (x.1 + Finsupp.single i 1) i : R) *
                                   coeff (x.1 + Finsupp.single i 1) f * coeff x.2 g := by
    rw [← Finset.sum_filter_add_sum_filter_not (antidiagonal m') (fun p => Finsupp.single i 1 ≤ p.1)]
    rw [sum_filter_zero_fst, add_zero, ← antidiag_shift_fst, Finset.sum_map]
    apply Finset.sum_congr rfl; intro x _; simp only [Function.Embedding.coeFn_mk]
  have eq2 : ∑ x ∈ antidiagonal m', coeff x.1 f * ((x.2 i : R) * coeff x.2 g) =
             ∑ x ∈ antidiagonal m, coeff x.1 f * ((DFunLike.coe (x.2 + Finsupp.single i 1) i : R) *
                                                   coeff (x.2 + Finsupp.single i 1) g) := by
    rw [← Finset.sum_filter_add_sum_filter_not (antidiagonal m') (fun p => Finsupp.single i 1 ≤ p.2)]
    rw [sum_filter_zero_snd, add_zero, ← antidiag_shift_snd, Finset.sum_map]
    apply Finset.sum_congr rfl; intro x _; simp only [Function.Embedding.coeFn_mk]
  rw [eq1, eq2]

/-!
### Substitution in multivariate power series

One needs to be careful with substitution - one cannot substitute non-commuting elements
into a multivariate polynomial. For example, you cannot substitute two non-commuting
matrices `A` and `B` for `x` and `y` into the polynomial `xy` without sacrificing the
rule that a value of the product of two polynomials should be the product of their values.

However, you can still substitute `k` commuting elements for the `k` indeterminates
in a `k`-variable polynomial. You can also compose multivariate FPSs as long as
appropriate summability conditions are satisfied.

The full theory of evaluation/substitution for multivariate power series is available
in Mathlib via `MvPowerSeries.eval` and related constructions.
-/

end AlgebraicCombinatorics
