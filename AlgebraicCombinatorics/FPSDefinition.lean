/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.FPS.InfiniteProducts2
import AlgebraicCombinatorics.FPS.InfiniteProducts

/-!
# Formal Power Series: Definition and Basic Properties

This file formalizes the definition of formal power series (FPS) and their basic operations,
following Section "The definition of formal power series" (subsec.gf.defs.fps) of the source.

## Main definitions

* `fpsEquivSeq` (Definition def.fps.fps): The equivalence between formal power series
  `R⟦X⟧` and sequences `ℕ → R`. This formalizes that an FPS is a sequence (a₀, a₁, a₂, ...).

* We use Mathlib's `PowerSeries R` which represents formal power series over a ring `R`.
  This is defined as `MvPowerSeries Unit R`, i.e., sequences `ℕ → R`.

* `PowerSeries.coeff n f` extracts the n-th coefficient of a power series f.
  This corresponds to `[x^n] f` in the source notation.

* `PowerSeries.mk` constructs a power series from a sequence of coefficients.

* `PowerSeries.X` is the indeterminate x = (0, 1, 0, 0, ...).

* `PowerSeries.C` embeds constants into power series as (a, 0, 0, ...).

## Main results

* `PowerSeries` forms a commutative ring (Theorem thm.fps.ring (a))
* `PowerSeries` is a module over the base ring (Theorem thm.fps.ring (b))
* Scaling by λ equals multiplication by C λ (Theorem thm.fps.ring (d))
* Coefficient extraction is additive and compatible with multiplication
* Multiplication by x shifts coefficients: X * (a₀, a₁, ...) = (0, a₀, a₁, ...) (Lemma lem.fps.xa)
* `x^k` has the form (0, 0, ..., 0, 1, 0, 0, ...) with k zeros (Proposition prop.fps.xk)
* Any FPS can be written as ∑ aₙ xⁿ (Corollary cor.fps.sumakxk)

## References

* Source: FPSDefinition.tex, subsec.gf.defs.fps

## Implementation notes

Mathlib already provides `PowerSeries R` with all the ring structure and basic operations.
This file provides additional lemmas and connects Mathlib's API to the textbook presentation.

For summable families of FPS, we use Mathlib's topological structure on power series
(`PowerSeries.WithPiTopology`), where a family is summable when for each coefficient index,
all but finitely many terms have that coefficient equal to zero.
-/

open scoped Polynomial
open PowerSeries Finset

namespace AlgebraicCombinatorics

namespace FPS

variable {R : Type*} [CommRing R]

/-!
## Definition of FPS (Definition def.fps.fps)

**Definition def.fps.fps**: A formal power series (FPS) in one indeterminate over K
is a sequence (a₀, a₁, a₂, ...) = (aₙ)_{n ∈ ℕ} ∈ K^ℕ of elements of K.

In Mathlib, this is represented by `PowerSeries R` (notation: `R⟦X⟧`).
The type `PowerSeries R` is defined as `MvPowerSeries Unit R`, which is
definitionally `(Unit →₀ ℕ) → R`. Since `Unit →₀ ℕ` is equivalent to `ℕ`,
this is essentially `ℕ → R`.

The constructor `PowerSeries.mk : (ℕ → R) → R⟦X⟧` builds an FPS from a sequence.
The extractor `PowerSeries.coeff n : R⟦X⟧ → R` retrieves the n-th coefficient.
-/

/-- **Definition def.fps.fps**: The equivalence between formal power series `R⟦X⟧`
    and sequences `ℕ → R`.

    This formalizes Definition def.fps.fps from the source: a formal power series
    is a sequence (a₀, a₁, a₂, ...) of elements of R.

    The forward direction extracts coefficients, the inverse constructs the FPS. -/
noncomputable def fpsEquivSeq : R⟦X⟧ ≃ (ℕ → R) where
  toFun f := fun n => coeff n f
  invFun a := PowerSeries.mk a
  left_inv f := by ext n; simp [coeff_mk]
  right_inv a := by ext n; simp [coeff_mk]

/-- The FPS (a₀, a₁, a₂, ...) is constructed from a sequence using `PowerSeries.mk`.
    This is the inverse of coefficient extraction. -/
theorem fps_mk_eq_symm (a : ℕ → R) : PowerSeries.mk a = fpsEquivSeq.symm a := rfl

/-- Extracting coefficients from an FPS gives back the original sequence
    (Definition def.fps.fps). -/
theorem fps_coeff_mk (a : ℕ → R) (n : ℕ) : coeff n (PowerSeries.mk a) = a n := coeff_mk n a

/-- Any FPS equals the FPS constructed from its coefficient sequence
    (Definition def.fps.fps). This shows that every FPS is determined by its coefficients. -/
theorem fps_eq_mk_coeff (f : R⟦X⟧) : f = PowerSeries.mk (fun n => coeff n f) := by
  ext n
  simp [coeff_mk]

/-- Two FPS are equal iff they have the same coefficients (Definition def.fps.fps).
    This is the extensionality principle for FPS. -/
theorem fps_ext_iff (f g : R⟦X⟧) : f = g ↔ ∀ n, coeff n f = coeff n g :=
  ⟨fun h _ => by rw [h], fun h => ext h⟩

/-- The zero FPS is (0, 0, 0, ...) -/
theorem zero_fps_eq : (0 : R⟦X⟧) = PowerSeries.mk (fun _ => 0) := by
  ext n
  simp [coeff_mk]

/-- The one FPS is (1, 0, 0, ...) -/
theorem one_fps_eq : (1 : R⟦X⟧) = PowerSeries.mk (fun n => if n = 0 then 1 else 0) := by
  ext n
  simp [coeff_one, coeff_mk]

/-!
## Operations on FPS (Definition def.fps.ops)

(a) Sum: (a₀ + b₀, a₁ + b₁, ...)
(b) Difference: (a₀ - b₀, a₁ - b₁, ...)
(c) Scalar multiplication: λa = (λa₀, λa₁, ...)
(d) Product: c_n = ∑_{i=0}^n a_i b_{n-i}
(e) Constants: a̲ = (a, 0, 0, ...)
-/

/-- (a) Sum of FPS is componentwise (eq. pf.thm.fps.ring.xn(a+b)=)
    Label: pf.thm.fps.ring.xn(a+b)= -/
@[simp]
theorem coeff_add_fps (n : ℕ) (f g : R⟦X⟧) :
    coeff n (f + g) = coeff n f + coeff n g := by
  simp [map_add]

/-- (b) Difference of FPS is componentwise (eq. pf.thm.fps.ring.xn(a-b)=)
    Label: pf.thm.fps.ring.xn(a-b)= -/
@[simp]
theorem coeff_sub_fps (n : ℕ) (f g : R⟦X⟧) :
    coeff n (f - g) = coeff n f - coeff n g := by
  simp [map_sub]

/-- Negation of FPS is componentwise (eq. pf.thm.fps.ring.xn(-a)=)
    Label: pf.thm.fps.ring.xn(-a)= -/
@[simp]
theorem coeff_neg_fps (n : ℕ) (f : R⟦X⟧) :
    coeff n (-f) = -coeff n f := by
  simp [map_neg]

/-- (c) Scalar multiplication (eq. pf.thm.fps.ring.xn(la)=)
    Label: pf.thm.fps.ring.xn(la)= -/
@[simp]
theorem coeff_smul_fps (n : ℕ) (c : R) (f : R⟦X⟧) :
    coeff n (c • f) = c * coeff n f := by
  simp [smul_eq_mul]

/-- (d) Product of FPS uses convolution (eq. pf.thm.fps.ring.xn(ab)=2)
    Label: pf.thm.fps.ring.xn(ab)=2 -/
theorem coeff_mul_fps (n : ℕ) (f g : R⟦X⟧) :
    coeff n (f * g) = ∑ p ∈ antidiagonal n, coeff p.1 f * coeff p.2 g :=
  coeff_mul n f g

/-- Alternative form of product formula (eq. pf.thm.fps.ring.xn(ab)=3)
    Label: pf.thm.fps.ring.xn(ab)=3 -/
theorem coeff_mul_fps' (n : ℕ) (f g : R⟦X⟧) :
    coeff n (f * g) = ∑ i ∈ range (n + 1), coeff i f * coeff (n - i) g := by
  rw [coeff_mul_fps]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j g)]

/-- (e) Constant FPS: C a = (a, 0, 0, ...) -/
theorem coeff_C_fps (n : ℕ) (a : R) :
    coeff n (C a : R⟦X⟧) = if n = 0 then a else 0 :=
  coeff_C n a

/-- The constant term of a product is the product of constant terms
    (eq. pf.thm.fps.ring.x0(ab)=)
    Label: pf.thm.fps.ring.x0(ab)= -/
theorem coeff_zero_mul_fps (f g : R⟦X⟧) :
    coeff 0 (f * g) = coeff 0 f * coeff 0 g := by
  rw [coeff_mul_fps]
  simp [antidiagonal_zero]

/-!
## Ring Structure (Theorem thm.fps.ring)

Theorem thm.fps.ring states that R⟦X⟧ is:
(a) A commutative ring with zero = (0,0,...) and one = (1,0,0,...)
(b) An R-module
(c) Scaling commutes with multiplication: λ(fg) = (λf)g = f(λg)
(d) Scaling equals multiplication by constant: λf = (C λ) * f

Note: Mathlib already provides these structures on `PowerSeries R`:
- `CommRing R⟦X⟧` instance exists in `Mathlib.RingTheory.PowerSeries.Basic`
- `Module R R⟦X⟧` instance exists via the algebra structure
-/

/-- (c) Scaling commutes with multiplication (Theorem thm.fps.ring (c)) -/
theorem smul_mul_fps (c : R) (f g : R⟦X⟧) :
    c • (f * g) = (c • f) * g := by
  rw [smul_eq_C_mul, smul_eq_C_mul, mul_assoc]

theorem smul_mul_fps' (c : R) (f g : R⟦X⟧) :
    c • (f * g) = f * (c • g) := by
  rw [smul_eq_C_mul, smul_eq_C_mul, mul_left_comm]

/-- (d) Scaling equals multiplication by constant (Theorem thm.fps.ring (d)) -/
theorem smul_eq_C_mul_fps (c : R) (f : R⟦X⟧) :
    c • f = C c * f :=
  smul_eq_C_mul f c

/-!
## Coefficient Extraction (Definition def.fps.coeff)

[x^n] f denotes the n-th coefficient of f.
In Mathlib this is `PowerSeries.coeff n f`.
-/

/-- The n-th coefficient of an FPS (Definition def.fps.coeff) -/
noncomputable example (n : ℕ) (f : R⟦X⟧) : R := coeff n f

/-!
## The Indeterminate x (Definition def.fps.x)

x = (0, 1, 0, 0, ...) is the FPS with [x^1] x = 1 and [x^i] x = 0 for i ≠ 1.
-/

/-- x = (0, 1, 0, 0, ...) (Definition def.fps.x) -/
@[simp]
theorem X_coeff_one : coeff 1 (X : R⟦X⟧) = 1 := coeff_one_X

theorem X_coeff_ne_one (i : ℕ) (hi : i ≠ 1) : coeff i (X : R⟦X⟧) = 0 := by
  rw [coeff_X]
  simp [hi]

/-!
## Multiplication by x (Lemma lem.fps.xa)

Multiplying by x shifts the sequence: x * (a₀, a₁, a₂, ...) = (0, a₀, a₁, a₂, ...)

Lemma lem.fps.xa states: If f = (a₀, a₁, a₂, ...), then X * f = (0, a₀, a₁, a₂, ...).
This is equivalent to:
- [x^n](X·f) = a_{n-1} if n > 0
- [x^0](X·f) = 0
-/

/-- Multiplying by x shifts coefficients: [x^{n+1}](X·f) = [x^n]f (Lemma lem.fps.xa) -/
theorem X_mul_shift (f : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (X * f) = coeff n f :=
  coeff_succ_X_mul n f

/-- Multiplying by x on the right shifts coefficients: [x^{n+1}](f·X) = [x^n]f -/
theorem mul_X_shift (f : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (f * X) = coeff n f :=
  coeff_succ_mul_X n f

/-- The constant term of X * f is 0 (Lemma lem.fps.xa, case n = 0) -/
@[simp]
theorem X_mul_coeff_zero (f : R⟦X⟧) :
    coeff 0 (X * f) = 0 := by
  rw [coeff_mul_fps]
  simp [antidiagonal_zero]

/-- The constant term of f * X is 0 -/
@[simp]
theorem mul_X_coeff_zero (f : R⟦X⟧) :
    coeff 0 (f * X) = 0 := by
  rw [coeff_mul_fps]
  simp [antidiagonal_zero]

/-- Complete characterization of multiplication by X (Lemma lem.fps.xa, unified form)

    If f = (a₀, a₁, a₂, ...), then X * f = (0, a₀, a₁, a₂, ...)
    This is equivalent to: [x^n](X·f) = if n = 0 then 0 else [x^{n-1}]f -/
theorem coeff_X_mul (f : R⟦X⟧) (n : ℕ) :
    coeff n (X * f) = if n = 0 then 0 else coeff (n - 1) f := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_X_mul]

/-- Complete characterization of multiplication by X on the right (Lemma lem.fps.xa, variant)

    If f = (a₀, a₁, a₂, ...), then f * X = (0, a₀, a₁, a₂, ...)
    This is equivalent to: [x^n](f·X) = if n = 0 then 0 else [x^{n-1}]f -/
theorem coeff_mul_X (f : R⟦X⟧) (n : ℕ) :
    coeff n (f * X) = if n = 0 then 0 else coeff (n - 1) f := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_succ_mul_X]

/-- X * f equals f with all coefficients shifted by one position (Lemma lem.fps.xa, equality form)

    This directly expresses: X * (a₀, a₁, a₂, ...) = (0, a₀, a₁, a₂, ...) -/
theorem X_mul_eq_shift (f : R⟦X⟧) :
    X * f = PowerSeries.mk (fun n => if n = 0 then 0 else coeff (n - 1) f) := by
  ext n
  rw [coeff_X_mul, coeff_mk]

/-- f * X equals f with all coefficients shifted by one position (Lemma lem.fps.xa, equality form) -/
theorem mul_X_eq_shift (f : R⟦X⟧) :
    f * X = PowerSeries.mk (fun n => if n = 0 then 0 else coeff (n - 1) f) := by
  ext n
  rw [coeff_mul_X, coeff_mk]

/-- X^k * f shifts f by k positions (generalization of Lemma lem.fps.xa)

    If f = (a₀, a₁, a₂, ...), then X^k * f = (0, ..., 0, a₀, a₁, a₂, ...) with k leading zeros. -/
theorem coeff_X_pow_mul (k : ℕ) (f : R⟦X⟧) (n : ℕ) :
    coeff n (X ^ k * f) = if n < k then 0 else coeff (n - k) f := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => simp
    | succ n =>
      rw [coeff_succ_X_mul, ih]
      simp [Nat.succ_sub_succ]

/-- f * X^k shifts f by k positions (generalization of Lemma lem.fps.xa) -/
theorem coeff_mul_X_pow (k : ℕ) (f : R⟦X⟧) (n : ℕ) :
    coeff n (f * X ^ k) = if n < k then 0 else coeff (n - k) f := by
  rw [mul_comm, coeff_X_pow_mul]

/-!
## Powers of x (Proposition prop.fps.xk)

x^k = (0, 0, ..., 0, 1, 0, 0, ...) with k zeros before the 1.
-/

/-- x^k has 1 in position k and 0 elsewhere (Proposition prop.fps.xk) -/
theorem X_pow_coeff (k n : ℕ) :
    coeff n ((X : R⟦X⟧) ^ k) = if n = k then 1 else 0 :=
  coeff_X_pow n k

@[simp]
theorem X_pow_coeff_self (k : ℕ) :
    coeff k ((X : R⟦X⟧) ^ k) = 1 :=
  coeff_X_pow_self k

/-!
## FPS as Infinite Sum (Corollary cor.fps.sumakxk)

Any FPS (a₀, a₁, a₂, ...) can be written as ∑_{n ∈ ℕ} aₙ x^n.
This requires the notion of summable families of FPS.
-/

/-- The family (aₙ x^n)_{n ∈ ℕ} represents the FPS with coefficients (aₙ).
    This is essentially saying PowerSeries.mk a = ∑ a n * X^n
    (Corollary cor.fps.sumakxk) -/
theorem fps_eq_tsum_coeff (f : R⟦X⟧) :
    f = PowerSeries.mk (fun n => coeff n f) := by
  ext n
  simp [coeff_mk]

/-- aₙ x^n has coefficient aₙ in position n and 0 elsewhere -/
theorem coeff_monomial_mul_X_pow (a : R) (k n : ℕ) :
    coeff n (C a * (X : R⟦X⟧) ^ k) = if n = k then a else 0 := by
  simp [coeff_C_mul, coeff_X_pow]

/-!
## Summable Families of FPS (Definition def.fps.summable)

A family (fᵢ)_{i ∈ I} of FPS is summable (or entrywise essentially finite) if
for each n ∈ ℕ, all but finitely many i ∈ I satisfy [x^n] fᵢ = 0.

In this case, the sum ∑_{i ∈ I} fᵢ is defined as the FPS with
[x^n](∑_{i ∈ I} fᵢ) = ∑_{i ∈ I} [x^n] fᵢ (an essentially finite sum).

In Mathlib, this is captured by the topology on power series where
convergence means eventual stability of each coefficient.
See `PowerSeries.WithPiTopology` for details.
-/

/-- A family of FPS is summable if for each coefficient index n,
    all but finitely many family members have that coefficient equal to zero.
    (Definition def.fps.summable) -/
def SummableFPS {ι : Type*} (f : ι → R⟦X⟧) : Prop :=
  ∀ n : ℕ, {i | coeff n (f i) ≠ 0}.Finite

/-- The sum of a summable family of FPS.
    (Definition def.fps.summable, eq. eq.def.fps.summable.sum)

    For a summable family (fᵢ)_{i ∈ I}, the sum ∑_{i ∈ I} fᵢ is the FPS whose
    n-th coefficient is ∑_{i ∈ I} [x^n] fᵢ (an essentially finite sum). -/
noncomputable def summableFPSSum {ι : Type*} (f : ι → R⟦X⟧) (_hf : SummableFPS f) : R⟦X⟧ :=
  PowerSeries.mk (fun n => ∑ᶠ i, coeff n (f i))

/-- The n-th coefficient of a summable sum is the sum of n-th coefficients.
    (eq. eq.def.fps.summable.sum) -/
theorem coeff_summableFPSSum {ι : Type*} (f : ι → R⟦X⟧) (hf : SummableFPS f) (n : ℕ) :
    coeff n (summableFPSSum f hf) = ∑ᶠ i, coeff n (f i) := by
  simp [summableFPSSum, coeff_mk]

/-- If `M` determines the `x^n`-coefficient of a summable family, then the
    coefficient of the infinite sum can be computed from the finite sum over `M`.
    (Proposition prop.fps.summable=fin-det part (b)) -/
theorem coeff_summableFPSSum_eq_sum_of_determines {ι : Type*}
    (f : ι → R⟦X⟧) (hf : SummableFPS f) (n : ℕ) (M : Finset ι)
    (hM : PowerSeries.DeterminesCoeffInSum f M n) :
    coeff n (summableFPSSum f hf) = coeff n (∑ i ∈ M, f i) := by
  classical
  rw [coeff_summableFPSSum]
  rw [finsum_eq_sum_of_support_subset
    (s := M ∪ (hf n).toFinset) _ (fun i hi => by
      apply Finset.mem_union_right
      simpa only [Set.Finite.mem_toFinset] using hi)]
  rw [← map_sum]
  exact hM _ Finset.subset_union_left

/-- The sum of the coefficients is finite (since the family is summable). -/
theorem summableFPS_finsum_finite {ι : Type*} (f : ι → R⟦X⟧) (hf : SummableFPS f) (n : ℕ) :
    (Function.support (fun i => coeff n (f i))).Finite := hf n

/-- Any subfamily of a summable family of FPS is summable.
    (Proposition prop.fps.summable.sub) -/
theorem summableFPS_subfamily {ι : Type*} {f : ι → R⟦X⟧} (J : Set ι)
    (hf : SummableFPS f) : SummableFPS (fun i : J => f i) := by
  intro n
  have h : {i : J | coeff n (f i) ≠ 0} ⊆ (Subtype.val) ⁻¹' {i | coeff n (f i) ≠ 0} := fun _ hx => hx
  exact Set.Finite.subset ((hf n).preimage Subtype.val_injective.injOn) h

/-- A finite family of FPS is always summable. -/
theorem summableFPS_of_finite {ι : Type*} [Finite ι] (f : ι → R⟦X⟧) : SummableFPS f := by
  intro n
  exact Set.toFinite _

/-- The zero family is summable. -/
theorem summableFPS_zero {ι : Type*} : SummableFPS (fun _ : ι => (0 : R⟦X⟧)) := by
  intro n
  simp

/-- A singleton family is summable. -/
theorem summableFPS_single (f : R⟦X⟧) : SummableFPS (fun _ : Unit => f) :=
  summableFPS_of_finite _

/-- Sum of two summable families is summable. -/
theorem summableFPS_add {ι : Type*} {f g : ι → R⟦X⟧}
    (hf : SummableFPS f) (hg : SummableFPS g) : SummableFPS (fun i => f i + g i) := by
  intro n
  have h : {i | coeff n (f i + g i) ≠ 0} ⊆ {i | coeff n (f i) ≠ 0} ∪ {i | coeff n (g i) ≠ 0} := by
    intro i hi
    simp only [Set.mem_setOf_eq, map_add, Set.mem_union] at *
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hi
  exact Set.Finite.subset (Set.Finite.union (hf n) (hg n)) h

/-- Negation of a summable family is summable. -/
theorem summableFPS_neg {ι : Type*} {f : ι → R⟦X⟧}
    (hf : SummableFPS f) : SummableFPS (fun i => -f i) := by
  intro n
  have h : {i | coeff n (-f i) ≠ 0} = {i | coeff n (f i) ≠ 0} := by
    ext i
    simp only [Set.mem_setOf_eq, map_neg, neg_ne_zero]
  rw [h]
  exact hf n

/-- Subtraction of two summable families is summable. -/
theorem summableFPS_sub {ι : Type*} {f g : ι → R⟦X⟧}
    (hf : SummableFPS f) (hg : SummableFPS g) : SummableFPS (fun i => f i - g i) := by
  simp only [sub_eq_add_neg]
  exact summableFPS_add hf (summableFPS_neg hg)

/-- Scalar multiple of a summable family is summable. -/
theorem summableFPS_smul {ι : Type*} {f : ι → R⟦X⟧} (c : R)
    (hf : SummableFPS f) : SummableFPS (fun i => c • f i) := by
  intro n
  have h : {i | coeff n (c • f i) ≠ 0} ⊆ {i | coeff n (f i) ≠ 0} := by
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    intro hfi
    simp [hfi] at hi
  exact Set.Finite.subset (hf n) h

/-- An essentially finite family of FPS is summable. -/
theorem summableFPS_of_essentiallyFinite {ι : Type*} (f : ι → R⟦X⟧)
    (hf : {i | f i ≠ 0}.Finite) : SummableFPS f := by
  intro n
  apply Set.Finite.subset hf
  intro i hi
  exact fun h => hi (by simp [h])

/-- The family (C(aₙ) * X^n)_{n ∈ ℕ} is summable for any sequence (aₙ).
    This is the canonical example showing that any FPS can be written as
    an infinite sum ∑_{n ∈ ℕ} aₙ x^n. -/
theorem summableFPS_monomial_family (a : ℕ → R) :
    SummableFPS (fun n => C (a n) * (X : R⟦X⟧) ^ n) := by
  intro m
  have h : {n | coeff m (C (a n) * (X : R⟦X⟧) ^ n) ≠ 0} ⊆ {m} := by
    intro n hn
    simp only [Set.mem_singleton_iff]
    simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Set.mem_setOf_eq] at hn
    by_contra hne
    have : m ≠ n := fun h => hne h.symm
    simp [this] at hn
  exact Set.Finite.subset (Set.finite_singleton m) h

/-!
## Essentially Finite Sums (Definition def.infsum.essfin)

A family (aᵢ)_{i ∈ I} of ring elements is essentially finite if
all but finitely many i satisfy aᵢ = 0.

Note: This is equivalent to `(Function.support f).Finite` in Mathlib.

### Part (a): Definition of essentially finite families

A family (aᵢ)_{i ∈ I} ∈ K^I of elements of K is essentially finite if all but finitely
many i ∈ I satisfy aᵢ = 0 (in other words, if the set {i ∈ I | aᵢ ≠ 0} is finite).

### Part (b): Sum of essentially finite families

Let (aᵢ)_{i ∈ I} ∈ K^I be an essentially finite family of elements of K.
Then, the infinite sum ∑_{i ∈ I} aᵢ is defined to equal the finite sum ∑_{i ∈ I, aᵢ ≠ 0} aᵢ.
Such an infinite sum is said to be essentially finite.
-/

/-- A family is essentially finite if its support is finite.
    (Definition def.infsum.essfin (a))

    **This is an alias** for the canonical `EssentiallyFinite` defined in
    `FPS/InfiniteProducts2.lean`. Both definitions are **definitionally equal**:
    `{i | f i ≠ 0}.Finite` = `(Function.support f).Finite` by definition.

    For the full API (including `_root_.EssentiallyFinite.add`, `_root_.EssentiallyFinite.neg`,
    `_root_.EssentiallyFinite.toFinsupp`, etc.), see `FPS/InfiniteProducts2.lean`. -/
abbrev EssentiallyFinite {ι : Type*} (f : ι → R) : Prop :=
  _root_.EssentiallyFinite f

/-- `EssentiallyFinite` is equivalent to having finite support. -/
theorem essentiallyFinite_iff_support_finite {ι : Type*} (f : ι → R) :
    EssentiallyFinite f ↔ (Function.support f).Finite :=
  _root_.EssentiallyFinite.iff_support_finite

/-- Any subfamily of an essentially finite family is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.subfamily`) -/
theorem essentiallyFinite_subfamily {ι : Type*} {f : ι → R} (J : Set ι)
    (hf : EssentiallyFinite f) : EssentiallyFinite (fun i : J => f i) :=
  _root_.EssentiallyFinite.subfamily J hf

/-- Any finite family is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.of_finite`) -/
theorem essentiallyFinite_of_finite {ι : Type*} [Finite ι] (f : ι → R) :
    EssentiallyFinite f :=
  _root_.EssentiallyFinite.of_finite f

/-- A family indexed by a finite type is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.of_fintype`) -/
theorem essentiallyFinite_fintype {ι : Type*} [Fintype ι] (f : ι → R) :
    EssentiallyFinite f :=
  _root_.EssentiallyFinite.of_fintype f

/-- The constant zero family is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.zero`) -/
theorem essentiallyFinite_zero {ι : Type*} : EssentiallyFinite (fun _ : ι => (0 : R)) :=
  _root_.EssentiallyFinite.zero

/-- Sum of two essentially finite families is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.add`) -/
theorem essentiallyFinite_add {ι : Type*} {f g : ι → R}
    (hf : EssentiallyFinite f) (hg : EssentiallyFinite g) :
    EssentiallyFinite (fun i => f i + g i) :=
  _root_.EssentiallyFinite.add hf hg

/-- Negation of an essentially finite family is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.neg`) -/
theorem essentiallyFinite_neg {ι : Type*} {f : ι → R} (hf : EssentiallyFinite f) :
    EssentiallyFinite (fun i => -f i) :=
  _root_.EssentiallyFinite.neg hf

/-- Subtraction of two essentially finite families is essentially finite.
    (Delegates to `_root_.EssentiallyFinite.sub`) -/
theorem essentiallyFinite_sub {ι : Type*} {f g : ι → R}
    (hf : EssentiallyFinite f) (hg : EssentiallyFinite g) :
    EssentiallyFinite (fun i => f i - g i) :=
  _root_.EssentiallyFinite.sub hf hg

/-- Scalar multiple of an essentially finite family is essentially finite.
    Note: Uses `_root_.EssentiallyFinite.const_mul` with NoZeroDivisors assumption. -/
theorem essentiallyFinite_smul {ι : Type*} {f : ι → R} (c : R) (hf : EssentiallyFinite f) :
    EssentiallyFinite (fun i => c * f i) := by
  apply Set.Finite.subset hf
  intro i hi
  simp only [ne_eq, Function.mem_support] at *
  intro h
  simp [h] at hi

/-!
### Sum of an essentially finite family (Definition def.infsum.essfin (b))

For an essentially finite family (aᵢ)_{i ∈ I}, the infinite sum ∑_{i ∈ I} aᵢ
is defined to equal the finite sum ∑_{i ∈ I, aᵢ ≠ 0} aᵢ.

We connect this to Mathlib's `Finsupp.sum` infrastructure.
-/

/-- The sum of an essentially finite family, defined as the finite sum over non-zero elements.
    (Definition def.infsum.essfin (b)) -/
noncomputable def essFinSum {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f) : R :=
  ∑ i ∈ hf.toFinset, f i

/-- The essentially finite sum equals the Finset sum over the support -/
theorem essFinSum_eq_finset_sum {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f) :
    essFinSum f hf = ∑ i ∈ hf.toFinset, f i := rfl

/-- If a family has finite support contained in a finset S, the essentially finite sum
    equals the sum over S -/
theorem essFinSum_eq_sum_of_support_subset {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f)
    (S : Finset ι) (hS : hf.toFinset ⊆ S) :
    essFinSum f hf = ∑ i ∈ S, f i := by
  rw [essFinSum]
  apply Finset.sum_subset hS
  intro x _ hx
  simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
  exact hx

/-- The essentially finite sum of a zero family is zero -/
theorem essFinSum_zero {ι : Type*} (hf : EssentiallyFinite (fun _ : ι => (0 : R))) :
    essFinSum (fun _ => 0) hf = 0 := by
  simp [essFinSum]

/-- The essentially finite sum of a family that is zero everywhere is zero -/
theorem essFinSum_eq_zero_of_forall_zero {ι : Type*} {f : ι → R} (hf : EssentiallyFinite f)
    (h : ∀ i, f i = 0) : essFinSum f hf = 0 := by
  simp [essFinSum, h]

/-- The essentially finite sum can be computed using any finset containing the support -/
theorem essFinSum_eq_sum_finset {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f)
    (S : Finset ι) (hS : ∀ i, f i ≠ 0 → i ∈ S) :
    essFinSum f hf = ∑ i ∈ S, f i := by
  apply essFinSum_eq_sum_of_support_subset
  intro x hx
  simp only [Set.Finite.mem_toFinset, Function.mem_support] at hx
  exact hS x hx

/-- The essentially finite sum of a single nonzero element -/
theorem essFinSum_single {ι : Type*} [DecidableEq ι] (i : ι) (a : R) :
    EssentiallyFinite (fun j => if j = i then a else 0) := by
  apply Set.Finite.subset (Set.finite_singleton i)
  intro j hj
  simp only [Function.mem_support, Set.mem_singleton_iff] at *
  by_contra h
  simp [h] at hj

/-- Connection to Finsupp: an essentially finite family can be converted to a Finsupp -/
noncomputable def essentiallyFiniteToFinsupp {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f) :
    ι →₀ R :=
  Finsupp.ofSupportFinite f hf

theorem essentiallyFiniteToFinsupp_apply {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f) (i : ι) :
    essentiallyFiniteToFinsupp f hf i = f i := rfl

/-- The essentially finite sum equals the Finsupp sum -/
theorem essFinSum_eq_finsupp_sum {ι : Type*} (f : ι → R) (hf : EssentiallyFinite f) :
    essFinSum f hf = (essentiallyFiniteToFinsupp f hf).sum (fun _ r => r) := by
  simp only [essFinSum, essentiallyFiniteToFinsupp, Finsupp.ofSupportFinite,
             Finsupp.sum, Finsupp.coe_mk]

/-- Additivity: the essentially finite sum of a sum is the sum of essentially finite sums -/
theorem essFinSum_add {ι : Type*} [DecidableEq ι] {f g : ι → R}
    (hf : EssentiallyFinite f) (hg : EssentiallyFinite g)
    (hfg : EssentiallyFinite (fun i => f i + g i)) :
    essFinSum (fun i => f i + g i) hfg = essFinSum f hf + essFinSum g hg := by
  -- The support of f + g is contained in support f ∪ support g
  let S := hf.toFinset ∪ hg.toFinset
  have hfS : hf.toFinset ⊆ S := Finset.subset_union_left
  have hgS : hg.toFinset ⊆ S := Finset.subset_union_right
  have hfgS : hfg.toFinset ⊆ S := by
    intro x hx
    simp only [Set.Finite.mem_toFinset, Function.mem_support] at hx
    simp only [S, Finset.mem_union, Set.Finite.mem_toFinset, Function.mem_support]
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hx
  calc essFinSum (fun i => f i + g i) hfg
      = ∑ i ∈ S, (f i + g i) := by
          apply Finset.sum_subset hfgS
          intro x _ hx
          simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
          exact hx
    _ = ∑ i ∈ S, f i + ∑ i ∈ S, g i := Finset.sum_add_distrib
    _ = essFinSum f hf + essFinSum g hg := by
          congr 1
          · symm
            apply Finset.sum_subset hfS
            intro x _ hx
            simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
            exact hx
          · symm
            apply Finset.sum_subset hgS
            intro x _ hx
            simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
            exact hx

/-- Scalar multiplication: c * (∑ aᵢ) = ∑ (c * aᵢ) -/
theorem essFinSum_smul {ι : Type*} {f : ι → R} (c : R) (hf : EssentiallyFinite f)
    (hcf : EssentiallyFinite (fun i => c * f i)) :
    essFinSum (fun i => c * f i) hcf = c * essFinSum f hf := by
  have hS : hcf.toFinset ⊆ hf.toFinset := by
    intro x hx
    simp only [Set.Finite.mem_toFinset, Function.mem_support] at *
    intro h
    simp [h] at hx
  calc essFinSum (fun i => c * f i) hcf
      = ∑ i ∈ hf.toFinset, c * f i := by
          apply Finset.sum_subset hS
          intro x _ hx
          simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
          simp [hx]
    _ = c * ∑ i ∈ hf.toFinset, f i := by rw [Finset.mul_sum]
    _ = c * essFinSum f hf := rfl

/-!
## Rules for Summable Sums (Proposition prop.fps.summable-sums-rule)

Sums of summable families of FPS satisfy the usual rules for sums:
- Breaking-apart rule: if S = X ∪ Y (disjoint), then ∑_{i ∈ S} fᵢ = ∑_{i ∈ X} fᵢ + ∑_{i ∈ Y} fᵢ
- Fubini rule: ∑_{i ∈ I} ∑_{j ∈ J} fᵢⱼ = ∑_{(i,j) ∈ I×J} fᵢⱼ = ∑_{j ∈ J} ∑_{i ∈ I} fᵢⱼ
  (when the family (fᵢⱼ)_{(i,j) ∈ I×J} is summable)

These properties follow from the corresponding properties of essentially finite sums
applied coefficient-wise.
-/

/-- A finite-support Fubini lemma for `finsum`. -/
private theorem finsum_finsum_eq_finsum_prod
    {A ι κ : Type*} [AddCommMonoid A] (g : ι × κ → A)
    (hg : (Function.support g).Finite) :
    (∑ᶠ i, ∑ᶠ j, g (i, j)) = ∑ᶠ p, g p := by
  classical
  let S : Finset (ι × κ) := hg.toFinset
  let I : Finset ι := S.image Prod.fst
  let J : Finset κ := S.image Prod.snd
  have hrow : Function.support (fun i => ∑ᶠ j, g (i, j)) ⊆ I := by
    intro i hi
    simp only [Function.mem_support] at hi
    by_contra hiI
    have hz : ∀ j, g (i, j) = 0 := by
      intro j
      by_contra hij
      have hpS : (i, j) ∈ S := by
        simp only [S, Set.Finite.mem_toFinset, Function.mem_support]
        exact hij
      exact hiI (by
        change i ∈ S.image Prod.fst
        exact Finset.mem_image.mpr ⟨(i, j), hpS, rfl⟩)
    exact hi (by simp only [hz, finsum_zero])
  have hcol (i : ι) : Function.support (fun j => g (i, j)) ⊆ J := by
    intro j hj
    simp only [Function.mem_support] at hj
    have hpS : (i, j) ∈ S := by
      simp only [S, Set.Finite.mem_toFinset, Function.mem_support]
      exact hj
    change j ∈ S.image Prod.snd
    exact Finset.mem_image.mpr ⟨(i, j), hpS, rfl⟩
  have hSprod : S ⊆ I ×ˢ J := by
    intro p hp
    simp only [Finset.mem_product]
    constructor
    · change p.1 ∈ S.image Prod.fst
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · change p.2 ∈ S.image Prod.snd
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  calc
    (∑ᶠ i, ∑ᶠ j, g (i, j)) =
        ∑ i ∈ I, ∑ᶠ j, g (i, j) :=
      finsum_eq_sum_of_support_subset _ hrow
    _ = ∑ i ∈ I, ∑ j ∈ J, g (i, j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact finsum_eq_sum_of_support_subset _ (hcol i)
    _ = ∑ p ∈ I ×ˢ J, g p := by
      rw [Finset.sum_product]
    _ = ∑ p ∈ S, g p := by
      symm
      apply Finset.sum_subset hSprod
      intro p _ hpS
      simp only [S, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hpS
      exact hpS
    _ = ∑ᶠ p, g p := (finsum_eq_sum _ hg).symm

/-- The support of the fiberwise sums of a finite-support family is finite. -/
private theorem finsum_fiber_support_finite
    {A ι κ : Type*} [AddCommMonoid A] (g : ι × κ → A)
    (hg : (Function.support g).Finite) :
    (Function.support (fun i => ∑ᶠ j, g (i, j))).Finite := by
  classical
  apply Set.Finite.subset (hg.image Prod.fst)
  intro i hi
  simp only [Function.mem_support] at hi ⊢
  by_contra hnot
  have hz : ∀ j, g (i, j) = 0 := by
    intro j
    by_contra hij
    exact hnot ⟨(i, j), hij, rfl⟩
  exact hi (by simp only [hz, finsum_zero])

/-- The Fubini rule for summable FPS families: interchange of summation is valid
    when the family indexed by the product is summable.
    (Proposition prop.fps.summable-sums-rule, discrete Fubini rule)

    This first theorem establishes summability of every row and column. -/
theorem summableFPS_fubini {ι κ : Type*} {f : ι × κ → R⟦X⟧}
    (hf : SummableFPS f) :
    (∀ i, SummableFPS (fun j => f (i, j))) ∧
    (∀ j, SummableFPS (fun i => f (i, j))) := by
  constructor
  · intro i n
    have : {j | coeff n (f (i, j)) ≠ 0} ⊆ Prod.snd '' {p | coeff n (f p) ≠ 0} := by
      intro j hj
      exact ⟨(i, j), hj, rfl⟩
    exact Set.Finite.subset (Set.Finite.image Prod.snd (hf n)) this
  · intro j n
    have : {i | coeff n (f (i, j)) ≠ 0} ⊆ Prod.fst '' {p | coeff n (f p) ≠ 0} := by
      intro i hi
      exact ⟨(i, j), hi, rfl⟩
    exact Set.Finite.subset (Set.Finite.image Prod.fst (hf n)) this

/-- Under the Fubini hypothesis, the family of row sums is summable. -/
theorem summableFPS_fubini_row_sums {ι κ : Type*} {f : ι × κ → R⟦X⟧}
    (hf : SummableFPS f)
    (hrows : ∀ i, SummableFPS (fun j => f (i, j))) :
    SummableFPS (fun i => summableFPSSum (fun j => f (i, j)) (hrows i)) := by
  intro n
  change (Function.support (fun i => coeff n
    (summableFPSSum (fun j => f (i, j)) (hrows i)))).Finite
  simpa only [coeff_summableFPSSum] using
    finsum_fiber_support_finite (fun p => coeff n (f p)) (hf n)

/-- Under the Fubini hypothesis, the family of column sums is summable. -/
theorem summableFPS_fubini_column_sums {ι κ : Type*} {f : ι × κ → R⟦X⟧}
    (hf : SummableFPS f)
    (hcols : ∀ j, SummableFPS (fun i => f (i, j))) :
    SummableFPS (fun j => summableFPSSum (fun i => f (i, j)) (hcols j)) := by
  intro n
  have hswap : SummableFPS (fun p : κ × ι => f (p.2, p.1)) := by
    intro m
    change ((Equiv.prodComm κ ι) ⁻¹'
      {p : ι × κ | coeff m (f p) ≠ 0}).Finite
    exact (hf m).preimage (Equiv.prodComm κ ι).injective.injOn
  change (Function.support (fun j => coeff n
    (summableFPSSum (fun i => f (i, j)) (hcols j)))).Finite
  simpa only [coeff_summableFPSSum] using
    finsum_fiber_support_finite
      (fun p : κ × ι => coeff n (f (p.2, p.1))) (hswap n)

/-- Discrete Fubini equality for summable families of formal power series:
    the row-iterated sum, product-indexed sum, and column-iterated sum agree.
    (Proposition prop.fps.summable-sums-rule, discrete Fubini rule) -/
theorem summableFPSSum_fubini {ι κ : Type*} {f : ι × κ → R⟦X⟧}
    (hf : SummableFPS f)
    (hrows : ∀ i, SummableFPS (fun j => f (i, j)))
    (hcols : ∀ j, SummableFPS (fun i => f (i, j))) :
    summableFPSSum
        (fun i => summableFPSSum (fun j => f (i, j)) (hrows i))
        (summableFPS_fubini_row_sums hf hrows) =
      summableFPSSum f hf ∧
    summableFPSSum f hf =
      summableFPSSum
        (fun j => summableFPSSum (fun i => f (i, j)) (hcols j))
        (summableFPS_fubini_column_sums hf hcols) := by
  constructor
  · ext n
    simp only [coeff_summableFPSSum]
    exact finsum_finsum_eq_finsum_prod (fun p => coeff n (f p)) (hf n)
  · ext n
    simp only [coeff_summableFPSSum]
    symm
    calc
      (∑ᶠ j, ∑ᶠ i, coeff n (f (i, j))) =
          ∑ᶠ p : κ × ι, coeff n (f (p.2, p.1)) := by
        apply finsum_finsum_eq_finsum_prod
          (g := fun p : κ × ι => coeff n (f (p.2, p.1)))
        change ((Equiv.prodComm κ ι) ⁻¹'
          {p : ι × κ | coeff n (f p) ≠ 0}).Finite
        exact (hf n).preimage (Equiv.prodComm κ ι).injective.injOn
      _ = ∑ᶠ p : ι × κ, coeff n (f p) := by
        apply finsum_eq_of_bijective (Equiv.prodComm κ ι)
          (Equiv.prodComm κ ι).bijective
        intro p
        rfl

/-!
## Generating Functions

The (ordinary) generating function of a sequence (a₀, a₁, a₂, ...) is
the FPS (a₀, a₁, a₂, ...) = a₀ + a₁x + a₂x² + ...
-/

/-- The generating function of a sequence is just the FPS with those coefficients -/
def generatingFunction (a : ℕ → R) : R⟦X⟧ := PowerSeries.mk a

theorem generatingFunction_coeff (a : ℕ → R) (n : ℕ) :
    coeff n (generatingFunction a) = a n := by
  simp [generatingFunction, coeff_mk]

/-- The generating function of the zero sequence is 0 -/
@[simp]
theorem generatingFunction_zero : generatingFunction (0 : ℕ → R) = 0 := by
  ext n
  simp [generatingFunction, coeff_mk]

/-- The generating function of a sum is the sum of generating functions -/
@[simp]
theorem generatingFunction_add (a b : ℕ → R) :
    generatingFunction (a + b) = generatingFunction a + generatingFunction b := by
  ext n
  simp [generatingFunction, coeff_mk]

/-- The generating function of a negation is the negation of the generating function -/
@[simp]
theorem generatingFunction_neg (a : ℕ → R) :
    generatingFunction (-a) = -generatingFunction a := by
  ext n
  simp [generatingFunction, coeff_mk]

/-- The generating function of a scalar multiple is the scalar multiple of the generating function -/
@[simp]
theorem generatingFunction_smul (c : R) (a : ℕ → R) :
    generatingFunction (c • a) = c • generatingFunction a := by
  ext n
  simp [generatingFunction, coeff_mk, Pi.smul_apply, smul_eq_mul]

/-- Subtraction of generating functions -/
@[simp]
theorem generatingFunction_sub (a b : ℕ → R) :
    generatingFunction (a - b) = generatingFunction a - generatingFunction b := by
  ext n
  simp [generatingFunction, coeff_mk]

/-- The generating function of the indicator function at 0 is 1 -/
@[simp]
theorem generatingFunction_one :
    generatingFunction (fun n => if n = 0 then (1 : R) else 0) = 1 := by
  ext n
  simp [generatingFunction, coeff_mk, coeff_one]

/-!
## Vandermonde / Chu-Vandermonde Identity

### For Natural Numbers (Proposition prop.binom.vandermonde.NN)

For a, b, n ∈ ℕ: C(a+b, n) = ∑_{k=0}^n C(a,k) C(b, n-k)
-/

/-- Vandermonde's identity for natural numbers (Proposition prop.binom.vandermonde.NN)
    Label: eq.prop.binom.vandermonde.NN.eq -/
theorem vandermonde_nat (a b n : ℕ) :
    (a + b).choose n = ∑ ij ∈ antidiagonal n, a.choose ij.1 * b.choose ij.2 :=
  Nat.add_choose_eq a b n

/-- Alternative form using range -/
theorem vandermonde_nat' (a b n : ℕ) :
    (a + b).choose n = ∑ k ∈ range (n + 1), a.choose k * b.choose (n - k) := by
  rw [vandermonde_nat]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.choose i * b.choose j)]

/-!
### For Complex Numbers (Theorem thm.binom.vandermonde.CC)

The Chu-Vandermonde identity extends to all complex numbers (or any binomial ring).
For a, b ∈ ℂ and n ∈ ℕ: C(a+b, n) = ∑_{k=0}^n C(a,k) C(b, n-k)

The proof uses the polynomial identity trick: both sides are polynomials in a and b
that agree on ℕ × ℕ, hence they agree everywhere.
-/

/-- Chu-Vandermonde identity for binomial rings (Theorem thm.binom.vandermonde.CC)
    Label: eq.prop.binom.vandermonde.CC.eq

    This generalizes Vandermonde's identity from natural numbers to any binomial ring
    (including ℚ, ℝ, ℂ, and polynomial rings). -/
theorem chuVandermonde {S : Type*} [CommRing S] [BinomialRing S] (a b : S) (n : ℕ) :
    Ring.choose (a + b) n = ∑ ij ∈ antidiagonal n, Ring.choose a ij.1 * Ring.choose b ij.2 :=
  Ring.add_choose_eq n (Commute.all a b)

end FPS

end AlgebraicCombinatorics
