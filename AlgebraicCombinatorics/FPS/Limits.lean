/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import AlgebraicCombinatorics.FPS.XnEquivalence

/-!
# Limits of Formal Power Series

This file formalizes the notion of coefficientwise limits of formal power series,
following Section 7.5 of Loehr's "Bijective Combinatorics".

## Main Definitions

* `Seq.StabilizesTo`: A sequence `(a_i)_{i ∈ ℕ}` stabilizes to `a` if there exists `N`
  such that for all `i ≥ N`, we have `a_i = a`. (Definition 7.5.1)
* `PowerSeries.CoeffStabilizesTo`: A sequence of FPSs `(f_i)` coefficientwise stabilizes
  to `f` if for each `n ∈ ℕ`, the sequence of `n`-th coefficients stabilizes.
  (Definition 7.5.2)

## Main Results

* `PowerSeries.coeffStabilizesTo_of_forall_coeff_stabilizes`: If each coefficient sequence
  stabilizes, then the FPS sequence coefficientwise stabilizes. (Theorem 7.5.3)
* `PowerSeries.exists_xnEquiv_of_coeffStabilizesTo`: If `f_i → f`, then for each `n`,
  eventually `f_i ≡ f (mod x^{n+1})`. (Lemma 7.5.4)
* `PowerSeries.coeffStabilizesTo_add`: Limits respect addition. (Proposition 7.5.5)
* `PowerSeries.coeffStabilizesTo_mul`: Limits respect multiplication. (Proposition 7.5.5)
* `PowerSeries.coeffStabilizesTo_div`: Limits respect division. (Proposition 7.5.6)
* `PowerSeries.coeffStabilizesTo_comp`: Limits respect composition. (Proposition 7.5.7)
* `PowerSeries.coeffStabilizesTo_derivative`: Limits respect derivatives. (Proposition 7.5.8)
* `PowerSeries.coeffStabilizesTo_sum`: Infinite sum is limit of partial sums. (Theorem 7.5.9)
* `PowerSeries.coeffStabilizesTo_prod`: Infinite product is limit of partial products.
  (Theorem 7.5.10)
* `PowerSeries.fps_eq_limit_of_polynomials`: Each FPS is a limit of polynomials.
  (Corollary 7.5.11)

## Relationship with InfiniteProducts.lean

This file also defines `IsMultipliable` and `tprod'` for ℕ-indexed sequences of FPS.
These are **more restrictive** than the general `PowerSeries.Multipliable` and
`PowerSeries.tprod` in `InfiniteProducts.lean`:

* `IsMultipliable f` requires: (1) all constant terms equal 1, AND (2) eventually
  all terms are 1 + O(x^{n+1}) for each n.
* `PowerSeries.Multipliable a` only requires that each coefficient is finitely determined.

The `IsMultipliable`/`tprod'` definitions are used specifically for limits of partial
products (where the index is ℕ and we consider products `∏_{i=0}^{N} f_i`).
For general infinite products over arbitrary index types, use the definitions in
`InfiniteProducts.lean`.

## References

* [Loehr, *Bijective Combinatorics*, Section 7.5]
-/

open scoped Polynomial

namespace Seq

variable {K : Type*}

/-- A sequence `(a_i)_{i ∈ ℕ}` stabilizes to `a` if there exists `N` such that
for all `i ≥ N`, we have `a_i = a`.

This is the notion of convergence in the discrete topology.
(Definition 7.5.1, label: def.fps.lim.stab) -/
def StabilizesTo (a : ℕ → K) (lim : K) : Prop :=
  ∃ N : ℕ, ∀ i ≥ N, a i = lim

/-- If a sequence stabilizes to a limit, that limit is unique. -/
theorem stabilizesTo_unique {a : ℕ → K} {lim₁ lim₂ : K}
    (h₁ : StabilizesTo a lim₁) (h₂ : StabilizesTo a lim₂) : lim₁ = lim₂ := by
  obtain ⟨N₁, hN₁⟩ := h₁
  obtain ⟨N₂, hN₂⟩ := h₂
  have h1 : a (max N₁ N₂) = lim₁ := hN₁ (max N₁ N₂) (le_max_left N₁ N₂)
  have h2 : a (max N₁ N₂) = lim₂ := hN₂ (max N₁ N₂) (le_max_right N₁ N₂)
  exact h1.symm.trans h2

/-- A constant sequence stabilizes to its value. -/
@[simp]
theorem stabilizesTo_const (c : K) : StabilizesTo (fun _ => c) c :=
  ⟨0, fun _ _ => rfl⟩

/-- If a sequence is eventually equal to another, they stabilize to the same limit. -/
theorem stabilizesTo_of_eventually_eq {a b : ℕ → K} {lim : K}
    (h : StabilizesTo a lim) (heq : ∃ N, ∀ i ≥ N, a i = b i) : StabilizesTo b lim := by
  obtain ⟨N₁, hN₁⟩ := h
  obtain ⟨N₂, hN₂⟩ := heq
  use max N₁ N₂
  intro i hi
  rw [← hN₂ i (le_of_max_le_right hi)]
  exact hN₁ i (le_of_max_le_left hi)

/-- Addition preserves stabilization. -/
theorem stabilizesTo_add [Add K] {a b : ℕ → K} {la lb : K}
    (ha : StabilizesTo a la) (hb : StabilizesTo b lb) :
    StabilizesTo (fun i => a i + b i) (la + lb) := by
  obtain ⟨Na, hNa⟩ := ha
  obtain ⟨Nb, hNb⟩ := hb
  use max Na Nb
  intro i hi
  simp only [hNa i (le_of_max_le_left hi), hNb i (le_of_max_le_right hi)]

/-- Multiplication preserves stabilization. -/
theorem stabilizesTo_mul [Mul K] {a b : ℕ → K} {la lb : K}
    (ha : StabilizesTo a la) (hb : StabilizesTo b lb) :
    StabilizesTo (fun i => a i * b i) (la * lb) := by
  obtain ⟨Na, hNa⟩ := ha
  obtain ⟨Nb, hNb⟩ := hb
  refine ⟨max Na Nb, fun i hi => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hi
  simp only [hNa i hi.1, hNb i hi.2]

/-- Negation preserves stabilization. -/
theorem stabilizesTo_neg [Neg K] {a : ℕ → K} {la : K}
    (ha : StabilizesTo a la) : StabilizesTo (fun i => -a i) (-la) := by
  obtain ⟨N, hN⟩ := ha
  exact ⟨N, fun i hi => by simp only [hN i hi]⟩

/-- If `s` is nilpotent (i.e., `s^k = 0` for some `k`), then `(s^i)` stabilizes to `0`. -/
theorem stabilizesTo_pow_of_nilpotent [MonoidWithZero K] {s : K} {k : ℕ}
    (hs : s ^ k = 0) : StabilizesTo (fun i => s ^ i) 0 := by
  use k
  intro i hi
  calc s ^ i = s ^ (k + (i - k)) := by rw [Nat.add_sub_cancel' hi]
    _ = s ^ k * s ^ (i - k) := by rw [pow_add]
    _ = 0 * s ^ (i - k) := by rw [hs]
    _ = 0 := by rw [zero_mul]

/-- If `s` is idempotent (i.e., `s^2 = s`), then `(s^i)_{i ≥ 1}` stabilizes to `s`. -/
theorem stabilizesTo_pow_of_idempotent [Monoid K] {s : K}
    (hs : s * s = s) : StabilizesTo (fun i => s ^ (i + 1)) s := by
  refine ⟨0, fun i _ => ?_⟩
  exact IsIdempotentElem.pow_succ_eq i hs

/-- A finite sum of stabilizing sequences stabilizes. -/
theorem stabilizesTo_finset_sum {ι : Type*} [AddCommMonoid K] [DecidableEq ι] (s : Finset ι)
    {a : ι → ℕ → K} {la : ι → K}
    (h : ∀ i ∈ s, StabilizesTo (a i) (la i)) :
    StabilizesTo (fun n => ∑ i ∈ s, a i n) (∑ i ∈ s, la i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact stabilizesTo_const 0
  | @insert x s hnotmem ih =>
    conv_lhs => ext n; rw [Finset.sum_insert hnotmem]
    rw [Finset.sum_insert hnotmem]
    apply stabilizesTo_add
    · exact h _ (Finset.mem_insert_self _ _)
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

end Seq

namespace PowerSeries

variable {K : Type*} [CommRing K]

/-- A sequence of FPSs `(f_i)_{i ∈ ℕ}` coefficientwise stabilizes to `f` if for each `n ∈ ℕ`,
the sequence `([x^n] f_i)_{i ∈ ℕ}` stabilizes to `[x^n] f`.

This is the notion of convergence in the product topology where each factor `K`
has the discrete topology.
(Definition 7.5.2, label: def.fps.lim.coeff-stab) -/
def CoeffStabilizesTo (f : ℕ → PowerSeries K) (lim : PowerSeries K) : Prop :=
  ∀ n : ℕ, Seq.StabilizesTo (fun i => coeff n (f i)) (coeff n lim)

/-- If a sequence coefficientwise stabilizes to a limit, that limit is unique. -/
theorem coeffStabilizesTo_unique {f : ℕ → PowerSeries K} {lim₁ lim₂ : PowerSeries K}
    (h₁ : CoeffStabilizesTo f lim₁) (h₂ : CoeffStabilizesTo f lim₂) : lim₁ = lim₂ := by
  ext n
  exact Seq.stabilizesTo_unique (h₁ n) (h₂ n)

/-- A constant sequence coefficientwise stabilizes to its value. -/
@[simp]
theorem coeffStabilizesTo_const (g : PowerSeries K) :
    CoeffStabilizesTo (fun _ => g) g :=
  fun n => Seq.stabilizesTo_const (coeff n g)

/-- The sequence `(x^i)_{i ∈ ℕ}` coefficientwise stabilizes to `0`.

For each `n`, the sequence of `n`-th coefficients is `(0, 0, ..., 0, 1, 0, 0, ...)`
which stabilizes to `0`. -/
theorem coeffStabilizesTo_X_pow :
    CoeffStabilizesTo (fun i => (X : PowerSeries K) ^ i) 0 := by
  intro n
  use n + 1
  intro i hi
  simp only [map_zero, coeff_X_pow]
  have hne : n ≠ i := Nat.ne_of_lt (Nat.lt_of_succ_le hi)
  simp [hne]

/-- If each coefficient sequence stabilizes, the FPS sequence coefficientwise stabilizes.
(Theorem 7.5.3, label: thm.fps.lim.lim-crit) -/
theorem coeffStabilizesTo_of_forall_coeff_stabilizes
    {f : ℕ → PowerSeries K} {g : ℕ → K}
    (h : ∀ n, Seq.StabilizesTo (fun i => coeff n (f i)) (g n)) :
    CoeffStabilizesTo f (mk g) := by
  intro n
  simp only [coeff_mk]
  exact h n

/-! ### x^n-Equivalence Properties

The canonical definition of x^n-equivalence (`XnEquiv`) and its properties are in
`AlgebraicCombinatorics.FPS.XnEquivalence`. The notation `f ≡[x^n] g` is defined there.

This section provides:
1. `xnEquiv` as an alias for `XnEquiv` (for use in this file's context)
2. `xnEquiv_*` lemmas as convenience aliases with underscore naming convention
3. Additional lemmas not in `XnEquivalence.lean` (e.g., `xnEquiv_subst`, `xnEquiv_invOfUnit`)

Note: `xnEquiv_refl` has `@[refl]` for use with the `refl` tactic. -/

/-- Alias for `XnEquiv` in the current type context. -/
abbrev xnEquiv := @XnEquiv K _

/-- x^n-equivalence is reflexive. -/
@[refl]
theorem xnEquiv_refl (n : ℕ) (f : PowerSeries K) : f ≡[x^n] f :=
  XnEquiv.refl n f

/-- x^n-equivalence is reflexive (simp-friendly version).

This is a simp lemma for automatic simplification in proofs involving x^n-equivalence.
The theorem `xnEquiv_refl` has the `@[refl]` attribute for use with the `refl` tactic. -/
@[simp]
theorem xnEquiv_self (n : ℕ) (f : PowerSeries K) : xnEquiv n f f := xnEquiv_refl n f

/-- x^n-equivalence is symmetric. -/
theorem xnEquiv_symm {n : ℕ} {f g : PowerSeries K} (h : f ≡[x^n] g) : g ≡[x^n] f :=
  fun k hk => (h k hk).symm

/-- x^n-equivalence is transitive. -/
theorem xnEquiv_trans {n : ℕ} {f g h : PowerSeries K}
    (hfg : f ≡[x^n] g) (hgh : g ≡[x^n] h) : f ≡[x^n] h :=
  fun k hk => (hfg k hk).trans (hgh k hk)

/-- x^n-equivalence is compatible with addition. -/
theorem xnEquiv_add {n : ℕ} {f₁ f₂ g₁ g₂ : PowerSeries K}
    (hf : f₁ ≡[x^n] f₂) (hg : g₁ ≡[x^n] g₂) : f₁ + g₁ ≡[x^n] f₂ + g₂ := by
  intro k hk
  simp only [map_add]
  rw [hf k hk, hg k hk]

/-- x^n-equivalence is compatible with subtraction.
(Theorem 7.3.11(b), label: thm.fps.xneq.props) -/
theorem xnEquiv_sub {n : ℕ} {f₁ f₂ g₁ g₂ : PowerSeries K}
    (hf : f₁ ≡[x^n] f₂) (hg : g₁ ≡[x^n] g₂) : f₁ - g₁ ≡[x^n] f₂ - g₂ := by
  intro k hk
  simp only [map_sub]
  rw [hf k hk, hg k hk]

/-- x^n-equivalence is compatible with scalar multiplication.
(Theorem 7.3.11(c), label: thm.fps.xneq.props) -/
theorem xnEquiv_smul {n : ℕ} {f g : PowerSeries K} (c : K)
    (h : f ≡[x^n] g) : c • f ≡[x^n] c • g := by
  intro k hk
  simp only [coeff_smul]
  rw [h k hk]

/-- x^n-equivalence is compatible with multiplication. -/
theorem xnEquiv_mul {n : ℕ} {f₁ f₂ g₁ g₂ : PowerSeries K}
    (hf : f₁ ≡[x^n] f₂) (hg : g₁ ≡[x^n] g₂) : f₁ * g₁ ≡[x^n] f₂ * g₂ := by
  intro k hk
  simp only [coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hi : p.1 ≤ n := by omega
  have hj : p.2 ≤ n := by omega
  rw [hf p.1 hi, hg p.2 hj]

/-- x^n-equivalence is compatible with powers. -/
theorem xnEquiv_pow {n : ℕ} {f g : PowerSeries K} (h : f ≡[x^n] g) (d : ℕ) :
    f ^ d ≡[x^n] g ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    simp only [pow_succ]
    exact xnEquiv_mul ih h

/-- x^n-equivalence is compatible with finite sums.
(Theorem 7.3.11(f), label: thm.fps.xneq.props) -/
theorem xnEquiv_finset_sum {ι : Type*} [DecidableEq ι] {n : ℕ} (s : Finset ι)
    {f g : ι → PowerSeries K} (h : ∀ i ∈ s, f i ≡[x^n] g i) :
    ∑ i ∈ s, f i ≡[x^n] ∑ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' has ih =>
    simp only [Finset.sum_insert has]
    apply xnEquiv_add
    · exact h a (Finset.mem_insert_self a s')
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- x^n-equivalence is compatible with finite products.

If two families of FPSs `(c_w)_{w ∈ V}` and `(d_w)_{w ∈ V}` satisfy `c_w ≡[x^n] d_w` for
each `w ∈ V`, then `∏_{w ∈ V} c_w ≡[x^n] ∏_{w ∈ V} d_w`.

This is a key lemma used in proving that the family of fiber subproducts is multipliable
(Proposition prop.fps.prods-mulable-rules.SW1).

(Theorem 7.3.11(f), label: thm.fps.xneq.props)
(Also: Lemma lem.fps.prods-mulable-rules.SW1.lem1) -/
theorem xnEquiv_finset_prod {ι : Type*} [DecidableEq ι] {n : ℕ} (s : Finset ι)
    {f g : ι → PowerSeries K} (h : ∀ i ∈ s, f i ≡[x^n] g i) :
    ∏ i ∈ s, f i ≡[x^n] ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' has ih =>
    simp only [Finset.prod_insert has]
    apply xnEquiv_mul
    · exact h a (Finset.mem_insert_self a s')
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- When `constantCoeff g = 0`, the coefficient `coeff n (g ^ d)` is zero for `d > n`.
This is because `order(g) ≥ 1` implies `order(g^d) ≥ d`. -/
theorem coeff_pow_eq_zero_of_constantCoeff_zero
    (g : PowerSeries K) (hg : constantCoeff g = 0)
    (n d : ℕ) (hd : d > n) : coeff n (g ^ d) = 0 := by
  apply coeff_of_lt_order
  calc (n : ℕ∞) < d := by exact Nat.cast_lt.mpr hd
    _ ≤ order (g ^ d) := le_order_pow_of_constantCoeff_eq_zero d hg

/-- The n-th coefficient of `f.subst g` equals a finite sum over coefficients.
When `constantCoeff g = 0`, only coefficients 0 through n of `f` contribute. -/
theorem coeff_subst_eq_finite_sum
    (f g : PowerSeries K) (hg : constantCoeff g = 0) (n : ℕ) :
    coeff n (f.subst g) = ∑ d ∈ Finset.range (n + 1), coeff d f • coeff n (g ^ d) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg) f n]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  simp only [Finset.coe_range, Set.mem_Iio]
  rw [Function.mem_support] at hd
  by_contra h
  push Not at h
  apply hd
  simp only [smul_eq_mul]
  rw [coeff_pow_eq_zero_of_constantCoeff_zero g hg n d (by omega), mul_zero]

/-- x^n-equivalence is compatible with composition (when inner series have zero constant term).
This is the key lemma (Proposition 7.4.7 in Loehr). -/
theorem xnEquiv_subst {n : ℕ} {f₁ f₂ g₁ g₂ : PowerSeries K}
    (hf : f₁ ≡[x^n] f₂) (hg : g₁ ≡[x^n] g₂)
    (hg₁ : constantCoeff g₁ = 0) (hg₂ : constantCoeff g₂ = 0) :
    f₁.subst g₁ ≡[x^n] f₂.subst g₂ := by
  intro m hm
  rw [coeff_subst_eq_finite_sum f₁ g₁ hg₁ m, coeff_subst_eq_finite_sum f₂ g₂ hg₂ m]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mem_range] at hd
  have hd' : d ≤ n := by omega
  rw [hf d (le_trans (Nat.lt_add_one_iff.mp hd) hm)]
  congr 1
  exact xnEquiv_pow hg d m hm

/-- If two pairs of FPSs agree on their first n+1 coefficients, then their products
also agree on those coefficients.
(Lemma 7.3.15, label: lem.fps.prod.irlv.cong-mul)

This is a direct consequence of the fact that the k-th coefficient of a product
only depends on coefficients 0 through k of each factor.

This is an alternative formulation of `xnEquiv_mul` using explicit coefficient equality. -/
theorem coeff_mul_eq_of_coeff_eq {a b c d : PowerSeries K} {n : ℕ}
    (hab : ∀ m ≤ n, coeff m a = coeff m b)
    (hcd : ∀ m ≤ n, coeff m c = coeff m d) :
    ∀ m ≤ n, coeff m (a * c) = coeff m (b * d) :=
  xnEquiv_mul hab hcd

/-- x^n-equivalence is compatible with taking inverses (when constant coefficients are units).
The key insight is that the coefficients of the inverse are determined by a recursive formula
that only depends on lower coefficients. -/
theorem xnEquiv_invOfUnit {n : ℕ} {f g : PowerSeries K} (u : Kˣ)
    (h : f ≡[x^n] g) :
    invOfUnit f u ≡[x^n] invOfUnit g u := by
  -- We prove by strong induction on k
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    -- Use the recursive formula for invOfUnit coefficients
    classical
    rw [coeff_invOfUnit, coeff_invOfUnit]
    split_ifs with hk0
    · -- k = 0 case: both are u⁻¹
      rfl
    · -- k > 0 case: use recursion
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      split_ifs with hlt
      · -- p.2 < k: use IH
        have hp1 : p.1 ≤ n := by omega
        have hp2 : p.2 ≤ n := by omega
        have hp2_lt_k : p.2 < k := hlt
        rw [h p.1 hp1, ih p.2 hp2_lt_k hp2]
      · rfl

/-- x^n-equivalence is compatible with taking inverses (with different units that are equal as elements).
This variant is useful when the units come from different IsUnit proofs but have the same value. -/
theorem xnEquiv_invOfUnit' {n : ℕ} {f g : PowerSeries K} (u v : Kˣ)
    (huv : (u : K) = v)
    (h : f ≡[x^n] g) :
    invOfUnit f u ≡[x^n] invOfUnit g v := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    classical
    rw [coeff_invOfUnit, coeff_invOfUnit]
    split_ifs with hk0
    · -- k = 0: show u⁻¹ = v⁻¹
      congr 1
      have : u = v := Units.ext huv
      rw [this]
    · -- k > 0: use recursion
      have hinv : (↑u⁻¹ : K) = ↑v⁻¹ := by
        have : u = v := Units.ext huv
        rw [this]
      rw [hinv]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      split_ifs with hlt
      · have hp1 : p.1 ≤ n := by omega
        have hp2 : p.2 ≤ n := by omega
        rw [h p.1 hp1, ih p.2 hlt hp2]
      · rfl

/-- x^n-equivalence is compatible with division (when denominators are invertible).
(Theorem 7.3.11(e), label: thm.fps.xneq.props)

If a ≡[x^n] b and c ≡[x^n] d, and c, d are invertible, then a/c ≡[x^n] b/d. -/
theorem xnEquiv_div {n : ℕ} {a b c d : PowerSeries K}
    (hab : a ≡[x^n] b) (hcd : c ≡[x^n] d)
    (u : Kˣ) (hu : constantCoeff c = u)
    (v : Kˣ) (hv : constantCoeff d = v) :
    a * invOfUnit c u ≡[x^n] b * invOfUnit d v := by
  -- First show that u = v (since c ≡[x^n] d implies coeff 0 c = coeff 0 d)
  have huv : (u : K) = v := by
    have h0 : coeff 0 c = coeff 0 d := hcd 0 (Nat.zero_le n)
    simp only [coeff_zero_eq_constantCoeff_apply] at h0
    rw [hu, hv] at h0
    exact h0
  apply xnEquiv_mul hab
  exact xnEquiv_invOfUnit' u v huv hcd

/-- If two pairs of FPSs agree on their first n+1 coefficients, and the denominators are
invertible, then their quotients also agree on those coefficients.
(Lemma 7.3.16, label: lem.fps.prod.irlv.cong-div)

This is a direct consequence of the fact that the k-th coefficient of a quotient
only depends on coefficients 0 through k of each factor.

This is an alternative formulation of `xnEquiv_div` using explicit coefficient equality. -/
theorem coeff_div_eq_of_coeff_eq {a b c d : PowerSeries K} {n : ℕ}
    (hab : ∀ m ≤ n, coeff m a = coeff m b)
    (hcd : ∀ m ≤ n, coeff m c = coeff m d)
    (u : Kˣ) (hu : constantCoeff c = u)
    (v : Kˣ) (hv : constantCoeff d = v) :
    ∀ m ≤ n, coeff m (a * invOfUnit c u) = coeff m (b * invOfUnit d v) :=
  xnEquiv_div hab hcd u hu v hv

/-- If `f_i → f`, then for each `n`, eventually `f_i ≡[x^n] f`.
(Lemma 7.5.4, label: lem.fps.lim.xn-equiv) -/
theorem exists_xnEquiv_of_coeffStabilizesTo
    {f : ℕ → PowerSeries K} {lim : PowerSeries K}
    (h : CoeffStabilizesTo f lim) (n : ℕ) :
    ∃ N : ℕ, ∀ i ≥ N, f i ≡[x^n] lim := by
  -- For each k ≤ n, get the stabilization bound N_k
  -- We need to take the maximum of all N_k for k in {0, 1, ..., n}
  choose N hN using fun k => h k
  use Finset.sup (Finset.range (n + 1)) N
  intro i hi k hk
  apply hN k
  exact le_trans (Finset.le_sup (by simp [hk])) hi

/-- Limits respect addition.
(Proposition 7.5.5, label: prop.fps.lim.sum-prod) -/
theorem coeffStabilizesTo_add
    {f g : ℕ → PowerSeries K} {lf lg : PowerSeries K}
    (hf : CoeffStabilizesTo f lf) (hg : CoeffStabilizesTo g lg) :
    CoeffStabilizesTo (fun i => f i + g i) (lf + lg) := by
  intro n
  simp only [map_add]
  exact Seq.stabilizesTo_add (hf n) (hg n)

/-- Limits respect multiplication.
(Proposition 7.5.5, label: prop.fps.lim.sum-prod) -/
theorem coeffStabilizesTo_mul
    {f g : ℕ → PowerSeries K} {lf lg : PowerSeries K}
    (hf : CoeffStabilizesTo f lf) (hg : CoeffStabilizesTo g lg) :
    CoeffStabilizesTo (fun i => f i * g i) (lf * lg) := by
  intro n
  -- The n-th coefficient of f_i * g_i is a sum over the antidiagonal
  simp only [coeff_mul]
  -- Apply the finite sum stabilization lemma
  apply Seq.stabilizesTo_finset_sum
  intro p _
  -- Each term is a product of stabilizing sequences
  exact Seq.stabilizesTo_mul (hf p.1) (hg p.2)

/-- Limits respect finite sums.
(Corollary 7.5.6, label: cor.fps.lim.sum-prod-k) -/
theorem coeffStabilizesTo_finset_sum {ι : Type*} (s : Finset ι)
    {f : ι → ℕ → PowerSeries K} {lf : ι → PowerSeries K}
    (h : ∀ i ∈ s, CoeffStabilizesTo (f i) (lf i)) :
    CoeffStabilizesTo (fun n => ∑ i ∈ s, f i n) (∑ i ∈ s, lf i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact coeffStabilizesTo_const 0
  | @insert a s' ha ih =>
    simp only [Finset.sum_insert ha]
    apply coeffStabilizesTo_add
    · exact h _ (Finset.mem_insert_self _ _)
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Limits respect finite products.
(Corollary 7.5.6, label: cor.fps.lim.sum-prod-k) -/
theorem coeffStabilizesTo_finset_prod {ι : Type*} (s : Finset ι)
    {f : ι → ℕ → PowerSeries K} {lf : ι → PowerSeries K}
    (h : ∀ i ∈ s, CoeffStabilizesTo (f i) (lf i)) :
    CoeffStabilizesTo (fun n => ∏ i ∈ s, f i n) (∏ i ∈ s, lf i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact coeffStabilizesTo_const 1
  | @insert a s' ha ih =>
    simp only [Finset.prod_insert ha]
    apply coeffStabilizesTo_mul
    · exact h _ (Finset.mem_insert_self _ _)
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Limits respect negation. -/
theorem coeffStabilizesTo_neg
    {f : ℕ → PowerSeries K} {lf : PowerSeries K}
    (hf : CoeffStabilizesTo f lf) :
    CoeffStabilizesTo (fun i => -f i) (-lf) := by
  intro n
  simp only [map_neg]
  exact Seq.stabilizesTo_neg (hf n)

/-- Limits respect subtraction. -/
theorem coeffStabilizesTo_sub
    {f g : ℕ → PowerSeries K} {lf lg : PowerSeries K}
    (hf : CoeffStabilizesTo f lf) (hg : CoeffStabilizesTo g lg) :
    CoeffStabilizesTo (fun i => f i - g i) (lf - lg) := by
  have h := coeffStabilizesTo_add hf (coeffStabilizesTo_neg hg)
  simp only [sub_eq_add_neg] at h ⊢
  exact h

/-- If each `g_i` is invertible and `g_i → g`, then `g` is invertible. -/
theorem isUnit_constantCoeff_of_coeffStabilizesTo
    {g : ℕ → PowerSeries K} {lg : PowerSeries K}
    (hg : CoeffStabilizesTo g lg) (hunit : ∀ i, IsUnit (constantCoeff (g i))) :
    IsUnit (constantCoeff lg) := by
  -- The 0-th coefficient of g i stabilizes to the 0-th coefficient of lg
  obtain ⟨N, hN⟩ := hg 0
  -- For i ≥ N, we have coeff 0 (g i) = coeff 0 lg
  -- Since constantCoeff = coeff 0, we have constantCoeff (g N) = constantCoeff lg
  have h : constantCoeff (g N) = constantCoeff lg := by
    simp only [← coeff_zero_eq_constantCoeff_apply]
    exact hN N (le_refl N)
  rw [← h]
  exact hunit N

/-- Helper: the unit from isUnit_constantCoeff_of_coeffStabilizesTo equals the unit from hunit i
for sufficiently large i. -/
lemma unit_eq_of_coeffStabilizesTo
    {g : ℕ → PowerSeries K} {lg : PowerSeries K}
    (hg : CoeffStabilizesTo g lg)
    (hunit : ∀ i, IsUnit (constantCoeff (g i))) :
    ∃ N, ∀ i ≥ N, (hunit i).unit = (isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit := by
  obtain ⟨N, hN⟩ := hg 0
  use N
  intro i hi
  apply Units.ext
  simp only [IsUnit.unit_spec]
  have h : constantCoeff (g i) = constantCoeff lg := by
    simp only [← coeff_zero_eq_constantCoeff_apply]
    exact hN i hi
  rw [h]

/-- Coefficients of invOfUnit stabilize when the input coefficients stabilize.
This is the key lemma for proving that limits respect division. -/
theorem coeffStabilizesTo_invOfUnit
    {g : ℕ → PowerSeries K} {lg : PowerSeries K}
    (hg : CoeffStabilizesTo g lg)
    (hunit : ∀ i, IsUnit (constantCoeff (g i))) :
    CoeffStabilizesTo
      (fun i => invOfUnit (g i) (hunit i).unit)
      (invOfUnit lg (isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit) := by
  -- We prove by strong induction on n that coeff n stabilizes
  intro n
  induction' n using Nat.strong_induction_on with n ih
  -- Use the recursive formula for coeff_invOfUnit
  by_cases hn : n = 0
  · -- Base case: n = 0
    subst hn
    simp only [coeff_zero_eq_constantCoeff_apply, constantCoeff_invOfUnit]
    -- Need to show that (hunit i).unit⁻¹ stabilizes to (isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit⁻¹
    obtain ⟨N, hN⟩ := unit_eq_of_coeffStabilizesTo hg hunit
    use N
    intro i hi
    show (↑(hunit i).unit⁻¹ : K) = (↑(isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit⁻¹ : K)
    rw [hN i hi]
  · -- Inductive case: n > 0
    -- coeff n (invOfUnit g u) = -u⁻¹ * ∑ x ∈ antidiagonal n, if x.2 < n then coeff x.1 g * coeff x.2 (invOfUnit g u) else 0
    have h_lhs : ∀ i, coeff n (invOfUnit (g i) (hunit i).unit) =
        -(↑(hunit i).unit⁻¹ : K) *
          ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
            if x.2 < n then coeff x.1 (g i) * coeff x.2 (invOfUnit (g i) (hunit i).unit) else 0 := by
      intro i
      rw [coeff_invOfUnit, ite_eq_right hn]
    have h_rhs : coeff n (invOfUnit lg (isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit) =
        -(↑((isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit⁻¹) : K) *
          ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
            if x.2 < n then coeff x.1 lg * coeff x.2 (invOfUnit lg (isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit) else 0 := by
      rw [coeff_invOfUnit, ite_eq_right hn]
    conv_lhs => ext i; rw [h_lhs]
    rw [h_rhs]
    -- The -u⁻¹ factor stabilizes
    have h_inv_stab : Seq.StabilizesTo (fun i => -(↑(hunit i).unit⁻¹ : K))
        (-(↑(isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit⁻¹ : K)) := by
      obtain ⟨N, hN⟩ := unit_eq_of_coeffStabilizesTo hg hunit
      use N
      intro i hi
      show -(↑(hunit i).unit⁻¹ : K) = -(↑(isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit⁻¹ : K)
      rw [hN i hi]
    -- The sum stabilizes by induction hypothesis
    have h_sum_stab : Seq.StabilizesTo
        (fun i => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, if x.2 < n then coeff x.1 (g i) * coeff x.2 (invOfUnit (g i) (hunit i).unit) else 0)
        (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, if x.2 < n then coeff x.1 lg * coeff x.2 (invOfUnit lg (isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit) else 0) := by
      apply Seq.stabilizesTo_finset_sum
      intro ⟨a, b⟩ hab
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      by_cases hb : b < n
      · simp only [hb, ↓reduceIte]
        apply Seq.stabilizesTo_mul
        · exact hg a
        · exact ih b hb
      · simp only [hb, ↓reduceIte]
        exact Seq.stabilizesTo_const 0
    exact Seq.stabilizesTo_mul h_inv_stab h_sum_stab

/-- Limits respect division (when denominators are invertible).
(Proposition 7.5.6, label: prop.fps.lim.sum-quot)

Note: We state this in terms of multiplication by the inverse. -/
theorem coeffStabilizesTo_mul_inv
    {f g : ℕ → PowerSeries K} {lf lg : PowerSeries K}
    (hf : CoeffStabilizesTo f lf) (hg : CoeffStabilizesTo g lg)
    (hunit : ∀ i, IsUnit (constantCoeff (g i))) :
    CoeffStabilizesTo
      (fun i => f i * invOfUnit (g i) (hunit i).unit)
      (lf * invOfUnit lg (isUnit_constantCoeff_of_coeffStabilizesTo hg hunit).unit) := by
  apply coeffStabilizesTo_mul hf
  exact coeffStabilizesTo_invOfUnit hg hunit

/-- Limits respect composition (when the inner FPS has zero constant term).
(Proposition 7.5.7, label: prop.fps.lim.comp)

We use `subst` for composition. -/
theorem coeffStabilizesTo_subst
    {f g : ℕ → PowerSeries K} {lf lg : PowerSeries K}
    (hf : CoeffStabilizesTo f lf) (hg : CoeffStabilizesTo g lg)
    (hconst : ∀ i, constantCoeff (g i) = 0) :
    CoeffStabilizesTo (fun i => (f i).subst (g i)) (lf.subst lg) := by
  -- First show that constantCoeff lg = 0
  have hlg : constantCoeff lg = 0 := by
    have : Seq.StabilizesTo (fun i => coeff 0 (g i)) (coeff 0 lg) := hg 0
    obtain ⟨N, hN⟩ := this
    have h0 : coeff 0 (g N) = coeff 0 lg := hN N (le_refl N)
    simp only [coeff_zero_eq_constantCoeff] at hconst h0 ⊢
    rw [← h0, hconst]
  -- Now for each n, show that coeff n of the substitution stabilizes
  intro n
  -- Get N such that for i ≥ N, f i ≡[x^n] lf and g i ≡[x^n] lg
  obtain ⟨Nf, hNf⟩ := exists_xnEquiv_of_coeffStabilizesTo hf n
  obtain ⟨Ng, hNg⟩ := exists_xnEquiv_of_coeffStabilizesTo hg n
  use max Nf Ng
  intro i hi
  have hfi : f i ≡[x^n] lf := hNf i (le_of_max_le_left hi)
  have hgi : g i ≡[x^n] lg := hNg i (le_of_max_le_right hi)
  exact xnEquiv_subst hfi hgi (hconst i) hlg n (le_refl n)

/-- Limits respect derivatives.
(Proposition 7.5.8, label: prop.fps.lim.deriv-lim) -/
theorem coeffStabilizesTo_derivativeFun
    {f : ℕ → PowerSeries K} {lf : PowerSeries K}
    (hf : CoeffStabilizesTo f lf) :
    CoeffStabilizesTo (fun i => d⁄dX (f i)) (d⁄dX lf) := by
  intro n
  -- coeff n (g') = coeff (n+1) g * (n+1)
  simp only [coeff_derivative]
  -- The sequence (coeff (n+1) (f i) * (n+1))_i stabilizes to coeff (n+1) lf * (n+1)
  exact Seq.stabilizesTo_mul (hf (n + 1)) (Seq.stabilizesTo_const _)

/-- A family of FPSs is summable if for each `n`, only finitely many have nonzero `n`-th coeff. -/
def IsSummable (f : ℕ → PowerSeries K) : Prop :=
  ∀ n : ℕ, {i : ℕ | coeff n (f i) ≠ 0}.Finite

/-- The infinite sum of a summable family. -/
noncomputable def tsum' (f : ℕ → PowerSeries K) (hf : IsSummable f) : PowerSeries K :=
  mk fun n => ∑ i ∈ (hf n).toFinset, coeff n (f i)

/-- Infinite sum is the limit of partial sums.
(Theorem 7.5.9, label: thm.fps.lim.sum-lim)

The proof proceeds by showing that for each coefficient index `n`, the sequence of
partial sums of `n`-th coefficients eventually equals the infinite sum.
This follows from the summability condition: only finitely many terms have
nonzero `n`-th coefficient, so once the partial sum includes all of these,
it stabilizes. -/
theorem coeffStabilizesTo_partial_sum
    {f : ℕ → PowerSeries K} (hf : IsSummable f) :
    CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) (tsum' f hf) := by
  intro n
  -- For coefficient n, we need to show that the partial sums stabilize
  -- The key is that only finitely many f j have nonzero n-th coefficient
  let S := (hf n).toFinset
  -- Find the maximum element in S (or handle the empty case)
  by_cases hS : S.Nonempty
  · -- S is nonempty: use the sup as the stabilization point
    let N := S.sup' hS id
    use N + 1
    intro i hi
    -- The n-th coefficient of the partial sum is the sum of n-th coefficients
    simp only [map_sum, coeff_mk, tsum']
    -- Show the sums are equal by subset argument
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · -- S ⊆ Finset.range (i + 1)
      intro x hx
      simp only [Finset.mem_range]
      have hxN : x ≤ N := Finset.le_sup' id hx
      omega
    · -- Elements in range (i+1) \ S have coefficient 0
      intro x hx
      simp only [Finset.mem_sdiff] at hx
      have hnotS : x ∉ S := hx.2
      by_contra h
      exact hnotS (Set.Finite.mem_toFinset (hf n) |>.mpr h)
    · -- The terms match
      intro _ _
      rfl
  · -- S is empty: all coefficients are 0
    use 0
    intro i _
    simp only [map_sum, coeff_mk, tsum']
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    conv_rhs => rw [show (hf n).toFinset = S from rfl, hSempty]
    simp only [Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro x _
    by_contra h
    have hmem : x ∈ S := Set.Finite.mem_toFinset (hf n) |>.mpr h
    rw [hSempty] at hmem
    simp at hmem

/-- A family of FPSs is multipliable if each has constant term 1 and for each `n`,
eventually all terms are 1 + O(x^{n+1}).

**Note:** This is a more restrictive definition than `PowerSeries.Multipliable` in
`InfiniteProducts.lean`. This definition is specifically designed for ℕ-indexed
sequences where we consider limits of partial products `∏_{i=0}^{N} f_i`.

The general `PowerSeries.Multipliable a` only requires that each coefficient is
finitely determined, and works for arbitrary index types. For general infinite
products, use the definitions in `InfiniteProducts.lean`. -/
def IsMultipliable (f : ℕ → PowerSeries K) : Prop :=
  (∀ i, constantCoeff (f i) = 1) ∧
  ∀ n : ℕ, ∃ N : ℕ, ∀ i ≥ N, ∀ k ≤ n, coeff k (f i) = if k = 0 then 1 else 0

/-- The infinite product of a multipliable family (ℕ-indexed version).

The `n`-th coefficient of the infinite product equals the `n`-th coefficient of
any sufficiently large partial product.

**Note:** This is the ℕ-indexed version for use with `IsMultipliable`. For the
general infinite product over arbitrary index types, use `PowerSeries.tprod` in
`InfiniteProducts.lean`. -/
noncomputable def tprod' (f : ℕ → PowerSeries K) (hf : IsMultipliable f) : PowerSeries K :=
  mk fun n =>
    let N := (hf.2 n).choose
    coeff n (∏ j ∈ Finset.range (N + 1), f j)

/-- If f has the form 1 + O(x^{n+1}), then (g * f) agrees with g on coefficients ≤ n.
This is a key lemma for showing that partial products stabilize. -/
lemma coeff_mul_one_plus_higher {g f : PowerSeries K} {n : ℕ}
    (hf : ∀ k ≤ n, coeff k f = if k = 0 then 1 else 0) :
    ∀ k ≤ n, coeff k (g * f) = coeff k g := by
  intro k hk
  rw [coeff_mul]
  -- The sum is over pairs (a, b) with a + b = k
  -- For b > 0, coeff b f = 0 (since b ≤ k ≤ n)
  -- For b = 0, coeff 0 f = 1
  have hsplit : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k, coeff p.1 g * coeff p.2 f =
      if p.2 = 0 then coeff p.1 g else 0 := by
    intro ⟨a, b⟩ hab
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    have hb : b ≤ n := by omega
    rw [hf b hb]
    split_ifs with hb0
    · ring
    · ring
  rw [Finset.sum_congr rfl hsplit]
  -- Now we need to simplify ∑ x ∈ antidiagonal k, if x.2 = 0 then coeff x.1 g else 0
  -- The only element with x.2 = 0 is (k, 0)
  have hmem : (k, 0) ∈ Finset.HasAntidiagonal.antidiagonal k := by
    simp [Finset.HasAntidiagonal.mem_antidiagonal]
  have huniq : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal k, p.2 = 0 → p = (k, 0) := by
    intro ⟨a, b⟩ hab hb
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    simp only at hb
    subst hb
    simp only [add_zero] at hab
    simp [hab]
  rw [Finset.sum_eq_single (k, 0)]
  · simp
  · intro p hp hne
    simp only [ite_eq_right_iff]
    intro hp2
    exact absurd (huniq p hp hp2) hne
  · intro habs
    exact absurd hmem habs

/-- Extending the partial product by one more term that is 1 + O(x^{n+1})
doesn't change coefficients ≤ n. -/
lemma coeff_prod_extend {f : ℕ → PowerSeries K} {n m : ℕ}
    (hf : ∀ k ≤ n, coeff k (f m) = if k = 0 then 1 else 0) (k : ℕ) (hk : k ≤ n) :
    coeff k (∏ j ∈ Finset.range (m + 1), f j) = coeff k (∏ j ∈ Finset.range m, f j) := by
  rw [Finset.prod_range_succ]
  exact coeff_mul_one_plus_higher hf k hk

/-- For a multipliable family, once the index exceeds N (where N witnesses the
multipliability condition for n), the k-th coefficient of partial products stabilizes. -/
lemma coeff_prod_range_eq_of_ge {f : ℕ → PowerSeries K} {n N : ℕ}
    (hN : ∀ j ≥ N, ∀ k ≤ n, coeff k (f j) = if k = 0 then 1 else 0)
    {i : ℕ} (hi : i ≥ N) {k : ℕ} (hk : k ≤ n) :
    coeff k (∏ j ∈ Finset.range (i + 1), f j) = coeff k (∏ j ∈ Finset.range (N + 1), f j) := by
  induction i with
  | zero =>
    have : N = 0 := Nat.eq_zero_of_le_zero hi
    subst this
    rfl
  | succ i ih =>
    by_cases hi' : i + 1 ≤ N
    · have : i + 1 = N := Nat.le_antisymm hi' hi
      simp only [this]
    · push Not at hi'
      have hi'' : i ≥ N := Nat.lt_succ_iff.mp hi'
      have hi_succ_ge : i + 1 ≥ N := Nat.le_of_lt hi'
      rw [coeff_prod_extend (hN (i + 1) hi_succ_ge) k hk]
      exact ih hi''

/-- For a multipliable family, the n-th coefficient of partial products stabilizes. -/
lemma coeff_partial_prod_stabilizes {f : ℕ → PowerSeries K} (hf : IsMultipliable f) (n : ℕ) :
    ∃ N : ℕ, ∀ i ≥ N, coeff n (∏ j ∈ Finset.range (i + 1), f j) = coeff n (tprod' f hf) := by
  obtain ⟨N, hN⟩ := hf.2 n
  set N' := (hf.2 n).choose with hN'_def
  have hN' : ∀ j ≥ N', ∀ k ≤ n, coeff k (f j) = if k = 0 then 1 else 0 := (hf.2 n).choose_spec
  use max N N'
  intro i hi
  simp only [tprod', coeff_mk]
  -- Both sides equal coeff n (∏ j in range (max N N' + 1), f j)
  have hi_N : i ≥ N := le_of_max_le_left hi
  have hi_N' : i ≥ N' := le_of_max_le_right hi
  -- Show LHS = coeff n (∏ j in range (max N N' + 1), f j)
  have lhs_eq : coeff n (∏ j ∈ Finset.range (i + 1), f j) =
      coeff n (∏ j ∈ Finset.range (max N N' + 1), f j) := by
    have hmax_N : max N N' ≥ N := le_max_left N N'
    calc coeff n (∏ j ∈ Finset.range (i + 1), f j)
        = coeff n (∏ j ∈ Finset.range (N + 1), f j) := coeff_prod_range_eq_of_ge hN hi_N le_rfl
      _ = coeff n (∏ j ∈ Finset.range (max N N' + 1), f j) :=
          (coeff_prod_range_eq_of_ge hN hmax_N le_rfl).symm
  -- Show RHS = coeff n (∏ j in range (max N N' + 1), f j)
  have rhs_eq : coeff n (∏ j ∈ Finset.range (N' + 1), f j) =
      coeff n (∏ j ∈ Finset.range (max N N' + 1), f j) := by
    have hmax_N' : max N N' ≥ N' := le_max_right N N'
    exact (coeff_prod_range_eq_of_ge hN' hmax_N' le_rfl).symm
  rw [lhs_eq, rhs_eq]

/-- Infinite product is the limit of partial products.
(Theorem 7.5.10, label: thm.fps.lim.prod-lim) -/
theorem coeffStabilizesTo_partial_prod
    {f : ℕ → PowerSeries K} (hf : IsMultipliable f) :
    CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) (tprod' f hf) := by
  intro n
  exact coeff_partial_prod_stabilizes hf n

/-- Each FPS is a limit of polynomials.
(Corollary 7.5.11, label: cor.fps.lim.fps-as-pol)

This can be restated as "the polynomials are dense in the FPSs". -/
theorem coeffStabilizesTo_trunc (a : PowerSeries K) :
    CoeffStabilizesTo (fun i => (trunc (i + 1) a : PowerSeries K)) a := by
  intro n
  use n
  intro i hi
  exact coeff_coe_trunc_of_lt (by omega : n < i + 1)

/-- Converse of `coeffStabilizesTo_partial_sum`: if the partial sums converge,
the family is summable.
(Theorem 7.5.12, label: thm.fps.lim.sum-lim-conv) -/
theorem isSummable_of_coeffStabilizesTo_partial_sum
    {f : ℕ → PowerSeries K} {lim : PowerSeries K}
    (h : CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) lim) :
    IsSummable f := by
  intro n
  -- Get the N where the n-th coefficient stabilizes
  obtain ⟨N, hN⟩ := h n
  -- The set of indices where coeff n (f i) ≠ 0 is contained in {0, 1, ..., N}
  apply Set.Finite.subset (Finset.finite_toSet (Finset.range (N + 1)))
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  -- We need to show i < N + 1, i.e., i ≤ N
  by_contra h_ge
  push Not at h_ge
  -- If i ≥ N + 1, then both i - 1 ≥ N and i ≥ N
  have hi_ge_N : i ≥ N := Nat.le_of_succ_le h_ge
  have hi_pred_ge_N : i - 1 ≥ N := Nat.le_sub_one_of_lt h_ge
  -- Get the stabilization equalities
  have h_eq1 := hN i hi_ge_N
  have h_eq2 := hN (i - 1) hi_pred_ge_N
  -- Simplify these
  simp only at h_eq1 h_eq2
  -- The partial sum at i equals the partial sum at i-1 plus f i
  have h_coeff_eq : coeff n (∑ j ∈ Finset.range (i + 1), f j) =
                    coeff n (∑ j ∈ Finset.range i, f j) + coeff n (f i) := by
    have h_split : Finset.range (i + 1) = Finset.range i ∪ {i} := by
      ext k
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton]
      omega
    rw [h_split, Finset.sum_union]
    · simp only [Finset.sum_singleton, map_add]
    · simp only [Finset.disjoint_singleton_right, Finset.mem_range, lt_self_iff_false,
        not_false_eq_true]
  -- Since i ≥ N + 1, we have i ≥ 1, so i - 1 + 1 = i
  have h_range_eq : Finset.range i = Finset.range ((i - 1) + 1) := by
    congr 1
    omega
  rw [h_range_eq] at h_coeff_eq
  -- Now h_eq1 says coeff n (∑ j ∈ Finset.range (i + 1), f j) = coeff n lim
  -- And h_eq2 says coeff n (∑ j ∈ Finset.range ((i-1) + 1), f j) = coeff n lim
  rw [h_eq1, h_eq2] at h_coeff_eq
  -- So coeff n lim = coeff n lim + coeff n (f i), meaning coeff n (f i) = 0
  have h_zero : coeff n (f i) = 0 := by
    have heq : coeff n lim = coeff n lim + coeff n (f i) := h_coeff_eq
    calc coeff n (f i) = coeff n lim + coeff n (f i) - coeff n lim := by ring
      _ = coeff n lim - coeff n lim := by rw [← heq]
      _ = 0 := by ring
  exact hi h_zero

/-- If partial sums converge, the limit equals the infinite sum.
(Theorem 7.5.12, label: thm.fps.lim.sum-lim-conv) -/
theorem tsum'_eq_of_coeffStabilizesTo_partial_sum
    {f : ℕ → PowerSeries K} {lim : PowerSeries K}
    (h : CoeffStabilizesTo (fun i => ∑ j ∈ Finset.range (i + 1), f j) lim) :
    tsum' f (isSummable_of_coeffStabilizesTo_partial_sum h) = lim := by
  apply coeffStabilizesTo_unique
  · exact coeffStabilizesTo_partial_sum (isSummable_of_coeffStabilizesTo_partial_sum h)
  · exact h

/-- Helper lemma: constant coeff of product of power series with constant coeff 1 is 1. -/
lemma constantCoeff_prod_eq_one {f : ℕ → PowerSeries K} {s : Finset ℕ}
    (hf : ∀ i ∈ s, constantCoeff (f i) = 1) :
    constantCoeff (∏ j ∈ s, f j) = 1 := by
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact hf i hi

/-- Converse of `coeffStabilizesTo_partial_prod`: if the partial products converge,
the family is multipliable.
(Theorem 7.5.13, label: thm.fps.lim.prod-lim-conv) -/
theorem isMultipliable_of_coeffStabilizesTo_partial_prod
    {f : ℕ → PowerSeries K} {lim : PowerSeries K}
    (h : CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) lim)
    (hconst : ∀ i, constantCoeff (f i) = 1) :
    IsMultipliable f := by
  constructor
  · exact hconst
  · intro n
    -- For each k, we get a stabilization threshold from h k
    have hN : ∀ k, ∃ N, ∀ i ≥ N, coeff k (∏ j ∈ Finset.range (i + 1), f j) = coeff k lim := h
    choose Nk hNk using hN
    -- Take the maximum over k ∈ {0, ..., n}, plus 1 to ensure i > 0
    let N := (Finset.sup (Finset.range (n + 1)) Nk) + 1
    use N

    -- Main claim: for i ≥ N and 0 < k ≤ n, coeff k (f i) = 0
    -- We prove this by strong induction on k
    have main_claim : ∀ k ≤ n, k ≠ 0 → ∀ i ≥ N, coeff k (f i) = 0 := by
      intro k
      -- Use strong induction on k
      induction' k using Nat.strong_induction_on with k ih
      intro hk_le hk0 i hi

      have hi_pos : i > 0 := by omega

      have hNk_le : Nk k ≤ (Finset.range (n + 1)).sup Nk := by
        apply Finset.le_sup
        simp only [Finset.mem_range]
        omega

      -- For i ≥ N, we have coeff k (∏ j ∈ range (i+1), f j) = coeff k lim
      have hstab_k : coeff k (∏ j ∈ Finset.range (i + 1), f j) = coeff k lim := by
        apply hNk k
        omega

      -- Also for i (using range i corresponds to step i-1)
      have hstab_k' : coeff k (∏ j ∈ Finset.range i, f j) = coeff k lim := by
        have := hNk k (i - 1)
        simp only [Nat.sub_add_cancel hi_pos] at this
        apply this
        omega

      -- Now: ∏ j ∈ range (i+1), f j = (∏ j ∈ range i, f j) * f i
      have hprod : ∏ j ∈ Finset.range (i + 1), f j = (∏ j ∈ Finset.range i, f j) * f i := by
        rw [Finset.range_add_one, Finset.prod_insert Finset.notMem_range_self]
        ring

      set P := ∏ j ∈ Finset.range i, f j with hP

      -- We have: coeff k (P * f i) = coeff k P
      have hstab_eq : coeff k (P * f i) = coeff k P := by
        calc coeff k (P * f i) = coeff k (∏ j ∈ Finset.range (i + 1), f j) := by rw [hprod, hP]
          _ = coeff k lim := hstab_k
          _ = coeff k P := hstab_k'.symm

      -- Constant coeff of P is 1
      have hP_const : constantCoeff P = 1 := by
        apply constantCoeff_prod_eq_one
        intro j hj
        exact hconst j

      -- coeff 0 P = 1
      have hP0 : coeff 0 P = 1 := by
        rw [coeff_zero_eq_constantCoeff]
        exact hP_const

      -- coeff 0 (f i) = 1
      have hfi0 : coeff 0 (f i) = 1 := by
        rw [coeff_zero_eq_constantCoeff]
        exact hconst i

      -- Use the coefficient formula for products
      rw [coeff_mul] at hstab_eq

      -- Split off the (k, 0) term
      have hanti : (k, 0) ∈ Finset.HasAntidiagonal.antidiagonal k := by
        simp [Finset.HasAntidiagonal.mem_antidiagonal]

      rw [← Finset.insert_erase hanti, Finset.sum_insert (Finset.notMem_erase _ _)] at hstab_eq
      simp only [hfi0, mul_one] at hstab_eq

      -- So the sum equals 0
      have hsum_zero : ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).erase (k, 0), coeff p.1 P * coeff p.2 (f i) = 0 := by
        have heq : coeff k P + ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).erase (k, 0), coeff p.1 P * coeff p.2 (f i) = coeff k P + 0 := by
          rw [add_zero, hstab_eq]
        exact add_left_cancel heq

      -- The (0, k) term is in the sum
      have hanti2 : (0, k) ∈ (Finset.HasAntidiagonal.antidiagonal k).erase (k, 0) := by
        simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, Prod.mk.injEq, ne_eq]
        constructor
        · intro ⟨h1, h2⟩
          exact hk0 h2
        · ring

      rw [← Finset.insert_erase hanti2, Finset.sum_insert (Finset.notMem_erase _ _)] at hsum_zero
      simp only [hP0, one_mul] at hsum_zero

      -- hsum_zero : coeff k (f i) + ∑ p ∈ ((antidiagonal k).erase (k, 0)).erase (0, k), ... = 0

      -- The remaining sum involves coeff p.2 (f i) for p in the remaining set
      -- For p in this set, p.1 + p.2 = k, p ≠ (k, 0), p ≠ (0, k)
      -- So 0 < p.1 < k and 0 < p.2 < k
      -- By induction hypothesis, coeff p.2 (f i) = 0 for all such p

      have hrest_zero : ∑ x ∈ ((Finset.HasAntidiagonal.antidiagonal k).erase (k, 0)).erase (0, k), coeff x.1 P * coeff x.2 (f i) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq] at hp
        -- hp : (p ≠ (0, k) ∧ p ≠ (k, 0) ∧ p.1 + p.2 = k)
        obtain ⟨hp1, hp2, hp_sum⟩ := hp
        -- p.2 < k because p.1 > 0 (since p ≠ (0, k))
        have hp2_lt : p.2 < k := by
          have hp1_pos : p.1 > 0 := by
            by_contra h
            push Not at h
            have hp1_zero : p.1 = 0 := Nat.eq_zero_of_le_zero h
            simp only [hp1_zero, zero_add] at hp_sum
            have : p = (0, k) := Prod.ext hp1_zero hp_sum
            exact hp1 this
          omega
        -- p.2 > 0 because p ≠ (k, 0)
        have hp2_pos : p.2 > 0 := by
          by_contra h
          push Not at h
          have hp2_zero : p.2 = 0 := Nat.eq_zero_of_le_zero h
          simp only [hp2_zero, add_zero] at hp_sum
          have : p = (k, 0) := Prod.ext hp_sum hp2_zero
          exact hp2 this
        -- By induction hypothesis, coeff p.2 (f i) = 0
        have hp2_ne0 : p.2 ≠ 0 := by omega
        have hp2_le : p.2 ≤ n := by omega
        have := ih p.2 hp2_lt hp2_le hp2_ne0 i hi
        simp [this]

      rw [hrest_zero, add_zero] at hsum_zero
      exact hsum_zero

    -- Now use main_claim to prove the goal
    intro i hi k hk
    by_cases hk0 : k = 0
    · simp only [hk0, ↓reduceIte, coeff_zero_eq_constantCoeff]
      exact hconst i
    · simp only [hk0, ↓reduceIte]
      exact main_claim k hk hk0 i hi

-- Helper: if g ≡ 1 (mod x^{n+1}), then coeff n (f * g) = coeff n f
private lemma coeff_mul_one_mod {f g : PowerSeries K} {n : ℕ}
    (hg : ∀ k ≤ n, coeff k g = if k = 0 then 1 else 0) :
    coeff n (f * g) = coeff n f := by
  rw [coeff_mul]
  have : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 f * coeff p.2 g =
         coeff n f * coeff 0 g := by
    apply Finset.sum_eq_single (n, 0)
    · intro ⟨i, j⟩ hij hne
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      have hj : j ≤ n := by omega
      have hj_pos : j ≠ 0 := by
        intro hj0
        apply hne
        simp only [Prod.mk.injEq]
        constructor
        · omega
        · exact hj0
      simp only [hg j hj, hj_pos, ↓reduceIte, mul_zero]
    · intro h
      exfalso
      apply h
      simp only [Finset.HasAntidiagonal.mem_antidiagonal, add_zero]
  rw [this, hg 0 (Nat.zero_le n), ite_eq_left rfl, mul_one]

-- Helper lemma: if f i ≡ 1 (mod x^{n+1}) for i ≥ N, then partial products stabilize at coefficient n
private lemma coeff_prod_eq_of_eventually_one {f : ℕ → PowerSeries K} {n N : ℕ}
    (hf : ∀ i ≥ N, ∀ k ≤ n, coeff k (f i) = if k = 0 then 1 else 0) :
    ∀ i ≥ N, coeff n (∏ j ∈ Finset.range (i + 1), f j) =
             coeff n (∏ j ∈ Finset.range (N + 1), f j) := by
  intro i hi
  induction i with
  | zero =>
    have hN : N = 0 := Nat.eq_zero_of_le_zero hi
    subst hN
    rfl
  | succ i ih =>
    by_cases hiN : i < N
    · have : i + 1 = N := by omega
      simp only [this]
    · push Not at hiN
      have ih' := ih hiN
      rw [Finset.prod_range_succ]
      have hfi : ∀ k ≤ n, coeff k (f (i + 1)) = if k = 0 then 1 else 0 := hf (i + 1) (by omega)
      rw [coeff_mul_one_mod hfi]
      exact ih'

/-- If partial products converge, the limit equals the infinite product.
(Theorem 7.5.13, label: thm.fps.lim.prod-lim-conv) -/
theorem tprod'_eq_of_coeffStabilizesTo_partial_prod
    {f : ℕ → PowerSeries K} {lim : PowerSeries K}
    (h : CoeffStabilizesTo (fun i => ∏ j ∈ Finset.range (i + 1), f j) lim)
    (hconst : ∀ i, constantCoeff (f i) = 1) :
    tprod' f (isMultipliable_of_coeffStabilizesTo_partial_prod h hconst) = lim := by
  ext n
  simp only [tprod', coeff_mk]
  -- Get the stabilization index from h
  obtain ⟨M, hM⟩ := h n
  -- Get the multipliable proof and its N
  set hMult := isMultipliable_of_coeffStabilizesTo_partial_prod h hconst with hMult_def
  set N := hMult.2 n |>.choose with hN_def
  have hN_spec := hMult.2 n |>.choose_spec
  -- For i ≥ max M N, the partial product has n-th coeff equal to both:
  -- 1. coeff n lim (from hM)
  -- 2. coeff n (∏ j ∈ range (N+1), f j) (from hN_spec via coeff_prod_eq_of_eventually_one)
  let L := max M N
  have hL_ge_M : L ≥ M := le_max_left M N
  have hL_ge_N : L ≥ N := le_max_right M N
  -- From hM: coeff n (∏ j ∈ range (L+1), f j) = coeff n lim
  have h1 : coeff n (∏ j ∈ Finset.range (L + 1), f j) = coeff n lim := hM L hL_ge_M
  -- From coeff_prod_eq_of_eventually_one: coeff n (∏ j ∈ range (L+1), f j) = coeff n (∏ j ∈ range (N+1), f j)
  have h2 : coeff n (∏ j ∈ Finset.range (L + 1), f j) =
            coeff n (∏ j ∈ Finset.range (N + 1), f j) :=
    coeff_prod_eq_of_eventually_one hN_spec L hL_ge_N
  -- Combine
  rw [← h1, h2]

end PowerSeries
