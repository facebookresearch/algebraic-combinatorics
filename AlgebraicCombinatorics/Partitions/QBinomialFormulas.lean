/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import AlgebraicCombinatorics.QBinomialBasic

/-!
# q-Binomial Formulas

This file formalizes the q-binomial formulas from the Algebraic Combinatorics text,
including:
- The first q-binomial theorem
- The second q-binomial theorem (Potter's binomial theorem)
- Counting subspaces of finite-dimensional vector spaces over finite fields
- Limits of q-binomial coefficients

## Main Definitions (in namespace `AlgebraicCombinatorics.QBinomialRec`)

* `qBinomial`: The q-binomial coefficient `[n choose k]_q`, defined via q-Pascal recurrence
* `qFactorial`: The q-factorial `[n]_q!`
* `qNat`: The q-analog of natural number `[n]_q`

**Namespace structure:** All definitions in this file are in the sub-namespace
`AlgebraicCombinatorics.QBinomialRec` to avoid conflicts with the canonical definitions
in `QBinomialBasic.lean`. The canonical definitions use the monotone function sum formula,
while this file uses the q-Pascal recurrence. Both are equivalent (see `qBinomial_eq_sum_monotone`).

To use definitions from this file:
- Use full path: `AlgebraicCombinatorics.QBinomialRec.qBinomial`
- Or open the namespace: `open AlgebraicCombinatorics.QBinomialRec`

## Main Results

* `qBinomial_eq_sum_monotone`: Equivalence to the monotone function sum definition
* `qBinomial_eq_sum_subsets`: Equivalence to the subset sum formula
* `qBinomial_first_theorem`: The first q-binomial theorem
* `qBinomial_second_theorem`: The second q-binomial theorem (Potter's binomial theorem)
* `qBinomial_subspace_count`: The q-binomial coefficient counts k-dimensional subspaces
* `qBinomial_limit`: The limit of q-binomial coefficients as n → ∞

## References

* Section on q-binomial formulas from Algebraic Combinatorics lecture notes
* See also `QBinomialBasic.lean` for the canonical definition and basic properties
-/

open Polynomial Finset BigOperators

namespace AlgebraicCombinatorics

/-!
## Sub-namespace for Recursive q-Binomial Definitions

The definitions `qNat`, `qFactorial`, `qBinomial`, and related theorems in this file
use the q-Pascal recurrence, which is different from the monotone function sum
definition in `QBinomialBasic.lean`. To avoid namespace conflicts when both files
are imported together, these definitions are placed in the `QBinomialRec` sub-namespace.

The equivalence between the two definitions is proven in `qBinomial_eq_sum_monotone`.

To use these definitions, either:
1. Open the namespace: `open AlgebraicCombinatorics.QBinomialRec`
2. Use the full path: `AlgebraicCombinatorics.QBinomialRec.qBinomial`
-/
namespace QBinomialRec

section QAnalogs

/-!
### Definition def.pars.qbinom.qint: q-integers and q-factorials

This section formalizes the q-analogs of integers and factorials from Definition 2.3.2.

**Part (a)**: The q-integer `[n]_q = q^0 + q^1 + ... + q^{n-1} ∈ ℤ[q]`

**Part (b)**: The q-factorial `[n]_q! = [1]_q · [2]_q · ... · [n]_q ∈ ℤ[q]`

**Part (c)**: For any element `a` of a ring `A`, `[n]_a` and `[n]_a!` denote the results
of substituting `a` for `q` in `[n]_q` and `[n]_q!`, respectively.

### Remark rmk.pars.qbinom.qint.frac

For any `n ∈ ℕ`:
- `[n]_q = (1 - q^n)/(1 - q)` (in ℤ⟦q⟧ or in the field of rational functions)
- `[n]_1 = n`
- `[n]_1! = n!`
-/

variable {R : Type*} [CommRing R]

/-- Definition def.pars.qbinom.qint (a): The q-integer `[n]_q`.

    The q-analog of a natural number is defined as the sum:
    `[n]_q = q^0 + q^1 + q^2 + ... + q^{n-1}`

    This equals `(1 - q^n)/(1 - q)` in appropriate rings (see `qNat_eq_geom_sum`).
    When evaluated at `q = 1`, this equals `n` (see `qNat_at_one`). -/
noncomputable def qNat (q : R) (n : ℕ) : R :=
  ∑ i ∈ range n, q ^ i

/-- Definition def.pars.qbinom.qint (b): The q-factorial `[n]_q!`.

    The q-factorial is defined as the product:
    `[n]_q! = [1]_q · [2]_q · ... · [n]_q`

    When evaluated at `q = 1`, this equals `n!` (see `qFactorial_at_one`). -/
noncomputable def qFactorial (q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, qNat q (i + 1)

/-- The q-binomial coefficient (Gaussian binomial coefficient)
    `[n choose k]_q = [n]_q! / ([k]_q! · [n-k]_q!)`.

    This is defined as a polynomial in q with integer coefficients.
    It counts partitions that fit in a k × (n-k) box, weighted by q^|λ|.

    We use the recurrence relation (q-Pascal's identity):
    [n choose k]_q = [n-1 choose k-1]_q + q^k · [n-1 choose k]_q

    This avoids division and works over any commutative ring.

    This definition is equivalent to `AlgebraicCombinatorics.qBinomial` in `QBinomialBasic.lean`,
    which uses the monotone function sum definition. The equivalence is proven in
    `qBinomial_eq_sum_monotone`. The argument order here is `(q : R) (n k : ℕ)` vs
    `(n k : ℕ) (q : R)` in `QBinomialBasic.lean`. -/
noncomputable def qBinomial (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinomial q n k + q ^ (k + 1) * qBinomial q n (k + 1)

@[simp]
theorem qNat_zero (q : R) : qNat q 0 = 0 := by simp [qNat]

@[simp]
theorem qNat_one (q : R) : qNat q 1 = 1 := by simp [qNat]

theorem qNat_succ (q : R) (n : ℕ) : qNat q (n + 1) = 1 + q * qNat q n := by
  simp only [qNat, sum_range_succ', pow_zero]
  rw [add_comm]
  congr 1
  simp only [mul_sum, pow_succ, mul_comm]

@[simp]
theorem qFactorial_zero (q : R) : qFactorial q 0 = 1 := by simp [qFactorial]

@[simp]
theorem qFactorial_one (q : R) : qFactorial q 1 = 1 := by simp [qFactorial, qNat]

theorem qFactorial_succ (q : R) (n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * qNat q (n + 1) := by
  simp only [qFactorial, prod_range_succ]

/-!
### Remark rmk.pars.qbinom.qint.frac: Properties of q-integers and q-factorials

The following lemmas formalize the key properties from Remark 2.3.3:
- The geometric series formula: `[n]_q = (1 - q^n)/(1 - q)`
- Evaluation at 1: `[n]_1 = n` and `[n]_1! = n!`
-/

/-- Remark rmk.pars.qbinom.qint.frac (part 1): The q-integer equals the geometric series formula.
    `[n]_q · (1 - q) = 1 - q^n`

    This is the "cleared denominator" form of `[n]_q = (1 - q^n)/(1 - q)`.
    The equality holds in any commutative ring. -/
theorem qNat_mul_one_sub (q : R) (n : ℕ) :
    qNat q n * (1 - q) = 1 - q ^ n := by
  induction n with
  | zero => simp [qNat]
  | succ n ih =>
    rw [qNat_succ]
    calc (1 + q * qNat q n) * (1 - q)
        = (1 - q) + q * qNat q n * (1 - q) := by ring
      _ = (1 - q) + q * (qNat q n * (1 - q)) := by ring
      _ = (1 - q) + q * (1 - q ^ n) := by rw [ih]
      _ = 1 - q ^ (n + 1) := by ring

/-- Remark rmk.pars.qbinom.qint.frac (part 1, field version):
    In a field where `q ≠ 1`, we have `[n]_q = (1 - q^n)/(1 - q)`. -/
theorem qNat_eq_geom_sum {F : Type*} [Field F] (q : F) (n : ℕ) (hq : q ≠ 1) :
    qNat q n = (1 - q ^ n) / (1 - q) := by
  have h : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr hq)
  field_simp [h]
  exact qNat_mul_one_sub q n

/-- Remark rmk.pars.qbinom.qint.frac (part 2): `[n]_1 = n`.

    When we substitute `q = 1` into the q-integer, we get the ordinary integer.
    This follows from `1^0 + 1^1 + ... + 1^{n-1} = n`. -/
@[simp]
theorem qNat_at_one (n : ℕ) : qNat (1 : R) n = n := by
  simp only [qNat, one_pow, sum_const, card_range]
  exact nsmul_one n

/-- Remark rmk.pars.qbinom.qint.frac (part 3): `[n]_1! = n!`.

    When we substitute `q = 1` into the q-factorial, we get the ordinary factorial.
    This follows from `[1]_1 · [2]_1 · ... · [n]_1 = 1 · 2 · ... · n = n!`. -/
@[simp]
theorem qFactorial_at_one (n : ℕ) : qFactorial (1 : R) n = n.factorial := by
  simp only [qFactorial, qNat_at_one]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, Nat.factorial_succ, Nat.cast_mul, mul_comm]

/-- The q-binomial coefficient at `q = 1` equals the ordinary binomial coefficient.

    This follows from the recurrence relation and the fact that `[n]_1 = n`. -/
@[simp]
theorem qBinomial_at_one (n k : ℕ) : qBinomial (1 : R) n k = n.choose k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [qBinomial]
    | succ k => simp [qBinomial, Nat.choose]
  | succ n ih =>
    cases k with
    | zero => simp [qBinomial]
    | succ k =>
      simp only [qBinomial, one_pow, one_mul, ih]
      rw [← Nat.cast_add, Nat.choose_succ_succ]

@[simp]
theorem qBinomial_zero_right (q : R) (n : ℕ) : qBinomial q n 0 = 1 := by
  cases n <;> rfl

/-- Proposition prop.pars.qbinom.0: If k > n, then [n choose k]_q = 0.

    This generalizes Proposition prop.binom.0 (that C(n,k) = 0 when k > n) to q-binomial coefficients.

    The proof uses the partition-theoretic interpretation: [n choose k]_q is a sum over partitions
    with largest part ≤ n-k and length ≤ k. When k > n, we have n-k < 0, so no such partition exists,
    and the sum is empty (equals 0).

    Alternatively, the proof proceeds by induction using the q-Pascal recurrence. -/
theorem qBinomial_gt (q : R) (n k : ℕ) (h : k > n) : qBinomial q n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      simp only [qBinomial]
      have hk1 : k > n := by omega
      have hk2 : k + 1 > n := by omega
      rw [ih k hk1, ih (k + 1) hk2, mul_zero, add_zero]

/-- Alias for `qBinomial_gt` with the hypothesis stated as `n < k`.
    This is the form used in Proposition prop.pars.qbinom.0. -/
theorem qBinomial_eq_zero_of_lt (q : R) (n k : ℕ) (h : n < k) : qBinomial q n k = 0 :=
  qBinomial_gt q n k h

theorem qBinomial_self (q : R) (n : ℕ) : qBinomial q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qBinomial, ih]
    have h : n + 1 > n := Nat.lt_succ_self n
    rw [qBinomial_gt q n (n + 1) h, mul_zero, add_zero]

/-- Proposition prop.pars.qbinom.n0: We have [n choose 0]_q = [n choose n]_q = 1
    for each n ∈ ℕ.

    This is a fundamental boundary condition for q-binomial coefficients,
    analogous to the classical binomial coefficient identities C(n,0) = C(n,n) = 1. -/
theorem qBinomial_boundary (q : R) (n : ℕ) : qBinomial q n 0 = 1 ∧ qBinomial q n n = 1 :=
  ⟨qBinomial_zero_right q n, qBinomial_self q n⟩

/-!
### Proposition prop.pars.qbinom.alt-defs: Alternative definitions of q-binomial coefficients

This section formalizes the three equivalent characterizations of q-binomial coefficients
from Proposition 11.2.4 (prop.pars.qbinom.alt-defs) of the textbook.

**Part (a)**: Sum over weakly increasing tuples
  `[n choose k]_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ i_k ≤ n-k} q^{i₁ + i₂ + ... + i_k}`

**Part (b)**: Sum over k-element subsets
  `[n choose k]_q = ∑_{S ⊆ {1,...,n}, |S| = k} q^{sum(S) - (1 + 2 + ... + k)}`

**Part (c)**: Evaluation at q = 1 gives ordinary binomial coefficient
  `[n choose k]_1 = C(n, k)`

Part (c) is already proved as `qBinomial_at_one` above.
-/

-- Triangular number: 1 + 2 + ... + k
/-- The triangular number T(k) = 1 + 2 + ... + k = k(k+1)/2. -/
def triangular (k : ℕ) : ℕ := k * (k + 1) / 2

@[simp] lemma triangular_zero : triangular 0 = 0 := rfl

@[simp] lemma triangular_one : triangular 1 = 1 := rfl

@[simp] lemma triangular_two : triangular 2 = 3 := rfl

/-- The triangular number equals the sum of the first k positive integers. -/
lemma triangular_eq_sum (k : ℕ) : triangular k = ∑ i ∈ range k, (i + 1) := by
  unfold triangular
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have h1 : (k + 1) * (k + 1 + 1) / 2 = k * (k + 1) / 2 + (k + 1) := by
      have h4 : (k * (k + 1) + 2 * (k + 1)) / 2 = k * (k + 1) / 2 + (k + 1) := by
        rw [Nat.add_mul_div_left _ _ (by omega : 2 > 0)]
      have h5 : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
      rw [h5, h4]
    rw [h1, ← ih]

-- The set of monotone functions from Fin k to Fin (m + 1)
-- NOTE: We reuse the canonical definition from QBinomialBasic.lean.
-- The definition is copied here (not aliased) to maintain proof compatibility,
-- but it is definitionally equal to `AlgebraicCombinatorics.monotoneFunctions`.
/-- The set of monotone (weakly increasing) functions from Fin k to Fin (m + 1).
    This represents k-tuples (i₁, ..., i_k) with 0 ≤ i₁ ≤ i₂ ≤ ... ≤ i_k ≤ m.

    This is definitionally equal to `AlgebraicCombinatorics.monotoneFunctions`. -/
def monotoneFunctions (k m : ℕ) : Finset (Fin k → Fin (m + 1)) :=
  Finset.univ.filter fun f => Monotone f

/-- The local `monotoneFunctions` is definitionally equal to the canonical version. -/
theorem monotoneFunctions_eq_canonical (k m : ℕ) :
    monotoneFunctions k m = AlgebraicCombinatorics.monotoneFunctions k m := rfl

/-- The sum of values of a function from Fin k to Fin (m + 1). -/
def sumValues (k m : ℕ) (f : Fin k → Fin (m + 1)) : ℕ :=
  ∑ i : Fin k, (f i).val

-- The set of k-element subsets of {1, 2, ..., n}
/-- The set of k-element subsets of {1, 2, ..., n}. -/
def kSubsetsOfIcc (n k : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (fun S => S.card = k)

/-- The sum of elements in a finite set of natural numbers.

    Note: This is named `finsetSumNat` to distinguish from `AlgebraicCombinatorics.CauchyBinet.finsetSumFin`,
    which computes the sum of elements in a `Finset (Fin n)` by extracting their `.val`.
    Both compute "the sum of elements" but for different element types. -/
def finsetSumNat (S : Finset ℕ) : ℕ := S.sum id

/-- Proposition prop.pars.qbinom.alt-defs (a): Alternative definition of q-binomial as sum
    over weakly increasing tuples.

    [n choose k]_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ i_k ≤ n-k} q^{i₁ + i₂ + ... + i_k}

    The sum ranges over all weakly increasing k-tuples (i₁, i₂, ..., i_k) with entries in {0, 1, ..., n-k}.
    When k = 0, this is a single term with exponent 0, giving 1.

    **Important**: This theorem requires `k ≤ n`. When k > n, the natural number subtraction
    `n - k = 0` in Lean, so `monotoneFunctions k 0` represents functions `Fin k → Fin 1`,
    which has exactly one element (the constant 0 function). This would give a sum of 1,
    but `qBinomial q n k = 0` when k > n (see `qBinomial_gt`).

    This characterization arises from the bijection between partitions fitting in a k × (n-k) box
    and weakly increasing k-tuples: a partition λ = (λ₁, ..., λ_k) with λ₁ ≤ n-k corresponds to
    the tuple (λ_k, λ_{k-1}, ..., λ₁) (reversed and possibly padded with zeros). -/
-- Helper definitions for the bijections in the proof of qBinomial_eq_sum_monotone
private def monotoneFunctionsStartZero (k m : ℕ) : Finset (Fin (k + 1) → Fin (m + 1)) :=
  (monotoneFunctions (k + 1) m).filter fun f => f 0 = 0

private def monotoneFunctionsStartPos (k m : ℕ) : Finset (Fin (k + 1) → Fin (m + 1)) :=
  (monotoneFunctions (k + 1) m).filter fun f => f 0 ≠ 0

private def dropFirst (k m : ℕ) (f : Fin (k + 1) → Fin (m + 1)) : Fin k → Fin (m + 1) :=
  fun i => f i.succ

private def prependZero (k m : ℕ) (g : Fin k → Fin (m + 1)) : Fin (k + 1) → Fin (m + 1) :=
  Fin.cons 0 g

private def shiftDown (k m : ℕ) (f : Fin (k + 1) → Fin (m + 2)) (hf : ∀ i, (f i).val ≥ 1) :
    Fin (k + 1) → Fin (m + 1) :=
  fun i => ⟨(f i).val - 1, by have h1 := (f i).isLt; have h2 := hf i; omega⟩

private def shiftUp (k m : ℕ) (g : Fin (k + 1) → Fin (m + 1)) : Fin (k + 1) → Fin (m + 2) :=
  fun i => ⟨(g i).val + 1, by have h := (g i).isLt; omega⟩

private lemma dropFirst_monotone (k m : ℕ) (f : Fin (k + 1) → Fin (m + 1)) (hf : Monotone f) :
    Monotone (dropFirst k m f) := fun _ _ hij => hf (Fin.succ_le_succ_iff.mpr hij)

private lemma prependZero_zero (k m : ℕ) (g : Fin k → Fin (m + 1)) : prependZero k m g 0 = 0 := by
  simp [prependZero]

private lemma prependZero_monotone (k m : ℕ) (g : Fin k → Fin (m + 1)) (hg : Monotone g) :
    Monotone (prependZero k m g) := by
  intro i j hij
  cases i using Fin.cases with
  | zero => simp only [prependZero, Fin.cons_zero]; exact Fin.zero_le _
  | succ i =>
    cases j using Fin.cases with
    | zero => exact absurd hij (Fin.not_le.mpr (Fin.succ_pos i))
    | succ j => simp only [prependZero, Fin.cons_succ]; exact hg (Fin.succ_le_succ_iff.mp hij)

private lemma dropFirst_prependZero (k m : ℕ) (g : Fin k → Fin (m + 1)) :
    dropFirst k m (prependZero k m g) = g := by ext i; simp [dropFirst, prependZero]

private lemma prependZero_dropFirst (k m : ℕ) (f : Fin (k + 1) → Fin (m + 1)) (hf0 : f 0 = 0) :
    prependZero k m (dropFirst k m f) = f := by
  ext i; cases i using Fin.cases with
  | zero => simp only [prependZero, Fin.cons_zero, hf0]
  | succ i => simp [prependZero, dropFirst]

private lemma dropFirst_sumValues (k m : ℕ) (f : Fin (k + 1) → Fin (m + 1)) (hf0 : f 0 = 0) :
    sumValues (k + 1) m f = sumValues k m (dropFirst k m f) := by
  simp only [sumValues, dropFirst]; rw [Fin.sum_univ_succ]; simp only [hf0, Fin.val_zero, zero_add]

private lemma shiftUp_pos (k m : ℕ) (g : Fin (k + 1) → Fin (m + 1)) (i : Fin (k + 1)) :
    (shiftUp k m g i).val ≥ 1 := by unfold shiftUp; exact Nat.le_add_left 1 _

private lemma shiftUp_zero_ne_zero (k m : ℕ) (g : Fin (k + 1) → Fin (m + 1)) :
    shiftUp k m g 0 ≠ 0 := by
  unfold shiftUp; intro h; simp only [Fin.ext_iff, Fin.val_zero] at h; omega

private lemma shiftUp_monotone (k m : ℕ) (g : Fin (k + 1) → Fin (m + 1)) (hg : Monotone g) :
    Monotone (shiftUp k m g) := by
  intro i j hij; unfold shiftUp; simp only [Fin.le_def]; have := hg hij; omega

private lemma shiftDown_monotone (k m : ℕ) (f : Fin (k + 1) → Fin (m + 2)) (hf : Monotone f)
    (hfpos : ∀ i, (f i).val ≥ 1) : Monotone (shiftDown k m f hfpos) := by
  intro i j hij; unfold shiftDown; simp only [Fin.le_def]
  have := hf hij; have hi := hfpos i; have hj := hfpos j; omega

private lemma shiftDown_sumValues (k m : ℕ) (f : Fin (k + 1) → Fin (m + 2)) (hfpos : ∀ i, (f i).val ≥ 1) :
    sumValues (k + 1) (m + 1) f = (k + 1) + sumValues (k + 1) m (shiftDown k m f hfpos) := by
  simp only [sumValues, shiftDown, Fin.val_mk]
  have h : ∑ i : Fin (k + 1), (f i).val = ∑ i : Fin (k + 1), ((f i).val - 1 + 1) := by
    apply Finset.sum_congr rfl; intro i _; have := hfpos i; omega
  rw [h]; simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one]; ring

private lemma monotoneFunctionsStartPos_all_pos (k m : ℕ) (f : Fin (k + 1) → Fin (m + 2))
    (hf : f ∈ monotoneFunctionsStartPos k (m + 1)) : ∀ i, (f i).val ≥ 1 := by
  simp only [monotoneFunctionsStartPos, monotoneFunctions, mem_filter, mem_univ, true_and] at hf
  intro i
  have hf0 : (f 0).val ≠ 0 := by intro h; apply hf.2; exact Fin.ext h
  have h0pos : (f 0).val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hf0
  have hi : f 0 ≤ f i := hf.1 (Fin.zero_le i)
  omega

private lemma mem_monotoneFunctionsStartPos_iff (k m : ℕ) (f : Fin (k + 1) → Fin (m + 2)) :
    f ∈ monotoneFunctionsStartPos k (m + 1) ↔ Monotone f ∧ f 0 ≠ 0 := by
  simp only [monotoneFunctionsStartPos, monotoneFunctions, mem_filter, mem_univ, true_and]

private lemma shiftUp_shiftDown (k m : ℕ) (f : Fin (k + 1) → Fin (m + 2)) (hfpos : ∀ i, (f i).val ≥ 1) :
    shiftUp k m (shiftDown k m f hfpos) = f := by
  funext i; unfold shiftDown shiftUp; simp only [Fin.ext_iff]; have := hfpos i; omega

private lemma shiftDown_shiftUp (k m : ℕ) (g : Fin (k + 1) → Fin (m + 1)) :
    shiftDown k m (shiftUp k m g) (shiftUp_pos k m g) = g := by
  funext i; unfold shiftDown shiftUp; simp only [Fin.ext_iff]; omega

private lemma monotoneFunctions_partition (k m : ℕ) :
    monotoneFunctions (k + 1) m = monotoneFunctionsStartZero k m ∪ monotoneFunctionsStartPos k m := by
  ext f
  simp only [monotoneFunctions, monotoneFunctionsStartZero, monotoneFunctionsStartPos,
             mem_filter, mem_union, mem_univ, true_and]
  constructor
  · intro hf; by_cases h : f 0 = 0; left; exact ⟨hf, h⟩; right; exact ⟨hf, h⟩
  · intro hf; rcases hf with ⟨hf, _⟩ | ⟨hf, _⟩ <;> exact hf

private lemma monotoneFunctions_disjoint (k m : ℕ) :
    Disjoint (monotoneFunctionsStartZero k m) (monotoneFunctionsStartPos k m) := by
  simp only [monotoneFunctionsStartZero, monotoneFunctionsStartPos, disjoint_filter]
  intro f _ h0 h1; exact h1 h0

private lemma sum_monotoneFunctionsStartZero_eq (k m : ℕ) (q : R) :
    ∑ f ∈ monotoneFunctionsStartZero k m, q ^ (sumValues (k + 1) m f) =
    ∑ g ∈ monotoneFunctions k m, q ^ (sumValues k m g) := by
  apply Finset.sum_bij'
    (i := fun f _ => dropFirst k m f)
    (j := fun g _ => prependZero k m g)
  · intro f hf; simp only [monotoneFunctionsStartZero, monotoneFunctions, mem_filter, mem_univ, true_and] at hf ⊢
    exact dropFirst_monotone k m f hf.1
  · intro g hg; simp only [monotoneFunctionsStartZero, monotoneFunctions, mem_filter, mem_univ, true_and] at hg ⊢
    exact ⟨prependZero_monotone k m g hg, prependZero_zero k m g⟩
  · intro f hf; simp only [monotoneFunctionsStartZero, mem_filter] at hf
    exact prependZero_dropFirst k m f hf.2
  · intro g _; exact dropFirst_prependZero k m g
  · intro f hf; simp only [monotoneFunctionsStartZero, mem_filter] at hf
    rw [dropFirst_sumValues k m f hf.2]

private lemma sum_monotoneFunctionsStartPos_eq (k m : ℕ) (q : R) :
    ∑ f ∈ monotoneFunctionsStartPos k (m + 1), q ^ (sumValues (k + 1) (m + 1) f) =
    q ^ (k + 1) * ∑ g ∈ monotoneFunctions (k + 1) m, q ^ (sumValues (k + 1) m g) := by
  rw [mul_sum]
  refine Finset.sum_bij'
    (i := fun (f : Fin (k + 1) → Fin (m + 2)) (hf : f ∈ monotoneFunctionsStartPos k (m + 1)) =>
      shiftDown k m f (monotoneFunctionsStartPos_all_pos k m f hf))
    (j := fun (g : Fin (k + 1) → Fin (m + 1)) (_ : g ∈ monotoneFunctions (k + 1) m) =>
      shiftUp k m g)
    ?_ ?_ ?_ ?_ ?_
  · intro f hf
    simp only [monotoneFunctions, mem_filter, mem_univ, true_and]
    have hf' := (mem_monotoneFunctionsStartPos_iff k m f).mp hf
    exact shiftDown_monotone k m f hf'.1 (monotoneFunctionsStartPos_all_pos k m f hf)
  · intro g hg
    rw [mem_monotoneFunctionsStartPos_iff]
    simp only [monotoneFunctions, mem_filter, mem_univ, true_and] at hg
    exact ⟨shiftUp_monotone k m g hg, shiftUp_zero_ne_zero k m g⟩
  · intro f hf
    exact shiftUp_shiftDown k m f (monotoneFunctionsStartPos_all_pos k m f hf)
  · intro g _
    exact shiftDown_shiftUp k m g
  · intro f hf
    rw [shiftDown_sumValues k m f (monotoneFunctionsStartPos_all_pos k m f hf)]
    rw [pow_add]

private lemma monotoneFunctionsStartPos_zero_empty (n : ℕ) : monotoneFunctionsStartPos n 0 = ∅ := by
  ext f
  constructor
  · intro hf
    simp only [monotoneFunctionsStartPos, monotoneFunctions, mem_filter, mem_univ, true_and] at hf
    exfalso
    apply hf.2
    exact Fin.eq_zero (f 0)
  · intro hf
    simp_all

theorem qBinomial_eq_sum_monotone (q : R) (n k : ℕ) (hk : k ≤ n) :
    qBinomial q n k = ∑ f ∈ monotoneFunctions k (n - k), q ^ (sumValues k (n - k) f) := by
  induction n generalizing k with
  | zero =>
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    simp only [qBinomial, Nat.sub_zero, monotoneFunctions, sumValues]
    have h1 : (univ : Finset (Fin 0 → Fin 1)).filter (fun f => Monotone f) = {default} := by
      ext f; simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro _; exact Subsingleton.elim f default
      · intro hf; subst hf; intro i; exact Fin.elim0 i
    rw [h1]
    simp only [sum_singleton, univ_eq_empty, sum_empty, pow_zero]
  | succ n ih =>
    cases k with
    | zero =>
      simp only [qBinomial, Nat.sub_zero, monotoneFunctions, sumValues]
      have h1 : (univ : Finset (Fin 0 → Fin (n + 2))).filter (fun f => Monotone f) = {default} := by
        ext f; simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro _; exact Subsingleton.elim f default
        · intro hf; subst hf; intro i; exact Fin.elim0 i
      rw [h1]
      simp only [sum_singleton, univ_eq_empty, sum_empty, pow_zero]
    | succ k =>
      have hkn : k ≤ n := Nat.le_of_succ_le_succ hk
      simp only [qBinomial]
      have ih1 : qBinomial q n k = ∑ f ∈ monotoneFunctions k (n - k), q ^ (sumValues k (n - k) f) := ih k hkn
      rw [ih1]
      have heq : n + 1 - (k + 1) = n - k := by omega
      conv_rhs => rw [heq, monotoneFunctions_partition k (n - k)]
      rw [sum_union (monotoneFunctions_disjoint k (n - k))]
      rw [sum_monotoneFunctionsStartZero_eq k (n - k) q]
      by_cases hkn1 : k + 1 ≤ n
      · have ih2 : qBinomial q n (k + 1) = ∑ f ∈ monotoneFunctions (k + 1) (n - (k + 1)),
            q ^ (sumValues (k + 1) (n - (k + 1)) f) := ih (k + 1) hkn1
        rw [ih2]
        have heq2 : n - k = n - (k + 1) + 1 := by omega
        congr 1
        rw [heq2]
        exact (sum_monotoneFunctionsStartPos_eq k (n - (k + 1)) q).symm
      · have hgt : k + 1 > n := Nat.lt_of_not_le hkn1
        have h0 : qBinomial q n (k + 1) = 0 := qBinomial_gt q n (k + 1) hgt
        rw [h0, mul_zero, add_zero]
        have hkeqn : k = n := by omega
        subst hkeqn
        rw [Nat.sub_self, monotoneFunctionsStartPos_zero_empty k, sum_empty, add_zero]

/-- Proposition prop.pars.qbinom.alt-defs (b): Alternative definition of q-binomial as sum
    over k-element subsets.

    [n choose k]_q = ∑_{S ⊆ {1,...,n}, |S| = k} q^{sum(S) - (1 + 2 + ... + k)}

    This characterization shows the q-binomial as a weighted count of k-element subsets
    of {1, 2, ..., n}, where the weight q^{sum(S) - triangular(k)} accounts for the
    "excess" sum beyond the minimal sum (which is 1 + 2 + ... + k for the subset {1, 2, ..., k}).

    The bijection between parts (a) and (b) is:
    Given a weakly increasing k-tuple (i₁, ..., i_k) ∈ {0, ..., n-k}^k,
    map to the strictly increasing k-tuple (i₁ + 1, i₂ + 2, ..., i_k + k) ∈ {1, ..., n}^k,
    which corresponds to the k-element subset {i₁ + 1, i₂ + 2, ..., i_k + k} ⊆ {1, ..., n}.
    This bijection preserves the exponent: i₁ + i₂ + ... + i_k = sum(S) - (1 + 2 + ... + k). -/
-- Helper lemmas for the bijection proof
private lemma kSubsetsOfIcc_empty_of_gt (n k : ℕ) (h : k > n) :
    kSubsetsOfIcc n k = ∅ := by
  rw [kSubsetsOfIcc]
  simp only [filter_eq_empty_iff, mem_powerset]
  intro S hS
  have hcard : S.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hS
  rw [Nat.card_Icc] at hcard
  omega

private lemma orderEmbOfFin_lower_bound' (S : Finset ℕ) (k : ℕ)
    (hcard : S.card = k) (hPos : ∀ x ∈ S, x ≥ 1) (i : Fin k) :
    S.orderEmbOfFin hcard i ≥ i.val + 1 := by
  have H : ∀ m : ℕ, (hm : m < k) → S.orderEmbOfFin hcard ⟨m, hm⟩ ≥ m + 1 := by
    intro m
    induction m with
    | zero =>
      intro hm
      have hmem : S.orderEmbOfFin hcard ⟨0, hm⟩ ∈ S := orderEmbOfFin_mem S hcard ⟨0, hm⟩
      exact hPos _ hmem
    | succ m ih =>
      intro hm
      have hm' : m < k := by omega
      have ihm := ih hm'
      have hlt : S.orderEmbOfFin hcard ⟨m, hm'⟩ < S.orderEmbOfFin hcard ⟨m + 1, hm⟩ := by
        apply (S.orderEmbOfFin hcard).strictMono
        simp only [Fin.lt_def]
        omega
      omega
  exact H i.val i.isLt

private lemma orderEmbOfFin_upper_bound_aux' (S : Finset ℕ) (n k : ℕ)
    (hcard : S.card = k) (hSub : S ⊆ Finset.Icc 1 n) (hkn : k ≤ n) (hkpos : 0 < k) :
    ∀ m : ℕ, (hm : m < k) → S.orderEmbOfFin hcard ⟨m, hm⟩ ≤ n - (k - 1 - m) := by
  have Hrev : ∀ d : ℕ, d < k → (∀ m : ℕ, k - 1 - m = d → (hm : m < k) →
      S.orderEmbOfFin hcard ⟨m, hm⟩ ≤ n - d) := by
    intro d
    induction d with
    | zero =>
      intro _ m hmeq hm
      have hmeq' : m = k - 1 := by omega
      subst hmeq'
      have hmem : S.orderEmbOfFin hcard ⟨k - 1, hm⟩ ∈ S := orderEmbOfFin_mem S hcard ⟨k - 1, hm⟩
      have hIn : S.orderEmbOfFin hcard ⟨k - 1, hm⟩ ∈ Finset.Icc 1 n := hSub hmem
      simp only [mem_Icc, Nat.sub_zero] at hIn ⊢
      exact hIn.2
    | succ d ihd =>
      intro hdk m hmeq hm
      have hdk' : d < k := by omega
      have hm1 : m + 1 < k := by omega
      have hmeq1 : k - 1 - (m + 1) = d := by omega
      have ih1 := ihd hdk' (m + 1) hmeq1 hm1
      have hlt : S.orderEmbOfFin hcard ⟨m, hm⟩ < S.orderEmbOfFin hcard ⟨m + 1, hm1⟩ := by
        apply (S.orderEmbOfFin hcard).strictMono
        simp only [Fin.lt_def]
        omega
      omega
  intro m hm
  have hd : k - 1 - m < k := by omega
  exact Hrev (k - 1 - m) hd m rfl hm

private lemma orderEmbOfFin_upper_bound' (S : Finset ℕ) (n k : ℕ)
    (hcard : S.card = k) (hSub : S ⊆ Finset.Icc 1 n) (hkn : k ≤ n) (i : Fin k) :
    S.orderEmbOfFin hcard i ≤ n - k + 1 + i.val := by
  have hkpos : 0 < k := Fin.pos i
  have h := orderEmbOfFin_upper_bound_aux' S n k hcard hSub hkn hkpos i.val i.isLt
  have heq : n - (k - 1 - i.val) = n - k + 1 + i.val := by omega
  rw [heq] at h
  exact h

private lemma orderEmbOfFin_gap' (S : Finset ℕ) (k : ℕ)
    (hcard : S.card = k) (a b : Fin k) (hab : a ≤ b) :
    S.orderEmbOfFin hcard b ≥ S.orderEmbOfFin hcard a + (b.val - a.val) := by
  have H : ∀ d : ℕ, ∀ (x y : Fin k), x.val + d = y.val →
      S.orderEmbOfFin hcard y ≥ S.orderEmbOfFin hcard x + d := by
    intro d
    induction d with
    | zero =>
      intro x y heq
      have hxy : x = y := by ext; omega
      simp only [add_zero, hxy, le_refl]
    | succ d ihd =>
      intro x y heq
      have hz : x.val + d < k := by omega
      let z : Fin k := ⟨x.val + d, hz⟩
      have hxz : x.val + d = z.val := rfl
      have ihd' := ihd x z hxz
      have hlt : S.orderEmbOfFin hcard z < S.orderEmbOfFin hcard y := by
        apply (S.orderEmbOfFin hcard).strictMono
        simp only [Fin.lt_def, z]
        omega
      calc S.orderEmbOfFin hcard y
          > S.orderEmbOfFin hcard z := hlt
        _ ≥ S.orderEmbOfFin hcard x + d := ihd'
  exact H (b.val - a.val) a b (by omega)

theorem qBinomial_eq_sum_subsets (q : R) (n k : ℕ) :
    qBinomial q n k = ∑ S ∈ kSubsetsOfIcc n k, q ^ (finsetSumNat S - triangular k) := by
  by_cases hkn : k ≤ n
  · -- Case k ≤ n: use the bijection between monotone functions and k-subsets
    rw [qBinomial_eq_sum_monotone q n k hkn]
    -- Define the forward map: f ↦ {f(0)+1, f(1)+2, ..., f(k-1)+k}
    -- Define the inverse map: S ↦ (λ i => S.orderEmbOfFin hcard i - (i+1))
    refine Finset.sum_bij'
      (i := fun f _ => Finset.image (fun i : Fin k => (f i).val + i.val + 1) Finset.univ)
      (j := fun S hS =>
        let hcard : S.card = k := by simp only [kSubsetsOfIcc, mem_filter] at hS; exact hS.2
        let hSub : S ⊆ Finset.Icc 1 n := by
          simp only [kSubsetsOfIcc, mem_filter, mem_powerset] at hS; exact hS.1
        fun i => ⟨S.orderEmbOfFin hcard i - (i.val + 1), by
          have hlow := orderEmbOfFin_lower_bound' S k hcard (fun x hx => by
            have := hSub hx; simp only [mem_Icc] at this; exact this.1) i
          have hup := orderEmbOfFin_upper_bound' S n k hcard hSub hkn i
          omega⟩)
      ?_ ?_ ?_ ?_ ?_
    · -- hi: forward map lands in kSubsetsOfIcc
      intro f hf
      simp only [kSubsetsOfIcc, mem_filter, mem_powerset]
      constructor
      · intro x hx
        simp only [mem_image, mem_univ, true_and] at hx
        obtain ⟨i, rfl⟩ := hx
        simp only [mem_Icc]
        constructor
        · omega
        · have hfi : (f i).val < n - k + 1 := (f i).isLt
          omega
      · rw [card_image_of_injective]
        · exact card_fin k
        · intro i j hij
          simp only [monotoneFunctions, mem_filter, mem_univ, true_and] at hf
          by_contra hne
          rcases Nat.lt_trichotomy i j with hlt | heq | hgt
          · have hle : f i ≤ f j := hf (le_of_lt hlt)
            have h1 : (f i).val ≤ (f j).val := hle
            have h2 : i.val < j.val := hlt
            have : (f i).val + i.val + 1 < (f j).val + j.val + 1 := by omega
            exact (Nat.ne_of_lt this) hij
          · exact hne (Fin.ext heq)
          · have hle : f j ≤ f i := hf (le_of_lt hgt)
            have h1 : (f j).val ≤ (f i).val := hle
            have h2 : j.val < i.val := hgt
            have : (f j).val + j.val + 1 < (f i).val + i.val + 1 := by omega
            exact (Nat.ne_of_gt this) hij
    · -- hj: inverse map lands in monotoneFunctions
      intro S hS
      simp only [monotoneFunctions, mem_filter, mem_univ, true_and]
      intro a b hab
      simp only [Fin.le_def]
      have hcard : S.card = k := by simp only [kSubsetsOfIcc, mem_filter] at hS; exact hS.2
      have hSub : S ⊆ Finset.Icc 1 n := by
        simp only [kSubsetsOfIcc, mem_filter, mem_powerset] at hS; exact hS.1
      have hgap := orderEmbOfFin_gap' S k hcard a b hab
      have hlow_a := orderEmbOfFin_lower_bound' S k hcard (fun x hx => by
        have := hSub hx; simp only [mem_Icc] at this; exact this.1) a
      omega
    · -- left_inv: inverse ∘ forward = id
      intro f hf
      ext i
      have hstrictMono : StrictMono (fun i : Fin k => (f i).val + i.val + 1) := by
        simp only [monotoneFunctions, mem_filter, mem_univ, true_and] at hf
        intro a b hab
        have hle : f a ≤ f b := hf (le_of_lt hab)
        have h1 : (f a).val ≤ (f b).val := hle
        have h2 : a.val < b.val := hab
        show (f a).val + a.val + 1 < (f b).val + b.val + 1
        omega
      have hinj : Function.Injective (fun i : Fin k => (f i).val + i.val + 1) := by
        intro a b hab
        by_contra hne
        rcases Nat.lt_trichotomy a b with hlt | heq | hgt
        · exact Nat.ne_of_lt (hstrictMono hlt) hab
        · exact hne (Fin.ext heq)
        · exact Nat.ne_of_gt (hstrictMono hgt) hab
      let S := Finset.image (fun i : Fin k => (f i).val + i.val + 1) Finset.univ
      have hcard : S.card = k := by
        rw [card_image_of_injective _ hinj, card_fin k]
      have hsort : S.sort = (List.finRange k).map (fun i => (f i).val + i.val + 1) := by
        apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
        · intro a _ b _ hab hba; omega
        · exact pairwise_sort S (· ≤ ·)
        · apply List.Pairwise.map (R := (· < ·))
          · intro a b hab; exact le_of_lt (hstrictMono hab)
          · exact List.pairwise_lt_finRange k
        · rw [List.perm_ext_iff_of_nodup (sort_nodup S (· ≤ ·))
              (List.Nodup.map hinj (List.nodup_finRange k))]
          intro x
          constructor
          · intro hx
            rw [mem_sort, mem_image] at hx
            obtain ⟨j, _, hj⟩ := hx
            rw [List.mem_map]
            exact ⟨j, List.mem_finRange j, hj⟩
          · intro hx
            rw [List.mem_map] at hx
            obtain ⟨j, hj1, hj2⟩ := hx
            rw [mem_sort, mem_image]
            exact ⟨j, mem_univ _, hj2⟩
      have helem : (S.orderEmbOfFin hcard i : ℕ) = S.sort[i.val]'(by simp [hcard]) :=
        orderEmbOfFin_apply S hcard i
      have hi2 : i.val < ((List.finRange k).map (fun i => (f i).val + i.val + 1)).length := by simp
      have hgoal : ((List.finRange k).map (fun i => (f i).val + i.val + 1))[i.val]'hi2 =
          (f i).val + i.val + 1 := by
        simp only [List.getElem_map, List.getElem_finRange]
        congr 1
      calc (S.orderEmbOfFin hcard i : ℕ) - (i.val + 1)
          = S.sort[i.val]'(by simp [hcard]) - (i.val + 1) := by rw [helem]
        _ = ((List.finRange k).map (fun i => (f i).val + i.val + 1))[i.val]'hi2 - (i.val + 1) := by
            simp only [hsort]
        _ = (f i).val + i.val + 1 - (i.val + 1) := by rw [hgoal]
        _ = (f i).val := by omega
    · -- right_inv: forward ∘ inverse = id
      intro S hS
      have hcard : S.card = k := by simp only [kSubsetsOfIcc, mem_filter] at hS; exact hS.2
      have hSub : S ⊆ Finset.Icc 1 n := by
        simp only [kSubsetsOfIcc, mem_filter, mem_powerset] at hS; exact hS.1
      ext x
      simp only [mem_image, mem_univ, true_and]
      constructor
      · intro ⟨i, hi⟩
        have hlow := orderEmbOfFin_lower_bound' S k hcard (fun y hy => by
          have := hSub hy; simp only [mem_Icc] at this; exact this.1) i
        have heq : S.orderEmbOfFin hcard i - (i.val + 1) + i.val + 1 = S.orderEmbOfFin hcard i := by
          omega
        rw [← hi, heq]
        exact orderEmbOfFin_mem S hcard i
      · intro hx
        have hxS : x ∈ S := hx
        -- x is the j-th element of S for some j
        have ⟨j, hj⟩ := (S.orderIsoOfFin hcard).surjective ⟨x, hxS⟩
        use j
        have hlow := orderEmbOfFin_lower_bound' S k hcard (fun y hy => by
          have := hSub hy; simp only [mem_Icc] at this; exact this.1) j
        have heq : S.orderEmbOfFin hcard j = x := by
          have : (S.orderIsoOfFin hcard j : ℕ) = x := by
            rw [hj]
          exact this
        rw [heq]
        omega
    · -- Exponent matching: sumValues = finsetSumNat - triangular
      intro f hf
      simp only [sumValues, finsetSumNat, triangular_eq_sum]
      have hinj : Function.Injective (fun i : Fin k => (f i).val + i.val + 1) := by
        simp only [monotoneFunctions, mem_filter, mem_univ, true_and] at hf
        intro a b hab
        by_contra hne
        rcases Nat.lt_trichotomy a b with hlt | heq | hgt
        · have hle : f a ≤ f b := hf (le_of_lt hlt)
          have h1 : (f a).val ≤ (f b).val := hle
          have : (f a).val + a.val + 1 < (f b).val + b.val + 1 := by omega
          exact (Nat.ne_of_lt this) hab
        · exact hne (Fin.ext heq)
        · have hle : f b ≤ f a := hf (le_of_lt hgt)
          have h1 : (f b).val ≤ (f a).val := hle
          have : (f b).val + b.val + 1 < (f a).val + a.val + 1 := by omega
          exact (Nat.ne_of_gt this) hab
      -- sum_{i} f(i) = sum_{x in S} x - sum_{i} (i + 1)
      -- where S = {f(0)+1, f(1)+2, ..., f(k-1)+k}
      let S := Finset.image (fun i : Fin k => (f i).val + i.val + 1) Finset.univ
      have hSsum : S.sum id = ∑ i : Fin k, ((f i).val + i.val + 1) := by
        rw [sum_image (fun _ _ _ _ h => hinj h)]
        rfl
      have htri : ∑ i ∈ range k, (i + 1) = ∑ i : Fin k, (i.val + 1) := by
        rw [← Fin.sum_univ_eq_sum_range (fun i => i + 1)]
      congr 1
      calc ∑ i : Fin k, (f i).val
          = ∑ i : Fin k, ((f i).val + i.val + 1) - ∑ i : Fin k, (i.val + 1) := by
            have h1 : ∑ i : Fin k, ((f i).val + i.val + 1) =
                ∑ i : Fin k, (f i).val + ∑ i : Fin k, (i.val + 1) := by
              simp only [sum_add_distrib]
              ring
            omega
        _ = S.sum id - ∑ i ∈ range k, (i + 1) := by rw [hSsum, htri]
  · -- Case k > n: both sides are 0
    push Not at hkn
    rw [qBinomial_gt q n k hkn, kSubsetsOfIcc_empty_of_gt n k hkn, sum_empty]

/-- The q-analog addition formula: [a+b]_q = [a]_q + q^a * [b]_q -/
private theorem qNat_add (q : R) (a b : ℕ) :
    qNat q (a + b) = qNat q a + q ^ a * qNat q b := by
  induction b with
  | zero => simp [qNat]
  | succ b ih =>
    simp only [qNat, sum_range_succ] at ih ⊢
    rw [← Nat.add_assoc]
    simp only [sum_range_succ]
    rw [ih]
    ring

/-- Splitting formula: [n+1]_q = [k+1]_q + q^(k+1) * [n-k]_q when k ≤ n -/
private theorem qNat_split' (q : R) (n k : ℕ) (hk : k ≤ n) :
    qNat q (n + 1) = qNat q (k + 1) + q ^ (k + 1) * qNat q (n - k) := by
  have h : n + 1 = (k + 1) + (n - k) := by omega
  conv_lhs => rw [h]
  rw [qNat_add]

/-- Key identity for the product formula proof -/
private theorem prod_qNat_ratio_identity (q : R) (n k : ℕ) (hk : k ≤ n) :
    (∏ i ∈ range k, qNat q (n - i)) * qNat q (n + 1) =
    (∏ i ∈ range k, qNat q (n + 1 - i)) * qNat q (n + 1 - k) := by
  induction k with
  | zero =>
    simp only [range_zero, prod_empty, one_mul, Nat.sub_zero]
  | succ k ih =>
    have hk' : k ≤ n := by omega
    rw [prod_range_succ, prod_range_succ]
    have heq : n + 1 - (k + 1) = n - k := by omega
    rw [heq]
    calc (∏ i ∈ range k, qNat q (n - i)) * qNat q (n - k) * qNat q (n + 1)
        = ((∏ i ∈ range k, qNat q (n - i)) * qNat q (n + 1)) * qNat q (n - k) := by ring
      _ = ((∏ i ∈ range k, qNat q (n + 1 - i)) * qNat q (n + 1 - k)) * qNat q (n - k) := by rw [ih hk']
      _ = (∏ i ∈ range k, qNat q (n + 1 - i)) * qNat q (n + 1 - k) * qNat q (n - k) := by ring

/-- Telescoping identity for products of q-analogs -/
private theorem prod_qNat_telescope_eq (q : R) (n : ℕ) :
    (∏ i ∈ range n, qNat q (n - i)) * qNat q (n + 1) = ∏ i ∈ range n, qNat q (n + 1 - i) := by
  have h := prod_qNat_ratio_identity q n n (le_refl n)
  have h1 : n + 1 - n = 1 := by omega
  rw [h1] at h
  rw [qNat_one, mul_one] at h
  exact h

/-- Index reversal for products of q-analogs -/
private theorem prod_qNat_reverse (q : R) (n : ℕ) :
    ∏ i ∈ range n, qNat q (i + 1) = ∏ i ∈ range n, qNat q (n - i) := by
  cases n with
  | zero => simp
  | succ n =>
    apply prod_bij' (fun i _ => n - i) (fun i _ => n - i)
    · intro i hi
      simp only [mem_range] at hi ⊢
      omega
    · intro i hi
      simp only [mem_range] at hi ⊢
      omega
    · intro i hi
      simp only [mem_range] at hi
      have : n - (n - i) = i := Nat.sub_sub_self (Nat.le_of_lt_succ hi)
      simp only [this]
    · intro i hi
      simp only [mem_range] at hi
      have : n - (n - i) = i := Nat.sub_sub_self (Nat.le_of_lt_succ hi)
      simp only [this]
    · intro i hi
      simp only [mem_range] at hi
      congr 1
      omega

/-- The q-binomial coefficient satisfies the product formula over a field:
    [n choose k]_q = ∏_{i=0}^{k-1} [n-i]_q / [i+1]_q

    This is equivalent to the recursive definition when q is not a root of unity. -/
theorem qBinomial_eq_prod_div {F : Type*} [Field F] (q : F) (n k : ℕ) (hk : k ≤ n)
    (hq : ∀ i : ℕ, i < k → qNat q (i + 1) ≠ 0) :
    qBinomial q n k = ∏ i ∈ range k, qNat q (n - i) / qNat q (i + 1) := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ m ih =>
    cases m with
    | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simp [qBinomial_zero_right]
    | succ n =>
      cases k with
      | zero =>
        simp [qBinomial_zero_right]
      | succ k =>
        simp only [qBinomial]
        rw [prod_range_succ]
        have hkn : k ≤ n := by omega
        have hq' : ∀ i < k, qNat q (i + 1) ≠ 0 := fun i hi => hq i (Nat.lt_trans hi (Nat.lt_succ_self k))
        have ih_k := ih n (Nat.lt_succ_self n) k hkn hq'
        by_cases hk1n : k + 1 ≤ n
        · have ih_k1 := ih n (Nat.lt_succ_self n) (k + 1) hk1n hq
          rw [prod_range_succ] at ih_k1
          rw [ih_k, ih_k1]
          have hk1 : qNat q (k + 1) ≠ 0 := hq k (Nat.lt_succ_self k)
          have hsplit : qNat q (n + 1) = qNat q (k + 1) + q ^ (k + 1) * qNat q (n - k) :=
            qNat_split' q n k hkn
          have hn1k : n + 1 - k = n - k + 1 := by omega
          rw [hn1k]
          have hprod_denom_ne : ∏ i ∈ range k, qNat q (i + 1) ≠ 0 := by
            apply prod_ne_zero_iff.mpr
            intro i hi
            simp only [mem_range] at hi
            exact hq' i hi
          rw [prod_div_distrib, prod_div_distrib]
          field_simp [hk1, hprod_denom_ne]
          have hident := prod_qNat_ratio_identity q n k hkn
          have hn1k' : n + 1 - k = n - k + 1 := by omega
          rw [hn1k'] at hident
          rw [← hsplit, hident]
        · push Not at hk1n
          have hkn_eq : k = n := by omega
          rw [hkn_eq]
          rw [qBinomial_gt q n (n + 1) (Nat.lt_succ_self n), mul_zero, add_zero]
          rw [qBinomial_self]
          have h1 : n + 1 - n = 1 := by omega
          rw [h1]
          rw [prod_div_distrib]
          have hprod_denom_ne' : ∏ i ∈ range n, qNat q (i + 1) ≠ 0 := by
            apply prod_ne_zero_iff.mpr
            intro i hi
            simp only [mem_range] at hi
            have : i < k := by omega
            exact hq' i this
          have htel := prod_qNat_telescope_eq q n
          field_simp [hprod_denom_ne']
          have hn1_ne : qNat q (n + 1) ≠ 0 := by
            cases n with
            | zero => simp
            | succ m =>
              have : m + 1 < k + 1 := by omega
              exact hq (m + 1) this
          rw [← htel]
          field_simp [hn1_ne]
          rw [prod_qNat_reverse q n]
          simp [qNat_one]

end QAnalogs

/-!
## Combinatorial Definition of q-Binomial Coefficients (Definition def.pars.qbinom.qbinom)

This section formalizes Definition 4.3.2 from the textbook, which defines the q-binomial
coefficient (Gaussian binomial coefficient) as a sum over partitions:

**(a)** The q-binomial coefficient `[n choose k]_q` is the polynomial
  `∑_{λ} q^|λ|`
where λ ranges over all partitions with largest part ≤ n-k and length ≤ k.

**(b)** For any ring element `a`, the evaluation `[n choose k]_a` is obtained by
substituting `a` for `q` in the polynomial `[n choose k]_q`.

### Key Properties

* When k > n, the q-binomial is 0 (empty sum since n - k < 0).
* `[n choose 0]_q = [n choose n]_q = 1` (only the empty partition qualifies).
* When a = 1, we recover the ordinary binomial coefficient: `[n choose k]_1 = C(n,k)`.
-/

section CombinatoricDefinition

/-- A partition has largest part ≤ m if all parts are ≤ m.
    This is used in the combinatorial definition of q-binomial coefficients. -/
def partitionLargestPartLeq {n : ℕ} (p : Nat.Partition n) (m : ℕ) : Prop :=
  ∀ i ∈ p.parts, i ≤ m

/-- A partition has length ≤ k if it has at most k parts.
    This is used in the combinatorial definition of q-binomial coefficients. -/
def partitionLengthLeq {n : ℕ} (p : Nat.Partition n) (k : ℕ) : Prop :=
  p.parts.card ≤ k

instance instDecidablePartitionLargestPartLeq {n m : ℕ} (p : Nat.Partition n) :
    Decidable (partitionLargestPartLeq p m) :=
  inferInstanceAs (Decidable (∀ i ∈ p.parts, i ≤ m))

instance instDecidablePartitionLengthLeq {n k : ℕ} (p : Nat.Partition n) :
    Decidable (partitionLengthLeq p k) :=
  inferInstanceAs (Decidable (p.parts.card ≤ k))

/-- The set of partitions of a given size that fit in a k × m box
    (i.e., have length ≤ k and largest part ≤ m).

    For the q-binomial `[n choose k]_q`, we use m = n - k.

    **Argument order:** `(size k m : ℕ)` where:
    - `size` is the partition size
    - `k` is the maximum number of parts (length ≤ k)
    - `m` is the maximum part size (largest part ≤ m)

    This matches the convention in `AlgebraicCombinatorics.partitionsInBox` from `QBinomialBasic.lean`. -/
def partitionsInBox (size k m : ℕ) : Finset (Nat.Partition size) :=
  (Finset.univ : Finset (Nat.Partition size)).filter
    (fun p => partitionLengthLeq p k ∧ partitionLargestPartLeq p m)

/-- The count of partitions of a given size that fit in a k × m box. -/
def countPartitionsInBox (size k m : ℕ) : ℕ := (partitionsInBox size k m).card

/-- Partitions with exactly k parts (not just at most k parts), fitting in a box with largest part ≤ m.
    Used in the q-Pascal identity proof to split partitions by exact number of parts. -/
def partitionsInBoxExact (size k m : ℕ) : Finset (Nat.Partition size) :=
  (Finset.univ : Finset (Nat.Partition size)).filter
    (fun p => p.parts.card = k ∧ partitionLargestPartLeq p m)

instance instDecidablePartitionsInBoxExact {size k m : ℕ} (p : Nat.Partition size) :
    Decidable (p.parts.card = k ∧ partitionLargestPartLeq p m) :=
  inferInstanceAs (Decidable (p.parts.card = k ∧ (∀ i ∈ p.parts, i ≤ m)))

/-- Helper: sum of a multiset is ≥ its cardinality when all elements are ≥ 1. -/
private lemma multiset_sum_ge_card {m : Multiset ℕ} (h : ∀ x ∈ m, x ≥ 1) : m.sum ≥ m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.sum_cons, Multiset.card_cons]
    have ha : a ≥ 1 := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≥ 1 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    specialize ih hs
    omega

/-- Helper: sum of (x - 1) over a multiset equals sum - card when all elements are ≥ 1. -/
private lemma multiset_sum_sub_one (m : Multiset ℕ) (h : ∀ x ∈ m, x ≥ 1) :
    (m.map (· - 1)).sum = m.sum - m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha : a ≥ 1 := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≥ 1 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have ihs := ih hs
    have hsum_ge : s.sum ≥ s.card := multiset_sum_ge_card hs
    omega

set_option backward.isDefEq.respectTransparency false in
/-- Partitions in a (k+1) × m box split into those with ≤ k parts and those with exactly k+1 parts. -/
private lemma partitionsInBox_succ_split (size k m : ℕ) :
    partitionsInBox size (k + 1) m =
    partitionsInBox size k m ∪ partitionsInBoxExact size (k + 1) m := by
  ext p
  simp only [partitionsInBox, partitionsInBoxExact, mem_filter, mem_univ, true_and,
    partitionLargestPartLeq, partitionLengthLeq, mem_union]
  constructor
  · intro ⟨hlen, hlp⟩
    by_cases hcard : p.parts.card ≤ k
    · left; exact ⟨hcard, hlp⟩
    · right
      push Not at hcard
      exact ⟨by omega, hlp⟩
  · intro h
    rcases h with ⟨hlen, hlp⟩ | ⟨hcard, hlp⟩
    · exact ⟨by omega, hlp⟩
    · exact ⟨by omega, hlp⟩

set_option backward.isDefEq.respectTransparency false in
/-- The two sets in the partition split are disjoint. -/
private lemma partitionsInBox_disjoint (size k m : ℕ) :
    Disjoint (partitionsInBox size k m) (partitionsInBoxExact size (k + 1) m) := by
  rw [Finset.disjoint_iff_ne]
  intro p hp q hq
  simp only [partitionsInBox, partitionsInBoxExact, mem_filter, mem_univ, true_and,
    partitionLargestPartLeq, partitionLengthLeq] at hp hq
  intro heq
  rw [heq] at hp
  omega

/-- Counting identity: partitions in (k+1) × m box = partitions in k × m box + exact (k+1) parts. -/
private lemma countPartitionsInBox_succ_eq (size k m : ℕ) :
    countPartitionsInBox size (k + 1) m =
    countPartitionsInBox size k m + (partitionsInBoxExact size (k + 1) m).card := by
  unfold countPartitionsInBox
  rw [partitionsInBox_succ_split]
  rw [Finset.card_union_of_disjoint (partitionsInBox_disjoint size k m)]

/-- If size > k * m, then countPartitionsInBox is 0 (no partition fits in the box). -/
private lemma countPartitionsInBox_zero_of_gt (size k m : ℕ) (h : size > k * m) :
    countPartitionsInBox size k m = 0 := by
  unfold countPartitionsInBox partitionsInBox
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _
  simp only [partitionLargestPartLeq, partitionLengthLeq, not_and]
  intro hlen hlp
  have hsum : size = p.parts.sum := p.parts_sum.symm
  have hbound : p.parts.sum ≤ p.parts.card * m := by
    have haux : ∀ (ms : Multiset ℕ), (∀ x ∈ ms, x ≤ m) → ms.sum ≤ ms.card * m := by
      intro ms hms
      induction ms using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        simp only [Multiset.sum_cons, Multiset.card_cons]
        have ha : a ≤ m := hms a (Multiset.mem_cons_self a s)
        have hs : ∀ x ∈ s, x ≤ m := fun x hx => hms x (Multiset.mem_cons_of_mem hx)
        have ihs : s.sum ≤ s.card * m := ih hs
        calc a + s.sum ≤ m + s.card * m := by linarith
          _ = (s.card + 1) * m := by ring
    exact haux p.parts hlp
  have hbound2 : p.parts.card * m ≤ k * m := Nat.mul_le_mul_right m hlen
  linarith

/-- When the size is less than k+1, there are no partitions with exactly k+1 parts. -/
private lemma partitionsInBoxExact_empty_of_lt (s k : ℕ) (m : ℕ) (hs : s < k + 1) :
    partitionsInBoxExact s (k + 1) m = ∅ := by
  ext p
  simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and]
  constructor
  · intro ⟨hcard, _⟩
    have hpos : ∀ x ∈ p.parts, x ≥ 1 := fun x hx => p.parts_pos hx
    have hsum_ge : p.parts.sum ≥ p.parts.card := multiset_sum_ge_card hpos
    rw [hcard] at hsum_ge
    have hsum_eq : p.parts.sum = s := p.parts_sum
    omega
  · intro h
    simp at h

/-- Forward bijection for q-Pascal: subtract 1 from each part of a partition with exactly k+1 parts.
    Uses `Nat.Partition.ofSums` to filter out zeros. -/
private noncomputable def subtractOnePartition (s k m : ℕ) (p : Nat.Partition s)
    (hp : p ∈ partitionsInBoxExact s (k + 1) m) : Nat.Partition (s - (k + 1)) := by
  have hparts : p.parts.card = k + 1 := by
    simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and] at hp
    exact hp.1
  have hpos : ∀ x ∈ p.parts, x ≥ 1 := fun x hx => p.parts_pos hx
  let newParts := p.parts.map (· - 1)
  have hsum : newParts.sum = s - (k + 1) := by
    simp only [newParts]
    rw [multiset_sum_sub_one p.parts hpos, p.parts_sum, hparts]
  exact Nat.Partition.ofSums (s - (k + 1)) newParts hsum

set_option backward.isDefEq.respectTransparency false in
/-- The forward bijection lands in the target box. -/
private lemma subtractOnePartition_mem (s k m : ℕ) (p : Nat.Partition s)
    (hp : p ∈ partitionsInBoxExact s (k + 1) m) (hm : m ≥ 1) :
    subtractOnePartition s k m p hp ∈ partitionsInBox (s - (k + 1)) (k + 1) (m - 1) := by
  simp only [partitionsInBox, mem_filter, mem_univ, true_and]
  constructor
  · simp only [subtractOnePartition, partitionLengthLeq]
    rw [Nat.Partition.ofSums_parts]
    have h1 : (Multiset.filter (· ≠ 0) (Multiset.map (· - 1) p.parts)).card ≤
              (Multiset.map (· - 1) p.parts).card :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    have h2 : (Multiset.map (· - 1) p.parts).card = p.parts.card := Multiset.card_map _ _
    have h3 : p.parts.card = k + 1 := by
      simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and] at hp
      exact hp.1
    omega
  · intro i hi
    simp only [subtractOnePartition] at hi
    rw [Nat.Partition.ofSums_parts] at hi
    simp only [Multiset.mem_filter] at hi
    obtain ⟨hi_mem, _⟩ := hi
    simp only [Multiset.mem_map] at hi_mem
    obtain ⟨j, hj_mem, hj_eq⟩ := hi_mem
    have hj_le : j ≤ m := by
      simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and,
        partitionLargestPartLeq] at hp
      exact hp.2 j hj_mem
    omega

set_option backward.isDefEq.respectTransparency false in
/-- Inverse bijection for q-Pascal: add 1 to each part and pad with 1s to get exactly k+1 parts. -/
private noncomputable def addOnePartition (t k m : ℕ) (q : Nat.Partition t)
    (hq : q ∈ partitionsInBox t (k + 1) (m - 1)) : Nat.Partition (t + (k + 1)) := by
  have hlen : q.parts.card ≤ k + 1 := by
    simp only [partitionsInBox, mem_filter, mem_univ, true_and, partitionLengthLeq] at hq
    exact hq.1
  let addedParts := q.parts.map (· + 1)
  let extraOnes := Multiset.replicate (k + 1 - q.parts.card) 1
  let newParts := addedParts + extraOnes
  have hsum : newParts.sum = t + (k + 1) := by
    simp only [newParts, addedParts, extraOnes]
    simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
    have h1 : (q.parts.map (· + 1)).sum = q.parts.sum + q.parts.card := by
      induction q.parts using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
        omega
    rw [h1, q.parts_sum]
    omega
  have hpos : ∀ i ∈ newParts, 0 < i := by
    intro i hi
    simp only [newParts, addedParts, extraOnes, Multiset.mem_add] at hi
    rcases hi with hi_add | hi_extra
    · simp only [Multiset.mem_map] at hi_add
      obtain ⟨j, _, hj_eq⟩ := hi_add
      omega
    · simp only [Multiset.mem_replicate] at hi_extra
      omega
  exact ⟨newParts, @hpos, hsum⟩

set_option backward.isDefEq.respectTransparency false in
/-- The inverse bijection lands in the target set. -/
private lemma addOnePartition_mem (t k m : ℕ) (q : Nat.Partition t)
    (hq : q ∈ partitionsInBox t (k + 1) (m - 1)) (hm : m ≥ 1) :
    addOnePartition t k m q hq ∈ partitionsInBoxExact (t + (k + 1)) (k + 1) m := by
  simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and]
  constructor
  · simp only [addOnePartition]
    have hlen : q.parts.card ≤ k + 1 := by
      simp only [partitionsInBox, mem_filter, mem_univ, true_and, partitionLengthLeq] at hq
      exact hq.1
    simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate]
    have h : k + 1 - q.parts.card + q.parts.card = k + 1 := Nat.sub_add_cancel hlen
    omega
  · intro i hi
    simp only [addOnePartition] at hi
    simp only [Multiset.mem_add] at hi
    rcases hi with hi_add | hi_rep
    · simp only [Multiset.mem_map] at hi_add
      obtain ⟨j, hj_mem, hj_eq⟩ := hi_add
      have hj_le : j ≤ m - 1 := by
        simp only [partitionsInBox, mem_filter, mem_univ, true_and,
          partitionLargestPartLeq] at hq
        exact hq.2 j hj_mem
      omega
    · simp only [Multiset.mem_replicate] at hi_rep
      obtain ⟨_, hi_eq⟩ := hi_rep
      rw [hi_eq]
      exact hm

/-- Key lemma: subtractOnePartition_parts -/
private lemma subtractOnePartition_parts (s k m : ℕ) (p : Nat.Partition s)
    (hp : p ∈ partitionsInBoxExact s (k + 1) m) :
    (subtractOnePartition s k m p hp).parts = Multiset.filter (· ≠ 0) (Multiset.map (· - 1) p.parts) := by
  simp only [subtractOnePartition]
  exact Nat.Partition.ofSums_parts _ _ _

/-- addOnePartition parts -/
private lemma addOnePartition_parts (t k m : ℕ) (q : Nat.Partition t)
    (hq : q ∈ partitionsInBox t (k + 1) (m - 1)) :
    (addOnePartition t k m q hq).parts =
    Multiset.map (· + 1) q.parts + Multiset.replicate (k + 1 - q.parts.card) 1 := by
  simp only [addOnePartition]

/-- Helper lemma: filtered card ≤ original card -/
private lemma filter_card_le (m : Multiset ℕ) :
    (Multiset.filter (· ≠ 0) (Multiset.map (· - 1) m)).card ≤ m.card := by
  calc (Multiset.filter (· ≠ 0) (Multiset.map (· - 1) m)).card
      ≤ (Multiset.map (· - 1) m).card := Multiset.card_le_card (Multiset.filter_le _ _)
    _ = m.card := Multiset.card_map _ _

/-- Helper lemma: recover original multiset from filtered version -/
private lemma recover_from_filtered (m : Multiset ℕ) (hpos : ∀ x ∈ m, x ≥ 1) :
    Multiset.map (· + 1) (Multiset.filter (· ≠ 0) (Multiset.map (· - 1) m)) +
    Multiset.replicate (m.count 1) 1 = m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≥ 1 := hpos a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≥ 1 := fun x hx => hpos x (Multiset.mem_cons_of_mem hx)
    specialize ih hs
    simp only [Multiset.map_cons, Multiset.count_cons]
    by_cases ha1 : a = 1
    · subst ha1
      simp only [Nat.sub_self, ne_eq, ↓reduceIte, Multiset.replicate_succ, Multiset.add_cons]
      have hfilter : Multiset.filter (· ≠ 0) (0 ::ₘ Multiset.map (· - 1) s) =
                     Multiset.filter (· ≠ 0) (Multiset.map (· - 1) s) := by
        rw [Multiset.filter_cons_of_neg]
        decide
      rw [hfilter, ih]
    · have ha_pos : a - 1 ≠ 0 := by omega
      have ha_ne1 : ¬(1 = a) := by omega
      simp only [ne_eq, ha_ne1, ↓reduceIte, add_zero]
      have hfilter : Multiset.filter (· ≠ 0) ((a - 1) ::ₘ Multiset.map (· - 1) s) =
                     (a - 1) ::ₘ Multiset.filter (· ≠ 0) (Multiset.map (· - 1) s) := by
        rw [Multiset.filter_cons_of_pos]
        exact ha_pos
      rw [hfilter]
      simp only [Multiset.map_cons, Multiset.cons_add]
      rw [ih]
      congr 1
      omega

/-- Helper lemma: count of 1s from card -/
private lemma count_one_from_card (m : Multiset ℕ) (hpos : ∀ x ∈ m, x ≥ 1) :
    m.count 1 = m.card - (Multiset.filter (· ≠ 0) (Multiset.map (· - 1) m)).card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≥ 1 := hpos a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≥ 1 := fun x hx => hpos x (Multiset.mem_cons_of_mem hx)
    specialize ih hs
    simp only [Multiset.count_cons, Multiset.map_cons, Multiset.card_cons]
    by_cases ha1 : a = 1
    · subst ha1
      simp only [↓reduceIte, Nat.sub_self, ne_eq]
      have hfilter : Multiset.filter (· ≠ 0) (0 ::ₘ Multiset.map (· - 1) s) =
                     Multiset.filter (· ≠ 0) (Multiset.map (· - 1) s) := by
        rw [Multiset.filter_cons_of_neg]
        decide
      rw [hfilter]
      have hle : (Multiset.filter (· ≠ 0) (Multiset.map (· - 1) s)).card ≤ s.card := filter_card_le s
      omega
    · have ha_pos : a - 1 ≠ 0 := by omega
      have ha_ne1 : ¬(1 = a) := by omega
      simp only [ha_ne1, ↓reduceIte, add_zero, ne_eq]
      have hfilter : Multiset.filter (· ≠ 0) ((a - 1) ::ₘ Multiset.map (· - 1) s) =
                     (a - 1) ::ₘ Multiset.filter (· ≠ 0) (Multiset.map (· - 1) s) := by
        rw [Multiset.filter_cons_of_pos]
        exact ha_pos
      rw [hfilter, Multiset.card_cons]
      have hle : (Multiset.filter (· ≠ 0) (Multiset.map (· - 1) s)).card ≤ s.card := filter_card_le s
      omega

/-- Helper lemma: injectivity of filter map sub -/
private lemma filter_map_sub_injective (m₁ m₂ : Multiset ℕ)
    (hpos₁ : ∀ x ∈ m₁, x ≥ 1) (hpos₂ : ∀ x ∈ m₂, x ≥ 1)
    (hcard : m₁.card = m₂.card)
    (heq : Multiset.filter (· ≠ 0) (Multiset.map (· - 1) m₁) =
           Multiset.filter (· ≠ 0) (Multiset.map (· - 1) m₂)) :
    m₁ = m₂ := by
  have hcount : m₁.count 1 = m₂.count 1 := by
    rw [count_one_from_card m₁ hpos₁, count_one_from_card m₂ hpos₂, heq, hcard]
  calc m₁ = Multiset.map (· + 1) (Multiset.filter (· ≠ 0) (Multiset.map (· - 1) m₁)) +
           Multiset.replicate (m₁.count 1) 1 := (recover_from_filtered m₁ hpos₁).symm
       _ = Multiset.map (· + 1) (Multiset.filter (· ≠ 0) (Multiset.map (· - 1) m₂)) +
           Multiset.replicate (m₂.count 1) 1 := by rw [heq, hcount]
       _ = m₂ := recover_from_filtered m₂ hpos₂

/-- Helper lemma: subtract after add -/
private lemma subtract_after_add (m : Multiset ℕ) (n : ℕ) (hm : ∀ x ∈ m, x ≠ 0) :
    Multiset.filter (· ≠ 0) (Multiset.map (· - 1) (Multiset.map (· + 1) m + Multiset.replicate n 1)) = m := by
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, Multiset.map_replicate,
    Nat.add_sub_cancel, Nat.sub_self, Multiset.filter_add]
  simp only [Multiset.map_id']
  have h1 : Multiset.filter (· ≠ 0) (Multiset.replicate n 0) = 0 := by
    ext x
    simp only [Multiset.count_filter, Multiset.count_replicate, ne_eq, Multiset.count_zero]
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx]
      intro h
      exact (hx h.symm).elim
  rw [h1, add_zero]
  rw [Multiset.filter_eq_self]
  exact hm

set_option backward.isDefEq.respectTransparency false in
/-- Key cardinality equality: partitions with exactly k+1 parts in (k+1) × m box biject with
    partitions with at most k+1 parts in (k+1) × (m-1) box, via the "subtract 1 from each part"
    bijection. This is the combinatorial heart of the q-Pascal identity.

    The bijection:
    - Forward: subtract 1 from each part, filter zeros (using `ofSums`)
    - Inverse: add 1 to each part, pad with 1s to get exactly k+1 parts -/
lemma partitionsInBoxExact_card_eq (s k m : ℕ) (hm : m ≥ 1) (hs : s ≥ k + 1) :
    (partitionsInBoxExact s (k + 1) m).card = countPartitionsInBox (s - (k + 1)) (k + 1) (m - 1) := by
  unfold countPartitionsInBox
  have h_add_sub : s - (k + 1) + (k + 1) = s := Nat.sub_add_cancel hs
  apply Finset.card_bij (fun p hp => subtractOnePartition s k m p hp)
  · -- subtractOnePartition lands in the target
    intro p hp
    simp only [partitionsInBox, mem_filter, mem_univ, true_and]
    constructor
    · simp only [subtractOnePartition, partitionLengthLeq]
      rw [Nat.Partition.ofSums_parts]
      have h1 : (Multiset.filter (· ≠ 0) (Multiset.map (· - 1) p.parts)).card ≤
                (Multiset.map (· - 1) p.parts).card :=
        Multiset.card_le_card (Multiset.filter_le _ _)
      have h2 : (Multiset.map (· - 1) p.parts).card = p.parts.card := Multiset.card_map _ _
      have h3 : p.parts.card = k + 1 := by
        simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and] at hp
        exact hp.1
      omega
    · intro i hi
      simp only [subtractOnePartition] at hi
      rw [Nat.Partition.ofSums_parts] at hi
      simp only [Multiset.mem_filter] at hi
      obtain ⟨hi_mem, _⟩ := hi
      simp only [Multiset.mem_map] at hi_mem
      obtain ⟨j, hj_mem, hj_eq⟩ := hi_mem
      have hj_le : j ≤ m := by
        simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and,
          partitionLargestPartLeq] at hp
        exact hp.2 j hj_mem
      omega
  · -- subtractOnePartition is injective
    intro p₁ hp₁ p₂ hp₂ heq
    rw [Nat.Partition.ext_iff] at heq ⊢
    rw [subtractOnePartition_parts, subtractOnePartition_parts] at heq
    have hcard₁ : p₁.parts.card = k + 1 := by
      simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and] at hp₁
      exact hp₁.1
    have hcard₂ : p₂.parts.card = k + 1 := by
      simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and] at hp₂
      exact hp₂.1
    have hpos₁ : ∀ x ∈ p₁.parts, x ≥ 1 := fun x hx => p₁.parts_pos hx
    have hpos₂ : ∀ x ∈ p₂.parts, x ≥ 1 := fun x hx => p₂.parts_pos hx
    exact filter_map_sub_injective p₁.parts p₂.parts hpos₁ hpos₂ (by omega) heq
  · -- subtractOnePartition is surjective
    intro q hq
    let p' := addOnePartition (s - (k + 1)) k m q hq
    have hp'_mem := addOnePartition_mem (s - (k + 1)) k m q hq hm
    let p : Nat.Partition s := ⟨p'.parts, p'.parts_pos, by rw [p'.parts_sum]; exact h_add_sub⟩
    have hp : p ∈ partitionsInBoxExact s (k + 1) m := by
      simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and]
      simp only [p]
      simp only [partitionsInBoxExact, mem_filter, mem_univ, true_and] at hp'_mem
      exact hp'_mem
    use p, hp
    rw [Nat.Partition.ext_iff]
    rw [subtractOnePartition_parts]
    simp only [p]
    rw [addOnePartition_parts]
    have hnonzero : ∀ x ∈ q.parts, x ≠ 0 := fun x hx => Nat.pos_iff_ne_zero.mp (q.parts_pos hx)
    exact subtract_after_add q.parts (k + 1 - q.parts.card) hnonzero

-- Helper lemma: the empty partition (of 0) satisfies any box constraint
private lemma empty_partition_satisfies_box (n k : ℕ) :
    ∀ (p : Nat.Partition 0), (∀ i ∈ p.parts, i ≤ n) ∧ p.parts.card ≤ k := by
  intro p
  constructor
  · intro i hi
    have hp : p.parts = 0 := Nat.Partition.partition_zero_parts p
    rw [hp] at hi
    simp at hi
  · have hp : p.parts = 0 := Nat.Partition.partition_zero_parts p
    simp only [hp, Multiset.card_zero, Nat.zero_le]

/-- The q-binomial coefficient as a polynomial in ℤ[q].
    (Definition def.pars.qbinom.qbinom (a))

    `[n choose k]_q = ∑_{λ} q^|λ|`

    where λ ranges over all partitions with largest part ≤ n-k and length ≤ k.

    This is a polynomial (not just a formal power series) because there are
    finitely many such partitions - they all fit in a k × (n-k) box, so their
    size is at most k · (n-k).

    When k > n, this is 0 (the empty sum, since n - k < 0 means no partitions qualify). -/
noncomputable def qBinomialPolyDef (n k : ℕ) : Polynomial ℤ :=
  if k ≤ n then
    ∑ size ∈ range (k * (n - k) + 1),
      (countPartitionsInBox size k (n - k)) • (Polynomial.X : Polynomial ℤ) ^ size
  else 0

/-- When k > n, the combinatorial q-binomial coefficient is 0. -/
@[simp]
theorem qBinomialPolyDef_of_gt (n k : ℕ) (h : k > n) : qBinomialPolyDef n k = 0 := by
  simp only [qBinomialPolyDef, show ¬(k ≤ n) by omega, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
/-- `[n choose 0]_q = 1` for all n. -/
@[simp]
theorem qBinomialPolyDef_zero_right (n : ℕ) : qBinomialPolyDef n 0 = 1 := by
  simp only [qBinomialPolyDef, Nat.zero_le, ↓reduceIte, zero_mul, zero_add, range_one,
    sum_singleton, countPartitionsInBox, partitionsInBox, Nat.sub_zero,
    partitionLargestPartLeq, partitionLengthLeq]
  have h : (filter (fun p => p.parts.card ≤ 0 ∧ (∀ i ∈ p.parts, i ≤ n))
      (univ : Finset (Nat.Partition 0))).card = 1 := by
    have h1 : filter (fun p => p.parts.card ≤ 0 ∧ (∀ i ∈ p.parts, i ≤ n))
        (univ : Finset (Nat.Partition 0)) = univ := by
      ext p
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro _; trivial
      · intro _
        have hbox := empty_partition_satisfies_box n 0 p
        exact ⟨hbox.2, hbox.1⟩
    rw [h1]
    rfl
  rw [h]
  simp only [one_smul, pow_zero]

/-- `[n choose n]_q = 1` for all n. -/
@[simp]
theorem qBinomialPolyDef_self (n : ℕ) : qBinomialPolyDef n n = 1 := by
  simp only [qBinomialPolyDef, le_refl, ↓reduceIte, Nat.sub_self, mul_zero, zero_add, range_one,
    sum_singleton, countPartitionsInBox, partitionsInBox, partitionLargestPartLeq, partitionLengthLeq]
  have h : (filter (fun p => p.parts.card ≤ n ∧ (∀ i ∈ p.parts, i ≤ 0))
      (univ : Finset (Nat.Partition 0))).card = 1 := by
    have h1 : filter (fun p => p.parts.card ≤ n ∧ (∀ i ∈ p.parts, i ≤ 0))
        (univ : Finset (Nat.Partition 0)) = univ := by
      ext p
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro _; trivial
      · intro _
        have hbox := empty_partition_satisfies_box 0 n p
        exact ⟨hbox.2, hbox.1⟩
    rw [h1]
    rfl
  rw [h]
  simp only [one_smul, pow_zero]

variable {R : Type*} [CommRing R]

/-- The q-binomial coefficient evaluated at a ring element.
    (Definition def.pars.qbinom.qbinom (b))

    `[n choose k]_a = ∑_{λ} a^|λ|`

    where λ ranges over all partitions with largest part ≤ n-k and length ≤ k.

    This is the result of substituting `a` for `q` in the polynomial `[n choose k]_q`. -/
noncomputable def qBinomialEval (n k : ℕ) (a : R) : R :=
  (qBinomialPolyDef n k).eval₂ (Int.castRingHom R) a

/-- Alternative definition: directly sum over partitions. -/
def qBinomialEvalDirect (n k : ℕ) (a : R) : R :=
  if k ≤ n then
    ∑ size ∈ range (k * (n - k) + 1),
      (countPartitionsInBox size k (n - k)) • a ^ size
  else 0

/-- The two definitions of qBinomialEval agree. -/
theorem qBinomialEval_eq_direct (n k : ℕ) (a : R) :
    qBinomialEval n k a = qBinomialEvalDirect n k a := by
  simp only [qBinomialEval, qBinomialEvalDirect, qBinomialPolyDef]
  split_ifs with hk
  · rw [Polynomial.eval₂_finsetSum]
    congr 1
    ext size
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_natCast,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, nsmul_eq_mul]
  · simp only [eval₂_zero]

/-- When k > n, the evaluated q-binomial is 0. -/
@[simp]
theorem qBinomialEval_of_gt (n k : ℕ) (h : k > n) (a : R) : qBinomialEval n k a = 0 := by
  simp only [qBinomialEval, qBinomialPolyDef_of_gt n k h, eval₂_zero]

/-- `[n choose 0]_a = 1` for all n and a. -/
@[simp]
theorem qBinomialEval_zero_right (n : ℕ) (a : R) : qBinomialEval n 0 a = 1 := by
  simp only [qBinomialEval, qBinomialPolyDef_zero_right, eval₂_one]

/-- `[n choose n]_a = 1` for all n and a. -/
@[simp]
theorem qBinomialEval_self (n : ℕ) (a : R) : qBinomialEval n n a = 1 := by
  simp only [qBinomialEval, qBinomialPolyDef_self, eval₂_one]

/-- Helper lemma: extending a sum with zero terms doesn't change it. -/
private lemma sum_range_extend_zero {R : Type*} [AddCommMonoid R] (f : ℕ → R) (a b : ℕ) (hab : a ≤ b)
    (hzero : ∀ i, a ≤ i → i < b → f i = 0) :
    ∑ i ∈ range b, f i = ∑ i ∈ range a, f i := by
  have hsplit : range b = range a ∪ Finset.Ico a b := by
    ext x
    simp only [mem_union, mem_range, mem_Ico]
    omega
  rw [hsplit, sum_union (by simp [Finset.disjoint_iff_ne]; intro x hx y hy; omega)]
  have hzero_sum : ∑ x ∈ Finset.Ico a b, f x = 0 := by
    apply sum_eq_zero
    intro i hi
    simp only [mem_Ico] at hi
    exact hzero i hi.1 hi.2
  simp [hzero_sum]

set_option backward.isDefEq.respectTransparency false in
/-- The q-Pascal identity for qBinomialPolyDef (polynomial version).
    This is the combinatorial heart of the proof connecting the two definitions.

    The identity states:
    `[n+1 choose k+1]_q = [n choose k]_q + q^{k+1} · [n choose k+1]_q`

    Combinatorially, partitions in a (k+1) × (n-k) box split into two types:
    1. Those with length ≤ k (same as partitions in k × (n-k) box)
    2. Those with length = k+1, which biject with partitions in (k+1) × (n-k-1) box
       via "removing a column" (subtracting 1 from each of the k+1 parts),
       with size decreased by k+1 (hence the factor q^{k+1}). -/
theorem qBinomialPolyDef_pascal (n k : ℕ) (hk : k + 1 ≤ n + 1) :
    qBinomialPolyDef (n + 1) (k + 1) =
      qBinomialPolyDef n k + (Polynomial.X : Polynomial ℤ) ^ (k + 1) * qBinomialPolyDef n (k + 1) := by
  -- This requires establishing a bijection on partitions:
  -- Partitions of size s in (k+1) × (n-k) box biject with:
  -- - Partitions of size s in k × (n-k) box (those with length ≤ k)
  -- - Partitions of size s-(k+1) in (k+1) × (n-k-1) box (those with length = k+1)
  -- The bijection for the second case is "remove a column" (subtract 1 from each part).
  have hkn : k ≤ n := by omega
  -- Expand the definitions
  unfold qBinomialPolyDef
  simp only [hk, hkn, ↓reduceIte]
  -- Handle the case k + 1 ≤ n vs k + 1 > n (i.e., k = n)
  by_cases hk1n : k + 1 ≤ n
  · -- Case k + 1 ≤ n (so k < n): requires the full bijection argument
    simp only [hk1n, ↓reduceIte]
    -- Simplify the arithmetic in the range bounds
    have h1 : n + 1 - (k + 1) = n - k := by omega
    have h2 : n - (k + 1) = n - k - 1 := by omega
    rw [h1, h2]
    -- Use countPartitionsInBox_succ_eq to split the LHS
    conv_lhs =>
      congr
      · skip
      · ext size
        rw [countPartitionsInBox_succ_eq size k (n - k)]
    simp only [add_smul]
    rw [sum_add_distrib]
    -- Now we need to show:
    -- ∑ countPartitionsInBox size k (n-k) • X^size + ∑ (partitionsInBoxExact size (k+1) (n-k)).card • X^size
    -- = ∑ countPartitionsInBox size k (n-k) • X^size + X^(k+1) * ∑ countPartitionsInBox size (k+1) (n-k-1) • X^size
    congr 1
    · -- First sum equality: extend the range from k*(n-k) to (k+1)*(n-k)
      -- Extra terms have countPartitionsInBox = 0 because size exceeds box capacity
      rw [sum_range_extend_zero]
      · have h : k * (n - k) ≤ (k + 1) * (n - k) := Nat.mul_le_mul_right (n - k) (Nat.le_succ k)
        exact Nat.add_le_add_right h 1
      · intro i hi1 hi2
        have h : i > k * (n - k) := by linarith
        rw [countPartitionsInBox_zero_of_gt i k (n - k) h]
        simp
    · -- Second sum equality: use the bijection
      have h_nk_pos : n - k ≥ 1 := by omega
      have hbound : k + 1 ≤ (k + 1) * (n - k) + 1 := by
        calc k + 1 = (k + 1) * 1 := by ring
          _ ≤ (k + 1) * (n - k) := Nat.mul_le_mul_left (k + 1) h_nk_pos
          _ ≤ (k + 1) * (n - k) + 1 := Nat.le_succ _
      have hsplit : range ((k + 1) * (n - k) + 1) = range (k + 1) ∪ Finset.Ico (k + 1) ((k + 1) * (n - k) + 1) := by
        ext x
        simp only [mem_union, mem_range, mem_Ico]
        constructor
        · intro h
          by_cases hx : x < k + 1
          · left; exact hx
          · right; exact ⟨Nat.not_lt.mp hx, h⟩
        · intro h
          cases h with
          | inl h => exact Nat.lt_of_lt_of_le h hbound
          | inr h => exact h.2
      rw [hsplit, sum_union (by rw [Finset.disjoint_iff_ne]; intro x hx y hy; simp only [mem_range] at hx; simp only [mem_Ico] at hy; omega)]
      -- The first sum is 0 (no partitions with k+1 parts when size < k+1)
      have hzero_sum : ∑ x ∈ range (k + 1), (partitionsInBoxExact x (k + 1) (n - k)).card • (X : Polynomial ℤ) ^ x = 0 := by
        apply sum_eq_zero
        intro i hi
        simp only [mem_range] at hi
        rw [partitionsInBoxExact_empty_of_lt i k (n - k) hi]
        simp
      rw [hzero_sum, zero_add]
      -- Now use the bijection: partitionsInBoxExact_card_eq
      have hrange_upper : (k + 1) * (n - k) + 1 = (k + 1) * (n - k - 1) + 1 + (k + 1) := by
        have h2 : (k + 1) * (n - k) = (k + 1) * (n - k - 1) + (k + 1) := by
          conv_lhs => rw [show n - k = n - k - 1 + 1 by omega]
          ring
        linarith
      -- Rewrite LHS using the bijection
      have hbij : ∀ x ∈ Finset.Ico (k + 1) ((k + 1) * (n - k) + 1),
          (partitionsInBoxExact x (k + 1) (n - k)).card = countPartitionsInBox (x - (k + 1)) (k + 1) (n - k - 1) := by
        intro x hx
        simp only [mem_Ico] at hx
        exact partitionsInBoxExact_card_eq x k (n - k) h_nk_pos hx.1
      rw [Finset.sum_congr rfl (fun x hx => by rw [hbij x hx])]
      -- Now do the index shift
      rw [mul_sum, Finset.sum_Ico_eq_sum_range]
      have h_range_eq : (k + 1) * (n - k) + 1 - (k + 1) = (k + 1) * (n - k - 1) + 1 := by
        rw [hrange_upper]; omega
      rw [h_range_eq]
      congr 1
      ext t
      have h_simp : k + 1 + t - (k + 1) = t := by omega
      rw [h_simp]
      rw [pow_add]
      ring_nf
  · -- Case k + 1 > n, i.e., k = n: the second term on RHS is 0
    have h_not : ¬(k + 1 ≤ n) := hk1n
    simp only [h_not, ↓reduceIte, mul_zero, add_zero]
    -- When k = n, both sides reduce to sums over a single element (size 0)
    have hnk_zero : n - k = 0 := by omega
    have hn1k1 : n + 1 - (k + 1) = 0 := by omega
    simp only [hn1k1, hnk_zero, mul_zero, zero_add, range_one, sum_singleton, pow_zero]
    -- Both sides equal countPartitionsInBox 0 _ 0 • 1 = 1 • 1 = 1
    -- since the only partition of 0 is the empty partition, which fits in any box
    have h1 : countPartitionsInBox 0 (k + 1) 0 = 1 := by
      unfold countPartitionsInBox partitionsInBox partitionLargestPartLeq partitionLengthLeq
      have h : (filter (fun p : Nat.Partition 0 => p.parts.card ≤ k + 1 ∧ (∀ i ∈ p.parts, i ≤ 0))
          (univ : Finset (Nat.Partition 0))) = univ := by
        ext p
        simp only [mem_filter, mem_univ, true_and, iff_true]
        constructor
        · have hp : p.parts = 0 := Nat.Partition.partition_zero_parts p
          simp only [hp, Multiset.card_zero, Nat.zero_le]
        · intro i hi
          have hp : p.parts = 0 := Nat.Partition.partition_zero_parts p
          rw [hp] at hi; simp at hi
      rw [h]; rfl
    have h2 : countPartitionsInBox 0 k 0 = 1 := by
      unfold countPartitionsInBox partitionsInBox partitionLargestPartLeq partitionLengthLeq
      have h : (filter (fun p : Nat.Partition 0 => p.parts.card ≤ k ∧ (∀ i ∈ p.parts, i ≤ 0))
          (univ : Finset (Nat.Partition 0))) = univ := by
        ext p
        simp only [mem_filter, mem_univ, true_and, iff_true]
        constructor
        · have hp : p.parts = 0 := Nat.Partition.partition_zero_parts p
          simp only [hp, Multiset.card_zero, Nat.zero_le]
        · intro i hi
          have hp : p.parts = 0 := Nat.Partition.partition_zero_parts p
          rw [hp] at hi; simp at hi
      rw [h]; rfl
    rw [h1, h2]

/-- The q-Pascal identity for qBinomialEval (evaluated version).
    Follows directly from the polynomial version by evaluation. -/
private theorem qBinomialEval_pascal (n k : ℕ) (q : R) (hk : k + 1 ≤ n + 1) :
    qBinomialEval (n + 1) (k + 1) q = qBinomialEval n k q + q ^ (k + 1) * qBinomialEval n (k + 1) q := by
  simp only [qBinomialEval]
  rw [qBinomialPolyDef_pascal n k hk]
  simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X]

/-- The combinatorial definition agrees with the recursive definition.
    This connects Definition def.pars.qbinom.qbinom with the recurrence-based `qBinomial`.

    The proof shows that both definitions satisfy the same recurrence relation
    (q-Pascal's identity) and boundary conditions. -/
theorem qBinomialEval_eq_qBinomial (n k : ℕ) (q : R) :
    qBinomialEval n k q = qBinomial q n k := by
  -- Both definitions satisfy:
  -- 1. [n choose 0]_q = 1
  -- 2. [n choose k]_q = 0 when k > n
  -- 3. [n+1 choose k+1]_q = [n choose k]_q + q^{k+1} · [n choose k+1]_q
  -- The proof follows by induction on n and k.
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    -- Case analysis: k = 0, k > n, k = n, or 0 < k < n
    by_cases hk0 : k = 0
    · -- k = 0
      subst hk0
      simp [qBinomialEval_zero_right, qBinomial_zero_right]
    · by_cases hkn : k > n
      · -- k > n
        simp [qBinomialEval_of_gt n k hkn, qBinomial_gt q n k hkn]
      · by_cases hkeq : k = n
        · -- k = n
          subst hkeq
          simp [qBinomialEval_self, qBinomial_self]
        · -- 0 < k < n
          have hk_lt : k < n := by omega
          -- Write k = j + 1 for some j
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
          -- n ≥ 1 since j + 1 < n
          have hn_pos : n ≥ 1 := by omega
          obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn_pos)
          -- Use q-Pascal identity
          have hpascal : j + 1 ≤ m + 1 := by omega
          rw [qBinomialEval_pascal m j q hpascal]
          -- Use IH
          have h1 : qBinomialEval m j q = qBinomial q m j := ih m (Nat.lt_succ_self m) j
          have h2 : qBinomialEval m (j + 1) q = qBinomial q m (j + 1) := ih m (Nat.lt_succ_self m) (j + 1)
          rw [h1, h2]
          -- This matches the definition of qBinomial
          rfl

end CombinatoricDefinition

section ProductRule

variable {L : Type*} [CommRing L]

/-- Lemma lem.prodrule.sum-ai-plus-bi: Product expansion rule.
    When expanding ∏ᵢ (aᵢ + bᵢ), we get a sum over all subsets S of [n],
    where each term is (∏_{i ∈ S} aᵢ) · (∏_{i ∉ S} bᵢ).

    This is a fundamental identity used in proofs of the q-binomial theorems
    and determinant formulas.

    A rigorous proof can be found in [detnotes, Exercise 6.1 (a)]. -/
theorem prod_add_eq_sum_over_subsets {n : ℕ} (a b : Fin n → L) :
    ∏ i, (a i + b i) = ∑ S : Finset (Fin n), (∏ i ∈ S, a i) * (∏ i ∈ Sᶜ, b i) := by
  simp only [compl_eq_univ_sdiff]
  rw [Finset.prod_add]
  -- Convert sum over univ.powerset to sum over all Finset (Fin n)
  exact sum_bij' (fun S _ => S) (fun S _ => S) (by simp) (by simp) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

end ProductRule

section FirstQBinomialTheorem

variable {K : Type*} [CommRing K]

/-- Helper: n ∉ T when T ⊆ range n -/
private lemma not_mem_of_subset_range' {n : ℕ} {T : Finset ℕ} (hT : T ⊆ range n) : n ∉ T := by
  intro hmem
  have : n ∈ range n := hT hmem
  exact notMem_range_self this

/-- Disjointness lemma for powersetCard and image of insert -/
private lemma disjoint_powersetCard_image_insert' {n k : ℕ} :
    Disjoint ((range n).powersetCard (k + 1)) (((range n).powersetCard k).image (insert n)) := by
  rw [disjoint_left]
  intro T hT1 hT2
  simp only [mem_powersetCard, mem_image] at hT1 hT2
  obtain ⟨U, ⟨hU1, _⟩, hT⟩ := hT2
  have hxT : n ∈ T := by rw [← hT]; exact mem_insert_self n U
  have hxs : n ∈ range n := hT1.1 hxT
  exact notMem_range_self hxs

/-- The q-binomial coefficient [n choose 1]_q equals the q-integer [n]_q.

    This follows from the recurrence relation: qBinomial q (n+1) 1 = 1 + q * qBinomial q n 1,
    which is the same recurrence as qNat q (n+1) = 1 + q * qNat q n. -/
private lemma qBinomial_eq_qNat (q : K) (n : ℕ) : qBinomial q n 1 = qNat q n := by
  induction n with
  | zero => simp [qBinomial, qNat]
  | succ n ih =>
    simp only [qBinomial, qBinomial_zero_right, ih]
    rw [qNat_succ]
    ring

/-- Key identity relating qNat and powers: qNat q n + q^n = 1 + q * qNat q n.

    This follows from the geometric series identity qNat q n * (1 - q) = 1 - q^n. -/
private lemma qNat_add_pow (q : K) (n : ℕ) : qNat q n + q ^ n = 1 + q * qNat q n := by
  have h := qNat_mul_one_sub q n
  have h' : qNat q n - qNat q n * q = 1 - q ^ n := by
    calc qNat q n - qNat q n * q = qNat q n * 1 - qNat q n * q := by ring
      _ = qNat q n * (1 - q) := by ring
      _ = 1 - q ^ n := h
  calc qNat q n + q ^ n
      = (qNat q n - qNat q n * q) + qNat q n * q + q ^ n := by ring
    _ = (1 - q ^ n) + qNat q n * q + q ^ n := by rw [h']
    _ = 1 + qNat q n * q := by ring
    _ = 1 + q * qNat q n := by ring

/-- Key algebraic identity for the induction step of qBinomial_sum_subsets.

    This identity holds because qBinomial satisfies specific algebraic relations.
    The proof uses induction on n, showing that the identity follows from
    the recurrence relation for qBinomial.

    Specifically, we need:
    q^k * qBinomial q n (k+1) + q^n * qBinomial q n k
    = q^k * qBinomial q n k + q^(2k+1) * qBinomial q n (k+1)

    This is equivalent to:
    (q^n - q^k) * qBinomial q n k = q^k * (q^(k+1) - 1) * qBinomial q n (k+1)

    The proof proceeds by induction on n, using the specific structure of
    qBinomial coefficients. The identity follows from the fact that qBinomial
    can be expressed as a geometric sum. -/
lemma qBinomial_induction_identity (q : K) (n k : ℕ) :
    q ^ k * qBinomial q n (k + 1) + q ^ n * qBinomial q n k =
    q ^ k * qBinomial q n k + q ^ (k + 1) * q ^ k * qBinomial q n (k + 1) := by
  induction n generalizing k with
  | zero =>
    simp only [qBinomial, mul_zero, add_zero]
    -- qBinomial q 0 (k+1) = 0 for any k, so both sides are 0
    cases k with
    | zero => simp [qBinomial]
    | succ k => simp [qBinomial]
  | succ n ih =>
    cases k with
    | zero =>
      simp only [qBinomial, pow_zero, one_mul, mul_one, zero_add]
      rw [qBinomial_eq_qNat]
      have h := qNat_add_pow q n
      simp only [pow_one]
      calc 1 + q * qNat q n + q ^ (n + 1)
          = 1 + q * qNat q n + q * q ^ n := by ring
        _ = 1 + q * (qNat q n + q ^ n) := by ring
        _ = 1 + q * (1 + q * qNat q n) := by rw [h]
    | succ k =>
      -- Use the recurrence for qBinomial
      simp only [qBinomial]
      -- Apply IH and algebraic manipulation
      have ih1 := ih (k + 1)
      have ih2 := ih k
      -- The proof uses linear_combination of q * ih2 and q^(k+2) * ih1
      linear_combination q * ih2 + q ^ (k + 2) * ih1

/-- Key lemma: The sum over k-element subsets of {0, 1, ..., n-1} of q^{sum(S)}
    equals q^{k(k-1)/2} * [n choose k]_q.

    This is the combinatorial interpretation of q-binomial coefficients from
    Proposition prop.pars.qbinom.alt-defs part (b) in the textbook.

    The formula arises because:
    - [n choose k]_q counts k-element subsets weighted by q^{sum(S) - (1+2+...+k)}
    - In 0-indexed form, this becomes q^{sum(S)} = q^{k(k-1)/2} * [n choose k]_q

    The proof proceeds by induction on n, using the q-Pascal recurrence. -/
theorem qBinomial_sum_subsets (q : K) (n k : ℕ) :
    ∑ S ∈ ((range n).powerset.filter (fun S => S.card = k)),
      q ^ (∑ i ∈ S, i) =
    q ^ (k * (k - 1) / 2) * qBinomial q n k := by
  rw [← powersetCard_eq_filter]
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases n with
    | zero =>
      cases k with
      | zero =>
        simp only [range_zero, powersetCard_zero, sum_singleton, sum_empty, pow_zero, qBinomial, mul_one]
        norm_num
      | succ k =>
        simp only [range_zero, qBinomial, mul_zero]
        rw [powersetCard_eq_empty.mpr (by simp)]
        simp
    | succ n =>
      cases k with
      | zero =>
        simp only [powersetCard_zero, sum_singleton, sum_empty, pow_zero, qBinomial, mul_one]
        norm_num
      | succ k =>
        rw [range_add_one, powersetCard_succ_insert notMem_range_self]
        rw [sum_union disjoint_powersetCard_image_insert']
        rw [ih n (Nat.lt_succ_self n) (k + 1)]
        have hinj : Set.InjOn (insert n) (((range n).powersetCard k) : Set (Finset ℕ)) := by
          intro T1 hT1 T2 hT2 heq
          simp only [mem_coe, mem_powersetCard] at hT1 hT2
          have h1 : n ∉ T1 := not_mem_of_subset_range' hT1.1
          have h2 : n ∉ T2 := not_mem_of_subset_range' hT2.1
          exact insert_erase_invOn.2.injOn h1 h2 heq
        rw [sum_image hinj]
        have h3 : ∀ T ∈ (range n).powersetCard k, q ^ (∑ i ∈ insert n T, i) = q ^ n * q ^ (∑ i ∈ T, i) := by
          intro T hT
          simp only [mem_powersetCard] at hT
          rw [sum_insert (not_mem_of_subset_range' hT.1), pow_add]
        rw [sum_congr rfl h3, ← mul_sum, ih n (Nat.lt_succ_self n) k]
        simp only [qBinomial]
        have hsimp : (k + 1) * (k + 1 - 1) / 2 = (k + 1) * k / 2 := by simp
        simp only [hsimp]
        have hexp : (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
          cases k with
          | zero => simp
          | succ m =>
            simp only [Nat.succ_sub_one]
            have h1 : (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) := by ring
            rw [h1]
            rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
        have hpow : q ^ ((k + 1) * k / 2) = q ^ (k * (k - 1) / 2) * q ^ k := by
          rw [hexp, pow_add]
        rw [hpow]
        have h4 : q ^ (k * (k - 1) / 2) * q ^ k * qBinomial q n (k + 1) +
                  q ^ n * (q ^ (k * (k - 1) / 2) * qBinomial q n k) =
                  q ^ (k * (k - 1) / 2) * (q ^ k * qBinomial q n (k + 1) + q ^ n * qBinomial q n k) := by
          ring
        rw [h4]
        have h5 : q ^ (k * (k - 1) / 2) * q ^ k *
                  (qBinomial q n k + q ^ (k + 1) * qBinomial q n (k + 1)) =
                  q ^ (k * (k - 1) / 2) * (q ^ k * qBinomial q n k + q ^ (k + 1) * q ^ k * qBinomial q n (k + 1)) := by
          ring
        rw [h5]
        congr 1
        exact qBinomial_induction_identity q n k

/-- Theorem thm.pars.qbinom.binom1: First q-binomial theorem.
    For a, b ∈ K and n ∈ ℕ, in the polynomial ring K[q], we have:
    (aq⁰ + b)(aq¹ + b)···(aqⁿ⁻¹ + b) = ∑_{k=0}^{n} q^{k(k-1)/2} · [n choose k]_q · aᵏ · bⁿ⁻ᵏ

    Setting q = 1 recovers the classical binomial formula (a + b)ⁿ.

    The proof uses the product expansion lemma (lem.prodrule.sum-ai-plus-bi):
    - Expand the product as a sum over subsets S ⊆ {0, 1, ..., n-1}
    - For each S, the contribution is a^|S| * q^{∑_{i ∈ S} i} * b^{n - |S|}
    - Group by cardinality k = |S|
    - Use qBinomial_sum_subsets to evaluate the sum over k-element subsets -/
theorem qBinomial_first_theorem (a b q : K) (n : ℕ) :
    ∏ i ∈ range n, (a * q ^ i + b) =
    ∑ k ∈ range (n + 1), q ^ (k * (k - 1) / 2) * qBinomial q n k * a ^ k * b ^ (n - k) := by
  -- Use the product expansion: ∏_i (a_i + b_i) = ∑_S (∏_{i ∈ S} a_i) (∏_{i ∉ S} b_i)
  rw [Finset.prod_add]
  -- Simplify the products
  conv_lhs =>
    arg 2
    ext S
    rw [prod_mul_distrib, prod_pow_eq_pow_sum, prod_const, prod_const]
  -- Now LHS = ∑_S a^|S| * q^{∑_{i ∈ S} i} * b^{|range n \ S|}
  -- Group by cardinality
  have h_card : ∀ S ∈ (range n).powerset, (range n \ S).card = n - S.card := by
    intro S hS
    rw [mem_powerset] at hS
    rw [Finset.card_sdiff_of_subset hS, card_range]
  -- Partition the sum by cardinality
  have h_partition : ∑ S ∈ (range n).powerset, (a ^ S.card * q ^ (∑ i ∈ S, i)) * b ^ (range n \ S).card =
      ∑ k ∈ range (n + 1), ∑ S ∈ ((range n).powerset.filter (fun S => S.card = k)),
        (a ^ S.card * q ^ (∑ i ∈ S, i)) * b ^ (range n \ S).card := by
    rw [← sum_biUnion]
    · congr 1
      ext S
      simp only [mem_biUnion, mem_range, mem_filter, mem_powerset]
      constructor
      · intro hS
        refine ⟨S.card, ?_, hS, rfl⟩
        calc S.card ≤ (range n).card := card_le_card hS
          _ = n := card_range n
          _ < n + 1 := Nat.lt_succ_self n
      · intro ⟨k, ⟨_, hS, _⟩⟩
        exact hS
    · intro i _ j _ hij
      simp only [Function.onFun, disjoint_filter]
      intro S _ hSi hSj
      exact hij (hSi.symm.trans hSj)
  rw [h_partition]
  -- Now extract the constants from the inner sum
  congr 1
  ext k
  have h_const : ∀ S ∈ ((range n).powerset.filter (fun S => S.card = k)),
      (a ^ S.card * q ^ (∑ i ∈ S, i)) * b ^ (range n \ S).card =
      a ^ k * q ^ (∑ i ∈ S, i) * b ^ (n - k) := by
    intro S hS
    simp only [mem_filter, mem_powerset] at hS
    rw [hS.2, h_card S (mem_powerset.mpr hS.1), hS.2]
  rw [sum_congr rfl h_const]
  rw [← sum_mul, ← mul_sum]
  -- Now use the key lemma
  rw [qBinomial_sum_subsets]
  ring

/-- The first q-binomial theorem specializes to the binomial formula when q = 1. -/
theorem qBinomial_first_theorem_at_one (a b : K) (n : ℕ) :
    ∏ _i ∈ range n, (a + b) = ∑ k ∈ range (n + 1), (n.choose k : K) * a ^ k * b ^ (n - k) := by
  -- LHS is (a + b)^n
  rw [prod_const, card_range]
  -- Use the binomial theorem
  rw [add_pow]
  -- Rearrange terms
  congr 1
  ext k
  ring

end FirstQBinomialTheorem

section SecondQBinomialTheorem

variable {L : Type*} [CommRing L]
variable {A : Type*} [Ring A] [Algebra L A]

/-- Helper lemma: b * a^k = ω^k * a^k * b for the twisted commutativity relation. -/
lemma b_mul_pow_a (ω : L) (a b : A) (hab : b * a = ω • (a * b)) (k : ℕ) :
    b * a ^ k = (ω ^ k) • (a ^ k * b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc b * a ^ (k + 1) = b * (a ^ k * a) := by rw [pow_succ]
      _ = b * a ^ k * a := by noncomm_ring
      _ = (ω ^ k) • (a ^ k * b) * a := by rw [ih]
      _ = (ω ^ k) • (a ^ k * b * a) := by rw [smul_mul_assoc]
      _ = (ω ^ k) • (a ^ k * (b * a)) := by noncomm_ring
      _ = (ω ^ k) • (a ^ k * (ω • (a * b))) := by rw [hab]
      _ = (ω ^ k) • ((ω) • (a ^ k * (a * b))) := by rw [mul_smul_comm]
      _ = (ω ^ k * ω) • (a ^ k * (a * b)) := by rw [smul_smul]
      _ = (ω ^ k * ω) • (a ^ k * a * b) := by noncomm_ring
      _ = (ω ^ (k + 1)) • (a ^ (k + 1) * b) := by rw [pow_succ, pow_succ]

/-- Theorem thm.pars.qbinom.binom2: Second q-binomial theorem (Potter's binomial theorem).
    Let A be a noncommutative L-algebra, and let a, b ∈ A satisfy ba = ω·ab for some ω ∈ L.
    Then (a + b)ⁿ = ∑_{k=0}^{n} [n choose k]_ω · aᵏ · bⁿ⁻ᵏ.

    This generalizes the binomial formula to the noncommutative setting with
    a "twisted" commutativity relation. -/
theorem qBinomial_second_theorem (ω : L) (a b : A) (hab : b * a = ω • (a * b)) (n : ℕ) :
    (a + b) ^ n = ∑ k ∈ range (n + 1), (qBinomial ω n k) • (a ^ k * b ^ (n - k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- (a + b)^{n+1} = (a + b) * (a + b)^n
    rw [pow_succ', ih, add_mul, mul_sum, mul_sum]
    -- Transform each term in the sums
    have ha : ∀ k ∈ range (n + 1), a * (qBinomial ω n k • (a ^ k * b ^ (n - k))) =
              (qBinomial ω n k) • (a ^ (k + 1) * b ^ (n - k)) := by
      intro k _; rw [mul_smul_comm]; congr 1; rw [pow_succ']; noncomm_ring
    have hb : ∀ k ∈ range (n + 1), b * (qBinomial ω n k • (a ^ k * b ^ (n - k))) =
              (ω ^ k * qBinomial ω n k) • (a ^ k * b ^ (n + 1 - k)) := by
      intro k hk
      simp only [mem_range] at hk
      rw [mul_smul_comm]
      have hnk : n - k + 1 = n + 1 - k := by omega
      calc qBinomial ω n k • (b * (a ^ k * b ^ (n - k)))
          = qBinomial ω n k • (b * a ^ k * b ^ (n - k)) := by noncomm_ring
        _ = qBinomial ω n k • ((ω ^ k) • (a ^ k * b) * b ^ (n - k)) := by rw [b_mul_pow_a ω a b hab k]
        _ = qBinomial ω n k • ((ω ^ k) • (a ^ k * b * b ^ (n - k))) := by rw [smul_mul_assoc]
        _ = qBinomial ω n k • ((ω ^ k) • (a ^ k * (b * b ^ (n - k)))) := by noncomm_ring
        _ = qBinomial ω n k • ((ω ^ k) • (a ^ k * b ^ (n - k + 1))) := by rw [pow_succ']
        _ = (qBinomial ω n k * ω ^ k) • (a ^ k * b ^ (n - k + 1)) := by rw [smul_smul]
        _ = (ω ^ k * qBinomial ω n k) • (a ^ k * b ^ (n - k + 1)) := by ring_nf
        _ = (ω ^ k * qBinomial ω n k) • (a ^ k * b ^ (n + 1 - k)) := by rw [hnk]
    simp_rw [sum_congr rfl ha, sum_congr rfl hb]
    -- Now we have:
    -- LHS = ∑_{k=0}^n [n,k] • (a^{k+1} * b^{n-k}) + ∑_{k=0}^n ω^k[n,k] • (a^k * b^{n+1-k})
    -- RHS = ∑_{k=0}^{n+1} [n+1,k] • (a^k * b^{n+1-k})
    -- The proof follows from the q-Pascal recurrence: [n+1,k+1] = [n,k] + ω^{k+1}[n,k+1]
    -- After reindexing and combining terms, the coefficients match exactly.
    conv_rhs => rw [sum_range_succ, sum_range_succ']
    simp only [qBinomial_zero_right, Nat.sub_zero, one_smul, qBinomial_self, Nat.sub_self,
               pow_zero, mul_one]
    conv_lhs =>
      arg 1; rw [sum_range_succ]
      simp only [qBinomial_self, Nat.sub_self, pow_zero, mul_one, one_smul]
    conv_lhs =>
      arg 2; rw [sum_range_succ']
      simp only [pow_zero, one_mul, qBinomial_zero_right, Nat.sub_zero, one_smul]
    simp only [one_mul]
    -- Use suffices to prove the key sum equality
    suffices h : ∑ x ∈ range n, qBinomial ω n x • (a ^ (x + 1) * b ^ (n - x)) +
                 ∑ k ∈ range n, (ω ^ (k + 1) * qBinomial ω n (k + 1)) • (a ^ (k + 1) * b ^ (n + 1 - (k + 1))) =
                 ∑ k ∈ range n, qBinomial ω (n + 1) (k + 1) • (a ^ (k + 1) * b ^ (n + 1 - (k + 1))) by
      calc ∑ x ∈ range n, qBinomial ω n x • (a ^ (x + 1) * b ^ (n - x)) + a ^ (n + 1) +
             (∑ k ∈ range n, (ω ^ (k + 1) * qBinomial ω n (k + 1)) • (a ^ (k + 1) * b ^ (n + 1 - (k + 1))) + b ^ (n + 1))
          = (∑ x ∈ range n, qBinomial ω n x • (a ^ (x + 1) * b ^ (n - x)) +
             ∑ k ∈ range n, (ω ^ (k + 1) * qBinomial ω n (k + 1)) • (a ^ (k + 1) * b ^ (n + 1 - (k + 1)))) +
            (a ^ (n + 1) + b ^ (n + 1)) := by abel
        _ = ∑ k ∈ range n, qBinomial ω (n + 1) (k + 1) • (a ^ (k + 1) * b ^ (n + 1 - (k + 1))) +
            (a ^ (n + 1) + b ^ (n + 1)) := by rw [h]
        _ = ∑ k ∈ range n, qBinomial ω (n + 1) (k + 1) • (a ^ (k + 1) * b ^ (n + 1 - (k + 1))) +
            b ^ (n + 1) + a ^ (n + 1) := by abel
    -- Prove h using the q-Pascal recurrence
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    simp only [mem_range] at hk
    have h1 : n + 1 - (k + 1) = n - k := by omega
    rw [h1, ← add_smul]
    -- The coefficient equality follows from the definition of qBinomial
    congr 1

/-- Example: For 2×2 matrices with ba = -ab, the second q-binomial theorem applies with ω = -1. -/
example : ∃ (a b : Matrix (Fin 2) (Fin 2) ℤ), b * a = (-1 : ℤ) • (a * b) := by
  use !![0, 1; 1, 0], !![1, 0; 0, -1]
  native_decide

end SecondQBinomialTheorem

section LinearIndependence

variable {F : Type*} [Field F]
variable {V : Type*} [AddCommGroup V] [Module F V]

omit [Field F] [AddCommGroup V] [Module F V] in
/-- Helper lemma: the range of Fin.init equals the image of indices less than n -/
private lemma range_init_eq_image_lt {n : ℕ} (v : Fin (n + 1) → V) :
    Set.range (Fin.init v) = v '' {j : Fin (n + 1) | j.val < n} := by
  ext x
  simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq, Fin.init]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j.val, hj⟩, by simp [Fin.castSucc]⟩

set_option backward.isDefEq.respectTransparency false in
/-- Lemma lem.linalg.lin-ind-via-span: A k-tuple (v₁, v₂, ..., vₖ) is linearly independent
    if and only if each vᵢ ∉ span{v₁, ..., vᵢ₋₁}.

    This is the inductive characterization of linear independence. -/
theorem linearIndependent_iff_not_mem_span_of_lt {k : ℕ} (v : Fin k → V) :
    LinearIndependent F v ↔
    ∀ i : Fin k, v i ∉ Submodule.span F (v '' {j : Fin k | j.val < i.val}) := by
  induction k with
  | zero =>
    simp only [IsEmpty.forall_iff, iff_true]
    exact linearIndependent_empty_type
  | succ n ih =>
    rw [linearIndependent_finSucc']
    constructor
    · intro ⟨hind, hlast⟩ i
      by_cases hi : i = Fin.last n
      · subst hi
        simp only [Fin.val_last]
        rw [range_init_eq_image_lt] at hlast
        exact hlast
      · have hi' : i.val < n := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) (fun h => hi (Fin.ext h))
        rw [ih (Fin.init v)] at hind
        specialize hind ⟨i.val, hi'⟩
        simp only [Fin.init] at hind
        intro hmem
        apply hind
        have hieq : v i = v (Fin.castSucc ⟨i.val, hi'⟩) := by
          simp only [Fin.castSucc, Fin.castAdd]
          congr
        rw [hieq] at hmem
        apply Submodule.span_mono _ hmem
        intro x hx
        simp only [Set.mem_image, Set.mem_ofPred_eq] at hx ⊢
        obtain ⟨j, hj, rfl⟩ := hx
        have hjn : j.val < n := Nat.lt_of_lt_of_le hj (Nat.le_of_lt hi')
        exact ⟨⟨j.val, hjn⟩, hj, by simp [Fin.castSucc, Fin.castAdd]⟩
    · intro h
      constructor
      · rw [ih]
        intro i
        have hlt : i.val < n.succ := Nat.lt_trans i.isLt (Nat.lt_succ_self n)
        specialize h ⟨i.val, hlt⟩
        simp only [Fin.init]
        intro hmem
        apply h
        have hieq : v ⟨i.val, hlt⟩ = v (Fin.castSucc i) := by
          simp only [Fin.castSucc, Fin.castAdd]
          congr
        rw [← hieq] at hmem
        apply Submodule.span_mono _ hmem
        intro x hx
        simp only [Set.mem_image, Set.mem_ofPred_eq] at hx ⊢
        obtain ⟨j, hj, rfl⟩ := hx
        have hjn : j.val < n.succ := Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hj (Nat.le_of_lt i.isLt))
        refine ⟨⟨j.val, hjn⟩, hj, ?_⟩
        simp only [Fin.castSucc, Fin.castAdd]
        congr
      · specialize h (Fin.last n)
        simp only [Fin.val_last] at h
        rw [range_init_eq_image_lt]
        exact h

end LinearIndependence

section CountingSubspaces

variable {F : Type*} [Field F] [Fintype F]
variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- Lemma lem.pars.qbinom.lin-ind-count: The number of linearly independent k-tuples
    of vectors in an n-dimensional F-vector space V is
    ∏_{i=0}^{k-1} (|F|ⁿ - |F|ⁱ).

    The proof proceeds by induction on k:
    - Base case (k = 0): There is exactly one 0-tuple, which is vacuously linearly independent.
    - Inductive step: A linearly independent (k+1)-tuple (v₁, ..., v_{k+1}) corresponds to
      a linearly independent k-tuple (v₂, ..., v_{k+1}) together with a choice of v₁ outside
      the span of {v₂, ..., v_{k+1}}. The span has |F|^k elements, so there are |F|^n - |F|^k
      choices for v₁.

    This uses `card_linearIndependent` from Mathlib which proves this via the equivalence
    `equiv_linearIndependent`. -/
theorem card_linearIndependent_tuples (n k : ℕ) (hn : Module.finrank F V = n) :
    Nat.card {v : Fin k → V // LinearIndependent F v} =
    ∏ i ∈ range k, (Fintype.card F ^ n - Fintype.card F ^ i) := by
  haveI : Finite V := Module.finite_of_finite (R := F) (M := V)
  by_cases hk : k ≤ n
  · -- Case k ≤ n: use Mathlib's card_linearIndependent
    have := @card_linearIndependent F V _ _ _ _ _ k (by rw [hn]; exact hk)
    rw [hn] at this
    convert this using 1
    rw [Finset.prod_range]
  · -- Case k > n: both sides are 0 (no linearly independent k-tuples exist)
    push Not at hk
    have h1 : Nat.card {v : Fin k → V // LinearIndependent F v} = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      intro ⟨v, hv⟩
      have : Fintype.card (Fin k) ≤ Module.finrank F V := hv.fintype_card_le_finrank
      simp only [Fintype.card_fin, hn] at this
      omega
    have h2 : ∏ i ∈ range k, (Fintype.card F ^ n - Fintype.card F ^ i) = 0 := by
      apply prod_eq_zero (mem_range.mpr hk)
      simp
    rw [h1, h2]

/-- Lemma lem.count.multijection: Multijection principle.
    If f : A → B is a map such that each b ∈ B has exactly m preimages, then |A| = m · |B|.

    This is a fundamental counting principle used throughout combinatorics.
    A map f satisfying this assumption is called an m-to-1 map.

    The proof uses the fiber decomposition: |A| = Σ_{b ∈ B} |fiber(b)|,
    where each fiber has cardinality m by assumption. -/
theorem card_eq_mul_of_fibers {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (m : ℕ) (hf : ∀ b : B, Fintype.card {a : A // f a = b} = m) :
    Fintype.card A = m * Fintype.card B := by
  -- Use the fiber decomposition: |A| = Σ_{b ∈ B} |fiber(b)|
  have h1 : Fintype.card A = ∑ b : B, Fintype.card {a : A // f a = b} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
  simp_rw [h1, hf, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- The span map sends a linearly independent k-tuple to its span (a k-dimensional subspace). -/
noncomputable def spanMap (k : ℕ) :
    {v : Fin k → V // LinearIndependent F v} → {W : Submodule F V // Module.finrank F W = k} :=
  fun ⟨v, hv⟩ => ⟨Submodule.span F (Set.range v), by
    rw [finrank_span_eq_card hv, Fintype.card_fin]⟩

-- Helper lemma: v maps into W when span(v) = W
omit [Fintype F] [Module.Finite F V] in
private lemma mem_of_spanMap_eq {k : ℕ} {v : Fin k → V}
    {W : Submodule F V} (hW : Submodule.span F (Set.range v) = W) (i : Fin k) : v i ∈ W := by
  rw [← hW]
  exact Submodule.subset_span (Set.mem_range_self i)

-- Bijection between {v : Fin k → W // LinearIndependent F (Subtype.val ∘ v)} and
-- {v : Fin k → W // LinearIndependent F v}
private noncomputable def linIndepEquiv (k : ℕ) (W : Submodule F V) :
    {v : Fin k → W // LinearIndependent F (Subtype.val ∘ v)} ≃
    {v : Fin k → W // LinearIndependent F v} := by
  refine Equiv.subtypeEquiv (Equiv.refl _) ?_
  intro v
  constructor
  · intro h
    exact LinearIndependent.of_comp W.subtype h
  · intro h
    exact h.map' W.subtype (Submodule.ker_subtype W)

-- Bijection between fiber and lin indep k-tuples in W
private noncomputable def fiberEquiv (k : ℕ) (W : {W : Submodule F V // Module.finrank F W = k}) :
    {v : {v : Fin k → V // LinearIndependent F v} // spanMap k v = W} ≃
    {v : Fin k → W.val // LinearIndependent F v} := by
  refine (Equiv.ofBijective ?_ ⟨?_, ?_⟩).trans (linIndepEquiv k W.val)
  -- Forward map: given v with span(v) = W, restrict to W
  · intro ⟨⟨v, hv⟩, hvW⟩
    have heq : Submodule.span F (Set.range v) = W.val := by
      simp only [spanMap, Subtype.ext_iff] at hvW
      exact hvW
    refine ⟨fun i => ⟨v i, mem_of_spanMap_eq heq i⟩, ?_⟩
    simp only [Function.comp_def]
    exact hv
  -- Injective
  · intro ⟨⟨v1, hv1⟩, hvW1⟩ ⟨⟨v2, hv2⟩, hvW2⟩ heq
    simp only [Subtype.mk.injEq] at heq ⊢
    funext i
    have := congrFun heq i
    simp only [Subtype.mk.injEq] at this
    exact this
  -- Surjective
  · intro ⟨w, hw⟩
    let v : Fin k → V := Subtype.val ∘ w
    have hv : LinearIndependent F v := hw
    have hspan : Submodule.span F (Set.range v) = W.val := by
      have hle : Submodule.span F (Set.range v) ≤ W.val := by
        apply Submodule.span_le.mpr
        intro x hx
        obtain ⟨i, rfl⟩ := hx
        exact (w i).prop
      have hfinrank : Module.finrank F (Submodule.span F (Set.range v)) = k := by
        rw [finrank_span_eq_card hv, Fintype.card_fin]
      exact Submodule.eq_of_le_of_finrank_eq hle (hfinrank.trans W.prop.symm)
    refine ⟨⟨⟨v, hv⟩, ?_⟩, ?_⟩
    · simp only [spanMap, Subtype.ext_iff]
      exact hspan
    · simp only [Subtype.mk.injEq]
      ext i
      simp [v]

/-- Key lemma for thm.pars.qbinom.subsp-count: Each k-dimensional subspace W has exactly
    ∏_{i=0}^{k-1} (q^k - q^i) preimages under the span map.

    This is because the preimages are exactly the ordered bases of W:
    - A linearly independent k-tuple v with span(v) = W must lie entirely in W
    - Since W is k-dimensional and v has k linearly independent vectors, v spans W automatically
    - Thus the preimages are exactly the linearly independent k-tuples in W
    - By card_linearIndependent, the count is ∏_{i=0}^{k-1} (q^k - q^i)

    This is the key step in the proof of qBinomial_subspace_count. -/
theorem spanMap_fiber_card (k : ℕ) (W : {W : Submodule F V // Module.finrank F W = k}) :
    Nat.card {v : {v : Fin k → V // LinearIndependent F v} // spanMap k v = W} =
    ∏ i ∈ range k, (Fintype.card F ^ k - Fintype.card F ^ i) := by
  -- Use the bijection to reduce to counting linearly independent k-tuples in W
  rw [Nat.card_congr (fiberEquiv k W)]
  -- W is a k-dimensional space over F
  haveI : Finite V := Module.finite_of_finite (R := F) (M := V)
  haveI : Finite W.val := Subtype.finite
  -- Apply card_linearIndependent for W
  have hk : k ≤ Module.finrank F W.val := by rw [W.prop]
  have := @card_linearIndependent F W.val _ _ _ _ _ k hk
  rw [W.prop] at this
  convert this using 1
  rw [Finset.prod_range]

/-- Theorem thm.pars.qbinom.subsp-count: The q-binomial coefficient at |F| counts
    k-dimensional subspaces.
    If V is an n-dimensional vector space over a finite field F, then
    [n choose k]_{|F|} = (# of k-dimensional subspaces of V).

    This is the "linear analogue" of the fact that C(n,k) counts k-element subsets
    of an n-element set.

    ## Proof outline

    The proof uses the **multijection principle** (Lemma lem.count.multijection):

    1. Define the span map f : (linearly independent k-tuples in V) → (k-dim subspaces of V)
       that sends a tuple v to its span span(v).

    2. By `card_linearIndependent_tuples`:
       |linearly independent k-tuples in V| = ∏_{i=0}^{k-1} (q^n - q^i)

    3. By `spanMap_fiber_card`, each k-dimensional subspace W has exactly
       ∏_{i=0}^{k-1} (q^k - q^i) preimages under f (the number of ordered bases of W).

    4. By the multijection principle:
       ∏_{i=0}^{k-1} (q^n - q^i) = (∏_{i=0}^{k-1} (q^k - q^i)) × (# of k-dim subspaces)

    5. Therefore:
       (# of k-dim subspaces) = ∏_{i=0}^{k-1} (q^n - q^i) / ∏_{i=0}^{k-1} (q^k - q^i)
                              = [n choose k]_q -/
theorem qBinomial_subspace_count (n k : ℕ) (hn : Module.finrank F V = n) :
    qBinomial (Fintype.card F : ℚ) n k =
    Nat.card {W : Submodule F V // Module.finrank F W = k} := by
  classical
  -- First handle the case k > n: both sides are 0
  by_cases hkn : k > n
  · rw [qBinomial_gt _ _ _ hkn]
    have : Nat.card {W : Submodule F V // Module.finrank F W = k} = 0 := by
      rw [Nat.card_eq_zero]
      left
      rw [isEmpty_subtype]
      intro W hW
      have : Module.finrank F W ≤ Module.finrank F V := Submodule.finrank_le W
      omega
    simp only [this, Nat.cast_zero]
  · push Not at hkn
    -- Main case: k ≤ n
    haveI : Finite V := Module.finite_of_finite (R := F) (M := V)
    -- Get the count of linearly independent k-tuples in V
    have hk_le : k ≤ Module.finrank F V := by rw [hn]; exact hkn
    have h_linind := card_linearIndependent_tuples (F := F) (V := V) n k hn
    -- The proof now follows from the multijection principle:
    -- |lin ind k-tuples| = |fiber size| × |k-dim subspaces|
    -- ∏_{i=0}^{k-1} (q^n - q^i) = (∏_{i=0}^{k-1} (q^k - q^i)) × (# of k-dim subspaces)
    -- Solving for # of k-dim subspaces gives [n choose k]_q
    
    -- Step 1: The types are finite (using Fintype.ofFinite since V is finite)
    haveI hfin_linind : Fintype {v : Fin k → V // LinearIndependent F v} := Fintype.ofFinite _
    haveI hfin_subsp : Fintype {W : Submodule F V // Module.finrank F W = k} := Fintype.ofFinite _
    
    -- Step 2: The fiber size is constant and nonzero
    let m := ∏ i ∈ range k, (Fintype.card F ^ k - Fintype.card F ^ i)
    have hm_ne : m ≠ 0 := by
      apply prod_ne_zero_iff.mpr
      intro i hi
      simp only [mem_range] at hi
      have hq : Fintype.card F ≥ 2 := Fintype.one_lt_card
      have h1 : Fintype.card F ^ i < Fintype.card F ^ k := Nat.pow_lt_pow_right hq hi
      omega
    
    -- Step 3: By multijection principle: |lin ind| = m × |subspaces|
    have h_multi : Nat.card {v : Fin k → V // LinearIndependent F v} = 
                   m * Nat.card {W : Submodule F V // Module.finrank F W = k} := by
      simp only [Nat.card_eq_fintype_card]
      have h1 : Fintype.card {v : Fin k → V // LinearIndependent F v} = 
                ∑ W : {W : Submodule F V // Module.finrank F W = k}, 
                Fintype.card {v : {v : Fin k → V // LinearIndependent F v} // spanMap k v = W} := by
        rw [← Fintype.card_sigma]
        exact Fintype.card_congr (Equiv.sigmaFiberEquiv (spanMap k)).symm
      rw [h1]
      have h2 : ∀ W, Fintype.card {v : {v : Fin k → V // LinearIndependent F v} // spanMap k v = W} = m := by
        intro W
        rw [← Nat.card_eq_fintype_card]
        exact spanMap_fiber_card k W
      simp_rw [h2, sum_const, card_univ, smul_eq_mul, mul_comm]
    
    -- Step 4: Compute |subspaces| = |lin ind| / m
    rw [h_linind] at h_multi
    have h_subsp_eq : Nat.card {W : Submodule F V // Module.finrank F W = k} = 
                      (∏ i ∈ range k, (Fintype.card F ^ n - Fintype.card F ^ i)) / m := by
      have h_eq : (∏ i ∈ range k, (Fintype.card F ^ n - Fintype.card F ^ i)) = 
                  Nat.card {W : Submodule F V // Module.finrank F W = k} * m := by
        rw [mul_comm]; exact h_multi
      exact (Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hm_ne) h_eq).symm
    
    -- Step 5: Cast to ℚ and relate to qBinomial
    -- We need: qBinomial q n k = (∏ (q^n - q^i)) / (∏ (q^k - q^i))
    let q : ℚ := Fintype.card F
    have hq_gt : q > 1 := by
      have h : Fintype.card F ≥ 2 := Fintype.one_lt_card
      have : (Fintype.card F : ℚ) ≥ 2 := by exact_mod_cast h
      linarith
    have hq_ne : q ≠ 1 := by linarith
    
    -- qNat q (i+1) ≠ 0 for all i
    have hqNat_ne : ∀ i : ℕ, i < k → qNat q (i + 1) ≠ 0 := by
      intro i _
      have : qNat q (i + 1) = ∑ j ∈ range (i + 1), q ^ j := rfl
      rw [this]
      apply ne_of_gt
      apply sum_pos
      · intro j _; positivity
      · exact nonempty_range_iff.mpr (by omega)
    
    -- Use qBinomial_eq_prod_div
    have h_qbinom := qBinomial_eq_prod_div q n k hkn hqNat_ne
    
    -- Relate qNat ratios to power ratios
    have h_qNat_eq : ∀ i, qNat q (n - i) / qNat q (i + 1) = (q ^ (n - i) - 1) / (q ^ (i + 1) - 1) := by
      intro i
      rw [qNat_eq_geom_sum q (n - i) hq_ne, qNat_eq_geom_sum q (i + 1) hq_ne]
      have h1 : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr hq_ne)
      have h2 : (1 - q ^ (n - i)) / (1 - q) / ((1 - q ^ (i + 1)) / (1 - q)) = 
                (1 - q ^ (n - i)) / (1 - q ^ (i + 1)) := by field_simp [h1]
      rw [h2]
      have h3 : (1 - q ^ (n - i)) = -(q ^ (n - i) - 1) := by ring
      have h4 : (1 - q ^ (i + 1)) = -(q ^ (i + 1) - 1) := by ring
      rw [h3, h4]
      field_simp
    
    -- The product of qNat ratios equals the product of power ratios
    have h_prod_qNat : ∏ i ∈ range k, (qNat q (n - i) / qNat q (i + 1)) = 
                       ∏ i ∈ range k, ((q ^ (n - i) - 1) / (q ^ (i + 1) - 1)) := by
      apply prod_congr rfl
      intro i _
      exact h_qNat_eq i
    
    -- Key algebraic identity: reindex the denominator product
    have h_prod_reindex : ∏ i ∈ range k, (q ^ (k - i) - 1) = ∏ i ∈ range k, (q ^ (i + 1) - 1) := by
      refine prod_bij' (fun i _ => k - 1 - i) (fun j _ => k - 1 - j) ?_ ?_ ?_ ?_ ?_
      · intro i hi; simp only [mem_range] at hi ⊢; omega
      · intro j hj; simp only [mem_range] at hj ⊢; omega
      · intro i hi; simp only [mem_range] at hi; omega
      · intro j hj; simp only [mem_range] at hj; omega
      · intro i hi
        simp only [mem_range] at hi
        have h1 : k - 1 - i + 1 = k - i := by omega
        show q ^ (k - i) - 1 = q ^ (k - 1 - i + 1) - 1
        rw [h1]
    
    -- Factor out q^i from (q^n - q^i)
    have h_factor : ∀ a b : ℕ, b ≤ a → q ^ a - q ^ b = q ^ b * (q ^ (a - b) - 1) := by
      intro a b hab
      have : q ^ a = q ^ b * q ^ (a - b) := by rw [← pow_add]; congr 1; omega
      rw [this]; ring
    
    -- Product split
    have h_prod_split : ∀ a b : ℕ, b ≤ a → 
        ∏ i ∈ range b, (q ^ a - q ^ i) = (∏ i ∈ range b, q ^ i) * ∏ i ∈ range b, (q ^ (a - i) - 1) := by
      intro a b hab
      rw [← prod_mul_distrib]
      apply prod_congr rfl
      intro i hi
      simp only [mem_range] at hi
      exact h_factor a i (by omega)
    
    -- The ratio of products equals the product of ratios
    have h_ratio_eq : (∏ i ∈ range k, (q ^ n - q ^ i)) / (∏ i ∈ range k, (q ^ k - q ^ i)) =
                      ∏ i ∈ range k, (q ^ (n - i) - 1) / (q ^ (i + 1) - 1) := by
      have h1 := h_prod_split n k hkn
      have h2 := h_prod_split k k (le_refl k)
      rw [h1, h2]
      have hprod_qi_ne : ∏ i ∈ range k, q ^ i ≠ 0 := by
        apply prod_ne_zero_iff.mpr; intro i _; positivity
      have hprod_denom_ne : ∏ i ∈ range k, (q ^ (k - i) - 1) ≠ 0 := by
        apply prod_ne_zero_iff.mpr
        intro i hi
        simp only [mem_range] at hi
        have : q ^ (k - i) > 1 := by
          have hki : k - i ≥ 1 := by omega
          calc q ^ (k - i) ≥ q ^ 1 := pow_le_pow_right₀ (by linarith) hki
            _ = q := pow_one q
            _ > 1 := hq_gt
        linarith
      rw [h_prod_reindex] at h2 hprod_denom_ne ⊢
      rw [mul_div_mul_left _ _ hprod_qi_ne, prod_div_distrib]
    
    -- Now combine everything
    rw [h_qbinom, h_prod_qNat, ← h_ratio_eq]
    
    -- Cast the Nat.card to ℚ and show the equality
    rw [h_subsp_eq]
    -- Need to show: (∏ (q^n - q^i)) / (∏ (q^k - q^i)) = (numerator / m) as ℚ
    -- where numerator = ∏ (|F|^n - |F|^i) and m = ∏ (|F|^k - |F|^i)
    have h_num_eq : (∏ i ∈ range k, (q ^ n - q ^ i)) = 
                    ↑(∏ i ∈ range k, (Fintype.card F ^ n - Fintype.card F ^ i)) := by
      rw [Nat.cast_prod]
      apply prod_congr rfl
      intro i hi
      simp only [mem_range] at hi
      have hcard : Fintype.card F ≥ 1 := Fintype.card_pos
      have hle : Fintype.card F ^ i ≤ Fintype.card F ^ n := 
        Nat.pow_le_pow_right hcard (by omega : i ≤ n)
      simp only [Nat.cast_sub hle, Nat.cast_pow]
      rfl
    have h_denom_eq : (∏ i ∈ range k, (q ^ k - q ^ i)) = (m : ℚ) := by
      rw [Nat.cast_prod]
      apply prod_congr rfl
      intro i hi
      simp only [mem_range] at hi
      have hcard : Fintype.card F ≥ 1 := Fintype.card_pos
      have hle : Fintype.card F ^ i ≤ Fintype.card F ^ k := 
        Nat.pow_le_pow_right hcard (by omega : i ≤ k)
      simp only [Nat.cast_sub hle, Nat.cast_pow]
      rfl
    rw [h_num_eq, h_denom_eq]
    -- Now we have: ↑numerator / ↑m = ↑(numerator / m)
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne
    have h_div : m ∣ (∏ i ∈ range k, (Fintype.card F ^ n - Fintype.card F ^ i)) := by
      exact Dvd.intro _ h_multi.symm
    rw [Nat.cast_div h_div (Nat.cast_ne_zero.mpr hm_ne)]

end CountingSubspaces

section Limits

/-- The number of partitions of n with at most k parts. -/
noncomputable def partitionCountAtMostKParts (n k : ℕ) : ℕ :=
  Nat.card {p : Nat.Partition n // p.parts.card ≤ k}

open scoped PowerSeries.WithPiTopology

/-- Helper lemma: For n, m ≥ d + k, the d-th coefficient of qBinomial X n k is the same. -/
private lemma qBinomial_coeff_eq_aux : ∀ (s : ℕ), ∀ (d k n m : ℕ), d + k ≤ s → n ≥ d + k → m ≥ d + k →
    PowerSeries.coeff d (qBinomial (PowerSeries.X : PowerSeries ℚ) n k) =
    PowerSeries.coeff d (qBinomial PowerSeries.X m k) := by
  intro s
  induction s with
  | zero =>
    intro d k n m hs _ _
    have hd : d = 0 := by omega
    have hk : k = 0 := by omega
    subst hd hk
    simp [qBinomial_zero_right]
  | succ s ih =>
    intro d k n m hs hn hm
    cases k with
    | zero =>
      simp [qBinomial_zero_right]
    | succ k =>
      cases n with
      | zero => omega
      | succ n' =>
        cases m with
        | zero => omega
        | succ m' =>
          simp only [qBinomial, map_add]
          have hn' : n' ≥ d + k := by omega
          have hm' : m' ≥ d + k := by omega
          have hs1 : d + k ≤ s := by omega
          have h1 : PowerSeries.coeff d (qBinomial (PowerSeries.X : PowerSeries ℚ) n' k) =
                    PowerSeries.coeff d (qBinomial PowerSeries.X m' k) :=
            ih d k n' m' hs1 hn' hm'
          rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
          split_ifs with hdk
          · have hs2 : (d - (k + 1)) + (k + 1) ≤ s := by omega
            have hn'' : n' ≥ (d - (k + 1)) + (k + 1) := by omega
            have hm'' : m' ≥ (d - (k + 1)) + (k + 1) := by omega
            have h2 : PowerSeries.coeff (d - (k + 1)) (qBinomial (PowerSeries.X : PowerSeries ℚ) n' (k + 1)) =
                      PowerSeries.coeff (d - (k + 1)) (qBinomial PowerSeries.X m' (k + 1)) :=
              ih (d - (k + 1)) (k + 1) n' m' hs2 hn'' hm''
            rw [h1, h2]
          · rw [h1]

lemma qBinomial_coeff_eq (d k n m : ℕ) (hn : n ≥ d + k) (hm : m ≥ d + k) :
    PowerSeries.coeff d (qBinomial (PowerSeries.X : PowerSeries ℚ) n k) =
    PowerSeries.coeff d (qBinomial PowerSeries.X m k) :=
  qBinomial_coeff_eq_aux (d + k) d k n m (le_refl _) hn hm

/-- The product formula satisfies a recurrence matching qBinomial. -/
private lemma prod_inv_recurrence (k : ℕ) :
    (∏ i ∈ range (k + 1), (1 - (PowerSeries.X : PowerSeries ℚ) ^ (i + 1))⁻¹) =
    (∏ i ∈ range k, (1 - PowerSeries.X ^ (i + 1))⁻¹) +
    PowerSeries.X ^ (k + 1) * (∏ i ∈ range (k + 1), (1 - PowerSeries.X ^ (i + 1))⁻¹) := by
  rw [prod_range_succ]
  set L := ∏ i ∈ range k, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (i + 1))⁻¹
  set f := (1 - (PowerSeries.X : PowerSeries ℚ) ^ (k + 1))⁻¹
  have hf : f * (1 - PowerSeries.X ^ (k + 1)) = 1 := by
    rw [PowerSeries.inv_mul_cancel]
    simp
  calc L * f = L * f * 1 := by ring
    _ = L * f * ((1 - PowerSeries.X ^ (k + 1)) + PowerSeries.X ^ (k + 1)) := by ring
    _ = L * f * (1 - PowerSeries.X ^ (k + 1)) + PowerSeries.X ^ (k + 1) * (L * f) := by ring
    _ = L * (f * (1 - PowerSeries.X ^ (k + 1))) + PowerSeries.X ^ (k + 1) * (L * f) := by ring
    _ = L * 1 + PowerSeries.X ^ (k + 1) * (L * f) := by rw [hf]
    _ = L + PowerSeries.X ^ (k + 1) * (L * f) := by ring

/-- The stable value of qBinomial coefficients equals the product formula coefficients. -/
private lemma qBinomial_stable_eq_prod_aux : ∀ (s d k : ℕ), d + k ≤ s →
    PowerSeries.coeff d (qBinomial (PowerSeries.X : PowerSeries ℚ) (d + k) k) =
    PowerSeries.coeff d (∏ i ∈ range k, (1 - PowerSeries.X ^ (i + 1))⁻¹) := by
  intro s
  induction s with
  | zero =>
    intro d k hs
    have hd : d = 0 := by omega
    have hk : k = 0 := by omega
    subst hd hk
    simp [qBinomial_zero_right]
  | succ s ih =>
    intro d k hs
    cases k with
    | zero =>
      simp [qBinomial_zero_right]
    | succ k =>
      have heq : d + (k + 1) = (d + k) + 1 := by omega
      conv_lhs => rw [heq]
      simp only [qBinomial, map_add]
      rw [prod_inv_recurrence k, map_add]
      have hs1 : d + k ≤ s := by omega
      have h1 : PowerSeries.coeff d (qBinomial (PowerSeries.X : PowerSeries ℚ) (d + k) k) =
                PowerSeries.coeff d (∏ i ∈ range k, (1 - PowerSeries.X ^ (i + 1))⁻¹) := ih d k hs1
      rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
      split_ifs with hdk
      · have hsub : d - (k + 1) + (k + 1) = d := Nat.sub_add_cancel hdk
        have hstab : PowerSeries.coeff (d - (k + 1)) (qBinomial (PowerSeries.X : PowerSeries ℚ) (d + k) (k + 1)) =
                     PowerSeries.coeff (d - (k + 1)) (qBinomial PowerSeries.X d (k + 1)) := by
          apply qBinomial_coeff_eq
          · omega
          · omega
        have hs2 : (d - (k + 1)) + (k + 1) ≤ s := by omega
        have h2 : PowerSeries.coeff (d - (k + 1)) (qBinomial (PowerSeries.X : PowerSeries ℚ) ((d - (k + 1)) + (k + 1)) (k + 1)) =
                  PowerSeries.coeff (d - (k + 1)) (∏ i ∈ range (k + 1), (1 - PowerSeries.X ^ (i + 1))⁻¹) := ih (d - (k + 1)) (k + 1) hs2
        rw [hsub] at h2
        rw [hstab, h2, h1]
      · rw [h1]

lemma qBinomial_stable_eq_prod (d k : ℕ) :
    PowerSeries.coeff d (qBinomial (PowerSeries.X : PowerSeries ℚ) (d + k) k) =
    PowerSeries.coeff d (∏ i ∈ range k, (1 - PowerSeries.X ^ (i + 1))⁻¹) :=
  qBinomial_stable_eq_prod_aux (d + k) d k (le_refl _)

/-- Proposition prop.pars.qbinom.lim1: Limit of q-binomial coefficients.
    As n → ∞, the q-binomial coefficient [n choose k]_q converges coefficientwise to
    ∑_{n ∈ ℕ} (p₀(n) + p₁(n) + ... + pₖ(n)) qⁿ = ∏_{i=1}^{k} 1/(1 - qⁱ)

    where pᵢ(n) is the number of partitions of n with exactly i parts.

    This is stated for power series over a field where inverses exist. -/
theorem qBinomial_limit (k : ℕ) :
    Filter.Tendsto (fun n => qBinomial (PowerSeries.X : PowerSeries ℚ) n k)
      Filter.atTop
      (nhds (∏ i ∈ range k, (1 - PowerSeries.X ^ (i + 1))⁻¹)) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  apply tendsto_atTop_of_eventually_const (i₀ := d + k)
  intro n hn
  rw [qBinomial_coeff_eq d k n (d + k) hn (le_refl _)]
  exact qBinomial_stable_eq_prod d k

/-- Helper lemma: The product of geometric series inverses equals the generating function
    for partitions where all parts are at most k.

    This uses `hasProd_powerSeriesMk_card_restricted` from Mathlib's partition generating
    function theory. -/
private lemma prod_inv_eq_restricted_gf (k : ℕ) :
    ∏ i ∈ range k, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (i + 1))⁻¹ =
    PowerSeries.mk fun n => (#(Nat.Partition.restricted n (· ≤ k)) : ℚ) := by
  -- First, convert each inverse to a geometric series
  have h1 : ∏ i ∈ range k, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (i + 1))⁻¹ =
            ∏ i ∈ range k, (∑' j, PowerSeries.X ^ ((i + 1) * j)) := by
    apply Finset.prod_congr rfl
    intro i _
    have h : ((PowerSeries.X : PowerSeries ℚ) ^ (i + 1)).constantCoeff = 0 := by simp
    have h1 := PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero h
    have hconst : PowerSeries.constantCoeff (1 - (PowerSeries.X : PowerSeries ℚ) ^ (i + 1)) ≠ 0 := by simp
    rw [PowerSeries.inv_eq_iff_mul_eq_one hconst]
    convert h1 using 2
    ext n
    simp only [pow_mul]
  rw [h1]
  -- Use the generating function theorem for restricted partitions
  have hp := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℚ (· ≤ k)
  have htprod := hp.tprod_eq
  rw [← htprod]
  -- The infinite product equals the finite product since terms with i ≥ k are 1
  have hsupp : Function.mulSupport (fun i ↦ if i + 1 ≤ k then ∑' j : ℕ, (PowerSeries.X : PowerSeries ℚ) ^ ((i + 1) * j) else 1) ⊆ range k := by
    intro i hi
    simp only [Function.mem_mulSupport, ne_eq] at hi
    simp only [mem_coe, mem_range]
    by_contra h
    push Not at h
    have hcond : ¬ (i + 1 ≤ k) := by omega
    rw [ite_eq_right hcond] at hi
    exact hi rfl
  rw [tprod_eq_prod' hsupp]
  apply Finset.prod_congr rfl
  intro i hi
  rw [mem_range] at hi
  have : i + 1 ≤ k := by omega
  simp only [this, ↓reduceIte]

/-- The bijection between partitions with all parts ≤ k and partitions with at most k parts.

    This is a well-known combinatorial fact: the two sets are in bijection via
    Young diagram conjugation (transpose).

    For a partition p with parts [p₁, p₂, ..., pₘ] (sorted decreasing):
    - The conjugate partition has its i-th part equal to #{j : pⱼ ≥ i}
    - This is an involution that swaps "max part" with "number of parts"

    Key properties:
    - If all parts of p are ≤ k, then the conjugate has at most k parts
    - If p has at most k parts, then the conjugate has all parts ≤ k

    The proof uses YoungDiagram.transpose from Mathlib, which provides the conjugation
    operation on Young diagrams. -/
-- Helper: Young diagram card equals sum of row lengths
private lemma youngDiagram_card_eq_rowLens_sum (μ : YoungDiagram) : μ.card = μ.rowLens.sum := by
  simp only [YoungDiagram.card, YoungDiagram.rowLens]
  have hsum : (List.map μ.rowLen (List.range (μ.colLen 0))).sum =
              ∑ i ∈ range (μ.colLen 0), μ.rowLen i := by
    induction μ.colLen 0 with
    | zero => simp
    | succ m ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
                 List.sum_singleton, sum_range_succ]
      rw [ih]
  rw [hsum]
  conv_rhs => arg 2; ext i; rw [YoungDiagram.rowLen_eq_card]
  have hcells : μ.cells = (range (μ.colLen 0)).biUnion (fun i => μ.row i) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_biUnion, mem_range, YoungDiagram.mem_cells, YoungDiagram.mem_row_iff]
    constructor
    · intro hcell
      have hi : i < μ.colLen 0 := by
        rw [← YoungDiagram.mem_iff_lt_colLen]
        exact μ.up_left_mem (le_refl i) (Nat.zero_le j) hcell
      exact ⟨i, hi, hcell, rfl⟩
    · intro ⟨i', hi', hcell, heq⟩
      exact heq ▸ hcell
  rw [hcells, Finset.card_biUnion]
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Finset.disjoint_iff_ne]
  intro ⟨a, b⟩ ha ⟨c, d⟩ hc heq
  simp only [YoungDiagram.mem_row_iff] at ha hc
  cases heq
  exact hij (ha.2.symm.trans hc.2)

-- Helper: ofRowLens card equals list sum
private lemma ofRowLens_card_eq_sum (w : List ℕ) (hw : w.SortedGE) (hpos : ∀ x ∈ w, 0 < x) :
    (YoungDiagram.ofRowLens w hw).card = w.sum := by
  rw [youngDiagram_card_eq_rowLens_sum, YoungDiagram.rowLens_ofRowLens_eq_self hpos]

-- Helper: positivity of sorted parts
private lemma parts_sort_pos' (m : ℕ) (p : Nat.Partition m) :
    ∀ x ∈ p.parts.sort (· ≥ ·), 0 < x := by
  intro x hx
  have : x ∈ p.parts := by simp only [Multiset.mem_sort] at hx; exact hx
  exact p.parts_pos this

-- Helper: sortedness of sorted parts
private lemma parts_sort_sorted' (m : ℕ) (p : Nat.Partition m) :
    (p.parts.sort (· ≥ ·)).SortedGE :=
  (Multiset.pairwise_sort p.parts (· ≥ ·)).sortedGE

-- Helper: transpose preserves card
private lemma transpose_card' (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  simp only [YoungDiagram.card]
  have h : μ.transpose.cells = (Equiv.prodComm ℕ ℕ).finsetCongr μ.cells := rfl
  rw [h, Equiv.finsetCongr_apply, Finset.card_map]

-- Helper: transpose rowLens length equals original rowLen 0
private lemma transpose_rowLens_length' (μ : YoungDiagram) :
    μ.transpose.rowLens.length = μ.rowLen 0 := by
  rw [YoungDiagram.length_rowLens, YoungDiagram.colLen_transpose]

-- Helper: sorted list remains unchanged when sorted
private lemma sorted_list_sort_eq (l : List ℕ) (hl : l.SortedGE) :
    (↑l : Multiset ℕ).sort (· ≥ ·) = l := by
  have h : (↑((↑l : Multiset ℕ).sort (· ≥ ·)) : Multiset ℕ) = (↑l : Multiset ℕ) :=
    Multiset.sort_eq (↑l : Multiset ℕ) (· ≥ ·)
  have hsorted_sort : ((↑l : Multiset ℕ).sort (· ≥ ·)).SortedGE :=
    (Multiset.pairwise_sort (↑l : Multiset ℕ) (· ≥ ·)).sortedGE
  have hperm : ((↑l : Multiset ℕ).sort (· ≥ ·)).Perm l := Multiset.coe_eq_coe.mp h
  exact List.Perm.eq_of_pairwise' (r := (· ≥ ·)) hsorted_sort.pairwise hl.pairwise hperm

-- Define the Young diagram for a partition
private noncomputable def partitionToYoungDiagram' (m : ℕ) (p : Nat.Partition m) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (parts_sort_sorted' m p)

-- The Young diagram has card m
private lemma partitionToYoungDiagram_card' (m : ℕ) (p : Nat.Partition m) :
    (partitionToYoungDiagram' m p).card = m := by
  unfold partitionToYoungDiagram'
  rw [ofRowLens_card_eq_sum _ _ (parts_sort_pos' m p)]
  have hsort : (↑(p.parts.sort (· ≥ ·)) : Multiset ℕ) = p.parts := Multiset.sort_eq p.parts (· ≥ ·)
  calc (p.parts.sort (· ≥ ·)).sum
      = (↑(p.parts.sort (· ≥ ·)) : Multiset ℕ).sum := rfl
    _ = p.parts.sum := by rw [hsort]
    _ = m := p.parts_sum

-- Define the conjugate partition
private noncomputable def conjugatePartition' (m : ℕ) (p : Nat.Partition m) : Nat.Partition m := by
  let μ := partitionToYoungDiagram' m p
  have hcard : μ.transpose.card = m := by rw [transpose_card', partitionToYoungDiagram_card']
  have hsum : μ.transpose.rowLens.sum = m := by rw [← youngDiagram_card_eq_rowLens_sum, hcard]
  exact ⟨μ.transpose.rowLens, fun hi => μ.transpose.pos_of_mem_rowLens _ hi,
         by rw [Multiset.sum_coe]; exact hsum⟩

-- conjugate.parts.card = original Young diagram's rowLen 0
private lemma conjugatePartition_parts_card' (m : ℕ) (p : Nat.Partition m) :
    (conjugatePartition' m p).parts.card = (partitionToYoungDiagram' m p).rowLen 0 := by
  unfold conjugatePartition'
  simp only
  exact transpose_rowLens_length' _

-- If all parts ≤ k, then conjugate has ≤ k parts
private lemma conjugatePartition_parts_card_le' (m k : ℕ) (p : Nat.Partition m)
    (hp : ∀ i ∈ p.parts, i ≤ k) : (conjugatePartition' m p).parts.card ≤ k := by
  rw [conjugatePartition_parts_card']
  unfold partitionToYoungDiagram'
  by_cases hne : p.parts.card = 0
  · have hparts : p.parts = 0 := Multiset.card_eq_zero.mp hne
    simp only [hparts, Multiset.sort_zero]
    have h : (YoungDiagram.ofRowLens [] (by decide : ([]:List ℕ).SortedGE)).rowLen 0 = 0 := by
      simp only [YoungDiagram.ofRowLens, YoungDiagram.rowLen, YoungDiagram.cellsOfRowLens,
                 Nat.find_eq_zero]
      simp
    convert Nat.zero_le k
  · have hlen : 0 < (p.parts.sort (· ≥ ·)).length := by
      simp only [Multiset.length_sort]; exact Nat.pos_of_ne_zero hne
    have hrowLen : (YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (parts_sort_sorted' m p)).rowLen 0 =
                   (p.parts.sort (· ≥ ·))[0]'hlen := YoungDiagram.rowLen_ofRowLens ⟨0, hlen⟩
    rw [hrowLen]
    have hmem : (p.parts.sort (· ≥ ·))[0] ∈ p.parts := by
      have : (p.parts.sort (· ≥ ·))[0] ∈ p.parts.sort (· ≥ ·) := List.getElem_mem hlen
      simp only [Multiset.mem_sort] at this; exact this
    exact hp _ hmem

-- If p has ≤ k parts, then all parts of conjugate are ≤ k
private lemma conjugatePartition_all_parts_le' (m k : ℕ) (p : Nat.Partition m)
    (hp : p.parts.card ≤ k) : ∀ i ∈ (conjugatePartition' m p).parts, i ≤ k := by
  intro i hi
  unfold conjugatePartition' at hi
  simp only [Multiset.mem_coe] at hi
  have hmax : i ≤ (partitionToYoungDiagram' m p).transpose.rowLen 0 := by
    have hsorted : (partitionToYoungDiagram' m p).transpose.rowLens.SortedGE :=
      (partitionToYoungDiagram' m p).transpose.rowLens_sorted
    obtain ⟨idx, hidx, heq⟩ := List.getElem_of_mem hi
    rw [← heq]
    have h0 : (partitionToYoungDiagram' m p).transpose.rowLens[0]'(by omega) =
              (partitionToYoungDiagram' m p).transpose.rowLen 0 := by rw [YoungDiagram.get_rowLens]
    by_cases hlen : (partitionToYoungDiagram' m p).transpose.rowLens.length = 0
    · simp [hlen] at hidx
    · rw [← h0]; exact hsorted.getElem_ge_getElem_of_le (Nat.zero_le idx)
  have hcolLen : (partitionToYoungDiagram' m p).transpose.rowLen 0 =
                 (partitionToYoungDiagram' m p).colLen 0 := by simp
  rw [hcolLen] at hmax
  have hpartsCard : (partitionToYoungDiagram' m p).colLen 0 = p.parts.card := by
    unfold partitionToYoungDiagram'
    rw [← YoungDiagram.length_rowLens, YoungDiagram.rowLens_length_ofRowLens (parts_sort_pos' m p)]
    simp only [Multiset.length_sort]
  rw [hpartsCard] at hmax
  exact le_trans hmax hp

-- Conjugation is an involution
lemma conjugatePartition_involution' (m : ℕ) (p : Nat.Partition m) :
    conjugatePartition' m (conjugatePartition' m p) = p := by
  apply Nat.Partition.ext
  have h1 : (conjugatePartition' m (conjugatePartition' m p)).parts =
            (partitionToYoungDiagram' m (conjugatePartition' m p)).transpose.rowLens := rfl
  have hconj_parts : (conjugatePartition' m p).parts =
                     (partitionToYoungDiagram' m p).transpose.rowLens := rfl
  have hsorted_conj : ((conjugatePartition' m p).parts.sort (· ≥ ·)) =
                      (partitionToYoungDiagram' m p).transpose.rowLens := by
    rw [hconj_parts]
    have hrl_sorted : (partitionToYoungDiagram' m p).transpose.rowLens.SortedGE :=
      (partitionToYoungDiagram' m p).transpose.rowLens_sorted
    exact sorted_list_sort_eq _ hrl_sorted
  have h2 : partitionToYoungDiagram' m (conjugatePartition' m p) =
            (partitionToYoungDiagram' m p).transpose := by
    unfold partitionToYoungDiagram'
    simp only [hsorted_conj]
    exact YoungDiagram.ofRowLens_to_rowLens_eq_self
  rw [h1, h2, YoungDiagram.transpose_transpose]
  unfold partitionToYoungDiagram'
  rw [YoungDiagram.rowLens_ofRowLens_eq_self (parts_sort_pos' m p)]
  exact Multiset.sort_eq p.parts (· ≥ ·)

lemma restricted_card_eq_atMostKParts (n k : ℕ) :
    #(Nat.Partition.restricted n (· ≤ k)) = partitionCountAtMostKParts n k := by
  have hlhs : #(Nat.Partition.restricted n (· ≤ k)) =
              (Finset.univ.filter (fun p : Nat.Partition n => ∀ i ∈ p.parts, i ≤ k)).card := rfl
  have hrhs : partitionCountAtMostKParts n k =
              (Finset.univ.filter (fun p : Nat.Partition n => p.parts.card ≤ k)).card := by
    simp [partitionCountAtMostKParts, Nat.card, Fintype.card_subtype]
  rw [hlhs, hrhs]
  apply Finset.card_bij (fun p _ => conjugatePartition' n p)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact conjugatePartition_parts_card_le' n k p hp
  · intro p1 _ p2 _ heq
    have h1 : conjugatePartition' n (conjugatePartition' n p1) =
              conjugatePartition' n (conjugatePartition' n p2) := by rw [heq]
    rw [conjugatePartition_involution', conjugatePartition_involution'] at h1
    exact h1
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    use conjugatePartition' n q
    exact ⟨conjugatePartition_all_parts_le' n k q hq, conjugatePartition_involution' n q⟩

/-- The limit of q-binomial coefficients equals the generating function for
    partitions with at most k parts.

    This is the second equality in Proposition prop.pars.qbinom.lim1:
    ∑_{n ∈ ℕ} (p₀(n) + p₁(n) + ... + pₖ(n)) qⁿ = ∏_{i=1}^{k} 1/(1 - qⁱ)

    Combined with Theorem thm.pars.main-gf-0n from the partition generating functions section. -/
theorem qBinomial_limit_eq_partition_gf (k : ℕ) :
    ∏ i ∈ range k, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (i + 1))⁻¹ =
    PowerSeries.mk fun n => (partitionCountAtMostKParts n k : ℚ) := by
  rw [prod_inv_eq_restricted_gf]
  ext n
  simp only [PowerSeries.coeff_mk]
  rw [restricted_card_eq_atMostKParts]

end Limits

end QBinomialRec

end AlgebraicCombinatorics
