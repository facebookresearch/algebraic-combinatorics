/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# q-Binomial Coefficients: Basic Definitions and Properties

This file introduces q-binomial coefficients (also known as Gaussian binomial coefficients)
and their basic properties. The q-binomial coefficient `⟦n;k⟧_q` is a polynomial in `q`
that serves as a q-analogue of the ordinary binomial coefficient.

**This file provides the canonical definition of q-binomial coefficients for this project.**

## Main Definitions

* `qInt`: The q-integer `[n]_q = 1 + q + q^2 + ... + q^(n-1)` (Definition 11.3.1)
* `qFactorial`: The q-factorial `[n]_q! = [1]_q * [2]_q * ... * [n]_q` (Definition 11.3.1)
* `qBinomial`: The q-binomial coefficient `⟦n;k⟧_q` (Definition 11.2.1) — **canonical definition**
* `qBinomialPoly`: The q-binomial coefficient as a polynomial in `ℤ[X]`
* `monotoneFunctions`: The set of monotone functions from `Fin k` to `Fin (m + 1)`

## Main Results

* `qBinomial_eq_sum_increasing_tuples`: Definition as sum over weakly increasing tuples
  (Proposition 11.2.1(a))
* `qBinomial_eq_partition_gf`: Equivalence to partition generating function
  (Definition 11.2.1(a))
* `qBinomial_eq_sum_subsets`: Alternative expression as sum over subsets (Proposition 11.2.1(b))
  -- Proved in `AlgebraicCombinatorics/Partitions/QBinomialFormulas.lean`
* `qBinomial_one_eq_binomial`: At q=1, we recover ordinary binomial coefficients
  (Proposition 11.2.1(c))
* `qBinomial_zero_of_lt`: q-binomial is zero when k > n (Proposition 11.2.2)
* `qBinomial_n_zero`: `⟦n;0⟧_q = 1` (Proposition 11.2.3)
* `qBinomial_n_n`: `⟦n;n⟧_q = 1` (Proposition 11.2.3)
* `qBinomial_rec_left`: Recurrence `⟦n;k⟧_q = q^(n-k) * ⟦n-1;k-1⟧_q + ⟦n-1;k⟧_q` (for 0 < k)
  (Theorem 11.2.4(a))
* `qBinomial_rec_right`: Recurrence `⟦n;k⟧_q = ⟦n-1;k-1⟧_q + q^k * ⟦n-1;k⟧_q` (for 0 < k)
  (Theorem 11.2.4(b))
* `qBinomial_quot_formula`: Product formula for q-binomial (Theorem thm.pars.qbinom.quot1(a))
* `qBinomial_eq_prod_quot`: Quotient formula for q-binomial (Theorem thm.pars.qbinom.quot1(b))
* `qInt_eq_geom_sum`: `[n]_q = (1 - q^n) / (1 - q)` (Remark 11.3.2)
* `qBinomial_eq_qFactorial_quot`: `⟦n;k⟧_q = [n]_q! / ([k]_q! * [n-k]_q!)` (Theorem 11.2.6)
* `qBinomial_symm`: Symmetry `⟦n;k⟧_q = ⟦n;n-k⟧_q` (Proposition 11.2.7)
* `card_partitions_with_parts_and_largest`: Counting partitions (Proposition 11.1.1)

## Implementation Notes

The q-binomial coefficient is defined via the sum over monotone tuples (Proposition 11.2.1(a)):
  `⟦n;k⟧_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ iₖ ≤ n-k} q^(i₁ + i₂ + ... + iₖ)`

This is equivalent to the generating function for partitions fitting in a k × (n-k) box
(Definition 11.2.1(a)), but the monotone tuple formulation is more directly computable
and avoids the need to sum over partitions of varying sizes.

We work over a general commutative semiring `R` with an element `q`, though the polynomial
version over `ℤ[q]` is the primary object of interest.

### Equivalent Formulations

The q-binomial coefficient has several equivalent definitions:

1. **Monotone function sum** (this definition): `∑_{f monotone} q^(∑ᵢ f(i))`
   See `qBinomial_eq_sum_increasing_tuples`.

2. **Subset sum formula**: `∑_{S ⊆ [n], |S|=k} q^(sum(S) - (1+2+...+k))`
   See `qBinomial_eq_sum_subsets` in `Partitions/QBinomialFormulas.lean`.

3. **q-Pascal recurrence**: `[n;k]_q = [n-1;k-1]_q + q^k · [n-1;k]_q`
   See `qBinomial_rec_right` (and `qBinomial_rec_left` for the dual form).

4. **q-factorial quotient**: `[n]_q! / ([k]_q! · [n-k]_q!)`
   See `qBinomial_eq_qFactorial_quot`.

Note: The file `Partitions/QBinomialFormulas.lean` defines equivalent versions of `qBinomial`
using the q-Pascal recurrence in the sub-namespace `AlgebraicCombinatorics.QBinomialRec`.
The file `SignedCounting/AlternatingSums.lean` defines a local version as `Polynomial ℤ`
in the namespace `AlgebraicCombinatorics.SignedCounting`. Both are proven equivalent to
this canonical definition via the theorems listed above.

## References

* Darij Grinberg, *Algebraic Combinatorics*, Section 11.2-11.3
* [Kac-Cheung, *Quantum Calculus*, Chapters 5-7]
* [Stanley, *Enumerative Combinatorics Vol. 1*]

## Tags

q-binomial, Gaussian binomial coefficient, q-integer, q-factorial, partition
-/

namespace AlgebraicCombinatorics

open Finset Polynomial BigOperators Nat

/-! ## q-Integers and q-Factorials -/

section QIntFact

variable {R : Type*} [CommSemiring R]

/-- The q-integer `[n]_q = 1 + q + q^2 + ... + q^(n-1)`.
This is a q-analogue of the natural number n, since `[n]_1 = n`.

See Definition 11.3.1(a) in the source. -/
def qInt (n : ℕ) (q : R) : R := ∑ i ∈ range n, q ^ i

/-- The q-factorial `[n]_q! = [1]_q * [2]_q * ... * [n]_q`.
This is a q-analogue of n!, since `[n]_1! = n!`.

See Definition 11.3.1(b) in the source. -/
def qFactorial (n : ℕ) (q : R) : R := ∏ i ∈ range n, qInt (i + 1) q

@[simp]
theorem qInt_zero (q : R) : qInt 0 q = 0 := by
  simp [qInt]

@[simp]
theorem qInt_one (q : R) : qInt 1 q = 1 := by
  simp [qInt]

@[simp]
theorem qInt_two (q : R) : qInt 2 q = 1 + q := by
  simp [qInt, sum_range_succ]

theorem qInt_succ (n : ℕ) (q : R) : qInt (n + 1) q = qInt n q + q ^ n := by
  simp [qInt, sum_range_succ]

/-- The q-integer satisfies `[n]_1 = n`.
See Remark 11.3.2 in the source. -/
@[simp]
theorem qInt_one_eq (n : ℕ) : qInt n (1 : R) = n := by
  simp [qInt]

@[simp]
theorem qFactorial_zero (q : R) : qFactorial 0 q = 1 := by
  simp [qFactorial]

@[simp]
theorem qFactorial_one (q : R) : qFactorial 1 q = 1 := by
  simp [qFactorial, qInt_one]

theorem qFactorial_succ (n : ℕ) (q : R) :
    qFactorial (n + 1) q = qFactorial n q * qInt (n + 1) q := by
  simp [qFactorial, prod_range_succ]

/-- The q-factorial satisfies `[n]_1! = n!`.
See Remark 11.3.2 in the source. -/
@[simp]
theorem qFactorial_one_eq (n : ℕ) : qFactorial n (1 : R) = n ! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qFactorial_succ, ih, qInt_one_eq, Nat.factorial_succ]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- The q-integer as a rational function: `[n]_q = (1 - q^n) / (1 - q)`.
This holds in any ring where `1 - q` is invertible, or as formal power series.

See Remark 11.3.2 in the source. -/
theorem qInt_eq_geom_sum {R : Type*} [CommRing R] (n : ℕ) (q : R) :
    (1 - q) * qInt n q = 1 - q ^ n := by
  induction n with
  | zero => simp [qInt]
  | succ n ih =>
    rw [qInt_succ, mul_add, ih, pow_succ]
    ring

/-- Helper: qFactorial n = (∏ i ∈ range k, qInt (n - i) q) * qFactorial (n - k) when k ≤ n.

This is the key splitting lemma for the factorial form of the q-binomial coefficient.
It states that [n]_q! can be split as:
  [n]_q! = [n]_q · [n-1]_q · ... · [n-k+1]_q · [n-k]_q!
-/
lemma qFactorial_split (n k : ℕ) (hk : k ≤ n) (q : R) :
    qFactorial n q = (∏ i ∈ range k, qInt (n - i) q) * qFactorial (n - k) q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    rw [prod_range_succ, ih hk']
    have h1 : n - k ≥ 1 := by omega
    have h2 : n - k - 1 = n - (k + 1) := by omega
    have h3 : qFactorial (n - k) q = qFactorial (n - k - 1) q * qInt (n - k) q := by
      have hpos : n - k - 1 + 1 = n - k := by omega
      conv_lhs => rw [← hpos, qFactorial_succ]
      simp only [hpos]
    rw [h3, h2]
    ring

/-- qInt n q ≠ 0 when q^n ≠ 1 (i.e., when q is not an n-th root of unity). -/
lemma qInt_ne_zero {R : Type*} [Field R] (n : ℕ) (q : R) (hq : q ^ n ≠ 1) :
    qInt n q ≠ 0 := by
  intro h
  have h1 : (1 - q) * qInt n q = 0 := by rw [h]; ring
  rw [qInt_eq_geom_sum] at h1
  have h2 : q ^ n = 1 := (sub_eq_zero.mp h1).symm
  exact hq h2

/-- qFactorial n q ≠ 0 when q^i ≠ 1 for i = 1, ..., n. -/
lemma qFactorial_ne_zero {R : Type*} [Field R] (n : ℕ) (q : R)
    (hq : ∀ i ∈ range n, q ^ (i + 1) ≠ 1) : qFactorial n q ≠ 0 := by
  simp only [qFactorial, prod_ne_zero_iff]
  intro i hi
  exact qInt_ne_zero (i + 1) q (hq i hi)

end QIntFact

/-! ## q-Binomial Coefficients -/

section QBinomial

variable {R : Type*} [CommSemiring R]

/-- A partition fits in a k × m box if it has at most k parts,
each of size at most m. -/
def PartitionFitsInBox (n : ℕ) (k m : ℕ) (μ : Nat.Partition n) : Prop :=
  μ.parts.card ≤ k ∧ ∀ p ∈ μ.parts, p ≤ m

/-- The set of monotone functions from `Fin k` to `Fin (m + 1)`, representing
weakly increasing k-tuples with entries in `{0, 1, ..., m}`. -/
def monotoneFunctions (k m : ℕ) : Finset (Fin k → Fin (m + 1)) :=
  Finset.univ.filter fun f => Monotone f

/-- The q-binomial coefficient `⟦n;k⟧_q`, defined via the sum over monotone tuples:
  `⟦n;k⟧_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ iₖ ≤ n-k} q^(i₁ + i₂ + ... + iₖ)`

This is equivalent to the generating function for partitions fitting in a k × (n-k) box
(see `qBinomial_eq_partition_gf`).

See Definition 11.2.1(a) and Proposition 11.2.1(a) in the source. -/
noncomputable def qBinomial (n k : ℕ) (q : R) : R :=
  if k ≤ n then
    ∑ f ∈ monotoneFunctions k (n - k), q ^ (∑ i, (f i).val)
  else 0

/-- The q-binomial coefficient as a polynomial in `ℤ[X]`.

This is the generating function for partitions fitting in a k × (n-k) box:
  `⟦n;k⟧_q = ∑_{λ fits in k × (n-k) box} q^|λ|`

See Definition 11.2.1(a) in the source. -/
noncomputable def qBinomialPoly (n k : ℕ) : ℤ[X] :=
  if k ≤ n then
    ∑ f ∈ monotoneFunctions k (n - k), (X : ℤ[X]) ^ (∑ i, (f i).val)
  else 0

/-! ### Alternative Characterizations -/

/-- The q-binomial is defined as a sum over weakly increasing tuples:
`⟦n;k⟧_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ iₖ ≤ n-k} q^(i₁ + i₂ + ... + iₖ)`

This is the definition, restated for clarity.

See Proposition 11.2.1(a) in the source. -/
theorem qBinomial_eq_sum_increasing_tuples (n k : ℕ) (hk : k ≤ n) (q : R) :
    qBinomial n k q = ∑ f ∈ monotoneFunctions k (n - k), q ^ (∑ i, (f i).val) := by
  simp only [qBinomial, ite_eq_left hk]

/-- The set of partitions of n fitting in a k × m box.

    **Argument order:** This definition uses `(n k m : ℕ)` where:
    - `n` is the partition size
    - `k` is the maximum number of parts (length ≤ k)
    - `m` is the maximum part size (largest part ≤ m)

    This is the canonical definition of `partitionsInBox` for this project.
    The definition `QBinomialRec.partitionsInBox` in `QBinomialFormulas.lean`
    uses the same argument order. -/
def partitionsInBox (n k m : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter fun μ => μ.parts.card ≤ k ∧ ∀ p ∈ μ.parts, p ≤ m

/-- Helper lemma: filtering zeros from a multiset preserves the sum. -/
private lemma multiset_sum_filter_ne_zero (s : Multiset ℕ) :
    (s.filter (· ≠ 0)).sum = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases ha : a = 0
    · subst ha
      have : (0 ::ₘ s).filter (fun x => x ≠ 0) = s.filter (fun x => x ≠ 0) := by
        exact Multiset.filter_cons_of_neg s (by decide : ¬(0 ≠ 0))
      rw [this]; simp [ih]
    · have : (a ::ₘ s).filter (fun x => x ≠ 0) = a ::ₘ (s.filter (fun x => x ≠ 0)) := by
        exact Multiset.filter_cons_of_pos s ha
      rw [this]; simp [ih]

/-- Given a partition μ with parts ≤ m and at most k parts,
construct a monotone function by padding with zeros and sorting. -/
private noncomputable def partitionToMonotoneAux (k m s : ℕ) (μ : Nat.Partition s)
    (hcard : μ.parts.card ≤ k) (hparts : ∀ p ∈ μ.parts, p ≤ m) : Fin k → Fin (m + 1) := by
  let padded : Multiset ℕ := μ.parts + Multiset.replicate (k - μ.parts.card) 0
  let sorted : List ℕ := padded.sort (· ≤ ·)
  have hlen : sorted.length = k := by
    simp only [Multiset.length_sort, Multiset.card_add, Multiset.card_replicate, sorted, padded]
    omega
  exact fun i => ⟨sorted.getD i.val 0, by
    by_cases hi : i.val < sorted.length
    · have h := List.getD_eq_getElem sorted 0 hi
      rw [h]
      have hmem : sorted[i.val] ∈ sorted := List.getElem_mem hi
      have hmem' : sorted[i.val] ∈ padded := by rw [Multiset.mem_sort] at hmem; exact hmem
      rw [Multiset.mem_add] at hmem'
      cases hmem' with
      | inl h => exact Nat.lt_succ_of_le (hparts _ h)
      | inr h => simp only [Multiset.mem_replicate, ne_eq] at h; omega
    · simp only [List.getD_eq_default _ _ (Nat.not_lt.mp hi), Nat.zero_lt_succ]⟩

/-- The constructed monotone function is indeed monotone. -/
private lemma partitionToMonotoneAux_monotone (k m s : ℕ) (μ : Nat.Partition s)
    (hcard : μ.parts.card ≤ k) (hparts : ∀ p ∈ μ.parts, p ≤ m) :
    Monotone (partitionToMonotoneAux k m s μ hcard hparts) := by
  intro i j hij
  simp only [partitionToMonotoneAux, Fin.mk_le_mk]
  set padded := μ.parts + Multiset.replicate (k - μ.parts.card) 0
  set sorted := padded.sort (· ≤ ·)
  have hlen : sorted.length = k := by
    simp only [Multiset.length_sort, Multiset.card_add, Multiset.card_replicate, sorted, padded]
    omega
  by_cases hi : i.val < sorted.length
  · by_cases hj : j.val < sorted.length
    · rw [List.getD_eq_getElem sorted 0 hi, List.getD_eq_getElem sorted 0 hj]
      have hsorted : sorted.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
      exact List.Pairwise.rel_get_of_le hsorted hij
    · have hj' : j.val ≥ sorted.length := Nat.not_lt.mp hj
      rw [hlen] at hj'
      exact absurd j.isLt (Nat.not_lt.mpr hj')
  · have hi' : i.val ≥ sorted.length := Nat.not_lt.mp hi
    rw [hlen] at hi'
    exact absurd i.isLt (Nat.not_lt.mpr hi')

/-- The sum of the constructed function equals s. -/
private lemma partitionToMonotoneAux_sum (k m s : ℕ) (μ : Nat.Partition s)
    (hcard : μ.parts.card ≤ k) (hparts : ∀ p ∈ μ.parts, p ≤ m) :
    ∑ i, (partitionToMonotoneAux k m s μ hcard hparts i).val = s := by
  simp only [partitionToMonotoneAux]
  set padded := μ.parts + Multiset.replicate (k - μ.parts.card) 0
  set sorted := padded.sort (· ≤ ·)
  have hlen : sorted.length = k := by
    simp only [Multiset.length_sort, Multiset.card_add, Multiset.card_replicate, sorted, padded]
    omega
  have h1 : ∑ i : Fin k, sorted.getD i.val 0 = sorted.sum := by
    rw [← List.sum_ofFn]; congr 1
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro n hn1 hn2
      simp only [List.getElem_ofFn, List.getD_eq_getElem sorted 0 (by omega : n < sorted.length)]
  rw [h1]
  have h2 : sorted.sum = padded.sum := by
    have heq := Multiset.sort_eq padded (· ≤ ·)
    rw [← Multiset.sum_coe sorted, heq]
  rw [h2, Multiset.sum_add, Multiset.sum_replicate, smul_zero, add_zero]
  exact μ.parts_sum

/-- The multiset of function values equals the padded partition. -/
private lemma partitionToMonotoneAux_multiset (k m s : ℕ) (μ : Nat.Partition s)
    (hcard : μ.parts.card ≤ k) (hparts : ∀ p ∈ μ.parts, p ≤ m) :
    (↑(List.ofFn fun i => (partitionToMonotoneAux k m s μ hcard hparts i).val) : Multiset ℕ) =
    μ.parts + Multiset.replicate (k - μ.parts.card) 0 := by
  simp only [partitionToMonotoneAux]
  set padded := μ.parts + Multiset.replicate (k - μ.parts.card) 0
  set sorted := padded.sort (· ≤ ·)
  have hlen : sorted.length = k := by
    simp only [Multiset.length_sort, Multiset.card_add, Multiset.card_replicate, sorted, padded]
    omega
  have h_list_eq : List.ofFn (fun i : Fin k => sorted.getD i.val 0) = sorted := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro n hn1 hn2
      simp only [List.getElem_ofFn, List.getD_eq_getElem sorted 0 (by omega : n < sorted.length)]
  rw [h_list_eq]
  exact Multiset.sort_eq padded (· ≤ ·)

/-- Filtering the multiset of function values gives back the partition's parts. -/
private lemma partitionToMonotoneAux_roundtrip (k m s : ℕ) (μ : Nat.Partition s)
    (hcard : μ.parts.card ≤ k) (hparts : ∀ p ∈ μ.parts, p ≤ m) :
    (↑(List.ofFn fun i => (partitionToMonotoneAux k m s μ hcard hparts i).val) : Multiset ℕ).filter (· ≠ 0) = μ.parts := by
  rw [partitionToMonotoneAux_multiset, Multiset.filter_add]
  have h_filter_parts : μ.parts.filter (· ≠ 0) = μ.parts := by
    rw [Multiset.filter_eq_self]; intro x hx; exact (μ.parts_pos hx).ne'
  have h_filter_zeros : (Multiset.replicate (k - μ.parts.card) 0).filter (· ≠ 0) = 0 := by
    rw [Multiset.filter_eq_nil]; intro x hx
    simp only [Multiset.mem_replicate, ne_eq] at hx; simp [hx.2]
  rw [h_filter_parts, h_filter_zeros, add_zero]

/-- The key bijection lemma: for each s, the number of monotone functions with sum s
equals the number of partitions of s fitting in a k × m box.

This follows from the classical bijection between monotone functions and partitions:
- Forward: f ↦ partition whose parts are the nonzero values of f
- Backward: μ ↦ monotone function obtained by padding μ.parts to k values and sorting

This is equivalent to the stars-and-bars / lattice path correspondence. -/
lemma card_monotoneFunctions_sum_eq (k m s : ℕ) (_hs : s ≤ k * m) :
    ((monotoneFunctions k m).filter fun f => ∑ i, (f i).val = s).card =
    (partitionsInBox s k m).card := by
  apply Finset.card_bij
    (fun f hf => Nat.Partition.ofSums s (↑(List.ofFn fun i => (f i).val) : Multiset ℕ)
      (by simp only [Multiset.sum_coe, List.sum_ofFn]
          simp only [monotoneFunctions, mem_filter] at hf; exact hf.2))
  -- 1. Forward map lands in partitionsInBox
  · intro f hf
    simp only [monotoneFunctions, mem_filter] at hf ⊢
    simp only [partitionsInBox, mem_filter, mem_univ, true_and]
    constructor
    · simp only [Nat.Partition.ofSums_parts]
      calc (Multiset.filter (· ≠ 0) (↑(List.ofFn fun i => (f i).val))).card
          ≤ (↑(List.ofFn fun i => (f i).val) : Multiset ℕ).card :=
            Multiset.card_le_card (Multiset.filter_le _ _)
        _ = k := by simp only [Multiset.coe_card, List.length_ofFn]
    · intro p hp
      have hp' : p ∈ (↑(List.ofFn fun i => (f i).val) : Multiset ℕ).filter (· ≠ 0) := hp
      rw [Multiset.mem_filter, Multiset.mem_coe, List.mem_ofFn] at hp'
      obtain ⟨⟨i, hi⟩, hp2⟩ := hp'
      have : (f i).val < m + 1 := (f i).isLt; omega
  -- 2. Injectivity
  · intro f1 hf1 f2 hf2 heq
    simp only [monotoneFunctions, mem_filter] at hf1 hf2
    have h_filter_eq : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).filter (· ≠ 0) =
        (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).filter (· ≠ 0) := by
      have := congrArg Nat.Partition.parts heq
      simp only [Nat.Partition.ofSums_parts] at this; exact this
    have h_card_eq : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).card =
        (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).card := by
      simp only [Multiset.coe_card, List.length_ofFn]
    have h_multiset_eq : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ) =
        (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ) := by
      ext n
      by_cases hn : n = 0
      · subst hn
        have h1 : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).count 0 =
            k - ((↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).filter (· ≠ 0)).card := by
          have := Multiset.filter_add_not (· ≠ 0) (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ)
          have hc := congrArg Multiset.card this
          simp only [Multiset.card_add, Multiset.coe_card, List.length_ofFn] at hc
          have hf : ((↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).filter (fun x => ¬x ≠ 0)).card =
              (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).count 0 := by
            simp only [ne_eq, not_not, Multiset.count_eq_card_filter_eq, eq_comm]
          omega
        have h2 : (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).count 0 =
            k - ((↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).filter (· ≠ 0)).card := by
          have := Multiset.filter_add_not (· ≠ 0) (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ)
          have hc := congrArg Multiset.card this
          simp only [Multiset.card_add, Multiset.coe_card, List.length_ofFn] at hc
          have hf : ((↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).filter (fun x => ¬x ≠ 0)).card =
              (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).count 0 := by
            simp only [ne_eq, not_not, Multiset.count_eq_card_filter_eq, eq_comm]
          omega
        rw [h1, h2, h_filter_eq]
      · have h1 : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).count n =
            ((↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).filter (· ≠ 0)).count n := by
          symm; exact Multiset.count_filter_of_pos hn
        have h2 : (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).count n =
            ((↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).filter (· ≠ 0)).count n := by
          symm; exact Multiset.count_filter_of_pos hn
        rw [h1, h2, h_filter_eq]
    have h_sort_eq : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).sort (· ≤ ·) =
        (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).sort (· ≤ ·) := by rw [h_multiset_eq]
    have h_sorted1 : (↑(List.ofFn fun i => (f1 i).val) : Multiset ℕ).sort (· ≤ ·) =
        List.ofFn fun i => (f1 i).val := by
      rw [Multiset.coe_sort]; apply List.mergeSort_eq_self
      rw [List.pairwise_ofFn]; intro i j hij; exact hf1.1.2 (Fin.mk_le_mk.mpr (le_of_lt hij))
    have h_sorted2 : (↑(List.ofFn fun i => (f2 i).val) : Multiset ℕ).sort (· ≤ ·) =
        List.ofFn fun i => (f2 i).val := by
      rw [Multiset.coe_sort]; apply List.mergeSort_eq_self
      rw [List.pairwise_ofFn]; intro i j hij; exact hf2.1.2 (Fin.mk_le_mk.mpr (le_of_lt hij))
    rw [h_sorted1, h_sorted2] at h_sort_eq
    funext i; exact Fin.val_inj.mp (congrFun (List.ofFn_inj.mp h_sort_eq) i)
  -- 3. Surjectivity
  · intro μ hμ
    simp only [partitionsInBox, mem_filter, mem_univ, true_and] at hμ
    refine ⟨partitionToMonotoneAux k m s μ hμ.1 hμ.2, ?_, ?_⟩
    · simp only [monotoneFunctions, mem_filter, mem_univ, true_and]
      exact ⟨partitionToMonotoneAux_monotone k m s μ hμ.1 hμ.2, partitionToMonotoneAux_sum k m s μ hμ.1 hμ.2⟩
    · apply Nat.Partition.ext
      simp only [Nat.Partition.ofSums_parts]
      exact partitionToMonotoneAux_roundtrip k m s μ hμ.1 hμ.2

/-- The q-binomial coefficient equals the generating function for partitions
fitting in a k × (n-k) box.

Note: This requires k ≤ n because when k > n, the LHS is 0 by definition
but the RHS would count the empty partition (giving 1). In the mathematical
definition over ℤ, when k > n, n - k < 0, so no partition has largest part ≤ n - k.
But in Lean with ℕ subtraction, n - k = 0 when k > n, and the empty partition
vacuously satisfies "all parts ≤ 0".

See Definition 11.2.1(a) in the source. -/
theorem qBinomial_eq_partition_gf (n k : ℕ) (hk : k ≤ n) (q : R) :
    qBinomial n k q = ∑ m ∈ range (k * (n - k) + 1),
      (partitionsInBox m k (n - k)).card • q ^ m := by
  simp only [qBinomial, ite_eq_left hk]
  -- Rewrite LHS by grouping by sum
  have hbound : ∀ f ∈ monotoneFunctions k (n - k), ∑ i, (f i).val ∈ range (k * (n - k) + 1) := by
    intro f _
    simp only [mem_range]
    calc ∑ i, (f i).val ≤ ∑ _ : Fin k, (n - k) := by
          apply Finset.sum_le_sum
          intro i _
          exact Nat.lt_succ_iff.mp (f i).isLt
      _ = k * (n - k) := by simp [Finset.sum_const]
      _ < k * (n - k) + 1 := Nat.lt_succ_self _
  -- Use sum_fiberwise
  conv_lhs => rw [← Finset.sum_fiberwise_of_maps_to hbound]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [mem_range] at hs
  -- The fiber sum is ∑ f with sum = s, q^s = (count) • q^s
  have hcard : ((monotoneFunctions k (n - k)).filter fun f => ∑ i, (f i).val = s).card =
      (partitionsInBox s k (n - k)).card := by
    apply card_monotoneFunctions_sum_eq
    omega
  -- Simplify the fiber sum
  have h1 : ∑ f ∈ (monotoneFunctions k (n - k)).filter (fun f => ∑ i, (f i).val = s),
      q ^ (∑ i, (f i).val) =
      ∑ f ∈ (monotoneFunctions k (n - k)).filter (fun f => ∑ i, (f i).val = s), q ^ s := by
    apply Finset.sum_congr rfl
    intro f hf
    simp only [mem_filter] at hf
    rw [hf.2]
  rw [h1, Finset.sum_const, hcard]

/-! ### Basic Properties -/

/-! #### Helper definitions and lemmas for counting monotone functions -/

/-- Forward map: monotone function to Sym (multiset of values) -/
private def monotoneToSym (k m : ℕ) (f : Fin k → Fin (m + 1)) : Sym (Fin (m + 1)) k :=
  ⟨Finset.univ.val.map f, by simp⟩

/-- Backward map: Sym to monotone function via sorting -/
private noncomputable def symToMonotone (k m : ℕ) (s : Sym (Fin (m + 1)) k) : Fin k → Fin (m + 1) :=
  fun i => ((s : Multiset (Fin (m + 1))).sort (· ≤ ·)).get ⟨i, by
    simp only [Multiset.length_sort]
    have : (s : Multiset (Fin (m + 1))).card = k := s.2
    omega⟩

/-- The backward map produces a monotone function -/
private theorem symToMonotone_monotone (k m : ℕ) (s : Sym (Fin (m + 1)) k) :
    Monotone (symToMonotone k m s) := by
  intro i j hij
  simp only [symToMonotone, List.get_eq_getElem]
  have h : ((s : Multiset (Fin (m + 1))).sort (· ≤ ·)).Pairwise (· ≤ ·) := by
    have h := @Multiset.pairwise_sort (Fin (m + 1)) (· ≤ ·) _ _ _ _ (s := (s : Multiset (Fin (m + 1))))
    convert h
  exact List.Pairwise.rel_get_of_le h hij

/-- For a monotone function, sorting the multiset of values gives back the function -/
private theorem monotone_sort_eq (k m : ℕ) (f : Fin k → Fin (m + 1)) (hf : Monotone f) :
    symToMonotone k m (monotoneToSym k m f) = f := by
  ext i
  simp only [symToMonotone, monotoneToSym, Sym.coe_mk, List.get_eq_getElem, Fin.val_inj]
  have h_sorted : ((List.finRange k).map f).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    apply List.Pairwise.imp _ (List.pairwise_lt_finRange k)
    intro a b hab
    exact hf (le_of_lt hab)
  have h_eq : (Finset.univ.val.map f).sort (· ≤ ·) = (List.finRange k).map f := by
    have h1 : (Finset.univ : Finset (Fin k)).val = ↑(List.finRange k) := rfl
    rw [h1, Multiset.map_coe, Multiset.coe_sort, List.mergeSort_eq_self _ h_sorted]
  simp only [h_eq, List.getElem_map, List.getElem_finRange, Fin.cast_mk]

set_option backward.isDefEq.respectTransparency false in
/-- For any Sym, converting to monotone function and back gives the same Sym -/
private theorem sym_monotone_sort_eq (k m : ℕ) (s : Sym (Fin (m + 1)) k) :
    monotoneToSym k m (symToMonotone k m s) = s := by
  ext
  simp only [monotoneToSym, symToMonotone, Sym.coe_mk]
  have h_len : ((s : Multiset (Fin (m + 1))).sort (· ≤ ·)).length = k := by
    simp only [Multiset.length_sort]
    exact s.2
  have h_eq : ↑((s : Multiset (Fin (m + 1))).sort (· ≤ ·)) = (s : Multiset (Fin (m + 1))) := by
    exact Multiset.sort_eq (s : Multiset (Fin (m + 1))) (· ≤ ·)
  have h1 : (Finset.univ : Finset (Fin k)).val = ↑(List.finRange k) := rfl
  rw [h1, Multiset.map_coe]
  conv_rhs => rw [← h_eq]
  set sorted := (s : Multiset (Fin (m + 1))).sort (· ≤ ·) with h_sorted_def
  have h_len' : sorted.length = k := h_len
  have h_list : (List.finRange k).map (fun (x : Fin k) => sorted.get ⟨x.val, by omega⟩) = sorted := by
    apply List.ext_getElem
    · simp [h_len']
    · intro n h1' h2
      simp only [List.getElem_map, List.getElem_finRange, List.get_eq_getElem]
      rfl
  rw [h_list]

/-- The equivalence between monotone functions and Sym -/
private noncomputable def monotoneEquivSym (k m : ℕ) :
    { f : Fin k → Fin (m + 1) // Monotone f } ≃ Sym (Fin (m + 1)) k where
  toFun := fun ⟨f, _⟩ => monotoneToSym k m f
  invFun := fun s => ⟨symToMonotone k m s, symToMonotone_monotone k m s⟩
  left_inv := fun ⟨f, hf⟩ => by simp [monotone_sort_eq k m f hf]
  right_inv := fun s => sym_monotone_sort_eq k m s

/-- The cardinality of monotone functions equals the binomial coefficient -/
private theorem card_monotoneFunctions_eq_choose' (k m : ℕ) :
    (monotoneFunctions k m).card = Nat.choose (k + m) k := by
  have h1 : (monotoneFunctions k m).card = Fintype.card { f : Fin k → Fin (m + 1) // Monotone f } := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact {
      toFun := fun ⟨f, hf⟩ => ⟨f, by simp [monotoneFunctions] at hf; exact hf⟩
      invFun := fun ⟨f, hf⟩ => ⟨f, by simp [monotoneFunctions]; exact hf⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
  rw [h1]
  have h2 : Fintype.card (Sym (Fin (m + 1)) k) = Nat.choose (m + k) k := by
    rw [Sym.card_sym_eq_choose]
    simp [Fintype.card_fin]
  rw [add_comm k m, ← h2]
  exact Fintype.card_congr (monotoneEquivSym k m)

/-- At q = 1, the q-binomial coefficient equals the ordinary binomial coefficient.

See Proposition 11.2.1(c) in the source. -/
@[simp]
theorem qBinomial_one_eq_binomial (n k : ℕ) : qBinomial n k (1 : R) = Nat.choose n k := by
  by_cases hk : k ≤ n
  · unfold qBinomial
    simp only [ite_eq_left hk, one_pow, Finset.sum_const]
    rw [card_monotoneFunctions_eq_choose']
    have h : k + (n - k) = n := Nat.add_sub_cancel' hk
    rw [h]
    simp
  · unfold qBinomial
    simp only [ite_eq_right hk]
    rw [Nat.choose_eq_zero_of_lt (by omega : n < k)]
    simp

/-- The q-binomial coefficient is zero when k > n.

See Proposition 11.2.2 in the source. -/
@[simp]
theorem qBinomial_zero_of_lt (n k : ℕ) (hk : n < k) (q : R) : qBinomial n k q = 0 := by
  simp [qBinomial, Nat.not_le.mpr hk]

/-- `⟦n;0⟧_q = 1` for all n.

See Proposition 11.2.3 in the source. -/
@[simp]
theorem qBinomial_n_zero (n : ℕ) (q : R) : qBinomial n 0 q = 1 := by
  simp only [qBinomial, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  -- Show monotoneFunctions 0 n = Finset.univ
  have h1 : monotoneFunctions 0 n = Finset.univ := by
    ext f
    simp only [monotoneFunctions, mem_filter, mem_univ, true_and, iff_true]
    intro i
    exact Fin.elim0 i
  rw [h1]
  simp

/-- `⟦n;n⟧_q = 1` for all n.

See Proposition 11.2.3 in the source. -/
@[simp]
theorem qBinomial_n_n (n : ℕ) (q : R) : qBinomial n n q = 1 := by
  unfold qBinomial
  simp only [le_refl, ↓reduceIte]
  conv_lhs => rw [Nat.sub_self]
  -- monotoneFunctions n 0 is singleton {fun _ => 0} since Fin 1 has one element
  have h_singleton : (monotoneFunctions n 0) = {fun _ => 0} := by
    ext f
    simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro _
      funext x
      exact @Subsingleton.elim _ Fin.subsingleton_one (f x) 0
    · intro hf
      rw [hf]
      exact fun _ _ _ => le_refl _
  rw [h_singleton, sum_singleton]
  simp only [Fin.val_zero, sum_const_zero, pow_zero]

/-! ### Recurrence Relations -/

/-- First recurrence relation for q-binomial coefficients:
`⟦n;k⟧_q = q^(n-k) * ⟦n-1;k-1⟧_q + ⟦n-1;k⟧_q`

This is a q-analogue of Pascal's identity.

Note: The hypothesis `0 < k` is necessary because in Lean with `k : ℕ`, we have `k - 1 = 0`
when `k = 0` due to saturating subtraction. This would make the RHS equal to
`q^n * qBinomial (n-1) 0 q + qBinomial (n-1) 0 q = q^n + 1`, which is not equal to
`qBinomial n 0 q = 1` in general.

See Theorem 11.2.4(a) in the source. The source handles k ∈ ℤ with the convention that
(n choose k)_q = 0 for negative k, and explicitly notes that when k = 0, the identity
reduces to 1 = q^(n-k) * 0 + 1. -/
theorem qBinomial_rec_left (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k) (q : R) :
    qBinomial n k q = q ^ (n - k) * qBinomial (n - 1) (k - 1) q + qBinomial (n - 1) k q := by
  by_cases hkn : k ≤ n
  · -- Case k ≤ n
    have hk1 : k - 1 ≤ n - 1 := Nat.sub_le_sub_right hkn 1
    simp only [qBinomial, hkn, hk1, ↓reduceIte]
    have hdim1 : (n - 1) - (k - 1) = n - k := by omega

    by_cases hkn' : k ≤ n - 1
    · -- Subcase k < n (both RHS terms contribute)
      simp only [hkn', ↓reduceIte]
      have hdim2 : (n - 1) - k = n - k - 1 := by omega
      rw [hdim1, hdim2]
      -- The main combinatorial identity requires showing that monotoneFunctions k (n-k)
      -- splits into two parts based on whether f(k-1) = n-k or f(k-1) < n-k.
      -- Type 1 (f(k-1) = n-k) bijects to monotoneFunctions (k-1) (n-k) with sum offset n-k
      -- Type 2 (f(k-1) < n-k) bijects to monotoneFunctions k (n-k-1) with same sum
      -- This is a standard bijection argument in q-binomial theory.
      set m := n - k with hm_def
      have hm_pos : 0 < m := by omega
      -- Define partition sets
      let lastIdx : Fin k := ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩
      let maxVal : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      let S_max := (monotoneFunctions k m).filter fun f => f lastIdx = maxVal
      let S_below := (monotoneFunctions k m).filter fun f => (f lastIdx).val < m
      -- Partition property
      have h_partition : monotoneFunctions k m = S_max ∪ S_below := by
        ext f
        simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_union, S_max, S_below, lastIdx, maxVal]
        constructor
        · intro hf
          have h_bound := (f ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).isLt
          by_cases h : (f ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).val = m
          · left; exact ⟨hf, Fin.ext h⟩
          · right; exact ⟨hf, by omega⟩
        · intro h
          rcases h with ⟨hf, _⟩ | ⟨hf, _⟩ <;> exact hf
      -- Disjointness
      have h_disjoint : Disjoint S_max S_below := by
        simp only [Finset.disjoint_iff_ne, S_max, S_below, mem_filter, lastIdx, maxVal]
        intro f hf g hg heq
        rw [heq] at hf
        simp only [Fin.ext_iff] at hf
        omega
      rw [h_partition, sum_union h_disjoint]
      congr 1
      -- Part 1: S_max sum equals q^m * sum over monotoneFunctions (k-1) m
      · rw [mul_sum]
        refine sum_bij' 
          (fun f _ => fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le k 1)⟩)
          (fun g _ => fun i => if h : i.val < k - 1 then g ⟨i.val, h⟩ else maxVal)
          ?_ ?_ ?_ ?_ ?_
        -- hi: forward lands in target
        · intro f hf
          simp only [S_max, mem_filter, monotoneFunctions] at hf
          simp only [monotoneFunctions, mem_filter, mem_univ, true_and]
          intro i j hij
          exact hf.1.2 (Fin.mk_le_mk.mpr hij)
        -- hj: backward lands in source
        · intro g hg
          simp only [monotoneFunctions, mem_filter, mem_univ, true_and] at hg
          simp only [S_max, mem_filter, monotoneFunctions, mem_univ, true_and, lastIdx, maxVal]
          constructor
          · intro i j hij
            beta_reduce
            split_ifs with hi hj hj
            · exact hg (Fin.mk_le_mk.mpr hij)
            · exact Nat.lt_succ_iff.mp (g ⟨i.val, hi⟩).isLt
            · omega
            · exact le_refl _
          · simp only [Nat.lt_irrefl, dite_false]
        -- left_inv
        · intro f hf
          simp only [S_max, mem_filter, lastIdx, maxVal] at hf
          funext i
          by_cases hi : i.val < k - 1
          · simp only [hi, dite_true]
          · simp only [hi, dite_false]
            have h1 := i.isLt
            have h2 : i.val = k - 1 := by omega
            have hi' : i = ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩ := Fin.ext h2
            rw [hi', hf.2]
        -- right_inv
        · intro g hg
          funext i
          simp only [i.isLt, dite_true]
        -- sum relation
        · intro f hf
          simp only [S_max, mem_filter, lastIdx, maxVal] at hf
          have h_sum : ∑ i : Fin k, (f i).val = 
              m + ∑ i : Fin (k - 1), (f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le k 1)⟩).val := by
            have h_decomp : (Finset.univ : Finset (Fin k)) = 
                (Finset.univ.filter (fun i => i.val < k - 1)) ∪ 
                (Finset.univ.filter (fun i => i.val = k - 1)) := by
              ext i; simp only [mem_univ, mem_union, mem_filter, true_and, true_iff]; omega
            have h_disj : Disjoint (Finset.univ.filter (fun i : Fin k => i.val < k - 1))
                                   (Finset.univ.filter (fun i : Fin k => i.val = k - 1)) := by
              simp only [disjoint_filter]; intro _ _ h1 h2; omega
            have h_last_eq : (Finset.univ : Finset (Fin k)).filter (fun i => i.val = k - 1) = 
                {⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩} := by
              ext i; simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
            calc ∑ i : Fin k, (f i).val 
                = ∑ i ∈ (Finset.univ.filter (fun i => i.val < k - 1)) ∪ 
                       (Finset.univ.filter (fun i => i.val = k - 1)), (f i).val := by rw [← h_decomp]
              _ = ∑ i ∈ Finset.univ.filter (fun i => i.val < k - 1), (f i).val + 
                  ∑ i ∈ Finset.univ.filter (fun i => i.val = k - 1), (f i).val := sum_union h_disj
              _ = ∑ i ∈ Finset.univ.filter (fun i => i.val < k - 1), (f i).val + 
                  (f ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).val := by rw [h_last_eq, sum_singleton]
              _ = ∑ i ∈ Finset.univ.filter (fun i => i.val < k - 1), (f i).val + m := by
                    simp only [hf.2, Fin.val_mk]
              _ = m + ∑ i ∈ Finset.univ.filter (fun i => i.val < k - 1), (f i).val := by ring
              _ = m + ∑ i : Fin (k - 1), (f ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le k 1)⟩).val := by
                    congr 1
                    have h_filter_eq : (Finset.univ : Finset (Fin k)).filter (fun i => i.val < k - 1) = 
                        Finset.univ.image (fun i : Fin (k - 1) => 
                          ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le k 1)⟩) := by
                      ext i
                      simp only [mem_filter, mem_univ, true_and, mem_image]
                      constructor
                      · intro hi; exact ⟨⟨i.val, hi⟩, by ext; rfl⟩
                      · intro ⟨j, hj⟩; simp only [Fin.ext_iff] at hj; rw [← hj]; exact j.isLt
                    rw [h_filter_eq, sum_image]
                    intro i _ j _ hij
                    simp only [Fin.mk.injEq] at hij
                    exact Fin.ext hij
          rw [h_sum, pow_add, mul_comm]
      -- Part 2: S_below sum equals sum over monotoneFunctions k (m-1)
      · have hm' : m - 1 + 1 = m := by omega
        refine sum_bij'
          (fun f hf => fun i => ⟨(f i).val, by
            simp only [S_below, mem_filter, monotoneFunctions, lastIdx] at hf
            have h_mono := hf.1.2
            have h_last := hf.2
            have h_bound : (f i).val ≤ (f ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).val := 
              h_mono (by simp only [Fin.le_def]; omega)
            omega⟩)
          (fun g _ => fun i => ⟨(g i).val, by have h := (g i).isLt; omega⟩)
          ?_ ?_ ?_ ?_ ?_
        -- hi: forward lands in target
        · intro f hf
          simp only [monotoneFunctions, mem_filter, mem_univ, true_and]
          simp only [S_below, mem_filter, monotoneFunctions] at hf
          intro i j hij
          simp only [Fin.mk_le_mk]
          exact hf.1.2 hij
        -- hj: backward lands in source
        · intro g hg
          simp only [monotoneFunctions, mem_filter, mem_univ, true_and] at hg
          simp only [S_below, mem_filter, monotoneFunctions, mem_univ, true_and, lastIdx]
          constructor
          · intro i j hij
            simp only [Fin.mk_le_mk]
            exact hg hij
          · have h := (g ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).isLt
            omega
        -- left_inv
        · intro f hf; funext i; rfl
        -- right_inv
        · intro g hg; funext i; rfl
        -- sum relation
        · intro f hf; rfl
    · -- Subcase k = n
      have hkn_eq : k = n := by omega
      have hn1k : n - 1 < k := Nat.not_le.mp hkn'
      simp only [Nat.not_le.mpr hn1k, ↓reduceIte, add_zero]
      rw [hkn_eq, Nat.sub_self, pow_zero, one_mul, Nat.sub_self]
      -- monotoneFunctions m 0 = {fun _ => 0} for any m
      have hmono_n : monotoneFunctions n 0 = {fun _ => 0} := by
        ext f
        simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro _; funext x; exact @Subsingleton.elim _ Fin.subsingleton_one (f x) 0
        · intro hf; rw [hf]; exact fun _ _ _ => le_refl _
      have hmono_n1 : monotoneFunctions (n - 1) 0 = {fun _ => 0} := by
        ext f
        simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro _; funext x; exact @Subsingleton.elim _ Fin.subsingleton_one (f x) 0
        · intro hf; rw [hf]; exact fun _ _ _ => le_refl _
      rw [hmono_n, hmono_n1, sum_singleton, sum_singleton]
      simp [sum_const_zero]
  · -- Case k > n: LHS = 0
    have hkn1 : ¬(k - 1 ≤ n - 1) := by omega
    have hkn2 : ¬(k ≤ n - 1) := by omega
    simp only [qBinomial, hkn, hkn1, hkn2, ↓reduceIte, mul_zero, add_zero]

/-! ### Transpose of monotone functions

The following helper definitions and lemmas establish a bijection between monotone
functions `Fin k → Fin (m + 1)` and `Fin m → Fin (k + 1)` via transposition.
This is used to prove the symmetry of q-binomial coefficients. -/

/-- The transpose of a monotone function f : Fin k → Fin (m + 1).
Given f, we define g : Fin m → Fin (k + 1) by g(j) = #{i : f(i) > m - 1 - j}.
This corresponds to the conjugate/transpose of the partition encoded by f. -/
private def transposeMonotone (k m : ℕ) (f : Fin k → Fin (m + 1)) : Fin m → Fin (k + 1) :=
  fun j => ⟨Finset.univ.filter (fun i => (f i).val > m - 1 - j.val) |>.card, by
    have : (Finset.univ.filter (fun i : Fin k => (f i).val > m - 1 - j.val)).card ≤ Finset.card Finset.univ :=
      Finset.card_filter_le _ _
    simp only [Finset.card_fin] at this
    omega⟩

private lemma transposeMonotone_monotone (k m : ℕ) (f : Fin k → Fin (m + 1)) (_hf : Monotone f) :
    Monotone (transposeMonotone k m f) := by
  intro j1 j2 hj
  simp only [transposeMonotone, Fin.mk_le_mk]
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

private lemma profile_le_iff (k m : ℕ) (f : Fin k → Fin (m + 1)) (hf : Monotone f)
    (i : Fin k) (j : Fin m) :
    (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card ≤ i.val ↔
    j.val ≥ m - (f i).val := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hfi : (f i).val ≤ m - 1 - j.val := by omega
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val) := by
      intro i' hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic] at hi' ⊢
      exact Nat.le_trans (hf hi') hfi
    have : i.val + 1 ≤ (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card := by
      calc i.val + 1 = (Finset.Iic i).card := by simp [Fin.card_Iic]
        _ ≤ _ := Finset.card_le_card hsub
    omega
  · intro h
    have hfi : (f i).val > m - 1 - j.val := by omega
    have hsub : Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val) ⊆ Finset.Iio i := by
      intro i' hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio] at hi' ⊢
      by_contra hne
      push Not at hne
      have : (f i).val ≤ (f i').val := hf hne
      omega
    calc (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card
        ≤ (Finset.Iio i).card := Finset.card_le_card hsub
      _ = i.val := by simp [Fin.card_Iio]

private lemma count_ge_complement (m v : ℕ) (hv : v ≤ m) :
    (Finset.univ.filter (fun j : Fin m => j.val ≥ m - v)).card = v := by
  cases m with
  | zero => simp; omega
  | succ m' =>
    have hv' : v ≤ m' + 1 := hv
    have h_inj : Function.Injective (fun x : Fin v => (⟨x.val + (m' + 1 - v), by omega⟩ : Fin (m' + 1))) := by
      intro a b hab; simp only [Fin.mk.injEq] at hab; ext; omega
    have h_eq : (Finset.univ.filter (fun j : Fin (m' + 1) => j.val ≥ m' + 1 - v)) =
                Finset.map ⟨fun x : Fin v => ⟨x.val + (m' + 1 - v), by omega⟩, h_inj⟩ Finset.univ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · intro hj; use ⟨j.val - (m' + 1 - v), by omega⟩; ext; simp; omega
      · intro ⟨a, ha⟩; simp only [Fin.ext_iff] at ha; omega
    rw [h_eq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma transposeMonotone_involutive (k m : ℕ) (f : Fin k → Fin (m + 1)) (hf : Monotone f) :
    transposeMonotone m k (transposeMonotone k m f) = f := by
  funext i
  simp only [transposeMonotone]
  have key : ∀ j : Fin m,
      ((Finset.univ.filter (fun i' : Fin k => (f i').val > m - 1 - j.val)).card > k - 1 - i.val) ↔
      (j.val ≥ m - (f i).val) := by
    intro j
    have h_compl : (Finset.univ.filter (fun i' : Fin k => (f i').val > m - 1 - j.val)).card =
                   k - (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card := by
      have h_eq : (Finset.univ.filter (fun i' : Fin k => (f i').val > m - 1 - j.val)) =
                  Finset.univ \ (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)) := by
        ext i'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]; omega
      rw [h_eq, Finset.card_sdiff]
      have h_inter : (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)) ∩ Finset.univ =
                     (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)) := Finset.inter_univ _
      rw [h_inter]; simp only [Finset.card_univ, Fintype.card_fin]
    rw [h_compl]
    have hcard : (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card ≤ k := by
      calc _ ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = k := Finset.card_fin k
    constructor
    · intro h
      have h2 : (Finset.univ.filter (fun i' : Fin k => (f i').val ≤ m - 1 - j.val)).card ≤ i.val := by
        omega
      exact (profile_le_iff k m f hf i j).mp h2
    · intro h
      have h2 := (profile_le_iff k m f hf i j).mpr h
      omega
  simp_rw [key]
  have hfi : (f i).val ≤ m := Nat.lt_succ_iff.mp (f i).isLt
  rw [Fin.ext_iff]
  exact count_ge_complement m (f i).val hfi

lemma sum_transposeMonotone (k m : ℕ) (f : Fin k → Fin (m + 1)) :
    ∑ j : Fin m, (transposeMonotone k m f j).val = ∑ i : Fin k, (f i).val := by
  simp only [transposeMonotone]
  simp_rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  trans (Finset.univ.filter (fun j : Fin m => (f i).val > m - 1 - j.val)).card
  · rw [Finset.card_eq_sum_ones]; simp only [Finset.sum_filter]
  · have hfi : (f i).val ≤ m := Nat.lt_succ_iff.mp (f i).isLt
    have key : ∀ j : Fin m, ((f i).val > m - 1 - j.val) ↔ (j.val ≥ m - (f i).val) := by
      intro j; have hj : j.val < m := j.isLt; omega
    simp_rw [key]
    exact count_ge_complement m (f i).val hfi

private lemma transposeMonotone_mem (k m : ℕ) (f : Fin k → Fin (m + 1)) (hf : f ∈ monotoneFunctions k m) :
    transposeMonotone k m f ∈ monotoneFunctions m k := by
  simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
  exact transposeMonotone_monotone k m f hf

/-- Local symmetry lemma for use in qBinomial_rec_right proof. -/
private lemma qBinomial_symm_local (n k : ℕ) (hk : k ≤ n) (q : R) :
    qBinomial n k q = qBinomial n (n - k) q := by
  have hnk : n - k ≤ n := Nat.sub_le n k
  have h_eq : n - (n - k) = k := Nat.sub_sub_self hk
  simp only [qBinomial, hk, hnk, ite_true]
  conv_rhs => rw [h_eq]
  apply Finset.sum_bij'
    (fun f _ => transposeMonotone k (n - k) f)
    (fun g _ => transposeMonotone (n - k) k g)
  · intro f hf; exact transposeMonotone_mem k (n - k) f hf
  · intro g hg; exact transposeMonotone_mem (n - k) k g hg
  · intro f hf
    simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    exact transposeMonotone_involutive k (n - k) f hf
  · intro g hg
    simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact transposeMonotone_involutive (n - k) k g hg
  · intro f _
    congr 1
    exact (sum_transposeMonotone k (n - k) f).symm



/-- Second recurrence relation for q-binomial coefficients:
`⟦n;k⟧_q = ⟦n-1;k-1⟧_q + q^k * ⟦n-1;k⟧_q`

This is another q-analogue of Pascal's identity.

Note: The hypothesis `0 < k` is necessary because in Lean with `k : ℕ`, we have `k - 1 = 0`
when `k = 0` due to saturating subtraction. This would make the RHS equal to
`qBinomial (n-1) 0 q + q^0 * qBinomial (n-1) 0 q = 1 + 1 = 2`, which is not equal to
`qBinomial n 0 q = 1`.

See Theorem 11.2.4(b) in the source. The source handles k ∈ ℤ with the convention that
(n choose k)_q = 0 for negative k. -/
theorem qBinomial_rec_right (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : 0 < k) (q : R) :
    qBinomial n k q = qBinomial (n - 1) (k - 1) q + q ^ k * qBinomial (n - 1) k q := by
  -- Use symmetry: qBinomial n k = qBinomial n (n-k)
  -- Then use rec_left on qBinomial n (n-k)
  -- qBinomial n (n-k) = q^k * qBinomial (n-1) (n-k-1) + qBinomial (n-1) (n-k)
  -- Then use symmetry again to convert back
  by_cases hkn : k ≤ n
  · -- Case k ≤ n
    have hnk : n - k ≤ n := Nat.sub_le n k
    by_cases h_nk_pos : 0 < n - k
    · -- Case n - k > 0
      rw [qBinomial_symm_local n k hkn]
      rw [qBinomial_rec_left n hn (n - k) h_nk_pos]
      -- Now we have: q ^ (n - (n-k)) * qBinomial (n-1) (n-k-1) + qBinomial (n-1) (n-k)
      have h1 : n - (n - k) = k := Nat.sub_sub_self hkn
      rw [h1]
      -- Need to show the terms match
      have h3 : n - 1 - (n - k) = k - 1 := by omega
      have hk' : k ≤ n - 1 ∨ k = n := by omega
      cases hk' with
      | inl hk' =>
        -- k ≤ n - 1
        have h4 : qBinomial (n - 1) (n - k - 1) q = qBinomial (n - 1) (n - 1 - (n - k - 1)) q := by
          apply qBinomial_symm_local
          omega
        have h5 : n - 1 - (n - k - 1) = k := by omega
        rw [h4, h5]
        have h6 : qBinomial (n - 1) (n - k) q = qBinomial (n - 1) (n - 1 - (n - k)) q := by
          apply qBinomial_symm_local
          omega
        rw [h6, h3]
        ring
      | inr hk' =>
        -- k = n contradicts h_nk_pos since n - k = 0 when k = n
        have : n - k = 0 := by omega
        omega
    · -- Case n - k = 0, i.e., k = n
      push Not at h_nk_pos
      have hkn' : k = n := by omega
      rw [hkn']
      simp only [qBinomial_n_n]
      have h1 : qBinomial (n - 1) n q = 0 := qBinomial_zero_of_lt (n - 1) n (by omega) q
      rw [h1]
      simp
  · -- Case k > n
    push Not at hkn
    simp only [qBinomial_zero_of_lt n k hkn]
    have h1 : qBinomial (n - 1) (k - 1) q = 0 := qBinomial_zero_of_lt (n - 1) (k - 1) (by omega) q
    have h2 : qBinomial (n - 1) k q = 0 := qBinomial_zero_of_lt (n - 1) k (by omega) q
    rw [h1, h2]
    simp

/-! ### Product Formulas -/

-- Helper lemma: relates products with shifted indices
private lemma prod_n_shift {R : Type*} [CommRing R] (k n : ℕ) (q : R) (hk : k ≤ n) :
    (1 - q ^ n) * ∏ i ∈ range k, (1 - q ^ (n - (i + 1))) =
    (∏ i ∈ range k, (1 - q ^ (n - i))) * (1 - q ^ (n - k)) := by
  induction k with
  | zero =>
    simp only [prod_range_zero, mul_one, one_mul, Nat.sub_zero]
  | succ k ih =>
    rw [prod_range_succ, prod_range_succ]
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have ih' := ih hk'
    calc (1 - q ^ n) * ((∏ i ∈ range k, (1 - q ^ (n - (i + 1)))) * (1 - q ^ (n - (k + 1))))
        = ((1 - q ^ n) * ∏ i ∈ range k, (1 - q ^ (n - (i + 1)))) * (1 - q ^ (n - (k + 1))) := by ring
      _ = ((∏ i ∈ range k, (1 - q ^ (n - i))) * (1 - q ^ (n - k))) * (1 - q ^ (n - (k + 1))) := by rw [ih']
      _ = (∏ i ∈ range k, (1 - q ^ (n - i))) * (1 - q ^ (n - k)) * (1 - q ^ (n - (k + 1))) := by ring

-- Helper lemma: simplifies product index shift
private lemma prod_shift {R : Type*} [CommRing R] (k n : ℕ) (q : R) (hn : k ≤ n) :
    ∏ i ∈ range k, (1 - q ^ (n - 1 - i)) = ∏ i ∈ range k, (1 - q ^ (n - (i + 1))) := by
  apply prod_congr rfl
  intro i hi
  have hi' : i < k := mem_range.mp hi
  have : n - 1 - i = n - (i + 1) := by omega
  rw [this]

/-- Product formula for q-binomial coefficients (polynomial identity):
`(1-q^k)(1-q^(k-1))...(1-q) * ⟦n;k⟧_q = (1-q^n)(1-q^(n-1))...(1-q^(n-k+1))`

This is Theorem thm.pars.qbinom.quot1 part (a) from the source.
Also known as Theorem 11.2.5(a) in the section numbering.

The identity holds over any commutative ring without requiring any divisibility conditions.
This is the "polynomial form" that avoids fractions, making it easier to substitute values
for q without worrying about whether denominators are invertible. -/
theorem qBinomial_quot_formula {R : Type*} [CommRing R] (n k : ℕ) (hk : k ≤ n) (q : R) :
    (∏ i ∈ range k, (1 - q ^ (i + 1))) * qBinomial n k q =
    ∏ i ∈ range k, (1 - q ^ (n - i)) := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hn : 0 < n := Nat.lt_of_lt_of_le (Nat.succ_pos k) hk
      have hk' : k ≤ n - 1 := by omega
      rw [qBinomial_rec_left n hn (k + 1) (Nat.succ_pos k)]
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      rw [prod_range_succ, mul_add]
      have ih1 := ih (n - 1) (Nat.sub_lt hn (Nat.succ_pos 0)) k hk'
      rw [prod_range_succ]
      have eq1 : (∏ i ∈ range k, (1 - q ^ (i + 1))) * (1 - q ^ (k + 1)) *
          (q ^ (n - (k + 1)) * qBinomial (n - 1) k q) =
          (1 - q ^ (k + 1)) * q ^ (n - (k + 1)) * (∏ i ∈ range k, (1 - q ^ (n - 1 - i))) := by
        rw [← ih1]
        ring
      rw [eq1]
      rw [prod_shift k n q (le_of_lt (Nat.lt_of_succ_le hk))]
      by_cases hcase : k + 1 = n
      · -- Case k + 1 = n, so qBinomial (n-1) (k+1) = 0
        have h0 : qBinomial (n - 1) (k + 1) q = 0 := by
          rw [hcase]
          apply qBinomial_zero_of_lt
          omega
        rw [h0, mul_zero, add_zero]
        have hnk1 : n - (k + 1) = 0 := by omega
        have hnk : n - k = 1 := by omega
        rw [hnk1, hnk, pow_zero, mul_one, pow_one, hcase]
        have hshift := prod_n_shift k n q (le_of_lt (Nat.lt_of_succ_le hk))
        have hnk' : n - k = 1 := by omega
        rw [hnk'] at hshift
        simp only [pow_one] at hshift
        exact hshift
      · -- Case k + 1 < n
        have hkn : k + 1 < n := Nat.lt_of_le_of_ne hk hcase
        have hk''' : k + 1 ≤ n - 1 := by omega
        have ih2 := ih (n - 1) (Nat.sub_lt hn (Nat.succ_pos 0)) (k + 1) hk'''
        rw [prod_range_succ, prod_range_succ] at ih2
        have hnk1 : (n - 1) - k = n - (k + 1) := by omega
        rw [hnk1] at ih2
        rw [prod_shift k n q (le_of_lt (Nat.lt_of_succ_le hk))] at ih2
        rw [ih2]
        have key : (1 - q ^ (k + 1)) * q ^ (n - (k + 1)) + (1 - q ^ (n - (k + 1))) = 1 - q ^ n := by
          calc (1 - q ^ (k + 1)) * q ^ (n - (k + 1)) + (1 - q ^ (n - (k + 1)))
              = q ^ (n - (k + 1)) - q ^ (k + 1) * q ^ (n - (k + 1)) + 1 - q ^ (n - (k + 1)) := by ring
            _ = 1 - q ^ (k + 1) * q ^ (n - (k + 1)) := by ring
            _ = 1 - q ^ (k + 1 + (n - (k + 1))) := by rw [← pow_add]
            _ = 1 - q ^ n := by rw [Nat.add_sub_cancel' (Nat.le_of_lt hkn)]
        calc (1 - q ^ (k + 1)) * q ^ (n - (k + 1)) * ∏ i ∈ range k, (1 - q ^ (n - (i + 1))) +
                (∏ i ∈ range k, (1 - q ^ (n - (i + 1)))) * (1 - q ^ (n - (k + 1)))
            = (∏ i ∈ range k, (1 - q ^ (n - (i + 1)))) *
                ((1 - q ^ (k + 1)) * q ^ (n - (k + 1)) + (1 - q ^ (n - (k + 1)))) := by ring
          _ = (∏ i ∈ range k, (1 - q ^ (n - (i + 1)))) * (1 - q ^ n) := by rw [key]
          _ = (1 - q ^ n) * ∏ i ∈ range k, (1 - q ^ (n - (i + 1))) := by ring
          _ = (∏ i ∈ range k, (1 - q ^ (n - i))) * (1 - q ^ (n - k)) :=
              prod_n_shift k n q (le_of_lt (Nat.lt_of_succ_le hk))

/-- Product formula for q-binomial coefficients (quotient form):
`⟦n;k⟧_q = ∏_{i=0}^{k-1} (1-q^(n-i)) / (1-q^(i+1))`

This is Theorem thm.pars.qbinom.quot1 part (b) from the source.
Also known as Theorem 11.2.5(b) in the section numbering.

This holds in any ring where the denominator is invertible. The hypothesis `hq` ensures
that `q` is not a root of unity of order ≤ k, which guarantees all factors `(1 - q^(i+1))`
in the denominator are nonzero.

Note: Part (b) is the more intuitive statement showing the q-binomial as a ratio of
products, but part (a) (`qBinomial_quot_formula`) is easier to work with when substituting
values for q since it has no denominators. -/
theorem qBinomial_eq_prod_quot {R : Type*} [Field R] (n k : ℕ) (hk : k ≤ n)
    (q : R) (hq : ∀ i ∈ range k, q ^ (i + 1) ≠ 1) :
    qBinomial n k q = ∏ i ∈ range k, (1 - q ^ (n - i)) / (1 - q ^ (i + 1)) := by
  have h := qBinomial_quot_formula n k hk q
  -- The product ∏ i ∈ range k, (1 - q ^ (i + 1)) is nonzero
  have hne : ∏ i ∈ range k, (1 - q ^ (i + 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    simp only [sub_ne_zero, ne_eq]
    exact (hq i hi).symm
  -- Divide both sides by the product
  rw [Finset.prod_div_distrib]
  rw [← h]
  field_simp [hne]

/-- q-binomial coefficient in terms of q-integers (falling factorial form):
`⟦n;k⟧_q = [n]_q * [n-1]_q * ... * [n-k+1]_q / [k]_q!`

See Theorem 11.2.6 in the source. -/
theorem qBinomial_eq_qInt_prod_quot {R : Type*} [Field R] (n k : ℕ) (hk : k ≤ n)
    (q : R) (hq : ∀ i ∈ range k, q ^ (i + 1) ≠ 1) :
    qBinomial n k q = (∏ i ∈ range k, qInt (n - i) q) / qFactorial k q := by
  -- First, use qBinomial_eq_prod_quot
  rw [qBinomial_eq_prod_quot n k hk q hq]
  -- Get the hypothesis that q ≠ 1 (from hq at i = 0 when k > 0)
  by_cases hk0 : k = 0
  · -- When k = 0, both sides are empty products
    simp [hk0, qFactorial]
  · -- When k > 0, we have q ≠ 1 from hq
    have hq1 : q ≠ 1 := by
      have h0 : 0 ∈ range k := by simp [Nat.pos_of_ne_zero hk0]
      specialize hq 0 h0
      simp at hq
      exact hq
    have h1q : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_comm.mpr hq1)
    -- Helper: qInt m q = (1 - q ^ m) / (1 - q) when q ≠ 1
    have hqInt : ∀ m, qInt m q = (1 - q ^ m) / (1 - q) := fun m => by
      rw [eq_div_iff h1q, mul_comm, qInt_eq_geom_sum]
    -- Rewrite the numerator product
    have eq1 : (∏ i ∈ range k, qInt (n - i) q) = ∏ i ∈ range k, (1 - q ^ (n - i)) / (1 - q) := by
      apply prod_congr rfl
      intro i _
      exact hqInt (n - i)
    -- Rewrite qFactorial
    have eq2 : qFactorial k q = ∏ i ∈ range k, (1 - q ^ (i + 1)) / (1 - q) := by
      simp only [qFactorial]
      apply prod_congr rfl
      intro i _
      exact hqInt (i + 1)
    rw [eq1, eq2]
    -- Now both sides are products of divisions
    rw [prod_div_distrib, prod_div_distrib]
    -- Simplify the constant products
    simp only [prod_const, card_range]
    -- Simplify RHS: (A / B) / (C / B) = A / C
    rw [div_div]
    -- Now need to show: A / C = A / (B * (C / B))
    congr 1
    -- Goal: ∏ x ∈ range k, (1 - q ^ (x + 1)) = (1 - q) ^ k * (∏ i ∈ range k, (1 - q ^ (i + 1)) / (1 - q))
    conv_rhs =>
      rw [show (1 - q) ^ k = ∏ _ ∈ range k, (1 - q) by simp [prod_const, card_range]]
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    field_simp

/-- q-binomial coefficient in terms of q-factorials:
`⟦n;k⟧_q = [n]_q! / ([k]_q! * [n-k]_q!)`

See Theorem 11.2.6 in the source.
This is also Theorem thm.pars.qbinom.quot2 from the text. -/
theorem qBinomial_eq_qFactorial_quot {R : Type*} [Field R] (n k : ℕ) (hk : k ≤ n)
    (q : R) (hq : ∀ i ∈ range n, q ^ (i + 1) ≠ 1) :
    qBinomial n k q = qFactorial n q / (qFactorial k q * qFactorial (n - k) q) := by
  -- First, derive the hypothesis needed for qBinomial_eq_qInt_prod_quot
  have hq' : ∀ i ∈ range k, q ^ (i + 1) ≠ 1 := by
    intro i hi
    apply hq i
    exact mem_range.mpr (Nat.lt_of_lt_of_le (mem_range.mp hi) hk)
  -- Use the falling factorial form
  rw [qBinomial_eq_qInt_prod_quot n k hk q hq']
  -- Use the split formula: qFactorial n q = (∏ i ∈ range k, qInt (n - i) q) * qFactorial (n - k) q
  rw [qFactorial_split n k hk q]
  -- Show the denominators are nonzero
  have hne_k : qFactorial k q ≠ 0 := qFactorial_ne_zero k q hq'
  have hq_nk : ∀ i ∈ range (n - k), q ^ (i + 1) ≠ 1 := by
    intro i hi
    apply hq i
    exact mem_range.mpr (Nat.lt_of_lt_of_le (mem_range.mp hi) (Nat.sub_le n k))
  have hne_nk : qFactorial (n - k) q ≠ 0 := qFactorial_ne_zero (n - k) q hq_nk
  field_simp [hne_k, hne_nk]



/-- Symmetry of q-binomial coefficients: `⟦n;k⟧_q = ⟦n;n-k⟧_q`.

See Proposition 11.2.7 in the source. -/
theorem qBinomial_symm (n k : ℕ) (hk : k ≤ n) (q : R) :
    qBinomial n k q = qBinomial n (n - k) q := by
  have hnk : n - k ≤ n := Nat.sub_le n k
  have h_eq : n - (n - k) = k := Nat.sub_sub_self hk
  simp only [qBinomial, hk, hnk, ite_true]
  conv_rhs => rw [h_eq]
  apply Finset.sum_bij'
    (fun f _ => transposeMonotone k (n - k) f)
    (fun g _ => transposeMonotone (n - k) k g)
  · intro f hf; exact transposeMonotone_mem k (n - k) f hf
  · intro g hg; exact transposeMonotone_mem (n - k) k g hg
  · intro f hf
    simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    exact transposeMonotone_involutive k (n - k) f hf
  · intro g hg
    simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact transposeMonotone_involutive (n - k) k g hg
  · intro f _
    congr 1
    exact (sum_transposeMonotone k (n - k) f).symm

end QBinomial

/-! ## Counting Partitions -/

section PartitionCount

/-- Equivalence between monotone functions `Fin k → Fin (ℓ + 1)` and multisets
of size k over `Fin (ℓ + 1)`. A monotone function is converted to a multiset
by taking its values (with multiplicity), and a multiset is converted to a
monotone function by sorting and indexing. -/
def monotoneFunctionsEquivSym (k ℓ : ℕ) :
    {f : Fin k → Fin (ℓ + 1) // Monotone f} ≃ Sym (Fin (ℓ + 1)) k := by
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  case toFun =>
    intro ⟨f, _⟩
    exact ⟨Multiset.ofList (List.ofFn f), by simp⟩
  case invFun =>
    intro s
    let sorted := s.val.sort (· ≤ ·)
    have hlen : sorted.length = k := by simp [sorted, Multiset.length_sort]
    refine ⟨fun i => sorted.get (i.cast hlen.symm), ?_⟩
    intro i j hij
    apply List.Pairwise.rel_get_of_le (Multiset.pairwise_sort s.val (· ≤ ·))
    exact hij
  case left_inv =>
    intro ⟨f, hf⟩
    simp only [Subtype.mk.injEq]
    ext i
    have h : (Multiset.ofList (List.ofFn f)).sort (· ≤ ·) = List.ofFn f := by
      simp only [Multiset.coe_sort]
      apply List.mergeSort_eq_self
      exact List.pairwise_ofFn.mpr (fun i j hij => hf (le_of_lt hij))
    have hlen : ((Multiset.ofList (List.ofFn f)).sort (· ≤ ·)).length = k := by simp
    have eq1 : ((Multiset.ofList (List.ofFn f)).sort (· ≤ ·)).get (i.cast hlen.symm) =
               ((Multiset.ofList (List.ofFn f)).sort (· ≤ ·))[i.val] := by
      rfl
    show ((((Multiset.ofList (List.ofFn f)).sort (· ≤ ·)).get (i.cast hlen.symm) :
        Fin (ℓ + 1)) : ℕ) =
      (f i : ℕ)
    rw [eq1]
    simp only [h]
    simp [List.getElem_ofFn]
  case right_inv =>
    intro s
    apply Sym.ext
    simp only [Sym.coe_mk]
    have hlen : (s.val.sort (· ≤ ·)).length = k := by simp [Multiset.length_sort]
    have h1 : List.ofFn (fun i : Fin k => (s.val.sort (· ≤ ·)).get (i.cast hlen.symm)) =
              s.val.sort (· ≤ ·) := by
      apply List.ext_get
      · simp
      · intro i hi1 hi2
        simp only [List.get_ofFn]
        rfl
    rw [h1]
    exact Multiset.sort_eq s.val (· ≤ ·)

/-- The number of partitions with at most k parts and largest part at most ℓ
equals the number of monotone functions from `Fin k` to `Fin (ℓ + 1)`,
which is the binomial coefficient `(k + ℓ) choose k`.

This is a consequence of the bijection between such partitions and lattice paths
from (0,0) to (ℓ,k) using east and north steps.

See discussion before Proposition 11.1.1 in the source. -/
theorem card_monotoneFunctions_eq_choose (k ℓ : ℕ) :
    (monotoneFunctions k ℓ).card = Nat.choose (k + ℓ) k := by
  -- monotoneFunctions k ℓ is a Finset of functions Fin k → Fin (ℓ + 1) that are monotone
  -- Its cardinality equals the cardinality of {f : Fin k → Fin (ℓ + 1) // Monotone f}
  have h1 : (monotoneFunctions k ℓ).card = Fintype.card {f : Fin k → Fin (ℓ + 1) // Monotone f} := by
    simp only [monotoneFunctions, card_filter, Fintype.card_subtype]
  rw [h1]
  -- Use the equivalence with Sym
  rw [Fintype.card_congr (monotoneFunctionsEquivSym k ℓ)]
  -- Use the stars and bars theorem
  rw [Sym.card_sym_eq_multichoose, Nat.multichoose_eq]
  simp only [Fintype.card_fin]
  -- Now simplify: (ℓ + 1 + k - 1).choose k = (k + ℓ).choose k
  congr 1
  omega

/-- The number of partitions with exactly k parts and largest part exactly ℓ
equals the binomial coefficient `(k + ℓ - 2) choose (k - 1)`.

This counts lattice paths from (0,0) to (ℓ,k) that start with an east step
and end with a north step.

See Proposition 11.1.1 in the source. -/
theorem card_partitions_with_parts_and_largest (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) :
    (monotoneFunctions (k - 1) (ℓ - 1)).card = Nat.choose (k + ℓ - 2) (k - 1) := by
  rw [card_monotoneFunctions_eq_choose]
  congr 1
  omega

end PartitionCount

/-! ## Examples -/

section Examples

/-! ### Helper definitions for explicit enumeration of monotone functions

For small values of n and k, we can enumerate all monotone functions explicitly
and compute the q-binomial polynomial by direct summation. -/

-- For qBinomialPoly 3 2: monotone functions Fin 2 → Fin 2
private def f00 : Fin 2 → Fin 2 := ![0, 0]
private def f01 : Fin 2 → Fin 2 := ![0, 1]
private def f11 : Fin 2 → Fin 2 := ![1, 1]

private lemma monotoneFunctions_2_1_eq : monotoneFunctions 2 1 = {f00, f01, f11} := by
  ext f
  simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro hf
    have h := hf (Fin.zero_le 1)
    match h0 : f 0, h1 : f 1 with
    | ⟨0, _⟩, ⟨0, _⟩ => left; ext i; fin_cases i <;> simp [f00, h0, h1]
    | ⟨0, _⟩, ⟨1, _⟩ => right; left; ext i; fin_cases i <;> simp [f01, h0, h1]
    | ⟨1, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨1, _⟩, ⟨1, _⟩ => right; right; ext i; fin_cases i <;> simp [f11, h0, h1]
  · intro hf
    rcases hf with rfl | rfl | rfl
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [f00]
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [f01]
    · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [f11]

private lemma sum_f00 : ∑ i : Fin 2, (f00 i).val = 0 := by simp [f00]
private lemma sum_f01 : ∑ i : Fin 2, (f01 i).val = 1 := by simp [f01]
private lemma sum_f11 : ∑ i : Fin 2, (f11 i).val = 2 := by simp [f11]

-- For qBinomialPoly 4 2: monotone functions Fin 2 → Fin 3
private def g00 : Fin 2 → Fin 3 := ![0, 0]
private def g01 : Fin 2 → Fin 3 := ![0, 1]
private def g02 : Fin 2 → Fin 3 := ![0, 2]
private def g11 : Fin 2 → Fin 3 := ![1, 1]
private def g12 : Fin 2 → Fin 3 := ![1, 2]
private def g22 : Fin 2 → Fin 3 := ![2, 2]

private lemma monotoneFunctions_2_2_eq : monotoneFunctions 2 2 = {g00, g01, g02, g11, g12, g22} := by
  ext f
  simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro hf
    have h := hf (Fin.zero_le 1)
    match h0 : f 0, h1 : f 1 with
    | ⟨0, _⟩, ⟨0, _⟩ => left; ext i; fin_cases i <;> simp [g00, h0, h1]
    | ⟨0, _⟩, ⟨1, _⟩ => right; left; ext i; fin_cases i <;> simp [g01, h0, h1]
    | ⟨0, _⟩, ⟨2, _⟩ => right; right; left; ext i; fin_cases i <;> simp [g02, h0, h1]
    | ⟨1, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨1, _⟩, ⟨1, _⟩ => right; right; right; left; ext i; fin_cases i <;> simp [g11, h0, h1]
    | ⟨1, _⟩, ⟨2, _⟩ => right; right; right; right; left; ext i; fin_cases i <;> simp [g12, h0, h1]
    | ⟨2, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨1, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨2, _⟩ => right; right; right; right; right; ext i; fin_cases i <;> simp [g22, h0, h1]
  · intro hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [g00, g01, g02, g11, g12, g22])

private lemma sum_g00 : ∑ i : Fin 2, (g00 i).val = 0 := by simp [g00]
private lemma sum_g01 : ∑ i : Fin 2, (g01 i).val = 1 := by simp [g01]
private lemma sum_g02 : ∑ i : Fin 2, (g02 i).val = 2 := by simp [g02]
private lemma sum_g11 : ∑ i : Fin 2, (g11 i).val = 2 := by simp [g11]
private lemma sum_g12 : ∑ i : Fin 2, (g12 i).val = 3 := by simp [g12]
private lemma sum_g22 : ∑ i : Fin 2, (g22 i).val = 4 := by simp [g22]

-- For qBinomialPoly 5 2: monotone functions Fin 2 → Fin 4
private def h00 : Fin 2 → Fin 4 := ![0, 0]
private def h01 : Fin 2 → Fin 4 := ![0, 1]
private def h02 : Fin 2 → Fin 4 := ![0, 2]
private def h03 : Fin 2 → Fin 4 := ![0, 3]
private def h11 : Fin 2 → Fin 4 := ![1, 1]
private def h12 : Fin 2 → Fin 4 := ![1, 2]
private def h13 : Fin 2 → Fin 4 := ![1, 3]
private def h22 : Fin 2 → Fin 4 := ![2, 2]
private def h23 : Fin 2 → Fin 4 := ![2, 3]
private def h33 : Fin 2 → Fin 4 := ![3, 3]

private lemma monotoneFunctions_2_3_eq : monotoneFunctions 2 3 = {h00, h01, h02, h03, h11, h12, h13, h22, h23, h33} := by
  ext f
  simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro hf
    have h := hf (Fin.zero_le 1)
    match h0 : f 0, h1 : f 1 with
    | ⟨0, _⟩, ⟨0, _⟩ => left; ext i; fin_cases i <;> simp [h00, h0, h1]
    | ⟨0, _⟩, ⟨1, _⟩ => right; left; ext i; fin_cases i <;> simp [h01, h0, h1]
    | ⟨0, _⟩, ⟨2, _⟩ => right; right; left; ext i; fin_cases i <;> simp [h02, h0, h1]
    | ⟨0, _⟩, ⟨3, _⟩ => right; right; right; left; ext i; fin_cases i <;> simp [h03, h0, h1]
    | ⟨1, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨1, _⟩, ⟨1, _⟩ => right; right; right; right; left; ext i; fin_cases i <;> simp [h11, h0, h1]
    | ⟨1, _⟩, ⟨2, _⟩ => right; right; right; right; right; left; ext i; fin_cases i <;> simp [h12, h0, h1]
    | ⟨1, _⟩, ⟨3, _⟩ => right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [h13, h0, h1]
    | ⟨2, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨1, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨2, _⟩ => right; right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [h22, h0, h1]
    | ⟨2, _⟩, ⟨3, _⟩ => right; right; right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [h23, h0, h1]
    | ⟨3, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨3, _⟩, ⟨1, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨3, _⟩, ⟨2, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨3, _⟩, ⟨3, _⟩ => right; right; right; right; right; right; right; right; right; ext i; fin_cases i <;> simp [h33, h0, h1]
  · intro hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [h00, h01, h02, h03, h11, h12, h13, h22, h23, h33])

private lemma sum_h00 : ∑ i : Fin 2, (h00 i).val = 0 := by simp [h00]
private lemma sum_h01 : ∑ i : Fin 2, (h01 i).val = 1 := by simp [h01]
private lemma sum_h02 : ∑ i : Fin 2, (h02 i).val = 2 := by simp [h02]
private lemma sum_h03 : ∑ i : Fin 2, (h03 i).val = 3 := by simp [h03]
private lemma sum_h11 : ∑ i : Fin 2, (h11 i).val = 2 := by simp [h11]
private lemma sum_h12 : ∑ i : Fin 2, (h12 i).val = 3 := by simp [h12]
private lemma sum_h13 : ∑ i : Fin 2, (h13 i).val = 4 := by simp [h13]
private lemma sum_h22 : ∑ i : Fin 2, (h22 i).val = 4 := by simp [h22]
private lemma sum_h23 : ∑ i : Fin 2, (h23 i).val = 5 := by simp [h23]
private lemma sum_h33 : ∑ i : Fin 2, (h33 i).val = 6 := by simp [h33]

/-- Example: `⟦3;2⟧_q = q^2 + q + 1`.

The partitions fitting in a 2 × 1 box are:
- (1, 1) with size 2
- (1) with size 1
- () with size 0 -/
example : qBinomialPoly 3 2 = X ^ 2 + X + 1 := by
  unfold qBinomialPoly
  have h1 : (2 : ℕ) ≤ 3 := by norm_num
  simp only [h1, ↓reduceIte]
  have h2 : (3 : ℕ) - 2 = 1 := by norm_num
  rw [h2, monotoneFunctions_2_1_eq]
  have hf00 : f00 ∉ ({f01, f11} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h <;> simp [f00, f01, f11] at h
  have hf01 : f01 ∉ ({f11} : Finset _) := by
    simp only [mem_singleton]
    intro h; simp [f01, f11] at h
  rw [sum_insert hf00, sum_insert hf01, sum_singleton]
  simp only [sum_f00, sum_f01, sum_f11]
  simp only [pow_zero, pow_one]
  ring

/-- Example: `⟦4;2⟧_q = q^4 + q^3 + 2q^2 + q + 1`.

The partitions fitting in a 2 × 2 box are:
- (2, 2) with size 4
- (2, 1) with size 3
- (2) with size 2
- (1, 1) with size 2
- (1) with size 1
- () with size 0 -/
example : qBinomialPoly 4 2 = X ^ 4 + X ^ 3 + 2 * X ^ 2 + X + 1 := by
  unfold qBinomialPoly
  have h1 : (2 : ℕ) ≤ 4 := by norm_num
  simp only [h1, ↓reduceIte]
  have h2 : (4 : ℕ) - 2 = 2 := by norm_num
  rw [h2, monotoneFunctions_2_2_eq]
  have hg00 : g00 ∉ ({g01, g02, g11, g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h <;> simp [g00, g01, g02, g11, g12, g22] at h
  have hg01 : g01 ∉ ({g02, g11, g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h <;> simp [g01, g02, g11, g12, g22] at h
  have hg02 : g02 ∉ ({g11, g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h <;> simp [g02, g11, g12, g22] at h
  have hg11 : g11 ∉ ({g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h <;> simp [g11, g12, g22] at h
  have hg12 : g12 ∉ ({g22} : Finset _) := by
    simp only [mem_singleton]
    intro h; simp [g12, g22] at h
  rw [sum_insert hg00, sum_insert hg01, sum_insert hg02, sum_insert hg11, sum_insert hg12, sum_singleton]
  simp only [sum_g00, sum_g01, sum_g02, sum_g11, sum_g12, sum_g22]
  simp only [pow_zero, pow_one]
  ring

/-- Example: `⟦5;2⟧_q = 1 + q + 2q^2 + 2q^3 + 2q^4 + q^5 + q^6`.

Computed using Proposition 11.2.1(b). -/
example : qBinomialPoly 5 2 = 1 + X + 2 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 := by
  unfold qBinomialPoly
  have h1 : (2 : ℕ) ≤ 5 := by norm_num
  simp only [h1, ↓reduceIte]
  have h2 : (5 : ℕ) - 2 = 3 := by norm_num
  rw [h2, monotoneFunctions_2_3_eq]
  have hh00 : h00 ∉ ({h01, h02, h03, h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp [h00, h01, h02, h03, h11, h12, h13, h22, h23, h33] at h
  have hh01 : h01 ∉ ({h02, h03, h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h | h | h <;> simp [h01, h02, h03, h11, h12, h13, h22, h23, h33] at h
  have hh02 : h02 ∉ ({h03, h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h | h <;> simp [h02, h03, h11, h12, h13, h22, h23, h33] at h
  have hh03 : h03 ∉ ({h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h <;> simp [h03, h11, h12, h13, h22, h23, h33] at h
  have hh11 : h11 ∉ ({h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h <;> simp [h11, h12, h13, h22, h23, h33] at h
  have hh12 : h12 ∉ ({h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h <;> simp [h12, h13, h22, h23, h33] at h
  have hh13 : h13 ∉ ({h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h <;> simp [h13, h22, h23, h33] at h
  have hh22 : h22 ∉ ({h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h <;> simp [h22, h23, h33] at h
  have hh23 : h23 ∉ ({h33} : Finset _) := by
    simp only [mem_singleton]
    intro h; simp [h23, h33] at h
  rw [sum_insert hh00, sum_insert hh01, sum_insert hh02, sum_insert hh03, sum_insert hh11, 
      sum_insert hh12, sum_insert hh13, sum_insert hh22, sum_insert hh23, sum_singleton]
  simp only [sum_h00, sum_h01, sum_h02, sum_h03, sum_h11, sum_h12, sum_h13, sum_h22, sum_h23, sum_h33]
  simp only [pow_zero, pow_one]
  ring

end Examples

end AlgebraicCombinatorics
