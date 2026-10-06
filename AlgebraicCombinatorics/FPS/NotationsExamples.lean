/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# Notations and Elementary Facts + Examples

This file formalizes the introductory material from the first chapter of the
Algebraic Combinatorics course notes. It covers:

1. Basic combinatorial principles (addition, multiplication, bijection)
2. Binomial coefficient definitions and properties
3. Four motivating examples using generating functions:
   - The Fibonacci sequence and Binet's formula
   - Dyck words and Catalan numbers
   - The Vandermonde convolution identity
   - Solving a linear recurrence

## Main Definitions

* `FPS.fibonacci` - The Fibonacci sequence (equivalent to `Nat.fib` in Mathlib)
* `FPS.catalan` - The Catalan numbers (equivalent to `catalan` in Mathlib)
* `FPS.isDyckWord` - Predicate for Dyck words (alternative to Mathlib's `DyckWord` structure)
* `FPS.goldenRatioPlus` - The golden ratio (equivalent to `Real.goldenRatio` in Mathlib)
* `FPS.goldenRatioMinus` - The conjugate golden ratio (equivalent to `Real.goldenConj` in Mathlib)

## Main Results

* `FPS.binom_def_formula` - **Definition \ref{def.binom.binom}**: $\binom{r}{n} = \frac{r(r-1)\cdots(r-n+1)}{n!}$
* `FPS.binom_factorial_smul` - The factorial formula: $n! \cdot \binom{r}{n} = r(r-1)\cdots(r-n+1)$
* `FPS.binom_natCast` - For natural numbers: $\binom{n}{k} = $ `Nat.choose n k`
* `FPS.binom_zero_right` - Base case: $\binom{r}{0} = 1$
* `FPS.binom_zero_left_pos` - For $k > 0$: $\binom{0}{k} = 0$
* `FPS.binom_one_right` - First case: $\binom{r}{1} = r$
* `FPS.binom_neg_one` - The binomial coefficient $\binom{-1}{k} = (-1)^k$
* `FPS.binom_two_n_n_eq` - Formula $\binom{2n}{n} = \frac{1 \cdot 3 \cdot 5 \cdots (2n-1)}{n!} \cdot 2^n$
* `FPS.pascal_identity` - Pascal's identity for binomial coefficients (natural numbers)
* `FPS.pascal_identity_ring` - Pascal's identity for generalized binomial coefficients (binomial rings)
* `FPS.pascal_identity_succ` - Pascal's identity in successor form
* `FPS.pascal_identity_int` - Pascal's identity for integers
* `FPS.pascal_identity_rat` - Pascal's identity for rationals
* `FPS.binom_zero_of_lt` - $\binom{m}{n} = 0$ when $m < n$ for natural numbers
* `FPS.binom_symm` - Symmetry: $\binom{n}{k} = \binom{n}{n-k}$ (Theorem \ref{thm.binom.sym})
* `FPS.binom_symm_add` - Symmetry variant: $\binom{a+b}{a} = \binom{a+b}{b}$
* `FPS.binom_symm_of_eq_add` - Symmetry when $n = a + b$
* `FPS.binom_symm_ring` - Symmetry for `Ring.choose` (generalized binomial coefficients)
* `FPS.fibonacci_binet` - Binet's formula for Fibonacci numbers
* `FPS.fibonacci_gf` - Generating function $F(x) = x/(1-x-x^2)$
* `FPS.catalan_recurrence` - Recurrence $c_n = \sum_{k=0}^{n-1} c_k c_{n-1-k}$
* `FPS.catalan_explicit` - Explicit formula $c_n = \frac{1}{n+1}\binom{2n}{n}$
* `FPS.vandermonde_convolution` - $\binom{a+b}{n} = \sum_{k=0}^n \binom{a}{k}\binom{b}{n-k}$

## References

* Course notes: AlgebraicCombinatorics/tex/FPS/Notations.tex

## Tags

combinatorics, binomial coefficients, generating functions, Fibonacci, Catalan
-/

namespace AlgebraicCombinatorics.FPS

open Finset BigOperators Nat

/-!
## Basic Combinatorial Principles

These are standard results in Mathlib. We provide docstrings explaining
the combinatorial interpretations.
-/

/-- **Addition Principle (Sum Rule)**: If $A$ and $B$ are disjoint finite sets,
then $|A \cup B| = |A| + |B|$.

This is `Finset.card_union_of_disjoint` in Mathlib. -/
theorem addition_principle {α : Type*} [DecidableEq α] (A B : Finset α) (h : Disjoint A B) :
    (A ∪ B).card = A.card + B.card :=
  Finset.card_union_of_disjoint h

/-- **Multiplication Principle (Product Rule)**: If $A$ and $B$ are finite sets,
then $|A \times B| = |A| \cdot |B|$.

This is `Finset.card_product` in Mathlib. -/
theorem multiplication_principle {α β : Type*} (A : Finset α) (B : Finset β) :
    (A ×ˢ B).card = A.card * B.card :=
  Finset.card_product A B

/-- **Bijection Principle**: If there is a bijection between two finite sets $X$ and $Y$,
then $|X| = |Y|$.

This is `Finset.card_bijective` in Mathlib. The converse (equal cardinality implies
existence of bijection) is `Fintype.truncEquivFinOfCardEq`. -/
theorem bijection_principle {α β : Type*} (A : Finset α) (B : Finset β)
    (e : α → β) (he : e.Bijective) (hst : ∀ i, i ∈ A ↔ e i ∈ B) : A.card = B.card :=
  Finset.card_bijective e he hst

/-- A set with $n$ elements has $2^n$ subsets.

This is `Finset.card_powerset` in Mathlib. -/
theorem card_subsets {α : Type*} (A : Finset α) :
    A.powerset.card = 2 ^ A.card :=
  Finset.card_powerset A

/-- A set with $n$ elements has $\binom{n}{k}$ subsets of size $k$.

This is `Finset.card_powersetCard` in Mathlib. -/
theorem card_subsets_of_size {α : Type*} (A : Finset α) (k : ℕ) :
    (A.powersetCard k).card = A.card.choose k :=
  Finset.card_powersetCard k A

/-!
## Binomial Coefficients

The binomial coefficient $\binom{n}{k}$ is defined in Mathlib as `Nat.choose`
for natural numbers and `Ring.choose` for more general rings.

### Definition \ref{def.binom.binom}

For any numbers $n$ and $k$:
$$\binom{n}{k} = \begin{cases}
\frac{n(n-1)(n-2)\cdots(n-k+1)}{k!} & \text{if } k \in \mathbb{N} \\
0 & \text{else}
\end{cases}$$

In Mathlib, this is implemented as:
- `Nat.choose n k` for natural numbers $n, k$
- `Ring.choose r n` for elements $r$ in a binomial ring and $n \in \mathbb{N}$

The key identity relating `Ring.choose` to the textbook definition is:
$$n! \cdot \binom{r}{n} = r(r-1)(r-2)\cdots(r-n+1)$$
which is the descending factorial (descending Pochhammer symbol).
-/

/-- **Definition \ref{def.binom.binom}** (Binomial Coefficient Formula):
For any element $r$ in a field of characteristic zero and $n \in \mathbb{N}$,
$$\binom{r}{n} = \frac{r(r-1)(r-2)\cdots(r-n+1)}{n!}$$

This is the fundamental definition of the binomial coefficient.
In Mathlib, this is expressed using the descending Pochhammer symbol:
`(descPochhammer ℤ n).smeval r = n.factorial • Ring.choose r n`

For fields of characteristic zero, we can write this as a division. -/
theorem binom_def_formula {K : Type*} [Field K] [CharZero K] (r : K) (n : ℕ) :
    Ring.choose r n = (descPochhammer ℤ n).smeval r / n.factorial := by
  have h : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [Ring.descPochhammer_eq_factorial_smul_choose]
  simp only [nsmul_eq_mul]
  field_simp

/-- The descending Pochhammer symbol `(descPochhammer ℤ n).smeval r` equals
the descending factorial $r(r-1)(r-2)\cdots(r-n+1)$.

This is the "falling factorial" or "descending factorial" notation often written
as $(r)_n$ or $r^{\underline{n}}$ in combinatorics.

For natural numbers, this equals `Nat.descFactorial`. -/
theorem descPochhammer_eq_descFactorial (n k : ℕ) :
    (descPochhammer ℤ k).smeval (n : ℤ) = n.descFactorial k :=
  Polynomial.descPochhammer_smeval_eq_descFactorial n k

/-- The binomial coefficient satisfies the factorial formula:
$$n! \cdot \binom{r}{n} = r(r-1)(r-2)\cdots(r-n+1)$$

This is `Ring.descPochhammer_eq_factorial_smul_choose` in Mathlib. -/
theorem binom_factorial_smul {R : Type*} [CommRing R] [BinomialRing R] [NatPowAssoc R]
    (r : R) (n : ℕ) :
    n.factorial • Ring.choose r n = (descPochhammer ℤ n).smeval r :=
  (Ring.descPochhammer_eq_factorial_smul_choose r n).symm

/-- For natural numbers, `Ring.choose` agrees with `Nat.choose`:
$$\binom{n}{k} = \text{Nat.choose } n\, k$$

This is `Ring.choose_natCast` in Mathlib. -/
theorem binom_natCast {R : Type*} [CommRing R] [BinomialRing R] [NatPowAssoc R]
    (n k : ℕ) : Ring.choose (n : R) k = Nat.choose n k :=
  Ring.choose_natCast n k

/-- Base case: $\binom{r}{0} = 1$ for any $r$.

This follows from the definition: the empty product $r(r-1)\cdots(r-0+1)$ equals $1$. -/
theorem binom_zero_right {R : Type*} [CommRing R] [BinomialRing R] [NatPowAssoc R]
    (r : R) : Ring.choose r 0 = 1 :=
  Ring.choose_zero_right r

/-- For $k > 0$, we have $\binom{0}{k} = 0$.

This follows from the definition: the product $0 \cdot (-1) \cdot (-2) \cdots$ has a factor of $0$. -/
theorem binom_zero_left_pos {R : Type*} [CommRing R] [BinomialRing R] [NatPowAssoc R]
    {k : ℕ} (hk : 0 < k) : Ring.choose (0 : R) k = 0 :=
  Ring.choose_zero_pos R hk

/-- First case: $\binom{r}{1} = r$.

This follows from the definition: $\frac{r}{1!} = r$. -/
theorem binom_one_right {R : Type*} [CommRing R] [BinomialRing R] [NatPowAssoc R]
    (r : R) : Ring.choose r 1 = r := by
  rw [Ring.choose_one_right', npow_one]

/-- Example \ref{exa.binom.-1choosek}: For any $k \in \mathbb{N}$,
$\binom{-1}{k} = (-1)^k$. -/
theorem binom_neg_one (k : ℕ) : Ring.choose (-1 : ℤ) k = (-1 : ℤ) ^ k := by
  rw [Ring.choose_neg, show (1 : ℤ) + ↑k - 1 = ↑k by ring, Ring.choose_natCast, Nat.choose_self]
  simp [Units.smul_def, Int.coe_negOnePow_natCast]

/-- The factorial formula for binomial coefficients: For $n, k \in \mathbb{N}$ with $k \leq n$,
$$\binom{n}{k} = \frac{n!}{k!(n-k)!}$$

This is `Nat.choose_eq_factorial_div_factorial` in Mathlib (Equation \eqref{eq.binom.fac-form}). -/
theorem binom_factorial_formula {n k : ℕ} (h : k ≤ n) :
    n.choose k = n.factorial / (k.factorial * (n - k).factorial) :=
  Nat.choose_eq_factorial_div_factorial h

/-- The product of odd numbers 1·3·5·...·(2n-1) equals the double factorial (2n-1)‼. -/
lemma prod_odd_eq_doubleFactorial (n : ℕ) :
    ∏ i ∈ range n, (2 * i + 1) = (2 * n - 1)‼ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prod_range_succ, ih]
    cases n with
    | zero => native_decide
    | succ m =>
      have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      have h2 : 2 * (m + 1 + 1) - 1 = 2 * m + 3 := by omega
      rw [h1, h2]
      have h3 : 2 * m + 3 = 2 * m + 1 + 2 := by ring
      rw [h3, doubleFactorial_add_two]
      ring

/-- The factorial (2n)! equals the product of double factorials (2n)‼ · (2n-1)‼. -/
private lemma factorial_two_mul' (n : ℕ) : (2 * n).factorial = (2 * n)‼ * (2 * n - 1)‼ := by
  cases n with
  | zero => rfl
  | succ m =>
    have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [h]
    exact factorial_eq_mul_doubleFactorial (2 * m + 1)

/-- n! divides the product (1·3·5·...·(2n-1)) · 2^n. -/
lemma factorial_dvd_prod_odd_mul_pow (n : ℕ) :
    n.factorial ∣ (∏ i ∈ range n, (2 * i + 1)) * 2 ^ n := by
  have h_fact : (2 * n).factorial = 2 ^ n * n.factorial * (2 * n - 1)‼ := by
    rw [factorial_two_mul', doubleFactorial_two_mul]
  have h_sub : 2 * n - n = n := by omega
  have h_dvd : n.factorial * n.factorial ∣ (2 * n).factorial := by
    have h2 : n.factorial * n.factorial = n.factorial * (2 * n - n).factorial := by rw [h_sub]
    rw [h2]
    exact factorial_mul_factorial_dvd_factorial (by omega : n ≤ 2 * n)
  rw [h_fact] at h_dvd
  have h : n.factorial ∣ 2 ^ n * (2 * n - 1)‼ := by
    have h1 : 2 ^ n * n.factorial * (2 * n - 1)‼ = n.factorial * (2 ^ n * (2 * n - 1)‼) := by ring
    rw [h1] at h_dvd
    exact (mul_dvd_mul_iff_left (factorial_ne_zero n)).mp h_dvd
  have key : (∏ i ∈ range n, (2 * i + 1)) * 2 ^ n = 2 ^ n * (2 * n - 1)‼ := by
    rw [prod_odd_eq_doubleFactorial]
    ring
  rw [key]
  exact h

/-- Example \ref{exa.binom.2n-choose-n}: For $n \in \mathbb{N}$,
$$\binom{2n}{n} = \frac{1 \cdot 3 \cdot 5 \cdots (2n-1)}{n!} \cdot 2^n$$

This relates the central binomial coefficient to double factorials. -/
theorem binom_two_n_n_eq (n : ℕ) :
    (2 * n).choose n = (∏ i ∈ range n, (2 * i + 1)) * 2 ^ n / n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h_rec := Nat.succ_mul_centralBinom_succ n
    unfold Nat.centralBinom at h_rec
    have h_div : (n + 1) ∣ 2 * (2 * n + 1) * (2 * n).choose n := by
      rw [← h_rec]
      exact Dvd.intro _ rfl
    have h_eq : (2 * (n + 1)).choose (n + 1) = 2 * (2 * n + 1) * (2 * n).choose n / (n + 1) := by
      have h_pos : 0 < n + 1 := Nat.succ_pos n
      symm
      rw [Nat.div_eq_iff_eq_mul_left h_pos h_div]
      linarith [h_rec]
    rw [h_eq, prod_range_succ, factorial_succ, pow_succ, ih]
    obtain ⟨k, hk⟩ := factorial_dvd_prod_odd_mul_pow n
    rw [hk, Nat.mul_div_cancel_left _ (factorial_pos n)]
    symm
    calc (∏ x ∈ range n, (2 * x + 1)) * (2 * n + 1) * (2 ^ n * 2) / ((n + 1) * n.factorial)
        = (2 * n + 1) * 2 * ((∏ x ∈ range n, (2 * x + 1)) * 2 ^ n) / ((n + 1) * n.factorial) := by ring_nf
      _ = (2 * n + 1) * 2 * (n.factorial * k) / ((n + 1) * n.factorial) := by rw [hk]
      _ = (2 * n + 1) * 2 * (n.factorial * k) / (n.factorial * (n + 1)) := by ring_nf
      _ = (2 * n + 1) * 2 * k / (n + 1) := by
          have h1 : (2 * n + 1) * 2 * (n.factorial * k) = n.factorial * ((2 * n + 1) * 2 * k) := by ring
          rw [h1, Nat.mul_div_mul_left _ _ (factorial_pos n)]
      _ = 2 * (2 * n + 1) * k / (n + 1) := by ring_nf

/-- Proposition \ref{prop.binom.rec} (Pascal's Identity) for natural numbers:
$$\binom{m}{n} = \binom{m-1}{n-1} + \binom{m-1}{n}$$

This is the fundamental recurrence for binomial coefficients.
Note: For natural numbers, we need $m > 0$ because when $m = 0$ and $n = 1$,
the LHS is $\binom{0}{1} = 0$ but the RHS (with Nat subtraction) becomes
$\binom{0}{0} + \binom{0}{1} = 1 + 0 = 1$.

This is `Nat.choose_eq_choose_pred_add` in Mathlib. -/
theorem pascal_identity (m n : ℕ) (hn : 0 < n) (hm : 0 < m) :
    m.choose n = (m - 1).choose (n - 1) + (m - 1).choose n := by
  exact Nat.choose_eq_choose_pred_add hm hn

/-- Proposition \ref{prop.binom.rec} (Pascal's Identity) for generalized binomial coefficients:
$$\binom{m}{n} = \binom{m-1}{n-1} + \binom{m-1}{n}$$

This version works for any element $m$ in a binomial ring and any positive natural number $n$.
This is `Ring.choose_succ_succ` in Mathlib, rewritten in the form matching the TeX source. -/
theorem pascal_identity_ring {R : Type*} [CommRing R] [BinomialRing R] [NatPowAssoc R]
    (m : R) (n : ℕ) (hn : 0 < n) :
    Ring.choose m n = Ring.choose (m - 1) (n - 1) + Ring.choose (m - 1) n := by
  have h : m = (m - 1) + 1 := by ring
  have hn' := Nat.succ_pred_eq_of_pos hn
  conv_lhs => rw [h, ← hn', Nat.pred_eq_sub_one]
  rw [Ring.choose_succ_succ (m - 1) (n - 1)]
  simp only [Nat.sub_add_cancel hn]

/-- Proposition \ref{prop.binom.rec} (Pascal's Identity) in the "successor" form:
$$\binom{r+1}{k+1} = \binom{r}{k} + \binom{r}{k+1}$$

This is the fundamental recurrence for generalized binomial coefficients.
This is `Ring.choose_succ_succ` in Mathlib. -/
theorem pascal_identity_succ {R : Type*} [CommRing R] [BinomialRing R] [NatPowAssoc R]
    (r : R) (k : ℕ) :
    Ring.choose (r + 1) (k + 1) = Ring.choose r k + Ring.choose r (k + 1) :=
  Ring.choose_succ_succ r k

/-- Pascal's identity for integers:
$$\binom{m}{n} = \binom{m-1}{n-1} + \binom{m-1}{n}$$

This is a special case of `pascal_identity_ring` for the integers. -/
theorem pascal_identity_int (m : ℤ) (n : ℕ) (hn : 0 < n) :
    Ring.choose m n = Ring.choose (m - 1) (n - 1) + Ring.choose (m - 1) n :=
  pascal_identity_ring m n hn

/-- Pascal's identity for rationals:
$$\binom{m}{n} = \binom{m-1}{n-1} + \binom{m-1}{n}$$

This is a special case of `pascal_identity_ring` for the rationals. -/
theorem pascal_identity_rat (m : ℚ) (n : ℕ) (hn : 0 < n) :
    Ring.choose m n = Ring.choose (m - 1) (n - 1) + Ring.choose (m - 1) n :=
  pascal_identity_ring m n hn

/-- Proposition \ref{prop.binom.0}: Let $m, n \in \mathbb{N}$ with $m < n$.
Then $\binom{m}{n} = 0$.

This is `Nat.choose_eq_zero_of_lt` in Mathlib. -/
theorem binom_zero_of_lt {m n : ℕ} (h : m < n) : m.choose n = 0 :=
  Nat.choose_eq_zero_of_lt h

/-- Theorem \ref{thm.binom.sym} (Symmetry of Binomial Coefficients):
Let $n \in \mathbb{N}$ and $k \in \mathbb{R}$. Then $\binom{n}{k} = \binom{n}{n-k}$.

For natural numbers $k \leq n$, this is `Nat.choose_symm`. -/
theorem binom_symm {n k : ℕ} (h : k ≤ n) : n.choose k = n.choose (n - k) :=
  (Nat.choose_symm h).symm

/-- Symmetry of binomial coefficients when $n = a + b$.
This is a useful variant: $\binom{a+b}{a} = \binom{a+b}{b}$. -/
@[simp]
theorem binom_symm_add (a b : ℕ) : (a + b).choose a = (a + b).choose b :=
  Nat.choose_symm_add

/-- Symmetry of binomial coefficients: if $n = a + b$, then $\binom{n}{a} = \binom{n}{b}$. -/
theorem binom_symm_of_eq_add {n a b : ℕ} (h : n = a + b) : n.choose a = n.choose b :=
  Nat.choose_symm_of_eq_add h

/-- Symmetry of generalized binomial coefficients for `Ring.choose` when the first
argument is a natural number. This extends `binom_symm` to binomial rings. -/
theorem binom_symm_ring {R : Type*} [CommRing R] [BinomialRing R] [NatPowAssoc R]
    (n k : ℕ) (h : k ≤ n) : Ring.choose (n : R) k = Ring.choose (n : R) (n - k) := by
  simp only [Ring.choose_natCast]
  congr 1
  exact (Nat.choose_symm h).symm

/-!
## The Fibonacci Sequence (Example 1)

The Fibonacci sequence $(f_0, f_1, f_2, \ldots)$ is defined by:
- $f_0 = 0$
- $f_1 = 1$
- $f_n = f_{n-1} + f_{n-2}$ for $n \geq 2$

Its generating function is $F(x) = \sum_{n \geq 0} f_n x^n = \frac{x}{1-x-x^2}$.

**Mathlib equivalences**: The Fibonacci sequence is `Nat.fib` in Mathlib. The golden ratios
are `Real.goldenRatio` and `Real.goldenConj` in `Mathlib.NumberTheory.Real.GoldenRatio`.
Binet's formula is proved there as `Real.coe_fib_eq`.
-/

/-- The Fibonacci sequence.

**Mathlib note**: This is definitionally equal to `Nat.fib` in Mathlib. -/
def fibonacci : ℕ → ℕ := Nat.fib

/-- Our definition of `fibonacci` is definitionally equal to `Nat.fib`. -/
theorem fibonacci_eq_nat_fib (n : ℕ) : fibonacci n = Nat.fib n := rfl

/-- The golden ratio $\phi_+ = \frac{1 + \sqrt{5}}{2}$.

**Mathlib note**: This is equal to `Real.goldenRatio` in Mathlib. -/
noncomputable def goldenRatioPlus : ℝ := (1 + Real.sqrt 5) / 2

/-- The conjugate golden ratio $\phi_- = \frac{1 - \sqrt{5}}{2}$.

**Mathlib note**: This is equal to `Real.goldenConj` in Mathlib. -/
noncomputable def goldenRatioMinus : ℝ := (1 - Real.sqrt 5) / 2

/-- Our `goldenRatioPlus` equals Mathlib's `Real.goldenRatio`. -/
theorem goldenRatioPlus_eq : goldenRatioPlus = Real.goldenRatio := rfl

/-- Our `goldenRatioMinus` equals Mathlib's `Real.goldenConj`. -/
theorem goldenRatioMinus_eq : goldenRatioMinus = Real.goldenConj := rfl

/-- The generating function of the Fibonacci sequence is $\frac{x}{1-x-x^2}$.

Equation \eqref{eq.sec.gf.exas.1.Fx=1}. -/
theorem fibonacci_gf : (PowerSeries.mk (fun n => (fibonacci n : ℚ)) : PowerSeries ℚ) =
    (PowerSeries.X : PowerSeries ℚ) * ((1 : PowerSeries ℚ) - PowerSeries.X - PowerSeries.X ^ 2)⁻¹ := by
  let F := PowerSeries.mk (fun n => (Nat.fib n : ℚ))
  let D := (1 : PowerSeries ℚ) - PowerSeries.X - PowerSeries.X ^ 2
  -- First, check that constantCoeff D ≠ 0
  have hD : PowerSeries.constantCoeff D ≠ 0 := by
    simp only [D, map_sub, map_one, PowerSeries.constantCoeff_X, sub_zero, map_pow]
    norm_num
  -- Coefficient of F at n is fib n
  have hF : ∀ n, PowerSeries.coeff n F = (Nat.fib n : ℚ) := fun n => PowerSeries.coeff_mk n _
  -- We need F * D = X
  have key : F * D = PowerSeries.X := by
    ext n
    simp only [D, mul_sub, mul_one, map_sub]
    rw [hF]
    -- For F * X
    have hFX : (PowerSeries.coeff n) (F * PowerSeries.X) =
        if n = 0 then 0 else (Nat.fib (n - 1) : ℚ) := by
      rcases n with _ | n
      · simp [PowerSeries.coeff_zero_mul_X]
      · simp only [PowerSeries.coeff_succ_mul_X, hF, Nat.succ_ne_zero, ↓reduceIte,
          Nat.add_sub_cancel]
    -- For F * X^2
    have hFX2 : (PowerSeries.coeff n) (F * PowerSeries.X ^ 2) =
        if n < 2 then 0 else (Nat.fib (n - 2) : ℚ) := by
      rcases n with _ | _ | n
      · simp [PowerSeries.coeff_mul_X_pow']
      · simp [PowerSeries.coeff_mul_X_pow']
      · have h : 2 ≤ n + 1 + 1 := by omega
        rw [PowerSeries.coeff_mul_X_pow' _ 2 (n + 1 + 1)]
        simp only [h, ↓reduceIte, hF, show ¬(n + 1 + 1 < 2) by omega]
    rw [hFX, hFX2]
    simp only [PowerSeries.coeff_X]
    -- Case split on n
    rcases n with _ | _ | n
    · -- n = 0: fib 0 - 0 - 0 = 0
      simp [Nat.fib_zero]
    · -- n = 1: fib 1 - fib 0 - 0 = 1
      simp [Nat.fib_zero, Nat.fib_one]
    · -- n >= 2: fib (n+2) - fib (n+1) - fib n = 0 by recurrence
      simp only [show ¬(n + 2 = 0) by omega, ite_false,
        show ¬(n + 2 = 1) by omega, show ¬(n + 2 < 2) by omega]
      -- fib (n+2) - fib (n+1) - fib n = 0
      have h1 : n + 2 - 1 = n + 1 := by omega
      have h2 : n + 2 - 2 = n := by omega
      rw [h1, h2]
      have := Nat.fib_add_two (n := n)
      -- fib(n+2) = fib(n) + fib(n+1), so fib(n+2) - fib(n+1) - fib(n) = 0
      simp only [this, Nat.cast_add]
      ring
  -- Now conclude using key
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hD]
  exact key

/-- **Binet's Formula**: For any $n \in \mathbb{N}$,
$$f_n = \frac{1}{\sqrt{5}} \left( \phi_+^n - \phi_-^n \right)$$
where $\phi_\pm = \frac{1 \pm \sqrt{5}}{2}$ are the golden ratios.

**Mathlib note**: This is proved as `Real.coe_fib_eq` in Mathlib. -/
theorem fibonacci_binet (n : ℕ) :
    (fibonacci n : ℝ) = (goldenRatioPlus ^ n - goldenRatioMinus ^ n) / Real.sqrt 5 := by
  simp only [fibonacci_eq_nat_fib, goldenRatioPlus_eq, goldenRatioMinus_eq]
  exact Real.coe_fib_eq n

/-!
## Dyck Words and Catalan Numbers (Example 2)

A **Dyck word** of length $2n$ is a $2n$-tuple of $0$s and $1$s such that:
1. There are exactly $n$ zeros and $n$ ones
2. For each prefix, the number of $0$s does not exceed the number of $1$s

The **Catalan numbers** $c_n$ count Dyck words of length $2n$.

**Mathlib equivalences**:
- Catalan numbers are defined in `Mathlib.Combinatorics.Enumerative.Catalan` as `Nat.catalan`
  using the recurrence relation. The explicit formula `catalan n = centralBinom n / (n + 1)`
  is proved as `Nat.catalan_eq_centralBinom_div`.
- Dyck words are formalized in `Mathlib.Combinatorics.Enumerative.DyckWord` as the `DyckWord`
  structure using a `DyckStep` enum (U for up, D for down) rather than Bool.
-/

/-- A list is a Dyck word if it consists of 0s and 1s, has equal numbers
of each, and every prefix has at least as many 1s as 0s.

Here we represent 1 as `true` and 0 as `false`.

**Mathlib note**: This is an alternative representation to Mathlib's `DyckWord` structure,
which uses a `DyckStep` enum with constructors `U` (up) and `D` (down). The two representations
are equivalent via the bijection sending `true` to `U` and `false` to `D`. -/
def isDyckWord (w : List Bool) : Prop :=
  w.count true = w.count false ∧
  ∀ k : ℕ, k ≤ w.length →
    (w.take k).count false ≤ (w.take k).count true

/-- The Catalan numbers, defined as $c_n = \frac{1}{n+1}\binom{2n}{n}$.

**Mathlib note**: This is equivalent to Mathlib's `catalan`, which is defined recursively.
The equivalence is proved by `catalan_eq_mathlib_catalan`. -/
def catalan (n : ℕ) : ℕ := (2 * n).choose n / (n + 1)

/-- Our explicit definition of `catalan` equals Mathlib's recursive `catalan`.

This follows from `catalan_eq_centralBinom_div` in Mathlib. -/
theorem catalan_eq_mathlib_catalan (n : ℕ) : catalan n = _root_.catalan n := by
  rw [catalan, catalan_eq_centralBinom_div, Nat.centralBinom]

/-- First few Catalan numbers: $c_0 = 1$. -/
@[simp]
theorem catalan_zero : catalan 0 = 1 := by rfl

/-- First few Catalan numbers: $c_1 = 1$. -/
@[simp]
theorem catalan_one : catalan 1 = 1 := by rfl

/-- First few Catalan numbers: $c_2 = 2$. -/
@[simp]
theorem catalan_two : catalan 2 = 2 := by rfl

/-- First few Catalan numbers: $c_3 = 5$. -/
@[simp]
theorem catalan_three : catalan 3 = 5 := by rfl

/-- The Catalan recurrence relation:
$$c_n = \sum_{k=0}^{n-1} c_k c_{n-1-k}$$
for $n \geq 1$, with $c_0 = 1$. -/
theorem catalan_recurrence (n : ℕ) (hn : 0 < n) :
    catalan n = ∑ k ∈ range n, catalan k * catalan (n - 1 - k) := by
  -- Convert to Mathlib's catalan
  simp_rw [catalan_eq_mathlib_catalan]
  -- Write n = m + 1 for some m
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  -- Simplify m.succ - 1 - x = m - x
  conv_rhs => arg 2; ext x; rw [show m.succ - 1 - x = m - x by omega]
  -- Apply Mathlib's recurrence and convert sum over Fin to sum over range
  rw [_root_.catalan_succ]
  exact (Finset.sum_range (fun i => _root_.catalan i * _root_.catalan (m - i))).symm

/-- Equation \eqref{eq.sec.gf.exas.cn=1/(n+1)}: The explicit formula for Catalan numbers:
$$c_n = \frac{1}{n+1} \binom{2n}{n}$$ -/
theorem catalan_explicit (n : ℕ) : catalan n = (2 * n).choose n / (n + 1) := by
  rfl

/-- Equation \eqref{eq.sec.gf.exas.cn=diff}: Alternative form of Catalan numbers:
$$c_n = \binom{2n}{n} - \binom{2n}{n-1}$$

Note: For $n = 0$, this becomes $1 - \binom{0}{-1} = 1 - 0 = 1$, which is correct since
$\binom{m}{k} = 0$ when $k < 0$ (or equivalently, when $k$ is not a natural number).
In Lean's `Nat.choose`, we have `0.choose (0 - 1) = 0.choose 0 = 1` due to subtraction
truncation, so this theorem requires $n > 0$. -/
theorem catalan_as_diff {n : ℕ} (hn : 0 < n) :
    catalan n = (2 * n).choose n - (2 * n).choose (n - 1) := by
  -- Key identity: (2n).choose (n-1) * (n+1) = (2n).choose n * n
  -- This follows from choose_succ_right_eq
  have key : (2 * n).choose (n - 1) * (n + 1) = (2 * n).choose n * n := by
    have h : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
    have eq := Nat.choose_succ_right_eq (2 * n) (n - 1)
    rw [h, show 2 * n - (n - 1) = n + 1 by omega] at eq
    linarith
  rw [catalan]
  have h_dvd : (n + 1) ∣ (2 * n).choose n := Nat.succ_dvd_centralBinom n
  rw [Nat.div_eq_iff_eq_mul_right (Nat.succ_pos n) h_dvd, Nat.mul_sub_left_distrib]
  -- Transform (n+1) * choose to n * choose using key
  have key' : (n + 1) * (2 * n).choose (n - 1) = n * (2 * n).choose n := by
    calc (n + 1) * (2 * n).choose (n - 1)
        = (2 * n).choose (n - 1) * (n + 1) := mul_comm _ _
      _ = (2 * n).choose n * n := key
      _ = n * (2 * n).choose n := mul_comm _ _
  rw [key', ← Nat.sub_mul]
  simp

/-- The generating function of the Catalan numbers satisfies
$C(x) = 1 + x \cdot C(x)^2$. -/
theorem catalan_gf_equation :
    let C := PowerSeries.mk (fun n => (catalan n : ℚ))
    C = 1 + PowerSeries.X * C ^ 2 := by
  -- Use Mathlib's result: catalanSeries ^ 2 * X + 1 = catalanSeries
  have h := PowerSeries.catalanSeries_sq_mul_X_add_one
  -- Rearrange to get: catalanSeries = 1 + X * catalanSeries ^ 2
  have h' : PowerSeries.catalanSeries = 1 + PowerSeries.X * PowerSeries.catalanSeries ^ 2 := by
    calc PowerSeries.catalanSeries
        = PowerSeries.catalanSeries ^ 2 * PowerSeries.X + 1 := h.symm
      _ = 1 + PowerSeries.X * PowerSeries.catalanSeries ^ 2 := by ring
  -- Show that C equals the map of Mathlib's catalanSeries to ℚ
  have hC : PowerSeries.mk (fun n => (catalan n : ℚ)) =
      PowerSeries.map (algebraMap ℕ ℚ) PowerSeries.catalanSeries := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_map, PowerSeries.catalanSeries_coeff]
    rw [catalan_eq_mathlib_catalan]
    rfl
  -- Now prove the goal using these facts
  intro C
  change PowerSeries.mk (fun n => (catalan n : ℚ)) =
    1 + PowerSeries.X * (PowerSeries.mk (fun n => (catalan n : ℚ))) ^ 2
  conv_lhs => rw [hC, h']
  conv_rhs => rw [hC]
  rw [map_add, map_one, map_mul, map_pow, PowerSeries.map_X]

/-- Recurrence relation for Ring.choose at 1/2:
$(n + 1) \cdot \binom{1/2}{n+1} = (1/2 - n) \cdot \binom{1/2}{n}$.

This follows from the descending Pochhammer formula for binomial coefficients. -/
lemma choose_half_recurrence (n : ℕ) :
    (n + 1 : ℚ) * Ring.choose (1/2 : ℚ) (n + 1) = (1/2 - n) * Ring.choose (1/2 : ℚ) n := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose (1/2 : ℚ) (n + 1)
  have h' := Ring.descPochhammer_eq_factorial_smul_choose (1/2 : ℚ) n
  rw [descPochhammer_succ_right] at h
  simp only [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, pow_one, pow_zero, factorial_succ, nsmul_eq_mul] at h h'
  rw [Nat.cast_mul] at h
  rw [h'] at h
  have h2 : (1/2 - (n : ℚ) * 1) = 1/2 - n := by ring
  rw [h2] at h
  field_simp at h ⊢
  have hcast : (↑(n + 1) : ℚ) = (n : ℚ) + 1 := by simp
  rw [hcast] at h
  ring_nf at h ⊢
  linarith [h]

/-- Key identity: $\binom{1/2}{n+1} \cdot (-4)^{n+1} \cdot (n+1) = -2 \cdot \binom{2n}{n}$.

This relates the binomial coefficient at 1/2 to the central binomial coefficient. -/
lemma A_eq_neg_two_centralBinom (n : ℕ) :
    Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) * (n + 1) = -2 * Nat.centralBinom n := by
  induction n with
  | zero =>
    rw [Ring.choose_one_right]
    simp [Nat.centralBinom]
    ring
  | succ n ih =>
    have hne' : (n + 1 : ℚ) ≠ 0 := by positivity

    have key : Ring.choose (1/2 : ℚ) (n + 2) * (n + 2) = (-1/2 - n) * Ring.choose (1/2 : ℚ) (n + 1) := by
      have := choose_half_recurrence (n + 1)
      simp only [Nat.cast_add, Nat.cast_one] at this ⊢
      linarith [this]

    have step1 : Ring.choose (1/2 : ℚ) (n + 1 + 1) * (-4 : ℚ)^(n + 1 + 1) * ((n + 1 : ℕ) + 1 : ℚ)
        = Ring.choose (1/2 : ℚ) (n + 2) * (-4 : ℚ)^(n + 2) * (n + 2 : ℚ) := by
      simp only [Nat.cast_add, Nat.cast_one]; ring

    have step2 : Ring.choose (1/2 : ℚ) (n + 2) * (-4 : ℚ)^(n + 2) * (n + 2 : ℚ)
        = (-1/2 - n) * Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 2) := by
      calc Ring.choose (1/2 : ℚ) (n + 2) * (-4 : ℚ)^(n + 2) * (n + 2 : ℚ)
          = (Ring.choose (1/2 : ℚ) (n + 2) * (n + 2 : ℚ)) * (-4 : ℚ)^(n + 2) := by ring
        _ = ((-1/2 - n) * Ring.choose (1/2 : ℚ) (n + 1)) * (-4 : ℚ)^(n + 2) := by rw [key]
        _ = (-1/2 - n) * Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 2) := by ring

    have step3 : (-1/2 - n) * Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 2)
        = (2*n + 1) * 2 * Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) := by
      calc (-1/2 - n) * Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 2)
          = (-1/2 - n) * Ring.choose (1/2 : ℚ) (n + 1) * ((-4 : ℚ)^(n + 1) * (-4)) := by rw [pow_succ]
        _ = (-1/2 - n) * (-4) * Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) := by ring
        _ = (2*n + 1) * 2 * Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) := by ring

    have step4 : (2*(n : ℚ) + 1) * 2 * Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1)
        = (2*n + 1) * 2 / (n + 1) * (Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) * (n + 1)) := by
      field_simp

    have step5 : (2*(n : ℚ) + 1) * 2 / (n + 1) * (Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) * (n + 1))
        = (2*n + 1) * 2 / (n + 1) * (-2 * Nat.centralBinom n) := by rw [ih]

    have step6 : (2*(n : ℚ) + 1) * 2 / (n + 1) * (-2 * (Nat.centralBinom n : ℚ))
        = -2 * Nat.centralBinom (n + 1) := by
      have hcb' := Nat.succ_mul_centralBinom_succ n
      have h2 : (2 * (2 * n + 1) * Nat.centralBinom n : ℕ) = (n + 1) * Nat.centralBinom (n + 1) := hcb'.symm
      have h3 : (2 * (2 * (n : ℚ) + 1) * ↑(Nat.centralBinom n)) = ((n + 1) * ↑(Nat.centralBinom (n + 1))) := by
        calc (2 * (2 * (n : ℚ) + 1) * ↑(Nat.centralBinom n))
            = ↑(2 * (2 * n + 1) * Nat.centralBinom n) := by push_cast; ring
          _ = ↑((n + 1) * Nat.centralBinom (n + 1)) := by rw [h2]
          _ = (n + 1) * ↑(Nat.centralBinom (n + 1)) := by push_cast; ring
      calc (2*(n : ℚ) + 1) * 2 / (n + 1) * (-2 * (Nat.centralBinom n : ℚ))
          = -(2 * (2 * (n : ℚ) + 1) * ↑(Nat.centralBinom n) * 2 / (n + 1)) := by ring
        _ = -(((n + 1) * ↑(Nat.centralBinom (n + 1))) * 2 / (n + 1)) := by rw [h3]
        _ = -(↑(Nat.centralBinom (n + 1)) * 2) := by field_simp
        _ = -2 * Nat.centralBinom (n + 1) := by ring

    calc Ring.choose (1/2 : ℚ) (n + 1 + 1) * (-4 : ℚ)^(n + 1 + 1) * ((n + 1 : ℕ) + 1 : ℚ)
        = Ring.choose (1/2 : ℚ) (n + 2) * (-4 : ℚ)^(n + 2) * (n + 2 : ℚ) := step1
      _ = (-1/2 - n) * Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 2) := step2
      _ = (2*(n : ℚ) + 1) * 2 * Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) := step3
      _ = (2*n + 1) * 2 / (n + 1) * (Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) * (n + 1)) := step4
      _ = (2*n + 1) * 2 / (n + 1) * (-2 * Nat.centralBinom n) := step5
      _ = -2 * Nat.centralBinom (n + 1) := step6

/-- The key coefficient identity for the Catalan generating function:
$\binom{1/2}{n+1} \cdot (-4)^{n+1} = -2 \cdot c_n$. -/
lemma choose_half_neg4_pow_eq (n : ℕ) :
    Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) = -2 * catalan n := by
  have h := A_eq_neg_two_centralBinom n
  have hne : (n + 1 : ℚ) ≠ 0 := by positivity
  -- centralBinom n = (n+1) * catalan n
  have hdvd : (n + 1) ∣ Nat.centralBinom n := Nat.succ_dvd_centralBinom n
  have hcb : (Nat.centralBinom n : ℚ) = (n + 1) * catalan n := by
    simp only [catalan, Nat.centralBinom]
    have eq := Nat.div_mul_cancel hdvd
    simp only [Nat.centralBinom] at eq
    have eq' : (((2 * n).choose n : ℕ) : ℚ) = ↑((2 * n).choose n / (n + 1) * (n + 1)) := by rw [eq]
    rw [eq']
    push_cast
    ring
  rw [hcb] at h
  calc Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1)
      = Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) * (n + 1) / (n + 1) := by field_simp
    _ = -2 * ((n + 1) * catalan n) / (n + 1) := by rw [h]
    _ = -2 * catalan n := by field_simp

/-- The generating function of the Catalan numbers is related to $\sqrt{1 - 4x}$.

The exact formula $C(x) = \frac{1 - \sqrt{1 - 4x}}{2x}$ is reformulated as
$2x \cdot C(x) = 1 - \sqrt{1 - 4x}$ to avoid division by $x$ in power series
(since $x$ is not a unit in the ring of formal power series).

The square root $\sqrt{1 - 4x}$ is represented by the binomial series
$\sum_{n \geq 0} \binom{1/2}{n} (-4x)^n = \sum_{n \geq 0} \binom{1/2}{n} (-4)^n x^n$.

Equation \eqref{eq.sec.gf.exas.2.-}. -/
theorem catalan_gf_explicit :
    (2 : ℚ) • (PowerSeries.mk (fun n => (catalan n : ℚ)) * PowerSeries.X) =
      (1 : PowerSeries ℚ) - PowerSeries.mk (fun n => Ring.choose (1/2 : ℚ) n * (-4 : ℚ)^n) := by
  ext n
  simp only [PowerSeries.coeff_smul, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_mk,
    smul_eq_mul]
  cases n with
  | zero =>
    simp only [PowerSeries.coeff_zero_mul_X, mul_zero, pow_zero, mul_one]
    rw [Ring.choose_zero_right]
    simp
  | succ n =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    -- The key identity: 2 * catalan n = -Ring.choose (1/2) (n+1) * (-4)^(n+1)
    have h := choose_half_neg4_pow_eq n
    have h' : -Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) = 2 * catalan n := by linarith [h]
    calc 2 * (catalan n : ℚ) = -Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) := h'.symm
      _ = 0 - Ring.choose (1/2 : ℚ) (n + 1) * (-4 : ℚ)^(n + 1) := by ring

/-!
## The Vandermonde Convolution (Example 3)

The **Vandermonde convolution identity** (also called Chu-Vandermonde):
$$\binom{a+b}{n} = \sum_{k=0}^{n} \binom{a}{k} \binom{b}{n-k}$$
-/

/-- The Vandermonde convolution identity:
$$\binom{a+b}{n} = \sum_{k=0}^{n} \binom{a}{k} \binom{b}{n-k}$$

**Mathlib note**: Mathlib's `Nat.add_choose_eq` uses `∑ ij ∈ antidiagonal n` instead of
`∑ k ∈ range (n + 1)`. The two formulations are equivalent via
`Finset.sum_antidiagonal_eq_sum_range_succ_mk`. This version matches the source material. -/
theorem vandermonde_convolution (a b n : ℕ) :
    (a + b).choose n = ∑ k ∈ range (n + 1), a.choose k * b.choose (n - k) := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-!
## Solving a Recurrence (Example 4)

Consider the sequence $(a_0, a_1, a_2, \ldots)$ defined by:
- $a_0 = 1$
- $a_{n+1} = 2a_n + n$ for all $n \geq 0$

Using generating functions, we can show that $a_n = 2^{n+1} - (n+1)$.
-/

/-- The sequence defined by $a_0 = 1$ and $a_{n+1} = 2a_n + n$. -/
def exampleRecurrence : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * exampleRecurrence n + n

/-- First few values: $a_0 = 1$. -/
@[simp]
theorem exampleRecurrence_zero : exampleRecurrence 0 = 1 := rfl

/-- First few values: $a_1 = 2$. -/
@[simp]
theorem exampleRecurrence_one : exampleRecurrence 1 = 2 := rfl

/-- First few values: $a_2 = 5$. -/
@[simp]
theorem exampleRecurrence_two : exampleRecurrence 2 = 5 := rfl

/-- The explicit formula: $a_n = 2^{n+1} - (n+1)$. -/
theorem exampleRecurrence_explicit (n : ℕ) :
    exampleRecurrence n = 2 ^ (n + 1) - (n + 1) := by
  induction n with
  | zero => simp [exampleRecurrence]
  | succ n ih =>
    simp only [exampleRecurrence]
    rw [ih]
    -- Need to show: 2 * (2 ^ (n + 1) - (n + 1)) + n = 2 ^ (n + 2) - (n + 2)
    have h1 : n + 1 ≤ 2 ^ (n + 1) := (Nat.lt_pow_self (by norm_num : 1 < 2)).le
    have h2 : n + 2 ≤ 2 ^ (n + 2) := (Nat.lt_pow_self (by norm_num : 1 < 2)).le
    omega

/-!
## Auxiliary Generating Function Results

These are helper results about power series used in the examples above.
-/

/-- The geometric series: $\frac{1}{1-x} = 1 + x + x^2 + x^3 + \cdots$

Equation \eqref{eq.sec.gf.exas.1.1/1-x}. -/
theorem geometric_series :
    (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ = PowerSeries.mk (fun _ => (1 : ℚ)) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · exact PowerSeries.mk_one_mul_one_sub_eq_one ℚ
  · simp [PowerSeries.constantCoeff_X]

/-- Helper lemma: $(1 - α \cdot X) \cdot \sum_{n \geq 0} α^n X^n = 1$. -/
private lemma one_sub_smul_X_mul_geom (α : ℚ) :
    (1 - α • PowerSeries.X : PowerSeries ℚ) * PowerSeries.mk (fun n => α ^ n) = 1 := by
  ext n
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_one, PowerSeries.coeff_mk]
  induction n with
  | zero =>
    rw [Finset.Nat.antidiagonal_zero]
    simp
  | succ n ih =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    rw [Finset.Nat.sum_antidiagonal_succ]
    have h0 : PowerSeries.coeff 0 (1 - α • PowerSeries.X : PowerSeries ℚ) = 1 := by simp
    rw [h0]
    simp only [one_mul]
    conv_lhs =>
      arg 2
      arg 2
      ext x
      rw [show PowerSeries.coeff (x.1 + 1) (1 - α • PowerSeries.X : PowerSeries ℚ) =
          if x.1 = 0 then -α else 0 by
        rcases x.1 with _ | k
        · simp
        · simp only [map_sub, PowerSeries.coeff_one, Nat.add_one_ne_zero, ↓reduceIte,
            PowerSeries.coeff_smul, PowerSeries.coeff_X, smul_eq_mul]
          norm_num]
    have hfilter : (antidiagonal n).filter (fun x => x.1 = 0) = {(0, n)} := by
      ext x
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton]
      constructor
      · intro ⟨hsum, h0⟩
        ext <;> omega
      · intro h
        simp [h]
    rw [← Finset.sum_filter_add_sum_filter_not (antidiagonal n) (fun x => x.1 = 0)]
    simp only [hfilter, Finset.sum_singleton, ↓reduceIte, neg_mul]
    have hzero : ∑ x ∈ (antidiagonal n).filter (fun x => ¬x.1 = 0),
        (if x.1 = 0 then -α else 0) * α ^ x.2 = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_filter] at hx
      simp [hx.2]
    rw [hzero]
    ring

/-- Generalized geometric series: $\frac{1}{1-\alpha x} = \sum_{k \geq 0} \alpha^k x^k$

Equation \eqref{eq.sec.gf.exas.1.1/1-ax}. -/
theorem geometric_series_scaled (α : ℚ) :
    (1 - α • PowerSeries.X : PowerSeries ℚ)⁻¹ = PowerSeries.mk (fun n => α ^ n) := by
  have hconst : PowerSeries.constantCoeff (1 - α • PowerSeries.X : PowerSeries ℚ) ≠ 0 := by simp
  rw [PowerSeries.inv_eq_iff_mul_eq_one hconst, mul_comm]
  exact one_sub_smul_X_mul_geom α

/-- The derivative of $\frac{1}{1-x}$ is $\frac{1}{(1-x)^2}$.

Equation \eqref{eq.sec.gf.exas.4.1/(1-x)2}. -/
theorem deriv_inv_one_minus_x :
    (PowerSeries.derivative (R := ℚ)) ((1 - PowerSeries.X : PowerSeries ℚ)⁻¹) =
      (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ ^ 2 := by
  rw [PowerSeries.derivative_inv']
  simp [sub_eq_add_neg]

/-- The power series $\sum_{n \geq 0} (n+1) x^n = \frac{1}{(1-x)^2}$.

Equation \eqref{eq.sec.gf.exas.4.1/(1-x)2}. -/
theorem sum_n_plus_one_pow :
    PowerSeries.mk (fun n => (n + 1 : ℚ)) = (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ ^ 2 := by
  -- First show that invOneSubPow ℚ 2 has the right coefficients
  have h : (PowerSeries.invOneSubPow ℚ 2).val = PowerSeries.mk (fun n => (n + 1 : ℚ)) := by
    simp only [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    ext n
    simp [Nat.choose_one_right, add_comm]
  rw [← h]
  -- Use the key relationship between invOneSubPow and (1 - X)⁻¹
  have key := PowerSeries.invOneSubPow_eq_inv_one_sub_pow (S := ℚ) (d := 2)
  simp only [key, Units.val_pow_eq_pow_val]
  congr 1
  -- Show that the inverse of the unit (1 - X) equals (1 - X)⁻¹ in the ring
  have hu_inv_val : (Units.mkOfMulEqOne (1 - PowerSeries.X) (PowerSeries.mk 1 : PowerSeries ℚ)
      (Eq.trans (mul_comm _ _) (PowerSeries.mk_one_mul_one_sub_eq_one ℚ)))⁻¹.val =
      PowerSeries.mk 1 := rfl
  rw [hu_inv_val]
  -- Show mk 1 = (1 - X)⁻¹
  have hconst : (PowerSeries.constantCoeff (R := ℚ)) (1 - PowerSeries.X : PowerSeries ℚ) ≠ 0 := by simp
  rw [eq_comm, PowerSeries.inv_eq_iff_mul_eq_one hconst]
  convert PowerSeries.mk_one_mul_one_sub_eq_one ℚ using 1

/-- The power series $\sum_{n \geq 1} n x^n = \frac{x}{(1-x)^2}$.

Equation \eqref{eq.sec.gf.exas.4.x/(1-x)2}. -/
theorem sum_n_pow :
    PowerSeries.mk (fun n => (n : ℚ)) = PowerSeries.X * (1 - PowerSeries.X : PowerSeries ℚ)⁻¹ ^ 2 := by
  rw [← sum_n_plus_one_pow]
  ext n
  simp only [PowerSeries.coeff_mk]
  cases n with
  | zero => simp
  | succ n => simp [PowerSeries.coeff_succ_X_mul]

end AlgebraicCombinatorics.FPS
