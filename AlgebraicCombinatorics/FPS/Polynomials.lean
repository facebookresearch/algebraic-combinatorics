/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib

/-!
# Polynomials

This file formalizes the relationship between polynomials and formal power series (FPS),
following the treatment in the Algebraic Combinatorics book.

## Main Content

The key insight is that polynomials can be viewed as FPSs with only finitely many nonzero
coefficients. In Mathlib:
- `PowerSeries R` (notation: `R⟦X⟧`) is the type of formal power series
- `Polynomial R` (notation: `R[X]`) is the type of univariate polynomials
- `Polynomial.toPowerSeries` embeds polynomials into power series

## Main Definitions

* `FPS.IsPolynomial` - A predicate characterizing when a power series is a polynomial
  (i.e., has only finitely many nonzero coefficients)
* `FPS.polynomialSubalgebra` - The K-subalgebra of polynomial power series (Theorem 7.5.2)
* `FPS.polynomialSubring` - The subring of polynomial power series (Theorem 7.5.2)
* `FPS.polynomialSubmodule` - The K-submodule of polynomial power series (Theorem 7.5.2)
* `FPS.polyEval` - Polynomial evaluation at an element of a K-algebra (Definition 7.5.6)
* Notation `f⦃a⦄` for polynomial evaluation (corresponds to book notation `f[a]`)

## Main Results

* `FPS.isPolynomial_iff_finite_support` - A power series is a polynomial iff it has finite support
* `FPS.isPolynomial_add` - The sum of polynomials is a polynomial
* `FPS.isPolynomial_mul` - The product of polynomials is a polynomial
* `FPS.isPolynomial_neg` - The negation of a polynomial is a polynomial
* `FPS.isPolynomial_sub` - The difference of polynomials is a polynomial

## Evaluation/Substitution (def.pol.subs)

The evaluation of a polynomial `f` at an element `a` of a `K`-algebra `A` is denoted
`polyEval f a` or `f⦃a⦄`. This corresponds to Definition 7.5.6 (def.pol.subs) in the source:
  f[a] := Σ_{n ∈ ℕ} f_n · a^n

Key properties (Theorem 7.5.7, thm.pol.eval.a+b):
- `(f + g)⦃a⦄ = f⦃a⦄ + g⦃a⦄` : `eval_add'`
- `(f * g)⦃a⦄ = f⦃a⦄ * g⦃a⦄` : `eval_mul'`
- `(c • f)⦃a⦄ = c • f⦃a⦄` : `eval_smul'`
- `C(c)⦃a⦄ = algebraMap K A c` : `eval_C'`
- `X⦃a⦄ = a` : `eval_X'`
- `X^i⦃a⦄ = a^i` : `eval_X_pow'`
- `f⦃g⦃a⦄⦄ = (f.comp g)⦃a⦄` : `eval_comp'`

Special cases:
- `f⦃x⦄ = f` : `eval_X_eq_self`
- `f⦃0⦄ = f₀` : `eval_zero_eq_coeff_zero`
- `f⦃1⦄ = sum of coefficients` : `eval_one_eq_sum_coeffs`

## References

* Definition 7.5.1 (def.fps.pol) - Definition of polynomial as FPS with finite support ✓
* Theorem 7.5.2 (thm.fps.pol.ring) - K[x] is a subring of K[[x]] ✓
* Definition 7.5.3 (def.alg.ring) - Definition of (noncommutative) ring
* Definition 7.5.5 (def.alg.Kalg) - Definition of K-algebra
* Definition 7.5.6 (def.pol.subs) - Evaluation/substitution into polynomials ✓
* Theorem 7.5.7 (thm.pol.eval.a+b) - Properties of polynomial evaluation ✓

-/

namespace FPS

open Polynomial PowerSeries

variable {K : Type*} [CommRing K]

/-! ## Definition of Polynomial as FPS with Finite Support

Definition 7.5.1 (def.fps.pol): An FPS `a ∈ K⟦X⟧` is a polynomial if all but finitely many
coefficients are zero.
-/

/-- A power series is a polynomial if it has finite support, i.e., only finitely many
nonzero coefficients. This corresponds to Definition 7.5.1 (def.fps.pol) in the source. -/
def IsPolynomial (f : PowerSeries K) : Prop :=
  {n : ℕ | PowerSeries.coeff n f ≠ 0}.Finite

/-- A power series is a polynomial iff its support (set of indices with nonzero coefficients)
is finite. -/
theorem isPolynomial_iff_finite_support (f : PowerSeries K) :
    IsPolynomial f ↔ {n : ℕ | PowerSeries.coeff n f ≠ 0}.Finite :=
  Iff.rfl

/-- The image of a polynomial under `toPowerSeries` is a polynomial (in the FPS sense). -/
theorem isPolynomial_of_polynomial (p : K[X]) : IsPolynomial (p : PowerSeries K) := by
  simp only [IsPolynomial]
  have h : {n : ℕ | PowerSeries.coeff n (p : PowerSeries K) ≠ 0} ⊆ ↑p.support := by
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    simp only [Finset.mem_coe, Polynomial.mem_support_iff]
    rw [Polynomial.coeff_coe] at hn
    exact hn
  exact Set.Finite.subset p.support.finite_toSet h

/-- For a polynomial power series, there exists a degree bound such that all coefficients
beyond this bound are zero. This is an equivalent characterization of polynomials. -/
theorem isPolynomial_iff_exists_degree_bound (f : PowerSeries K) :
    IsPolynomial f ↔ ∃ N : ℕ, ∀ n ≥ N, PowerSeries.coeff n f = 0 := by
  constructor
  · intro hf
    simp only [IsPolynomial] at hf
    obtain ⟨N, hN⟩ := hf.bddAbove
    use N + 1
    intro n hn
    by_contra h
    have hmem : n ∈ {m : ℕ | PowerSeries.coeff m f ≠ 0} := h
    have hle : n ≤ N := hN hmem
    omega
  · intro ⟨N, hN⟩
    simp only [IsPolynomial]
    apply Set.Finite.subset (Finset.finite_toSet (Finset.range N))
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    push Not at h
    exact hn (hN n h)

/-- A power series is a polynomial iff it equals the coercion of some polynomial.
This provides the key equivalence between `IsPolynomial` and Mathlib's `Polynomial` type. -/
theorem isPolynomial_iff_exists_polynomial (f : PowerSeries K) :
    IsPolynomial f ↔ ∃ p : K[X], f = p := by
  constructor
  · intro hf
    -- Use the degree bound characterization and truncation
    rw [isPolynomial_iff_exists_degree_bound] at hf
    obtain ⟨N, hN⟩ := hf
    use PowerSeries.trunc N f
    ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · push Not at hn
      exact hN n hn
  · intro ⟨p, hp⟩
    rw [hp]
    exact isPolynomial_of_polynomial p

/-- Convert a polynomial power series to its corresponding polynomial.
This requires a proof that the power series is a polynomial. -/
noncomputable def toPolynomial (f : PowerSeries K) (hf : IsPolynomial f) : K[X] :=
  (isPolynomial_iff_exists_degree_bound f).mp hf |>.choose |> fun N => PowerSeries.trunc N f

/-- The polynomial corresponding to a polynomial power series coerces back to the original.
This shows that `toPolynomial` is a left inverse of the coercion from polynomials. -/
theorem coe_toPolynomial (f : PowerSeries K) (hf : IsPolynomial f) :
    (toPolynomial f hf : PowerSeries K) = f := by
  simp only [toPolynomial]
  set N := (isPolynomial_iff_exists_degree_bound f).mp hf |>.choose
  have hN := (isPolynomial_iff_exists_degree_bound f).mp hf |>.choose_spec
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · push Not at hn
    exact (hN n hn).symm

/-- Converting a polynomial to a power series and back gives the original polynomial. -/
theorem toPolynomial_coe (p : K[X]) :
    toPolynomial (p : PowerSeries K) (isPolynomial_of_polynomial p) = p := by
  apply Polynomial.coe_injective K
  rw [coe_toPolynomial]

/-! ## Polynomials Form a Subring of Power Series

Theorem 7.5.2 (thm.fps.pol.ring): The set K[x] is a subring of K[[x]].
-/

/-- The zero power series is a polynomial. -/
@[simp]
theorem isPolynomial_zero : IsPolynomial (0 : PowerSeries K) := by
  simp only [IsPolynomial]
  have : {n : ℕ | PowerSeries.coeff n (0 : PowerSeries K) ≠ 0} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, map_zero, ne_eq, not_true_eq_false, Set.mem_empty_iff_false]
  rw [this]
  exact Set.finite_empty

/-- The constant power series 1 is a polynomial. -/
@[simp]
theorem isPolynomial_one : IsPolynomial (1 : PowerSeries K) := by
  have h : (1 : PowerSeries K) = ((1 : K[X]) : PowerSeries K) := by
    ext n
    simp only [Polynomial.coeff_coe, Polynomial.coeff_one]
    simp only [PowerSeries.coeff_one]
  rw [h]
  exact isPolynomial_of_polynomial (1 : K[X])

/-- The sum of two polynomial power series is a polynomial.
This is part of Theorem 7.5.2 (thm.fps.pol.ring). -/
theorem isPolynomial_add {f g : PowerSeries K} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (f + g) := by
  simp only [IsPolynomial] at *
  have h : {n : ℕ | PowerSeries.coeff n (f + g) ≠ 0} ⊆
      {n : ℕ | PowerSeries.coeff n f ≠ 0} ∪ {n : ℕ | PowerSeries.coeff n g ≠ 0} := by
    intro n hn
    simp only [Set.mem_ofPred_eq, map_add, ne_eq] at hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, ne_eq]
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2, add_zero] at hn
    exact hn rfl
  exact Set.Finite.subset (Set.Finite.union hf hg) h

/-- The negation of a polynomial power series is a polynomial.
This is part of Theorem 7.5.2 (thm.fps.pol.ring). -/
theorem isPolynomial_neg {f : PowerSeries K} (hf : IsPolynomial f) : IsPolynomial (-f) := by
  simp only [IsPolynomial] at *
  convert hf using 1
  ext n
  simp only [Set.mem_ofPred_eq, map_neg, neg_ne_zero]

/-- The difference of two polynomial power series is a polynomial.
This is part of Theorem 7.5.2 (thm.fps.pol.ring). -/
theorem isPolynomial_sub {f g : PowerSeries K} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (f - g) := by
  rw [sub_eq_add_neg]
  exact isPolynomial_add hf (isPolynomial_neg hg)

/-- The product of two polynomial power series is a polynomial.
This is the main content of Theorem 7.5.2 (thm.fps.pol.ring). -/
theorem isPolynomial_mul {f g : PowerSeries K} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (f * g) := by
  simp only [IsPolynomial] at *
  -- The support of f*g is contained in {i + j | i ∈ supp f, j ∈ supp g}
  let I := {n : ℕ | PowerSeries.coeff n f ≠ 0}
  let J := {n : ℕ | PowerSeries.coeff n g ≠ 0}
  let S := {n : ℕ | ∃ i ∈ I, ∃ j ∈ J, n = i + j}
  have hS : S.Finite := by
    have hsub : S ⊆ Finset.image₂ (· + ·) hf.toFinset hg.toFinset := by
      intro n ⟨i, hi, j, hj, hn⟩
      simp only [Finset.coe_image₂, Set.mem_image2]
      refine ⟨i, ?_, j, ?_, hn.symm⟩
      · exact hf.mem_toFinset.mpr hi
      · exact hg.mem_toFinset.mpr hj
    exact Set.Finite.subset (Finset.finite_toSet _) hsub
  have h : {n : ℕ | PowerSeries.coeff n (f * g) ≠ 0} ⊆ S := by
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    by_contra hns
    simp only [S, Set.mem_ofPred_eq, not_exists, not_and] at hns
    have hzero : ∀ i, i ≤ n → (PowerSeries.coeff i) f * (PowerSeries.coeff (n - i)) g = 0 := by
      intro i hi
      by_cases hif : (PowerSeries.coeff i) f = 0
      · exact by rw [hif, zero_mul]
      · have hig : (PowerSeries.coeff (n - i)) g = 0 := by
          by_contra hig'
          have : n = i + (n - i) := (Nat.add_sub_cancel' hi).symm
          exact hns i hif (n - i) hig' this
        exact by rw [hig, mul_zero]
    apply hn
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨i, j⟩ hij
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hi : i ≤ n := by omega
    have hj : j = n - i := by omega
    have := hzero i hi
    simp only at this ⊢
    rw [hj]
    exact this
  exact Set.Finite.subset hS h

/-- Scalar multiplication of a polynomial power series is a polynomial.
This is part of Theorem 7.5.2 (thm.fps.pol.ring). -/
theorem isPolynomial_smul {f : PowerSeries K} (c : K) (hf : IsPolynomial f) :
    IsPolynomial (c • f) := by
  simp only [IsPolynomial] at *
  have h : {n : ℕ | PowerSeries.coeff n (c • f) ≠ 0} ⊆
      {n : ℕ | PowerSeries.coeff n f ≠ 0} := by
    intro n hn
    simp only [Set.mem_ofPred_eq, map_smul, smul_eq_mul, ne_eq] at hn
    simp only [Set.mem_ofPred_eq, ne_eq]
    intro hf'
    rw [hf', mul_zero] at hn
    exact hn rfl
  exact Set.Finite.subset hf h

/-! ## K[x] as a Subalgebra of K[[x]]

Theorem 7.5.2 (thm.fps.pol.ring): The set K[x] is a subring of K[[x]] (closed under addition,
subtraction, and multiplication, and contains 0 and 1) and a K-submodule of K[[x]] (closed
under addition and scalar multiplication).

These two properties together mean that K[x] forms a K-subalgebra of K[[x]].
-/

/-- The set of polynomial power series forms a K-subalgebra of K[[x]].
This is Theorem 7.5.2 (thm.fps.pol.ring) in the source:
K[x] is a subring of K[[x]] (closed under +, -, *, contains 0 and 1)
and a K-submodule (closed under + and scalar multiplication). -/
def polynomialSubalgebra : Subalgebra K (PowerSeries K) where
  carrier := {f | IsPolynomial f}
  mul_mem' := isPolynomial_mul
  one_mem' := isPolynomial_one
  add_mem' := isPolynomial_add
  zero_mem' := isPolynomial_zero
  algebraMap_mem' := fun c => by
    simp only [Set.mem_ofPred_eq, IsPolynomial]
    have h : {n : ℕ | PowerSeries.coeff n (algebraMap K (PowerSeries K) c) ≠ 0} ⊆ {0} := by
      intro n hn
      simp only [Set.mem_ofPred_eq, ne_eq] at hn
      simp only [Set.mem_singleton_iff]
      by_contra hne
      simp only [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, PowerSeries.coeff_one,
        ite_eq_right hne, mul_zero, not_true_eq_false] at hn
    exact Set.Finite.subset (Set.finite_singleton 0) h

/-- The underlying subring of the polynomial subalgebra.
This is the "subring" part of Theorem 7.5.2 (thm.fps.pol.ring):
K[x] is closed under +, -, *, and contains 0 and 1. -/
noncomputable def polynomialSubring : Subring (PowerSeries K) := polynomialSubalgebra.toSubring

/-- The underlying K-submodule of the polynomial subalgebra.
This is the "K-submodule" part of Theorem 7.5.2 (thm.fps.pol.ring):
K[x] is closed under + and scalar multiplication by elements of K. -/
noncomputable def polynomialSubmodule : Submodule K (PowerSeries K) :=
  polynomialSubalgebra.toSubmodule

/-- Membership in the polynomial subalgebra is equivalent to being a polynomial.
This is the characterization of K[x] from Theorem 7.5.2 (thm.fps.pol.ring). -/
@[simp]
theorem mem_polynomialSubalgebra (f : PowerSeries K) :
    f ∈ polynomialSubalgebra ↔ IsPolynomial f := Iff.rfl

/-- Membership in the polynomial subring is equivalent to being a polynomial.
This is the "subring" characterization from Theorem 7.5.2 (thm.fps.pol.ring). -/
@[simp]
theorem mem_polynomialSubring (f : PowerSeries K) :
    f ∈ polynomialSubring ↔ IsPolynomial f := Iff.rfl

/-- Membership in the polynomial submodule is equivalent to being a polynomial.
This is the "K-submodule" characterization from Theorem 7.5.2 (thm.fps.pol.ring). -/
@[simp]
theorem mem_polynomialSubmodule (f : PowerSeries K) :
    f ∈ polynomialSubmodule ↔ IsPolynomial f := Iff.rfl

/-! ## Rings (Noncommutative Rings)

Definition 7.5.3 (def.alg.ring): A ring (also known as a noncommutative ring) is defined
in the same way as a commutative ring, except that the commutativity of multiplication
axiom is removed.

In Mathlib, this is captured by the `Ring` typeclass. Note that "noncommutative ring"
does not imply that the ring is not commutative; it merely means that commutativity
is not required. Thus, any commutative ring is a noncommutative ring.

Examples of noncommutative rings:
- Matrix rings `Matrix n n R` for any ring R and n > 1
- The quaternions `ℍ[R]` (Mathlib: `Quaternion`)
- Endomorphism rings `Module.End R M` for any R-module M
-/

section RingBasics

variable {R : Type*} [Ring R]

/-- **Associativity of addition** (Ring axiom):
    `a + (b + c) = (a + b) + c` for all `a, b, c ∈ R`. -/
theorem ring_add_assoc (a b c : R) : a + (b + c) = (a + b) + c := (add_assoc a b c).symm

/-- **Commutativity of addition** (Ring axiom):
    `a + b = b + a` for all `a, b ∈ R`.
    Note: Addition is always commutative, even in noncommutative rings. -/
theorem ring_add_comm (a b : R) : a + b = b + a := add_comm a b

/-- **Neutrality of zero** (Ring axiom):
    `a + 0 = a` for all `a ∈ R`. -/
theorem ring_add_zero (a : R) : a + 0 = a := add_zero a

/-- **Neutrality of zero** (Ring axiom):
    `0 + a = a` for all `a ∈ R`. -/
theorem ring_zero_add (a : R) : 0 + a = a := zero_add a

/-- **Existence of additive inverse** (Ring axiom):
    `a + (-a) = 0` for all `a ∈ R`. -/
theorem ring_add_neg (a : R) : a + (-a) = 0 := add_neg_cancel a

/-- **Associativity of multiplication** (Ring axiom):
    `a * (b * c) = (a * b) * c` for all `a, b, c ∈ R`. -/
theorem ring_mul_assoc (a b c : R) : a * (b * c) = (a * b) * c := (mul_assoc a b c).symm

/-- **Left distributivity** (Ring axiom):
    `a * (b + c) = a * b + a * c` for all `a, b, c ∈ R`. -/
theorem ring_left_distrib (a b c : R) : a * (b + c) = a * b + a * c := mul_add a b c

/-- **Right distributivity** (Ring axiom):
    `(a + b) * c = a * c + b * c` for all `a, b, c ∈ R`. -/
theorem ring_right_distrib (a b c : R) : (a + b) * c = a * c + b * c := add_mul a b c

/-- **Neutrality of one** (Ring axiom):
    `a * 1 = a` for all `a ∈ R`. -/
theorem ring_mul_one (a : R) : a * 1 = a := mul_one a

/-- **Neutrality of one** (Ring axiom):
    `1 * a = a` for all `a ∈ R`. -/
theorem ring_one_mul (a : R) : 1 * a = a := one_mul a

/-- **Annihilation** (Ring property):
    `a * 0 = 0` for all `a ∈ R`. -/
theorem ring_mul_zero (a : R) : a * 0 = 0 := mul_zero a

/-- **Annihilation** (Ring property):
    `0 * a = 0` for all `a ∈ R`. -/
theorem ring_zero_mul (a : R) : 0 * a = 0 := zero_mul a

end RingBasics

/-! ### Examples of Noncommutative Rings

The source lists several examples of noncommutative rings:
- Matrix rings `R^{n×n}` for any ring R (commutative if n ≤ 1, noncommutative if n > 1)
- The quaternions ℍ
- Endomorphism rings of abelian groups/modules
-/

section RingExamples

-- Matrix rings are rings (noncommutative for n > 1)
example (n : ℕ) (R : Type*) [Ring R] [DecidableEq (Fin n)] : Ring (Matrix (Fin n) (Fin n) R) :=
  inferInstance

-- The quaternions over ℝ are a ring (noncommutative)
noncomputable example : Ring (Quaternion ℝ) := inferInstance

-- Endomorphism rings are rings
example (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Ring (Module.End R M) := inferInstance

-- Every commutative ring is a ring (commutativity is not required, just not forbidden)
example {K : Type*} [CommRing K] : Ring K := inferInstance

end RingExamples

/-! ## K-Algebras

### Definition 7.5.5 (def.alg.Kalg): K-Algebras

The source defines a K-algebra as a set A equipped with four maps:
- `⊕ : A × A → A` (addition)
- `⊖ : A × A → A` (subtraction)
- `⊙ : A × A → A` (multiplication)
- `⇀ : K × A → A` (scalar multiplication)

and two elements `0⃗ ∈ A` (zero) and `1⃗ ∈ A` (one), satisfying three properties:

1. **A is a (noncommutative) ring**: The set A with ⊕, ⊖, ⊙, 0⃗, 1⃗ satisfies the ring axioms
   (same as commutative ring but without commutativity of multiplication).

2. **A is a K-module**: The set A with ⊕, ⊖, ⇀, 0⃗ satisfies the module axioms.

3. **Compatibility property** (equation 7.5.2):
   `λ ⇀ (a ⊙ b) = (λ ⇀ a) ⊙ b = a ⊙ (λ ⇀ b)` for all `λ ∈ K` and `a, b ∈ A`.

In Mathlib, this is captured by the `Algebra` typeclass, which requires:
- `[Semiring A]` (or `[Ring A]` for rings with subtraction)
- `[Algebra K A]` which provides scalar multiplication and the compatibility property

The key property `λ(ab) = (λa)b = a(λb)` is expressed via:
- `Algebra.smul_mul_assoc`: `r • x * y = r • (x * y)`
- `Algebra.mul_smul_comm`: `x * r • y = r • (x * y)`
-/

section KAlgebra

variable {A : Type*} [Ring A] [Algebra K A]

/-! ### Property 1: A is a Ring

A K-algebra A is automatically a ring. The ring axioms are satisfied.
Note: The source allows noncommutative rings; in Mathlib, `Ring A` captures this.
For commutative algebras, we use `CommRing A`.
-/

/-- A K-algebra is a ring: addition is commutative.
    Label: def.alg.Kalg (Property 1) -/
theorem kalg_add_comm (a b : A) : a + b = b + a := add_comm a b

/-- A K-algebra is a ring: addition is associative.
    Label: def.alg.Kalg (Property 1) -/
theorem kalg_add_assoc (a b c : A) : a + (b + c) = (a + b) + c := (add_assoc a b c).symm

/-- A K-algebra is a ring: zero is the additive identity.
    Label: def.alg.Kalg (Property 1) -/
theorem kalg_add_zero (a : A) : a + 0 = a := add_zero a

/-- A K-algebra is a ring: multiplication is associative.
    Label: def.alg.Kalg (Property 1) -/
theorem kalg_mul_assoc (a b c : A) : a * (b * c) = (a * b) * c := (mul_assoc a b c).symm

/-- A K-algebra is a ring: left distributivity.
    Label: def.alg.Kalg (Property 1) -/
theorem kalg_left_distrib (a b c : A) : a * (b + c) = a * b + a * c := mul_add a b c

/-- A K-algebra is a ring: right distributivity.
    Label: def.alg.Kalg (Property 1) -/
theorem kalg_right_distrib (a b c : A) : (a + b) * c = a * c + b * c := add_mul a b c

/-- A K-algebra is a ring: one is the multiplicative identity.
    Label: def.alg.Kalg (Property 1) -/
theorem kalg_mul_one (a : A) : a * 1 = a := mul_one a

/-- A K-algebra is a ring: one is the multiplicative identity (left).
    Label: def.alg.Kalg (Property 1) -/
theorem kalg_one_mul (a : A) : 1 * a = a := one_mul a

/-! ### Property 2: A is a K-Module

A K-algebra A is automatically a K-module. The module axioms are satisfied.
-/

/-- A K-algebra is a K-module: scalar multiplication is associative.
    Label: def.alg.Kalg (Property 2) -/
theorem kalg_smul_assoc (u v : K) (a : A) : u • (v • a) = (u * v) • a := by rw [mul_smul]

/-- A K-algebra is a K-module: scalar multiplication distributes over addition (left).
    Label: def.alg.Kalg (Property 2) -/
theorem kalg_smul_add (u : K) (a b : A) : u • (a + b) = u • a + u • b := smul_add u a b

/-- A K-algebra is a K-module: scalar multiplication distributes over addition (right).
    Label: def.alg.Kalg (Property 2) -/
theorem kalg_add_smul (u v : K) (a : A) : (u + v) • a = u • a + v • a := add_smul u v a

/-- A K-algebra is a K-module: 1 acts as identity.
    Label: def.alg.Kalg (Property 2) -/
theorem kalg_one_smul (a : A) : (1 : K) • a = a := one_smul K a

/-- A K-algebra is a K-module: 0 annihilates.
    Label: def.alg.Kalg (Property 2) -/
theorem kalg_zero_smul (a : A) : (0 : K) • a = 0 := zero_smul K a

/-- A K-algebra is a K-module: scalar multiplication by zero element gives zero.
    Label: def.alg.Kalg (Property 2) -/
theorem kalg_smul_zero (u : K) : u • (0 : A) = 0 := smul_zero u

/-! ### Property 3: Compatibility (Equation 7.5.2)

The key compatibility property: `λ(ab) = (λa)b = a(λb)` for all `λ ∈ K` and `a, b ∈ A`.

This says that scaling a product in A by a scalar λ ∈ K is equivalent to scaling
either of its two factors by λ.
-/

/-- The compatibility property for K-algebras: `λ(ab) = (λa)b`.
    This is equation (7.5.2) in the source.
    Label: def.alg.Kalg (Property 3) -/
theorem kalg_smul_mul_assoc (c : K) (a b : A) : c • (a * b) = (c • a) * b :=
  (Algebra.smul_mul_assoc c a b).symm

/-- The compatibility property for K-algebras: `λ(ab) = a(λb)`.
    This is equation (7.5.2) in the source.
    Label: def.alg.Kalg (Property 3) -/
theorem kalg_mul_smul_comm (c : K) (a b : A) : c • (a * b) = a * (c • b) :=
  (Algebra.mul_smul_comm c a b).symm

/-- Combined compatibility: `(λa)b = a(λb)`.
    Follows from the two parts of equation (7.5.2).
    Label: def.alg.Kalg (Property 3) -/
theorem kalg_smul_mul_eq_mul_smul (c : K) (a b : A) : (c • a) * b = a * (c • b) := by
  rw [← kalg_smul_mul_assoc, kalg_mul_smul_comm]

end KAlgebra

/-! ### Examples of K-Algebras

The source lists several examples of K-algebras:
- The ring K itself
- The ring K⟦X⟧ of formal power series
- The polynomial ring K[X] (as a subring of K⟦X⟧)
- The matrix ring K^{n×n} for each n ∈ ℕ
- Any quotient ring K/I where I is an ideal
- Any commutative ring containing K as a subring
-/

section KAlgebraExamples

/-- K is a K-algebra over itself.
    Label: def.alg.Kalg (Example 1) -/
example : Algebra K K := inferInstance

/-- The ring of formal power series K⟦X⟧ is a K-algebra.
    Label: def.alg.Kalg (Example 2) -/
noncomputable example : Algebra K (PowerSeries K) := inferInstance

/-- The polynomial ring K[X] is a K-algebra.
    Label: def.alg.Kalg (Example 3) -/
noncomputable example : Algebra K K[X] := inferInstance

/-- For any n, the matrix ring K^{n×n} is a K-algebra.
    Label: def.alg.Kalg (Example 4) -/
example (n : ℕ) : Algebra K (Matrix (Fin n) (Fin n) K) := inferInstance

/-- ℤ/m is a ℤ-algebra for any m.
    Label: def.alg.Kalg (Example 5) -/
example (m : ℕ) [NeZero m] : Algebra ℤ (ZMod m) := inferInstance

/-- ℚ is a ℤ-algebra.
    Label: def.alg.Kalg (Example 6) -/
example : Algebra ℤ ℚ := inferInstance

/-- Any ring is automatically a ℤ-algebra.
    This is because any ring has a unique ring homomorphism from ℤ.
    Label: def.alg.Kalg (Note) -/
example {R : Type*} [Ring R] : Algebra ℤ R := inferInstance

end KAlgebraExamples

/-! ### The algebraMap

In Mathlib, a K-algebra A comes with a ring homomorphism `algebraMap K A : K →+* A`
that embeds K into the center of A. This allows us to view elements of K as elements of A.
-/

section AlgebraMap

variable {A : Type*} [CommRing A] [Algebra K A]

/-- The algebraMap is a ring homomorphism from K to A.
    Label: def.alg.Kalg -/
example : K →+* A := algebraMap K A

/-- algebraMap preserves zero. -/
theorem algebraMap_zero : algebraMap K A 0 = 0 := map_zero (algebraMap K A)

/-- algebraMap preserves one. -/
theorem algebraMap_one : algebraMap K A 1 = 1 := map_one (algebraMap K A)

/-- algebraMap preserves addition. -/
theorem algebraMap_add (a b : K) : algebraMap K A (a + b) = algebraMap K A a + algebraMap K A b :=
  map_add (algebraMap K A) a b

/-- algebraMap preserves multiplication. -/
theorem algebraMap_mul (a b : K) : algebraMap K A (a * b) = algebraMap K A a * algebraMap K A b :=
  map_mul (algebraMap K A) a b

/-- Elements in the image of algebraMap commute with all elements of A.
    This is a key property: algebraMap K A lands in the center of A. -/
theorem algebraMap_commutes (r : K) (x : A) : algebraMap K A r * x = x * algebraMap K A r :=
  Algebra.commutes r x

/-- Scalar multiplication is related to algebraMap:
    `r • x = algebraMap K A r * x`. -/
theorem smul_eq_algebraMap_mul (r : K) (x : A) : r • x = algebraMap K A r * x :=
  Algebra.smul_def r x

end AlgebraMap

/-! ## Evaluation of Polynomials

Definition 7.5.6 (def.pol.subs): For a polynomial f ∈ K[x] and an element a of a K-algebra A,
we define f[a] := Σ_{n ∈ ℕ} f_n * a^n.

In Mathlib, this is `Polynomial.aeval a f` for evaluation in a K-algebra A.

### Implementation Notes

The book uses notation `f[a]` for polynomial evaluation. In Mathlib:
- `Polynomial.aeval a f` evaluates polynomial `f` at element `a` of a K-algebra
- `Polynomial.eval₂ φ a f` is more general, using a ring homomorphism `φ`
- `Polynomial.eval a f` evaluates in the base ring K itself

We provide `polyEval` as a wrapper matching the book's presentation.
-/

section Evaluation

variable {A : Type*} [CommRing A] [Algebra K A]

/-- Evaluation of a polynomial at an element of a K-algebra.
This is Definition 7.5.6 (def.pol.subs).

Given a polynomial f ∈ K[X] and an element a of a K-algebra A,
we define f[a] := Σ_{n ∈ ℕ} f_n · a^n.

The sum is essentially finite since f is a polynomial (only finitely many
coefficients are nonzero).

In Mathlib, this is implemented as `Polynomial.aeval a f`. -/
noncomputable abbrev polyEval (f : K[X]) (a : A) : A := aeval a f

/-- Notation for polynomial evaluation: `f⦃a⦄` means the value of `f` at `a`.
This corresponds to the book's notation `f[a]`. -/
scoped notation:max f:max "⦃" a "⦄" => polyEval f a

/-- Evaluation of a polynomial at an element of a K-algebra equals the sum Σ f_n · a^n.
This is the explicit formula from Definition 7.5.6 (def.pol.subs). -/
theorem eval_def (f : K[X]) (a : A) :
    f⦃a⦄ = f.sum fun n c => algebraMap K A c * a ^ n := by
  rw [polyEval, aeval_def, eval₂_eq_sum]

/-- The evaluation f[a] can be written as a finite sum over the support of f.
This makes explicit that the sum in Definition 7.5.6 is essentially finite. -/
theorem eval_eq_finsum (f : K[X]) (a : A) :
    f⦃a⦄ = ∑ n ∈ f.support, algebraMap K A (f.coeff n) * a ^ n := by
  rw [polyEval, aeval_def, eval₂_eq_sum, Polynomial.sum]

/-- Alternative formulation: f[a] = Σ_{n=0}^{deg f} f_n · a^n.
This shows that the sum can be taken up to the degree. -/
theorem eval_eq_sum_range (f : K[X]) (a : A) :
    f⦃a⦄ = ∑ n ∈ Finset.range (f.natDegree + 1), algebraMap K A (f.coeff n) * a ^ n := by
  rw [polyEval, aeval_def, eval₂_eq_sum_range]

/-! ### Properties of Polynomial Evaluation

Theorem 7.5.7 (thm.pol.eval.a+b): Basic properties of evaluation.
-/

/-- (f + g)[a] = f[a] + g[a].
This is Theorem 7.5.7(a) in the source. -/
theorem eval_add' (f g : K[X]) (a : A) :
    (f + g)⦃a⦄ = f⦃a⦄ + g⦃a⦄ :=
  map_add (aeval a) f g

/-- (f * g)[a] = f[a] * g[a].
This is Theorem 7.5.7(a) in the source. -/
theorem eval_mul' (f g : K[X]) (a : A) :
    (f * g)⦃a⦄ = f⦃a⦄ * g⦃a⦄ :=
  map_mul (aeval a) f g

/-- (c · f)[a] = c · f[a].
This is Theorem 7.5.7(b) in the source. -/
theorem eval_smul' (f : K[X]) (c : K) (a : A) :
    (c • f)⦃a⦄ = c • f⦃a⦄ :=
  map_smul (aeval a) c f

/-- C(c)[a] = c · 1_A.
This is Theorem 7.5.7(c) in the source. -/
theorem eval_C' (c : K) (a : A) :
    (Polynomial.C c)⦃a⦄ = algebraMap K A c :=
  aeval_C a c

/-- X[a] = a.
This is Theorem 7.5.7(d) in the source. -/
theorem eval_X' (a : A) :
    (Polynomial.X : K[X])⦃a⦄ = a :=
  aeval_X a

/-- X^i[a] = a^i.
This is Theorem 7.5.7(e) in the source. -/
theorem eval_X_pow' (a : A) (i : ℕ) :
    ((Polynomial.X : K[X]) ^ i)⦃a⦄ = a ^ i := by
  simp only [polyEval, map_pow, aeval_X]

/-- f[g[a]] = (f ∘ g)[a], where f ∘ g denotes composition of polynomials.
This is Theorem 7.5.7(f) in the source. -/
theorem eval_comp' (f g : K[X]) (a : A) :
    f⦃g⦃a⦄⦄ = (f.comp g)⦃a⦄ := by
  rw [polyEval, polyEval, polyEval, aeval_comp]

end Evaluation

/-! ## Examples and Special Cases -/

/-- The polynomial X is a polynomial (in the FPS sense). -/
@[simp]
theorem isPolynomial_X : IsPolynomial (PowerSeries.X : PowerSeries K) := by
  simp only [IsPolynomial]
  have h : {n : ℕ | PowerSeries.coeff n (PowerSeries.X : PowerSeries K) ≠ 0} ⊆ {1} := by
    intro n hn
    simp only [Set.mem_ofPred_eq, PowerSeries.coeff_X, ne_eq] at hn
    simp only [Set.mem_singleton_iff]
    by_contra hne
    rw [ite_eq_right hne] at hn
    exact hn rfl
  exact Set.Finite.subset (Set.finite_singleton 1) h

/-- Any constant is a polynomial (in the FPS sense). -/
@[simp]
theorem isPolynomial_C (c : K) : IsPolynomial (PowerSeries.C c) := by
  simp only [IsPolynomial]
  have h : {n : ℕ | PowerSeries.coeff n (PowerSeries.C c) ≠ 0} ⊆ {0} := by
    intro n hn
    simp only [Set.mem_ofPred_eq, ne_eq] at hn
    simp only [Set.mem_singleton_iff]
    by_contra hne
    rw [PowerSeries.coeff_C, ite_eq_right hne] at hn
    exact hn rfl
  exact Set.Finite.subset (Set.finite_singleton 0) h

/-! ## Special Evaluation Results -/

section SpecialEval

variable {A : Type*} [CommRing A] [Algebra K A]

/-- f[x] = f, i.e., evaluating at the indeterminate gives back the polynomial.
This is noted after Definition 7.5.6 in the source. -/
theorem eval_X_eq_self (f : K[X]) :
    f⦃(Polynomial.X : K[X])⦄ = f := by
  have h := Polynomial.aeval_X_left (R := K)
  simp only [AlgHom.ext_iff, AlgHom.id_apply] at h
  exact h f

/-- f[0] = f₀, i.e., evaluating at 0 gives the constant term.
This is noted after Definition 7.5.6 in the source. -/
theorem eval_zero_eq_coeff_zero (f : K[X]) :
    f⦃(0 : A)⦄ = algebraMap K A (f.coeff 0) := by
  simp only [polyEval, aeval_def, eval₂_at_zero]

/-- f[1] = sum of all coefficients of f.
This is noted after Definition 7.5.6 in the source. -/
theorem eval_one_eq_sum_coeffs (f : K[X]) :
    f⦃(1 : A)⦄ = algebraMap K A (f.sum fun _ c => c) := by
  rw [polyEval, aeval_def, eval₂_at_one, Polynomial.eval_eq_sum]
  simp only [one_pow, mul_one]

end SpecialEval

end FPS
