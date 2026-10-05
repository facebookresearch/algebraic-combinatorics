/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib

/-!
# Partition basics

This file formalizes the basic theory of integer partitions from Section
"Partition basics" of the Algebraic Combinatorics textbook.

## Main definitions

* `IversonBracket.iverson` - the Iverson bracket `[P]` converting propositions to 0 or 1
* `FloorCeiling.floor_def` - the floor function `⌊a⌋` (largest integer ≤ a)
* `FloorCeiling.ceil_def` - the ceiling function `⌈a⌉` (smallest integer ≥ a)
* `Nat.Partition.partitionCount` - the partition function `p(n)`, counting partitions of `n`
* `Nat.Partition.partsCount` - the function `p_k(n)`, counting partitions of `n` into `k` parts
* `Nat.Partition.largestPart` - the largest part of a partition (0 for the empty partition)
* `Nat.Partition.transpose` - the conjugate/transpose of a partition
* `Nat.Partition.partsLeqCount` - count of partitions with parts ≤ m
* `Nat.Partition.partsInCount` - count of partitions with parts in a set I

## Main results

### Integer partitions (Definition \ref{def.pars.parts})
* `Nat.Partition.size_eq` - The size of a partition equals the sum of parts (Definition \ref{def.pars.parts} (c))
* `Nat.Partition.parts_pos'` - All parts are positive (Definition \ref{def.pars.parts} (a))
* `Nat.Partition.parts_le` - Each part is bounded by the size
* `Nat.Partition.parts_eq_zero_of_partition_zero` - The partition of 0 has no parts
* `Nat.Partition.parts_card_zero` - The partition of 0 has length 0
* `Nat.Partition.indiscrete_parts_card` - The indiscrete partition (n) has one part
* `Nat.Partition.ofList'` - Construct a partition from a list of positive integers
* `Nat.Partition.eq_iff_parts_eq` - Partitions are determined by their parts

### Iverson bracket (Definition \ref{def.pars.iverson})
* `IversonBracket.iverson` - `[P] = 1` if `P` is true, `[P] = 0` if `P` is false
* `IversonBracket.iverson_true` - `[P] = 1` when `P` is true
* `IversonBracket.iverson_false` - `[P] = 0` when `P` is false
* `IversonBracket.kronecker_eq_iverson` - Kronecker delta `δ_{i,j} = [i = j]`
* `IversonBracket.sum_iverson_eq_card` - `∑ [P(x)] = |{x : P(x)}|`
* `IversonBracket.iverson_and` - `[P ∧ Q] = [P] * [Q]`
* `IversonBracket.iverson_not` - `[¬P] = 1 - [P]`
* `IversonBracket.iverson_or` - `[P ∨ Q] = [P] + [Q] - [P] * [Q]`
* `IversonBracket.iverson_imp` - `[P → Q] = 1 - [P] * (1 - [Q])`

### Floor and ceiling (Definition \ref{def.pars.floor-ceil})
* `FloorCeiling.floor_def` - `n ≤ ⌊a⌋ ↔ n ≤ a` (characterization of floor)
* `FloorCeiling.ceil_def` - `⌈a⌉ ≤ n ↔ a ≤ n` (characterization of ceiling)
* `FloorCeiling.floor_of_int` - `⌊n⌋ = n` for integers
* `FloorCeiling.ceil_of_int` - `⌈n⌉ = n` for integers
* `FloorCeiling.nat_div_eq_floor` - `n / m = ⌊n/m⌋` for natural numbers

### Basic properties (Proposition \ref{prop.pars.basics})
* `Nat.Partition.partsCount_of_gt` - `p_k(n) = 0` when `k > n`
* `Nat.Partition.partsCount_of_gt'` - `@[simp]` lemma for `p_k(n) = 0` when `n < k`
* `Nat.Partition.partsCount_eq_zero_iff` - `p_k(n) = 0` iff `k > n` or `k = 0 ∧ n > 0`
* `Nat.Partition.partsCount_zero` - `p_0(n) = [n = 0]`
* `Nat.Partition.partsCount_one` - `p_1(n) = [n > 0]`
* `Nat.Partition.partsCount_recurrence` - `p_k(n) = p_k(n-k) + p_{k-1}(n-1)` for `k > 0` and `n > 0`
* `Nat.Partition.partsCount_two` - `p_2(n) = ⌊n/2⌋` for `n ∈ ℕ`
* `Nat.Partition.partitionCount_sum` - `p(n) = p_0(n) + p_1(n) + ... + p_n(n)` for `n ∈ ℕ`

### Generating functions (Theorems \ref{thm.pars.main-gf}, \ref{thm.pars.main-gf-parts-n}, \ref{thm.pars.main-gf-parts-I}, \ref{thm.pars.main-gf-0n})
* `Nat.Partition.partitionCount_genFun` - `∑ p(n) x^n = ∏_{k≥1} 1/(1-x^k)`
* `Nat.Partition.partitionCount_genFun_partsLeq` - `∑ p_{parts≤m}(n) x^n = ∏_{k=1}^m 1/(1-x^k)`
* `Nat.Partition.partitionCount_genFun_partsIn` - `∑ p_I(n) x^n = ∏_{k∈I} 1/(1-x^k)`
* `Nat.Partition.partsCountSum_genFun` - `∑ (p_0(n) + ... + p_m(n)) x^n = ∏_{k=1}^m 1/(1-x^k)`

### Odd-distinct theorem (Theorem \ref{thm.pars.odd-dist-equal})
* `Nat.Partition.card_odds_eq_card_distincts` - Euler's odd-distinct identity (from Mathlib)

### Conjugation (Proposition \ref{prop.pars.pkn=dual})
* `Nat.Partition.partsCount_eq_largestPartCount` - `p_k(n) = #{ partitions of n with largest part k }`

### Counting by parts and largest (Proposition \ref{prop.pars.qbinom.intro-count-binom})
* `Nat.Partition.partsAndLargestCountTotal_eq` - `#{ partitions with k parts and largest ℓ } = C(k+ℓ-2, k-1)`

### Partition numbers and divisor sums (Theorem \ref{thm.pars.sigma1})
* `Nat.Partition.partitionCount_divisorSum` - `n·p(n) = ∑_{k=1}^n σ(k)·p(n-k)`

## Implementation notes

We use Mathlib's `Nat.Partition` type which represents a partition as a multiset of positive
integers. This is equivalent to the "weakly decreasing tuple" representation in the source text.

The functions `partsCount` and `partitionCount` are defined as cardinalities of finite sets,
which automatically ensures they are nonnegative. For negative `n`, there are no partitions,
so these functions return 0 naturally.

The generating function theorems use Mathlib's `HasProd` to express convergent infinite products
in the power series topology. The identity `∏_{k≥1} 1/(1-x^k)` is expressed as
`∏_{k≥1} ∑_{j≥0} x^{kj}` since the geometric series `1/(1-x^k) = ∑_{j≥0} x^{kj}`.

## References

* The source text: Algebraic Combinatorics, Section on Partition Basics
* Mathlib: `Mathlib.Combinatorics.Enumerative.Partition.Basic`
* Mathlib: `Mathlib.Combinatorics.Enumerative.Partition.GenFun`
* Mathlib: `Mathlib.Combinatorics.Enumerative.Partition.Glaisher`
-/

open Nat Finset BigOperators PowerSeries
open scoped PowerSeries.WithPiTopology

/-! ### Iverson bracket notation (Definition \ref{def.pars.iverson})

The **Iverson bracket notation** represents the truth value of a proposition `P`:
- 1 if `P` is true
- 0 if `P` is false

In Lean, this is represented as `if P then 1 else 0` or equivalently `(decide P).toNat`.

The Kronecker delta `δ_{i,j}` is a special case: `δ_{i,j} = [i = j]`.
-/

namespace IversonBracket

/-- The Iverson bracket converts a proposition to its truth value (0 or 1).
    (Definition \ref{def.pars.iverson})

    This is the standard way to embed boolean values into a semiring:
    - 1 if `P` is true
    - 0 if `P` is false

    In Mathlib, this is `if P then 1 else 0` or `(decide P).toNat` for naturals. -/
abbrev iverson (P : Prop) [Decidable P] {α : Type*} [Zero α] [One α] : α :=
  if P then 1 else 0

/-- Notation `⦃P⦄` for the Iverson bracket. -/
scoped notation "⦃" P "⦄" => iverson P

/-- The Iverson bracket of a true proposition is 1. -/
@[simp]
theorem iverson_true {α : Type*} [Zero α] [One α] {P : Prop} [Decidable P] (h : P) :
    (⦃P⦄ : α) = 1 := ite_eq_left h

/-- The Iverson bracket of a false proposition is 0. -/
@[simp]
theorem iverson_false {α : Type*} [Zero α] [One α] {P : Prop} [Decidable P] (h : ¬P) :
    (⦃P⦄ : α) = 0 := ite_eq_right h

/-- The Iverson bracket equals 1 iff the proposition is true. -/
theorem iverson_eq_one_iff {α : Type*} [Zero α] [One α] [NeZero (1 : α)]
    {P : Prop} [Decidable P] : (⦃P⦄ : α) = 1 ↔ P := by
  constructor
  · intro h
    by_contra hn
    simp [iverson, hn] at h
  · intro h
    simp [h]

/-- The Iverson bracket equals 0 iff the proposition is false (assuming 1 ≠ 0). -/
theorem iverson_eq_zero_iff {α : Type*} [Zero α] [One α] [NeZero (1 : α)]
    {P : Prop} [Decidable P] : (⦃P⦄ : α) = 0 ↔ ¬P := by
  constructor
  · intro h
    by_contra hn
    simp [iverson, hn] at h
  · intro h
    simp [h]

/-- Example: [2 + 2 = 4] = 1. -/
example : (⦃2 + 2 = 4⦄ : ℕ) = 1 := by simp

/-- Example: [2 + 2 = 5] = 0. -/
example : (⦃2 + 2 = 5⦄ : ℕ) = 0 := by simp

/-- The Kronecker delta is a special case of the Iverson bracket: δ_{i,j} = [i = j].

    In Mathlib, this is represented by `Pi.single i 1 j` for dependent functions,
    or `if i = j then 1 else 0` directly. -/
theorem kronecker_eq_iverson {α : Type*} [DecidableEq α] {R : Type*} [Zero R] [One R]
    (i j : α) : (if i = j then (1 : R) else 0) = ⦃i = j⦄ := rfl

/-- The Iverson bracket for natural numbers equals `Bool.toNat` of the decision. -/
theorem iverson_nat_eq_toNat (P : Prop) [Decidable P] :
    (⦃P⦄ : ℕ) = (decide P).toNat := by
  cases Decidable.em P with
  | inl h => simp [iverson, h]
  | inr h => simp [iverson, h]

/-- Sum of Iverson brackets equals cardinality of the filtered set. -/
theorem sum_iverson_eq_card {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ∑ x ∈ s, (⦃p x⦄ : ℕ) = (s.filter p).card := by
  simp only [iverson, Finset.card_filter]

/-- The Iverson bracket is multiplicative for conjunctions:
    [P ∧ Q] = [P] * [Q] when the propositions are decidable. -/
theorem iverson_and {α : Type*} [MulZeroOneClass α] {P Q : Prop} [Decidable P] [Decidable Q] :
    (⦃P ∧ Q⦄ : α) = ⦃P⦄ * ⦃Q⦄ := by
  simp only [iverson]
  split_ifs <;> simp_all

/-- The Iverson bracket satisfies [P]² = [P] (idempotent under multiplication). -/
theorem iverson_sq {α : Type*} [MonoidWithZero α] {P : Prop} [Decidable P] :
    (⦃P⦄ : α) ^ 2 = ⦃P⦄ := by
  simp only [iverson, sq]
  split_ifs <;> simp

/-- The Iverson bracket of a negation: [¬P] = 1 - [P].
    This requires 1 ≠ 0 in the ring. -/
theorem iverson_not {α : Type*} [Ring α] [NeZero (1 : α)] {P : Prop} [Decidable P] :
    (⦃¬P⦄ : α) = 1 - ⦃P⦄ := by
  simp only [iverson]
  split_ifs <;> simp_all

/-- The Iverson bracket of a disjunction: [P ∨ Q] = [P] + [Q] - [P] * [Q].
    This is the inclusion-exclusion principle for Iverson brackets. -/
theorem iverson_or {α : Type*} [Ring α] {P Q : Prop} [Decidable P] [Decidable Q] :
    (⦃P ∨ Q⦄ : α) = ⦃P⦄ + ⦃Q⦄ - ⦃P⦄ * ⦃Q⦄ := by
  simp only [iverson]
  split_ifs <;> simp_all

/-- The Iverson bracket of an implication: [P → Q] = 1 - [P] * (1 - [Q]) = 1 - [P] * [¬Q].
    Equivalently, [P → Q] = 1 - [P] + [P] * [Q]. -/
theorem iverson_imp {α : Type*} [Ring α] {P Q : Prop} [Decidable P] [Decidable Q] :
    (⦃P → Q⦄ : α) = 1 - ⦃P⦄ * (1 - ⦃Q⦄) := by
  simp only [iverson]
  split_ifs <;> simp_all

end IversonBracket

/-! ### Floor and ceiling functions (Definition \ref{def.pars.floor-ceil})

The **floor** of a real number `a`, denoted `⌊a⌋`, is the largest integer that is ≤ a.
The **ceiling** of a real number `a`, denoted `⌈a⌉`, is the smallest integer that is ≥ a.

In Mathlib, these are provided by the `FloorRing` and `FloorSemiring` typeclasses:
- `Int.floor` gives the floor as an integer
- `Int.ceil` gives the ceiling as an integer
- `Nat.floor` gives the floor as a natural number (for nonnegative inputs)
- `Nat.ceil` gives the ceiling as a natural number (for nonnegative inputs)

The notation `⌊a⌋` and `⌈a⌉` is available via `import Mathlib`.
-/

namespace FloorCeiling

/-!
## Definition (def.pars.floor-ceil)

Let `a` be a real number.
- `⌊a⌋` (the **floor** of `a`) is the largest integer that is ≤ a.
- `⌈a⌉` (the **ceiling** of `a`) is the smallest integer that is ≥ a.

These are formalized in Mathlib as `Int.floor` and `Int.ceil`.
-/

/-- The floor of a real number is the largest integer ≤ a.
    (Definition \ref{def.pars.floor-ceil})

    This is the characterization: n ≤ ⌊a⌋ iff n ≤ a. -/
theorem floor_def (a : ℝ) (n : ℤ) : n ≤ ⌊a⌋ ↔ n ≤ a := Int.le_floor

/-- The ceiling of a real number is the smallest integer ≥ a.
    (Definition \ref{def.pars.floor-ceil})

    This is the characterization: ⌈a⌉ ≤ n iff a ≤ n. -/
theorem ceil_def (a : ℝ) (n : ℤ) : ⌈a⌉ ≤ n ↔ a ≤ n := Int.ceil_le

/-- The floor is at most the original number. -/
theorem floor_le (a : ℝ) : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a

/-- The original number is at most the ceiling. -/
theorem le_ceil (a : ℝ) : a ≤ ⌈a⌉ := Int.le_ceil a

/-- The floor is at most the ceiling. -/
theorem floor_le_ceil (a : ℝ) : ⌊a⌋ ≤ ⌈a⌉ := Int.floor_le_ceil a

/-- The floor of an integer is itself.
    (Example from the textbook: ⌊n⌋ = n for n ∈ ℤ) -/
theorem floor_of_int (n : ℤ) : ⌊(n : ℝ)⌋ = n := Int.floor_intCast n

/-- The ceiling of an integer is itself.
    (Example from the textbook: ⌈n⌉ = n for n ∈ ℤ) -/
theorem ceil_of_int (n : ℤ) : ⌈(n : ℝ)⌉ = n := Int.ceil_intCast n

/-- For integers, floor equals ceiling.
    (Example from the textbook: ⌊n⌋ = ⌈n⌉ = n for n ∈ ℤ) -/
theorem floor_eq_ceil_of_int (n : ℤ) : ⌊(n : ℝ)⌋ = ⌈(n : ℝ)⌉ := by
  rw [floor_of_int, ceil_of_int]

/-! ### Examples from the textbook

The textbook gives π ≈ 3.14 as an example. We use 3.14 directly as a rational. -/

/-- Example: ⌊3.14⌋ = 3 (approximating ⌊π⌋ = 3). -/
example : ⌊(3.14 : ℚ)⌋ = 3 := by native_decide

/-- Example: ⌈3.14⌉ = 4 (approximating ⌈π⌉ = 4). -/
example : ⌈(3.14 : ℚ)⌉ = 4 := by native_decide

/-- Example: ⌊-3.14⌋ = -4 (approximating ⌊-π⌋ = -4). -/
example : ⌊(-3.14 : ℚ)⌋ = -4 := by native_decide

/-- Example: ⌈-3.14⌉ = -3 (approximating ⌈-π⌉ = -3). -/
example : ⌈(-3.14 : ℚ)⌉ = -3 := by native_decide

/-! ### Connection to natural number division -/

/-- Natural number division equals the floor of rational division.
    This connects `n / m` (natural number division) to `⌊n/m⌋` (floor of rational division). -/
theorem nat_div_eq_floor (n m : ℕ) (_hm : m ≠ 0) : n / m = Nat.floor ((n : ℚ) / m) := by
  haveI : NeZero m := ⟨_hm⟩
  have h : Nat.floor ((n : ℚ) / ((m : ℕ) : ℚ)) = n / m := Nat.floor_div_eq_div (K := ℚ) n m
  exact h.symm

/-! ### Additional properties -/

/-- Floor of a sum: ⌊a + n⌋ = ⌊a⌋ + n for integer n. -/
theorem floor_add_int (a : ℝ) (n : ℤ) : ⌊a + n⌋ = ⌊a⌋ + n := Int.floor_add_intCast a n

/-- Ceiling of a sum: ⌈a + n⌉ = ⌈a⌉ + n for integer n. -/
theorem ceil_add_int (a : ℝ) (n : ℤ) : ⌈a + n⌉ = ⌈a⌉ + n := Int.ceil_add_intCast a n

/-- Floor is monotone: a ≤ b implies ⌊a⌋ ≤ ⌊b⌋. -/
theorem floor_mono {a b : ℝ} (h : a ≤ b) : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_mono h

/-- Ceiling is monotone: a ≤ b implies ⌈a⌉ ≤ ⌈b⌉. -/
theorem ceil_mono {a b : ℝ} (h : a ≤ b) : ⌈a⌉ ≤ ⌈b⌉ := Int.ceil_mono h

/-- The fractional part of a real number: a - ⌊a⌋ ∈ [0, 1). -/
theorem fract_nonneg (a : ℝ) : 0 ≤ a - ⌊a⌋ := by
  have h := Int.fract_nonneg a
  simp only [Int.fract] at h
  exact h

/-- The fractional part of a real number: a - ⌊a⌋ < 1. -/
theorem fract_lt_one (a : ℝ) : a - ⌊a⌋ < 1 := by
  have h := Int.fract_lt_one a
  simp only [Int.fract] at h
  exact h

/-- Relationship between floor and ceiling: ⌈a⌉ = ⌊a⌋ + 1 iff a is not an integer. -/
theorem ceil_eq_floor_add_one_iff (a : ℝ) : ⌈a⌉ = ⌊a⌋ + 1 ↔ a ≠ ⌊a⌋ := by
  constructor
  · intro h hcontra
    have h1 : ⌈a⌉ = ⌊a⌋ := by
      have : a = (⌊a⌋ : ℝ) := hcontra
      rw [this, Int.ceil_intCast, Int.floor_intCast]
    omega
  · intro h
    have h1 : (⌊a⌋ : ℝ) < a := by
      by_contra hle
      push Not at hle
      have heq : a = ⌊a⌋ := le_antisymm hle (Int.floor_le a)
      exact h heq
    have h2 : ⌊a⌋ + 1 ≤ ⌈a⌉ := by
      rw [Int.add_one_le_iff, Int.lt_ceil]
      exact h1
    have h3 : ⌈a⌉ ≤ ⌊a⌋ + 1 := by
      have : a < ⌊a⌋ + 1 := Int.lt_floor_add_one a
      rw [Int.ceil_le]
      push_cast
      exact le_of_lt this
    omega

/-- When a is an integer, floor equals ceiling. -/
theorem floor_eq_ceil_iff (a : ℝ) : ⌊a⌋ = ⌈a⌉ ↔ a = ⌊a⌋ := by
  constructor
  · intro h
    by_contra hne
    have := ceil_eq_floor_add_one_iff a |>.mpr hne
    omega
  · intro h
    rw [h, Int.floor_intCast, Int.ceil_intCast]

end FloorCeiling

namespace Nat.Partition

/-! ### Definition of integer partitions (Definition \ref{def.pars.parts})

This section formalizes Definition \ref{def.pars.parts} from the source text.

In Mathlib, `Nat.Partition n` represents partitions of `n`. The underlying data is a
multiset of positive integers that sums to `n`. This is equivalent to the "weakly
decreasing tuple" representation in the source text:

**Definition \ref{def.pars.parts}:**

**(a)** An **(integer) partition** means a (finite) weakly decreasing tuple of positive
integers -- i.e., a finite tuple (λ₁, λ₂, ..., λₘ) of positive integers such that
λ₁ ≥ λ₂ ≥ ... ≥ λₘ.

**(b)** The **parts** of a partition (λ₁, λ₂, ..., λₘ) are simply its entries λ₁, λ₂, ..., λₘ.

**(c)** Let n ∈ ℤ. A **partition of n** means a partition whose size is n.

**(d)** Let n ∈ ℤ and k ∈ ℕ. A **partition of n into k parts** is a partition whose size
is n and whose length is k.

**Implementation note:** Mathlib uses multisets rather than tuples, which is equivalent
since partitions are determined by their parts (with multiplicity), regardless of order.
The "weakly decreasing" constraint in the tuple representation is automatically satisfied
when we sort the multiset in decreasing order.
-/

/-! #### Parts of a partition (Definition \ref{def.pars.parts} (b))

In Mathlib, `Partition.parts` returns the multiset of parts. Each part is a positive
integer (guaranteed by `parts_pos`), and the sum of parts equals the size
(guaranteed by `parts_sum`).

The parts are the fundamental data of a partition. They are positive integers
whose sum equals the size n. We use Mathlib's `Partition.parts` directly rather than
redefining it, and provide wrapper lemmas for the key properties. -/

/-- The size of a partition is the sum of its parts.
    (Definition \ref{def.pars.parts} (c))

    For a partition of n, the size is n. This is guaranteed by `Partition.parts_sum`.
    The type `Partition n` itself encodes that the partition has size n. -/
theorem size_eq {n : ℕ} (p : Partition n) : p.parts.sum = n := p.parts_sum

/-- All parts of a partition are positive.
    (Definition \ref{def.pars.parts} (a) - "tuple of positive integers")

    This is a fundamental property: every entry in a partition is ≥ 1.
    This is the defining property that distinguishes partitions from weak compositions. -/
theorem parts_pos' {n : ℕ} (p : Partition n) (i : ℕ) (hi : i ∈ p.parts) : 0 < i :=
  p.parts_pos hi

/-- A partition of n has all parts ≤ n.
    (Consequence of Definition \ref{def.pars.parts})

    Since parts are positive and sum to n, each individual part is bounded by n. -/
theorem parts_le {n : ℕ} (p : Partition n) (i : ℕ) (hi : i ∈ p.parts) : i ≤ n := by
  calc i ≤ p.parts.sum := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hi
    _ = n := p.parts_sum

/-- The empty partition is the unique partition of 0.
    (Definition \ref{def.pars.parts} (a) - empty tuple case)

    The partition of 0 has no parts. -/
theorem parts_eq_zero_of_partition_zero (p : Partition 0) : p.parts = 0 :=
  partition_zero_parts p

/-- The length of the partition of 0 is 0.
    (Definition \ref{def.pars.parts} (a) - empty tuple has length 0) -/
theorem parts_card_zero (p : Partition 0) : p.parts.card = 0 := by
  simp only [partition_zero_parts, Multiset.card_zero]

/-- For n > 0, the indiscrete partition (n) has exactly one part.
    (Example of Definition \ref{def.pars.parts}) -/
theorem indiscrete_parts_card {n : ℕ} (hn : n ≠ 0) : (indiscrete n).parts.card = 1 := by
  simp only [indiscrete_parts hn, Multiset.card_singleton]

/-- The parts of the indiscrete partition (n) for n > 0.
    (Example of Definition \ref{def.pars.parts}) -/
theorem indiscrete_parts' {n : ℕ} (hn : n ≠ 0) : (indiscrete n).parts = {n} :=
  indiscrete_parts hn

/-- Constructing a partition from a list of positive integers.
    (Definition \ref{def.pars.parts} (a) - the tuple representation)

    Given a list of positive integers that sums to n, we can construct a partition of n.
    The list need not be sorted; Mathlib's `Partition` uses multisets. -/
def ofList' {n : ℕ} (l : List ℕ) (hl_pos : ∀ i ∈ l, 0 < i) (hl_sum : l.sum = n) : Partition n :=
  ⟨↑l, @fun i hi => hl_pos i (Multiset.mem_coe.mp hi), by simp only [Multiset.sum_coe, hl_sum]⟩

/-- The parts of a partition constructed from a list.
    (Definition \ref{def.pars.parts} (b)) -/
@[simp]
theorem ofList'_parts {n : ℕ} (l : List ℕ) (hl_pos : ∀ i ∈ l, 0 < i) (hl_sum : l.sum = n) :
    (ofList' l hl_pos hl_sum).parts = ↑l := rfl

/-- Two partitions are equal iff their parts are equal.
    (Definition \ref{def.pars.parts} - partitions are determined by their parts) -/
theorem eq_iff_parts_eq {n : ℕ} (p q : Partition n) : p = q ↔ p.parts = q.parts := by
  constructor
  · intro h; rw [h]
  · intro h; exact Partition.ext h

/-! ### Examples from the textbook (Example \ref{exa.pars.pars5})

The partitions of 5 are:
- (5): one part
- (4,1): two parts
- (3,2): two parts
- (3,1,1): three parts
- (2,2,1): three parts
- (2,1,1,1): four parts
- (1,1,1,1,1): five parts
-/

/-- The partition (5) of 5. -/
example : Partition 5 := ⟨{5}, by simp, rfl⟩

/-- The partition (4,1) of 5. -/
example : Partition 5 := ⟨{4, 1}, by simp, rfl⟩

/-- The partition (3,2) of 5. -/
example : Partition 5 := ⟨{3, 2}, by simp, rfl⟩

/-- The partition (3,1,1) of 5. -/
example : Partition 5 := ⟨{3, 1, 1}, by simp, rfl⟩

/-- The partition (2,2,1) of 5. -/
example : Partition 5 := ⟨{2, 2, 1}, by simp, rfl⟩

/-- The partition (2,1,1,1) of 5. -/
example : Partition 5 := ⟨{2, 1, 1, 1}, by simp, rfl⟩

/-- The partition (1,1,1,1,1) of 5. -/
example : Partition 5 := ⟨{1, 1, 1, 1, 1}, by simp, rfl⟩

/-- There are exactly 7 partitions of 5. -/
example : Fintype.card (Partition 5) = 7 := by native_decide

/-! ### Auxiliary lemmas -/

/-- The cardinality of a multiset of positive naturals is at most its sum. -/
theorem card_le_sum_of_pos (s : Multiset ℕ) (h : ∀ i ∈ s, 0 < i) : s.card ≤ s.sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.card_cons, Multiset.sum_cons]
    have ha : 1 ≤ a := h a (Multiset.mem_cons_self a s)
    have hs : ∀ i ∈ s, 0 < i := fun i hi => h i (Multiset.mem_cons_of_mem hi)
    have ihs := ih hs
    omega

/-- Elements of a multiset are bounded by the fold max. -/
lemma fold_max_ge_of_mem (p : Multiset ℕ) (a : ℕ) (ha : a ∈ p) : a ≤ p.fold max 0 := by
  induction p using Multiset.induction with
  | empty => simp at ha
  | cons b s ih =>
    simp only [Multiset.fold_cons_left]
    simp only [Multiset.mem_cons] at ha
    rcases ha with rfl | ha
    · exact le_max_left a (Multiset.fold max 0 s)
    · exact le_trans (ih ha) (le_max_right b (Multiset.fold max 0 s))

/-- Extending the range of summation when elements are bounded. -/
lemma sum_filter_card_range_extend (s : Multiset ℕ) (M N : ℕ) (hM : ∀ x ∈ s, x ≤ M) (hMN : M ≤ N) :
    (Finset.range N).sum (fun i => (s.filter (· > i)).card) =
    (Finset.range M).sum (fun i => (s.filter (· > i)).card) := by
  have h := Finset.sum_range_add_sum_Ico (fun i => (s.filter (· > i)).card) hMN
  rw [← h]
  suffices hzero : ∑ i ∈ Finset.Ico M N, (s.filter (· > i)).card = 0 by linarith
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_Ico] at hi
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro x hx
  simp only [gt_iff_lt, not_lt]
  exact le_trans (hM x hx) hi.1

/-- The number of i < M with i < x is exactly min x M. -/
lemma card_range_filter_gt (x M : ℕ) :
    ((Finset.range M).filter (fun i => x > i)).card = min x M := by
  simp only [gt_iff_lt]
  rw [← Finset.card_range (min x M)]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Double counting: sum of filter cardinalities equals multiset sum. -/
lemma sum_filter_card_eq_sum (p : Multiset ℕ) (hp : ∀ i ∈ p, 0 < i) :
    (Finset.range (p.fold max 0)).sum (fun i => (p.filter (· > i)).card) = p.sum := by
  induction p using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have hs : ∀ i ∈ s, 0 < i := fun i hi => hp i (Multiset.mem_cons_of_mem hi)
    have ha : 0 < a := hp a (Multiset.mem_cons_self a s)
    specialize ih hs
    simp only [Multiset.sum_cons, Multiset.fold_cons_left]
    let M := s.fold max 0
    conv_lhs =>
      arg 2
      ext i
      rw [Multiset.filter_cons]
    have hcard : ∀ i, ((if a > i then {a} else 0) + s.filter (· > i)).card =
                      (if a > i then 1 else 0) + (s.filter (· > i)).card := by
      intro i
      split_ifs with h
      · simp only [Multiset.singleton_add, Multiset.card_cons]; ring
      · simp only [zero_add]
    simp_rw [hcard]
    rw [Finset.sum_add_distrib]
    have h1 : ∑ i ∈ Finset.range (max a M), (if a > i then 1 else 0) = a := by
      rw [Finset.sum_boole, Nat.cast_id]
      convert card_range_filter_gt a (max a M) using 2
      simp only [le_max_iff, le_refl, true_or, min_eq_left]
    rw [h1]
    have hbound : ∀ x ∈ s, x ≤ M := fun x hx => fold_max_ge_of_mem s x hx
    have h2 : (Finset.range (max a M)).sum (fun i => (s.filter (· > i)).card) =
              (Finset.range M).sum (fun i => (s.filter (· > i)).card) := by
      apply sum_filter_card_range_extend s M (max a M) hbound (le_max_right a M)
    rw [h2, ih]

/-- Filtering out zeros doesn't change the sum. -/
lemma sum_filter_positive (s : Multiset ℕ) : (s.filter (· > 0)).sum = s.sum := by
  have h := @Multiset.sum_filter_add_sum_filter_not ℕ _ s (· > 0) _
  simp only [gt_iff_lt, Nat.not_lt, Nat.le_zero] at h
  suffices hz : (s.filter (· = 0)).sum = 0 by linarith
  rw [Multiset.sum_eq_zero_iff]
  intro x hx
  simp only [Multiset.mem_filter] at hx
  exact hx.2

/-! ### Partition counting functions -/

/-- The partition function `p(n)`: the number of partitions of `n`.
    (Definition \ref{def.pars.pn-pkn} (b)) -/
def partitionCount (n : ℕ) : ℕ := Fintype.card (Partition n)

/-- The function `p_k(n)`: the number of partitions of `n` into exactly `k` parts.
    (Definition \ref{def.pars.pn-pkn} (a)) -/
def partsCount (k n : ℕ) : ℕ :=
  (Finset.univ : Finset (Partition n)).filter (fun p => Multiset.card p.parts = k) |>.card

/-- The number of partitions of `n` with all parts ≤ `m`.
    (Used in Theorem \ref{thm.pars.main-gf-parts-n}) -/
def partsLeqCount (m n : ℕ) : ℕ := (restricted n (· ≤ m)).card

/-- The number of partitions of `n` with all parts in a set `I`.
    (Used in Theorem \ref{thm.pars.main-gf-parts-I}) -/
def partsInCount (I : Set ℕ) [DecidablePred (· ∈ I)] (n : ℕ) : ℕ := (restricted n (· ∈ I)).card

/-! ### Basic API for partition counting functions -/

/-- `p(0) = 1`: there is exactly one partition of 0 (the empty partition).
    (Definition \ref{def.pars.pn-pkn} (b), special case) -/
@[simp]
theorem partitionCount_zero : partitionCount 0 = 1 := by
  simp only [partitionCount]
  rfl

/-- `p(1) = 1`: there is exactly one partition of 1 (the partition (1)). -/
@[simp]
theorem partitionCount_one : partitionCount 1 = 1 := by native_decide

/-- `p(n) > 0` for all `n ∈ ℕ`: there is always at least one partition of any natural number.
    For n > 0, the partition (n) has one part. For n = 0, the empty partition works. -/
theorem partitionCount_pos (n : ℕ) : 0 < partitionCount n := by
  simp only [partitionCount]
  exact Fintype.card_pos

/-! ### Examples from the textbook

The following examples verify the definitions against the values given in the textbook
following Definition \ref{def.pars.pn-pkn}. -/

/-- Example: `p(5) = 7`. The 7 partitions of 5 are:
    (5), (4,1), (3,2), (3,1,1), (2,2,1), (2,1,1,1), (1,1,1,1,1). -/
example : partitionCount 5 = 7 := by native_decide

/-- Example: `p_0(5) = 0`. There are no partitions of 5 into 0 parts. -/
example : partsCount 0 5 = 0 := by native_decide

/-- Example: `p_1(5) = 1`. The only partition of 5 into 1 part is (5). -/
example : partsCount 1 5 = 1 := by native_decide

/-- Example: `p_2(5) = 2`. The partitions of 5 into 2 parts are (4,1) and (3,2). -/
example : partsCount 2 5 = 2 := by native_decide

/-- Example: `p_3(5) = 2`. The partitions of 5 into 3 parts are (3,1,1) and (2,2,1). -/
example : partsCount 3 5 = 2 := by native_decide

/-- Example: `p_4(5) = 1`. The only partition of 5 into 4 parts is (2,1,1,1). -/
example : partsCount 4 5 = 1 := by native_decide

/-- Example: `p_5(5) = 1`. The only partition of 5 into 5 parts is (1,1,1,1,1). -/
example : partsCount 5 5 = 1 := by native_decide

/-! ### Basic properties of partition numbers -/

/-- The number of parts of a partition equals the cardinality of its parts multiset. -/
def numParts {n : ℕ} (p : Partition n) : ℕ := Multiset.card p.parts

set_option backward.isDefEq.respectTransparency false in
/-- Alternative characterization: `partsCount k n` counts partitions with `numParts = k`. -/
theorem partsCount_eq_filter_numParts (k n : ℕ) :
    partsCount k n = ((Finset.univ : Finset (Partition n)).filter (fun p => p.numParts = k)).card := by
  simp only [partsCount, numParts]

/-- The largest part of a partition (0 for the empty partition).
    (Convention \ref{conv.pars.largest-part-0}) -/
def largestPart {n : ℕ} (p : Partition n) : ℕ :=
  p.parts.fold max 0

/-- If all elements of a multiset are ≤ m, then fold max 0 is ≤ m. -/
private lemma fold_max_le_of_all_le' (s : Multiset ℕ) (m : ℕ) (h : ∀ i ∈ s, i ≤ m) :
    s.fold max 0 ≤ m := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.fold_cons_left]
    have ha : a ≤ m := h a (Multiset.mem_cons_self a t)
    have ht : ∀ i ∈ t, i ≤ m := fun i hi => h i (Multiset.mem_cons_of_mem hi)
    exact max_le ha (ih ht)

/-- A partition has largest part ≤ m iff all its parts are ≤ m.
    This is because the largest part is defined as the maximum of all parts.

    This lemma is key for proving Theorem \ref{thm.pars.main-gf-0n}, which states that
    the generating function for `p_0(n) + p_1(n) + ... + p_m(n)` equals `∏_{k=1}^m 1/(1-x^k)`.
    The proof uses:
    1. Corollary \ref{cor.pars.p0kn=dual}: the sum equals the count of partitions with largest part ≤ m
    2. This lemma: "largest part ≤ m" is equivalent to "all parts ≤ m"
    3. Theorem \ref{thm.pars.main-gf-parts-n}: the generating function for "all parts ≤ m" -/
theorem largestPart_le_iff_all_parts_le {n m : ℕ} (p : Partition n) :
    p.largestPart ≤ m ↔ ∀ i ∈ p.parts, i ≤ m := by
  unfold largestPart
  constructor
  · intro h i hi
    exact le_trans (fold_max_ge_of_mem p.parts i hi) h
  · intro h
    exact fold_max_le_of_all_le' p.parts m h

/-- The set of partitions with largest part ≤ m equals the set of partitions
    with all parts ≤ m (i.e., `restricted n (· ≤ m)`).

    This is a key equivalence used in the proof of Theorem \ref{thm.pars.main-gf-0n}. -/
theorem filter_largestPart_le_eq_restricted (n m : ℕ) :
    (Finset.univ : Finset (Partition n)).filter (fun p => p.largestPart ≤ m) =
    restricted n (· ≤ m) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, restricted]
  exact largestPart_le_iff_all_parts_le p

/-- Partitions of 0 have no parts. -/
@[simp]
theorem numParts_zero (p : Partition 0) : p.numParts = 0 := by
  simp only [numParts, partition_zero_parts, Multiset.card_zero]

/-- The largest part of the partition of 0 is 0.
    (Convention conv.pars.largest-part-0)
    
    Since the partition of 0 has no parts, the largest part (defined as the 
    maximum of all parts, with 0 as the default) is 0. -/
@[simp]
theorem largestPart_zero (p : Partition 0) : p.largestPart = 0 := by
  simp only [largestPart, partition_zero_parts, Multiset.fold_zero]

/-- For a partition of n, the largest part is at most n.
    This parallels the existing `numParts_le` lemma which states `p.numParts ≤ n`. -/
theorem largestPart_le {n : ℕ} (p : Partition n) : p.largestPart ≤ n := by
  rw [largestPart_le_iff_all_parts_le]
  exact fun i hi => parts_le p i hi

/-- For a partition of n > 0, the largest part is positive.
    This parallels `largestPart_zero` (for n = 0) and `largestPart_le`.

    Since n > 0, the partition has at least one part (by `numParts_pos`),
    and all parts are positive (by `parts_pos`). The largest part
    (fold max 0) of a non-empty multiset of positive numbers is positive. -/
theorem largestPart_pos {n : ℕ} (hn : n > 0) (p : Partition n) : 0 < p.largestPart := by
  unfold largestPart
  have hne : p.parts ≠ 0 := by
    intro h
    have := p.parts_sum
    simp only [h, Multiset.sum_zero] at this
    omega
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
  have hxpos := p.parts_pos hx
  exact lt_of_lt_of_le hxpos (fold_max_ge_of_mem p.parts x hx)

/-- A partition has at most n parts. -/
theorem numParts_le {n : ℕ} (p : Partition n) : p.numParts ≤ n := by
  simp only [numParts]
  calc p.parts.card ≤ p.parts.sum := card_le_sum_of_pos p.parts (fun i hi => p.parts_pos hi)
    _ = n := p.parts_sum

/-- For a partition of n > 0, the number of parts is positive.
    This parallels `numParts_zero` (for n = 0) and `numParts_le`. -/
theorem numParts_pos {n : ℕ} (hn : n > 0) (p : Partition n) : 0 < p.numParts := by
  simp only [numParts]
  by_contra hc
  simp only [not_lt, Nat.le_zero, Multiset.card_eq_zero] at hc
  have h := p.parts_sum
  simp only [hc, Multiset.sum_zero] at h
  omega

/-- There are no partitions of `n` into more than `n` parts.
    (Proposition \ref{prop.pars.basics} (b)) -/
theorem partsCount_of_gt {k n : ℕ} (h : k > n) : partsCount k n = 0 := by
  simp only [partsCount, filter_eq_empty_iff, Finset.card_eq_zero]
  intro p _
  have hle : Multiset.card p.parts ≤ p.parts.sum :=
    card_le_sum_of_pos p.parts (fun i hi => p.parts_pos hi)
  have hsum : Multiset.card p.parts ≤ n := by
    calc Multiset.card p.parts ≤ p.parts.sum := hle
      _ = n := p.parts_sum
  omega

/-- `p_k(n) = 0` when `n < k`: alternative form of `partsCount_of_gt` with
    the hypothesis `n < k` instead of `k > n`, useful for simp.
    (Proposition \ref{prop.pars.basics} (b)) -/
@[simp]
theorem partsCount_of_gt' {k n : ℕ} (h : n < k) : partsCount k n = 0 :=
  partsCount_of_gt h

/-- `p_0(n) = [n = 0]`: the only partition into 0 parts is the empty partition of 0.
    (Proposition \ref{prop.pars.basics} (c)) -/
theorem partsCount_zero (n : ℕ) : partsCount 0 n = if n = 0 then 1 else 0 := by
  simp only [partsCount]
  split_ifs with hn
  · subst hn
    have huniv : (Finset.univ : Finset (Partition 0)).filter
        (fun p => Multiset.card p.parts = 0) = Finset.univ := by
      ext p
      simp only [Finset.mem_filter, mem_univ, true_and, partition_zero_parts, Multiset.card_zero]
    simp only [huniv]
    rfl
  · rw [Finset.card_eq_zero, filter_eq_empty_iff]
    intro p _
    have hp : p.parts.sum = n := p.parts_sum
    by_contra hc
    simp only [Multiset.card_eq_zero] at hc
    simp only [hc, Multiset.sum_zero] at hp
    exact hn hp.symm

/-- There are no partitions of n > 0 into exactly 0 parts.
    This is a simp-friendly form of `partsCount_zero` for positive n.
    (Corollary of Proposition \ref{prop.pars.basics} (c)) -/
@[simp]
theorem partsCount_zero_left (n : ℕ) (hn : n > 0) : partsCount 0 n = 0 := by
  rw [partsCount_zero]
  simp only [Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]

/-- `partsCount k n = 0` iff `k > n` or `k = 0 ∧ n > 0`.
    This provides a complete characterization of when the partition count is zero. -/
theorem partsCount_eq_zero_iff (k n : ℕ) :
    partsCount k n = 0 ↔ k > n ∨ (k = 0 ∧ n > 0) := by
  constructor
  · -- Forward direction: if partsCount k n = 0, then k > n or (k = 0 ∧ n > 0)
    intro h
    by_contra hc
    push Not at hc
    obtain ⟨hkn, hk0⟩ := hc
    -- We have k ≤ n and (k ≠ 0 or n = 0)
    rcases Nat.eq_zero_or_pos k with hk | hkpos
    · -- k = 0
      subst hk
      -- n = 0 since k = 0 → n ≤ 0 from hk0, and n : ℕ
      have hn0 : n = 0 := Nat.le_zero.mp (hk0 rfl)
      -- But partsCount 0 0 = 1 ≠ 0
      subst hn0
      simp only [partsCount_zero, ↓reduceIte] at h
      exact Nat.one_ne_zero h
    · -- k > 0, and k ≤ n
      -- There exists a partition of n into k parts: (1, 1, ..., 1, n - k + 1)
      -- The partition (1, 1, ..., 1, n - k + 1) has k parts and sums to n
      let parts : Multiset ℕ := Multiset.replicate (k - 1) 1 + {n - k + 1}
      have hparts_card : parts.card = k := by
        simp only [parts, Multiset.card_add, Multiset.card_replicate, Multiset.card_singleton]
        omega
      have hparts_sum : parts.sum = n := by
        simp only [parts, Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_singleton,
                   smul_eq_mul, mul_one]
        omega
      have hparts_pos : ∀ x ∈ parts, 0 < x := by
        intro x hx
        simp only [parts, Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_singleton] at hx
        cases hx with
        | inl h => exact h.2 ▸ Nat.one_pos
        | inr h => omega
      let p : Partition n := { parts := parts, parts_sum := hparts_sum, parts_pos := @hparts_pos }
      have hp_mem : p ∈ (Finset.univ : Finset (Partition n)).filter
          (fun q => Multiset.card q.parts = k) := by
        simp only [Finset.mem_filter, mem_univ, true_and, p]
        exact hparts_card
      simp only [partsCount, Finset.card_eq_zero] at h
      rw [h] at hp_mem
      simp at hp_mem
  · -- Backward direction: if k > n or (k = 0 ∧ n > 0), then partsCount k n = 0
    intro h
    cases h with
    | inl hkn => exact partsCount_of_gt hkn
    | inr hk0 =>
      obtain ⟨hk, hn⟩ := hk0
      subst hk
      rw [partsCount_zero]
      simp only [Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]

/-- `p_1(n) = [n > 0]`: the only partition of a positive `n` into 1 part is `(n)`.
    (Proposition \ref{prop.pars.basics} (d)) -/
theorem partsCount_one (n : ℕ) : partsCount 1 n = if n > 0 then 1 else 0 := by
  simp only [partsCount]
  split_ifs with hn
  · -- For n > 0, there's exactly one partition into 1 part: (n)
    have h : (Finset.univ : Finset (Partition n)).filter
        (fun p => Multiset.card p.parts = 1) = {indiscrete n} := by
      ext p
      simp only [Finset.mem_filter, mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hcard
        ext
        have hp_sum : p.parts.sum = n := p.parts_sum
        rw [Multiset.card_eq_one] at hcard
        obtain ⟨a, ha⟩ := hcard
        simp only [ha, Multiset.sum_singleton] at hp_sum
        subst hp_sum
        simp only [ha, indiscrete_parts (Nat.pos_iff_ne_zero.mp hn)]
      · intro heq
        rw [heq, indiscrete_parts (Nat.pos_iff_ne_zero.mp hn)]
        simp only [Multiset.card_singleton]
    rw [h]
    simp only [Finset.card_singleton]
  · -- For n = 0, there are no partitions into 1 part
    push Not at hn
    interval_cases n
    rw [Finset.card_eq_zero, filter_eq_empty_iff]
    intro p _
    simp only [partition_zero_parts, Multiset.card_zero]
    omega

/-! ### Helper lemmas for the recurrence relation -/

/-- A partition containing 1 as a part. -/
def containsOne {n : ℕ} (p : Partition n) : Prop := 1 ∈ p.parts

instance {n : ℕ} : DecidablePred (containsOne (n := n)) :=
  fun p => Multiset.decidableMem 1 p.parts

/-- Partitions of n into k parts that contain 1. -/
def partsWithOne (k n : ℕ) : Finset (Partition n) :=
  (Finset.univ : Finset (Partition n)).filter fun p => p.parts.card = k ∧ containsOne p

/-- Partitions of n into k parts that don't contain 1. -/
def partsWithoutOne (k n : ℕ) : Finset (Partition n) :=
  (Finset.univ : Finset (Partition n)).filter fun p => p.parts.card = k ∧ ¬containsOne p

private lemma partsWithOne_disjoint_partsWithoutOne {k n : ℕ} :
    Disjoint (partsWithOne k n) (partsWithoutOne k n) := by
  rw [Finset.disjoint_iff_ne]
  intro p hp q hq heq
  simp only [partsWithOne, partsWithoutOne, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  rw [heq] at hp
  exact hq.2 hp.2

private lemma partsWithOne_union_partsWithoutOne {k n : ℕ} :
    partsWithOne k n ∪ partsWithoutOne k n =
    (Finset.univ : Finset (Partition n)).filter fun p => p.parts.card = k := by
  ext p
  simp only [partsWithOne, partsWithoutOne, Finset.mem_union, Finset.mem_filter,
             Finset.mem_univ, true_and]
  constructor
  · intro h; rcases h with ⟨hk, _⟩ | ⟨hk, _⟩ <;> exact hk
  · intro hk'; by_cases h : containsOne p
    · left; exact ⟨hk', h⟩
    · right; exact ⟨hk', h⟩

lemma partsCount_split {k n : ℕ} :
    partsCount k n = (partsWithOne k n).card + (partsWithoutOne k n).card := by
  simp only [partsCount]
  rw [← Finset.card_union_of_disjoint partsWithOne_disjoint_partsWithoutOne]
  congr 1
  exact partsWithOne_union_partsWithoutOne.symm

private lemma sum_ge_card_of_all_pos {s : Multiset ℕ} (h : ∀ x ∈ s, x > 0) : s.sum ≥ s.card := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.sum_cons, Multiset.card_cons]
    have ha : a > 0 := h a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, x > 0 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have := ih ht
    omega

private lemma sum_map_sub_one_eq {s : Multiset ℕ} (h : ∀ x ∈ s, x > 1) :
    (s.map (· - 1)).sum = s.sum - s.card := by
  have hpos : ∀ x ∈ s, x > 0 := fun x hx => Nat.lt_trans Nat.zero_lt_one (h x hx)
  have hge : s.sum ≥ s.card := sum_ge_card_of_all_pos hpos
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have ha : a > 1 := h a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, x > 1 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have htpos : ∀ x ∈ t, x > 0 := fun x hx => Nat.lt_trans Nat.zero_lt_one (ht x hx)
    have htge : t.sum ≥ t.card := sum_ge_card_of_all_pos htpos
    rw [ih ht htpos htge]
    omega

private lemma filter_ne_zero_of_all_pos {s : Multiset ℕ} (h : ∀ x ∈ s, x > 0) :
    s.filter (· ≠ 0) = s := by
  rw [Multiset.filter_eq_self]
  intro x hx
  exact Nat.pos_iff_ne_zero.mp (h x hx)

/-- Remove one 1 from a partition containing 1 to get a partition of n-1. -/
def removeOne {n : ℕ} (p : Partition n) (h : 1 ∈ p.parts) : Partition (n - 1) :=
  Partition.ofSums (n - 1) (p.parts.erase 1) (by
    have hsum : p.parts.sum = (p.parts.erase 1).sum + 1 := by
      rw [← Multiset.cons_erase h]; simp [add_comm]
    rw [p.parts_sum] at hsum
    omega)

/-- Add one 1 to a partition to get a partition of n+1. -/
def addOne {n : ℕ} (p : Partition n) : Partition (n + 1) :=
  Partition.ofSums (n + 1) (1 ::ₘ p.parts) (by simp [p.parts_sum, add_comm])

/-- Subtract 1 from each part of a partition (when all parts > 1) to get a partition of n - k. -/
def subtractOneFromEach {n k : ℕ} (p : Partition n) (hk : p.parts.card = k)
    (h : ∀ x ∈ p.parts, x > 1) : Partition (n - k) :=
  Partition.ofSums (n - k) (p.parts.map (· - 1)) (by
    rw [sum_map_sub_one_eq h, p.parts_sum, hk])

/-- Add 1 to each part of a partition to get a partition of n + k. -/
def addOneToEach {n k : ℕ} (p : Partition n) (hk : p.parts.card = k) : Partition (n + k) :=
  Partition.ofSums (n + k) (p.parts.map (· + 1)) (by
    simp only [Multiset.sum_map_add, Multiset.map_id', Multiset.map_const', p.parts_sum, hk]
    simp [Multiset.sum_replicate])

private lemma removeOne_parts {n : ℕ} (p : Partition n) (h : 1 ∈ p.parts) :
    (removeOne p h).parts = p.parts.erase 1 := by
  simp only [removeOne, Partition.ofSums]
  apply filter_ne_zero_of_all_pos
  intro x hx
  exact p.parts_pos (Multiset.erase_subset 1 p.parts hx)

private lemma removeOne_parts_card {n : ℕ} (p : Partition n) (h : 1 ∈ p.parts) :
    (removeOne p h).parts.card = p.parts.card - 1 := by
  rw [removeOne_parts, Multiset.card_erase_of_mem h]
  simp only [Nat.pred_eq_sub_one]

private lemma addOne_parts {n : ℕ} (p : Partition n) :
    (addOne p).parts = 1 ::ₘ p.parts := by
  simp only [addOne, Partition.ofSums]
  rw [Multiset.filter_cons_of_pos]
  · congr 1
    apply filter_ne_zero_of_all_pos
    intro x hx
    exact p.parts_pos hx
  · decide

private lemma addOne_parts_card {n : ℕ} (p : Partition n) :
    (addOne p).parts.card = p.parts.card + 1 := by
  rw [addOne_parts]
  simp only [Multiset.card_cons]

private lemma addOne_containsOne {n : ℕ} (p : Partition n) : containsOne (addOne p) := by
  simp only [containsOne, addOne_parts, Multiset.mem_cons, true_or]

/-- Helper lemma: map (· - 1) is injective on multisets where all elements > 1. -/
private lemma map_sub_one_injective {s t : Multiset ℕ} (hs : ∀ x ∈ s, x > 1) (ht : ∀ x ∈ t, x > 1)
    (h : s.map (· - 1) = t.map (· - 1)) : s = t := by
  have key : ∀ (m : Multiset ℕ), (∀ x ∈ m, x > 1) → (m.map (· - 1)).map (· + 1) = m := by
    intro m hm
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id m]
    apply Multiset.map_congr rfl
    intro x hx
    simp only [Function.comp_apply, id_eq]
    have : x > 1 := hm x hx
    omega
  calc s = (s.map (· - 1)).map (· + 1) := (key s hs).symm
    _ = (t.map (· - 1)).map (· + 1) := by rw [h]
    _ = t := key t ht

/-- Lemmas for subtractOneFromEach. -/
private lemma subtractOneFromEach_parts {n k : ℕ} (p : Partition n) (hk : p.parts.card = k)
    (h : ∀ x ∈ p.parts, x > 1) :
    (subtractOneFromEach p hk h).parts = p.parts.map (· - 1) := by
  simp only [subtractOneFromEach, Partition.ofSums]
  apply filter_ne_zero_of_all_pos
  intro x hx
  simp only [Multiset.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have : y > 1 := h y hy
  omega

private lemma subtractOneFromEach_parts_card {n k : ℕ} (p : Partition n) (hk : p.parts.card = k)
    (h : ∀ x ∈ p.parts, x > 1) :
    (subtractOneFromEach p hk h).parts.card = k := by
  rw [subtractOneFromEach_parts, Multiset.card_map, hk]

/-- Lemmas for addOneToEach. -/
private lemma addOneToEach_parts {n k : ℕ} (p : Partition n) (hk : p.parts.card = k) :
    (addOneToEach p hk).parts = p.parts.map (· + 1) := by
  simp only [addOneToEach, Partition.ofSums]
  apply filter_ne_zero_of_all_pos
  intro x hx
  simp only [Multiset.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have : y > 0 := p.parts_pos hy
  omega

private lemma addOneToEach_parts_card {n k : ℕ} (p : Partition n) (hk : p.parts.card = k) :
    (addOneToEach p hk).parts.card = k := by
  rw [addOneToEach_parts, Multiset.card_map, hk]

/-- Helper to cast partition when sizes are equal. -/
private def castPartition {n m : ℕ} (h : n = m) (p : Partition n) : Partition m where
  parts := p.parts
  parts_sum := by rw [← h]; exact p.parts_sum
  parts_pos := @p.parts_pos

private lemma castPartition_parts {n m : ℕ} (h : n = m) (p : Partition n) :
    (castPartition h p).parts = p.parts := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Bijection: partsWithOne k n ↔ partitions of (n-1) into (k-1) parts. -/
lemma partsWithOne_card_eq {k n : ℕ} (hk : k > 0) (hn : n > 0) :
    (partsWithOne k n).card = partsCount (k - 1) (n - 1) := by
  simp only [partsWithOne, partsCount]
  have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  apply Finset.card_bij (fun p hp => by
    have hmem := Finset.mem_filter.mp hp
    exact removeOne p hmem.2.2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [removeOne_parts_card]; omega
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    ext
    have h1 : (removeOne p₁ hp₁.2).parts = (removeOne p₂ hp₂.2).parts := by rw [heq]
    simp only [removeOne_parts] at h1
    rw [← Multiset.cons_erase hp₁.2, ← Multiset.cons_erase hp₂.2, h1]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    let p' := addOne q
    let p := castPartition hn_eq p'
    have hp'_parts : p'.parts = 1 ::ₘ q.parts := addOne_parts q
    have h1mem : 1 ∈ p.parts := by
      simp only [p, castPartition_parts, hp'_parts]
      exact Multiset.mem_cons_self 1 q.parts
    refine ⟨p, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, h1mem⟩
      have hp'_card : p'.parts.card = q.parts.card + 1 := addOne_parts_card q
      simp only [p, castPartition_parts, hp'_card, hq]; omega
    · ext
      simp only [removeOne_parts, p, castPartition_parts, hp'_parts, Multiset.erase_cons_head]

/-- Bijection: partsWithoutOne k n ↔ partitions of (n-k) into k parts. -/
lemma partsWithoutOne_card_eq {k n : ℕ} (hk : k > 0) :
    (partsWithoutOne k n).card = partsCount k (n - k) := by
  simp only [partsWithoutOne, partsCount]
  by_cases hn : n < k
  · -- When n < k, both sides are 0
    have h1 : ((Finset.univ : Finset (Partition n)).filter
        fun p => p.parts.card = k ∧ ¬containsOne p).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _
      simp only [not_and, not_not]
      intro hcard
      have hsum : p.parts.sum ≥ k := by
        calc p.parts.sum ≥ p.parts.card := sum_ge_card_of_all_pos (fun x hx => p.parts_pos hx)
          _ = k := hcard
      have : p.parts.sum = n := p.parts_sum
      omega
    have h2 : ((Finset.univ : Finset (Partition (n - k))).filter
        fun p => p.parts.card = k).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _ hcard
      have hsum : p.parts.sum ≥ k := by
        calc p.parts.sum ≥ p.parts.card := sum_ge_card_of_all_pos (fun x hx => p.parts_pos hx)
          _ = k := hcard
      have : p.parts.sum = n - k := p.parts_sum
      have : n - k = 0 := Nat.sub_eq_zero_of_le (le_of_lt hn)
      omega
    rw [h1, h2]
  · -- When n ≥ k
    push Not at hn
    have hn_eq : n - k + k = n := Nat.sub_add_cancel hn
    apply Finset.card_bij (fun p hp => by
      have hmem := Finset.mem_filter.mp hp
      have hno1 : ∀ x ∈ p.parts, x > 1 := by
        intro x hx
        have hpos := p.parts_pos hx
        have hne1 : x ≠ 1 := fun heq => by rw [heq] at hx; exact hmem.2.2 hx
        omega
      exact subtractOneFromEach p hmem.2.1 hno1)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have hno1 : ∀ x ∈ p.parts, x > 1 := by
        intro x hx
        have hpos := p.parts_pos hx
        have hne1 : x ≠ 1 := fun heq => by rw [heq] at hx; exact hp.2 hx
        omega
      exact subtractOneFromEach_parts_card p hp.1 hno1
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
      have hno1₁ : ∀ x ∈ p₁.parts, x > 1 := by
        intro x hx
        have hpos := p₁.parts_pos hx
        have hne1 : x ≠ 1 := fun h => by rw [h] at hx; exact hp₁.2 hx
        omega
      have hno1₂ : ∀ x ∈ p₂.parts, x > 1 := by
        intro x hx
        have hpos := p₂.parts_pos hx
        have hne1 : x ≠ 1 := fun h => by rw [h] at hx; exact hp₂.2 hx
        omega
      ext
      have h1 : (subtractOneFromEach p₁ hp₁.1 hno1₁).parts =
                (subtractOneFromEach p₂ hp₂.1 hno1₂).parts := by rw [heq]
      simp only [subtractOneFromEach_parts] at h1
      rw [map_sub_one_injective hno1₁ hno1₂ h1]
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      let p' := addOneToEach q hq
      let p := castPartition hn_eq p'
      have hp'_parts : p'.parts = q.parts.map (· + 1) := addOneToEach_parts q hq
      have hno1 : ∀ x ∈ p.parts, x > 1 := by
        intro x hx
        simp only [p, castPartition_parts, hp'_parts, Multiset.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        have : y > 0 := q.parts_pos hy
        omega
      have hp_card : p.parts.card = k := by
        simp only [p, castPartition_parts]; exact addOneToEach_parts_card q hq
      have hp_no1 : ¬containsOne p := by
        simp only [containsOne, p, castPartition_parts, hp'_parts, Multiset.mem_map]
        intro ⟨y, hy, heq⟩
        have : y > 0 := q.parts_pos hy
        omega
      refine ⟨p, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hp_card, hp_no1⟩
      · have heq_parts : (subtractOneFromEach p hp_card hno1).parts = q.parts := by
          simp only [subtractOneFromEach_parts, p, castPartition_parts, hp'_parts,
                     Multiset.map_map, Function.comp]
          conv_rhs => rw [← Multiset.map_id q.parts]
          apply Multiset.map_congr rfl
          intro x hx
          simp only [id_eq]
          have : x > 0 := q.parts_pos hx
          omega
        ext; rw [heq_parts]

/-- The recurrence relation for partition numbers:
    `p_k(n) = p_k(n-k) + p_{k-1}(n-1)` for `k > 0` and `n > 0`.
    (Proposition \ref{prop.pars.basics} (e))

    **Note:** The hypothesis `n > 0` is required because in natural number arithmetic,
    `0 - 1 = 0`, so the recurrence fails for `k = 1, n = 0`:
    - LHS = `p_1(0) = 0`
    - RHS = `p_1(0) + p_0(0) = 0 + 1 = 1`

    This classifies partitions into:
    - Type 1: partitions with 1 as a part (bijection with partitions of n-1 into k-1 parts)
    - Type 2: partitions without 1 (subtract 1 from each part → partitions of n-k into k parts)

    The proof requires establishing two bijections:
    1. {partitions of n into k parts containing 1} ↔ {partitions of n-1 into k-1 parts}
       via removeOne/addOne
    2. {partitions of n into k parts not containing 1} ↔ {partitions of n-k into k parts}
       via subtractOneFromEach/addOneToEach -/
theorem partsCount_recurrence {k n : ℕ} (hk : k > 0) (hn : n > 0) :
    partsCount k n = partsCount k (n - k) + partsCount (k - 1) (n - 1) := by
  rw [partsCount_split, add_comm]
  congr 1
  · exact partsWithoutOne_card_eq hk
  · exact partsWithOne_card_eq hk hn

/-- A partition into 2 parts has the form {n-b, b} for some 1 ≤ b ≤ n/2. -/
lemma partition_two_parts_form {n : ℕ} (p : Partition n) (hp : p.parts.card = 2) :
    ∃ b : ℕ, 1 ≤ b ∧ 2 * b ≤ n ∧ p.parts = {n - b, b} := by
  rw [Multiset.card_eq_two] at hp
  obtain ⟨a, b, hab⟩ := hp
  wlog h : b ≤ a generalizing a b
  · push Not at h
    have hab' : p.parts = {b, a} := by
      rw [hab]; ext x
      simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
      split_ifs <;> omega
    exact this b a hab' (le_of_lt h)
  have hsum : a + b = n := by
    have := p.parts_sum; rw [hab] at this; simp at this; omega
  have hb_pos : 0 < b := p.parts_pos (by rw [hab]; simp)
  use b
  refine ⟨by omega, by omega, ?_⟩
  rw [hab]; congr 1; omega

/-- The minimum element of a 2-element multiset {a, b} with n ≥ a + b. -/
private lemma fold_min_of_two_multiset (a b n : ℕ) (h : a + b ≤ n) :
    ({a, b} : Multiset ℕ).fold min n = min a b := by
  simp only [Multiset.insert_eq_cons, Multiset.fold_cons_left, Multiset.fold_singleton]
  have ha : a ≤ n := by omega
  have hb : b ≤ n := by omega
  omega

/-- Extract the smaller part from a partition into 2 parts. -/
private def smallerPartOf {n : ℕ} (p : Partition n) (_ : p.parts.card = 2) : ℕ :=
  p.parts.fold min n

private lemma smallerPartOf_spec {n : ℕ} (p : Partition n) (hp : p.parts.card = 2) :
    let b := smallerPartOf p hp
    1 ≤ b ∧ 2 * b ≤ n ∧ p.parts = {n - b, b} := by
  obtain ⟨b, hb1, hb2, hparts⟩ := partition_two_parts_form p hp
  simp only [smallerPartOf, hparts]
  have hsum : (n - b) + b = n := by omega
  rw [fold_min_of_two_multiset _ _ _ (le_of_eq hsum)]
  have hmin : min (n - b) b = b := by omega
  simp only [hmin]
  exact ⟨hb1, hb2, trivial⟩

/-- Construct a partition from a smaller part b. -/
private def ofSmallerPart (n b : ℕ) (hb1 : 1 ≤ b) (hb2 : 2 * b ≤ n) : Partition n :=
  Partition.ofSums n {n - b, b} (by simp; omega)

private lemma ofSmallerPart_parts (n b : ℕ) (hb1 : 1 ≤ b) (hb2 : 2 * b ≤ n) :
    (ofSmallerPart n b hb1 hb2).parts = {n - b, b} := by
  simp only [ofSmallerPart, Partition.ofSums]
  have hnb_pos : n - b ≠ 0 := by omega
  have hb_pos : b ≠ 0 := by omega
  ext x
  simp only [Multiset.count_filter, Multiset.insert_eq_cons, Multiset.count_cons,
    Multiset.count_singleton]
  split_ifs with h1 h2 h3 h4 <;> simp_all

private lemma ofSmallerPart_parts_card (n b : ℕ) (hb1 : 1 ≤ b) (hb2 : 2 * b ≤ n) :
    (ofSmallerPart n b hb1 hb2).parts.card = 2 := by
  rw [ofSmallerPart_parts]
  simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton]

private lemma smallerPartOf_ofSmallerPart (n b : ℕ) (hb1 : 1 ≤ b) (hb2 : 2 * b ≤ n) :
    smallerPartOf (ofSmallerPart n b hb1 hb2) (ofSmallerPart_parts_card n b hb1 hb2) = b := by
  simp only [smallerPartOf, ofSmallerPart_parts]
  rw [fold_min_of_two_multiset _ _ _ (by omega)]
  omega

/-- `p_2(n) = ⌊n/2⌋` for `n ∈ ℕ`.
    (Proposition \ref{prop.pars.basics} (f))

    The partitions of n into 2 parts are (n-1,1), (n-2,2), ..., (⌈n/2⌉, ⌊n/2⌋). -/
theorem partsCount_two (n : ℕ) : partsCount 2 n = n / 2 := by
  simp only [partsCount]
  -- Establish bijection with Finset.Icc 1 (n/2)
  have h : (Finset.Icc 1 (n / 2)).card = n / 2 := by
    rw [Nat.card_Icc]
    omega
  rw [← h]
  -- Now prove the cardinalities are equal via a bijection
  apply Finset.card_bij (fun p hp => smallerPartOf p (Finset.mem_filter.mp hp).2)
  · -- The image is in Icc 1 (n/2)
    intro p hp
    obtain ⟨hb1, hb2, _⟩ := smallerPartOf_spec p (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_Icc]
    constructor
    · exact hb1
    · exact Nat.le_div_iff_mul_le (by omega) |>.mpr (by linarith)
  · -- Injectivity
    intro p₁ hp₁ p₂ hp₂ heq
    obtain ⟨_, _, hparts₁⟩ := smallerPartOf_spec p₁ (Finset.mem_filter.mp hp₁).2
    obtain ⟨_, _, hparts₂⟩ := smallerPartOf_spec p₂ (Finset.mem_filter.mp hp₂).2
    ext
    simp only [hparts₁, hparts₂, heq]
  · -- Surjectivity
    intro b hb
    simp only [Finset.mem_Icc] at hb
    have hb2 : 2 * b ≤ n := by
      have := hb.2
      omega
    use ofSmallerPart n b hb.1 hb2
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, mem_univ, true_and]
      exact ofSmallerPart_parts_card n b hb.1 hb2
    · exact smallerPartOf_ofSmallerPart n b hb.1 hb2

/-- `p(n) = p_0(n) + p_1(n) + ... + p_n(n)` for `n ∈ ℕ`.
    (Proposition \ref{prop.pars.basics} (g)) -/
theorem partitionCount_sum (n : ℕ) :
    partitionCount n = ∑ k ∈ Finset.range (n + 1), partsCount k n := by
  simp only [partitionCount, partsCount]
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun p : Partition n => p.parts.card)]
  · simp only [Finset.card_univ]
  · intro p _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (numParts_le p)

/-! ### Generating functions -/

section GenFun

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]

/-- The generating function for partition numbers:
    `∑_{n≥0} p(n) x^n = ∏_{k≥1} 1/(1-x^k)`.
    (Theorem \ref{thm.pars.main-gf})

    More precisely, this states that the power series whose n-th coefficient is
    the number of partitions of n equals the infinite product ∏_{k≥1} (∑_{j≥0} x^{kj}).

    The product converges in the power series topology because
    multiplying by 1/(1-x^k) = ∑_{j≥0} x^{kj} doesn't affect the first k coefficients.

    The proof uses Mathlib's `hasProd_powerSeriesMk_card_restricted` with the trivially
    true predicate. -/
theorem partitionCount_genFun :
    HasProd (fun k => ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j))
      (PowerSeries.mk fun n => (partitionCount n : R)) := by
  have h := hasProd_powerSeriesMk_card_restricted R (fun _ => True)
  simp only [ite_true] at h
  convert h using 2
  ext n
  have : (restricted n (fun _ => True)).card = partitionCount n := by
    simp only [restricted, partitionCount]
    rw [Finset.filter_true_of_mem (by simp : ∀ x ∈ (Finset.univ : Finset (Partition n)), ∀ i ∈ x.parts, True)]
    exact Finset.card_univ
  simp only [this]

/-- The generating function for partitions with parts ≤ m:
    `∑_{n≥0} p_{parts≤m}(n) x^n = ∏_{k=1}^m 1/(1-x^k)`.
    (Theorem \ref{thm.pars.main-gf-parts-n})

    This is a finite product version of the partition generating function.
    The product is over k from 1 to m, expressed here with shifted index as
    a conditional infinite product. -/
theorem partitionCount_genFun_partsLeq (m : ℕ) :
    HasProd (fun k => if k + 1 ≤ m then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1)
      (PowerSeries.mk fun n => (partsLeqCount m n : R)) := by
  convert hasProd_powerSeriesMk_card_restricted R (· ≤ m) using 1; rfl

/-- The generating function for partitions with parts ≤ m, expressed as a finite product:
    `∑_{n≥0} p_{parts≤m}(n) x^n = ∏_{k=1}^m (∑_{j≥0} x^{kj})`.
    (Theorem \ref{thm.pars.main-gf-parts-n})

    This is the same theorem as `partitionCount_genFun_partsLeq`, but expressed
    as an equality of power series rather than a `HasProd` statement.

    The product `∏_{k=1}^m (∑_{j≥0} x^{kj})` equals `∏_{k=1}^m 1/(1-x^k)` since
    the geometric series `1/(1-x^k) = ∑_{j≥0} x^{kj}` converges in the power series topology. -/
theorem partitionCount_genFun_partsLeq_finprod (m : ℕ) :
    (∏ k ∈ range m, (∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j))) =
    PowerSeries.mk fun n => ((restricted n (· ≤ m)).card : R) := by
  have h := hasProd_powerSeriesMk_card_restricted R (· ≤ m)
  rw [← h.tprod_eq]
  -- Convert the finite product to match the infinite product form
  have hprod : ∏ k ∈ range m, (∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j)) =
               ∏ k ∈ range m, (if k + 1 ≤ m then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [mem_range] at hk
    simp only [show k + 1 ≤ m by omega, ite_true]
  rw [hprod]
  symm
  apply tprod_eq_prod
  intro k hk
  simp only [mem_range, not_lt] at hk
  simp only [show ¬(k + 1 ≤ m) by omega, ite_false]

/-- The number of partitions with parts ≤ m equals the n-th coefficient
    of the finite product ∏_{k=1}^m (∑_{j≥0} x^{kj}).
    (Corollary to Theorem \ref{thm.pars.main-gf-parts-n}) -/
theorem partsLeqCount_eq_coeff (m n : ℕ) :
    ((restricted n (· ≤ m)).card : R) =
    (∏ k ∈ range m, (∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j))).coeff n := by
  rw [partitionCount_genFun_partsLeq_finprod]
  simp only [coeff_mk]

/-- The generating function for partitions with parts in a set I:
    `∑_{n≥0} p_I(n) x^n = ∏_{k∈I} 1/(1-x^k)`.
    (Theorem \ref{thm.pars.main-gf-parts-I})

    This generalizes both the standard partition generating function (I = ℕ⁺)
    and the finite product version (I = {1, ..., m}).

    The product is over k in I, expressed here with shifted index as a conditional
    infinite product. Each factor `∑' j, X^((k+1)*j)` equals `1/(1-X^(k+1))` as
    a geometric series.

    **Proof sketch:** The bijection from the TeX source maps each essentially finite
    family `(u_i)_{i∈I}` of nonnegative integers to the partition containing each
    `i ∈ I` exactly `u_i` times. The coefficient of `X^n` on the product side counts
    such families with `∑_{i∈I} i·u_i = n`, which bijects with partitions of `n`
    having all parts in `I`. -/
theorem partitionCount_genFun_partsIn (I : Set ℕ) [DecidablePred (· ∈ I)] :
    HasProd (fun k => if (k + 1) ∈ I then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1)
      (PowerSeries.mk fun n => (partsInCount I n : R)) := by
  convert hasProd_powerSeriesMk_card_restricted R (· ∈ I) using 1; rfl

/-- The infinite product form of the generating function for partitions with parts in I.
    This is the `tprod` version of `partitionCount_genFun_partsIn`.

    Expresses the generating function as an unconditional infinite product. -/
theorem partsInCount_genFun_eq_tprod (I : Set ℕ) [DecidablePred (· ∈ I)] :
    PowerSeries.mk (fun n => (partsInCount I n : R)) =
    ∏' k, if (k + 1) ∈ I then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1 :=
  (partitionCount_genFun_partsIn I).tprod_eq.symm

/-- The infinite product for partitions with parts in I is multipliable.
    This is useful when manipulating the product form of the generating function. -/
theorem multipliable_partsIn_genFun (I : Set ℕ) [DecidablePred (· ∈ I)] :
    Multipliable (fun k => if (k + 1) ∈ I then ∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j) else 1) :=
  (partitionCount_genFun_partsIn (R := R) I).multipliable

end GenFun

/-! ### Odd parts and distinct parts

This section formalizes Euler's odd-distinct identity (Theorem \ref{thm.pars.odd-dist-equal}),
which states that the number of partitions of n into odd parts equals the number of
partitions of n into distinct parts.

#### Definition \ref{def.pars.odd-dist-parts}

* A **partition into odd parts** is a partition whose all parts are odd.
* A **partition into distinct parts** is a partition whose parts are all different.
* `p_odd(n)` = number of partitions of n into odd parts
* `p_dist(n)` = number of partitions of n into distinct parts

#### Theorem \ref{thm.pars.odd-dist-equal}: Euler's Odd-Distinct Identity

We have `p_odd(n) = p_dist(n)` for each n ∈ ℕ.

##### Generating Function Proof

The identity follows from the generating function identity:
```
∏_{i>0} (1-x^{2i-1})^{-1} = ∏_{k>0} (1+x^k)
```
The LHS generates partitions into odd parts (each odd k can appear any number of times).
The RHS generates partitions into distinct parts (each k appears 0 or 1 times).

##### Bijective Proof

**Map A: odd parts → distinct parts**
Given a partition λ into odd parts, repeatedly merge pairs of equal parts until no
equal parts remain. The result A(λ) is a partition into distinct parts.

Example: (5,5,3,1,1,1) → (10,3,2,1) by merging (5,5)→10 and (1,1)→2.

This is well-defined because merging equal odd parts produces even parts, and the
process terminates. The final partition has distinct parts because if k appears m times
in the original partition, then in A(λ), the parts 2^0·k, 2^1·k, 2^2·k, ... appear
according to the binary representation of m.

**Map B: distinct parts → odd parts**
Given a partition λ into distinct parts, repeatedly split even parts into halves until
only odd parts remain.

Example: (10,3,2,1) → (5,5,3,1,1,1) by splitting 10→(5,5) and 2→(1,1).

The maps A and B are mutually inverse, establishing the bijection.
-/

/-- A partition into odd parts is a partition whose all parts are odd.
    (Definition \ref{def.pars.odd-dist-parts} (a))

    For example, (7), (5,1,1), (3,3,1), (3,1,1,1,1), (1,1,1,1,1,1,1) are the
    partitions of 7 into odd parts. -/
def IsOddParts {n : ℕ} (p : Partition n) : Prop := ∀ i ∈ p.parts, Odd i

/-- A partition into distinct parts is a partition whose parts are all different.
    (Definition \ref{def.pars.odd-dist-parts} (b))

    For example, (7), (6,1), (5,2), (4,3), (4,2,1) are the partitions of 7 into
    distinct parts. Note that repeated parts are not allowed. -/
def IsDistinctParts {n : ℕ} (p : Partition n) : Prop := p.parts.Nodup

/-- The number of partitions of n into odd parts: `p_odd(n)`.
    (Definition \ref{def.pars.odd-dist-parts} (c))

    This counts the partitions of n where every part is an odd number.
    Uses Mathlib's `Nat.Partition.odds` which filters partitions by the
    predicate `¬Even` (equivalent to `Odd` for positive integers). -/
def oddPartsCount (n : ℕ) : ℕ := (odds n).card

/-- The number of partitions of n into distinct parts: `p_dist(n)`.
    (Definition \ref{def.pars.odd-dist-parts} (c))

    This counts the partitions of n where all parts are different (no repeats).
    Uses Mathlib's `Nat.Partition.distincts` which filters partitions by
    the `Nodup` predicate on the parts multiset. -/
def distinctPartsCount (n : ℕ) : ℕ := (distincts n).card

instance {n : ℕ} (p : Partition n) : Decidable (IsOddParts p) :=
  inferInstanceAs (Decidable (∀ i ∈ p.parts, Odd i))

instance {n : ℕ} (p : Partition n) : Decidable (IsDistinctParts p) :=
  inferInstanceAs (Decidable p.parts.Nodup)

/-! #### Examples from the textbook (following Definition \ref{def.pars.odd-dist-parts}) -/

/-- Example: `p_odd(7) = 5`. The partitions of 7 into odd parts are:
    (7), (5,1,1), (3,3,1), (3,1,1,1,1), (1,1,1,1,1,1,1). -/
example : oddPartsCount 7 = 5 := by native_decide

/-- Example: `p_dist(7) = 5`. The partitions of 7 into distinct parts are:
    (7), (6,1), (5,2), (4,3), (4,2,1). -/
example : distinctPartsCount 7 = 5 := by native_decide

/-- Example: `p_odd(0) = 1`. The only partition of 0 into odd parts is the empty partition. -/
example : oddPartsCount 0 = 1 := by native_decide

/-- Example: `p_dist(0) = 1`. The only partition of 0 into distinct parts is the empty partition. -/
example : distinctPartsCount 0 = 1 := by native_decide

/-- `p_odd(0) = 1`: the only partition of 0 into odd parts is the empty partition.
    (Following Definition \ref{def.pars.odd-dist-parts}) -/
@[simp]
theorem oddPartsCount_zero : oddPartsCount 0 = 1 := by native_decide

/-- `p_dist(0) = 1`: the only partition of 0 into distinct parts is the empty partition.
    (Following Definition \ref{def.pars.odd-dist-parts}) -/
@[simp]
theorem distinctPartsCount_zero : distinctPartsCount 0 = 1 := by native_decide

/-- Example: `p_odd(3) = 2`. The partitions of 3 into odd parts are (3) and (1,1,1). -/
example : oddPartsCount 3 = 2 := by native_decide

/-- Example: `p_dist(3) = 2`. The partitions of 3 into distinct parts are (3) and (2,1). -/
example : distinctPartsCount 3 = 2 := by native_decide

/-! #### API for IsOddParts and IsDistinctParts -/

/-- The empty partition (of 0) is trivially a partition into odd parts. -/
theorem isOddParts_zero (p : Partition 0) : p.IsOddParts := by
  simp only [IsOddParts, partition_zero_parts]
  intro i hi
  exact (Multiset.notMem_zero i hi).elim

/-- The empty partition (of 0) is trivially a partition into distinct parts. -/
theorem isDistinctParts_zero (p : Partition 0) : p.IsDistinctParts := by
  simp only [IsDistinctParts, partition_zero_parts, Multiset.nodup_zero]

/-- A partition is into odd parts iff all its parts satisfy `Odd`. -/
theorem isOddParts_iff {n : ℕ} (p : Partition n) :
    p.IsOddParts ↔ ∀ i ∈ p.parts, Odd i := Iff.rfl

/-- A partition is into distinct parts iff its parts multiset has no duplicates. -/
theorem isDistinctParts_iff {n : ℕ} (p : Partition n) :
    p.IsDistinctParts ↔ p.parts.Nodup := Iff.rfl

/-- Alternative characterization: a partition is into distinct parts iff
    each part appears at most once. -/
theorem isDistinctParts_iff_count_le_one {n : ℕ} (p : Partition n) :
    p.IsDistinctParts ↔ ∀ i, p.parts.count i ≤ 1 := by
  simp only [IsDistinctParts, Multiset.nodup_iff_count_le_one]

/-- Characterization of `odds` in terms of `IsOddParts`. -/
theorem mem_odds_iff {n : ℕ} (p : Partition n) : p ∈ odds n ↔ p.IsOddParts := by
  simp only [odds, restricted, Finset.mem_filter, mem_univ, true_and, IsOddParts]
  constructor
  · intro h i hi
    exact Nat.not_even_iff_odd.mp (h i hi)
  · intro h i hi
    exact Nat.not_even_iff_odd.mpr (h i hi)

/-- Characterization of `distincts` in terms of `IsDistinctParts`. -/
theorem mem_distincts_iff {n : ℕ} (p : Partition n) : p ∈ distincts n ↔ p.IsDistinctParts := by
  simp only [distincts, Finset.mem_filter, mem_univ, true_and, IsDistinctParts]

/-- The counting function `oddPartsCount` equals the cardinality of the filter. -/
theorem oddPartsCount_eq_filter_card (n : ℕ) :
    oddPartsCount n = ((Finset.univ : Finset (Partition n)).filter IsOddParts).card := by
  simp only [oddPartsCount]
  apply Finset.card_bij (fun p _ => p)
  · intro p hp
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact (mem_odds_iff p).mp hp
  · intro p₁ _ p₂ _ h
    exact h
  · intro p hp
    simp only [Finset.mem_filter, mem_univ, true_and] at hp
    exact ⟨p, (mem_odds_iff p).mpr hp, rfl⟩

/-- The counting function `distinctPartsCount` equals the cardinality of the filter. -/
theorem distinctPartsCount_eq_filter_card (n : ℕ) :
    distinctPartsCount n = ((Finset.univ : Finset (Partition n)).filter IsDistinctParts).card := by
  simp only [distinctPartsCount]
  apply Finset.card_bij (fun p _ => p)
  · intro p hp
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact (mem_distincts_iff p).mp hp
  · intro p₁ _ p₂ _ h
    exact h
  · intro p hp
    simp only [Finset.mem_filter, mem_univ, true_and] at hp
    exact ⟨p, (mem_distincts_iff p).mpr hp, rfl⟩

/-- Euler's odd-distinct identity: the number of partitions of n into odd parts
    equals the number of partitions of n into distinct parts.
    (Theorem \ref{thm.pars.odd-dist-equal})

    This is Theorem 45 from Freek Wiedijk's list of 100 theorems.

    The proof in Mathlib uses Glaisher's theorem, which generalizes this result:
    for any positive integer d, the number of partitions with parts not divisible by d
    equals the number of partitions where no part is repeated d or more times.
    Euler's identity is the special case d = 2.

    The bijective proof (sketched in the module docstring) works by:
    - Merging pairs of equal parts (odd → distinct)
    - Splitting even parts into halves (distinct → odd) -/
theorem odd_eq_distinct (n : ℕ) : (odds n).card = (distincts n).card :=
  card_odds_eq_card_distincts n

/-- Euler's odd-distinct identity in terms of counting functions. -/
theorem oddPartsCount_eq_distinctPartsCount (n : ℕ) : oddPartsCount n = distinctPartsCount n :=
  odd_eq_distinct n

/-- The odd-distinct identity stated with predicates. -/
theorem card_isOddParts_eq_card_isDistinctParts (n : ℕ) :
    ((Finset.univ : Finset (Partition n)).filter IsOddParts).card =
    ((Finset.univ : Finset (Partition n)).filter IsDistinctParts).card := by
  have h1 : (Finset.univ : Finset (Partition n)).filter IsOddParts = odds n := by
    ext p
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact (mem_odds_iff p).symm
  have h2 : (Finset.univ : Finset (Partition n)).filter IsDistinctParts = distincts n := by
    ext p
    simp only [Finset.mem_filter, mem_univ, true_and]
    exact (mem_distincts_iff p).symm
  rw [h1, h2]
  exact odd_eq_distinct n

/-! ### Conjugation / Transposition of partitions -/

/-- The transpose (conjugate) of a partition.
    For a partition λ = (λ₁, λ₂, ..., λₖ), the transpose λᵗ is defined by:
    - The Young diagram of λᵗ is the transpose of the Young diagram of λ
    - Equivalently: (λᵗ)ᵢ = #{j : λⱼ ≥ i}

    The transpose satisfies:
    - |λᵗ| = |λ| (same size)
    - (λᵗ)ᵗ = λ (involution)
    - length(λᵗ) = largest part of λ
    - largest part of λᵗ = length(λ) -/
noncomputable def transpose {n : ℕ} (p : Partition n) : Partition n := by
  -- The transpose has parts: for each i from 1 to (largest part of p),
  -- the i-th part of the transpose is the number of parts of p that are ≥ i
  let largest := p.parts.fold max 0
  let newParts : Multiset ℕ := (Finset.range largest).val.map
    (fun i => (p.parts.filter (· > i)).card)
  refine ⟨newParts.filter (· > 0), ?_, ?_⟩
  · intro i hi
    simp only [Multiset.mem_filter] at hi
    exact hi.2
  · -- Prove sum equals n using double counting
    show (newParts.filter (· > 0)).sum = n
    have h1 : newParts.sum = n := by
      show ((Finset.range largest).val.map (fun i => (p.parts.filter (· > i)).card)).sum = n
      have heq : ((Finset.range largest).val.map (fun i => (p.parts.filter (· > i)).card)).sum =
                 (Finset.range largest).sum (fun i => (p.parts.filter (· > i)).card) := rfl
      rw [heq]
      have hp' : ∀ i ∈ p.parts, 0 < i := fun i hi => p.parts_pos hi
      have := sum_filter_card_eq_sum p.parts hp'
      rw [p.parts_sum] at this
      exact this
    rw [sum_filter_positive newParts]
    exact h1

/-- Helper lemma: for a sorted decreasing list, the count of elements > i is > j iff the j-th element > i.
    This is the key bijection for the Young diagram transpose. -/
lemma sorted_countP_gt_iff {sl : List ℕ} (hsl : sl.Pairwise (· ≥ ·)) (j : ℕ) (hj : j < sl.length)
    (i : ℕ) : sl.countP (· > i) > j ↔ sl[j] > i := by
  -- Helper for sorted lists: earlier elements are larger
  have sorted_ge : ∀ {a b : ℕ} (hab : a ≤ b) (hb : b < sl.length), sl[a]'(Nat.lt_of_le_of_lt hab hb) ≥ sl[b] := by
    intro a b hab hb
    have ha : a < sl.length := Nat.lt_of_le_of_lt hab hb
    by_cases heq : a = b
    · subst heq; rfl
    · have hlt : a < b := Nat.lt_of_le_of_ne hab heq
      rw [List.pairwise_iff_getElem] at hsl
      exact hsl (i := a) (j := b) ha hb hlt
  constructor
  · -- If countP > j, then sl[j] > i
    intro h
    by_contra hle
    push Not at hle
    -- If sl[j] ≤ i, then sl[j], sl[j+1], ... are all ≤ i, so countP ≤ j
    have hcount : sl.countP (· > i) ≤ j := by
      have htake : (sl.take j).countP (· > i) + (sl.drop j).countP (· > i) = sl.countP (· > i) := by
        rw [← List.countP_append, List.take_append_drop]
      have hdrop_zero : (sl.drop j).countP (· > i) = 0 := by
        rw [List.countP_eq_zero]
        intro x hx
        simp only [decide_eq_true_eq, not_lt]
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
        rw [List.getElem_drop]
        have hjk : j ≤ j + k := Nat.le_add_right j k
        have hjkl : j + k < sl.length := by rw [List.length_drop] at hk; omega
        have hge : sl[j] ≥ sl[j + k] := sorted_ge hjk hjkl
        omega
      rw [hdrop_zero, add_zero] at htake
      calc sl.countP (· > i) = (sl.take j).countP (· > i) := htake.symm
        _ ≤ (sl.take j).length := List.countP_le_length
        _ ≤ j := List.length_take_le j sl
    omega
  · -- If sl[j] > i, then sl[0], ..., sl[j] are all > i, so countP ≥ j+1 > j
    intro h
    have htake_all : (sl.take (j + 1)).countP (· > i) = j + 1 := by
      have hlen : (sl.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
      have hall : ∀ x ∈ sl.take (j + 1), x > i := by
        intro x hx
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
        rw [List.length_take] at hk
        have hkj : k ≤ j := by omega
        rw [List.getElem_take]
        have hkl : k < sl.length := by omega
        have hge : sl[k]'hkl ≥ sl[j] := sorted_ge hkj hj
        omega
      have hfilter_eq : (sl.take (j + 1)).filter (· > i) = sl.take (j + 1) := by
        rw [List.filter_eq_self]; intro x hx; simp only [decide_eq_true_eq]; exact hall x hx
      rw [List.countP_eq_length_filter, hfilter_eq, hlen]
    have htake_le : (sl.take (j + 1)).countP (· > i) ≤ sl.countP (· > i) := by
      have heq : sl.take (j + 1) ++ sl.drop (j + 1) = sl := List.take_append_drop (j + 1) sl
      calc (sl.take (j + 1)).countP (· > i)
        ≤ (sl.take (j + 1)).countP (· > i) + (sl.drop (j + 1)).countP (· > i) := Nat.le_add_right _ _
        _ = (sl.take (j + 1) ++ sl.drop (j + 1)).countP (· > i) := by rw [List.countP_append]
        _ = sl.countP (· > i) := by rw [heq]
    omega

/-- The transpose is an involution.

    The proof uses the fundamental property that transposing a Young diagram twice
    gives back the original diagram. For a partition λ = (λ₁, λ₂, ..., λₖ):
    - The transpose λᵗ has parts μⱼ = #{i : λᵢ ≥ j} for j = 1, ..., λ₁
    - Applying transpose again: #{j : μⱼ ≥ i} = λᵢ for all i

    This is because the number of columns of height ≥ i in the Young diagram of λᵗ
    equals the i-th row length of λ. -/
theorem transpose_transpose {n : ℕ} (p : Partition n) : p.transpose.transpose = p := by
  -- We need to show the parts multisets are equal
  apply Partition.ext
  -- Use multiset extensionality: show counts are equal for all k
  rw [Multiset.ext]
  intro k
  -- For k = 0, both counts are 0 (partition parts are positive)
  by_cases hk : k = 0
  · subst hk
    have h1 : Multiset.count 0 p.transpose.transpose.parts = 0 := by
      rw [Multiset.count_eq_zero]
      exact fun hm => (p.transpose.transpose.parts_pos hm).ne rfl
    have h2 : Multiset.count 0 p.parts = 0 := by
      rw [Multiset.count_eq_zero]
      exact fun hm => (p.parts_pos hm).ne rfl
    rw [h1, h2]
  · -- For k > 0, the proof uses the Young diagram involution property.
      -- The key insight is that transpose.transpose.parts = p.parts as multisets.
      -- This follows from the bijection property of Young diagrams.
      push Not at hk
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      -- Set up the sorted list representation
      set sl := p.parts.sort (· ≥ ·) with hsl_def
      have hsl_eq : (sl : Multiset ℕ) = p.parts := Multiset.sort_eq p.parts (· ≥ ·)
      have hsl_sorted : sl.Pairwise (· ≥ ·) := Multiset.pairwise_sort p.parts (· ≥ ·)
      -- The key fact: filter card on sorted list equals countP
      have hfilter_countP : ∀ i, (p.parts.filter (· > i)).card = sl.countP (· > i) := by
        intro i
        conv_lhs => rw [← hsl_eq]
        simp only [Multiset.filter_coe, List.countP_eq_length_filter]
        rfl
      -- Key relationship: sl.length = p.parts.card
      have hsl_len : sl.length = p.parts.card := by
        rw [← Multiset.coe_card, hsl_eq]
      -- Handle empty partition case
      by_cases hparts_empty : p.parts = 0
      · -- If p.parts is empty, both counts are 0
        have h1 : Multiset.count k p.transpose.transpose.parts = 0 := by
          rw [Multiset.count_eq_zero]
          intro hm
          have hsum := p.transpose.transpose.parts_sum
          have hn0 : n = 0 := by
            have := p.parts_sum
            rw [hparts_empty] at this
            simp at this
            exact this.symm
          subst hn0
          -- transpose.transpose.parts.sum = 0
          -- But k ∈ transpose.transpose.parts and k > 0, contradiction
          have hpos := p.transpose.transpose.parts_pos hm
          have hle := Multiset.le_sum_of_mem hm
          omega
        have h2 : Multiset.count k p.parts = 0 := by
          rw [hparts_empty]
          simp
        rw [h1, h2]
      · -- Non-empty partition case
        have hsl_ne : sl ≠ [] := by
          intro heq
          have : (sl : Multiset ℕ) = 0 := by simp [heq]
          rw [hsl_eq] at this
          exact hparts_empty this
        have h0 : 0 < sl.length := by
          rw [List.length_pos_iff_ne_nil]
          exact hsl_ne
        -- Helper for sorted lists: earlier elements are larger
        have sorted_ge : ∀ {a b : ℕ} (hab : a ≤ b) (hb : b < sl.length),
            sl[a]'(Nat.lt_of_le_of_lt hab hb) ≥ sl[b] := by
          intro a b hab hb
          have ha : a < sl.length := Nat.lt_of_le_of_lt hab hb
          by_cases heq : a = b
          · subst heq; rfl
          · have hlt : a < b := Nat.lt_of_le_of_ne hab heq
            rw [List.pairwise_iff_getElem] at hsl_sorted
            exact hsl_sorted (i := a) (j := b) ha hb hlt
        -- Use the fact that transpose.transpose.parts = (sl : Multiset ℕ) = p.parts
        rw [← hsl_eq]
        -- Now we need: count k (transpose.transpose.parts) = count k sl
        -- Key helper: count of i with countP (· > i) > j equals sl[j]
        have h_countP_count : ∀ j (hj : j < sl.length),
            (List.range sl[0]).countP (fun i => sl.countP (· > i) > j) = sl[j] := by
          intro j hj
          -- The condition sl.countP (· > i) > j is equivalent to sl[j] > i
          have heq_iff : ∀ i, (sl.countP (· > i) > j) ↔ (i < sl[j]) := by
            intro i
            have h := sorted_countP_gt_iff hsl_sorted j hj i
            omega
          -- Rewrite the countP using the equivalence
          have hcountP_eq : (List.range sl[0]).countP (fun i => sl.countP (· > i) > j) =
                            (List.range sl[0]).countP (fun i => i < sl[j]) := by
            apply List.countP_congr
            intro i _
            simp only [decide_eq_true_eq]
            exact heq_iff i
          rw [hcountP_eq]
          -- Count of i < sl[j] in [0, sl[0]) is min(sl[j], sl[0]) = sl[j]
          have hle : sl[j] ≤ sl[0] := sorted_ge (Nat.zero_le j) hj
          -- The filter [0, sl[0]) ∩ {i : i < sl[j]} = [0, min(sl[j], sl[0])) = [0, sl[j])
          have hcount_lt : (List.range sl[0]).countP (fun i => i < sl[j]) = sl[j] := by
            rw [List.countP_eq_length_filter]
            have hfilter_eq : (List.range sl[0]).filter (fun i => i < sl[j]) = List.range sl[j] := by
              have key : ∀ i, i ∈ (List.range sl[0]).filter (fun i => i < sl[j]) ↔ i ∈ List.range sl[j] := by
                intro i
                simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
                constructor
                · intro ⟨_, hi⟩; exact hi
                · intro hi; exact ⟨Nat.lt_of_lt_of_le hi hle, hi⟩
              have hnodup1 : ((List.range sl[0]).filter (fun i => i < sl[j])).Nodup := by
                apply List.Nodup.filter
                exact List.nodup_range
              have hnodup2 : (List.range sl[j]).Nodup := List.nodup_range
              have hperm : ((List.range sl[0]).filter (fun i => i < sl[j])).Perm (List.range sl[j]) := by
                rw [List.perm_ext_iff_of_nodup hnodup1 hnodup2]
                exact key
              have hsorted1 : ((List.range sl[0]).filter (fun i => i < sl[j])).Pairwise (· < ·) := by
                apply List.Pairwise.filter
                exact List.pairwise_lt_range
              have hsorted2 : (List.range sl[j]).Pairwise (· < ·) := List.pairwise_lt_range
              exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => (Nat.lt_irrefl _ (Nat.lt_trans h1 h2)).elim)
                hsorted1 hsorted2
            rw [hfilter_eq, List.length_range]
          exact hcount_lt
        -- The key insight: both transpose.transpose.parts and sl have the same sum (= n)
        -- and the same "shape" (constructed from the same data via Young diagram transpose)
        have h_sl_pos : ∀ x ∈ sl, 0 < x := by
          intro x hx
          have : x ∈ (sl : Multiset ℕ) := hx
          rw [hsl_eq] at this
          exact p.parts_pos this
        -- Define the intermediate constructions
        let tp_list := (List.range (sl[0]'h0)).map (fun i => sl.countP (· > i))
        let tp : Multiset ℕ := (↑tp_list : Multiset ℕ).filter (· > 0)
        let tp_largest := tp.fold max 0
        let ttp_list := (List.range tp_largest).map (fun j => (tp.filter (· > j)).card)
        let ttp : Multiset ℕ := (↑ttp_list : Multiset ℕ).filter (· > 0)
        -- Key lemma: fold max 0 equals sup for multisets
        have h_fold_max_eq_sup : ∀ (s : Multiset ℕ), s.fold max 0 = s.sup := by
          intro s
          induction s using Multiset.induction with
          | empty => rfl
          | cons a t ih =>
            simp only [Multiset.fold_cons_left, Multiset.sup_cons, ih]
        -- Show that p.parts.fold max 0 = sl[0] (the largest element)
        have h_largest : p.parts.fold max 0 = sl[0]'h0 := by
          rw [h_fold_max_eq_sup, ← hsl_eq]
          -- (↑sl).sup = sl[0] for non-empty sorted decreasing list
          have hsl_ne' : sl ≠ [] := hsl_ne
          obtain ⟨a, as, hsl_eq'⟩ : ∃ a as, sl = a :: as := List.exists_cons_of_ne_nil hsl_ne'
          simp only [hsl_eq', List.getElem_cons_zero]
          rw [show (↑(a :: as) : Multiset ℕ) = a ::ₘ ↑as from rfl, Multiset.sup_cons]
          have h_all_le : ∀ x ∈ as, x ≤ a := by
            intro x hx
            have hsorted' : (a :: as).Pairwise (· ≥ ·) := hsl_eq' ▸ hsl_sorted
            rw [List.pairwise_cons] at hsorted'
            exact hsorted'.1 x hx
          have h_sup_le : (↑as : Multiset ℕ).sup ≤ a := Multiset.sup_le.mpr (fun x hx => h_all_le x hx)
          exact sup_eq_left.mpr h_sup_le
        -- Show that p.transpose.parts = tp
        have h_tp_eq : p.transpose.parts = tp := by
          unfold transpose
          simp only
          rw [h_largest]
          -- Need to show the multisets are equal
          have hmap_eq : (Finset.range (sl[0]'h0)).val.map
              (fun i => (p.parts.filter (· > i)).card) = ↑tp_list := by
            rw [Finset.range_val]
            -- Multiset.range n = ↑(List.range n) by rfl
            show Multiset.map (fun i => (p.parts.filter (· > i)).card) (Multiset.range (sl[0]'h0)) =
                 ↑(tp_list)
            rw [show Multiset.range (sl[0]'h0) = ↑(List.range (sl[0]'h0)) from rfl]
            rw [Multiset.map_coe]
            congr 1
            apply List.map_congr_left
            intro i _
            exact hfilter_countP i
          rw [hmap_eq]
        -- Establish tp_largest = sl.length
        have h_tp_largest : tp_largest = sl.length := by
          show tp.fold max 0 = sl.length
          have h_countP_0 : sl.countP (· > 0) = sl.length := by
            rw [List.countP_eq_length]
            intro x hx
            simp only [decide_eq_true_eq]
            exact h_sl_pos x hx
          have h0_in_range : 0 ∈ List.range (sl[0]'h0) := by
            rw [List.mem_range]
            exact h_sl_pos (sl[0]'h0) (List.getElem_mem h0)
          have h_len_in_tp_list : sl.length ∈ tp_list := by
            rw [List.mem_map]
            exact ⟨0, h0_in_range, h_countP_0⟩
          have h_len_pos : 0 < sl.length := h0
          have h_len_in_tp : sl.length ∈ tp := by
            rw [Multiset.mem_filter]
            exact ⟨h_len_in_tp_list, h_len_pos⟩
          have h_all_le : ∀ x ∈ tp, x ≤ sl.length := by
            intro x hx
            rw [Multiset.mem_filter] at hx
            obtain ⟨hx_mem, _⟩ := hx
            simp only [Multiset.mem_coe] at hx_mem
            rw [List.mem_map] at hx_mem
            obtain ⟨i, _, hi_eq⟩ := hx_mem
            rw [← hi_eq]
            exact List.countP_le_length
          rw [h_fold_max_eq_sup]
          apply le_antisymm
          · exact Multiset.sup_le.mpr h_all_le
          · exact Multiset.le_sup h_len_in_tp
        -- Key: tp.filter (· > j).card = sl[j] for j < sl.length
        have h_filter_card : ∀ j (hj : j < sl.length), (tp.filter (· > j)).card = sl[j] := by
          intro j hj
          have h_filter_eq : tp.filter (· > j) = (↑tp_list : Multiset ℕ).filter (· > j) := by
            conv_lhs => rw [show tp = (↑tp_list : Multiset ℕ).filter (· > 0) from rfl]
            rw [Multiset.filter_filter]
            congr 1
            ext x
            constructor
            · intro ⟨hxj, _⟩; exact hxj
            · intro hxj; exact ⟨hxj, by omega⟩
          rw [h_filter_eq, Multiset.filter_coe, Multiset.coe_card,
              List.countP_eq_length_filter.symm]
          have heq : tp_list.countP (· > j) =
              (List.range (sl[0]'h0)).countP (fun i => sl.countP (· > i) > j) := by
            rw [show tp_list = (List.range (sl[0]'h0)).map (fun i => sl.countP (· > i)) from rfl]
            rw [List.countP_map]
            rfl
          rw [heq]
          exact h_countP_count j hj
        -- Show ttp_list = sl
        have h_ttp_list_eq : ttp_list = sl := by
          conv_lhs =>
            rw [show ttp_list = (List.range tp_largest).map
                (fun j => (tp.filter (· > j)).card) from rfl]
          rw [h_tp_largest]
          apply List.ext_getElem
          · simp [List.length_map, List.length_range]
          · intro i h1 h2
            simp only [List.length_map, List.length_range] at h1
            simp only [List.getElem_map, List.getElem_range]
            exact h_filter_card i h1
        -- Show ttp = ↑sl
        have h_ttp_eq : ttp = ↑sl := by
          conv_lhs => rw [show ttp = (↑ttp_list : Multiset ℕ).filter (· > 0) from rfl]
          rw [h_ttp_list_eq, Multiset.filter_coe]
          have h_filter_sl : sl.filter (· > 0) = sl := by
            rw [List.filter_eq_self]
            intro x hx
            simp only [decide_eq_true_eq]
            exact h_sl_pos x hx
          rw [h_filter_sl]
        -- Show p.transpose.transpose.parts = ttp
        have h_ttp_parts : p.transpose.transpose.parts = ttp := by
          -- Use the fact that p.transpose.parts = tp
          conv_lhs => rw [show p.transpose.transpose = 
              ⟨(Finset.range (p.transpose.parts.fold max 0)).val.map
                (fun i => (p.transpose.parts.filter (· > i)).card) |>.filter (· > 0), 
               p.transpose.transpose.parts_pos, p.transpose.transpose.parts_sum⟩ from rfl]
          simp only
          rw [h_tp_eq]
          rw [Finset.range_val]
          rw [show Multiset.range tp_largest = ↑(List.range tp_largest) from rfl]
          rw [Multiset.map_coe]
        -- Final step: count k in both multisets
        rw [h_ttp_parts, h_ttp_eq]

/-- The transpose preserves size. -/
theorem transpose_size {n : ℕ} (p : Partition n) : p.transpose.parts.sum = n :=
  p.transpose.parts_sum

/-- Helper: fold max 0 is bounded by all elements -/
private lemma fold_max_le_of_all_le (s : Multiset ℕ) (i : ℕ) (h : ∀ x ∈ s, x ≤ i) :
    s.fold max 0 ≤ i := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.fold_cons_left]
    have ha : a ≤ i := h a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ≤ i := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    exact max_le ha (ih hs)

/-- Key lemma: for i < largest, the filter count is positive -/
lemma filter_card_pos_of_lt_largest {n : ℕ} (p : Partition n) (i : ℕ)
    (hi : i < p.parts.fold max 0) : 0 < (p.parts.filter (· > i)).card := by
  have h : ∃ x ∈ p.parts, x > i := by
    by_contra hc
    push Not at hc
    have hmax : p.parts.fold max 0 ≤ i := fold_max_le_of_all_le p.parts i hc
    omega
  obtain ⟨x, hx_mem, hx_gt⟩ := h
  rw [Multiset.card_pos]
  intro heq
  have : x ∈ p.parts.filter (· > i) := Multiset.mem_filter.mpr ⟨hx_mem, hx_gt⟩
  simp [heq] at this

/-- The length of the transpose equals the largest part of the original partition. -/
theorem transpose_length_eq_largestPart {n : ℕ} (p : Partition n) :
    p.transpose.numParts = p.largestPart := by
  unfold transpose numParts largestPart
  simp only
  set largest := p.parts.fold max 0 with h_largest
  set newParts := Multiset.map (fun i => (p.parts.filter (· > i)).card) (range largest).val
  have hall_pos : ∀ x ∈ newParts, x > 0 := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.range_val, Multiset.mem_range] at hi
    exact filter_card_pos_of_lt_largest p i (h_largest ▸ hi)
  have hfilter_eq : newParts.filter (· > 0) = newParts := by
    rw [Multiset.filter_eq_self]
    exact hall_pos
  rw [hfilter_eq]
  rw [Multiset.card_map, Finset.range_val, Multiset.card_range]

-- Lemma: fold max over a multiset is the sup
private lemma fold_max_eq_sup (s : Multiset ℕ) : s.fold max 0 = s.sup := by
  induction s using Multiset.induction with
  | empty => rfl
  | cons a s ih =>
    simp only [Multiset.fold_cons_left, Multiset.sup_cons, ih]

-- If all parts are positive and fold max 0 = 0, then the multiset is empty
private lemma parts_empty_of_fold_max_zero {n : ℕ} (p : Partition n) (h : p.parts.fold max 0 = 0) :
    p.parts = 0 := by
  rw [fold_max_eq_sup] at h
  by_contra hne
  have hne' : p.parts.card ≠ 0 := fun h => hne (Multiset.card_eq_zero.mp h)
  rw [← Nat.pos_iff_ne_zero] at hne'
  have ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hne'
  have hle : x ≤ p.parts.sup := Multiset.le_sup hx
  have hpos := p.parts_pos hx
  omega

-- Key lemma: filtering positive elements preserves cardinality for partition parts
lemma filter_gt_zero_card_eq {n : ℕ} (p : Partition n) :
    (p.parts.filter (· > 0)).card = p.parts.card := by
  congr 1
  ext x
  simp only [Multiset.count_filter, gt_iff_lt, Nat.pos_iff_ne_zero, ite_eq_left_iff, not_not]
  intro hx
  subst hx
  rw [eq_comm, Multiset.count_eq_zero]
  exact fun h => (p.parts_pos h).ne rfl

/-- The largest part of the transpose equals the length of the original partition. -/
theorem transpose_largestPart_eq_length {n : ℕ} (p : Partition n) :
    p.transpose.largestPart = p.numParts := by
  unfold transpose largestPart numParts
  simp only
  by_cases hn : p.parts.fold max 0 = 0
  · -- Case: largest part is 0 (empty partition)
    have h_empty := parts_empty_of_fold_max_zero p hn
    simp only [h_empty, Multiset.card_zero]
    rfl
  · -- Case: largest part > 0
    push Not at hn
    have hpos : 0 < p.parts.fold max 0 := Nat.pos_of_ne_zero hn
    have h_first : (p.parts.filter (· > 0)).card = p.parts.card := filter_gt_zero_card_eq p

    set largest := p.parts.fold max 0 with hlarg
    set newParts := (Finset.range largest).val.map
        (fun i => (p.parts.filter (· > i)).card) with hnewParts

    -- The newParts multiset contains p.parts.card at position 0
    have h_mem_card : p.parts.card ∈ newParts := by
      rw [hnewParts, Multiset.mem_map]
      use 0
      constructor
      · exact Multiset.mem_range.mpr hpos
      · exact h_first

    -- All elements are ≤ p.parts.card
    have h_all_le : ∀ x ∈ newParts, x ≤ p.parts.card := by
      intro x hx
      rw [hnewParts, Multiset.mem_map] at hx
      obtain ⟨i, _, hi_eq⟩ := hx
      rw [← hi_eq]
      apply Multiset.card_le_card
      exact Multiset.filter_le (· > i) p.parts

    -- Determine if p.parts.card > 0 or = 0
    have h_card_pos_or_zero : p.parts.card > 0 ∨ p.parts.card = 0 := by omega
    rcases h_card_pos_or_zero with h_card_pos | h_card_zero
    · -- p.parts.card > 0, so it passes the filter
      have h_mem_filtered : p.parts.card ∈ newParts.filter (· > 0) := by
        rw [Multiset.mem_filter]
        exact ⟨h_mem_card, h_card_pos⟩

      -- The max of a set containing p.parts.card where all elements ≤ p.parts.card is p.parts.card
      rw [fold_max_eq_sup]
      apply le_antisymm
      · rw [Multiset.sup_le]
        intro x hx
        rw [Multiset.mem_filter] at hx
        exact h_all_le x hx.1
      · exact Multiset.le_sup h_mem_filtered
    · -- p.parts.card = 0, but then parts is empty, contradicting hpos
      have h_parts_empty : p.parts = 0 := Multiset.card_eq_zero.mp h_card_zero
      rw [h_parts_empty, Multiset.fold_zero] at hlarg
      omega

/-- The number of partitions of n into k parts equals the number of partitions
    of n whose largest part is k.
    (Proposition \ref{prop.pars.pkn=dual})

    This follows from the fact that transpose is a bijection that swaps
    "number of parts" with "largest part". -/
theorem partsCount_eq_largestPartCount (n k : ℕ) :
    partsCount k n =
    ((Finset.univ : Finset (Partition n)).filter (fun p => p.largestPart = k)).card := by
  -- Use transpose as a bijection between:
  -- - partitions with k parts
  -- - partitions with largest part k
  apply Finset.card_bij (fun p _ => p.transpose)
  · -- Membership: transpose sends "k parts" to "largest part k"
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [transpose_largestPart_eq_length]
    exact hp
  · -- Injectivity: follows from transpose being an involution
    intro p₁ hp₁ p₂ hp₂ heq
    have h1 := congrArg transpose heq
    simp only [transpose_transpose] at h1
    exact h1
  · -- Surjectivity: every partition with largest part k is the transpose of some partition with k parts
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    use q.transpose
    refine ⟨?_, transpose_transpose q⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- Need: q.transpose.parts.card = k
    -- We have: q.largestPart = k
    -- By transpose_length_eq_largestPart: q.transpose.numParts = q.largestPart
    have h := transpose_length_eq_largestPart q
    unfold numParts at h
    rw [h, hq]

/-- Corollary: `p_0(n) + p_1(n) + ... + p_k(n)` equals the number of partitions
    of n whose largest part is ≤ k.
    (Corollary \ref{cor.pars.p0kn=dual}) -/
theorem partsCount_sum_eq_largestPartLeq (n k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), partsCount i n =
    ((Finset.univ : Finset (Partition n)).filter (fun p => p.largestPart ≤ k)).card := by
  conv_lhs =>
    congr
    · skip
    · ext i
      rw [partsCount_eq_largestPartCount]
  rw [sum_card_fiberwise_eq_card_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_range]
  omega

/-- The sum `p_0(n) + p_1(n) + ... + p_m(n)` equals the count of partitions with all parts ≤ m.

    This combines Corollary \ref{cor.pars.p0kn=dual} (sum equals count with largest part ≤ m)
    with the equivalence "largest part ≤ m" ↔ "all parts ≤ m" from `filter_largestPart_le_eq_restricted`. -/
theorem partsCount_sum_eq_partsLeqCount (n m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), partsCount k n = partsLeqCount m n := by
  rw [partsCount_sum_eq_largestPartLeq, filter_largestPart_le_eq_restricted]
  rfl

section GenFun2

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [T2Space R] [IsTopologicalSemiring R]

/-- The generating function for the sum `p_0(n) + p_1(n) + ... + p_m(n)`:
    `∑_{n≥0} (p_0(n) + p_1(n) + ... + p_m(n)) x^n = ∏_{k=1}^m 1/(1-x^k)`.
    (Theorem \ref{thm.pars.main-gf-0n})

    The proof uses three key facts:
    1. **Corollary \ref{cor.pars.p0kn=dual}**: `p_0(n) + p_1(n) + ... + p_m(n)` equals the number of
       partitions of n with largest part ≤ m.
    2. **Equivalence**: "largest part ≤ m" is equivalent to "all parts ≤ m"
       (this is obvious from the definition of largest part as the maximum).
    3. **Theorem \ref{thm.pars.main-gf-parts-n}**: The generating function for partitions
       with all parts ≤ m is `∏_{k=1}^m 1/(1-x^k)`.

    The product `∏_{k=1}^m 1/(1-x^k)` is represented here as `∏_{k=0}^{m-1} (∑_{j≥0} x^{(k+1)j})`
    since the geometric series `1/(1-x^k) = ∑_{j≥0} x^{kj}` converges in the power series topology. -/
theorem partsCountSum_genFun (m : ℕ) :
    PowerSeries.mk (fun n => (∑ k ∈ range (m + 1), partsCount k n : R)) =
    ∏ k ∈ range m, (∑' j : ℕ, (X : R⟦X⟧) ^ ((k + 1) * j)) := by
  rw [partitionCount_genFun_partsLeq_finprod]
  ext n
  simp only [coeff_mk]
  have h := partsCount_sum_eq_partsLeqCount n m
  simp only [partsLeqCount] at h
  simp only [← h, Nat.cast_sum]

end GenFun2

/-! ### Counting partitions by parts and largest part -/

/-- The count of partitions with exactly k parts and largest part ℓ, for a specific size n. -/
def partsAndLargestCount (k ℓ n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Partition n)).filter
    (fun p => p.numParts = k ∧ p.largestPart = ℓ)).card

/-- The total count of partitions with exactly k parts and largest part ℓ (summed over all sizes).
    The size ranges from k (minimum, when all parts are 1 except the largest) to k*ℓ (maximum,
    when all parts equal ℓ). -/
def partsAndLargestCountTotal (k ℓ : ℕ) : ℕ :=
  ∑ n ∈ Finset.Icc k (k * ℓ), partsAndLargestCount k ℓ n

/-! #### Helper lemmas for the bijection

The following lemmas provide infrastructure for the bijection proof in `partsAndLargestCountTotal_eq`.
They establish key properties of the forward map (Sym → Partition):
- `symToPartsMultiset`: constructs partition parts from a Sym
- `symToPartsMultiset_pos`: all parts are positive
- `symToPartsMultiset_card`: cardinality is k
- `symToPartsMultiset_fold_max`: largest part is ℓ
- `symToPartsMultiset_erase`: erasing ℓ recovers the Sym elements
- `symToPartsMultiset_sum_range`: sum lies in the valid range [k, k*ℓ]

The backward map (Partition → Sym) uses `Multiset.pmap` to map each part x in
`p.parts.erase ℓ` to `⟨x - 1, ...⟩ : Fin ℓ`, which is valid since all such parts
are in {1, ..., ℓ}.

The `Equiv` construction is completed in `partsAndLargestCountTotal_eq` using
`Equiv.ofBijective` with `toSigma_injective` and `toSigma_surj`. -/

/-- For a multiset m, all elements are ≤ fold max 0 m. -/
private lemma multiset_le_fold_max {m : Multiset ℕ} : ∀ x ∈ m, x ≤ m.fold max 0 := by
  intro x hx
  induction m using Multiset.induction with
  | empty => simp at hx
  | cons a m' ih =>
    rw [Multiset.mem_cons] at hx
    simp only [Multiset.fold_cons_left]
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

/-- If a multiset is nonempty, then fold max 0 is in the multiset. -/
private lemma fold_max_mem_of_nonempty {m : Multiset ℕ} (h : m ≠ 0) :
    m.fold max 0 ∈ m := by
  induction m using Multiset.induction with
  | empty => contradiction
  | cons a m' ih =>
    simp only [Multiset.fold_cons_left, Multiset.mem_cons]
    by_cases hm' : m' = 0
    · simp [hm']
    · by_cases ha : a ≥ m'.fold max 0
      · left; exact max_eq_left ha
      · push Not at ha
        right
        rw [max_eq_right (le_of_lt ha)]
        exact ih hm'

variable {n : ℕ} in
/-- The multiset ℓ ::ₘ (s.val.map (fun x => x.val + 1)) for a Sym (Fin ℓ) n. -/
private def symToPartsMultiset (ℓ : ℕ) (s : Sym (Fin ℓ) n) : Multiset ℕ :=
  ℓ ::ₘ (s.val.map (fun x => x.val + 1))

variable {n : ℕ} in
/-- All parts in symToPartsMultiset are positive. -/
lemma symToPartsMultiset_pos (ℓ : ℕ) (hℓ : ℓ ≥ 1) (s : Sym (Fin ℓ) n) :
    ∀ x ∈ symToPartsMultiset ℓ s, 0 < x := by
  intro x hx
  simp only [symToPartsMultiset, Multiset.mem_cons, Multiset.mem_map] at hx
  rcases hx with rfl | ⟨a, _, rfl⟩
  · exact hℓ
  · omega

variable {n : ℕ} in
/-- The cardinality of symToPartsMultiset is n + 1. -/
lemma symToPartsMultiset_card (ℓ : ℕ) (s : Sym (Fin ℓ) n) :
    (symToPartsMultiset ℓ s).card = n + 1 := by
  simp [symToPartsMultiset, Multiset.card_cons, Multiset.card_map]

variable {n : ℕ} in
/-- The largest part (fold max 0) of symToPartsMultiset is ℓ. -/
lemma symToPartsMultiset_fold_max (ℓ : ℕ) (s : Sym (Fin ℓ) n) :
    (symToPartsMultiset ℓ s).fold max 0 = ℓ := by
  simp only [symToPartsMultiset, Multiset.fold_cons_left]
  have h : (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).fold max 0 ≤ ℓ := by
    induction s.val using Multiset.induction with
    | empty => simp
    | cons a m ih =>
      simp only [Multiset.map_cons, Multiset.fold_cons_left]
      have ha : a.val + 1 ≤ ℓ := by omega
      omega
  omega

variable {n : ℕ} in
/-- Erasing ℓ from symToPartsMultiset recovers the mapped parts. -/
lemma symToPartsMultiset_erase (ℓ : ℕ) (s : Sym (Fin ℓ) n) :
    (symToPartsMultiset ℓ s).erase ℓ = s.val.map (fun x => x.val + 1) := by
  simp [symToPartsMultiset, Multiset.erase_cons_head]

/-- The sum of symToPartsMultiset lies in [k, k*ℓ] for s : Sym (Fin ℓ) (k-1). -/
lemma symToPartsMultiset_sum_range (k ℓ : ℕ) (hk : k ≥ 1) (hℓ : ℓ ≥ 1)
    (s : Sym (Fin ℓ) (k - 1)) : (symToPartsMultiset ℓ s).sum ∈ Finset.Icc k (k * ℓ) := by
  simp only [symToPartsMultiset, Multiset.sum_cons, Finset.mem_Icc]
  constructor
  · -- Lower bound: each part is at least 1, so sum of k-1 parts is at least k-1
    have h1 : (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).sum ≥ k - 1 := by
      have hcard : (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).card = k - 1 := by simp
      have hpos : ∀ x ∈ Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val, 1 ≤ x := by simp
      have := Multiset.card_nsmul_le_sum hpos
      simp only [smul_eq_mul, mul_one, hcard] at this
      exact this
    omega
  · -- Upper bound: each part is at most ℓ
    have h2 : (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).sum ≤ (k - 1) * ℓ := by
      have hbound : ∀ x ∈ Multiset.map (fun (x : Fin ℓ) => x.val + 1) (s : Multiset (Fin ℓ)),
          x ≤ ℓ := by
        intro x hx
        simp only [Multiset.mem_map] at hx
        obtain ⟨a, _, rfl⟩ := hx
        omega
      have := Multiset.sum_le_card_nsmul _ _ hbound
      simp only [smul_eq_mul] at this
      calc (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).sum
          ≤ (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).card * ℓ := this
        _ = (k - 1) * ℓ := by simp
    have h3 : ℓ + (k - 1) * ℓ = k * ℓ := by
      cases k with
      | zero => omega
      | succ k' => simp; ring
    omega

/-- Proposition \ref{prop.pars.qbinom.intro-count-binom}: For positive integers k and ℓ,
    the number of partitions with exactly k parts and largest part ℓ equals C(k+ℓ-2, k-1).

    **Proof outline**: A partition with k parts and largest part ℓ has the form
    (ℓ, λ₂, ..., λₖ) where ℓ ≥ λ₂ ≥ ... ≥ λₖ ≥ 1.

    The tuple (λ₂, ..., λₖ) is a weakly decreasing sequence of k-1 positive integers,
    each at most ℓ. This is equivalent to choosing a (k-1)-element multisubset
    of {1, 2, ..., ℓ}, which by the "stars and bars" formula equals
    C(ℓ + (k-1) - 1, k-1) = C(k + ℓ - 2, k - 1).

    Note: This formula is independent of the size n of the partition.

    **Bijection details**:
    - Forward: partition (ℓ, λ₂, ..., λₖ) ↦ multiset {λ₂-1, ..., λₖ-1} ⊆ Fin ℓ
    - Backward: multiset {a₁, ..., aₖ₋₁} ⊆ Fin ℓ ↦ partition (ℓ, a₁+1, ..., aₖ₋₁+1) sorted

    This is well-defined because:
    1. Each λᵢ ∈ {1, ..., ℓ}, so λᵢ - 1 ∈ {0, ..., ℓ-1} = Fin ℓ
    2. Each aᵢ ∈ Fin ℓ gives aᵢ + 1 ∈ {1, ..., ℓ}
    3. The resulting partition has largest part ℓ (which is explicitly the first part)
    4. The partition has k parts (one ℓ, plus k-1 from the multiset) -/
theorem partsAndLargestCountTotal_eq (k ℓ : ℕ) (hk : k ≥ 1) (hℓ : ℓ ≥ 1) :
    partsAndLargestCountTotal k ℓ = (k + ℓ - 2).choose (k - 1) := by
  -- The proof uses a bijection with Sym (Fin ℓ) (k-1), whose cardinality is
  -- C(ℓ + (k-1) - 1, k-1) = C(k + ℓ - 2, k - 1) by Sym.card_sym_eq_choose.
  --
  -- The bijection maps:
  -- - A partition (ℓ, λ₂, ..., λₖ) to the multiset {λ₂-1, ..., λₖ-1} ⊆ Fin ℓ
  -- - A multiset {a₁, ..., aₖ₋₁} ⊆ Fin ℓ to the partition (ℓ, a₁+1, ..., aₖ₋₁+1) sorted
  --
  -- This is well-defined because:
  -- 1. Each λᵢ ∈ {1, ..., ℓ}, so λᵢ - 1 ∈ {0, ..., ℓ-1} = Fin ℓ
  -- 2. Each aᵢ ∈ Fin ℓ gives aᵢ + 1 ∈ {1, ..., ℓ}
  -- 3. The resulting partition has largest part ℓ (which is explicitly the first part)
  -- 4. The partition has k parts (one ℓ, plus k-1 from the multiset)

  -- Define the sigma type of partitions with k parts and largest ℓ
  let PartsAndLargestSigma := 
    (n : Finset.Icc k (k * ℓ)) × { p : Partition n // numParts p = k ∧ largestPart p = ℓ }

  -- Step 1: partsAndLargestCountTotal equals the cardinality of this sigma type
  have h_sigma : Fintype.card PartsAndLargestSigma = partsAndLargestCountTotal k ℓ := by
    simp only [PartsAndLargestSigma, partsAndLargestCountTotal, partsAndLargestCount]
    rw [Fintype.card_sigma]
    simp only [Fintype.card_subtype]
    convert Finset.sum_coe_sort (Finset.Icc k (k * ℓ)) _ using 2
    rfl

  -- Step 2: The RHS equals the cardinality of Sym (Fin ℓ) (k-1)
  have h_sym : (k + ℓ - 2).choose (k - 1) = Fintype.card (Sym (Fin ℓ) (k - 1)) := by
    rw [Sym.card_sym_eq_choose, Fintype.card_fin]
    congr 1
    omega

  -- Step 3: Show the two types have the same cardinality via the bijection
  rw [← h_sigma, h_sym]
  apply Fintype.card_congr
  
  -- The bijection between PartsAndLargestSigma and Sym (Fin ℓ) (k-1):
  -- Forward: Sym (Fin ℓ) (k-1) → PartsAndLargestSigma
  --   s ↦ (⟨n, _⟩, ⟨p, _⟩) where:
  --   - n = ℓ + (s.val.map (·.val + 1)).sum (the partition sum)
  --   - p = Partition.ofSums n (ℓ ::ₘ s.val.map (·.val + 1))
  --   - numParts p = k (since there's one ℓ plus k-1 parts from s)
  --   - largestPart p = ℓ (since all parts from s are ≤ ℓ)
  --
  -- Backward: PartsAndLargestSigma → Sym (Fin ℓ) (k-1)
  --   (n, p) ↦ (p.parts.erase ℓ).pmap (fun x _ => ⟨x - 1, _⟩)
  --   - Erasing ℓ gives k-1 parts
  --   - Each part x satisfies 1 ≤ x ≤ ℓ, so x - 1 ∈ Fin ℓ
  --
  -- The proof that these are inverses follows from:
  -- - (ℓ ::ₘ m).erase ℓ = m for any multiset m
  -- - For a : Fin ℓ, ⟨(a.val + 1) - 1, _⟩ = a
  -- - The partition sum and numParts/largestPart properties
  
  -- Define the forward map
  let symToPartitionSum (s : Sym (Fin ℓ) (k - 1)) : ℕ := 
    (symToPartsMultiset ℓ s).sum
  
  have symToPartitionSum_range (s : Sym (Fin ℓ) (k - 1)) : 
      symToPartitionSum s ∈ Finset.Icc k (k * ℓ) := 
    symToPartsMultiset_sum_range k ℓ hk hℓ s
  
  let symToPartitionParts (s : Sym (Fin ℓ) (k - 1)) : Multiset ℕ := 
    symToPartsMultiset ℓ s
  
  have symToPartitionParts_sum (s : Sym (Fin ℓ) (k - 1)) : 
      (symToPartitionParts s).sum = symToPartitionSum s := rfl
  
  let symToPartitionVal (s : Sym (Fin ℓ) (k - 1)) : Partition (symToPartitionSum s) := 
    Partition.ofSums _ (symToPartitionParts s) (symToPartitionParts_sum s)
  
  have symToPartitionVal_parts (s : Sym (Fin ℓ) (k - 1)) : 
      (symToPartitionVal s).parts = symToPartitionParts s := by
    simp only [symToPartitionVal, symToPartitionParts, Partition.ofSums_parts]
    ext x
    simp only [Multiset.count_filter, symToPartsMultiset]
    split_ifs with h
    · rfl
    · push Not at h
      subst h
      symm
      rw [Multiset.count_eq_zero]
      intro hx
      have := symToPartsMultiset_pos ℓ hℓ s 0 hx
      omega
  
  have symToPartitionVal_numParts (s : Sym (Fin ℓ) (k - 1)) : 
      numParts (symToPartitionVal s) = k := by
    simp only [numParts, symToPartitionVal_parts, symToPartitionParts, symToPartsMultiset,
      Multiset.card_cons, Multiset.card_map]
    have := s.prop
    omega
  
  have symToPartitionVal_largestPart (s : Sym (Fin ℓ) (k - 1)) : 
      largestPart (symToPartitionVal s) = ℓ := by
    simp only [largestPart, symToPartitionVal_parts, symToPartitionParts, symToPartsMultiset,
      Multiset.fold_cons_left]
    have h : (Multiset.map (fun (x : Fin ℓ) => x.val + 1) s.val).fold max 0 ≤ ℓ := by
      induction s.val using Multiset.induction with
      | empty => simp
      | cons a m ih =>
        simp only [Multiset.map_cons, Multiset.fold_cons_left]
        have ha : a.val + 1 ≤ ℓ := by omega
        omega
    omega
  
  -- Define the forward map as a function to PartsAndLargestSigma
  let toSigma (s : Sym (Fin ℓ) (k - 1)) : PartsAndLargestSigma := 
    ⟨⟨symToPartitionSum s, symToPartitionSum_range s⟩, 
     ⟨symToPartitionVal s, symToPartitionVal_numParts s, symToPartitionVal_largestPart s⟩⟩
  
  -- Helper for HEq handling
  have parts_eq_of_heq : ∀ {n m : ℕ} (h : n = m) 
      {x : { p : Partition n // numParts p = k ∧ largestPart p = ℓ }} 
      {y : { p : Partition m // numParts p = k ∧ largestPart p = ℓ }},
      HEq x y → x.val.parts = y.val.parts := by
    intro n m h x y hxy
    subst h
    simp only [heq_eq_eq] at hxy
    rw [hxy]
  
  -- Prove injectivity
  have toSigma_injective : Function.Injective toSigma := by
    intro s t hst
    -- Extract the equality of first components and HEq of second components
    have hn : symToPartitionSum s = symToPartitionSum t := by
      have := congrArg (fun x => x.1.val) hst
      exact this
    have hp : HEq (toSigma s).2 (toSigma t).2 := Sigma.mk.inj hst |>.2
    -- From hn, we get that the multiset sums are equal
    have hsum : (symToPartsMultiset ℓ s).sum = (symToPartsMultiset ℓ t).sum := hn
    -- Use hn to convert hp from HEq to Eq
    have hmultiset : s.val.map (fun x => x.val + 1) = t.val.map (fun x => x.val + 1) := by
      have hparts : (symToPartitionVal s).parts = (symToPartitionVal t).parts := 
        parts_eq_of_heq hn hp
      rw [symToPartitionVal_parts, symToPartitionVal_parts] at hparts
      simp only [symToPartitionParts, symToPartsMultiset, Multiset.cons_inj_right] at hparts
      exact hparts
    -- The map x ↦ x.val + 1 is injective on Fin ℓ
    ext a
    have : s.val.count a = t.val.count a := by
      have := congrArg (Multiset.count (a.val + 1)) hmultiset
      simp only [Multiset.count_map_eq_count' (fun x : Fin ℓ => x.val + 1) _ 
        (fun x y h => by simp only [add_left_inj] at h; exact Fin.ext h)] at this
      exact this
    exact this
  
  -- Since both types are finite and toSigma is injective, 
  -- we can construct an equivalence by showing toSigma is surjective.
  -- We prove surjectivity by constructing an explicit right inverse.
  
  -- Helper lemmas for the backward map
  have fold_max_mem : ∀ (m : Multiset ℕ), m ≠ 0 → m.fold max 0 ∈ m := by
    intro m hm
    induction m using Multiset.induction with
    | empty => simp at hm
    | cons a m ih =>
      simp only [Multiset.fold_cons_left]
      by_cases hm' : m = 0
      · simp [hm']
      · by_cases ha : a ≥ m.fold max 0
        · simp [max_eq_left ha]
        · push Not at ha
          simp only [max_eq_right (le_of_lt ha)]
          exact Multiset.mem_cons_of_mem (ih hm')
  
  have le_fold_max : ∀ (m : Multiset ℕ) (x : ℕ), x ∈ m → x ≤ m.fold max 0 := by
    intro m x hx
    induction m using Multiset.induction with
    | empty => simp at hx
    | cons a m ih =>
      simp only [Multiset.mem_cons] at hx
      simp only [Multiset.fold_cons_left]
      obtain rfl | hx := hx
      · exact le_max_left x (m.fold max 0)
      · exact le_trans (ih hx) (le_max_right a (m.fold max 0))
  
  -- Define the backward map
  let fromSigma (x : PartsAndLargestSigma) : Sym (Fin ℓ) (k - 1) := by
    obtain ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩ := x
    -- p.parts has k parts, largest is ℓ
    -- After erasing ℓ, we have k-1 parts, each in {1, ..., ℓ}
    have hp_card : p.parts.card = k := hp_numParts
    have hp_max : p.parts.fold max 0 = ℓ := hp_largestPart
    have h_nonempty : p.parts ≠ 0 := by
      simp only [← Multiset.card_pos, hp_card]
      omega
    have h_ell_mem : ℓ ∈ p.parts := by
      have := fold_max_mem p.parts h_nonempty
      simp only [hp_max] at this
      exact this
    let erased := p.parts.erase ℓ
    have h_erased_card : erased.card = k - 1 := by
      simp only [erased, Multiset.card_erase_of_mem h_ell_mem, hp_card]
      rfl
    have h_erased_bound : ∀ y ∈ erased, 1 ≤ y ∧ y ≤ ℓ := by
      intro y hy
      have hy_mem : y ∈ p.parts := Multiset.mem_of_mem_erase hy
      constructor
      · exact p.parts_pos hy_mem
      · have := le_fold_max p.parts y hy_mem
        simp only [hp_max] at this
        exact this
    exact ⟨erased.pmap (fun y hy => ⟨y - 1, by have := h_erased_bound y hy; omega⟩) 
           (fun y hy => hy), by simp [Multiset.card_pmap, h_erased_card]⟩
  
  -- Prove that fromSigma is a right inverse of toSigma (i.e., toSigma ∘ fromSigma = id)
  -- This makes toSigma surjective
  -- 
  -- The proof outline:
  -- 1. For any x = ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩ ∈ PartsAndLargestSigma
  -- 2. fromSigma x constructs a Sym by erasing ℓ from p.parts and mapping y ↦ y-1
  -- 3. toSigma (fromSigma x) constructs a partition with parts ℓ ::ₘ (map (·+1) ...)
  -- 4. The key is that map (·+1) ∘ map (·-1) = id on positive integers
  -- 5. So the parts are ℓ ::ₘ (p.parts.erase ℓ) = p.parts (by Multiset.cons_erase)
  -- 6. Therefore the sum and partition match
  have toSigma_surj : Function.Surjective toSigma := by
    intro x
    use fromSigma x
    -- The round-trip proof requires showing that:
    -- 1. The sum (symToPartitionSum (fromSigma x)) equals n
    -- 2. The partition (symToPartitionVal (fromSigma x)) equals p
    -- Both follow from: map (·+1) ∘ pmap (·-1) = id on positive integers
    -- and Multiset.cons_erase: ℓ ::ₘ (p.parts.erase ℓ) = p.parts
    
    -- Extract components of x
    obtain ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩ := x
    
    -- Establish key properties of p
    have hp_card : p.parts.card = k := hp_numParts
    have hp_max : p.parts.fold max 0 = ℓ := hp_largestPart
    have h_nonempty : p.parts ≠ 0 := by
      simp only [← Multiset.card_pos, hp_card]
      omega
    have h_ell_mem : ℓ ∈ p.parts := by
      have := fold_max_mem p.parts h_nonempty
      simp only [hp_max] at this
      exact this
    have h_erased_bound : ∀ y ∈ p.parts.erase ℓ, 1 ≤ y ∧ y ≤ ℓ := by
      intro y hy
      have hy_mem : y ∈ p.parts := Multiset.mem_of_mem_erase hy
      constructor
      · exact p.parts_pos hy_mem
      · have := le_fold_max p.parts y hy_mem
        simp only [hp_max] at this
        exact this
    
    -- Key lemma: pmap (·-1) followed by map (·+1) is identity
    have pmap_map_id : ∀ (m : Multiset ℕ) (hm : ∀ y ∈ m, 1 ≤ y ∧ y ≤ ℓ),
        (m.pmap (fun y (hy : y ∈ m) => (⟨y - 1, by have := hm y hy; omega⟩ : Fin ℓ)) 
         (fun y hy => hy)).map (fun x => x.val + 1) = m := by
      intro m hm
      rw [Multiset.map_pmap]
      have eq1 : m.pmap (fun y (hy : y ∈ m) => 
          (⟨y - 1, by have := hm y hy; omega⟩ : Fin ℓ).val + 1) 
          (fun y hy => hy) = 
          m.pmap (fun y _ => y) (fun y hy => hy) := by
        apply Multiset.pmap_congr m
        intro y hy
        have hbound := hm y hy
        have : (⟨y - 1, by have := hm y hy; omega⟩ : Fin ℓ).val = y - 1 := rfl
        omega
      rw [eq1]
      rw [Multiset.pmap_eq_map_attach]
      simp
    
    -- Show that symToPartsMultiset of fromSigma x equals p.parts
    have h_parts_eq : symToPartsMultiset ℓ (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩) = 
        p.parts := by
      simp only [fromSigma, symToPartsMultiset]
      rw [pmap_map_id (p.parts.erase ℓ) h_erased_bound]
      exact Multiset.cons_erase h_ell_mem
    
    -- From h_parts_eq, derive the sum equality
    have h_sum_eq : symToPartitionSum (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩) = n := by
      simp only [symToPartitionSum]
      rw [h_parts_eq]
      exact p.parts_sum
    
    -- Show the sigma type equality
    simp only [toSigma]
    -- We need to show the two sigma elements are equal
    -- First component: ⟨symToPartitionSum (fromSigma x), _⟩ = ⟨n, hn⟩
    -- Second component: ⟨symToPartitionVal (fromSigma x), _, _⟩ = ⟨p, hp_numParts, hp_largestPart⟩
    
    -- Show the partitions have equal parts
    have h_parts' : (symToPartitionVal (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩)).parts = 
        p.parts := by
      rw [symToPartitionVal_parts]
      exact h_parts_eq
    
    -- First component equality
    have h_first : (⟨symToPartitionSum (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩), 
        symToPartitionSum_range (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩)⟩ : 
        Finset.Icc k (k * ℓ)) = ⟨n, hn⟩ := by
      ext
      exact h_sum_eq
    
    -- Second component HEq - The key facts are established:
    -- 1. h_sum_eq : symToPartitionSum (fromSigma x) = n
    -- 2. h_parts' : the partitions have equal parts
    -- The HEq follows from these by transport, but the dependent type handling is complex.
    -- We use eq_mpr_heq to handle the transport.
    have h_second : HEq 
        (⟨symToPartitionVal (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩), 
          symToPartitionVal_numParts (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩),
          symToPartitionVal_largestPart (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩)⟩ : 
         { p : Partition (symToPartitionSum (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩)) // 
           numParts p = k ∧ largestPart p = ℓ })
        (⟨p, hp_numParts, hp_largestPart⟩ : { p : Partition n // numParts p = k ∧ largestPart p = ℓ }) := by
      -- The key insight: both partitions have the same parts (h_parts'), and the types
      -- are equal (h_sum_eq). We construct the HEq by showing that after transporting
      -- via h_sum_eq, the partitions are equal.
      have h_eq_rec : ∀ (m : ℕ) (hm : m = n) 
          (q : Partition m) (hq_numParts : numParts q = k) (hq_largestPart : largestPart q = ℓ)
          (hq_parts : q.parts = p.parts),
          HEq (⟨q, hq_numParts, hq_largestPart⟩ : { p : Partition m // numParts p = k ∧ largestPart p = ℓ })
              (⟨p, hp_numParts, hp_largestPart⟩ : { p : Partition n // numParts p = k ∧ largestPart p = ℓ }) := by
        intro m hm q hq_numParts hq_largestPart hq_parts
        subst hm
        simp only [heq_eq_eq]
        apply Subtype.ext
        apply Partition.ext
        exact hq_parts
      exact h_eq_rec _ h_sum_eq _ 
        (symToPartitionVal_numParts (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩))
        (symToPartitionVal_largestPart (fromSigma ⟨⟨n, hn⟩, ⟨p, hp_numParts, hp_largestPart⟩⟩))
        h_parts'
    
    -- Combine using Sigma.ext_iff
    rw [Sigma.ext_iff]
    exact ⟨h_first, h_second⟩
  
  exact (Equiv.ofBijective toSigma ⟨toSigma_injective, toSigma_surj⟩).symm





/-! #### Examples verifying the formula

The following examples verify the formula C(k+ℓ-2, k-1) against computed values:
- k=1, ℓ=1: C(0,0) = 1. Partition: (1).
- k=1, ℓ=5: C(4,0) = 1. Partition: (5).
- k=2, ℓ=1: C(1,1) = 1. Partition: (1,1).
- k=2, ℓ=2: C(2,1) = 2. Partitions: (2,1), (2,2).
- k=2, ℓ=3: C(3,1) = 3. Partitions: (3,1), (3,2), (3,3).
- k=3, ℓ=2: C(3,2) = 3. Partitions: (2,1,1), (2,2,1), (2,2,2).
-/

example : partsAndLargestCountTotal 1 1 = (1 + 1 - 2).choose (1 - 1) := by native_decide
example : partsAndLargestCountTotal 1 5 = (1 + 5 - 2).choose (1 - 1) := by native_decide
example : partsAndLargestCountTotal 2 1 = (2 + 1 - 2).choose (2 - 1) := by native_decide
example : partsAndLargestCountTotal 2 2 = (2 + 2 - 2).choose (2 - 1) := by native_decide
example : partsAndLargestCountTotal 2 3 = (2 + 3 - 2).choose (2 - 1) := by native_decide
example : partsAndLargestCountTotal 3 2 = (3 + 2 - 2).choose (3 - 1) := by native_decide
example : partsAndLargestCountTotal 3 3 = (3 + 3 - 2).choose (3 - 1) := by native_decide
example : partsAndLargestCountTotal 4 3 = (4 + 3 - 2).choose (4 - 1) := by native_decide

/-! ### Partition numbers and divisor sums -/

open ArithmeticFunction in
/-- The sum of divisors function σ(n) = ∑_{d|n} d.
    This is `ArithmeticFunction.sigma 1` in Mathlib. -/
abbrev divisorSum (n : ℕ) : ℕ := sigma 1 n

section DivisorSumRecurrence

/-!
## Proof of Theorem σ₁ (thm.pars.sigma1)

We prove the recurrence `n · p(n) = ∑_{k=1}^n σ(k) · p(n-k)` using generating functions.

### Proof outline (from the TeX source)

Define the generating functions:
- `P := ∑_{n≥0} p(n) x^n` (the partition generating function)
- `S := ∑_{k≥1} σ(k) x^k` (the divisor sum generating function)

The key identity is `X · P' = S · P`, which we prove using logarithmic derivatives.

Since `P = ∏_{k≥1} 1/(1-x^k)`, taking the logarithmic derivative gives:
```
  P'/P = ∑_{k≥1} loder(1/(1-x^k))
       = ∑_{k≥1} kx^{k-1}/(1-x^k)
       = ∑_{n≥1} σ(n) x^{n-1}
```

Multiplying by `xP` gives `xP' = SP`.

Comparing coefficients of `x^n` on both sides:
- LHS: coefficient of `x^n` in `xP'` is `n · p(n)`
- RHS: coefficient of `x^n` in `SP` is `∑_{k=1}^n σ(k) · p(n-k)`

This proves the theorem.
-/

/-- The partition generating function P = ∑_{n≥0} p(n) x^n, specialized to ℤ coefficients. -/
noncomputable def P : ℤ⟦X⟧ := genFun (fun _ _ => 1)

/-- The coefficient of x^n in P equals p(n). -/
lemma coeff_P (n : ℕ) : coeff n P = partitionCount n := by
  simp only [P, coeff_genFun, partitionCount]
  conv_lhs =>
    arg 2
    ext p
    rw [show p.parts.toFinsupp.prod (fun _ _ => (1 : ℤ)) = 1 by simp [Finsupp.prod]]
  rw [sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The divisor sum generating function S = ∑_{k≥1} σ(k) x^k. -/
noncomputable def S : ℤ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else divisorSum n

/-- The coefficient of x^n in S. -/
@[simp]
lemma coeff_S (n : ℕ) : coeff n S = if n = 0 then 0 else divisorSum n := by
  simp only [S, coeff_mk]
  split_ifs <;> simp

/-- The coefficient of x^n in X · P' equals n · p(n). -/
lemma coeff_X_mul_derivative_P (n : ℕ) :
    coeff n (X * d⁄dX P) = n * coeff n P := by
  rcases n with _ | n
  · simp [coeff_zero_eq_constantCoeff_apply]
  · change coeff (n + 1) (X * d⁄dX P) = (n + 1) * coeff (n + 1) P
    rw [coeff_succ_X_mul, coeff_derivative]
    ring

/-- The coefficient of x^n in S · P equals ∑_{k=1}^n σ(k) · p(n-k). -/
lemma coeff_S_mul_P (n : ℕ) :
    coeff n (S * P) = ∑ k ∈ Finset.range n, divisorSum (k + 1) * partitionCount (n - k - 1) := by
  rw [coeff_mul]
  simp only [coeff_S, coeff_P]
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [sum_range_succ']
  simp only [ite_true, CharP.cast_eq_zero, zero_mul]
  simp only [Nat.succ_ne_zero, ite_false, add_zero]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.sub_sub]

end DivisorSumRecurrence

/-- Helper: sum of multiset minus another multiset. -/
private lemma multiset_sum_sub_le {s t : Multiset ℕ} (h : t ≤ s) :
    (s - t).sum = s.sum - t.sum := by
  have hadd : s = (s - t) + t := (Multiset.sub_add_cancel h).symm
  calc (s - t).sum = (s - t).sum + t.sum - t.sum := by omega
    _ = ((s - t) + t).sum - t.sum := by rw [Multiset.sum_add]
    _ = s.sum - t.sum := by rw [← hadd]

/-- Helper: replicate is ≤ multiset if count is sufficient. -/
private lemma replicate_le_of_count_ge {s : Multiset ℕ} {a : ℕ} {j : ℕ}
    (h : j ≤ s.count a) : Multiset.replicate j a ≤ s := by
  rw [Multiset.le_iff_count]
  intro b
  rw [Multiset.count_replicate]
  split_ifs with hba
  · subst hba; exact h
  · exact Nat.zero_le _

/-- Sum of parts equals sum over distinct parts weighted by count. -/
lemma sum_parts_as_weighted_count {n : ℕ} (p : Partition n) :
    p.parts.sum = (p.parts.toFinset).sum (fun d => d * p.parts.count d) := by
  induction p.parts using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.toFinset_cons]
    by_cases ha : a ∈ s.toFinset
    · rw [Finset.insert_eq_of_mem ha, ih]
      have key : ∀ x ∈ s.toFinset, x * Multiset.count x s + (if x = a then x else 0) =
             x * Multiset.count x (a ::ₘ s) := by
        intro x _
        rw [Multiset.count_cons]
        split_ifs with hxa <;> ring
      trans (∑ x ∈ s.toFinset, (x * Multiset.count x s + if x = a then x else 0))
      · rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', ha, ↓reduceIte]
        ring
      · exact Finset.sum_congr rfl key
    · simp only [Multiset.mem_toFinset] at ha
      have hcount : s.count a = 0 := Multiset.count_eq_zero.mpr ha
      rw [Finset.sum_insert (by simp [ha]), Multiset.count_cons_self, hcount, ih]
      ring_nf
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hxa : x ≠ a := fun h => ha (h ▸ (Multiset.mem_toFinset.mp hx))
      simp [Multiset.count_cons_of_ne hxa]

/-- LHS of the identity equals sum of parts over all partitions. -/
lemma lhs_eq_sum_parts (I : Set ℕ) [DecidablePred (· ∈ I)] (n : ℕ) :
    n * (restricted n (· ∈ I)).card =
    (restricted n (· ∈ I)).sum (fun p => p.parts.sum) := by
  simp only [Partition.parts_sum, Finset.sum_const, smul_eq_mul, mul_comm]

/-! #### Helper lemmas for partitionCount_divisorSum_restricted

These lemmas establish the key pieces needed for the double-counting proof:
1. **Bijection lemma**: Removing j copies of d from a partition gives a partition of n - d*j
2. **Count sum identity**: ∑_p count(d, p) = ∑_{j≥1} |{p : count(d,p) ≥ j}|
3. **Sum swap lemma**: Swap the order of summation over partitions and parts
4. **Divisor sum reindexing**: Transform ∑_k ∑_{d | k+1} to ∑_d ∑_{j : d*j ≤ n}
-/

/-- Remove j copies of element d from a partition, getting a partition of n - d*j.
    This is the forward direction of the bijection. -/
def removePartCopies {n : ℕ} (p : Partition n) (d j : ℕ) (_hd : d > 0) (hj : j ≤ p.parts.count d) :
    Partition (n - d * j) := by
  let newParts := p.parts - Multiset.replicate j d
  have hle : Multiset.replicate j d ≤ p.parts := replicate_le_of_count_ge hj
  have hsum : newParts.sum = n - d * j := by
    rw [multiset_sum_sub_le hle, p.parts_sum, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hpos : ∀ {x}, x ∈ newParts → 0 < x := by
    intro x hx
    have hx_in_orig : x ∈ p.parts := Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
    exact p.parts_pos hx_in_orig
  exact ⟨newParts, hpos, hsum⟩

/-- Add j copies of element d to a partition, getting a partition of m + d*j.
    This is the backward direction of the bijection. -/
def addPartCopies {m : ℕ} (q : Partition m) (d j : ℕ) (hd : d > 0) :
    Partition (m + d * j) := by
  let newParts := q.parts + Multiset.replicate j d
  have hsum : newParts.sum = m + d * j := by
    simp only [newParts, Multiset.sum_add, q.parts_sum, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hpos : ∀ {x}, x ∈ newParts → 0 < x := by
    intro x hx
    simp only [newParts, Multiset.mem_add] at hx
    rcases hx with hx_q | hx_rep
    · exact q.parts_pos hx_q
    · simp only [Multiset.mem_replicate] at hx_rep
      rcases hx_rep with ⟨_, rfl⟩
      exact hd
  exact ⟨newParts, hpos, hsum⟩

/-- Helper: Standard identity ∑_i f(i) = ∑_j |{i : f(i) ≥ j+1}| for bounded functions.
    The proof uses a bijection on sigma types to swap the order of summation. -/
private lemma sum_eq_sum_card_filter_ge_aux {α : Type*} (s : Finset α) (f : α → ℕ) (bound : ℕ)
    (hbound : ∀ a ∈ s, f a ≤ bound) :
    s.sum f = (Finset.range bound).sum (fun j => (s.filter (fun a => f a ≥ j + 1)).card) := by
  -- Each f(a) = card {j ∈ range (f a)} = card {j ∈ range bound | j < f a}
  have h1 : s.sum f = s.sum (fun a => ((Finset.range bound).filter (fun j => j < f a)).card) := by
    apply Finset.sum_congr rfl
    intro a ha
    have hfa : f a ≤ bound := hbound a ha
    have : (Finset.range bound).filter (fun j => j < f a) = Finset.range (f a) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro ⟨_, hj⟩; exact hj
      · intro hj; exact ⟨Nat.lt_of_lt_of_le hj hfa, hj⟩
    rw [this, Finset.card_range]
  rw [h1]
  -- Use sigma types to swap the order of summation
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  -- Show the two sigma sets have the same cardinality via bijection
  apply Finset.card_bij (fun (p : (a : α) × ℕ) _ => ⟨p.2, p.1⟩)
  · -- Image is in the RHS sigma
    intro ⟨a, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hp ⊢
    obtain ⟨ha, hj_range, hj_lt⟩ := hp
    exact ⟨hj_range, ha, Nat.lt_iff_add_one_le.mp hj_lt⟩
  · -- Injectivity
    intro ⟨a₁, j₁⟩ _ ⟨a₂, j₂⟩ _ heq
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
    obtain ⟨hj, ha⟩ := heq
    simp only [Sigma.mk.inj_iff, heq_eq_eq]
    exact ⟨ha, hj⟩
  · -- Surjectivity
    intro ⟨j, a⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hj_range, ha, hge⟩ := hp
    refine ⟨⟨a, j⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range]
    exact ⟨ha, hj_range, Nat.lt_of_succ_le hge⟩

/-- Helper: count(d, p) ≤ n for any partition of n. -/
private lemma count_le_of_partition_aux (n d : ℕ) (p : Partition n) : p.parts.count d ≤ n := by
  by_cases hd : d = 0
  · -- d = 0 case: 0 cannot be in parts of a partition
    have h0 : 0 ∉ p.parts := fun h => Nat.lt_irrefl 0 (p.parts_pos h)
    rw [hd, Multiset.count_eq_zero.mpr h0]
    exact Nat.zero_le n
  · -- d > 0 case
    have h := p.parts_sum
    have hpos : 0 < d := Nat.pos_of_ne_zero hd
    have hrep : Multiset.replicate (p.parts.count d) d ≤ p.parts :=
      Multiset.le_count_iff_replicate_le.mp le_rfl
    have hle : p.parts.count d * d ≤ p.parts.sum := by
      have hsum_rep : (Multiset.replicate (p.parts.count d) d).sum = p.parts.count d * d := by
        simp [Multiset.sum_replicate]
      rw [← hsum_rep]
      obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hrep
      calc (Multiset.replicate (p.parts.count d) d).sum
          ≤ (Multiset.replicate (p.parts.count d) d).sum + u.sum := Nat.le_add_right _ _
        _ = p.parts.sum := by rw [← Multiset.sum_add, ← hu]
    calc p.parts.count d ≤ p.parts.count d * d := Nat.le_mul_of_pos_right _ hpos
      _ ≤ p.parts.sum := hle
      _ = n := h

/-- Helper: count(d, p) ≤ n/d for any partition of n and d > 0.
    This is the tight bound: at most n/d copies of d can fit in a partition of n. -/
lemma count_le_div_of_partition (n d : ℕ) (p : Partition n) (hd : 0 < d) :
    p.parts.count d ≤ n / d := by
  have h1 : Multiset.replicate (p.parts.count d) d ≤ p.parts :=
    Multiset.le_count_iff_replicate_le.mp le_rfl
  have h2 : (Multiset.replicate (p.parts.count d) d).sum ≤ p.parts.sum := by
    obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp h1
    calc (Multiset.replicate (p.parts.count d) d).sum
        ≤ (Multiset.replicate (p.parts.count d) d).sum + u.sum := Nat.le_add_right _ _
      _ = (Multiset.replicate (p.parts.count d) d + u).sum := (Multiset.sum_add _ _).symm
      _ = p.parts.sum := by rw [← hu]
  simp only [Multiset.sum_replicate] at h2
  rw [p.parts_sum] at h2
  exact Nat.le_div_iff_mul_le hd |>.mpr h2

/-- The count sum identity: ∑_p count(d, p) = ∑_{j=1}^{max_count} |{p : count(d,p) ≥ j}|.
    This is the standard identity that sum of values equals sum of "at least j" counts.

    The proof uses double counting: each partition p with count(d,p) = c contributes
    c to the LHS and is counted in exactly c of the sets {p : count(d,p) ≥ j+1} for j < c. -/
lemma sum_count_eq_sum_card_ge (n : ℕ) (s : Finset (Partition n)) (d : ℕ) :
    s.sum (fun p => p.parts.count d) =
    (Finset.range (n + 1)).sum (fun j =>
      (s.filter (fun p => p.parts.count d ≥ j + 1)).card) := by
  apply sum_eq_sum_card_filter_ge_aux
  intro p _
  exact Nat.le_succ_of_le (count_le_of_partition_aux n d p)

/-- Partitions with count(d, p) ≥ j biject with partitions of n - d*j.
    Specifically, {p ∈ restricted n I : count(d,p) ≥ j} ≃ restricted (n - d*j) I.

    Forward: remove j copies of d
    Backward: add j copies of d -/
lemma card_count_ge_eq_restricted (I : Set ℕ) [DecidablePred (· ∈ I)]
    (hI : ∀ i ∈ I, i > 0) (n d j : ℕ) (hd : d ∈ I) (hdj : d * j ≤ n) :
    ((restricted n (· ∈ I)).filter (fun p => p.parts.count d ≥ j)).card =
    (restricted (n - d * j) (· ∈ I)).card := by
  -- We establish a bijection between the two sets
  apply Finset.card_bij
    -- Forward map: remove j copies of d
    (fun p hp => by
      have hmem : p ∈ restricted n (· ∈ I) := Finset.mem_filter.mp hp |>.1
      have hge : p.parts.count d ≥ j := Finset.mem_filter.mp hp |>.2
      exact removePartCopies p d j (hI d hd) hge)
  · -- The image is in restricted (n - d*j) I
    intro p hp
    simp only [restricted, Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx
    have hmem : p ∈ restricted n (· ∈ I) := Finset.mem_filter.mp hp |>.1
    simp only [restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hx_orig : x ∈ p.parts := by
      simp only [removePartCopies] at hx
      exact Multiset.mem_of_le (Multiset.sub_le_self _ _) hx
    exact hmem x hx_orig
  · -- Injectivity
    intro p₁ hp₁ p₂ hp₂ heq
    have hge₁ : p₁.parts.count d ≥ j := Finset.mem_filter.mp hp₁ |>.2
    have hge₂ : p₂.parts.count d ≥ j := Finset.mem_filter.mp hp₂ |>.2
    simp only [removePartCopies] at heq
    apply Partition.ext
    have h : p₁.parts - Multiset.replicate j d = p₂.parts - Multiset.replicate j d := by
      injection heq
    have hle₁ : Multiset.replicate j d ≤ p₁.parts := replicate_le_of_count_ge hge₁
    have hle₂ : Multiset.replicate j d ≤ p₂.parts := replicate_le_of_count_ge hge₂
    calc p₁.parts = (p₁.parts - Multiset.replicate j d) + Multiset.replicate j d :=
           (Multiset.sub_add_cancel hle₁).symm
      _ = (p₂.parts - Multiset.replicate j d) + Multiset.replicate j d := by rw [h]
      _ = p₂.parts := Multiset.sub_add_cancel hle₂
  · -- Surjectivity
    intro q hq
    simp only [restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    -- Construct p by adding j copies of d
    have hd_pos : d > 0 := hI d hd
    let p := addPartCopies q d j hd_pos
    have hp_parts_in_I : ∀ x ∈ p.parts, x ∈ I := by
      intro x hx
      simp only [addPartCopies, p] at hx
      simp only [Multiset.mem_add] at hx
      rcases hx with hx_q | hx_rep
      · exact hq x hx_q
      · simp only [Multiset.mem_replicate] at hx_rep
        rcases hx_rep with ⟨_, rfl⟩
        exact hd
    have hp_sum : p.parts.sum = (n - d * j) + d * j := p.parts_sum
    have hp_sum' : p.parts.sum = n := by omega
    -- Cast p to Partition n
    let p' : Partition n := ⟨p.parts, @Partition.parts_pos _ p, hp_sum'⟩
    use p'
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, restricted, Finset.mem_univ, true_and]
      refine ⟨hp_parts_in_I, ?_⟩
      -- Show count(d, p') ≥ j
      simp only [p', addPartCopies, p]
      rw [Multiset.count_add, Multiset.count_replicate_self]
      omega
    · -- Show removePartCopies p' d j = q
      apply Partition.ext
      simp only [removePartCopies, p', addPartCopies, p]
      rw [Multiset.add_sub_cancel_right]

/-- Divisor sum reindexing: swaps the order of summation from
    ∑_{k=0}^{n-1} ∑_{d | k+1, d ∈ I} to ∑_{d ∈ I, d ≤ n} ∑_{j=1}^{⌊n/d⌋}.

    The bijection is: (k, d) ↔ (d, j) where k = d*j - 1, j = (k+1)/d.
    This transforms the constraint "d | k+1" to "k = d*j - 1 for some j ≥ 1".

    Used in the proof of partitionCount_divisorSum_restricted. -/
lemma divisor_sum_reindex (I : Set ℕ) [DecidablePred (· ∈ I)] (n : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ Finset.range n, ∑ d ∈ (Nat.divisors (k + 1)).filter (· ∈ I), d * f (n - k - 1) =
    ∑ d ∈ (Finset.Icc 1 n).filter (· ∈ I),
      d * ∑ j ∈ Finset.Icc 1 (n / d), f (n - d * j) := by
  -- The proof establishes a bijection between index pairs:
  -- LHS: (k, d) with k ∈ [0, n-1], d | k+1, d ∈ I
  -- RHS: (d, j) with d ∈ I ∩ [1, n], j ∈ [1, n/d]
  -- via k = d*j - 1, j = (k+1)/d
  --
  -- Key observations:
  -- 1. If d | k+1, then (k+1)/d ≥ 1 (since d ≤ k+1)
  -- 2. If d | k+1 and k < n, then (k+1)/d ≤ n/d
  -- 3. If j ∈ [1, n/d], then d*j - 1 < n (since d*j ≤ d*(n/d) ≤ n)
  -- 4. d | (d*j - 1 + 1) = d*j is automatic
  rw [Finset.sum_sigma']
  conv_rhs =>
    arg 2
    ext d
    rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  -- Forward map: (k, d) ↦ (d, (k+1)/d)
  let i : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) := fun ⟨k, d⟩ => ⟨d, (k + 1) / d⟩
  -- Backward map: (d, j) ↦ (d*j - 1, d)
  let j : (Σ _ : ℕ, ℕ) → (Σ _ : ℕ, ℕ) := fun ⟨d, j⟩ => ⟨d * j - 1, d⟩
  -- Use sum_nbij' with these maps
  apply Finset.sum_nbij' i j
  · -- i maps S to T
    intro ⟨k, d⟩ hkd
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_divisors] at hkd
    obtain ⟨hk, ⟨hdiv, _⟩, hI⟩ := hkd
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, i]
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdiv (Nat.succ_pos k)
    refine ⟨⟨⟨hd_pos, ?_⟩, hI⟩, ⟨?_, ?_⟩⟩
    · -- d ≤ n: since d | k+1 and k < n, we have d ≤ k+1 ≤ n
      calc d ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) hdiv
           _ ≤ n := hk
    · -- (k+1)/d ≥ 1: since d | k+1 and k+1 ≠ 0
      exact Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos k) hdiv) hd_pos
    · -- (k+1)/d ≤ n/d: since k+1 ≤ n
      exact Nat.div_le_div_right hk
  · -- j maps T to S
    intro ⟨d, jval⟩ hdj
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hdj
    obtain ⟨⟨⟨hd1, hdn⟩, hI⟩, hj1, hjn⟩ := hdj
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_divisors, j]
    have h1 : 1 ≤ d * jval := one_le_mul_of_one_le_of_one_le hd1 hj1
    refine ⟨?_, ⟨?_, ?_⟩, hI⟩
    · -- d * jval - 1 < n
      have h2 : d * jval ≤ n := calc
        d * jval ≤ d * (n / d) := Nat.mul_le_mul_left d hjn
        _ ≤ n := Nat.mul_div_le n d
      omega
    · -- d | (d * jval - 1 + 1) = d * jval
      simp only [Nat.sub_add_cancel h1]
      exact Nat.dvd_mul_right d jval
    · -- d * jval - 1 + 1 ≠ 0
      simp only [Nat.sub_add_cancel h1]
      exact (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hd1)
        (Nat.lt_of_lt_of_le Nat.zero_lt_one hj1)).ne'
  · -- j ∘ i = id on S
    intro ⟨k, d⟩ hkd
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_divisors] at hkd
    obtain ⟨_, ⟨hdiv, _⟩, _⟩ := hkd
    simp only [i, j]
    -- Need: ⟨d * ((k+1)/d) - 1, d⟩ = ⟨k, d⟩
    -- This requires d * ((k+1)/d) = k + 1, which holds since d | k+1
    congr 1
    rw [Nat.mul_div_cancel' hdiv]
    omega
  · -- i ∘ j = id on T
    intro ⟨d, jval⟩ hdj
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hdj
    obtain ⟨⟨⟨hd1, _⟩, _⟩, hj1, _⟩ := hdj
    simp only [i, j]
    -- Need: ⟨d, (d*jval - 1 + 1)/d⟩ = ⟨d, jval⟩
    -- This requires (d*jval)/d = jval
    congr 1
    have h1 : 1 ≤ d * jval := one_le_mul_of_one_le_of_one_le hd1 hj1
    simp only [Nat.sub_add_cancel h1]
    exact Nat.mul_div_cancel_left jval (Nat.lt_of_lt_of_le Nat.zero_lt_one hd1)
  · -- f values match: d * f(n - k - 1) = d * f(n - d * ((k+1)/d))
    intro ⟨k, d⟩ hkd
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Nat.mem_divisors] at hkd
    obtain ⟨_, ⟨hdiv, _⟩, _⟩ := hkd
    simp only [i]
    -- Need: d * f(n - k - 1) = d * f(n - d * ((k+1)/d))
    -- Since d | k+1, we have d * ((k+1)/d) = k+1, so n - d * ((k+1)/d) = n - k - 1
    congr 2
    rw [Nat.mul_div_cancel' hdiv]
    omega

/-- Generalization of the divisor sum recurrence for partitions with parts in a set I:
    `n · p_I(n) = ∑_{k=1}^n σ_I(k) · p_I(n-k)`
    where σ_I(n) is the sum of divisors of n that belong to I.
    (Theorem \ref{thm.pars.sigma1-I})

    The proof uses the generating function approach via logarithmic derivatives:
    - Let P_I = ∑_n p_I(n) x^n = ∏_{k∈I} 1/(1-x^k)
    - Let S_I = ∑_n σ_I(n) x^n
    - Taking logarithmic derivative of P_I gives x·P_I'/P_I = S_I
    - Therefore x·P_I' = S_I·P_I
    - Comparing coefficients of x^n gives the identity

    Equivalently, both sides count weighted pairs:
    - LHS = ∑_p (sum of parts) = ∑_p ∑_d d·count(d,p)
    - RHS = ∑_{m=1}^n σ_I(m)·p_I(n-m) = ∑_d d·∑_{j≥1} p_I(n-d·j)
    - Both equal ∑_{d∈I, d≤n} d·∑_{j=1}^{n/d} p_I(n-d·j) -/
theorem partitionCount_divisorSum_restricted (I : Set ℕ) [DecidablePred (· ∈ I)]
    (hI : ∀ i ∈ I, i > 0) (n : ℕ) :
    n * (restricted n (· ∈ I)).card =
    ∑ k ∈ Finset.range n,
      (∑ d ∈ (Nat.divisors (k + 1)).filter (· ∈ I), d) *
      (restricted (n - k - 1) (· ∈ I)).card := by
  /-
  The proof uses a double counting argument. Both sides count weighted pairs.

  **LHS Analysis:**
  n * |restricted n I| = ∑_{p ∈ restricted n I} p.parts.sum  (since each partition sums to n)
  = ∑_{p ∈ restricted n I} ∑_{d ∈ p.parts.toFinset} d * count(d, p)
  = ∑_{d ∈ I, d ≤ n} d * ∑_{p ∈ restricted n I} count(d, p)  (swapping sums)
  = ∑_{d ∈ I, d ≤ n} d * ∑_{j=1}^{⌊n/d⌋} |restricted (n - d·j) I|

  The last step uses: ∑_p count(d, p) = ∑_{j≥1} |{p : count(d,p) ≥ j}|
  and the bijection: {p : count(d,p) ≥ j} ↔ restricted (n - d·j) I
  (removing j copies of d from p gives a partition of n - d·j with parts in I)

  **RHS Analysis:**
  ∑_{k=0}^{n-1} σ_I(k+1) · |restricted (n-k-1) I|
  = ∑_{k=0}^{n-1} (∑_{d | k+1, d ∈ I} d) · |restricted (n-k-1) I|
  = ∑_{k=0}^{n-1} ∑_{d | k+1, d ∈ I} d · |restricted (n-k-1) I|  (distributing)

  Now swap: if d | k+1, write k+1 = d·j for some j ≥ 1, so k = d·j - 1
  and n - k - 1 = n - d·j. The constraint 0 ≤ k < n becomes 1 ≤ d·j ≤ n.

  = ∑_{d ∈ I, d ≤ n} d · ∑_{j=1}^{⌊n/d⌋} |restricted (n - d·j) I|

  **Conclusion:** LHS = RHS since both equal the same expression.
  -/
  -- Rewrite LHS using lhs_eq_sum_parts
  rw [lhs_eq_sum_parts]
  -- Rewrite each p.parts.sum using sum_parts_as_weighted_count
  conv_lhs => arg 2; ext p; rw [sum_parts_as_weighted_count]
  -- Step 1: Extend inner sum from p.parts.toFinset to (Icc 1 n).filter (· ∈ I)
  -- For d ∉ p.parts.toFinset, count(d, p) = 0, so the term is 0
  have h_extend : (restricted n (· ∈ I)).sum (fun p => p.parts.toFinset.sum (fun d => d * p.parts.count d)) =
      (restricted n (· ∈ I)).sum (fun p => ((Finset.Icc 1 n).filter (· ∈ I)).sum (fun d => d * p.parts.count d)) := by
    apply Finset.sum_congr rfl
    intro p hp
    -- p.parts.toFinset ⊆ (Icc 1 n).filter (· ∈ I)
    have hsubset : p.parts.toFinset ⊆ (Finset.Icc 1 n).filter (· ∈ I) := by
      intro d hd
      simp only [Multiset.mem_toFinset] at hd
      simp only [Finset.mem_filter, Finset.mem_Icc]
      simp only [restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨⟨p.parts_pos hd, parts_le p d hd⟩, hp d hd⟩
    rw [← Finset.sum_sdiff hsubset]
    have h0 : ((Finset.Icc 1 n).filter (· ∈ I) \ p.parts.toFinset).sum (fun d => d * p.parts.count d) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      simp only [Finset.mem_sdiff, Multiset.mem_toFinset] at hd
      rw [Multiset.count_eq_zero.mpr hd.2, mul_zero]
    rw [h0, zero_add]
  rw [h_extend]
  -- Step 2: Swap the order of summation
  rw [Finset.sum_comm]
  -- Now LHS = ∑_{d ∈ I ∩ [1,n]} (∑_p d * count(d, p))
  --         = ∑_{d ∈ I ∩ [1,n]} d * (∑_p count(d, p))
  conv_lhs =>
    arg 2
    ext d
    rw [← Finset.mul_sum]
  -- Step 3: Use sum_count_eq_sum_card_ge
  -- ∑_p count(d, p) = ∑_{j=0}^{n} |{p : count(d,p) ≥ j+1}|
  conv_lhs =>
    arg 2
    ext d
    rw [sum_count_eq_sum_card_ge]
  -- Now LHS = ∑_{d ∈ I ∩ [1,n]} d * ∑_{j=0}^{n} |{p : count(d,p) ≥ j+1}|
  --
  -- The key insight is that for j+1 > n/d, the filter is empty because
  -- count(d, p) ≤ n/d for any partition p of n (at most n/d copies of d can fit).
  -- So we can restrict the sum to j ∈ [0, n/d - 1], which after shifting becomes j' ∈ [1, n/d].
  --
  -- Then we apply card_count_ge_eq_restricted to convert filter cardinalities to restricted counts.
  -- Finally, we apply divisor_sum_reindex to match the RHS.
  --
  -- The remaining steps are index manipulation and application of the helper lemmas.
  -- All the mathematical content is captured in the helper lemmas; this is bookkeeping.

  -- Step 4: Transform inner sum for each d
  have h_inner : ∀ d ∈ (Finset.Icc 1 n).filter (· ∈ I),
      (Finset.range (n + 1)).sum (fun j =>
        ((restricted n (· ∈ I)).filter (fun p => p.parts.count d ≥ j + 1)).card) =
      (Finset.Icc 1 (n / d)).sum (fun j => (restricted (n - d * j) (· ∈ I)).card) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨_, _⟩, hdI⟩ := hd
    have hd_pos : 0 < d := hI d hdI
    -- Step 4a: Truncate sum at n/d (terms for j ≥ n/d are 0)
    have h_trunc : (Finset.range (n + 1)).sum (fun j =>
        ((restricted n (· ∈ I)).filter (fun p => p.parts.count d ≥ j + 1)).card) =
        (Finset.range (n / d)).sum (fun j =>
          ((restricted n (· ∈ I)).filter (fun p => p.parts.count d ≥ j + 1)).card) := by
      have hsub : Finset.range (n / d) ⊆ Finset.range (n + 1) := by
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        calc x < n / d := hx
             _ ≤ n := Nat.div_le_self n d
             _ < n + 1 := Nat.lt_succ_self n
      symm
      apply Finset.sum_subset hsub
      intro j hj1 hj2
      simp only [Finset.mem_range, not_lt] at hj1 hj2
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro p _
      simp only [not_le]
      have h : p.parts.count d ≤ n / d := count_le_div_of_partition n d p hd_pos
      omega
    rw [h_trunc]
    -- Step 4b: Shift index from range (n/d) to Icc 1 (n/d)
    have h_shift : Finset.Icc 1 (n / d) = (Finset.range (n / d)).map ⟨(· + 1), Nat.succ_injective⟩ := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro ⟨h1, h2⟩; use x - 1; omega
      · intro ⟨y, hy1, hy2⟩; omega
    rw [h_shift, Finset.sum_map]
    -- Step 4c: Apply card_count_ge_eq_restricted for each term
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Function.Embedding.coeFn_mk]
    have hdj : d * (j + 1) ≤ n := by
      have h1 : j + 1 ≤ n / d := hj
      calc d * (j + 1) ≤ d * (n / d) := Nat.mul_le_mul_left d h1
           _ ≤ n := Nat.mul_div_le n d
    exact card_count_ge_eq_restricted I hI n d (j + 1) hdI hdj
  -- Step 5: Apply the inner transformation
  have h_transform : ((Finset.Icc 1 n).filter (· ∈ I)).sum (fun d =>
      d * (Finset.range (n + 1)).sum (fun j =>
        ((restricted n (· ∈ I)).filter (fun p => p.parts.count d ≥ j + 1)).card)) =
      ((Finset.Icc 1 n).filter (· ∈ I)).sum (fun d =>
        d * (Finset.Icc 1 (n / d)).sum (fun j => (restricted (n - d * j) (· ∈ I)).card)) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [h_inner d hd]
  rw [h_transform]
  -- Step 6: Apply divisor_sum_reindex in reverse to match RHS
  rw [← divisor_sum_reindex I n (fun m => (restricted m (· ∈ I)).card)]
  -- Step 7: Convert from ∑∑ to (∑) * form
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]

/-- The recurrence relation connecting partition numbers and divisor sums:
    `n · p(n) = ∑_{k=1}^n σ(k) · p(n-k)`.
    (Theorem \ref{thm.pars.sigma1})

    This is proved using the generalized identity `partitionCount_divisorSum_restricted`
    specialized to I = all positive integers. -/
theorem partitionCount_divisorSum (n : ℕ) :
    n * partitionCount n = ∑ k ∈ Finset.range n, divisorSum (k + 1) * partitionCount (n - k - 1) := by
  -- Specialize partitionCount_divisorSum_restricted with I = Set.Ioi 0 (positive integers)
  have h := partitionCount_divisorSum_restricted (Set.Ioi 0) (fun i hi => hi) n
  -- Convert restricted to partitionCount:
  -- For partitions, all parts are positive, so restricted n (· > 0) = all partitions
  have h_card : ∀ m, (restricted m (· ∈ Set.Ioi 0)).card = partitionCount m := fun m => by
    simp only [Set.mem_Ioi, restricted, partitionCount]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ i hi => p.parts_pos hi⟩
  simp only [h_card] at h
  -- Convert sum over filtered divisors to divisorSum:
  -- All divisors of k+1 are positive, so the filter is trivial
  have h_sum : ∀ k, ∑ d ∈ (Nat.divisors (k + 1)).filter (· ∈ Set.Ioi 0), d = divisorSum (k + 1) := fun k => by
    have hf : (Nat.divisors (k + 1)).filter (· ∈ Set.Ioi 0) = Nat.divisors (k + 1) := by
      ext d
      simp only [Finset.mem_filter, Set.mem_Ioi, and_iff_left_iff_imp]
      exact Nat.pos_of_mem_divisors
    rw [hf]
    simp [divisorSum, ArithmeticFunction.sigma_one_apply]
  simp only [h_sum] at h
  exact h

/-- The key generating function identity: X · P' = S · P.

This follows from the combinatorial identity `partitionCount_divisorSum` by
comparing coefficients. -/
theorem X_mul_derivative_P_eq_S_mul_P : X * d⁄dX P = S * P := by
  ext n
  rw [coeff_X_mul_derivative_P, coeff_S_mul_P, coeff_P]
  exact_mod_cast partitionCount_divisorSum n

end Nat.Partition
