/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib

/-!
# Laurent Power Series

This file formalizes the content from Section `sec.gf.laure` of the textbook,
covering Laurent power series and related concepts.

## Main Definitions

* `BinaryRepresentation` - A binary representation of a nonnegative integer
* `BalancedTernaryRepresentation` - A balanced ternary representation of an integer
* `DoublyInfinitePowerSeries` - The K-module K[[x^±]] of all families indexed by ℤ
* `DoublyInfinitePowerSeries.IsLaurentSeries` - Predicate for when a doubly infinite
  power series is a Laurent series (Definition `def.fps.laure.lauser`)
* We also use Mathlib's `LaurentPolynomial` for K[x^±] and `LaurentSeries` for K((x))

## Main Results

* `binaryRepresentation_unique` - Each n ∈ ℕ has a unique binary representation
* `balancedTernaryRepresentation_unique` - Each integer has a unique balanced ternary representation
* `isLaurentSeries_ofLaurentSeries` - Mathlib's LaurentSeries satisfies our IsLaurentSeries predicate
* `toLaurentSeries_ofLaurentSeries` / `ofLaurentSeries_toLaurentSeries` - Round-trip equivalence
  showing our definition matches Mathlib's
* `Int.isPWO_of_bddBelow` - Bounded below subsets of ℤ are partially well-ordered
* Properties of Laurent polynomials and Laurent series from Mathlib

## References

* [Grinberg, *Algebraic Combinatorics*], Section on Laurent power series
-/

open scoped LaurentPolynomial

noncomputable section

namespace AlgebraicCombinatorics

/-! ## Binary Representation

A binary representation encodes a nonnegative integer as an essentially finite
sequence of bits (0 or 1).
-/

/-- A binary representation of a nonnegative integer `n` is an essentially finite
sequence `(b_i)_{i ∈ ℕ}` of elements in `{0, 1}` such that `n = ∑ b_i * 2^i`.

This corresponds to Definition in `sec.gf.laure` of the source.
-/
structure BinaryRepresentation (n : ℕ) where
  /-- The sequence of bits -/
  bits : ℕ → Fin 2
  /-- Only finitely many bits are nonzero -/
  finite_support : {i | bits i ≠ 0}.Finite
  /-- The sum equals n -/
  sum_eq : ∑ᶠ i, (bits i : ℕ) * 2^i = n

namespace BinaryRepresentation

/-- Helper: construct bits from a list of digits. -/
private def bitsFromList (L : List ℕ) (hL : ∀ x ∈ L, x < 2) : ℕ → Fin 2 := fun i =>
  if h : i < L.length then ⟨L[i], hL _ (List.getElem_mem h)⟩ else 0

private theorem bitsFromList_support_finite (L : List ℕ) (hL : ∀ x ∈ L, x < 2) :
    {i | bitsFromList L hL i ≠ 0}.Finite := by
  apply Set.Finite.subset (Set.finite_lt_nat L.length)
  intro i hi
  simp only [Set.mem_ofPred_eq, bitsFromList, ne_eq] at hi ⊢
  by_contra h
  push Not at h
  simp only [dite_eq_right (not_lt.mpr h), not_true_eq_false] at hi

@[simp]
private theorem bitsFromList_of_lt {L : List ℕ} {hL : ∀ x ∈ L, x < 2} {i : ℕ} (hi : i < L.length) :
    (bitsFromList L hL i : ℕ) = L[i] := by
  simp only [bitsFromList, hi, ↓reduceDIte]

@[simp]
private theorem bitsFromList_of_ge {L : List ℕ} {hL : ∀ x ∈ L, x < 2} {i : ℕ} (hi : L.length ≤ i) :
    bitsFromList L hL i = 0 := by
  simp only [bitsFromList, not_lt.mpr hi, ↓reduceDIte]

private theorem bitsFromList_sum_eq (L : List ℕ) (hL : ∀ x ∈ L, x < 2) :
    ∑ᶠ i, (bitsFromList L hL i : ℕ) * 2^i = Nat.ofDigits 2 L := by
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range L.length)]
  · -- Show sum over range equals ofDigits
    induction L with
    | nil => simp [Nat.ofDigits]
    | cons d L' ih =>
      have hL' : ∀ x ∈ L', x < 2 := fun x hx => hL x (List.mem_cons_of_mem d hx)
      simp only [List.length_cons, Finset.sum_range_succ']
      rw [Nat.ofDigits_cons]
      have h0 : (0 : ℕ) < (d :: L').length := List.length_pos_of_ne_nil (List.cons_ne_nil d L')
      simp only [bitsFromList_of_lt h0, List.getElem_cons_zero, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      -- Transform the sum
      have h_eq : ∀ x ∈ Finset.range L'.length, (bitsFromList (d :: L') hL (x + 1) : ℕ) =
                  (bitsFromList L' hL' x : ℕ) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        have h1 : i + 1 < (d :: L').length := by simp; omega
        have h2 : i < L'.length := hi
        simp only [bitsFromList_of_lt h1, bitsFromList_of_lt h2, List.getElem_cons_succ]
      calc ∑ x ∈ Finset.range L'.length, (bitsFromList (d :: L') hL (x + 1) : ℕ) * 2 ^ (x + 1)
          = ∑ x ∈ Finset.range L'.length, (bitsFromList L' hL' x : ℕ) * 2 ^ (x + 1) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [h_eq i hi]
        _ = ∑ x ∈ Finset.range L'.length, (bitsFromList L' hL' x : ℕ) * (2 * 2 ^ x) := by
            apply Finset.sum_congr rfl
            intro i _
            ring_nf
        _ = ∑ x ∈ Finset.range L'.length, 2 * ((bitsFromList L' hL' x : ℕ) * 2 ^ x) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = 2 * ∑ x ∈ Finset.range L'.length, (bitsFromList L' hL' x : ℕ) * 2 ^ x := by
            rw [Finset.mul_sum]
        _ = 2 * Nat.ofDigits 2 L' := by rw [ih hL']
  · -- Support is contained in range
    intro i hi
    simp only [Function.mem_support, ne_eq, bitsFromList] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    push Not at h
    simp only [dite_eq_right (not_lt.mpr h), Fin.val_zero, zero_mul, not_true_eq_false] at hi

end BinaryRepresentation

/-- Every natural number has a binary representation.
This is part of Theorem `thm.fps.laure.binary-rep-uniq`. -/
theorem binaryRepresentation_exists (n : ℕ) : Nonempty (BinaryRepresentation n) := by
  let L := Nat.digits 2 n
  have hL : ∀ x ∈ L, x < 2 := fun x hx => Nat.digits_lt_base (by norm_num : 1 < 2) hx
  refine ⟨⟨BinaryRepresentation.bitsFromList L hL,
          BinaryRepresentation.bitsFromList_support_finite L hL, ?_⟩⟩
  rw [BinaryRepresentation.bitsFromList_sum_eq, Nat.ofDigits_digits]

/-- Helper: the support of bits i * 2^i is contained in the support of bits. -/
private lemma support_mul_pow_subset (bits : ℕ → Fin 2) :
    {i : ℕ | (bits i : ℕ) * 2^i ≠ 0} ⊆ {i | bits i ≠ 0} := by
  intro i hi
  simp only [Set.mem_ofPred_eq, ne_eq] at hi ⊢
  intro h
  apply hi
  simp [h]

/-- The least significant bit equals n mod 2. -/
private lemma bits_zero_eq_mod (n : ℕ) (r : BinaryRepresentation n) : (r.bits 0 : ℕ) = n % 2 := by
  have h := r.sum_eq
  have hfin : {i : ℕ | (r.bits i : ℕ) * 2^i ≠ 0}.Finite :=
    r.finite_support.subset (support_mul_pow_subset r.bits)
  have hdiv : ∀ i : ℕ, i ≥ 1 → 2 ∣ (r.bits i : ℕ) * 2^i := by
    intro i hi
    have : 2 ∣ 2^i := dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hi)
    exact Dvd.dvd.mul_left this (r.bits i : ℕ)
  have h_mod : (∑ᶠ i, (r.bits i : ℕ) * 2^i) % 2 = (r.bits 0 : ℕ) % 2 := by
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) (f := fun i => (r.bits i : ℕ) * 2^i)]
    · by_cases h0 : 0 ∈ hfin.toFinset
      · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem h0]
        simp only [pow_zero, mul_one]
        have hsum_div : 2 ∣ ∑ i ∈ hfin.toFinset \ {0}, (r.bits i : ℕ) * 2 ^ i := by
          apply Finset.dvd_sum
          intro i hi
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hi
          exact hdiv i (Nat.one_le_iff_ne_zero.mpr hi.2)
        have : (∑ i ∈ hfin.toFinset \ {0}, (r.bits i : ℕ) * 2 ^ i) % 2 = 0 :=
          Nat.mod_eq_zero_of_dvd hsum_div
        omega
      · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, pow_zero, mul_one, ne_eq,
                   not_not] at h0
        have hsum_div : 2 ∣ ∑ i ∈ hfin.toFinset, (r.bits i : ℕ) * 2 ^ i := by
          apply Finset.dvd_sum
          intro i hi
          simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ne_eq] at hi
          have hne : i ≠ 0 := by
            intro heq
            subst heq
            simp only [pow_zero, mul_one] at hi h0
            exact hi h0
          exact hdiv i (Nat.one_le_iff_ne_zero.mpr hne)
        have hsum_zero : (∑ i ∈ hfin.toFinset, (r.bits i : ℕ) * 2 ^ i) % 2 = 0 :=
          Nat.mod_eq_zero_of_dvd hsum_div
        simp only [h0, Nat.zero_mod]
        exact hsum_zero
    · intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      exact hfin.mem_toFinset.mpr hi
  rw [h] at h_mod
  have hlt : (r.bits 0 : ℕ) < 2 := (r.bits 0).isLt
  omega

/-- If the sum is 0, all bits must be 0. -/
private lemma bits_eq_zero_of_sum_eq_zero {r : BinaryRepresentation 0} (i : ℕ) : r.bits i = 0 := by
  by_contra h
  have hsum := r.sum_eq
  have hfin : {i : ℕ | (r.bits i : ℕ) * 2^i ≠ 0}.Finite :=
    r.finite_support.subset (support_mul_pow_subset r.bits)
  have hpos : (r.bits i : ℕ) * 2^i > 0 := by
    have hb : (r.bits i : ℕ) ≥ 1 := by
      simp only [Fin.ext_iff] at h
      omega
    positivity
  have hmem : i ∈ hfin.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ne_eq]
    omega
  have hsum_pos : ∑ j ∈ hfin.toFinset, (r.bits j : ℕ) * 2^j > 0 := by
    apply Finset.sum_pos'
    · intro j _
      positivity
    · exact ⟨i, hmem, hpos⟩
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)] at hsum
  · omega
  · intro j hj
    simp only [Function.mem_support, ne_eq] at hj
    exact hfin.mem_toFinset.mpr hj

/-- Sum decomposition: ∑ᶠ i, bits i * 2^i = bits 0 + 2 * ∑ᶠ i, bits (i+1) * 2^i -/
private lemma sum_decomposition (bits : ℕ → Fin 2) (hfin : {i | bits i ≠ 0}.Finite) :
    ∑ᶠ i, (bits i : ℕ) * 2^i = (bits 0 : ℕ) + 2 * (∑ᶠ i, (bits (i + 1) : ℕ) * 2^i) := by
  -- First rewrite the LHS as sum over {0} plus sum over positive naturals
  have huniv : (Set.univ : Set ℕ) = {0} ∪ Set.range Nat.succ := by
    ext n
    simp only [Set.mem_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_range, true_iff]
    cases n with
    | zero => left; rfl
    | succ n => right; exact ⟨n, rfl⟩
  -- Helper lemma: (bits i : ℕ) = 0 iff bits i = 0
  have hval_zero : ∀ i, (bits i : ℕ) = 0 ↔ bits i = 0 := by
    intro i
    constructor
    · intro h
      exact Fin.val_injective h
    · intro h
      simp [h]
  -- The support is finite
  have hsup : (Function.support (fun i => (bits i : ℕ) * 2^i)).Finite := by
    apply hfin.subset
    intro i hi
    simp only [Function.mem_support, ne_eq, Set.mem_ofPred_eq] at hi ⊢
    intro hb
    apply hi
    simp [hb]
  -- Rewrite as finsum over univ
  rw [← finsum_mem_univ (f := fun i => (bits i : ℕ) * 2^i)]
  rw [huniv]
  -- Split the union
  rw [finsum_mem_union']
  · -- Simplify the singleton sum
    simp only [finsum_mem_singleton, pow_zero, mul_one]
    congr 1
    -- The sum over range Nat.succ equals the shifted sum
    rw [finsum_mem_range Nat.succ_injective]
    -- Now we have ∑ᶠ j, bits (j + 1) * 2^(j + 1)
    -- Need to show this equals 2 * ∑ᶠ i, bits (i + 1) * 2^i
    have hfin_shift : (Function.support (fun i => (bits (i + 1) : ℕ) * 2^i)).Finite := by
      have hsub : Function.support (fun i => (bits (i + 1) : ℕ) * 2^i) ⊆
                  Nat.pred '' {i | bits i ≠ 0} := by
        intro i hi
        simp only [Function.mem_support, ne_eq] at hi
        simp only [Set.mem_image, Set.mem_ofPred_eq]
        use i + 1
        constructor
        · intro hb
          apply hi
          simp [hb]
        · simp
      exact (hfin.image _).subset hsub
    -- We have ∑ᶠ j, bits (j.succ) * 2^(j.succ) = ∑ᶠ j, bits (j + 1) * 2^(j + 1)
    -- And we want 2 * ∑ᶠ i, bits (i + 1) * 2^i
    -- Note that bits (j + 1) * 2^(j + 1) = 2 * bits (j + 1) * 2^j
    have heq : ∀ j, (bits j.succ : ℕ) * 2^j.succ = 2 * ((bits (j + 1) : ℕ) * 2^j) := by
      intro j
      simp only [Nat.succ_eq_add_one]
      ring
    conv_lhs =>
      arg 1
      ext j
      rw [heq j]
    -- Now we have ∑ᶠ j, 2 * (bits (j + 1) * 2^j) = 2 * ∑ᶠ i, bits (i + 1) * 2^i
    -- The support of 2 * f is the same as the support of f
    have hsup2 : (Function.support (fun i => 2 * ((bits (i + 1) : ℕ) * 2^i))).Finite := by
      apply hfin_shift.subset
      intro i hi
      simp only [Function.mem_support, ne_eq] at hi ⊢
      intro h
      apply hi
      omega
    have hsupeq : hsup2.toFinset = hfin_shift.toFinset := by
      ext i
      simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
      constructor
      · intro h1 h2
        apply h1
        omega
      · intro h1 h2
        apply h1
        simp only [mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false] at h2
        cases h2 with
        | inl h => exact absurd h (by norm_num)
        | inr h => simp [(hval_zero (i + 1)).mp h]
    rw [finsum_eq_sum _ hsup2, hsupeq]
    calc ∑ i ∈ hfin_shift.toFinset, 2 * ((bits (i + 1) : ℕ) * 2^i)
        = 2 * ∑ i ∈ hfin_shift.toFinset, (bits (i + 1) : ℕ) * 2^i := by rw [Finset.mul_sum]
      _ = 2 * ∑ᶠ i, (bits (i + 1) : ℕ) * 2^i := by rw [← finsum_eq_sum _ hfin_shift]
  · -- Disjoint
    simp only [Set.disjoint_singleton_left, Set.mem_range]
    intro ⟨n, hn⟩
    omega
  · -- Finite intersection for singleton
    exact Set.finite_singleton 0 |>.inter_of_left _
  · -- Finite intersection for range
    apply Set.Finite.subset hsup
    intro i hi
    obtain ⟨_, hi'⟩ := hi
    exact hi'

/-- The shifted representation gives a representation of n / 2. -/
private def BinaryRepresentation.shift {n : ℕ} (r : BinaryRepresentation n) :
    BinaryRepresentation (n / 2) where
  bits := fun i => r.bits (i + 1)
  finite_support := by
    have h := r.finite_support
    have hsub : {i | r.bits (i + 1) ≠ 0} ⊆ Nat.pred '' {i | r.bits i ≠ 0} := by
      intro i hi
      simp only [Set.mem_ofPred_eq, ne_eq] at hi
      simp only [Set.mem_image, Set.mem_ofPred_eq, ne_eq]
      use i + 1, hi
      rfl
    exact Set.Finite.subset (h.image _) hsub
  sum_eq := by
    have h := r.sum_eq
    have hb0 := bits_zero_eq_mod n r
    have hlt : (r.bits 0 : ℕ) < 2 := (r.bits 0).isLt
    have hdecomp := sum_decomposition r.bits r.finite_support
    have heq : n = (r.bits 0 : ℕ) + 2 * (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := by
      calc n = ∑ᶠ i, (r.bits i : ℕ) * 2^i := h.symm
           _ = (r.bits 0 : ℕ) + 2 * (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := hdecomp
    have hdiv2 : n / 2 = (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := by
      calc n / 2 = ((r.bits 0 : ℕ) + 2 * (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i)) / 2 := by rw [← heq]
           _ = (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := by
               rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
               simp only [Nat.div_eq_of_lt hlt, Nat.zero_add]
    exact hdiv2.symm

/-- The binary representation of a natural number is unique.
This is Theorem `thm.fps.laure.binary-rep-uniq`. -/
theorem binaryRepresentation_unique (n : ℕ) (r₁ r₂ : BinaryRepresentation n) :
    r₁.bits = r₂.bits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    funext i
    cases i with
    | zero =>
      have h1 := bits_zero_eq_mod n r₁
      have h2 := bits_zero_eq_mod n r₂
      ext
      omega
    | succ i =>
      by_cases hn : n = 0
      · subst hn
        have h1 := bits_eq_zero_of_sum_eq_zero (i + 1) (r := r₁)
        have h2 := bits_eq_zero_of_sum_eq_zero (i + 1) (r := r₂)
        rw [h1, h2]
      · have hdiv : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
        have hih := ih (n / 2) hdiv r₁.shift r₂.shift
        have : r₁.shift.bits i = r₂.shift.bits i := by rw [hih]
        simp only [BinaryRepresentation.shift] at this
        exact this

/-! ## Balanced Ternary Representation

A balanced ternary representation uses digits from {-1, 0, 1} with base 3.
Unlike binary representations, this can represent negative integers.
-/

/-- The set of balanced ternary digits: {-1, 0, 1} -/
inductive BalancedTernaryDigit : Type
  | negOne : BalancedTernaryDigit
  | zero : BalancedTernaryDigit
  | one : BalancedTernaryDigit
  deriving DecidableEq, Repr

namespace BalancedTernaryDigit

/-- Convert a balanced ternary digit to an integer -/
def toInt : BalancedTernaryDigit → ℤ
  | negOne => -1
  | zero => 0
  | one => 1

instance : Zero BalancedTernaryDigit := ⟨zero⟩

@[simp]
theorem toInt_zero : (0 : BalancedTernaryDigit).toInt = 0 := rfl

/-- Different digits have different integer values -/
theorem toInt_injective : Function.Injective toInt := by
  intro a b h
  cases a <;> cases b <;> simp [toInt] at h <;> rfl

/-- The range of toInt is {-1, 0, 1} -/
theorem toInt_range (d : BalancedTernaryDigit) : -1 ≤ d.toInt ∧ d.toInt ≤ 1 := by
  cases d <;> simp [toInt]

/-- Different digits have different residues mod 3 -/
theorem toInt_mod_three_injective :
    Function.Injective (fun d : BalancedTernaryDigit => d.toInt % 3) := by
  intro a b h
  cases a <;> cases b <;> simp [toInt] at h <;> native_decide

theorem eq_of_toInt_mod_three_eq (a b : BalancedTernaryDigit)
    (h : a.toInt % 3 = b.toInt % 3) : a = b :=
  toInt_mod_three_injective h

end BalancedTernaryDigit

/-- A balanced ternary representation of an integer `n` is an essentially finite
sequence `(b_i)_{i ∈ ℕ}` of elements in `{-1, 0, 1}` such that `n = ∑ b_i * 3^i`.

This corresponds to the Definition of balanced ternary representation in `sec.gf.laure`.
-/
structure BalancedTernaryRepresentation (n : ℤ) where
  /-- The sequence of digits -/
  digits : ℕ → BalancedTernaryDigit
  /-- Only finitely many digits are nonzero -/
  finite_support : {i | digits i ≠ 0}.Finite
  /-- The sum equals n -/
  sum_eq : ∑ᶠ i, (digits i).toInt * (3 : ℤ)^i = n

/-! ### Helper definitions and lemmas for balanced ternary existence proof -/

/-- A digit is nonzero iff its toInt is nonzero -/
theorem BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero (d : BalancedTernaryDigit) :
    d ≠ 0 ↔ d.toInt ≠ 0 := by
  cases d with
  | negOne => simp only [toInt, ne_eq]; decide
  | zero => simp only [toInt, ne_eq, not_true_eq_false, iff_false, not_not]; rfl
  | one => simp only [toInt, ne_eq]; decide

/-- Given n mod 3, return the unique balanced ternary digit d such that
    (n - d.toInt) is divisible by 3. -/
private def digitOfMod3 (r : ℤ) : BalancedTernaryDigit :=
  if r % 3 = 0 then .zero
  else if r % 3 = 1 ∨ r % 3 = -2 then .one
  else .negOne

private theorem digitOfMod3_spec (n : ℤ) : (n - (digitOfMod3 n).toInt) % 3 = 0 := by
  unfold digitOfMod3
  split_ifs with h1 h2
  · simp [BalancedTernaryDigit.toInt, h1]
  · simp only [BalancedTernaryDigit.toInt]
    rcases h2 with h2a | h2b <;> omega
  · simp only [BalancedTernaryDigit.toInt]
    have : n % 3 = 2 ∨ n % 3 = -1 := by
      have hmod := Int.emod_lt_of_pos n (by norm_num : (3 : ℤ) > 0)
      have hmod' := Int.emod_nonneg n (by norm_num : (3 : ℤ) ≠ 0)
      omega
    omega

private theorem abs_div_three_lt (n : ℤ) (hn : n ≠ 0) :
    |(n - (digitOfMod3 n).toInt) / 3| < |n| := by
  set d := digitOfMod3 n
  have hdiv : (n - d.toInt) % 3 = 0 := digitOfMod3_spec n
  have hd := BalancedTernaryDigit.toInt_range d
  have hdiv' : 3 ∣ (n - d.toInt) := Int.dvd_of_emod_eq_zero hdiv
  obtain ⟨q, hq⟩ := hdiv'
  have hq' : (n - d.toInt) / 3 = q := by rw [hq]; exact Int.mul_ediv_cancel_left q (by norm_num)
  rw [hq']
  have hn_eq : n = 3 * q + d.toInt := by omega
  by_cases hq0 : q = 0
  · simp [hq0] at hn_eq; simp [hq0]; omega
  · by_cases hqpos : q > 0
    · have h1 : 3 * q ≥ 3 := by omega
      have h2 : 3 * q + d.toInt ≥ 2 := by omega
      have h3' : 3 * q + d.toInt > 0 := by omega
      rw [abs_of_pos hqpos, hn_eq, abs_of_pos h3']; omega
    · push Not at hqpos
      have hqneg : q < 0 := by omega
      have h1 : 3 * q ≤ -3 := by omega
      have h2 : 3 * q + d.toInt ≤ -2 := by omega
      have h3' : 3 * q + d.toInt < 0 := by omega
      rw [abs_of_neg hqneg, hn_eq, abs_of_neg h3']; omega

/-- The zero representation for n = 0. -/
private def zeroRep : BalancedTernaryRepresentation 0 where
  digits := fun _ => 0
  finite_support := by simp only [ne_eq, not_true_eq_false, Set.ofPred_false, Set.finite_empty]
  sum_eq := by simp only [BalancedTernaryDigit.toInt_zero, zero_mul, finsum_zero]

/-- Helper: the digits function for prepending a digit. -/
private def prependDigits (d : BalancedTernaryDigit) (f : ℕ → BalancedTernaryDigit) :
    ℕ → BalancedTernaryDigit
  | 0 => d
  | i + 1 => f i

private theorem prependDigits_zero (d : BalancedTernaryDigit) (f : ℕ → BalancedTernaryDigit) :
    prependDigits d f 0 = d := rfl

private theorem prependDigits_succ (d : BalancedTernaryDigit) (f : ℕ → BalancedTernaryDigit)
    (i : ℕ) : prependDigits d f (i + 1) = f i := rfl

private theorem prependDigits_finite_support (d : BalancedTernaryDigit)
    (f : ℕ → BalancedTernaryDigit) (hf : {i | f i ≠ 0}.Finite) :
    {i | prependDigits d f i ≠ 0}.Finite := by
  have hsub : {i | prependDigits d f i ≠ 0} ⊆ {0} ∪ Nat.succ '' {i | f i ≠ 0} := by
    intro i hi
    simp only [Set.mem_ofPred_eq, ne_eq] at hi
    cases i with
    | zero => left; exact Set.mem_singleton 0
    | succ i =>
      right
      simp only [Set.mem_image, Set.mem_ofPred_eq, ne_eq]
      use i
      simp [prependDigits] at hi
      exact ⟨hi, rfl⟩
  exact Set.Finite.subset (Set.finite_singleton 0 |>.union (hf.image _)) hsub

private theorem prependDigits_sum (d : BalancedTernaryDigit) (f : ℕ → BalancedTernaryDigit)
    (hf : {i | f i ≠ 0}.Finite) :
    ∑ᶠ i, (prependDigits d f i).toInt * (3 : ℤ)^i =
    d.toInt + 3 * ∑ᶠ i, (f i).toInt * (3 : ℤ)^i := by
  let S := {0} ∪ Nat.succ '' (hf.toFinset : Set ℕ)
  have hS_fin : S.Finite := Set.finite_singleton 0 |>.union (Finset.finite_toSet _ |>.image _)
  have hsupp_sub : Function.support (fun i => (prependDigits d f i).toInt * (3 : ℤ)^i) ⊆
      hS_fin.toFinset := by
    intro i hi
    simp only [Function.mem_support, ne_eq, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      false_and, or_false, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_image, Finset.mem_coe, S] at hi ⊢
    cases i with
    | zero => left; rfl
    | succ i =>
      right; use i; simp [prependDigits] at hi
      refine ⟨?_, rfl⟩
      simp only [Set.mem_ofPred_eq]
      exact (BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero _).mpr hi
  rw [finsum_eq_sum_of_support_subset _ hsupp_sub]
  have hS_eq : hS_fin.toFinset = {0} ∪ (hf.toFinset.image Nat.succ) := by
    ext i; simp [Set.Finite.mem_toFinset, Set.mem_image, Finset.mem_image, S]
  rw [hS_eq]
  have h0_not_in_image : (0 : ℕ) ∉ hf.toFinset.image Nat.succ := by
    simp only [Finset.mem_image, not_exists, not_and]; intro i _ h; omega
  rw [Finset.sum_union (Finset.disjoint_singleton_left.mpr h0_not_in_image)]
  simp only [Finset.sum_singleton, prependDigits_zero, pow_zero, mul_one]
  rw [Finset.sum_image (fun i _ j _ h => Nat.succ_injective h)]
  have hsum_eq : ∑ i ∈ hf.toFinset, (prependDigits d f (i + 1)).toInt * (3 : ℤ)^(i + 1) =
                 ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^(i + 1) := by
    apply Finset.sum_congr rfl; intro i _; simp [prependDigits_succ]
  rw [hsum_eq]
  have hfactor : ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^(i + 1) =
                 3 * ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hfactor]
  have hfinsum_eq : ∑ᶠ i, (f i).toInt * (3 : ℤ)^i =
      ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^i := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Function.mem_support, ne_eq, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      false_and, or_false] at hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact (BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero _).mpr hi
  simp only [hfinsum_eq]

/-- Prepend a digit to a representation, scaling by 3. -/
private def prependDigit (d : BalancedTernaryDigit) {m : ℤ}
    (r : BalancedTernaryRepresentation m) :
    BalancedTernaryRepresentation (d.toInt + 3 * m) where
  digits := prependDigits d r.digits
  finite_support := prependDigits_finite_support d r.digits r.finite_support
  sum_eq := by rw [prependDigits_sum d r.digits r.finite_support, r.sum_eq]

private theorem natAbs_of_nonneg_eq_toNat (m : ℤ) (hm : 0 ≤ m) : m.natAbs = m.toNat := by
  have h1 : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm
  have h2 : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
  omega

private theorem natAbs_lt_of_abs_lt (m n : ℤ) (h : |m| < |n|) (hn0 : n ≠ 0) :
    m.natAbs < n.natAbs := by
  rw [← Int.natAbs_abs m, ← Int.natAbs_abs n]
  have hm_nn : 0 ≤ |m| := abs_nonneg m
  have hn_nn : 0 ≤ |n| := abs_nonneg n
  have hn_pos : 0 < |n| := abs_pos.mpr hn0
  rw [natAbs_of_nonneg_eq_toNat |m| hm_nn, natAbs_of_nonneg_eq_toNat |n| hn_nn]
  rw [Int.toNat_lt_toNat hn_pos]
  exact h

/-- Every integer has a balanced ternary representation.
This is part of Theorem `thm.fps.laure.balanced-tern-rep-uniq`. -/
theorem balancedTernaryRepresentation_exists (n : ℤ) :
    Nonempty (BalancedTernaryRepresentation n) := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | _ k ih =>
    by_cases hn0 : n = 0
    · subst hn0; exact ⟨zeroRep⟩
    · set d := digitOfMod3 n with hd_def
      set m := (n - d.toInt) / 3 with hm_def
      have hdiv : (n - d.toInt) % 3 = 0 := digitOfMod3_spec n
      have hm_abs : |m| < |n| := abs_div_three_lt n hn0
      have hm_nat : m.natAbs < k := by
        rw [← hn]
        exact natAbs_lt_of_abs_lt m n hm_abs hn0
      have ih_m := ih m.natAbs hm_nat m rfl
      obtain ⟨r⟩ := ih_m
      have hn_eq : n = d.toInt + 3 * m := by
        have hdiv' : 3 ∣ (n - d.toInt) := Int.dvd_of_emod_eq_zero hdiv
        obtain ⟨q, hq⟩ := hdiv'
        have : m = q := by simp only [hm_def, hq]; exact Int.mul_ediv_cancel_left q (by norm_num)
        omega
      rw [hn_eq]
      exact ⟨prependDigit d r⟩

/-- Key lemma: if sum of c_i * 3^i = 0 where c_i ∈ {-2,...,2} and only finitely many nonzero,
then all c_i = 0. This is the core uniqueness argument for balanced ternary representations. -/
private lemma sum_powers_of_three_eq_zero_aux (k : ℕ) (c : ℕ → ℤ)
    (hc : ∀ i ≤ k, -2 ≤ c i ∧ c i ≤ 2)
    (hzero : ∀ i > k, c i = 0)
    (hsum : ∑ i ∈ Finset.range (k + 1), c i * (3 : ℤ)^i = 0) :
    ∀ i, c i = 0 := by
  induction k generalizing c with
  | zero =>
    intro i
    cases i with
    | zero =>
      simp at hsum
      have hc0 := hc 0 (le_refl 0)
      omega
    | succ j =>
      exact hzero (j + 1) (by omega)
  | succ k' ih =>
    -- c 0 must be 0 mod 3, so c 0 ∈ {-2,-1,0,1,2} ∩ 3ℤ = {0}
    have hmod : (∑ i ∈ Finset.range (k' + 2), c i * (3 : ℤ)^i) % 3 = 0 := by
      rw [hsum]
      simp
    rw [Finset.sum_range_succ'] at hmod
    simp only [pow_zero, mul_one] at hmod
    have hrest : (∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^(i + 1)) % 3 = 0 := by
      rw [Finset.sum_int_mod]
      have h1 : ∀ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^(i + 1) % 3 = 0 := by
        intro i _
        simp only [pow_succ]
        have h3 : (3 : ℤ) ^ i * 3 % 3 = 0 := by simp
        rw [Int.mul_emod, h3, mul_zero, Int.zero_emod]
      rw [Finset.sum_eq_zero h1]
      simp
    rw [Int.add_emod, hrest, zero_add] at hmod
    have hc0 := hc 0 (by omega)
    have hc0_mod : c 0 % 3 = 0 := by
      rw [Int.emod_emod_of_dvd] at hmod
      · exact hmod
      · norm_num
    have hc0_zero : c 0 = 0 := by omega
    -- Factor out 3 from the remaining sum
    rw [Finset.sum_range_succ'] at hsum
    simp only [pow_zero, mul_one, hc0_zero] at hsum
    have hfactor : ∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^(i + 1) =
                   3 * ∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfactor] at hsum
    have hc_sum' : ∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^i = 0 := by
      have h3ne : (3 : ℤ) ≠ 0 := by norm_num
      have : 3 * ∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^i + 0 = 0 := hsum
      linarith [mul_eq_zero.mp (by linarith : 3 * ∑ i ∈ Finset.range (k' + 1), c (i + 1) * (3 : ℤ)^i = 0)]
    -- Apply IH to the shifted sequence c' i = c (i + 1)
    let c' : ℕ → ℤ := fun i => c (i + 1)
    have hc'_bound : ∀ i ≤ k', -2 ≤ c' i ∧ c' i ≤ 2 := fun i hi => hc (i + 1) (by omega)
    have hc'_zero : ∀ i > k', c' i = 0 := fun i hi => hzero (i + 1) (by omega)
    have ih' := ih c' hc'_bound hc'_zero hc_sum'
    intro i
    cases i with
    | zero => exact hc0_zero
    | succ j => exact ih' j

/-- The balanced ternary representation of an integer is unique.
This is Theorem `thm.fps.laure.balanced-tern-rep-uniq`. -/
theorem balancedTernaryRepresentation_unique (n : ℤ)
    (r₁ r₂ : BalancedTernaryRepresentation n) : r₁.digits = r₂.digits := by
  -- Get bounds on the support
  obtain ⟨k₁, hk₁⟩ := r₁.finite_support.bddAbove
  obtain ⟨k₂, hk₂⟩ := r₂.finite_support.bddAbove
  let k := max k₁ k₂
  -- Both are k-bounded
  have h₁ : ∀ i > k, r₁.digits i = 0 := by
    intro i hi
    by_contra hc
    have : i ≤ k₁ := hk₁ hc
    omega
  have h₂ : ∀ i > k, r₂.digits i = 0 := by
    intro i hi
    by_contra hc
    have : i ≤ k₂ := hk₂ hc
    omega
  -- Convert finsum to finite sum
  have sum₁ : n = ∑ i ∈ Finset.range (k + 1), (r₁.digits i).toInt * (3 : ℤ)^i := by
    conv_lhs => rw [← r₁.sum_eq]
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    push Not at hc
    have hd : r₁.digits i = 0 := h₁ i hc
    change (r₁.digits i).toInt * (3 : ℤ)^i ≠ 0 at hi
    rw [hd, BalancedTernaryDigit.toInt_zero, zero_mul] at hi
    exact hi rfl
  have sum₂ : n = ∑ i ∈ Finset.range (k + 1), (r₂.digits i).toInt * (3 : ℤ)^i := by
    conv_lhs => rw [← r₂.sum_eq]
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hc
    push Not at hc
    have hd : r₂.digits i = 0 := h₂ i hc
    change (r₂.digits i).toInt * (3 : ℤ)^i ≠ 0 at hi
    rw [hd, BalancedTernaryDigit.toInt_zero, zero_mul] at hi
    exact hi rfl
  -- Define the difference
  let c : ℕ → ℤ := fun i => (r₁.digits i).toInt - (r₂.digits i).toInt
  have hc_bound : ∀ i ≤ k, -2 ≤ c i ∧ c i ≤ 2 := by
    intro i _
    have h1 := BalancedTernaryDigit.toInt_range (r₁.digits i)
    have h2 := BalancedTernaryDigit.toInt_range (r₂.digits i)
    simp only [c]
    constructor <;> omega
  have hc_zero : ∀ i > k, c i = 0 := by
    intro i hi
    simp only [c]
    rw [h₁ i hi, h₂ i hi]
    simp
  have hc_sum : ∑ i ∈ Finset.range (k + 1), c i * (3 : ℤ)^i = 0 := by
    simp only [c]
    have : ∑ i ∈ Finset.range (k + 1), ((r₁.digits i).toInt - (r₂.digits i).toInt) * (3 : ℤ)^i =
           ∑ i ∈ Finset.range (k + 1), (r₁.digits i).toInt * (3 : ℤ)^i -
           ∑ i ∈ Finset.range (k + 1), (r₂.digits i).toInt * (3 : ℤ)^i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this, ← sum₁, ← sum₂]
    ring
  -- Apply the key lemma
  have hall := sum_powers_of_three_eq_zero_aux k c hc_bound hc_zero hc_sum
  -- Conclude that all digits are equal
  ext i
  have hi := hall i
  simp only [c] at hi
  have hr1 := BalancedTernaryDigit.toInt_range (r₁.digits i)
  have hr2 := BalancedTernaryDigit.toInt_range (r₂.digits i)
  apply BalancedTernaryDigit.toInt_injective
  omega

/-! ## Doubly Infinite Power Series

The K-module K[[x^±]] of all families (a_n)_{n ∈ ℤ} of elements of K.
This is the largest space allowing negative powers of x, but it does not
have a well-defined multiplication in general.

This corresponds to Definition `def.fps.laure.double`.
-/

/-- The K-module of doubly infinite power series K[[x^±]].

An element is a family `(a_n)_{n ∈ ℤ}` of elements of K. Addition and scalar
multiplication are defined entrywise.

Note: This is NOT a ring because multiplication is not always well-defined
(the convolution sum may be infinite).

This corresponds to Definition `def.fps.laure.double`.
-/
def DoublyInfinitePowerSeries (K : Type*) [Semiring K] := ℤ → K

namespace DoublyInfinitePowerSeries

variable {K : Type*} [Semiring K]

instance : AddCommMonoid (DoublyInfinitePowerSeries K) := Pi.addCommMonoid

instance : Module K (DoublyInfinitePowerSeries K) := Pi.module _ _ _

/-- The coefficient of x^n in a doubly infinite power series -/
def coeff (f : DoublyInfinitePowerSeries K) (n : ℤ) : K := f n

/-- Two doubly infinite power series are equal iff all their coefficients are equal -/
@[ext]
theorem ext {f g : DoublyInfinitePowerSeries K} (h : ∀ n, coeff f n = coeff g n) : f = g :=
  funext h

@[simp]
theorem coeff_add (f g : DoublyInfinitePowerSeries K) (n : ℤ) :
    coeff (f + g) n = coeff f n + coeff g n := rfl

@[simp]
theorem coeff_smul (r : K) (f : DoublyInfinitePowerSeries K) (n : ℤ) :
    coeff (r • f) n = r * coeff f n := rfl

/-- The element x^n in K[[x^±]], represented as a family -/
def single (n : ℤ) : DoublyInfinitePowerSeries K := fun m => if m = n then 1 else 0

@[simp]
theorem coeff_single (n m : ℤ) : coeff (single n : DoublyInfinitePowerSeries K) m =
    if m = n then 1 else 0 := rfl

/-- The zero element of K[[x^±]] has all coefficients zero.
This is part of Definition `def.fps.laure.double`. -/
@[simp]
theorem coeff_zero (n : ℤ) : coeff (0 : DoublyInfinitePowerSeries K) n = 0 := rfl

/-- The single at 0 with coefficient 1 represents 1 (as a constant series). -/
@[simp]
theorem single_zero_eq_one : (single 0 : DoublyInfinitePowerSeries K) = fun n => if n = 0 then 1 else 0 := rfl

/-- Coefficient of single n at n is 1. -/
@[simp]
theorem coeff_single_self (n : ℤ) : coeff (single n : DoublyInfinitePowerSeries K) n = 1 := by
  simp [coeff_single]

/-- Coefficient of single n at m ≠ n is 0. -/
@[simp]
theorem coeff_single_ne {n m : ℤ} (h : m ≠ n) :
    coeff (single n : DoublyInfinitePowerSeries K) m = 0 := by
  simp [coeff_single, h]

/-- Scalar multiplication of single. -/
@[simp]
theorem smul_single (r : K) (n : ℤ) :
    r • (single n : DoublyInfinitePowerSeries K) = fun m => if m = n then r else 0 := by
  funext m
  show r * (if m = n then 1 else 0) = if m = n then r else 0
  split_ifs with h
  · simp
  · simp

/-- Any doubly infinite power series f equals (coeff f n) at position n.
This is the pointwise characterization of the notation ∑_{n∈ℤ} a_n x^n:
at each position m, the coefficient is a_m.

This formalizes the representation mentioned at the end of Definition `def.fps.laure.double`:
"we will later use the notation ∑_{n∈ℤ} a_n x^n for a family (a_n)_{n∈ℤ}".

Note: This is a formal identity of families. The "sum" is well-defined because
at each coefficient position m, only the term n = m contributes. -/
theorem eq_coeff_at_position (f : DoublyInfinitePowerSeries K) (m : ℤ) :
    f m = coeff f m := rfl

/-- The representation f = ∑_{n∈ℤ} (coeff f n) · x^n holds pointwise:
at position m, f m = (coeff f m) · 1 + ∑_{n≠m} (coeff f n) · 0 = coeff f m. -/
theorem coeff_eq_single_contrib (f : DoublyInfinitePowerSeries K) (m : ℤ) :
    coeff f m = coeff f m * coeff (single m : DoublyInfinitePowerSeries K) m := by
  simp

/-- A doubly infinite power series is a Laurent series if the sequence of negative
coefficients (a_{-1}, a_{-2}, a_{-3}, ...) is essentially finite, i.e., all
sufficiently negative indices have zero coefficient.

This is Definition `def.fps.laure.lauser` from the textbook:
We let K((x)) be the subset of K[[x^±]] consisting of all families (a_i)_{i∈ℤ}
such that the sequence (a_{-1}, a_{-2}, a_{-3}, ...) is essentially finite --
i.e., such that all sufficiently low i ∈ ℤ satisfy a_i = 0.

The elements of K((x)) are called Laurent series in one indeterminate x over K. -/
def IsLaurentSeries (f : DoublyInfinitePowerSeries K) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n < N → coeff f n = 0

/-- The support of a Laurent series is bounded below. -/
theorem IsLaurentSeries.support_bddBelow {f : DoublyInfinitePowerSeries K}
    (hf : IsLaurentSeries f) : BddBelow {n : ℤ | coeff f n ≠ 0} := by
  obtain ⟨N, hN⟩ := hf
  use N
  intro n hn
  by_contra h
  push Not at h
  exact hn (hN n h)

/-- Convert a Mathlib LaurentSeries to a DoublyInfinitePowerSeries -/
def ofLaurentSeries (f : LaurentSeries K) : DoublyInfinitePowerSeries K :=
  fun n => f.coeff n

/-- A Mathlib LaurentSeries satisfies our IsLaurentSeries predicate.

This shows that Mathlib's definition of LaurentSeries (as HahnSeries ℤ K)
matches the textbook Definition `def.fps.laure.lauser`. -/
theorem isLaurentSeries_ofLaurentSeries (f : LaurentSeries K) :
    IsLaurentSeries (ofLaurentSeries f) := by
  have h := f.isPWO_support
  by_cases hne : f.support.Nonempty
  · have hmin := h.isWF.min_mem hne
    use h.isWF.min hne
    intro n hn
    unfold ofLaurentSeries coeff
    by_contra h'
    have hmem : n ∈ f.support := by
      simp only [HahnSeries.mem_support]
      exact h'
    exact not_lt.mpr (h.isWF.min_le hne hmem) hn
  · use 0
    intro n _
    unfold ofLaurentSeries coeff
    simp only [Set.not_nonempty_iff_eq_empty, HahnSeries.support_eq_empty_iff] at hne
    simp only [hne, HahnSeries.coeff_zero]

/-- For ℤ, a set bounded below is partially well-ordered.

This follows from the fact that any sequence in ℤ bounded below has a monotone
subsequence (by Ramsey's theorem / infinite pigeonhole). -/
theorem Int.isPWO_of_bddBelow {s : Set ℤ} (hs : BddBelow s) : s.IsPWO := by
  obtain ⟨N, hN⟩ := hs
  rw [Set.isPWO_iff_exists_monotone_subseq]
  intro g hg
  -- g : ℕ → ℤ with values in s
  -- Consider h : ℕ → ℕ defined by h(n) = (g(n) - N).toNat
  let h : ℕ → ℕ := fun n => (g n - N).toNat
  -- Any sequence in ℕ has a monotone or antitone subsequence (Ramsey)
  have ⟨φ, hφ⟩ := exists_increasing_or_nonincreasing_subseq (α := ℕ) (r := (· ≤ ·)) h
  rcases hφ with hφ_mono | hφ_anti
  · -- Increasing case
    use φ
    intro i j hij
    have hi := hg (φ i)
    have hj := hg (φ j)
    have hNi : N ≤ g (φ i) := hN hi
    have hNj : N ≤ g (φ j) := hN hj
    rcases hij.lt_or_eq with hij' | rfl
    · have hmono := hφ_mono i j hij'
      simp only [h] at hmono
      have h1 : 0 ≤ g (φ i) - N := by omega
      have h2 : 0 ≤ g (φ j) - N := by omega
      have h3 : (g (φ i) - N).toNat ≤ (g (φ j) - N).toNat := hmono
      have h4 : g (φ i) - N ≤ g (φ j) - N := by
        calc g (φ i) - N = ((g (φ i) - N).toNat : ℤ) := (Int.toNat_of_nonneg h1).symm
          _ ≤ ((g (φ j) - N).toNat : ℤ) := by exact_mod_cast h3
          _ = g (φ j) - N := Int.toNat_of_nonneg h2
      -- Now we need g (φ i) ≤ g (φ j), which follows from h4
      have : g (φ i) ≤ g (φ j) := by linarith
      exact this
    · rfl
  · -- Non-increasing (decreasing) case
    -- In ℕ, a strictly decreasing sequence can't exist infinitely
    exfalso
    -- Build a strictly decreasing sequence in ℕ
    have hdec : ∀ m n, m < n → h (φ n) < h (φ m) := fun m n hmn => by
      have := hφ_anti m n hmn
      omega
    -- Infinite strictly decreasing sequence in ℕ is impossible
    -- h(φ 0) > h(φ 1) > h(φ 2) > ... but all are ≥ 0
    have : ∀ n, h (φ n) + n ≤ h (φ 0) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have hk := hdec k (k + 1) (Nat.lt_succ_self k)
        omega
    have := this (h (φ 0) + 1)
    omega

/-- Convert a DoublyInfinitePowerSeries satisfying IsLaurentSeries to a Mathlib LaurentSeries -/
def toLaurentSeries (f : DoublyInfinitePowerSeries K) (hf : IsLaurentSeries f) :
    LaurentSeries K := by
  refine ⟨fun n => coeff f n, ?_⟩
  apply Int.isPWO_of_bddBelow
  obtain ⟨N, hN⟩ := hf
  use N
  intro n hn
  -- hn : n ∈ {n | coeff f n ≠ 0}
  change coeff f n ≠ 0 at hn
  by_contra h
  push Not at h
  exact hn (hN n h)

/-- The round-trip from LaurentSeries to DoublyInfinitePowerSeries and back gives the same series -/
theorem toLaurentSeries_ofLaurentSeries (f : LaurentSeries K) :
    toLaurentSeries (ofLaurentSeries f) (isLaurentSeries_ofLaurentSeries f) = f := by
  ext n
  rfl

/-- The round-trip from DoublyInfinitePowerSeries to LaurentSeries and back gives the same function -/
theorem ofLaurentSeries_toLaurentSeries (f : DoublyInfinitePowerSeries K)
    (hf : IsLaurentSeries f) :
    ofLaurentSeries (toLaurentSeries f hf) = f := by
  funext n
  rfl

end DoublyInfinitePowerSeries

/-! ## Laurent Polynomials

The K-algebra K[x^±] of Laurent polynomials consists of essentially finite
families (a_n)_{n ∈ ℤ}. Unlike K[[x^±]], this IS a ring.

We use Mathlib's `LaurentPolynomial` which is defined as `AddMonoidAlgebra R ℤ`.

This corresponds to Definition `def.fps.laure.laupol`.

### Theorem `thm.fps.laure.laupol-ring`

The K-module K[x^±], equipped with the convolution multiplication, is a commutative
K-algebra. Its unity is `(δ_{i,0})_{i∈ℤ}`. The element x (represented as T 1) is
invertible in this K-algebra.

This is fully formalized below using Mathlib's `LaurentPolynomial` type.
-/

section LaurentPolynomials

variable (K : Type*) [CommSemiring K]

/-! ### Part 1: K[x^±] is a commutative K-algebra

The Laurent polynomial ring K[x^±] is a commutative semiring (and a commutative ring
when K is a ring). It is also a K-algebra.

In Mathlib, this is established via `AddMonoidAlgebra.instCommSemiring` and related instances.
-/

/-- Laurent polynomials form a commutative semiring.
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
instance laurentPolynomial_commSemiring : CommSemiring K[T;T⁻¹] := inferInstance

/-- Laurent polynomials form a K-algebra.
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
instance laurentPolynomial_algebra : Algebra K K[T;T⁻¹] := inferInstance

/-! ### Part 2: The unity is (δ_{i,0})_{i∈ℤ}

The multiplicative identity in K[x^±] is the family that is 1 at index 0 and 0 elsewhere.
In Mathlib, this is `LaurentPolynomial.T 0 = 1`.
-/

/-- The unity of K[x^±] is T 0 = (δ_{i,0})_{i∈ℤ}.
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
theorem laurentPolynomial_one_eq_T_zero : (1 : K[T;T⁻¹]) = LaurentPolynomial.T 0 := rfl

/-- The unity of K[x^±] evaluated at index n is 1 if n = 0, else 0.
This is the explicit characterization from Theorem `thm.fps.laure.laupol-ring`. -/
@[simp]
theorem laurentPolynomial_one_apply (n : ℤ) : (1 : K[T;T⁻¹]).coeff n = if n = 0 then 1 else 0 := by
  simp only [laurentPolynomial_one_eq_T_zero K, LaurentPolynomial.T_apply]
  simp only [eq_comm]

/-! ### Part 3: The element x is invertible

The element x (represented as T 1 in Mathlib) is a unit in K[x^±], with inverse x⁻¹ = T (-1).
-/

/-- The element T 1 (corresponding to x) is invertible in K[T;T⁻¹].
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
theorem laurentPolynomial_T_isUnit : IsUnit (LaurentPolynomial.T 1 : K[T;T⁻¹]) :=
  LaurentPolynomial.isUnit_T 1

/-- More generally, T n is invertible for any n ∈ ℤ.
This generalizes the invertibility statement in Theorem `thm.fps.laure.laupol-ring`. -/
theorem laurentPolynomial_T_isUnit' (n : ℤ) : IsUnit (LaurentPolynomial.T n : K[T;T⁻¹]) :=
  LaurentPolynomial.isUnit_T n

/-- The inverse of T n is T (-n).
This is the explicit inverse formula from Theorem `thm.fps.laure.laupol-ring`. -/
@[simp]
theorem laurentPolynomial_T_mul_T_neg (n : ℤ) :
    (LaurentPolynomial.T n : K[T;T⁻¹]) * LaurentPolynomial.T (-n) = 1 := by
  rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

/-- The inverse of T n is T (-n) (multiplication in the other order).
This is the explicit inverse formula from Theorem `thm.fps.laure.laupol-ring`. -/
@[simp]
theorem laurentPolynomial_T_neg_mul_T (n : ℤ) :
    (LaurentPolynomial.T (-n) : K[T;T⁻¹]) * LaurentPolynomial.T n = 1 := by
  rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

/-- The unit associated to T n, with explicit inverse T (-n). -/
def laurentPolynomial_T_unit (n : ℤ) : (K[T;T⁻¹])ˣ where
  val := LaurentPolynomial.T n
  inv := LaurentPolynomial.T (-n)
  val_inv := laurentPolynomial_T_mul_T_neg K n
  inv_val := laurentPolynomial_T_neg_mul_T K n

/-! ### Representation as sum

Any Laurent polynomial f = (a_i)_{i ∈ ℤ} satisfies f = ∑_{i ∈ support f} a_i T^i.
-/

/-- Any Laurent polynomial f = (a_i)_{i ∈ ℤ} satisfies f = ∑_{i ∈ support f} a_i T^i.
This is Proposition `prop.fps.laure.a=sumaixi`.

Here we state this for Laurent polynomials, where the sum is finite. -/
theorem laurentPolynomial_eq_sum (f : K[T;T⁻¹]) :
    f = f.coeff.sum fun n a => LaurentPolynomial.C a * LaurentPolynomial.T n := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  congr 1
  funext n a
  exact LaurentPolynomial.single_eq_C_mul_T a n

/-! ### Alternative characterizations

The Laurent polynomial ring K[x^±] can equivalently be described as:
- The group algebra of ℤ over K
- The localization of K[x] at the powers of x

These are mentioned in the textbook after Theorem `thm.fps.laure.laupol-ring`.
-/

/-- K[x^±] is isomorphic to the group algebra K[ℤ].
This is one of the alternative characterizations mentioned after Theorem `thm.fps.laure.laupol-ring`. -/
theorem laurentPolynomial_eq_groupAlgebra :
    K[T;T⁻¹] = AddMonoidAlgebra K ℤ := rfl

end LaurentPolynomials

section LaurentPolynomialsCommRing

variable (K : Type*) [CommRing K]

/-- When K is a CommRing, Laurent polynomials form a CommRing.
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
instance laurentPolynomial_commRing : CommRing K[T;T⁻¹] := inferInstance

end LaurentPolynomialsCommRing

/-! ## Laurent Series

The K-algebra K((x)) of Laurent series consists of families (a_n)_{n ∈ ℤ}
such that a_n = 0 for all sufficiently negative n.

We use Mathlib's `LaurentSeries` which is defined as `HahnSeries ℤ R`.

This corresponds to Definition `def.fps.laure.lauser`.
-/

section LaurentSeriesSection

variable (K : Type*) [CommRing K]

/-- Laurent series form a commutative K-algebra with unity.
This is Theorem `thm.fps.laure.lauser-ring`.

In Mathlib, this is established via `HahnSeries.instCommRing` and related instances. -/
example : CommRing (LaurentSeries K) := inferInstance

example : Algebra K (LaurentSeries K) := inferInstance

/-- The FPS ring K[[x]] embeds into the Laurent series ring K((x)).
This is mentioned after Theorem `thm.fps.laure.lauser-ring`. -/
example : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K

/-- Helper monoid homomorphism: maps n ∈ ℤ (as a multiplicative element) to the single
Hahn series x^n. This is used to construct the Laurent polynomial embedding. -/
private def singleMonoidHom : Multiplicative ℤ →* LaurentSeries K where
  toFun n := HahnSeries.single (Multiplicative.toAdd n) 1
  map_one' := rfl
  map_mul' := by
    intro x y
    have h : Multiplicative.toAdd (x * y) = Multiplicative.toAdd x + Multiplicative.toAdd y := rfl
    simp only [h, HahnSeries.single_mul_single, one_mul]

/-- The ring homomorphism from Laurent polynomials to Laurent series.
This embeds K[x^±] into K((x)) by mapping each Laurent polynomial to the corresponding
Laurent series with the same coefficients.

This is mentioned after Theorem `thm.fps.laure.lauser-ring`. -/
def laurentPolyToSeries : K[T;T⁻¹] →+* LaurentSeries K :=
  AddMonoidAlgebra.liftNCRingHom HahnSeries.C (singleMonoidHom K)
    (by
      intro x y
      simp only [HahnSeries.C, singleMonoidHom, Commute, SemiconjBy]
      simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [HahnSeries.single_mul_single, HahnSeries.single_mul_single]
      simp [add_comm])

/-- The Laurent polynomial to series map sends single n r to single n r. -/
theorem laurentPolyToSeries_single (n : ℤ) (r : K) :
    laurentPolyToSeries K (AddMonoidAlgebra.single n r) = HahnSeries.single n r := by
  unfold laurentPolyToSeries
  simp only [AddMonoidAlgebra.liftNCRingHom_single]
  simp only [singleMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk, HahnSeries.C]
  change HahnSeries.single 0 r * HahnSeries.single n 1 = HahnSeries.single n r
  rw [HahnSeries.single_mul_single]
  simp only [zero_add, mul_one]

/-- The Laurent polynomial to series map preserves coefficients. -/
theorem laurentPolyToSeries_coeff (f : K[T;T⁻¹]) (n : ℤ) :
    (laurentPolyToSeries K f).coeff n = f.coeff n := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single f]
  rw [Finsupp.sum, map_sum]
  rw [HahnSeries.coeff_sum]
  simp_rw [laurentPolyToSeries_single, HahnSeries.coeff_single]
  by_cases hn : n ∈ f.coeff.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hbn
      simp [hbn.symm]
    · intro h
      exact absurd hn h
  · rw [Finset.sum_eq_zero]
    · simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hn
      exact hn.symm
    · intro x hx
      simp only [Finsupp.mem_support_iff, ne_eq] at hn hx
      by_cases hxn : n = x
      · subst hxn
        exact absurd hx hn
      · simp [hxn]

/-- The Laurent polynomial to series map is injective. -/
theorem laurentPolyToSeries_injective : Function.Injective (laurentPolyToSeries K) := by
  intro f g hfg
  ext n
  rw [← laurentPolyToSeries_coeff K f n, ← laurentPolyToSeries_coeff K g n, hfg]

/-- The Laurent polynomial ring K[x^±] can be embedded into the Laurent series ring K((x)).
This is mentioned after Theorem `thm.fps.laure.lauser-ring`. -/
theorem laurentPolynomial_embeds_in_laurentSeries :
    ∃ (f : K[T;T⁻¹] →+* LaurentSeries K), Function.Injective f :=
  ⟨laurentPolyToSeries K, laurentPolyToSeries_injective K⟩

/-- For any positive integer i, the power series 1 - x^i is invertible in K[[x]]
and hence also in K((x)). This allows the computation in the proof of
Theorem `thm.fps.laure.balanced-tern-rep-uniq`. -/
theorem one_sub_X_pow_isUnit (i : ℕ) (hi : 0 < i) :
    IsUnit (1 - (PowerSeries.X : PowerSeries K)^i) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp only [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X,
    zero_pow (Nat.ne_of_gt hi), sub_zero, isUnit_one]

end LaurentSeriesSection

/-! ## Module Structure on K[[x^±]]

While K[[x^±]] is not a ring, it has a K[x^±]-module structure.
A Laurent polynomial can be multiplied with any doubly infinite power series.

This corresponds to the discussion in "A K[x^±]-module structure on K[[x^±]]".
-/

section ModuleStructure

variable {K : Type*} [CommRing K] [Nontrivial K]

/-- The action of a Laurent polynomial on a doubly infinite power series.

The product (∑ b_n x^n) · (∑ a_n x^n) = (∑ c_n x^n) where c_n = ∑_{i ∈ ℤ} a_i b_{n-i}.
This sum is finite because the Laurent polynomial has finite support.

This makes K[[x^±]] into a K[x^±]-module. -/
def laurentPolynomialSmul (p : K[T;T⁻¹]) (f : DoublyInfinitePowerSeries K) :
    DoublyInfinitePowerSeries K :=
  fun n => p.coeff.sum fun i b => b * f (n - i)

/-- The multiplication (1-x) · (∑_{n ∈ ℤ} x^n) = 0 shows that K[[x^±]] has torsion
as a K[x^±]-module. This is the calculation showing why we cannot divide by (1-x)
in K[[x^±]].

This corresponds to the discussion at the end of the section. -/
theorem torsion_example :
    ∃ (p : K[T;T⁻¹]) (f : DoublyInfinitePowerSeries K),
      p ≠ 0 ∧ f ≠ 0 ∧ laurentPolynomialSmul p f = 0 := by
  -- p = 1 - T 1 = 1 - x
  -- f = fun _ => 1 (the constant 1 function, representing ∑_{n ∈ ℤ} x^n)
  use 1 - LaurentPolynomial.T 1
  use fun _ => 1
  refine ⟨?_, ?_, ?_⟩
  · -- Show p ≠ 0
    intro h
    have h0 : ((1 : K[T;T⁻¹]) - (LaurentPolynomial.T 1 : K[T;T⁻¹])).coeff 0 = 0 := by
      rw [h]; rfl
    have h1 : (1 : K[T;T⁻¹]).coeff 0 = 1 := by
      rw [laurentPolynomial_one_apply]; simp
    have hT : (LaurentPolynomial.T 1 : K[T;T⁻¹]).coeff 0 = 0 := by
      simp [LaurentPolynomial.T_apply]
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, h1, hT, sub_zero] at h0
    exact one_ne_zero h0
  · -- Show f ≠ 0
    intro h
    have : (fun _ : ℤ => (1 : K)) 0 = 0 := by rw [h]; rfl
    exact one_ne_zero this
  · -- Show laurentPolynomialSmul p f = 0
    funext n
    simp only [laurentPolynomialSmul]
    show (1 - LaurentPolynomial.T 1 : K[T;T⁻¹]).coeff.sum (fun i b => b * (1 : K)) = (0 : K)
    simp only [mul_one]
    have hc : (1 - LaurentPolynomial.T 1 : K[T;T⁻¹]).coeff =
        Finsupp.single 0 (1 : K) - Finsupp.single 1 1 := by
      rw [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]
      rfl
    rw [hc, Finsupp.sum_sub_index (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
      Finsupp.sum_single_index rfl, sub_self]

end ModuleStructure

/-! ## k-bounded Balanced Ternary Representations

A balanced ternary representation is k-bounded if all digits beyond position k are zero.
This is used in the rigorous proof of Theorem `thm.fps.laure.balanced-tern-rep-uniq`.
-/

/-- A balanced ternary representation is k-bounded if b_{k+1} = b_{k+2} = ... = 0. -/
def BalancedTernaryRepresentation.isBounded {n : ℤ} (r : BalancedTernaryRepresentation n)
    (k : ℕ) : Prop :=
  ∀ i > k, r.digits i = 0

/-- For k-bounded representations, the finsum equals a finite sum over range(k+1). -/
lemma bounded_sum_eq {n : ℤ} (r : BalancedTernaryRepresentation n) (k : ℕ)
    (hk : r.isBounded k) :
    n = ∑ i ∈ Finset.range (k + 1), (r.digits i).toInt * (3 : ℤ)^i := by
  have h := r.sum_eq
  conv_lhs => rw [← h]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  push Not at hc
  have hd : r.digits i = 0 := hk i hc
  change (r.digits i).toInt * (3 : ℤ)^i ≠ 0 at hi
  rw [hd, BalancedTernaryDigit.toInt_zero, zero_mul] at hi
  exact hi rfl

/-- Key lemma: if sum of c_i * 3^i = 0 where c_i ∈ {-2,...,2}, then all c_i = 0.

This is the core uniqueness argument: the difference of two balanced ternary
representations has coefficients in {-2,...,2}, and if the sum is 0, all
coefficients must be 0. -/
lemma sum_powers_of_three_eq_zero (k : ℕ) (c : ℕ → ℤ)
    (hc : ∀ i ≤ k, -2 ≤ c i ∧ c i ≤ 2)
    (hzero : ∀ i > k, c i = 0)
    (hsum : ∑ i ∈ Finset.range (k + 1), c i * (3 : ℤ)^i = 0) :
    ∀ i, c i = 0 := by
  induction k generalizing c with
  | zero =>
    intro i
    cases i with
    | zero =>
      simp at hsum
      have hc0 := hc 0 (le_refl 0)
      omega
    | succ j =>
      exact hzero (j + 1) (by omega)
  | succ k ih =>
    -- The key: c 0 must be 0 mod 3, so c 0 ∈ {-2,-1,0,1,2} ∩ 3ℤ = {0}
    have hmod : (∑ i ∈ Finset.range (k + 2), c i * (3 : ℤ)^i) % 3 = 0 := by
      rw [hsum]
      simp
    rw [Finset.sum_range_succ'] at hmod
    simp only [pow_zero, mul_one] at hmod
    have hrest : (∑ i ∈ Finset.range (k + 1), c (i + 1) * (3 : ℤ)^(i + 1)) % 3 = 0 := by
      rw [Finset.sum_int_mod]
      have h1 : ∀ i ∈ Finset.range (k + 1), c (i + 1) * (3 : ℤ)^(i + 1) % 3 = 0 := by
        intro i _
        simp only [pow_succ]
        have h3 : (3 : ℤ) ^ i * 3 % 3 = 0 := by simp
        rw [Int.mul_emod, h3, mul_zero, Int.zero_emod]
      rw [Finset.sum_eq_zero h1]
      simp
    rw [Int.add_emod, hrest, zero_add] at hmod
    have hc0 := hc 0 (by omega)
    have hc0_mod : c 0 % 3 = 0 := by
      rw [Int.emod_emod_of_dvd] at hmod
      · exact hmod
      · norm_num
    have hc0_zero : c 0 = 0 := by omega
    -- Now we can factor out 3 from the remaining sum
    rw [Finset.sum_range_succ'] at hsum
    simp only [pow_zero, mul_one, hc0_zero] at hsum
    have hfactor : ∑ i ∈ Finset.range (k + 1), c (i + 1) * (3 : ℤ)^(i + 1) =
                   3 * ∑ i ∈ Finset.range (k + 1), c (i + 1) * (3 : ℤ)^i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfactor] at hsum
    have hsum' : ∑ i ∈ Finset.range (k + 1), c (i + 1) * (3 : ℤ)^i = 0 := by
      simp at hsum
      exact hsum
    -- Apply IH to the shifted sequence c' i = c (i + 1)
    let c' : ℕ → ℤ := fun i => c (i + 1)
    have hc' : ∀ i ≤ k, -2 ≤ c' i ∧ c' i ≤ 2 := fun i hi => hc (i + 1) (by omega)
    have hzero' : ∀ i > k, c' i = 0 := fun i hi => hzero (i + 1) (by omega)
    have hsum'' : ∑ i ∈ Finset.range (k + 1), c' i * (3 : ℤ)^i = 0 := hsum'
    have ih' := ih c' hc' hzero' hsum''
    intro i
    cases i with
    | zero => exact hc0_zero
    | succ j => exact ih' j

/-- Each integer n with |n| ≤ 3^0 + 3^1 + ... + 3^k has a unique k-bounded
balanced ternary representation.

This is the key lemma used in the rigorous proof of
Theorem `thm.fps.laure.balanced-tern-rep-uniq`. -/
theorem balancedTernaryRepresentation_bounded_unique (k : ℕ) (n : ℤ)
    (_hn : |n| ≤ ∑ i ∈ Finset.range (k + 1), (3 : ℤ)^i)
    (r₁ r₂ : BalancedTernaryRepresentation n)
    (h₁ : r₁.isBounded k) (h₂ : r₂.isBounded k) :
    r₁.digits = r₂.digits := by
  -- Define the difference of digits
  let c : ℕ → ℤ := fun i => (r₁.digits i).toInt - (r₂.digits i).toInt
  -- Show c satisfies the conditions of sum_powers_of_three_eq_zero
  have hc : ∀ i ≤ k, -2 ≤ c i ∧ c i ≤ 2 := by
    intro i _
    have h1 := BalancedTernaryDigit.toInt_range (r₁.digits i)
    have h2 := BalancedTernaryDigit.toInt_range (r₂.digits i)
    simp only [c]
    constructor <;> omega
  have hzero : ∀ i > k, c i = 0 := by
    intro i hi
    simp only [c]
    rw [h₁ i hi, h₂ i hi]
    simp
  have hsum : ∑ i ∈ Finset.range (k + 1), c i * (3 : ℤ)^i = 0 := by
    have h1 := bounded_sum_eq r₁ k h₁
    have h2 := bounded_sum_eq r₂ k h₂
    simp only [c]
    have : ∑ i ∈ Finset.range (k + 1), ((r₁.digits i).toInt - (r₂.digits i).toInt) * (3 : ℤ)^i =
           ∑ i ∈ Finset.range (k + 1), (r₁.digits i).toInt * (3 : ℤ)^i -
           ∑ i ∈ Finset.range (k + 1), (r₂.digits i).toInt * (3 : ℤ)^i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this, ← h1, ← h2]
    ring
  -- Apply the key lemma
  have hall := sum_powers_of_three_eq_zero k c hc hzero hsum
  -- Conclude that all digits are equal
  ext i
  have hi := hall i
  simp only [c] at hi
  have hr1 := BalancedTernaryDigit.toInt_range (r₁.digits i)
  have hr2 := BalancedTernaryDigit.toInt_range (r₂.digits i)
  apply BalancedTernaryDigit.toInt_injective
  omega

/-! ## Field Structure

When K is a field, K((x)) is also a field. This is mentioned at the end of the section. -/

/-- When K is a field, the Laurent series ring K((x)) is a field.
This is stated at the end of the section and proved in Exercise `exe.fps.laure.field`. -/
example (K : Type*) [Field K] : Field (LaurentSeries K) := inferInstance

/-! ## Partial Product Formula

The key computation used to prove Theorem `thm.fps.laure.balanced-tern-rep-uniq`
involves the partial products ∏_{i=0}^{k} (1 + x^{3^i} + x^{-3^i}).
-/

/-- The partial product ∏_{i=0}^{k} (1 + T^{3^i} + T^{-3^i}) in the Laurent polynomial ring.
This is used in the proof of Theorem `thm.fps.laure.balanced-tern-rep-uniq`. -/
def balancedTernaryPartialProduct (K : Type*) [CommSemiring K] (k : ℕ) : K[T;T⁻¹] :=
  ∏ i ∈ Finset.range (k + 1),
    (1 + LaurentPolynomial.T ((3 : ℤ)^i) + LaurentPolynomial.T (-((3 : ℤ)^i)))

/-- The identity 1 + x + x^{-1} = (1 - x^3) / (x(1-x)) as Laurent polynomials.
This is used in simplifying the partial products. -/
theorem one_plus_T_plus_Tinv_eq (K : Type*) [CommRing K] :
    (1 + LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : K[T;T⁻¹]) *
    (LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T 1)) =
    (1 - LaurentPolynomial.T 3) := by
  simp only [mul_sub, mul_one, one_mul, add_mul, ← LaurentPolynomial.T_add]
  norm_num
  ring

/-- The sum 3^0 + 3^1 + ... + 3^k = (3^{k+1} - 1) / 2.
This is used in bounding the range of balanced ternary representations. -/
theorem geom_sum_three (k : ℕ) :
    2 * ∑ i ∈ Finset.range (k + 1), (3 : ℤ)^i = (3 : ℤ)^(k + 1) - 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    ring_nf
    have : (∑ x ∈ Finset.range (1 + n), (3 : ℤ) ^ x) * 2 = 3 ^ (n + 1) - 1 := by
      simp only [add_comm 1 n]
      convert ih using 1
      ring
    omega

end AlgebraicCombinatorics
