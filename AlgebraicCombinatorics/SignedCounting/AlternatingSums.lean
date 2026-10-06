/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025. All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.QBinomialBasic

/-!
# Cancellations in Alternating Sums

This file formalizes the theory of cancellations in alternating sums using
sign-reversing bijections and involutions. The main results include:

* The negative hockey-stick identity for binomial coefficients
* Three versions of the cancellation principle (Lemmas `sign_cancel1`, `sign_cancel2`, `sign_cancel3`)
* The evaluation of q-binomial coefficients at q = -1
* The q-Lucas theorem for primitive roots of unity

## Main definitions

* `acceptableSets`: A finset of subsets of `Finset.range n` with cardinality at most `m`
* `partner`: The symmetric difference of a set with `{0}`, used for sign-reversing
* `setSign`: The sign `(-1)^|I|` of a finite set `I`
* `switch`: Swap elements `i` and `i+1` in a set when exactly one is present
* `IsBlocky`: A subset that is a union of consecutive pairs (blocks)
* `IsRootOfUnity`: An element `ω` satisfying `ω^d = 1`
* `qBinomial`: The q-binomial coefficient `[n choose k]_q` (local definition as `Polynomial ℤ`)

## Main results

* `negHockeyStick`: The negative hockey-stick identity
  `∑ k ∈ Finset.range (m+1), (-1)^k * (n.choose k) = (-1)^m * (n-1).choose m`
* `sign_cancel1`: Cancellation principle for sign-reversing bijections
* `sign_cancel2`: Cancellation principle for sign-reversing involutions without fixed points
* `sign_cancel3`: Cancellation principle for sign-reversing involutions with zero-sign fixed points
* `qBinom_neg_one`: Formula for q-binomial coefficients evaluated at q = -1
* `qLucas`: The q-Lucas theorem for primitive roots of unity
* `qBinomial_eq_canonical`: Bridge lemma connecting local `qBinomial` to `AlgebraicCombinatorics.qBinomialPoly`

**Note on qBinomial:** This file defines a local `qBinomial` as a `Polynomial ℤ` using
the subset sum formula. This is equivalent to `AlgebraicCombinatorics.qBinomialPoly` in
`QBinomialBasic.lean`. The theorem `qBinomial_eq_canonical` proves this equivalence.
The local definition is in namespace `AlgebraicCombinatorics.SignedCounting` to avoid conflicts.

## References

* Section on "Cancellations in alternating sums" from Algebraic Combinatorics notes
* Labels: prop.binom.nhs, lem.sign.cancel1, lem.sign.cancel2, lem.sign.cancel3,
  exe.sign.-1inom, def.root-of-unity.prim, thm.sign.q-lucas

## Tags

alternating sums, sign-reversing involution, cancellation principle, q-binomial,
hockey-stick identity, roots of unity, q-Lucas theorem
-/

namespace AlgebraicCombinatorics.SignedCounting

open Finset BigOperators

/-! ### Acceptable Sets and Partners

We define acceptable sets (subsets of `{0, 1, ..., n-1}` with size at most `m`)
and the partner operation (symmetric difference with `{0}`).
-/

/-- The finset of acceptable sets: subsets of `Finset.range n` with cardinality at most `m`. -/
def acceptableSets (n m : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter (fun I => I.card ≤ m)

/-- The partner of a finite set `I` is `I △ {0}` (symmetric difference with singleton 0).
If `0 ∈ I`, this removes 0; if `0 ∉ I`, this adds 0. -/
def partner (I : Finset ℕ) : Finset ℕ :=
  symmDiff I {0}

/-- The partner operation is an involution. -/
theorem partner_partner (I : Finset ℕ) : partner (partner I) = I := by
  simp only [partner, symmDiff_symmDiff_cancel_right]

/-- The partner has size differing by 1 (when 0 is in range). -/
theorem partner_card (I : Finset ℕ) :
    (partner I).card = I.card + 1 ∨ (partner I).card + 1 = I.card := by
  unfold partner
  by_cases h : 0 ∈ I
  · -- Case: 0 ∈ I, so partner removes 0
    right
    simp only [symmDiff_def, sup_eq_union, sdiff_singleton_eq_erase]
    have h1 : {0} \ I = ∅ := by simp [h]
    rw [h1, union_empty]
    rw [card_erase_of_mem h]
    -- Goal should be (I.card - 1) + 1 = I.card
    have hpos : 0 < I.card := card_pos.mpr ⟨0, h⟩
    omega
  · -- Case: 0 ∉ I, so partner adds 0
    left
    simp only [symmDiff_def, sup_eq_union, sdiff_singleton_eq_erase]
    have h1 : I.erase 0 = I := by simp [h]
    rw [h1]
    have h2 : {0} \ I = {0} := by
      ext x
      simp only [mem_sdiff, mem_singleton]
      constructor
      · intro ⟨hx, _⟩; exact hx
      · intro hx; exact ⟨hx, by rw [hx]; exact h⟩
    rw [h2]
    rw [card_union_of_disjoint]
    · simp
    · simp [h]

/-- The sign of a finite set is `(-1)^|I|`. -/
def setSign (I : Finset ℕ) : ℤ :=
  (-1 : ℤ) ^ I.card

/-- The sign of the empty set is 1. -/
@[simp]
theorem setSign_empty : setSign ∅ = 1 := by
  simp only [setSign, card_empty, pow_zero]

/-- The sign of a singleton set is -1. -/
@[simp]
theorem setSign_singleton (a : ℕ) : setSign {a} = -1 := by
  simp only [setSign, card_singleton, pow_one]

/-- The partner of the empty set is `{0}`. -/
@[simp]
theorem partner_empty : partner ∅ = {0} := by
  simp only [partner]
  rfl

/-- The partner of `{0}` is the empty set. -/
@[simp]
theorem partner_singleton_zero : partner {0} = ∅ := by
  simp only [partner, symmDiff_self, bot_eq_empty]

/-- The partner has opposite sign. -/
theorem partner_sign (I : Finset ℕ) : setSign (partner I) = -setSign I := by
  simp only [setSign, partner]
  by_cases h : 0 ∈ I
  · -- 0 ∈ I: partner removes 0, so card decreases by 1
    have heq : symmDiff I {0} = I.erase 0 := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase, ne_eq]
      constructor
      · rintro (⟨hxI, hx0⟩ | ⟨rfl, hxI⟩)
        · exact ⟨hx0, hxI⟩
        · exact absurd h hxI
      · rintro ⟨hx0, hxI⟩
        exact Or.inl ⟨hxI, hx0⟩
    rw [heq]
    have hcard : (I.erase 0).card = I.card - 1 := by simp [h]
    have hpos : 0 < I.card := card_pos.mpr ⟨0, h⟩
    rw [hcard]
    have hsub : I.card - 1 + 1 = I.card := Nat.sub_add_cancel hpos
    calc (-1 : ℤ) ^ (I.card - 1) = (-1) ^ (I.card - 1) * 1 := by ring
      _ = (-1) ^ (I.card - 1) * ((-1) * (-1)) := by ring
      _ = (-1) ^ (I.card - 1 + 1) * (-1) := by ring_nf
      _ = (-1) ^ I.card * (-1) := by rw [hsub]
      _ = -((-1) ^ I.card) := by ring
  · -- 0 ∉ I: partner adds 0, so card increases by 1
    have heq : symmDiff I {0} = insert 0 I := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · rintro (⟨hxI, hx0⟩ | ⟨rfl, hxI⟩)
        · exact Or.inr hxI
        · exact Or.inl rfl
      · rintro (rfl | hxI)
        · exact Or.inr ⟨rfl, h⟩
        · exact Or.inl ⟨hxI, fun hx0 => h (hx0 ▸ hxI)⟩
    rw [heq]
    have hcard : (insert 0 I).card = I.card + 1 := by simp [h]
    rw [hcard, pow_succ]
    ring

/-! ### The Negative Hockey-Stick Identity

The negative hockey-stick identity states:
`∑_{k=0}^{m} (-1)^k * C(n,k) = (-1)^m * C(n-1,m)`

This is Proposition \ref{prop.binom.nhs} in the source.
-/

/-- **Negative Hockey-Stick Identity** (prop.binom.nhs)

For `n : ℕ` with `n ≥ 1` and `m : ℕ`, we have
`∑ k in range (m+1), (-1)^k * n.choose k = (-1)^m * (n-1).choose m`

Note: We state this for natural numbers with `n ≥ 1`. The source states it for `n ∈ ℂ`,
but by the polynomial identity principle, it suffices to prove it for positive integers.
The hypothesis `n ≥ 1` is necessary because natural number subtraction gives
`(0 - 1) = 0`, which would make the RHS incorrect when `n = 0` and `m ≥ 1`.
-/
theorem negHockeyStick (n m : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (m + 1), ((-1 : ℤ) ^ k * (n.choose k)) =
    (-1 : ℤ) ^ m * ((n - 1).choose m) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  simp only [Nat.succ_sub_one]
  exact Int.alternating_sum_range_choose_eq_choose

/-- **Negative Hockey-Stick Identity** (variant without hypothesis)

Alternative formulation using `(n + 1)` to avoid the edge case.
This is exactly `Int.alternating_sum_range_choose_eq_choose` from Mathlib.
-/
theorem negHockeyStick' (n m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), ((-1 : ℤ) ^ k * ((n + 1).choose k)) =
    (-1 : ℤ) ^ m * (n.choose m) :=
  Int.alternating_sum_range_choose_eq_choose

/-! ### Cancellation Principles

These lemmas formalize the idea that sign-reversing bijections/involutions
cause addends to cancel in sums.
-/

section CancellationPrinciples

variable {α : Type*} [DecidableEq α] {R : Type*} [AddCommGroup R]

/-- **Cancellation Principle, Take 1** (lem.sign.cancel1)

Let `A` be a finite set, `X ⊆ A`, and `sign : A → R` where `R` is an additive group
with no 2-torsion (i.e., `2a = 0 → a = 0`). If `f : X → X` is a bijection satisfying
`sign(f(I)) = -sign(I)` for all `I ∈ X`, then `∑_{I ∈ A} sign(I) = ∑_{I ∈ A \ X} sign(I)`.

This version requires `R` to have no 2-torsion (e.g., `R = ℤ`, `ℚ`, `ℝ`).
-/
theorem sign_cancel1 [NoZeroSMulDivisors ℕ R]
    (A : Finset α) (X : Finset α) (hXA : X ⊆ A)
    (sign : α → R)
    (f : X → X) (hf_bij : Function.Bijective f)
    (hf_sign : ∀ I : X, sign (f I) = -sign I) :
    ∑ I ∈ A, sign I = ∑ I ∈ A \ X, sign I := by
  -- First, show that the sum over X is zero
  have hX_zero : ∑ I ∈ X, sign I = 0 := by
    -- Use the bijection to reindex the sum
    let e : X ≃ X := Equiv.ofBijective f hf_bij
    -- First rewrite using attachment
    have h1 : ∑ I ∈ X, sign I = ∑ I : X, sign I := (Finset.sum_attach X (fun x => sign x)).symm
    -- Key: ∑ sign(f(I)) = ∑ sign(J) by substituting J = f(I)
    have h2 : ∑ I : X, sign (f I) = ∑ I : X, sign I := by
      rw [Fintype.sum_equiv e (fun i => sign (f i)) (fun i => sign i)]
      intro i
      rfl
    -- Also: ∑ sign(f(I)) = -∑ sign(I) by the sign-reversing property
    have h3 : ∑ I : X, sign (f I) = -(∑ I : X, sign I) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact hf_sign x
    -- Combining h2 and h3: ∑ sign(I) = -∑ sign(I)
    -- So 2∑ sign(I) = 0
    have h4 : (2 : ℕ) • (∑ I : X, sign I) = 0 := by
      calc (2 : ℕ) • (∑ I : X, sign I)
          = (∑ I : X, sign I) + (∑ I : X, sign I) := two_nsmul _
        _ = (∑ I : X, sign I) + (∑ I : X, sign (f I)) := by rw [h2]
        _ = (∑ I : X, sign I) + (-(∑ I : X, sign I)) := by rw [h3]
        _ = 0 := add_neg_cancel _
    rw [h1]
    exact (smul_eq_zero.mp h4).resolve_left (by norm_num)
  -- Now split the sum over A
  rw [← Finset.sum_sdiff hXA, hX_zero, add_zero]

/-- **Cancellation Principle, Take 2** (lem.sign.cancel2)

Let `A` be a finite set, `X ⊆ A`, and `sign : A → R` for any additive abelian group `R`.
If `f : X → X` is an involution with no fixed points satisfying
`sign(f(I)) = -sign(I)` for all `I ∈ X`, then `∑_{I ∈ A} sign(I) = ∑_{I ∈ A \ X} sign(I)`.

This version works for any additive abelian group (no 2-torsion requirement).
-/
theorem sign_cancel2
    (A : Finset α) (X : Finset α) (hXA : X ⊆ A)
    (sign : α → R)
    (f : X → X) (hf_invol : ∀ I : X, f (f I) = I)
    (hf_no_fixed : ∀ I : X, f I ≠ I)
    (hf_sign : ∀ I : X, sign (f I) = -sign I) :
    ∑ I ∈ A, sign I = ∑ I ∈ A \ X, sign I := by
  -- Sum over X is zero: elements pair up and cancel via the involution
  have hX_zero : ∑ I ∈ X, sign I = 0 := by
    rw [← sum_attach]
    apply sum_involution (fun I _ => f I)
    · intro I _; rw [hf_sign I]; simp [add_neg_cancel]
    · intro I _ _; exact hf_no_fixed I
    · intro I _; exact mem_attach _ _
    · intro I _; exact hf_invol I
  -- Split sum over A into (A \ X) ∪ X and use that sum over X is zero
  have h : (∑ I ∈ A \ X, sign I) + ∑ I ∈ X, sign I = ∑ I ∈ A, sign I := by
    rw [← sum_union (disjoint_sdiff_self_left)]
    congr 1
    exact sdiff_union_of_subset hXA
  rw [← h, hX_zero, add_zero]

/-- **Cancellation Principle, Take 3** (lem.sign.cancel3)

Let `A` be a finite set, `X ⊆ A`, and `sign : A → R` for any additive abelian group `R`.
If `f : X → X` is an involution satisfying `sign(f(I)) = -sign(I)` for all `I ∈ X`,
and furthermore `sign(I) = 0` for all fixed points `I` of `f`,
then `∑_{I ∈ A} sign(I) = ∑_{I ∈ A \ X} sign(I)`.

This is the most general version, allowing fixed points as long as they have sign 0.
-/
theorem sign_cancel3
    (A : Finset α) (X : Finset α) (hXA : X ⊆ A)
    (sign : α → R)
    (f : X → X) (hf_invol : ∀ I : X, f (f I) = I)
    (hf_sign : ∀ I : X, sign (f I) = -sign I)
    (hf_fixed_zero : ∀ I : X, f I = I → sign I = 0) :
    ∑ I ∈ A, sign I = ∑ I ∈ A \ X, sign I := by
  -- Use sum_sdiff to split A into (A \ X) and X
  have : ∑ I ∈ A, sign I = ∑ I ∈ A \ X, sign I + ∑ I ∈ X, sign I := by
    rw [← sum_sdiff hXA]
  rw [this]
  -- Now we need to show ∑ I ∈ X, sign I = 0
  suffices h : ∑ I ∈ X, sign I = 0 by rw [h]; simp
  -- Define the involution on X using f
  let g : ∀ a ∈ X, α := fun a ha => f ⟨a, ha⟩
  have g_mem : ∀ a ha, g a ha ∈ X := fun a ha => (f ⟨a, ha⟩).2
  -- Apply sum_involution: elements pair up with opposite signs and cancel
  refine sum_involution g ?_ ?_ g_mem ?_
  · -- hg₁: sign a + sign (g a ha) = 0
    intro a ha
    simp only [g]
    rw [hf_sign ⟨a, ha⟩, add_neg_cancel]
  · -- hg₃: sign a ≠ 0 → g a ha ≠ a (non-zero sign means not a fixed point)
    intro a ha hne
    simp only [g, ne_eq]
    intro heq
    have hfeq : f ⟨a, ha⟩ = ⟨a, ha⟩ := Subtype.ext heq
    exact hne (hf_fixed_zero ⟨a, ha⟩ hfeq)
  · -- hg₄: g (g a ha) (g_mem a ha) = a (involution property)
    intro a ha
    simp only [g]
    exact congrArg Subtype.val (hf_invol ⟨a, ha⟩)

end CancellationPrinciples

/-! ### Switching Operation

The switching operation `switch_{i,i+1}` swaps elements `i` and `i+1` in a set
when exactly one of them is present.
-/

/-- Switch `i` with `i+1` in a set: if exactly one of `{i, i+1}` is in `S`,
replace it with the other; otherwise leave `S` unchanged. -/
def switch (i : ℕ) (S : Finset ℕ) : Finset ℕ :=
  if (S ∩ {i, i + 1}).card = 1 then
    symmDiff S {i, i + 1}
  else S

/-- Switching the empty set gives the empty set. -/
@[simp] lemma switch_empty (i : ℕ) : switch i ∅ = ∅ := by
  simp [switch, Finset.card_empty]

/-- If exactly one of `{i, i+1}` is in `S`, then exactly one is in `symmDiff S {i, i+1}`.
This is a key lemma for showing that `switch` is an involution. -/
private lemma symmDiff_inter_pair_card (i : ℕ) (S : Finset ℕ)
    (h : (S ∩ {i, i + 1}).card = 1) :
    (symmDiff S {i, i + 1} ∩ {i, i + 1}).card = 1 := by
  -- Key insight: symmDiff S {i, i+1} ∩ {i, i+1} = {i, i+1} \ S
  have key : symmDiff S {i, i + 1} ∩ {i, i + 1} = {i, i + 1} \ S := by
    ext x
    simp only [mem_inter, mem_symmDiff, mem_insert, mem_singleton, mem_sdiff]
    constructor
    · intro ⟨hx, hx'⟩
      exact ⟨hx', hx.elim (fun ⟨_, hpair⟩ => (hpair hx').elim) (fun ⟨_, hS⟩ => hS)⟩
    · intro ⟨hpair, hS⟩
      exact ⟨Or.inr ⟨hpair, hS⟩, hpair⟩
  rw [key, Finset.card_sdiff, h, Finset.card_pair (Nat.succ_ne_self i |>.symm)]

/-- The switch operation is an involution. -/
theorem switch_switch (i : ℕ) (S : Finset ℕ) : switch i (switch i S) = S := by
  unfold switch
  by_cases h1 : (S ∩ {i, i + 1}).card = 1
  · simp only [h1, ↓reduceIte, symmDiff_inter_pair_card i S h1, symmDiff_symmDiff_cancel_right]
  · simp only [h1, ↓reduceIte]

/-- Switching preserves cardinality. -/
theorem switch_card (i : ℕ) (S : Finset ℕ) : (switch i S).card = S.card := by
  unfold switch
  split_ifs with h
  · -- Case: exactly one of i, i+1 is in S
    -- We need to show the symmetric difference has the same cardinality
    have hi_ne : i ≠ i + 1 := Nat.ne_of_lt (Nat.lt_succ_self i)
    have h_pair_card : ({i, i + 1} : Finset ℕ).card = 2 := by
      rw [card_pair hi_ne]
    -- The intersection has exactly 1 element
    have h_inter_card : (S ∩ {i, i + 1}).card = 1 := h
    -- Use the symmetric difference cardinality formula
    simp only [symmDiff_def, sup_eq_union]
    rw [card_union_of_disjoint (disjoint_sdiff_sdiff)]
    -- Need: (S \ {i, i+1}).card + ({i, i+1} \ S).card = S.card
    have h_S_sdiff : (S \ {i, i + 1}).card = S.card - 1 := by
      rw [card_sdiff]
      rw [inter_comm, h_inter_card]
    have h_pair_sdiff : ({i, i + 1} \ S).card = 1 := by
      have key : ({i, i + 1} : Finset ℕ).card = (S ∩ {i, i + 1}).card + ({i, i + 1} \ S).card := by
        rw [← card_union_of_disjoint]
        · congr 1
          ext x
          simp only [mem_union, mem_inter, mem_sdiff]
          constructor
          · intro hx
            by_cases hxS : x ∈ S <;> simp [hx, hxS]
          · intro hx
            rcases hx with ⟨_, hx⟩ | ⟨hx, _⟩ <;> exact hx
        · simp [disjoint_iff_inter_eq_empty]
          ext x
          simp [mem_inter, mem_sdiff]
          tauto
      omega
    have h_S_pos : 1 ≤ S.card := by
      have : (S ∩ {i, i + 1}).card ≤ S.card := card_le_card inter_subset_left
      omega
    omega
  · -- Case: 0 or 2 of i, i+1 are in S, so switch S = S
    rfl

/-! ### q-Binomial Coefficients

We define q-binomial coefficients and study their properties.
Note: As of this writing, q-binomial coefficients are not in Mathlib,
so we define them here.
-/

/-- The q-factorial `[n]_q! = [1]_q * [2]_q * ... * [n]_q` where `[k]_q = 1 + q + q^2 + ... + q^{k-1}`.
We define it as a polynomial in `q`. -/
noncomputable def qFactorial (n : ℕ) : Polynomial ℤ :=
  ∏ k ∈ Finset.range n, ∑ i ∈ Finset.range (k + 1), Polynomial.X ^ i

/-- The q-binomial coefficient `[n choose k]_q = [n]_q! / ([k]_q! * [n-k]_q!)`.
This is well-defined as a polynomial (the division is exact).

We define it combinatorially using the sum over k-element subsets formula:
`[n choose k]_q = ∑_{S ⊆ [n], |S|=k} q^{sum(S) - (1+2+...+k)}`

**Note:** This is a local definition as `Polynomial ℤ`, equivalent to
`AlgebraicCombinatorics.qBinomial n k X` from `QBinomialBasic.lean` when the latter
is evaluated as a polynomial. The equivalence follows from `qBinomial_eq_sum_subsets`.
This definition uses 0-indexed sets `{0, 1, ..., n-1}` while `QBinomialBasic` uses
1-indexed sets `{1, 2, ..., n}` in its subset formula, but both are equivalent. -/
noncomputable def qBinomial (n k : ℕ) : Polynomial ℤ :=
  ∑ S ∈ (Finset.range n).powerset.filter (fun S => S.card = k),
    Polynomial.X ^ (S.sum id - (Finset.range k).sum id)

/-! ### Roots of Unity and Primitive Roots of Unity

This section formalizes Definition \ref{def.root-of-unity.prim} from the source.

**Definition (def.root-of-unity.prim):**
Let `K` be a field and `d` a positive integer.

**(a)** A *d-th root of unity* in `K` is an element `ω` of `K` satisfying `ω^d = 1`.
In other words, a d-th root of unity in `K` is an element of `K` whose d-th power is 1.

**(b)** A *primitive d-th root of unity* in `K` is an element `ω` of `K` satisfying
`ω^d = 1` but `ω^i ≠ 1` for each `i ∈ {1, 2, ..., d-1}`.
In other words, a primitive d-th root of unity in `K` is an element of the
multiplicative group `K×` whose order is exactly `d`.

**Mathlib correspondence:**
- Part (a) is captured by `ω ∈ rootsOfUnity d K` or equivalently `ω ^ d = 1`
- Part (b) is captured by `IsPrimitiveRoot ω d` from `RingTheory.RootsOfUnity.PrimitiveRoots`

**Key property:**
For `K = ℂ`, the d-th roots of unity are the `d` complex numbers
`e^{2πi·0/d}, e^{2πi·1/d}, ..., e^{2πi·(d-1)/d}` (vertices of a regular d-gon on the unit circle).
The primitive d-th roots of unity are those `e^{2πi·g/d}` where `gcd(g, d) = 1`.

In particular:
- The 2nd roots of unity in `ℂ` are `1` and `-1`
- The only primitive 2nd root of unity is `-1`
-/

section RootsOfUnity

variable {K : Type*} [CommRing K]

/-- An element `ω` is a *d-th root of unity* if `ω^d = 1`. (def.root-of-unity.prim (a))

This is the condition for membership in `rootsOfUnity d K` when `ω` is a unit.
For fields, we can state this directly without the unit requirement. -/
def IsRootOfUnity (ω : K) (d : ℕ) : Prop := ω ^ d = 1

/-- A d-th root of unity satisfies `ω^d = 1`. -/
theorem IsRootOfUnity.pow_eq_one {ω : K} {d : ℕ} (h : IsRootOfUnity ω d) : ω ^ d = 1 := h

/-- 1 is always a d-th root of unity. -/
theorem isRootOfUnity_one (d : ℕ) : IsRootOfUnity (1 : K) d := one_pow d

/-- Every primitive d-th root of unity is also a d-th root of unity. -/
theorem IsPrimitiveRoot.isRootOfUnity {ω : K} {d : ℕ} (h : IsPrimitiveRoot ω d) :
    IsRootOfUnity ω d := h.pow_eq_one

/-- **Characterization of primitive roots** (def.root-of-unity.prim (b))

An element `ω` is a primitive d-th root of unity if and only if:
- `ω^d = 1`, and
- `ω^i ≠ 1` for all `i` with `0 < i < d`.

This is the characterization given in the source definition. -/
theorem isPrimitiveRoot_iff_pow_eq_one_and_pow_ne_one {ω : K} {d : ℕ} (hd : 0 < d) :
    IsPrimitiveRoot ω d ↔ (ω ^ d = 1 ∧ ∀ i : ℕ, 0 < i → i < d → ω ^ i ≠ 1) := by
  constructor
  · intro h
    exact ⟨h.pow_eq_one, fun i hi hi' => h.pow_ne_one_of_pos_of_lt (Nat.ne_of_gt hi) hi'⟩
  · intro ⟨hpow, hne⟩
    exact IsPrimitiveRoot.mk_of_lt ω hd hpow fun l hl hlt => hne l hl hlt

/-- A primitive d-th root of unity `ω` satisfies `ω^i ≠ 1` for `0 < i < d`. -/
theorem IsPrimitiveRoot.pow_ne_one' {ω : K} {d : ℕ} (h : IsPrimitiveRoot ω d)
    {i : ℕ} (hi : 0 < i) (hi' : i < d) : ω ^ i ≠ 1 :=
  h.pow_ne_one_of_pos_of_lt (Nat.ne_of_gt hi) hi'

variable [IsDomain K]

omit [IsDomain K] in
/-- `-1` is a primitive 2nd root of unity in any integral domain where `-1 ≠ 1`. -/
theorem neg_one_isPrimitiveRoot_two (h : (-1 : K) ≠ 1) : IsPrimitiveRoot (-1 : K) 2 := by
  refine IsPrimitiveRoot.mk_of_lt (-1) (by norm_num) (by ring) ?_
  intro l hl hlt
  interval_cases l
  simp_all

/-- In an integral domain where `-1 ≠ 1`, `-1` is the unique primitive 2nd root of unity.

The 2nd roots of unity are `1` and `-1`, but only `-1` is primitive. -/
theorem isPrimitiveRoot_two_iff (h : (-1 : K) ≠ 1) (ω : K) :
    IsPrimitiveRoot ω 2 ↔ ω = -1 := by
  constructor
  · intro hω
    have h1 : ω ^ 2 = 1 := hω.pow_eq_one
    have h2 : ω ≠ 1 := hω.ne_one (by norm_num)
    -- ω^2 = 1 means ω^2 - 1 = 0, i.e., (ω - 1)(ω + 1) = 0
    have hfac : (ω - 1) * (ω + 1) = 0 := by
      have : ω ^ 2 - 1 = 0 := sub_eq_zero.mpr h1
      calc (ω - 1) * (ω + 1) = ω ^ 2 - 1 := by ring
        _ = 0 := this
    -- In an integral domain, either ω - 1 = 0 or ω + 1 = 0
    rcases mul_eq_zero.mp hfac with h3 | h3
    · exfalso
      exact h2 (sub_eq_zero.mp h3)
    · exact eq_neg_of_add_eq_zero_left h3
  · intro hω
    rw [hω]
    exact neg_one_isPrimitiveRoot_two h

end RootsOfUnity

/-! #### Sum of Primitive Roots of Unity

A key property used in cancellation arguments: if `ω` is a primitive d-th root of unity
with `d > 1`, then `1 + ω + ω² + ... + ω^{d-1} = 0`.

This generalizes `1 + (-1) = 0` (the case `d = 2`) and allows cancellation in sums
involving powers of `ω`.

Note: Mathlib provides `IsPrimitiveRoot.geom_sum_eq_zero` which proves exactly this.
-/

section GeomSum

variable {K : Type*} [CommRing K] [IsDomain K]

/-- **Geometric sum of primitive roots** (used in the discrete Fourier transform)

If `ω` is a primitive d-th root of unity with `d > 1`, then
`1 + ω + ω² + ... + ω^{d-1} = 0`.

This is the key identity that enables cancellation in sums involving roots of unity.
It generalizes `1 + (-1) = 0` (the case `d = 2`).

This is `IsPrimitiveRoot.geom_sum_eq_zero` from Mathlib, included here for documentation. -/
theorem primitiveRoot_geom_sum_eq_zero {ω : K} {d : ℕ} (hω : IsPrimitiveRoot ω d)
    (hd : 1 < d) : ∑ i ∈ Finset.range d, ω ^ i = 0 :=
  hω.geom_sum_eq_zero hd

end GeomSum

/-! ### The q-Lucas Theorem

The q-Lucas theorem relates q-binomial coefficients at primitive roots of unity
to ordinary binomial coefficients.
-/

/-! #### Helper Lemmas for q-Lucas -/

/-- For a primitive d-th root of unity ω, ω^n = ω^(n % d) -/
theorem pow_mod_primitiveRoot {K : Type*} [CommRing K] {ω : K} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (n : ℕ) : ω ^ n = ω ^ (n % d) := by
  conv_lhs => rw [← Nat.div_add_mod n d, pow_add, pow_mul]
  simp [hω.pow_eq_one]

/-- q-binomial at q=1 gives ordinary binomial coefficient -/
theorem qBinomial_eval_one (n k : ℕ) : (qBinomial n k).eval 1 = n.choose k := by
  simp only [qBinomial, Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X, one_pow]
  -- Each term evaluates to 1, so we're counting the number of terms
  simp only [sum_const]
  -- The number of k-element subsets of {0,...,n-1} is n.choose k
  rw [← powersetCard_eq_filter, card_powersetCard, card_range]
  simp

/-- q-binomial is 0 when k > n -/
theorem qBinomial_eq_zero_of_lt (n k : ℕ) (h : n < k) : qBinomial n k = 0 := by
  simp only [qBinomial]
  apply Finset.sum_eq_zero
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS
  have : S.card ≤ (Finset.range n).card := Finset.card_le_card hS.1
  simp only [Finset.card_range] at this
  omega

/-- q-binomial boundary case: [n choose 0]_q = 1 -/
theorem qBinomial_zero_right (n : ℕ) : qBinomial n 0 = 1 := by
  simp only [qBinomial]
  have h : (Finset.range n).powerset.filter (fun S => S.card = 0) = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton, Finset.card_eq_zero]
    constructor
    · intro ⟨_, h2⟩; exact h2
    · intro h; simp [h]
  rw [h, Finset.sum_singleton]
  simp

/-- q-binomial boundary case: [n choose n]_q = 1 -/
theorem qBinomial_self (n : ℕ) : qBinomial n n = 1 := by
  simp only [qBinomial]
  have h : (Finset.range n).powerset.filter (fun S => S.card = n) = {Finset.range n} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · intro ⟨h1, h2⟩
      exact Finset.eq_of_subset_of_card_le h1 (by simp [h2])
    · intro h
      simp [h]
  rw [h, Finset.sum_singleton]
  simp

/-! ### Bridge to Canonical q-Binomial Definition

The local `qBinomial` definition uses 0-indexed k-subsets of `{0, 1, ..., n-1}`,
while the canonical `AlgebraicCombinatorics.qBinomialPoly` uses monotone functions.
This section proves they are equal.
-/

/-- Helper: The sum of `{0, 1, ..., k-1}` equals `k*(k-1)/2`. -/
private lemma sum_range_id_eq (k : ℕ) : (Finset.range k).sum id = k * (k - 1) / 2 :=
  Finset.sum_range_id k

/-- For a k-element subset S of {0, ..., n-1}, the i-th smallest element is at least i. -/
private lemma orderEmbOfFin_ge_index {S : Finset ℕ} {k : ℕ} (hcard : S.card = k) (i : Fin k) :
    i.val ≤ S.orderEmbOfFin hcard i := by
  match i with
  | ⟨0, _⟩ => exact Nat.zero_le _
  | ⟨j + 1, hj⟩ =>
    have ih : j ≤ S.orderEmbOfFin hcard ⟨j, Nat.lt_of_succ_lt hj⟩ :=
      orderEmbOfFin_ge_index hcard ⟨j, Nat.lt_of_succ_lt hj⟩
    have hmono : S.orderEmbOfFin hcard ⟨j, Nat.lt_of_succ_lt hj⟩ <
                 S.orderEmbOfFin hcard ⟨j + 1, hj⟩ := by
      apply (S.orderEmbOfFin hcard).strictMono
      simp only [Fin.lt_def]
      omega
    calc (j + 1 : ℕ) ≤ S.orderEmbOfFin hcard ⟨j, Nat.lt_of_succ_lt hj⟩ + 1 := by omega
      _ ≤ S.orderEmbOfFin hcard ⟨j + 1, hj⟩ := hmono

/-- For a k-element subset S of {0, ..., n-1}, the i-th smallest element is at most n - k + i. -/
private lemma orderEmbOfFin_le_sub_card_add {S : Finset ℕ} {n k : ℕ}
    (hS : S ⊆ Finset.range n) (hcard : S.card = k) (i : Fin k) :
    S.orderEmbOfFin hcard i ≤ n - k + i := by
  have hkn : k ≤ n := by
    calc k = S.card := hcard.symm
      _ ≤ (Finset.range n).card := Finset.card_le_card hS
      _ = n := Finset.card_range n
  have hk_pos : 0 < k := Fin.pos i
  by_contra h
  push Not at h
  set T : Finset ℕ := (Finset.univ : Finset (Fin k)).filter (fun j => i ≤ j) |>.image (S.orderEmbOfFin hcard) with hT_def
  have hT_card : T.card = k - i := by
    rw [hT_def, Finset.card_image_of_injective _ (S.orderEmbOfFin hcard).injective]
    have heq : (Finset.univ : Finset (Fin k)).filter (fun j => i ≤ j) =
               Finset.Icc i ⟨k - 1, by omega⟩ := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
      exact ⟨fun hj => ⟨hj, by simp only [Fin.le_def]; omega⟩, fun ⟨hj, _⟩ => hj⟩
    rw [heq]; have hcard_Icc : (Finset.Icc i ⟨k - 1, by omega⟩).card = k - 1 + 1 - i.val := by simp
    rw [hcard_Icc]; omega
  have hT_subset : T ⊆ Finset.Ico (n - k + i + 1) n := by
    intro x hx; rw [hT_def] at hx
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨j, hji, hj⟩ := hx; simp only [Finset.mem_Ico]
    exact ⟨by rw [← hj]; have hmono := (S.orderEmbOfFin hcard).monotone hji; omega,
           by rw [← hj]; exact Finset.mem_range.mp (hS (Finset.orderEmbOfFin_mem S hcard j))⟩
  have hcount : T.card ≤ (Finset.Ico (n - k + i + 1) n).card := Finset.card_le_card hT_subset
  rw [hT_card, Nat.card_Ico] at hcount; omega

/-- The function i ↦ orderEmbOfFin S i - i is monotone. -/
private lemma orderEmbOfFin_sub_mono {S : Finset ℕ} {k : ℕ} (hcard : S.card = k)
    (i j : Fin k) (hij : i ≤ j) :
    S.orderEmbOfFin hcard i - i ≤ S.orderEmbOfFin hcard j - j := by
  by_cases heq : i = j
  · simp [heq]
  · have hlt : i < j := lt_of_le_of_ne hij heq
    have hle : S.orderEmbOfFin hcard i ≤ S.orderEmbOfFin hcard j := (S.orderEmbOfFin hcard).monotone hij
    have hdiff : S.orderEmbOfFin hcard j - S.orderEmbOfFin hcard i ≥ j - i := by
      let T := (Finset.Icc i j).image (S.orderEmbOfFin hcard)
      have hT_card : T.card = j.val - i.val + 1 := by
        rw [Finset.card_image_of_injective _ (S.orderEmbOfFin hcard).injective]
        simp [Fin.card_Icc]; omega
      have hT_subset : T ⊆ Finset.Icc (S.orderEmbOfFin hcard i) (S.orderEmbOfFin hcard j) := by
        intro x hx; simp only [T, Finset.mem_image, Finset.mem_Icc] at hx ⊢
        obtain ⟨m, ⟨hmi, hmj⟩, hm⟩ := hx
        exact ⟨by rw [← hm]; exact (S.orderEmbOfFin hcard).monotone hmi,
               by rw [← hm]; exact (S.orderEmbOfFin hcard).monotone hmj⟩
      have hcount' := Finset.card_le_card hT_subset
      rw [hT_card, Nat.card_Icc] at hcount'; omega
    omega

/-- The local `qBinomial` equals the canonical `qBinomialPoly` from `QBinomialBasic.lean`.

This bridge lemma connects the subset-sum definition used in this file
(which uses 0-indexed subsets of `{0, 1, ..., n-1}`) with the canonical
monotone function definition in `QBinomialBasic.lean`.

The key bijection: for a k-subset S = {s₀ < s₁ < ... < sₖ₋₁} of {0,...,n-1},
define f(i) = sᵢ - i. This is a monotone function Fin k → Fin (n-k+1), and
∑ᵢ f(i) = ∑ᵢ sᵢ - ∑ᵢ i = S.sum id - (range k).sum id.
-/
theorem qBinomial_eq_canonical (n k : ℕ) :
    qBinomial n k = AlgebraicCombinatorics.qBinomialPoly n k := by
  unfold qBinomial AlgebraicCombinatorics.qBinomialPoly
  by_cases hkn : k ≤ n
  · -- Main case: k ≤ n
    simp only [hkn, ↓reduceIte]
    rw [← Finset.powersetCard_eq_filter]
    -- Define the bijection φ : k-subsets → monotone functions
    let φ : (S : Finset ℕ) → S ∈ (Finset.range n).powersetCard k → (Fin k → Fin (n - k + 1)) :=
      fun S hS => fun i => ⟨S.orderEmbOfFin (mem_powersetCard.mp hS).2 i - i, by
        have hSsub := (mem_powersetCard.mp hS).1
        have hScard := (mem_powersetCard.mp hS).2
        have hle := orderEmbOfFin_le_sub_card_add hSsub hScard i
        omega⟩
    apply Finset.sum_bij φ
    · -- φ S maps into monotoneFunctions
      intro S hS
      simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i j hij
      simp only [Fin.le_def]
      exact orderEmbOfFin_sub_mono (mem_powersetCard.mp hS).2 i j hij
    · -- Injectivity
      intro S hS T hT heq
      have heq' : ∀ i, S.orderEmbOfFin (mem_powersetCard.mp hS).2 i = 
                       T.orderEmbOfFin (mem_powersetCard.mp hT).2 i := by
        intro i
        have h : (φ S hS i).val = (φ T hT i).val := by rw [heq]
        -- φ S hS i = ⟨S.orderEmbOfFin _ i - i, _⟩, so (φ S hS i).val = S.orderEmbOfFin _ i - i
        change S.orderEmbOfFin (mem_powersetCard.mp hS).2 i - i = 
               T.orderEmbOfFin (mem_powersetCard.mp hT).2 i - i at h
        have hSge := orderEmbOfFin_ge_index (mem_powersetCard.mp hS).2 i
        have hTge := orderEmbOfFin_ge_index (mem_powersetCard.mp hT).2 i
        omega
      ext x
      constructor
      · intro hx
        have hxrange : x ∈ Set.range (S.orderEmbOfFin (mem_powersetCard.mp hS).2) := by
          rw [Finset.range_orderEmbOfFin]; exact hx
        obtain ⟨i, hi⟩ := hxrange
        rw [heq' i] at hi
        have : x ∈ Set.range (T.orderEmbOfFin (mem_powersetCard.mp hT).2) := ⟨i, hi⟩
        rw [Finset.range_orderEmbOfFin] at this
        exact this
      · intro hx
        have hxrange : x ∈ Set.range (T.orderEmbOfFin (mem_powersetCard.mp hT).2) := by
          rw [Finset.range_orderEmbOfFin]; exact hx
        obtain ⟨i, hi⟩ := hxrange
        rw [← heq' i] at hi
        have : x ∈ Set.range (S.orderEmbOfFin (mem_powersetCard.mp hS).2) := ⟨i, hi⟩
        rw [Finset.range_orderEmbOfFin] at this
        exact this
    · -- Surjectivity
      intro f hf
      simp only [monotoneFunctions, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      let S := Finset.univ.image (fun i : Fin k => (f i).val + i.val)
      have hSsub : S ⊆ Finset.range n := by
        intro x hx
        simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨i, hi⟩ := hx
        rw [← hi, Finset.mem_range]
        have hfi : (f i).val < n - k + 1 := (f i).isLt
        have hi' : i.val < k := i.isLt
        omega
      have hScard : S.card = k := by
        have hinj : Function.Injective (fun i : Fin k => (f i).val + i.val) := by
          intro a b hab
          simp only at hab
          -- hab : (f a).val + a.val = (f b).val + b.val
          by_contra hne
          have hab' : a < b ∨ b < a := lt_or_gt_of_ne hne
          rcases hab' with hab' | hab'
          · have hfab : (f a).val ≤ (f b).val := Fin.val_fin_le.mpr (hf (le_of_lt hab'))
            have : (f a).val + a.val < (f b).val + b.val := by
              calc (f a).val + a.val < (f a).val + b.val := by omega
                _ ≤ (f b).val + b.val := by omega
            omega
          · have hfba : (f b).val ≤ (f a).val := Fin.val_fin_le.mpr (hf (le_of_lt hab'))
            have : (f b).val + b.val < (f a).val + a.val := by
              calc (f b).val + b.val < (f b).val + a.val := by omega
                _ ≤ (f a).val + a.val := by omega
            omega
        simp only [S, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      use S
      refine ⟨mem_powersetCard.mpr ⟨hSsub, hScard⟩, ?_⟩
      ext i
      simp only [φ]
      have hg_strictMono : StrictMono (fun j : Fin k => (f j).val + j.val) := by
        intro a b hab
        have hfab : (f a).val ≤ (f b).val := Fin.val_fin_le.mpr (hf (le_of_lt hab))
        have hfa : (f a).val < n - k + 1 := (f a).isLt
        have hfb : (f b).val < n - k + 1 := (f b).isLt
        have hav : a.val < k := a.isLt
        have hbv : b.val < k := b.isLt
        calc (f a).val + a.val < (f a).val + b.val := by omega
          _ ≤ (f b).val + b.val := by omega
      have heq : (fun j : Fin k => (f j).val + j.val) = S.orderEmbOfFin hScard := by
        apply Finset.orderEmbOfFin_unique
        · intro x
          simp only [S, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨x, rfl⟩
        · exact hg_strictMono
      have := congr_fun heq i
      have hge := orderEmbOfFin_ge_index hScard i
      omega
    · -- Exponents match
      intro S hS
      have hScard := (mem_powersetCard.mp hS).2
      congr 1
      have h1 : S.sum id = ∑ i : Fin k, (S.orderEmbOfFin hScard i : ℕ) := by
        have hinj := (S.orderEmbOfFin hScard).injective
        have himage : (Finset.univ : Finset (Fin k)).image (S.orderEmbOfFin hScard) = S :=
          Finset.image_orderEmbOfFin_univ S hScard
        calc S.sum id = ∑ x ∈ S, (x : ℕ) := rfl
          _ = ∑ x ∈ (Finset.univ : Finset (Fin k)).image (S.orderEmbOfFin hScard), (x : ℕ) := by rw [himage]
          _ = ∑ i ∈ (Finset.univ : Finset (Fin k)), (S.orderEmbOfFin hScard i : ℕ) := by
              rw [Finset.sum_image hinj.injOn]
          _ = ∑ i : Fin k, (S.orderEmbOfFin hScard i : ℕ) := by simp
      have h2 : (Finset.range k).sum id = ∑ i : Fin k, i.val := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_range] at hx
        simp [hx]
      rw [h1, h2]
      have h3 : ∀ i : Fin k, i.val ≤ S.orderEmbOfFin hScard i := orderEmbOfFin_ge_index hScard
      have h4 : (∑ i : Fin k, S.orderEmbOfFin hScard i) - (∑ i : Fin k, i.val) =
                ∑ i : Fin k, (S.orderEmbOfFin hScard i - i.val) := by
        have hle : ∑ i : Fin k, i.val ≤ ∑ i : Fin k, (S.orderEmbOfFin hScard i : ℕ) :=
          Finset.sum_le_sum (fun i _ => h3 i)
        have h5 : ∑ i : Fin k, (S.orderEmbOfFin hScard i : ℕ) =
                  ∑ i : Fin k, ((S.orderEmbOfFin hScard i : ℕ) - i.val + i.val) := by
          congr 1; ext i; exact (Nat.sub_add_cancel (h3 i)).symm
        rw [h5, Finset.sum_add_distrib]
        omega
      rw [h4]
  · -- Case k > n: both sides are 0
    push Not at hkn
    simp only [↓reduceIte, not_le.mpr hkn]
    rw [← Finset.powersetCard_eq_filter]
    apply Finset.sum_eq_zero
    intro S hS
    simp only [mem_powersetCard] at hS
    have : S.card ≤ (Finset.range n).card := Finset.card_le_card hS.1
    simp only [card_range] at this
    omega


/-! #### d-Cycle Infrastructure for q-Lucas

The key to proving the q-Lucas theorem is the d-cycle cancellation argument.
For a primitive d-th root of unity ω, we have ∑_{j=0}^{d-1} ω^j = 0 (when d > 1).
This allows us to cancel contributions from subsets that don't respect the "block structure"
where blocks are consecutive intervals of size d.
-/

/-- A subset S of [n] is d-blocky if for each complete d-block {id, id+1, ..., id+d-1}
contained in [n], the set S either contains all elements or none of the elements. -/
def IsDBlocky (d n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.range n ∧
  ∀ i < n / d,
    (∀ j < d, i * d + j ∈ S) ∨ (∀ j < d, i * d + j ∉ S)

instance decidableIsDBlocky (d n : ℕ) (S : Finset ℕ) : Decidable (IsDBlocky d n S) := by
  unfold IsDBlocky
  infer_instance

/-- The set of k-element subsets of [n]. -/
def kSubsets (n k : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powersetCard k

/-- The set of d-blocky k-element subsets of [n]. -/
def blockySubsets (d n k : ℕ) : Finset (Finset ℕ) :=
  (kSubsets n k).filter (fun S => IsDBlocky d n S)

/-- For d > 1, the sum ∑_{j=0}^{d-1} ω^j = 0 when ω is a primitive d-th root of unity. -/
theorem primitiveRoot_geom_sum_zero {K : Type*} [Field K] {ω : K} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 1 < d) :
    ∑ j ∈ Finset.range d, ω ^ j = 0 :=
  hω.geom_sum_eq_zero hd

/-- For a subset S of [n], the smallest complete d-block index where S is "split"
(i.e., contains some but not all elements). Returns none if S is d-blocky. -/
def smallestSplitBlock (d n : ℕ) (S : Finset ℕ) : Option ℕ :=
  (Finset.range (n / d)).filter (fun i =>
    let blockStart := i * d
    (∃ j < d, blockStart + j ∈ S) ∧ (∃ j < d, blockStart + j ∉ S)) |>.min

/-- Given a split block at index i, find the smallest offset j such that i*d + j is in S. -/
def smallestInBlock (d i : ℕ) (S : Finset ℕ) : Option ℕ :=
  (Finset.range d).filter (fun j => i * d + j ∈ S) |>.min

/-- The d-cycle switch operation: for a non-d-blocky subset S with smallest split block i,
find the smallest element in that block that's in S, and swap it with the next element (mod d).
This operation has the property that applying it d times returns to the original set. -/
def dCycleSwitch (d n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  match smallestSplitBlock d n S with
  | none => S  -- S is d-blocky on complete blocks
  | some i =>
    match smallestInBlock d i S with
    | none => S  -- shouldn't happen if split
    | some j =>
      let elem := i * d + j
      let nextElem := i * d + (j + 1) % d
      -- If nextElem is already in S, we need a different approach
      -- For now, we use a simpler swap that may not preserve the set structure perfectly
      if nextElem ∈ S then S
      else insert nextElem (S.erase elem)

/-- Key algebraic lemma: ω^(d/m) is a primitive m-th root when m | d -/
private lemma isPrimitiveRoot_pow_div {K : Type*} [CommRing K] [IsDomain K] {ω : K} {d m : ℕ}
    (hω : IsPrimitiveRoot ω d) (hm : m ∣ d) (hm_pos : 0 < m) (hd_pos : 0 < d) :
    IsPrimitiveRoot (ω ^ (d / m)) m := by
  have hdiv_pos : 0 < d / m := Nat.div_pos (Nat.le_of_dvd hd_pos hm) hm_pos
  refine ⟨?_, ?_⟩
  · rw [← pow_mul, Nat.div_mul_cancel hm, hω.pow_eq_one]
  · intro j hj
    rw [← pow_mul] at hj
    have hdvd : d ∣ (d / m) * j := hω.dvd_of_pow_eq_one (d / m * j) hj
    obtain ⟨c, hc⟩ := hdvd
    have hdk : d = (d / m) * m := (Nat.div_mul_cancel hm).symm
    have : (d / m) * j = (d / m) * (m * c) := by
      calc (d / m) * j = d * c := hc
        _ = (d / m) * m * c := by rw [← hdk]
        _ = (d / m) * (m * c) := by ring
    have hj_eq : j = m * c := Nat.eq_of_mul_eq_mul_left hdiv_pos this
    exact ⟨c, hj_eq⟩

/-- Corollary: sum of geometric progression with ratio ω^(d/m) is 0 when 1 < m | d -/
private lemma geom_sum_pow_div_zero {K : Type*} [Field K] {ω : K} {d m : ℕ}
    (hω : IsPrimitiveRoot ω d) (hm : m ∣ d) (hm1 : 1 < m) (hd1 : 1 < d) :
    ∑ j ∈ Finset.range m, (ω ^ (d / m)) ^ j = 0 := by
  have hd_pos : 0 < d := by omega
  have hm_pos : 0 < m := by omega
  exact (isPrimitiveRoot_pow_div hω hm hm_pos hd_pos).geom_sum_eq_zero hm1

/-- Key algebraic lemma for orbit sums: Given 0 < j < d, the sum
∑_{k=0}^{m-1} ω^(baseSum + k*j) = 0 where m = d/gcd(d,j).

This is the algebraic core of the d-cycle cancellation argument.
For each non-blocky set S with smallest split block i, let j = |blockOffsets d i S|.
The orbit of S under rotation in block i has size m = d/gcd(d,j), and this lemma
shows that the sum of ω^(sum T) over the orbit is 0. -/
lemma orbit_sum_eq_zero {K : Type*} [Field K] {ω : K} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 1 < d) (baseSum : ℕ) (j : ℕ) (hj_pos : 0 < j) (hj_lt : j < d) :
    let m := d / Nat.gcd d j
    ∑ k ∈ Finset.range m, ω ^ (baseSum + k * j) = 0 := by
  intro m
  have hd_pos : 0 < d := by omega
  have hgcd_pos : 0 < Nat.gcd d j := Nat.gcd_pos_of_pos_left j hd_pos
  have hgcd_dvd : Nat.gcd d j ∣ d := Nat.gcd_dvd_left d j
  have hgcd_le : Nat.gcd d j ≤ j := Nat.gcd_le_right d hj_pos
  have hgcd_lt : Nat.gcd d j < d := Nat.lt_of_le_of_lt hgcd_le hj_lt
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hd_pos hgcd_dvd) hgcd_pos
  have hgcd_mul_m : Nat.gcd d j * m = d := by
    simp only [m]
    rw [mul_comm, Nat.div_mul_cancel hgcd_dvd]
  have hm_gt_one : 1 < m := by
    by_contra hle
    push Not at hle
    have : m = 0 ∨ m = 1 := by omega
    rcases this with hm0 | hm1
    · omega
    · have : Nat.gcd d j = d := by
        calc Nat.gcd d j = Nat.gcd d j * 1 := by ring
          _ = Nat.gcd d j * m := by rw [hm1]
          _ = d := hgcd_mul_m
      omega
  -- Factor out ω^baseSum
  have h1 : ∑ k ∈ Finset.range m, ω ^ (baseSum + k * j) =
            ω ^ baseSum * ∑ k ∈ Finset.range m, ω ^ (k * j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    rw [← pow_add]
  rw [h1]
  -- Rewrite as geometric sum
  have h2 : ∑ k ∈ Finset.range m, ω ^ (k * j) = ∑ k ∈ Finset.range m, (ω ^ j) ^ k := by
    apply sum_congr rfl
    intro k _
    rw [← pow_mul, mul_comm]
  rw [h2]
  -- Show (ω^j)^m = 1
  have hj_gcd_dvd : Nat.gcd d j ∣ j := Nat.gcd_dvd_right d j
  have h3 : (ω ^ j) ^ m = 1 := by
    rw [← pow_mul]
    have : j * m = d * (j / Nat.gcd d j) := by
      have h := Nat.div_mul_cancel hj_gcd_dvd
      have h' := Nat.div_mul_cancel hgcd_dvd
      calc j * m = j * (d / Nat.gcd d j) := rfl
        _ = (j / Nat.gcd d j) * Nat.gcd d j * (d / Nat.gcd d j) := by rw [h]
        _ = (j / Nat.gcd d j) * (Nat.gcd d j * (d / Nat.gcd d j)) := by ring
        _ = (j / Nat.gcd d j) * d := by rw [mul_comm (Nat.gcd d j), h']
        _ = d * (j / Nat.gcd d j) := by ring
    rw [this, pow_mul, hω.pow_eq_one, one_pow]
  -- Show ω^j ≠ 1
  have hj_ne_one : ω ^ j ≠ 1 := by
    intro heq
    have hdvd : d ∣ j := hω.dvd_of_pow_eq_one j heq
    rcases hdvd with ⟨c, hc⟩
    cases c with
    | zero => simp at hc; omega
    | succ c =>
      have : d ≤ j := by calc d = d * 1 := by ring
        _ ≤ d * (c + 1) := Nat.mul_le_mul_left d (Nat.succ_pos c)
        _ = j := hc.symm
      omega
  -- Use geometric sum formula
  rw [geom_sum_eq hj_ne_one, h3, sub_self, zero_div, mul_zero]

/-- Orbit sum over full range d: Given 0 < j < d, the sum
∑_{k=0}^{d-1} ω^(baseSum + k*j) = 0.

This is a stronger version of orbit_sum_eq_zero that sums over the full range d
instead of range m where m = d/gcd(d,j). The sum is still 0 because ω^j is a 
primitive (d/gcd(d,j))-th root of unity, and the geometric series formula applies.

This lemma is useful when we need to work with the full orbit of size d rather than
the reduced orbit of size m. The algebraic cancellation still works because the
sums repeat with period m, and each period sums to 0. -/
lemma orbit_sum_full_eq_zero {K : Type*} [Field K] {ω : K} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 1 < d) (baseSum : ℕ) (j : ℕ) (hj_pos : 0 < j) (hj_lt : j < d) :
    ∑ k ∈ Finset.range d, ω ^ (baseSum + k * j) = 0 := by
  have hd_pos : 0 < d := by omega
  -- ω^j ≠ 1 since 0 < j < d and ω is a primitive d-th root
  have hωj_ne_one : ω ^ j ≠ 1 := by
    intro heq
    have hdvd : d ∣ j := hω.dvd_of_pow_eq_one j heq
    rcases hdvd with ⟨c, hc⟩
    cases c with
    | zero => simp at hc; omega
    | succ c =>
      have : d ≤ j := by calc d = d * 1 := by ring
        _ ≤ d * (c + 1) := Nat.mul_le_mul_left d (Nat.succ_pos c)
        _ = j := hc.symm
      omega
  -- ∑_{k=0}^{d-1} ω^(baseSum + k*j) = ω^baseSum * ∑_{k=0}^{d-1} (ω^j)^k
  have hsum_factor : ∑ k ∈ Finset.range d, ω ^ (baseSum + k * j) = 
                     ω ^ baseSum * ∑ k ∈ Finset.range d, (ω ^ j) ^ k := by
    rw [Finset.mul_sum]
    congr 1
    ext k
    rw [pow_add, mul_comm k j, pow_mul]
  rw [hsum_factor]
  -- Use geometric series formula: ∑_{k=0}^{n-1} x^k = (x^n - 1) / (x - 1) for x ≠ 1
  rw [geom_sum_eq hωj_ne_one]
  -- (ω^j)^d = ω^(j*d) = (ω^d)^j = 1^j = 1
  have hωjd : (ω ^ j) ^ d = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  rw [hωjd, sub_self, zero_div, mul_zero]

/-- Helper lemma: if the sum over range d is 0 and all elements of the image appear
with uniform multiplicity c > 0, then the sum over the image is also 0.

This is used to prove orbit sums are 0 when the orbit might have fewer than d elements.
The key insight is that rotation is a group action, so all orbit elements appear
the same number of times (by orbit-stabilizer theorem). -/
private lemma sum_image_eq_zero_of_uniform_multiplicity {α : Type*} [DecidableEq α] 
    {K : Type*} [Field K] [CharZero K] (f : ℕ → α) (g : α → K) (d : ℕ)
    (hsum_zero : ∑ k ∈ Finset.range d, g (f k) = 0)
    (hstab : ∃ c : ℕ, 0 < c ∧ ∀ T ∈ (Finset.range d).image f, 
        ((Finset.range d).filter (fun k => f k = T)).card = c) :
    ∑ T ∈ (Finset.range d).image f, g T = 0 := by
  obtain ⟨c, hc_pos, hc_eq⟩ := hstab
  have hchar_ne : (c : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hc_pos)
  -- ∑_{k < d} g(f(k)) = c * ∑_{T ∈ image} g(T)
  have hsum_eq : ∑ k ∈ Finset.range d, g (f k) = (c : K) * ∑ T ∈ (Finset.range d).image f, g T := by
    rw [mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range d) (t := (Finset.range d).image f) 
        (fun k hk => Finset.mem_image_of_mem f hk) (fun k => g (f k))]
    apply Finset.sum_congr rfl
    intro T hT
    have hsum_fiber : ∑ a ∈ (Finset.range d).filter (fun a => f a = T), g (f a) = 
                      ((Finset.range d).filter (fun a => f a = T)).card * g T := by
      rw [← nsmul_eq_mul]
      apply Finset.sum_eq_card_nsmul
      intro a ha
      simp only [Finset.mem_filter] at ha
      rw [ha.2]
    rw [hsum_fiber, hc_eq T hT]
  rw [hsum_eq] at hsum_zero
  exact (mul_eq_zero.mp hsum_zero).resolve_left hchar_ne

/-- Key lemma: if ω is a primitive d-th root of unity, then any divisor of d is nonzero in K.
This follows from IsPrimitiveRoot.neZero' which shows d ≠ 0 in K. -/
private lemma divisor_ne_zero_of_primitiveRoot {K : Type*} [Field K] {d : ℕ} {ω : K} 
    (hω : IsPrimitiveRoot ω d) (hd : 0 < d) (c : ℕ) (hc_dvd : c ∣ d) : 
    (c : K) ≠ 0 := by
  by_cases hc_zero : c = 0
  · simp only [hc_zero] at hc_dvd
    simp at hc_dvd
    omega
  · haveI : NeZero d := ⟨Nat.pos_iff_ne_zero.mp hd⟩
    have hne : NeZero ((d : ℕ) : K) := hω.neZero'
    intro hzero
    have hchar : ringChar K ∣ c := ringChar.dvd hzero
    have hchar_d : ringChar K ∣ d := dvd_trans hchar hc_dvd
    have hne' : (d : K) ≠ 0 := hne.out
    have hd_zero : (d : K) = 0 := (ringChar.spec K d).mpr hchar_d
    exact hne' hd_zero

/-- Variant of sum_image_eq_zero_of_uniform_multiplicity that uses IsPrimitiveRoot
instead of CharZero. The key insight is that if ω is a primitive d-th root of unity,
then any divisor of d is nonzero in K. -/
private lemma sum_image_eq_zero_of_uniform_multiplicity_primitiveRoot {α : Type*} [DecidableEq α] 
    {K : Type*} [Field K] {d : ℕ} {ω : K} (hω : IsPrimitiveRoot ω d) (hd : 0 < d)
    (f : ℕ → α) (g : α → K)
    (hsum_zero : ∑ k ∈ Finset.range d, g (f k) = 0)
    (hstab : ∃ c : ℕ, c ∣ d ∧ ∀ T ∈ (Finset.range d).image f, 
        ((Finset.range d).filter (fun k => f k = T)).card = c) :
    ∑ T ∈ (Finset.range d).image f, g T = 0 := by
  obtain ⟨c, hc_dvd, hc_eq⟩ := hstab
  have hc_ne : (c : K) ≠ 0 := divisor_ne_zero_of_primitiveRoot hω hd c hc_dvd
  -- ∑_{k < d} g(f(k)) = c * ∑_{T ∈ image} g(T)
  have hsum_eq : ∑ k ∈ Finset.range d, g (f k) = (c : K) * ∑ T ∈ (Finset.range d).image f, g T := by
    rw [mul_sum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range d) (t := (Finset.range d).image f) 
        (fun k hk => Finset.mem_image_of_mem f hk) (fun k => g (f k))]
    apply Finset.sum_congr rfl
    intro T hT
    have hsum_fiber : ∑ a ∈ (Finset.range d).filter (fun a => f a = T), g (f a) = 
                      ((Finset.range d).filter (fun a => f a = T)).card * g T := by
      rw [← nsmul_eq_mul]
      apply Finset.sum_eq_card_nsmul
      intro a ha
      simp only [Finset.mem_filter] at ha
      rw [ha.2]
    rw [hsum_fiber, hc_eq T hT]
  rw [hsum_eq] at hsum_zero
  exact (mul_eq_zero.mp hsum_zero).resolve_left hc_ne

/-! #### Rotation infrastructure for orbit cancellation -/

/-- Helper: offsets in block i that are in S -/
private def blockOffsets (d : ℕ) (i : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range d).filter (fun j => i * d + j ∈ S)

/-- A block is "split" if it has some but not all elements -/
private def isSplitBlock (d n : ℕ) (i : ℕ) (S : Finset ℕ) : Prop :=
  i < n / d ∧ 0 < (blockOffsets d i S).card ∧ (blockOffsets d i S).card < d

/-- Rotate elements within block i by 1 (cyclically mod d) -/
private def rotateInBlock (d : ℕ) (i : ℕ) (x : ℕ) : ℕ :=
  if i * d ≤ x ∧ x < (i + 1) * d then
    i * d + (x - i * d + 1) % d
  else
    x

/-- Apply rotation to a set -/
private def rotateSetInBlock (d : ℕ) (i : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.image (rotateInBlock d i)

/-- Iterate rotation k times -/
private def rotateSetInBlockK (d : ℕ) (i : ℕ) (k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (rotateSetInBlock d i)^[k] S

/-- For non-blocky S, there exists a split block -/
private lemma nonBlocky_has_split_block {d n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) (hNB : ¬IsDBlocky d n S) :
    ∃ i < n / d, isSplitBlock d n i S := by
  unfold IsDBlocky at hNB
  simp only [not_and, not_forall, not_or] at hNB
  obtain ⟨i, hi, ⟨j1, hj1_lt, hj1_out⟩, ⟨j2, hj2_lt, hj2_in⟩⟩ := hNB hS
  use i, hi
  constructor
  · exact hi
  constructor
  · rw [Finset.card_pos]
    use j2
    simp only [blockOffsets, mem_filter, mem_range]
    exact ⟨hj2_lt, not_not.mp hj2_in⟩
  · by_contra hge
    push Not at hge
    have hfull : (blockOffsets d i S).card = d := by
      have hsub : blockOffsets d i S ⊆ Finset.range d := by
        intro x hx
        simp only [blockOffsets, mem_filter] at hx
        exact hx.1
      have hle := Finset.card_le_card hsub
      simp only [card_range] at hle
      omega
    have : blockOffsets d i S = Finset.range d := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [blockOffsets, mem_filter] at hx
        exact hx.1
      · simp [hfull]
    have hj1_in_offsets : j1 ∈ blockOffsets d i S := by
      rw [this]
      exact mem_range.mpr hj1_lt
    simp only [blockOffsets, mem_filter, mem_range] at hj1_in_offsets
    exact hj1_out hj1_in_offsets.2

/-- The rotation function is injective. -/
lemma rotateInBlock_injective (d : ℕ) (i : ℕ) (hd : 0 < d) :
    Function.Injective (rotateInBlock d i) := by
  intro x y hxy
  simp only [rotateInBlock] at hxy
  split_ifs at hxy with hxin hyin hyin
  · -- Both in block
    have heq' : (x - i * d + 1) % d = (y - i * d + 1) % d := by omega
    have hx_off : x - i * d < d := Nat.sub_lt_left_of_lt_add hxin.1 (by linarith [hxin.2])
    have hy_off : y - i * d < d := Nat.sub_lt_left_of_lt_add hyin.1 (by linarith [hyin.2])
    by_cases hxw : x - i * d + 1 = d
    · by_cases hyw : y - i * d + 1 = d
      · omega
      · rw [hxw, Nat.mod_self, Nat.mod_eq_of_lt (by omega : y - i * d + 1 < d)] at heq'; omega
    · by_cases hyw : y - i * d + 1 = d
      · rw [hyw, Nat.mod_self, Nat.mod_eq_of_lt (by omega : x - i * d + 1 < d)] at heq'; omega
      · rw [Nat.mod_eq_of_lt (by omega : x - i * d + 1 < d),
            Nat.mod_eq_of_lt (by omega : y - i * d + 1 < d)] at heq'; omega
  · -- x in block, y not in block
    exfalso
    have hmod_lt : (x - i * d + 1) % d < d := Nat.mod_lt _ hd
    have hrot_lt : i * d + (x - i * d + 1) % d < (i + 1) * d := by
      have h1 : i * d + (x - i * d + 1) % d < i * d + d := Nat.add_lt_add_left hmod_lt _
      linarith [Nat.mul_add_one i d]
    have hrot_ge : i * d ≤ i * d + (x - i * d + 1) % d := Nat.le_add_right _ _
    rw [hxy] at hrot_lt hrot_ge
    exact hyin ⟨hrot_ge, hrot_lt⟩
  · -- x not in block, y in block
    exfalso
    have hmod_lt : (y - i * d + 1) % d < d := Nat.mod_lt _ hd
    have hrot_lt : i * d + (y - i * d + 1) % d < (i + 1) * d := by
      have h1 : i * d + (y - i * d + 1) % d < i * d + d := Nat.add_lt_add_left hmod_lt _
      linarith [Nat.mul_add_one i d]
    have hrot_ge : i * d ≤ i * d + (y - i * d + 1) % d := Nat.le_add_right _ _
    rw [← hxy] at hrot_lt hrot_ge
    exact hxin ⟨hrot_ge, hrot_lt⟩
  · -- Neither in block
    exact hxy

/-- Rotation does not change elements outside block i. -/
private lemma rotateInBlock_outside (d : ℕ) (i : ℕ) (x : ℕ)
    (hx : ¬(i * d ≤ x ∧ x < (i + 1) * d)) :
    rotateInBlock d i x = x := by
  simp only [rotateInBlock, ite_eq_right hx]

/-- For ω^a = ω^b when ω is primitive d-th root and a ≡ b (mod d). -/
private lemma pow_eq_of_diff_mod {K : Type*} [Field K] {ω : K} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (a b : ℕ) (h : a % d = b % d) :
    ω ^ a = ω ^ b := by
  have ha : a = a / d * d + a % d := (Nat.div_add_mod' a d).symm
  have hb : b = b / d * d + b % d := (Nat.div_add_mod' b d).symm
  rw [ha, hb, pow_add, pow_add]
  have h1 : ω ^ (a / d * d) = 1 := by rw [mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have h2 : ω ^ (b / d * d) = 1 := by rw [mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  simp only [h1, h2, one_mul, h]

/-- Rotation changes x by +1 (mod d) when x is in block i.
More precisely: rotateInBlock d i x ≡ x + 1 (mod d) -/
private lemma rotateInBlock_mod (d : ℕ) (i : ℕ) (x : ℕ) (_hd : 0 < d)
    (hx : i * d ≤ x ∧ x < (i + 1) * d) :
    (rotateInBlock d i x) % d = (x + 1) % d := by
  simp only [rotateInBlock, ite_eq_left hx]
  have hoff : x - i * d < d := Nat.sub_lt_left_of_lt_add hx.1 (by linarith [hx.2])
  have hdvd : d ∣ i * d := by rw [mul_comm]; exact dvd_mul_right d i
  have h1 : (i * d + (x - i * d + 1) % d) % d = (x - i * d + 1) % d := by
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, zero_add]; simp
  have h2 : (x + 1) % d = (x - i * d + 1) % d := by
    have hx_eq : x = i * d + (x - i * d) := by omega
    conv_lhs => rw [hx_eq]
    rw [Nat.add_assoc, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, zero_add]; simp
  rw [h1, ← h2]

/-- Elements in block i of a set S -/
private def inBlock (d i : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun x => i * d ≤ x ∧ x < (i + 1) * d)

/-- Elements outside block i of a set S -/
private def outBlock (d i : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun x => ¬(i * d ≤ x ∧ x < (i + 1) * d))

/-- inBlock and outBlock partition S -/
private lemma inBlock_outBlock_partition (d i : ℕ) (S : Finset ℕ) :
    S = inBlock d i S ∪ outBlock d i S := by
  ext x
  simp only [inBlock, outBlock, mem_union, mem_filter]
  constructor
  · intro hx
    by_cases h : i * d ≤ x ∧ x < (i + 1) * d
    · left; exact ⟨hx, h⟩
    · right; exact ⟨hx, h⟩
  · intro hx; rcases hx with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h

/-- inBlock and outBlock are disjoint -/
private lemma inBlock_outBlock_disjoint (d i : ℕ) (S : Finset ℕ) :
    Disjoint (inBlock d i S) (outBlock d i S) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [inBlock, outBlock, mem_filter] at hx1 hx2
  exact hx2.2 hx1.2

/-- The cardinality of inBlock equals the cardinality of blockOffsets -/
private lemma inBlock_card_eq_blockOffsets_card (d i : ℕ) (S : Finset ℕ) :
    (inBlock d i S).card = (blockOffsets d i S).card := by
  apply Finset.card_bij (fun x _ => x - i * d)
  · intro x hx
    simp only [inBlock, mem_filter] at hx
    simp only [blockOffsets, mem_filter, mem_range]
    constructor
    · have hlt : x < (i + 1) * d := hx.2.2
      have hge : i * d ≤ x := hx.2.1
      have h1 : (i + 1) * d = i * d + d := by ring
      omega
    · have hge : i * d ≤ x := hx.2.1
      have heq : x = i * d + (x - i * d) := by omega
      rw [heq] at hx
      exact hx.1
  · intro x₁ hx₁ x₂ hx₂ heq
    simp only [inBlock, mem_filter] at hx₁ hx₂
    omega
  · intro y hy
    simp only [blockOffsets, mem_filter, mem_range] at hy
    use i * d + y
    simp only [inBlock, mem_filter, and_iff_right hy.2]
    refine ⟨⟨Nat.le_add_right _ _, ?_⟩, ?_⟩
    · have h1 : (i + 1) * d = i * d + d := by ring
      omega
    · simp only [Nat.add_sub_cancel_left]

/-- Sum decomposition into inBlock and outBlock -/
private lemma sum_eq_inBlock_add_outBlock (d i : ℕ) (S : Finset ℕ) :
    S.sum id = (inBlock d i S).sum id + (outBlock d i S).sum id := by
  have h := inBlock_outBlock_partition d i S
  conv_lhs => rw [h]
  rw [Finset.sum_union (inBlock_outBlock_disjoint d i S)]

/-- rotateInBlock inside block -/
private lemma rotateInBlock_inside (d : ℕ) (i : ℕ) (x : ℕ)
    (hx : i * d ≤ x ∧ x < (i + 1) * d) :
    rotateInBlock d i x = i * d + (x - i * d + 1) % d := by
  simp only [rotateInBlock, ite_eq_left hx]

/-- Sum over rotated set equals sum with rotateInBlock -/
private lemma rotateSetInBlock_sum_eq (d i : ℕ) (hd : 0 < d) (S : Finset ℕ) :
    (rotateSetInBlock d i S).sum id = S.sum (rotateInBlock d i) := by
  unfold rotateSetInBlock
  rw [Finset.sum_image]
  · simp only [id_eq]
  · intro x _ y _ hxy
    exact rotateInBlock_injective d i hd hxy

/-- Sums are congruent mod d if each term is congruent mod d -/
private lemma sum_congr_mod (d : ℕ) (S : Finset ℕ) (f g : ℕ → ℕ)
    (h : ∀ x ∈ S, f x % d = g x % d) :
    (∑ x ∈ S, f x) % d = (∑ x ∈ S, g x) % d := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s hna ih =>
    rw [sum_insert hna, sum_insert hna]
    have ha : f a % d = g a % d := h a (mem_insert_self a s)
    have hs : ∀ x ∈ s, f x % d = g x % d := fun x hx => h x (mem_insert_of_mem hx)
    have ih' := ih hs
    calc (f a + ∑ x ∈ s, f x) % d
      = (f a % d + (∑ x ∈ s, f x) % d) % d := by rw [Nat.add_mod]
      _ = (g a % d + (∑ x ∈ s, g x) % d) % d := by rw [ha, ih']
      _ = (g a + ∑ x ∈ s, g x) % d := by rw [← Nat.add_mod]

/-- Sum of rotateInBlock over S is congruent to sum + |inBlock| (mod d) -/
private lemma rotateSetInBlock_sum_mod (d i : ℕ) (hd : 0 < d) (S : Finset ℕ) :
    (S.sum (rotateInBlock d i)) % d = (S.sum id + (inBlock d i S).card) % d := by
  have hsum_rot : S.sum (rotateInBlock d i) =
      (inBlock d i S).sum (rotateInBlock d i) + (outBlock d i S).sum (rotateInBlock d i) := by
    have h := inBlock_outBlock_partition d i S
    conv_lhs => rw [h]
    rw [Finset.sum_union (inBlock_outBlock_disjoint d i S)]
  rw [hsum_rot]
  have hout : (outBlock d i S).sum (rotateInBlock d i) = (outBlock d i S).sum id := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [outBlock, mem_filter] at hx
    exact rotateInBlock_outside d i x hx.2
  rw [hout]
  have hin_mod : ((inBlock d i S).sum (rotateInBlock d i)) % d =
                 ((inBlock d i S).sum (fun x => x + 1)) % d := by
    apply sum_congr_mod
    intro x hx
    simp only [inBlock, mem_filter] at hx
    exact rotateInBlock_mod d i x hd hx.2
  have hsum_plus_one : (inBlock d i S).sum (fun x => x + 1) =
                       (inBlock d i S).sum id + (inBlock d i S).card := by
    rw [Finset.sum_add_distrib]
    simp only [sum_const, smul_eq_mul, mul_one, id_eq]
  have hS_sum : S.sum id = (inBlock d i S).sum id + (outBlock d i S).sum id :=
    sum_eq_inBlock_add_outBlock d i S
  calc
    ((inBlock d i S).sum (rotateInBlock d i) + (outBlock d i S).sum id) % d
      = (((inBlock d i S).sum (rotateInBlock d i)) % d + ((outBlock d i S).sum id) % d) % d := by
        rw [Nat.add_mod]
    _ = (((inBlock d i S).sum (fun x => x + 1)) % d + ((outBlock d i S).sum id) % d) % d := by
        rw [hin_mod]
    _ = ((inBlock d i S).sum (fun x => x + 1) + (outBlock d i S).sum id) % d := by
        rw [← Nat.add_mod]
    _ = ((inBlock d i S).sum id + (inBlock d i S).card + (outBlock d i S).sum id) % d := by
        rw [hsum_plus_one]
    _ = (S.sum id + (inBlock d i S).card) % d := by
        rw [hS_sum]; ring_nf

/-- blockOffsets cardinality is preserved under rotation -/
private lemma blockOffsets_rotateSetInBlock (d i : ℕ) (hd : 0 < d) (S : Finset ℕ) :
    (blockOffsets d i (rotateSetInBlock d i S)).card = (blockOffsets d i S).card := by
  rw [← inBlock_card_eq_blockOffsets_card, ← inBlock_card_eq_blockOffsets_card]
  unfold rotateSetInBlock inBlock
  have h1 : (S.image (rotateInBlock d i)).filter (fun x => i * d ≤ x ∧ x < (i + 1) * d) =
            (S.filter (fun x => i * d ≤ x ∧ x < (i + 1) * d)).image (rotateInBlock d i) := by
    ext y
    constructor
    · intro hy
      simp only [mem_filter, mem_image] at hy ⊢
      obtain ⟨⟨x, hxS, hxy⟩, hy_in⟩ := hy
      use x
      constructor
      · constructor
        · exact hxS
        · by_contra hx_not
          rw [rotateInBlock_outside d i x hx_not] at hxy
          rw [← hxy] at hy_in
          exact hx_not hy_in
      · exact hxy
    · intro hy
      simp only [mem_filter, mem_image] at hy ⊢
      obtain ⟨x, ⟨hxS, hx_in⟩, hxy⟩ := hy
      constructor
      · use x, hxS
      · rw [← hxy, rotateInBlock_inside d i x hx_in]
        constructor
        · exact Nat.le_add_right _ _
        · have hmod_lt : (x - i * d + 1) % d < d := Nat.mod_lt _ hd
          have h1 : i * d + (x - i * d + 1) % d < i * d + d := Nat.add_lt_add_left hmod_lt _
          linarith [Nat.mul_add_one i d]
  rw [h1]
  have hinj : Set.InjOn (rotateInBlock d i)
      (S.filter (fun x => i * d ≤ x ∧ x < (i + 1) * d) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
    exact rotateInBlock_injective d i hd hxy
  exact Finset.card_image_of_injOn hinj

/-- blockOffsets cardinality is preserved under k iterations of rotation -/
private lemma blockOffsets_rotateSetInBlockK (d i : ℕ) (hd : 0 < d) (S : Finset ℕ) (k : ℕ) :
    (blockOffsets d i (rotateSetInBlockK d i k S)).card = (blockOffsets d i S).card := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold rotateSetInBlockK at ih ⊢
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [blockOffsets_rotateSetInBlock d i hd, ih]

/-- Elements in a different block are unchanged by rotation -/
private lemma blockOffsets_rotateSetInBlock_other (d i j : ℕ) (hij : j ≠ i) (S : Finset ℕ) :
    blockOffsets d j (rotateSetInBlock d i S) = blockOffsets d j S := by
  unfold blockOffsets rotateSetInBlock
  ext off
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · intro ⟨hoff_lt, x, hxS, hxy⟩
    constructor
    · exact hoff_lt
    · have h_not_in_block_i : ¬(i * d ≤ j * d + off ∧ j * d + off < (i + 1) * d) := by
        intro ⟨h1, h2⟩
        have hj_eq : j = i := by
          have hoff_lt_d : off < d := hoff_lt
          have h5 : i ≤ j := by
            by_contra hcontra
            push Not at hcontra
            have : j + 1 ≤ i := hcontra
            have : (j + 1) * d ≤ i * d := Nat.mul_le_mul_right d this
            have : j * d + d ≤ i * d := by ring_nf at this ⊢; exact this
            have : j * d + off < j * d + d := Nat.add_lt_add_left hoff_lt_d _
            omega
          have h6 : j ≤ i := by
            by_contra hcontra
            push Not at hcontra
            have : i + 1 ≤ j := hcontra
            have : (i + 1) * d ≤ j * d := Nat.mul_le_mul_right d this
            omega
          omega
        exact hij hj_eq
      have hrotate_eq : rotateInBlock d i (j * d + off) = j * d + off :=
        rotateInBlock_outside d i (j * d + off) h_not_in_block_i
      by_cases hx_eq : x = j * d + off
      · rw [hx_eq] at hxS; exact hxS
      · exfalso
        by_cases hx_in_block : i * d ≤ x ∧ x < (i + 1) * d
        · simp only [rotateInBlock, ite_eq_left hx_in_block] at hxy
          have hmod_lt : (x - i * d + 1) % d < d := by
            cases d with
            | zero => simp at hx_in_block
            | succ d => exact Nat.mod_lt _ (Nat.succ_pos d)
          have h_eq : i * d + (x - i * d + 1) % d = j * d + off := hxy
          have hi_eq_j : i = j := by
            by_contra hne
            cases Nat.lt_or_gt_of_ne hne with
            | inl hi_lt_j =>
              have : (i + 1) * d ≤ j * d := Nat.mul_le_mul_right d hi_lt_j
              have hlt : i * d + (x - i * d + 1) % d < (i + 1) * d := by
                calc i * d + (x - i * d + 1) % d < i * d + d := Nat.add_lt_add_left hmod_lt _
                  _ = (i + 1) * d := by ring
              omega
            | inr hj_lt_i =>
              have : (j + 1) * d ≤ i * d := Nat.mul_le_mul_right d hj_lt_i
              have hlt : j * d + off < (j + 1) * d := by
                calc j * d + off < j * d + d := Nat.add_lt_add_left hoff_lt _
                  _ = (j + 1) * d := by ring
              omega
          exact hij hi_eq_j.symm
        · have : rotateInBlock d i x = x := rotateInBlock_outside d i x hx_in_block
          rw [this] at hxy
          exact hx_eq hxy
  · intro ⟨hoff_lt, hmem⟩
    constructor
    · exact hoff_lt
    · use j * d + off, hmem
      exact rotateInBlock_outside d i (j * d + off) (by
        intro ⟨h1, h2⟩
        have hj_eq : j = i := by
          have hoff_lt_d : off < d := hoff_lt
          have h5 : i ≤ j := by
            by_contra hcontra
            push Not at hcontra
            have : j + 1 ≤ i := hcontra
            have : (j + 1) * d ≤ i * d := Nat.mul_le_mul_right d this
            have : j * d + d ≤ i * d := by ring_nf at this ⊢; exact this
            have : j * d + off < j * d + d := Nat.add_lt_add_left hoff_lt_d _
            omega
          have h6 : j ≤ i := by
            by_contra hcontra
            push Not at hcontra
            have : i + 1 ≤ j := hcontra
            have : (i + 1) * d ≤ j * d := Nat.mul_le_mul_right d this
            omega
          omega
        exact hij hj_eq)

/-- Elements in a different block are unchanged by k iterations of rotation -/
private lemma blockOffsets_rotateSetInBlockK_other (d i j : ℕ) (hij : j ≠ i) (S : Finset ℕ) (k : ℕ) :
    blockOffsets d j (rotateSetInBlockK d i k S) = blockOffsets d j S := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold rotateSetInBlockK at ih ⊢
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [blockOffsets_rotateSetInBlock_other d i j hij, ih]

/-- Sum mod d after k iterations of rotation -/
private lemma rotateSetInBlockK_sum_mod (d i : ℕ) (hd : 0 < d) (S : Finset ℕ) (k : ℕ) :
    ((rotateSetInBlockK d i k S).sum id) % d = (S.sum id + k * (blockOffsets d i S).card) % d := by
  induction k with
  | zero =>
    unfold rotateSetInBlockK
    simp only [Function.iterate_zero, id_eq, zero_mul, add_zero]
  | succ k ih =>
    unfold rotateSetInBlockK at ih ⊢
    simp only [Function.iterate_succ', Function.comp_apply]
    set T := (rotateSetInBlock d i)^[k] S with hT
    have hmod : ((rotateSetInBlock d i T).sum id) % d =
                (T.sum id + (inBlock d i T).card) % d := by
      rw [rotateSetInBlock_sum_eq d i hd T]
      exact rotateSetInBlock_sum_mod d i hd T
    rw [inBlock_card_eq_blockOffsets_card] at hmod
    have hcard : (blockOffsets d i T).card = (blockOffsets d i S).card := by
      have : (blockOffsets d i ((rotateSetInBlock d i)^[k] S)).card = (blockOffsets d i S).card :=
        blockOffsets_rotateSetInBlockK d i hd S k
      simp only [hT] at this ⊢
      exact this
    rw [hcard] at hmod
    have hT_sum_mod : T.sum id % d = (S.sum id + k * (blockOffsets d i S).card) % d := ih
    calc ((rotateSetInBlock d i T).sum id) % d
      = (T.sum id + (blockOffsets d i S).card) % d := hmod
      _ = (T.sum id % d + (blockOffsets d i S).card % d) % d := by rw [Nat.add_mod]
      _ = ((S.sum id + k * (blockOffsets d i S).card) % d + (blockOffsets d i S).card % d) % d := by
          rw [hT_sum_mod]
      _ = (S.sum id + k * (blockOffsets d i S).card + (blockOffsets d i S).card) % d := by
          rw [← Nat.add_mod]
      _ = (S.sum id + (k + 1) * (blockOffsets d i S).card) % d := by ring_nf

/-- KEY COMBINATORIAL LEMMA: rotation changes sum by j (mod d).
Since ω^d = 1, this means ω^(sum(rotate^k(S))) = ω^(sum(S) + k*j).

The proof uses:
1. Each rotation changes the sum by j - d * (wraparounds) where j = |blockOffsets|
2. Since ω^d = 1, the -d * (wraparounds) term vanishes
3. So ω^(sum(rotate(S))) = ω^(sum(S) + j)
4. By induction, ω^(sum(rotate^k(S))) = ω^(sum(S) + k*j)

The key insight is that rotation preserves |blockOffsets|, so we can use induction. -/
lemma rotateSetInBlockK_sum_pow {K : Type*} [Field K] {ω : K} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0 < d) (i : ℕ) (S : Finset ℕ) (k : ℕ) :
    ω ^ ((rotateSetInBlockK d i k S).sum id) = ω ^ (S.sum id + k * (blockOffsets d i S).card) := by
  apply pow_eq_of_diff_mod hω
  exact rotateSetInBlockK_sum_mod d i hd S k

/-- Rotation stays within [n] when block i is complete (i.e., i < n/d) -/
private lemma rotateInBlock_lt (d n i x : ℕ) (hd : 0 < d) (hx : x < n) (hi : i < n / d) :
    rotateInBlock d i x < n := by
  simp only [rotateInBlock]
  split_ifs with hblock
  · -- x is in block i, so rotated x is also in block i
    have h1 : (x - i * d + 1) % d < d := Nat.mod_lt _ hd
    have h2 : (i + 1) * d ≤ n := by
      have : i + 1 ≤ n / d := hi
      calc (i + 1) * d ≤ (n / d) * d := Nat.mul_le_mul_right d this
        _ ≤ n := Nat.div_mul_le_self n d
    calc i * d + (x - i * d + 1) % d < i * d + d := by omega
      _ = (i + 1) * d := by ring
      _ ≤ n := h2
  · exact hx

/-- Rotation preserves subset of [n] -/
private lemma rotateSetInBlock_subset (d n i : ℕ) (hd : 0 < d) (hi : i < n / d) (S : Finset ℕ) 
    (hS : S ⊆ Finset.range n) :
    rotateSetInBlock d i S ⊆ Finset.range n := by
  intro y hy
  simp only [rotateSetInBlock, mem_image] at hy
  obtain ⟨x, hxS, hxy⟩ := hy
  have hx : x < n := mem_range.mp (hS hxS)
  rw [← hxy]
  exact mem_range.mpr (rotateInBlock_lt d n i x hd hx hi)

/-- Rotation k times preserves subset of [n] -/
lemma rotateSetInBlockK_subset (d n i : ℕ) (hd : 0 < d) (hi : i < n / d) (S : Finset ℕ) 
    (hS : S ⊆ Finset.range n) (k : ℕ) :
    rotateSetInBlockK d i k S ⊆ Finset.range n := by
  induction k with
  | zero => exact hS
  | succ k ih =>
    simp only [rotateSetInBlockK, Function.iterate_succ', Function.comp_apply]
    exact rotateSetInBlock_subset d n i hd hi _ ih

/-- Rotation preserves cardinality -/
private lemma rotateSetInBlock_card (d i : ℕ) (hd : 0 < d) (S : Finset ℕ) :
    (rotateSetInBlock d i S).card = S.card := by
  exact card_image_of_injective S (rotateInBlock_injective d i hd)

/-- Rotation k times preserves cardinality -/
lemma rotateSetInBlockK_card (d i : ℕ) (hd : 0 < d) (S : Finset ℕ) (k : ℕ) :
    (rotateSetInBlockK d i k S).card = S.card := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rotateSetInBlockK, Function.iterate_succ', Function.comp_apply]
    rw [rotateSetInBlock_card d i hd]
    simp only [rotateSetInBlockK] at ih
    exact ih

/-! #### Commutativity of rotations in different blocks

Rotations in different blocks commute because they act on disjoint sets of elements.
This is KEY for the correct approach to proving `nonBlocky_contributions_cancel`:
instead of using single-block orbits, we should use equivalence classes under ALL
rotations. Since rotations in different blocks commute, the equivalence class is
a product of single-block orbits. -/

/-- Rotations in different blocks commute at the element level.

**Proof idea:** If x is in block j, then rotateInBlock d j x stays in block j,
so rotateInBlock d i (rotateInBlock d j x) = rotateInBlock d j x (since i ≠ j).
Similarly for the other order. If x is in block i, the same logic applies.
If x is in neither block, both rotations act as identity. -/
private lemma rotateInBlock_comm (d i j : ℕ) (hd : 0 < d) (x : ℕ) (hij : i ≠ j) :
    rotateInBlock d i (rotateInBlock d j x) = rotateInBlock d j (rotateInBlock d i x) := by
  unfold rotateInBlock
  by_cases hi : i * d ≤ x ∧ x < (i + 1) * d
  · have hj_orig : ¬(j * d ≤ x ∧ x < (j + 1) * d) := by
      intro ⟨hle, hlt⟩
      rcases Nat.lt_trichotomy i j with hlt_ij | heq_ij | hgt_ij
      · have h1 : (i + 1) * d ≤ j * d := by nlinarith
        omega
      · exact hij heq_ij
      · have h1 : (j + 1) * d ≤ i * d := by nlinarith
        omega
    simp only [hi, and_self, ite_true, hj_orig, ite_false]
    have hi_result : i * d ≤ i * d + (x - i * d + 1) % d ∧ 
                     i * d + (x - i * d + 1) % d < (i + 1) * d := by
      constructor; · omega
      · have hmod : (x - i * d + 1) % d < d := Nat.mod_lt _ hd
        calc i * d + (x - i * d + 1) % d < i * d + d := by omega
          _ = (i + 1) * d := by ring
    have hj_result : ¬(j * d ≤ i * d + (x - i * d + 1) % d ∧ 
                       i * d + (x - i * d + 1) % d < (j + 1) * d) := by
      intro ⟨hle, hlt⟩
      have hmod : (x - i * d + 1) % d < d := Nat.mod_lt _ hd
      rcases Nat.lt_trichotomy i j with hlt_ij | heq_ij | hgt_ij
      · have h1 : (i + 1) * d ≤ j * d := by nlinarith
        have h2 : i * d + (x - i * d + 1) % d < (i + 1) * d := hi_result.2
        omega
      · exact hij heq_ij
      · have h1 : (j + 1) * d ≤ i * d := by nlinarith
        omega
    simp only [hj_result, ite_false]
  · simp only [hi, ite_false]
    by_cases hj : j * d ≤ x ∧ x < (j + 1) * d
    · simp only [hj, and_self, ite_true]
      have hj_result : j * d ≤ j * d + (x - j * d + 1) % d ∧ 
                       j * d + (x - j * d + 1) % d < (j + 1) * d := by
        constructor; · omega
        · have hmod : (x - j * d + 1) % d < d := Nat.mod_lt _ hd
          calc j * d + (x - j * d + 1) % d < j * d + d := by omega
            _ = (j + 1) * d := by ring
      have hi_result : ¬(i * d ≤ j * d + (x - j * d + 1) % d ∧ 
                         j * d + (x - j * d + 1) % d < (i + 1) * d) := by
        intro ⟨hle, hlt⟩
        have hmod : (x - j * d + 1) % d < d := Nat.mod_lt _ hd
        rcases Nat.lt_trichotomy i j with hlt_ij | heq_ij | hgt_ij
        · have h1 : (i + 1) * d ≤ j * d := by nlinarith
          omega
        · exact hij heq_ij
        · have h1 : (j + 1) * d ≤ i * d := by nlinarith
          have h2 : j * d + (x - j * d + 1) % d < (j + 1) * d := hj_result.2
          omega
      simp only [hi_result, ite_false]
    · simp only [hj, ite_false, hi]

/-- Rotations in different blocks commute at the set level. -/
private lemma rotateSetInBlock_comm (d i j : ℕ) (hd : 0 < d) (S : Finset ℕ) (hij : i ≠ j) :
    rotateSetInBlock d i (rotateSetInBlock d j S) = 
    rotateSetInBlock d j (rotateSetInBlock d i S) := by
  unfold rotateSetInBlock
  ext x
  simp only [mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨rotateInBlock d i z, ⟨z, hz, rfl⟩, ?_⟩
    exact (rotateInBlock_comm d i j hd z hij).symm
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨rotateInBlock d j z, ⟨z, hz, rfl⟩, ?_⟩
    exact rotateInBlock_comm d i j hd z hij

/-- Iterated rotations in different blocks commute at the set level.

This is the key commutativity lemma needed for the correct proof of
`nonBlocky_contributions_cancel`. It shows that the order of applying
rotations in different blocks doesn't matter. -/
private lemma rotateSetInBlockK_comm (d i j : ℕ) (hd : 0 < d) (S : Finset ℕ) (hij : i ≠ j) 
    (ki kj : ℕ) :
    rotateSetInBlockK d i ki (rotateSetInBlockK d j kj S) = 
    rotateSetInBlockK d j kj (rotateSetInBlockK d i ki S) := by
  unfold rotateSetInBlockK
  have hcomm : Function.Commute (rotateSetInBlock d i) (rotateSetInBlock d j) := by
    intro S
    exact rotateSetInBlock_comm d i j hd S hij
  exact hcomm.iterate_iterate ki kj S

/-! #### Multi-block equivalence classes (for correct proof approach)

The correct proof of `nonBlocky_contributions_cancel` uses equivalence classes under
ALL rotations (not just single-block orbits). Two sets S and T are equivalent if T
can be obtained from S by applying rotations in any combination of blocks.

**Key insight**: Since rotations in different blocks COMMUTE (proven above as
`rotateSetInBlockK_comm`), the equivalence class of S is:
  { rotateSetInBlockK d i₁ k₁ (... (rotateSetInBlockK d iₘ kₘ S)...) }
for all choices of k₁, ..., kₘ where i₁, ..., iₘ are the split blocks of S.

This equals the product of single-block orbits:
  ∏_{i : split block of S} {rotations in block i}

**Why this fixes the proof**:
1. The equivalence class is orbit-closed under rotation in ANY split block (by definition)
2. The sum over each equivalence class factors as:
   ∑_{k₁} ∑_{k₂} ... ∑_{kₘ} ω^(sum of rotated set)
   = (∑_{k₁} ω^(k₁ * j₁)) * ... * (∑_{kₘ} ω^(kₘ * jₘ)) * ω^(base)
3. Since S is non-blocky, at least one block i has 0 < jᵢ < d,
   so ∑_{k} ω^(k * jᵢ) = 0, making the whole product 0.

**Current status**: The commutativity lemmas are proven. The full multi-block
equivalence infrastructure is outlined below. The main theorem
`nonBlocky_contributions_cancel` is fully proven using single-block orbit arguments.
-/

/-- Apply a sequence of rotations in multiple blocks.
Given a list of (block_index, rotation_amount) pairs, apply them in order.
Since rotations commute, the order doesn't matter. -/
private def multiBlockRotate (d : ℕ) (rotations : List (ℕ × ℕ)) (S : Finset ℕ) : Finset ℕ :=
  rotations.foldl (fun acc ⟨i, k⟩ => rotateSetInBlockK d i k acc) S

/-- The multi-block orbit of S: all sets obtainable by rotating in split blocks.

**Note**: This is a simplified definition using only the smallest split block.
The full multi-block equivalence class would enumerate all combinations of
rotations across all split blocks. The simplified version is sufficient for
understanding the structure but not for the complete proof.

For a non-blocky set S with split blocks {i₁, ..., iₘ}, the full orbit is:
  { rotateSetInBlockK d i₁ k₁ (... (rotateSetInBlockK d iₘ kₘ S)...) : 
    k₁ ∈ range d, ..., kₘ ∈ range d }
    
The orbit size is d^m where m is the number of split blocks. -/
private noncomputable def multiBlockOrbit (d n : ℕ) (S : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  let splitBlocks := (Finset.range (n / d)).filter (fun i => isSplitBlock d n i S)
  -- For simplicity, we define this using the smallest split block orbit first
  -- A full implementation would enumerate all combinations
  exact if h : splitBlocks.Nonempty then
    let i₀ := splitBlocks.min' h
    (Finset.range d).image (fun k => rotateSetInBlockK d i₀ k S)
  else
    {S}

/-! #### Periodicity and orbit infrastructure for orbit cancellation -/

/-- Key periodicity lemma: rotating d times in block i returns to identity.
This is because each element in block i has offset (x - i*d) which cycles through
0, 1, ..., d-1 and back to 0 after d rotations. -/
lemma rotateInBlock_iterate_d (d i x : ℕ) (hd : 0 < d) :
    (rotateInBlock d i)^[d] x = x := by
  by_cases hblock : i * d ≤ x ∧ x < (i + 1) * d
  · -- x is in block i
    have h1 : (i + 1) * d = i * d + d := by ring
    have hoff : x - i * d < d := by omega
    -- Key: after k rotations, offset becomes (original_offset + k) % d
    have hiter : ∀ k, (rotateInBlock d i)^[k] x = i * d + (x - i * d + k) % d := by
      intro k
      induction k with
      | zero => 
        simp only [Function.iterate_zero, id_eq, add_zero]
        rw [Nat.mod_eq_of_lt hoff]
        omega
      | succ k ih =>
        simp only [Function.iterate_succ', Function.comp_apply, ih]
        simp only [rotateInBlock]
        have hmod_lt : (x - i * d + k) % d < d := Nat.mod_lt _ hd
        have hin_block : i * d ≤ i * d + (x - i * d + k) % d ∧ 
                         i * d + (x - i * d + k) % d < (i + 1) * d := by
          constructor
          · exact Nat.le_add_right _ _
          · calc i * d + (x - i * d + k) % d < i * d + d := by omega
              _ = (i + 1) * d := by ring
        simp only [ite_eq_left hin_block]
        congr 1
        have hsub : i * d + (x - i * d + k) % d - i * d = (x - i * d + k) % d := by omega
        rw [hsub]
        have hmod_eq : ((x - i * d + k) % d + 1) % d = (x - i * d + (k + 1)) % d := by
          have h2 : x - i * d + (k + 1) = x - i * d + k + 1 := by ring
          rw [h2]
          conv_rhs => rw [← Nat.mod_add_div (x - i * d + k) d]
          have h3 : (x - i * d + k) % d + d * ((x - i * d + k) / d) + 1 = 
                    (x - i * d + k) % d + 1 + d * ((x - i * d + k) / d) := by ring
          rw [h3, Nat.add_mul_mod_self_left]
        exact hmod_eq
    rw [hiter d]
    have : (x - i * d + d) % d = (x - i * d) % d := by
      rw [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
    rw [this, Nat.mod_eq_of_lt hoff]
    omega
  · -- x is outside block i, so rotation is identity
    have h : ∀ k, (rotateInBlock d i)^[k] x = x := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        simp only [Function.iterate_succ', Function.comp_apply, ih]
        simp only [rotateInBlock, ite_eq_right hblock]
    exact h d

/-- Rotating a set d times returns to identity -/
lemma rotateSetInBlockK_d (d i : ℕ) (hd : 0 < d) (S : Finset ℕ) :
    rotateSetInBlockK d i d S = S := by
  unfold rotateSetInBlockK
  have h : ∀ k, (rotateSetInBlock d i)^[k] S = S.image ((rotateInBlock d i)^[k]) := by
    intro k
    induction k with
    | zero => simp only [Function.iterate_zero, id_eq, Finset.image_id]
    | succ k ih =>
      simp only [Function.iterate_succ', Function.comp_apply, ih]
      unfold rotateSetInBlock
      rw [Finset.image_image]
  rw [h d]
  ext x
  simp only [Finset.mem_image]
  constructor
  · intro ⟨y, hy, hxy⟩
    rw [rotateInBlock_iterate_d d i y hd] at hxy
    rw [← hxy]; exact hy
  · intro hx
    use x, hx
    exact rotateInBlock_iterate_d d i x hd

/-- Composition of rotations: rotating a times then b times equals rotating (a+b) times -/
private lemma rotateSetInBlockK_add (d i a b : ℕ) (S : Finset ℕ) :
    rotateSetInBlockK d i a (rotateSetInBlockK d i b S) = rotateSetInBlockK d i (a + b) S := by
  simp only [rotateSetInBlockK, Function.iterate_add_apply]

/-- Rotating by a multiple of d returns to identity -/
private lemma rotateSetInBlockK_mul_d (d i k : ℕ) (hd : 0 < d) (S : Finset ℕ) :
    rotateSetInBlockK d i (k * d) S = S := by
  induction k with
  | zero => simp [rotateSetInBlockK]
  | succ k ih =>
    rw [Nat.succ_mul, ← rotateSetInBlockK_add, rotateSetInBlockK_d d i hd, ih]

/-- Rotation is periodic with period d -/
private lemma rotateSetInBlockK_mod_d (d i k : ℕ) (hd : 0 < d) (S : Finset ℕ) :
    rotateSetInBlockK d i k S = rotateSetInBlockK d i (k % d) S := by
  conv_lhs => rw [← Nat.div_add_mod k d]
  rw [add_comm, ← rotateSetInBlockK_add]
  congr 1
  rw [mul_comm]
  exact rotateSetInBlockK_mul_d d i _ hd S

/-- Rotating within the defining block stays in the orbit.
This is straightforward from periodicity and is a key helper for multi-block orbit closure. -/
private lemma multiBlockOrbit_closed_same_block (d : ℕ) (hd : 0 < d) (S : Finset ℕ) 
    (i₀ : ℕ) (k iter : ℕ) :
    rotateSetInBlockK d i₀ iter (rotateSetInBlockK d i₀ k S) ∈ 
    (Finset.range d).image (fun k => rotateSetInBlockK d i₀ k S) := by
  simp only [Finset.mem_image, Finset.mem_range]
  use (iter + k) % d
  constructor
  · exact Nat.mod_lt _ hd
  · have h1 : rotateSetInBlockK d i₀ iter (rotateSetInBlockK d i₀ k S) = 
              rotateSetInBlockK d i₀ (iter + k) S := rotateSetInBlockK_add d i₀ iter k S
    rw [h1]
    have hdiv := Nat.div_add_mod (iter + k) d
    have h2 : iter + k = d * ((iter + k) / d) + (iter + k) % d := by omega
    conv_rhs => rw [h2, add_comm]
    rw [← rotateSetInBlockK_add]
    induction (iter + k) / d with
    | zero => simp [rotateSetInBlockK]
    | succ q ih => 
      have h3 : d * (q + 1) = d + d * q := by ring
      rw [h3, ← rotateSetInBlockK_add, ih, rotateSetInBlockK_d d i₀ hd]

/-- Orbit injectivity: For k1, k2 < m = d/gcd(d,j) where j = |blockOffsets d i S|,
if rotateSetInBlockK d i k1 S = rotateSetInBlockK d i k2 S, then k1 = k2.

This follows from the fact that the sums differ: 
sum(rotate^k(S)) ≡ sum(S) + k*j (mod d), and k*j takes distinct values mod d
for k in range(m) since m = d/gcd(d,j). -/
lemma rotateSetInBlockK_injective (d i : ℕ) (hd : 0 < d) (S : Finset ℕ) 
    (_hj_pos : 0 < (blockOffsets d i S).card) (_hj_lt : (blockOffsets d i S).card < d) :
    let j := (blockOffsets d i S).card
    let m := d / Nat.gcd d j
    ∀ k1 k2, k1 < m → k2 < m → 
      rotateSetInBlockK d i k1 S = rotateSetInBlockK d i k2 S → k1 = k2 := by
  intro j m k1 k2 hk1 hk2 heq
  by_contra hne
  wlog hlt : k1 < k2 generalizing k1 k2 with hsymm
  · cases Nat.lt_or_gt_of_ne hne with
    | inl h => exact hlt h
    | inr h => exact hsymm k2 k1 hk2 hk1 heq.symm (Ne.symm hne) h
  -- k1 < k2, so k2 - k1 > 0 and k2 - k1 < m
  have hdiff_pos : 0 < k2 - k1 := Nat.sub_pos_of_lt hlt
  have hdiff_lt : k2 - k1 < m := by omega
  -- From heq, their sums are equal
  have hsum_eq : (rotateSetInBlockK d i k1 S).sum id = 
                 (rotateSetInBlockK d i k2 S).sum id := by rw [heq]
  have hmod1 := rotateSetInBlockK_sum_mod d i hd S k1
  have hmod2 := rotateSetInBlockK_sum_mod d i hd S k2
  -- (S.sum id + k1 * j) % d = (S.sum id + k2 * j) % d
  have hmod_eq : (S.sum id + k1 * j) % d = (S.sum id + k2 * j) % d := by
    calc (S.sum id + k1 * j) % d = (rotateSetInBlockK d i k1 S).sum id % d := hmod1.symm
      _ = (rotateSetInBlockK d i k2 S).sum id % d := by rw [hsum_eq]
      _ = (S.sum id + k2 * j) % d := hmod2
  -- The key number-theoretic step: from k1*j ≡ k2*j (mod d) and 0 < k2-k1 < m = d/gcd(d,j),
  -- we derive a contradiction using modular arithmetic cancellation.
  -- hmod_eq gives us S.sum id + k1 * j ≡ S.sum id + k2 * j [MOD d]
  have h_modeq : S.sum id + k1 * j ≡ S.sum id + k2 * j [MOD d] := hmod_eq
  -- Cancel S.sum id from both sides
  have h_modeq' : k1 * j ≡ k2 * j [MOD d] := Nat.ModEq.add_left_cancel' (S.sum id) h_modeq
  -- Cancel j to get k1 ≡ k2 [MOD d / gcd d j]
  have h_cancel := Nat.ModEq.cancel_right_div_gcd hd h_modeq'
  -- This means m = (d / gcd d j) divides (k2 - k1)
  have hdvd : m ∣ (k2 - k1) := by
    rw [Nat.modEq_iff_dvd' (le_of_lt hlt)] at h_cancel
    exact h_cancel
  -- But 0 < k2 - k1 < m and m | (k2 - k1) is impossible
  have := Nat.eq_zero_of_dvd_of_lt hdvd hdiff_lt
  omega

/-- Helper lemma for modular arithmetic: (d - iter % d + iter) % d = 0 -/
private lemma mod_sub_add_mod (d iter : ℕ) (hd : 0 < d) : 
    (d - iter % d + iter) % d = 0 := by
  have h1 : iter % d < d := Nat.mod_lt iter hd
  have h2 : iter % d ≤ iter := Nat.mod_le iter d
  have h3 : iter % d ≤ d := le_of_lt h1
  have key : d - iter % d + iter = d + iter - iter % d := by omega
  rw [key]
  have key2 : d + iter - iter % d = d + (iter - iter % d) := Nat.add_sub_assoc h2 d
  rw [key2]
  rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
  have h4 : iter - iter % d = d * (iter / d) := by
    have := Nat.div_add_mod iter d
    omega
  rw [h4]
  simp

/-- Helper: rotating d*q times is identity -/
private lemma rotateSetInBlockK_mul_period (d i q : ℕ) (hd : 0 < d) (S : Finset ℕ) : 
    rotateSetInBlockK d i (d * q) S = S := by
  induction q with
  | zero => simp [rotateSetInBlockK]
  | succ q ih => 
    have h : d * (q + 1) = d + d * q := by ring
    rw [h, ← rotateSetInBlockK_add, ih, rotateSetInBlockK_d d i hd]

/-- The rotation orbit has uniform fiber cardinality.

For any set S and block i, the function k ↦ rotateSetInBlockK d i k S has period p | d
(where p is the smallest positive integer with rotate^p(S) = S).
Thus each element of the image appears d/p times in the sum over range d.

This lemma provides the uniform multiplicity needed for sum_image_eq_zero_of_uniform_multiplicity_primitiveRoot.
The proof uses the orbit-stabilizer principle: the stabilizer of S under rotation is a subgroup of ℤ/dℤ,
so its size divides d, and all orbit elements have the same stabilizer size. -/
lemma rotateSetInBlockK_fiber_card_uniform (d i : ℕ) (hd : 0 < d) (S : Finset ℕ) :
    ∃ c : ℕ, c ∣ d ∧ ∀ T ∈ (Finset.range d).image (fun k => rotateSetInBlockK d i k S),
        ((Finset.range d).filter (fun k => rotateSetInBlockK d i k S = T)).card = c := by
  -- Key insight: use the stabilizer (fiber of S itself) and show all fibers have the same size
  -- via a bijection k ↦ (k + d - j) % d from fiber(rotate^j(S)) to stabilizer
  let stab := (Finset.range d).filter (fun k => rotateSetInBlockK d i k S = S)
  use stab.card
  have hfiber_eq : ∀ T ∈ (Finset.range d).image (fun k => rotateSetInBlockK d i k S),
      ((Finset.range d).filter (fun k => rotateSetInBlockK d i k S = T)).card = stab.card := by
    intro T hT
    obtain ⟨j, hj_range, hj_eq⟩ := Finset.mem_image.mp hT
    have hj : j < d := Finset.mem_range.mp hj_range
    conv_lhs => rw [← hj_eq]
    apply Finset.card_bij (fun k _ => (k + d - j) % d)
    · -- hi: maps fiber to stab
      intro k hk
      have hk_mem := Finset.mem_filter.mp hk
      have hk_lt : k < d := Finset.mem_range.mp hk_mem.1
      have h1 : rotateSetInBlockK d i (d - j) (rotateSetInBlockK d i k S) = 
                rotateSetInBlockK d i (d - j) (rotateSetInBlockK d i j S) := by rw [hk_mem.2]
      rw [rotateSetInBlockK_add, rotateSetInBlockK_add] at h1
      have h2 : d - j + j = d := by omega
      rw [h2, rotateSetInBlockK_d d i hd] at h1
      have h3 : d - j + k = k + (d - j) := by omega
      rw [h3] at h1
      have h4 : k + (d - j) = k + d - j := by omega
      rw [h4] at h1
      rw [rotateSetInBlockK_mod_d d i (k + d - j) hd] at h1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hd), h1⟩
    · -- i_inj: injective
      intro k1 hk1 k2 hk2 heq
      have h1 : k1 < d := Finset.mem_range.mp (Finset.mem_filter.mp hk1).1
      have h2 : k2 < d := Finset.mem_range.mp (Finset.mem_filter.mp hk2).1
      have h3 : k1 + d - j = k1 + (d - j) := by omega
      have h4 : k2 + d - j = k2 + (d - j) := by omega
      rw [h3, h4] at heq
      by_cases hcase1 : k1 + (d - j) < d <;> by_cases hcase2 : k2 + (d - j) < d
      · simp only [Nat.mod_eq_of_lt hcase1, Nat.mod_eq_of_lt hcase2] at heq; omega
      · push Not at hcase2
        simp only [Nat.mod_eq_of_lt hcase1] at heq
        have h5 : (k2 + (d - j)) % d = k2 - j := by
          have : k2 + (d - j) = d + (k2 - j) := by omega
          rw [this, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by omega : k2 - j < d)
        rw [h5] at heq; omega
      · push Not at hcase1
        simp only [Nat.mod_eq_of_lt hcase2] at heq
        have h5 : (k1 + (d - j)) % d = k1 - j := by
          have : k1 + (d - j) = d + (k1 - j) := by omega
          rw [this, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by omega : k1 - j < d)
        rw [h5] at heq; omega
      · push Not at hcase1 hcase2
        have h5 : (k1 + (d - j)) % d = k1 - j := by
          have : k1 + (d - j) = d + (k1 - j) := by omega
          rw [this, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by omega : k1 - j < d)
        have h6 : (k2 + (d - j)) % d = k2 - j := by
          have : k2 + (d - j) = d + (k2 - j) := by omega
          rw [this, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
          exact Nat.mod_eq_of_lt (by omega : k2 - j < d)
        rw [h5, h6] at heq; omega
    · -- i_surj: surjective
      intro m hm
      have hm_mem := Finset.mem_filter.mp hm
      use (m + j) % d
      have hm_lt : m < d := Finset.mem_range.mp hm_mem.1
      have hmj_lt : (m + j) % d < d := Nat.mod_lt _ hd
      have key : ((m + j) % d + d - j) % d = m := by
        by_cases hcase : m + j < d
        · simp only [Nat.mod_eq_of_lt hcase]
          have h1 : m + j + d - j = m + d := by omega
          rw [h1, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
          exact Nat.mod_eq_of_lt hm_lt
        · push Not at hcase
          have h1 : (m + j) % d = m + j - d := by
            rw [Nat.mod_eq_sub_mod hcase, Nat.mod_eq_of_lt (by omega)]
          rw [h1]
          have h2 : m + j - d + d - j = m := by omega
          rw [h2]
          exact Nat.mod_eq_of_lt hm_lt
      refine ⟨?_, key⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr hmj_lt
      · have h1 : rotateSetInBlockK d i j (rotateSetInBlockK d i m S) = 
                  rotateSetInBlockK d i j S := by rw [hm_mem.2]
        rw [rotateSetInBlockK_add] at h1
        have h2 : j + m = m + j := by ring
        conv_lhs at h1 => rw [h2]
        rw [rotateSetInBlockK_mod_d d i (m + j) hd] at h1
        exact h1
  constructor
  · -- stab.card | d: follows from d = |orbit| * stab.card
    have h1 : (Finset.range d).card = ∑ T ∈ (Finset.range d).image (fun k => rotateSetInBlockK d i k S), 
        ((Finset.range d).filter (fun k => rotateSetInBlockK d i k S = T)).card := by
      exact Finset.card_eq_sum_card_image (fun k => rotateSetInBlockK d i k S) (Finset.range d)
    rw [Finset.card_range] at h1
    have h3 : ∑ T ∈ (Finset.range d).image (fun k => rotateSetInBlockK d i k S), 
        ((Finset.range d).filter (fun k => rotateSetInBlockK d i k S = T)).card = 
        ((Finset.range d).image (fun k => rotateSetInBlockK d i k S)).card * stab.card := by
      rw [Finset.sum_congr rfl hfiber_eq]
      simp only [Finset.sum_const, smul_eq_mul]
    rw [h3] at h1
    exact Dvd.intro ((Finset.range d).image (fun k => rotateSetInBlockK d i k S)).card (by linarith)
  · exact hfiber_eq

/-- CORRECTED VERSION: If rotate^iter(S) = rotate^k(S₀), then S is in the full orbit of S₀.

The original lemma (rotateSetInBlockK_eq_implies_same_orbit) was FALSE because it claimed
∃ j < m₀ where m₀ = d / gcd(d, |offsets|). The actual orbit has period d, not m₀.

This corrected version concludes ∃ j < d, which is always true when the hypothesis holds.

**Proof idea:** Apply rotate^(d - iter % d) to both sides of heq:
- LHS becomes S (since d - iter % d + iter ≡ 0 mod d)
- RHS becomes rotate^((d - iter % d + k) % d)(S₀)
So S = rotate^j(S₀) where j = (d - iter % d + k) % d < d. -/
private lemma rotateSetInBlockK_eq_implies_same_orbit_full (d i : ℕ) (hd : 0 < d) 
    (S S₀ : Finset ℕ) (iter k : ℕ)
    (heq : rotateSetInBlockK d i iter S = rotateSetInBlockK d i k S₀) :
    ∃ j < d, rotateSetInBlockK d i j S₀ = S := by
  let j := (d - iter % d + k) % d
  use j
  constructor
  · exact Nat.mod_lt _ hd
  · -- Show rotate^j(S₀) = S
    -- Apply rotate^(d - iter % d) to both sides of heq
    have h1 : rotateSetInBlockK d i (d - iter % d) (rotateSetInBlockK d i iter S) = 
              rotateSetInBlockK d i (d - iter % d) (rotateSetInBlockK d i k S₀) := by
      rw [heq]
    -- Simplify LHS using periodicity
    have hlhs : rotateSetInBlockK d i (d - iter % d) (rotateSetInBlockK d i iter S) = S := by
      rw [rotateSetInBlockK_add]
      -- (d - iter % d + iter) = d * q for some q (since (d - iter % d + iter) % d = 0)
      have hzero := mod_sub_add_mod d iter hd
      have hdiv : d - iter % d + iter = d * ((d - iter % d + iter) / d) := by
        have := Nat.div_add_mod (d - iter % d + iter) d
        omega
      rw [hdiv]
      exact rotateSetInBlockK_mul_period d i _ hd _
    -- Simplify RHS using periodicity
    have hrhs : rotateSetInBlockK d i (d - iter % d) (rotateSetInBlockK d i k S₀) = 
                rotateSetInBlockK d i j S₀ := by
      rw [rotateSetInBlockK_add]
      -- (d - iter % d + k) = q * d + j
      have hdiv := Nat.div_add_mod (d - iter % d + k) d
      conv_lhs => rw [← hdiv]
      rw [add_comm, ← rotateSetInBlockK_add]
      rw [rotateSetInBlockK_mul_period d i _ hd]
    rw [hlhs, hrhs] at h1
    exact h1.symm

/-! #### Smallest split block infrastructure

These lemmas establish that rotation preserves the smallest split block,
which is key to proving that orbits (defined using smallest split block) partition NonBlocky.
-/

/-- Decidability for isSplitBlock -/
instance isSplitBlock_decidable (d n i : ℕ) (S : Finset ℕ) : Decidable (isSplitBlock d n i S) := by
  unfold isSplitBlock; infer_instance

/-- The set of split block indices for a subset S -/
private def splitBlockIndices (d n : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (n / d)).filter (fun i => isSplitBlock d n i S)

/-- Rotation preserves whether a block is split -/
private lemma isSplitBlock_rotateSetInBlockK (d n i j : ℕ) (hd : 0 < d) (S : Finset ℕ) (k : ℕ) :
    isSplitBlock d n j (rotateSetInBlockK d i k S) ↔ isSplitBlock d n j S := by
  unfold isSplitBlock
  by_cases hij : j = i
  · subst hij
    rw [blockOffsets_rotateSetInBlockK d j hd S k]
  · rw [blockOffsets_rotateSetInBlockK_other d i j hij S k]

/-- The set of split blocks is the same after rotation -/
private lemma splitBlockIndices_rotateSetInBlockK (d n i : ℕ) (hd : 0 < d) (S : Finset ℕ) (k : ℕ) :
    splitBlockIndices d n (rotateSetInBlockK d i k S) = splitBlockIndices d n S := by
  ext j
  simp only [splitBlockIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro ⟨hj, hsplit⟩
    exact ⟨hj, (isSplitBlock_rotateSetInBlockK d n i j hd S k).mp hsplit⟩
  · intro ⟨hj, hsplit⟩
    exact ⟨hj, (isSplitBlock_rotateSetInBlockK d n i j hd S k).mpr hsplit⟩

/-- For non-blocky S, the set of split block indices is nonempty -/
private lemma splitBlockIndices_nonempty_of_nonBlocky {d n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range n) (hNB : ¬IsDBlocky d n S) :
    (splitBlockIndices d n S).Nonempty := by
  obtain ⟨i, hi, hsplit⟩ := nonBlocky_has_split_block hS hNB
  use i
  simp only [splitBlockIndices, Finset.mem_filter, Finset.mem_range]
  exact ⟨hi, hsplit⟩

/-- The smallest split block index (as a natural number) -/
private noncomputable def smallestSplitBlockIdx (d n : ℕ) (S : Finset ℕ) 
    (hne : (splitBlockIndices d n S).Nonempty) : ℕ :=
  (splitBlockIndices d n S).min' hne

private lemma smallestSplitBlockIdx_mem {d n : ℕ} {S : Finset ℕ}
    (hne : (splitBlockIndices d n S).Nonempty) :
    smallestSplitBlockIdx d n S hne ∈ splitBlockIndices d n S :=
  Finset.min'_mem _ hne

private lemma smallestSplitBlockIdx_lt {d n : ℕ} {S : Finset ℕ}
    (hne : (splitBlockIndices d n S).Nonempty) :
    smallestSplitBlockIdx d n S hne < n / d := by
  have h := smallestSplitBlockIdx_mem hne
  simp only [splitBlockIndices, Finset.mem_filter, Finset.mem_range] at h
  exact h.1

private lemma smallestSplitBlockIdx_isSplit {d n : ℕ} {S : Finset ℕ}
    (hne : (splitBlockIndices d n S).Nonempty) :
    isSplitBlock d n (smallestSplitBlockIdx d n S hne) S := by
  have h := smallestSplitBlockIdx_mem hne
  simp only [splitBlockIndices, Finset.mem_filter, Finset.mem_range] at h
  exact h.2

private lemma smallestSplitBlockIdx_le {d n : ℕ} {S : Finset ℕ}
    (hne : (splitBlockIndices d n S).Nonempty) (i : ℕ) 
    (hi : i ∈ splitBlockIndices d n S) :
    smallestSplitBlockIdx d n S hne ≤ i :=
  Finset.min'_le _ i hi

/-- KEY LEMMA: The smallest split block is preserved by rotation.
This is the crucial property that ensures orbits (defined using smallest split block)
partition NonBlocky, making the orbit-based cancellation argument work. -/
private lemma smallestSplitBlockIdx_rotateSetInBlockK {d n i : ℕ} (hd : 0 < d) {S : Finset ℕ} 
    (hne : (splitBlockIndices d n S).Nonempty) (k : ℕ) :
    let hne' := by rw [splitBlockIndices_rotateSetInBlockK d n i hd S k]; exact hne
    smallestSplitBlockIdx d n (rotateSetInBlockK d i k S) hne' = 
    smallestSplitBlockIdx d n S hne := by
  intro hne'
  unfold smallestSplitBlockIdx
  congr 1
  exact splitBlockIndices_rotateSetInBlockK d n i hd S k

/-- Helper: removing a nonempty subset strictly decreases cardinality -/
private lemma card_sdiff_lt_card_of_nonempty {α : Type*} [DecidableEq α] 
    {s t : Finset α} (hne : s.Nonempty) (hst : s ⊆ t) :
    (t \ s).card < t.card := by
  have h1 : (t \ s).card + s.card = t.card := by
    calc (t \ s).card + s.card = (t \ s ∪ s).card := by
           rw [card_union_of_disjoint disjoint_sdiff_self_left]
      _ = t.card := by rw [sdiff_union_of_subset hst]
  obtain ⟨x, hx⟩ := hne
  have hs_pos : 0 < s.card := card_pos.mpr ⟨x, hx⟩
  omega

/-- Helper: f(k + m) = f(k) implies f(m*q + k) = f(k) -/
private lemma period_shift_sum {K : Type*} [AddCommMonoid K] {m : ℕ} (q : ℕ)
    (f : ℕ → K) (hperiod : ∀ k, f (k + m) = f k) (k : ℕ) :
    f (m * q + k) = f k := by
  induction q with
  | zero => simp
  | succ q' ih => 
    have : m * (q' + 1) + k = m * q' + k + m := by ring
    rw [this, hperiod, ih]

/-- Helper: sum over range (m * q) where f has period m -/
private lemma sum_range_mul_period {K : Type*} [AddCommMonoid K] {m : ℕ} (q : ℕ)
    (f : ℕ → K) (hperiod : ∀ k, f (k + m) = f k) 
    (hsum : ∑ k ∈ Finset.range m, f k = 0) :
    ∑ k ∈ Finset.range (m * q), f k = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add]
    simp only [ih, zero_add]
    have h : ∀ k ∈ Finset.range m, f (m * q + k) = f k := fun k _ => period_shift_sum q f hperiod k
    rw [Finset.sum_congr rfl h, hsum]

/-- Helper: sum over range d equals 0 when sum over range m₀ equals 0 and m₀ | d -/
private lemma sum_range_period_zero {K : Type*} [AddCommMonoid K] {d m₀ : ℕ}
    (hdiv : m₀ ∣ d)
    (f : ℕ → K) (hperiod : ∀ k, f (k + m₀) = f k)
    (hsum_m₀ : ∑ k ∈ Finset.range m₀, f k = 0) :
    ∑ k ∈ Finset.range d, f k = 0 := by
  have hd_eq : d = m₀ * (d / m₀) := (Nat.mul_div_cancel' hdiv).symm
  rw [hd_eq]
  exact sum_range_mul_period (d / m₀) f hperiod hsum_m₀

/-- Helper: For any orbit-closed subset of NonBlocky, the weighted sum is 0.
This is the key lemma that allows the induction to work correctly.
It's proved by strong induction on the cardinality of the subset.

The orbit-closure hypothesis ensures that when we pick an element S₀ ∈ A and 
compute its orbit O under rotation in the smallest split block, we have O ⊆ A. 
This avoids the problematic case where A is a proper subset of an orbit.

**Key insight (2025-01 fix):** The orbit-closure only needs to hold for the 
SMALLEST split block of each element. This is because:
1. All elements of an orbit O (under block i₀) have the same smallest split block i₀
2. If S ∉ O has smallest split block i_S ≠ i₀, rotating S in block i_S gives T
   with smallest split block i_S ≠ i₀, so T ∉ O
3. If S ∉ O has smallest split block i₀, then S differs from S₀ outside block i₀,
   which is impossible if O uses the full orbit (range d) -/
lemma sum_nonBlocky_subset_eq_zero {K : Type*} [Field K] {ω : K} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 1 < d) (n k : ℕ) (_hnd : d ≤ n)
    -- The full set of non-blocky k-subsets
    (NonBlocky : Finset (Finset ℕ))
    (hNB_def : NonBlocky = (kSubsets n k).filter (fun S => ¬IsDBlocky d n S))
    -- Helper lemmas about rotation
    (hrot_mem : ∀ S ∈ NonBlocky, ∀ i < n / d, ∀ iter : ℕ, 
        rotateSetInBlockK d i iter S ∈ kSubsets n k)
    (hrot_nonblocky : ∀ S ∈ NonBlocky, ∀ rotBlock < n / d, ∀ iter : ℕ,
        ¬IsDBlocky d n (rotateSetInBlockK d rotBlock iter S))
    (_horbit_sum_zero : ∀ S ∈ NonBlocky, ∀ i < n / d, 
        isSplitBlock d n i S →
        let j := (blockOffsets d i S).card
        let m := d / Nat.gcd d j
        ∑ k ∈ Finset.range m, ω ^ ((rotateSetInBlockK d i k S).sum id) = 0)
    -- The subset we're summing over
    (A : Finset (Finset ℕ))
    (hA_sub : A ⊆ NonBlocky)
    -- Orbit-closure: A is closed under rotation in the SMALLEST split block
    -- (This is weaker than closure under any split block, but sufficient for the proof)
    -- Key change: We only require closure under the smallest split block of each element,
    -- not under any split block. This makes the induction work because:
    -- 1. All elements of an orbit O (under block i₀) have the same smallest split block i₀
    -- 2. If S ∉ O has smallest split block i_S ≠ i₀, rotating S in block i_S keeps it in A \ O
    (hOrbitClosed : ∀ S ∈ A, 
        (hne_S : (splitBlockIndices d n S).Nonempty) →
        let i_S := smallestSplitBlockIdx d n S hne_S
        ∀ iter, rotateSetInBlockK d i_S iter S ∈ A) :
    ∑ S ∈ A, ω ^ (S.sum id) = 0 := by
  classical
  have hd_pos : 0 < d := by omega
  -- Strong induction on |A|
  induction h : A.card using Nat.strong_induction_on generalizing A with
  | _ card_val ih =>
    by_cases hA_empty : A = ∅
    · rw [hA_empty, sum_empty]
    · -- A is nonempty, pick an element S₀
      have hA_nonempty : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA_empty
      obtain ⟨S₀, hS₀⟩ := hA_nonempty
      have hS₀_NB : S₀ ∈ NonBlocky := hA_sub hS₀
      -- S₀ is non-blocky, so it has a split block
      have hS₀_nb : ¬IsDBlocky d n S₀ := by
        rw [hNB_def] at hS₀_NB
        simp only [mem_filter] at hS₀_NB
        exact hS₀_NB.2
      have hS₀_sub : S₀ ⊆ Finset.range n := by
        rw [hNB_def] at hS₀_NB
        simp only [mem_filter, kSubsets, mem_powersetCard] at hS₀_NB
        exact hS₀_NB.1.1
      -- Use smallestSplitBlockIdx for canonical orbit definition
      -- This ensures orbits partition NonBlocky, making the induction work
      have hne₀ : (splitBlockIndices d n S₀).Nonempty :=
        splitBlockIndices_nonempty_of_nonBlocky hS₀_sub hS₀_nb
      let i₀ := smallestSplitBlockIdx d n S₀ hne₀
      have hi₀ : i₀ < n / d := smallestSplitBlockIdx_lt hne₀
      have hsplit₀ : isSplitBlock d n i₀ S₀ := smallestSplitBlockIdx_isSplit hne₀
      -- Define orbit parameters
      let j₀ := (blockOffsets d i₀ S₀).card
      have hj₀_pos : 0 < j₀ := hsplit₀.2.1
      have hj₀_lt : j₀ < d := hsplit₀.2.2
      -- Define the orbit of S₀ using range d (the full orbit)
      -- NOTE: Changed from range m₀ to range d to fix the orbit definition.
      -- The orbit has d distinct elements (rotation has period d).
      let O := (Finset.range d).image (fun k => rotateSetInBlockK d i₀ k S₀)
      -- Show O ⊆ NonBlocky
      have hO_sub_NB : O ⊆ NonBlocky := by
        intro T hT
        simp only [O, Finset.mem_image, Finset.mem_range] at hT
        obtain ⟨iter, _, rfl⟩ := hT
        rw [hNB_def, mem_filter]
        constructor
        · exact hrot_mem S₀ hS₀_NB i₀ hi₀ iter
        · exact hrot_nonblocky S₀ hS₀_NB i₀ hi₀ iter
      -- Show S₀ ∈ O
      have hS₀_in_O : S₀ ∈ O := by
        simp only [O, Finset.mem_image, Finset.mem_range]
        refine ⟨0, hd_pos, ?_⟩
        simp only [rotateSetInBlockK, Function.iterate_zero, id_eq]
      -- Show O.Nonempty
      have hO_ne : O.Nonempty := ⟨S₀, hS₀_in_O⟩
      -- Orbit sum is 0
      -- We use sum_image_eq_zero_of_uniform_multiplicity_primitiveRoot with:
      -- 1. The sum over range d is 0 (by orbit_sum_full_eq_zero)
      -- 2. Each element of the image appears uniformly (by rotateSetInBlockK_fiber_card_uniform)
      have hO_sum : ∑ T ∈ O, ω ^ (T.sum id) = 0 := by
        simp only [O]
        -- Step 1: The sum over range d of ω^(sum(rotate^k(S₀))) is 0
        have hsum_range_zero : ∑ k ∈ Finset.range d, ω ^ ((rotateSetInBlockK d i₀ k S₀).sum id) = 0 := by
          -- Rewrite using rotateSetInBlockK_sum_pow
          have hrewrite : ∀ k ∈ Finset.range d,
              ω ^ ((rotateSetInBlockK d i₀ k S₀).sum id) = ω ^ (S₀.sum id + k * j₀) := by
            intro k _
            exact rotateSetInBlockK_sum_pow hω hd_pos i₀ S₀ k
          rw [Finset.sum_congr rfl hrewrite]
          exact orbit_sum_full_eq_zero hω hd (S₀.sum id) j₀ hj₀_pos hj₀_lt
        -- Step 2: Apply sum_image_eq_zero_of_uniform_multiplicity_primitiveRoot
        apply sum_image_eq_zero_of_uniform_multiplicity_primitiveRoot hω hd_pos
        · exact hsum_range_zero
        · exact rotateSetInBlockK_fiber_card_uniform d i₀ hd_pos S₀
      -- Intersect O with A to get the part of the orbit in A
      let O_A := O ∩ A
      have hO_A_sub_A : O_A ⊆ A := inter_subset_right
      have hO_A_sub_O : O_A ⊆ O := inter_subset_left
      have hS₀_in_O_A : S₀ ∈ O_A := mem_inter.mpr ⟨hS₀_in_O, hS₀⟩
      have hO_A_ne : O_A.Nonempty := ⟨S₀, hS₀_in_O_A⟩
      -- The key insight: if O ⊆ A, then we can use the orbit sum directly
      -- Otherwise, we need the orbit disjointness property
      by_cases hO_sub_A : O ⊆ A
      · -- O ⊆ A: can use orbit sum directly
        have hdisj : Disjoint O (A \ O) := disjoint_sdiff_self_right
        calc ∑ S ∈ A, ω ^ (S.sum id) 
            = ∑ S ∈ O ∪ (A \ O), ω ^ (S.sum id) := by
                congr 1
                exact (union_sdiff_of_subset hO_sub_A).symm
          _ = ∑ S ∈ O, ω ^ (S.sum id) + ∑ S ∈ A \ O, ω ^ (S.sum id) :=
                sum_union hdisj
          _ = 0 + ∑ S ∈ A \ O, ω ^ (S.sum id) := by rw [hO_sum]
          _ = ∑ S ∈ A \ O, ω ^ (S.sum id) := zero_add _
          _ = 0 := by
              have hcard_lt : (A \ O).card < card_val := by
                rw [← h]
                exact card_sdiff_lt_card_of_nonempty hO_ne hO_sub_A
              have hA_O_sub : A \ O ⊆ NonBlocky := fun x hx => hA_sub (mem_sdiff.mp hx).1
              -- Prove orbit-closure for A \ O under SMALLEST split block
              -- Key insight: Since O is defined using smallestSplitBlockIdx of S₀,
              -- and smallestSplitBlockIdx is preserved by rotation, orbits partition NonBlocky.
              -- If S ∉ O has smallest split block i_S, then:
              -- - If i_S ≠ i₀: rotating S in block i_S gives T with smallest split block i_S ≠ i₀,
              --   so T ∉ O (elements of O have smallest split block i₀)
              -- - If i_S = i₀: S would be in the same orbit as S₀ (contradiction)
              have hA_O_closed : ∀ S ∈ A \ O, 
                  (hne_S : (splitBlockIndices d n S).Nonempty) →
                  let i_S := smallestSplitBlockIdx d n S hne_S
                  ∀ iter, rotateSetInBlockK d i_S iter S ∈ A \ O := by
                intro S hS hne_S i_S iter
                have hS_in_A : S ∈ A := (mem_sdiff.mp hS).1
                have hS_not_O : S ∉ O := (mem_sdiff.mp hS).2
                have hS_NB : S ∈ NonBlocky := hA_sub hS_in_A
                rw [mem_sdiff]
                constructor
                · -- rotateSetInBlockK d i_S iter S ∈ A
                  -- This follows from hOrbitClosed since i_S is the smallest split block of S
                  exact hOrbitClosed S hS_in_A hne_S iter
                · -- rotateSetInBlockK d i_S iter S ∉ O
                  -- Key: smallest split block is preserved by rotation
                  -- Let T = rotateSetInBlockK d i_S iter S
                  -- Then smallestSplitBlockIdx of T = smallestSplitBlockIdx of S = i_S
                  -- If i_S ≠ i₀, then T has different smallest split block than elements of O
                  -- If i_S = i₀, then we use rotateSetInBlockK_eq_implies_same_orbit_full
                  intro hT_in_O
                  simp only [O, Finset.mem_image, Finset.mem_range] at hT_in_O
                  obtain ⟨k, hk_lt, hT_eq⟩ := hT_in_O
                  -- hT_eq : rotateSetInBlockK d i₀ k S₀ = rotateSetInBlockK d i_S iter S
                  -- 
                  -- Key observation: all elements of O have smallest split block i₀
                  -- (since rotation in block i₀ preserves smallest split block)
                  -- 
                  -- If i_S ≠ i₀:
                  -- - S has smallest split block i_S
                  -- - T = rotate(S) in block i_S also has smallest split block i_S
                  -- - But rotateSetInBlockK d i₀ k S₀ has smallest split block i₀
                  -- - So T ≠ rotateSetInBlockK d i₀ k S₀ (contradiction)
                  -- 
                  -- If i_S = i₀:
                  -- - Use rotateSetInBlockK_eq_implies_same_orbit_full to show S ∈ O
                  -- - This contradicts hS_not_O
                  by_cases hi_eq : i_S = i₀
                  · -- Case i_S = i₀: S and S₀ have the same smallest split block
                    apply hS_not_O
                    simp only [O, Finset.mem_image, Finset.mem_range]
                    -- Use rotateSetInBlockK_eq_implies_same_orbit_full
                    -- We need to show S ∈ orbit of S₀ under block i₀
                    -- hT_eq : rotateSetInBlockK d i₀ k S₀ = rotateSetInBlockK d i_S iter S
                    -- Since i_S = i₀, this becomes:
                    -- rotateSetInBlockK d i₀ k S₀ = rotateSetInBlockK d i₀ iter S
                    rw [hi_eq] at hT_eq
                    exact rotateSetInBlockK_eq_implies_same_orbit_full d i₀ hd_pos S S₀
                      iter k hT_eq.symm
                  · -- Case i_S ≠ i₀: S has different smallest split block than S₀
                    -- T = rotate(S) in block i_S has smallest split block i_S
                    -- But hT_eq says T = rotate(S₀) in block i₀, which has smallest split block i₀
                    -- This is a contradiction since i_S ≠ i₀
                    -- 
                    -- Key: smallestSplitBlockIdx is preserved by rotation, and depends only on the SET,
                    -- not on how it was constructed. So if T = rotateSetInBlockK d i₀ k S₀,
                    -- then smallestSplitBlockIdx of T = smallestSplitBlockIdx of S₀ = i₀
                    -- But T = rotateSetInBlockK d i_S iter S, so 
                    -- smallestSplitBlockIdx of T = smallestSplitBlockIdx of S = i_S
                    -- Since i_S ≠ i₀, we have a contradiction.
                    -- 
                    -- The technical challenge is handling the dependent Nonempty proof.
                    -- We use a helper that extracts the index without the proof dependency.
                    have hS_smallest : smallestSplitBlockIdx d n S hne_S = i_S := rfl
                    -- Show that the smallest split block of S equals that of S₀ via the rotation equality
                    -- smallestSplitBlockIdx(rotate^iter_S(S)) = smallestSplitBlockIdx(S) = i_S
                    -- smallestSplitBlockIdx(rotate^k_i₀(S₀)) = smallestSplitBlockIdx(S₀) = i₀
                    -- But these two rotations are equal (by hT_eq), so i_S = i₀
                    have h1 : smallestSplitBlockIdx d n S hne_S = i_S := rfl
                    have h2 : smallestSplitBlockIdx d n S₀ hne₀ = i₀ := rfl
                    -- By smallestSplitBlockIdx_rotateSetInBlockK:
                    -- smallestSplitBlockIdx(rotate^iter_S(S)) = smallestSplitBlockIdx(S) = i_S
                    -- smallestSplitBlockIdx(rotate^k_i₀(S₀)) = smallestSplitBlockIdx(S₀) = i₀
                    -- Since rotate^iter_S(S) = rotate^k_i₀(S₀) (by hT_eq), we have i_S = i₀
                    -- This is a contradiction with hi_eq
                    -- 
                    -- To formalize, we use the fact that splitBlockIndices only depends on the set
                    have hsplit_eq : splitBlockIndices d n (rotateSetInBlockK d i_S iter S) = 
                                     splitBlockIndices d n (rotateSetInBlockK d i₀ k S₀) := by
                      rw [hT_eq]
                    -- Both sides equal splitBlockIndices of the original sets (by the rotation lemma)
                    have hsplit_S : splitBlockIndices d n (rotateSetInBlockK d i_S iter S) = 
                                    splitBlockIndices d n S := 
                      splitBlockIndices_rotateSetInBlockK d n i_S hd_pos S iter
                    have hsplit_S₀ : splitBlockIndices d n (rotateSetInBlockK d i₀ k S₀) = 
                                     splitBlockIndices d n S₀ := 
                      splitBlockIndices_rotateSetInBlockK d n i₀ hd_pos S₀ k
                    -- So splitBlockIndices d n S = splitBlockIndices d n S₀
                    have hsplit_same : splitBlockIndices d n S = splitBlockIndices d n S₀ := by
                      rw [← hsplit_S, hsplit_eq, hsplit_S₀]
                    -- Therefore their mins are equal
                    have hmin_eq : (splitBlockIndices d n S).min' hne_S = 
                                   (splitBlockIndices d n S₀).min' hne₀ := by
                      simp only [hsplit_same]
                    -- But this means i_S = i₀
                    have hidx_eq : i_S = i₀ := hmin_eq
                    exact hi_eq hidx_eq
              exact ih (A \ O).card hcard_lt (A \ O) hA_O_sub hA_O_closed rfl
      · -- O ⊄ A: This case is impossible with hOrbitClosed
        -- Since S₀ ∈ A and i₀ is the smallest split block of S₀, by hOrbitClosed,
        -- the entire orbit O is contained in A.
        exfalso
        apply hO_sub_A
        intro T hT
        simp only [O, Finset.mem_image, Finset.mem_range] at hT
        obtain ⟨iter, _, rfl⟩ := hT
        exact hOrbitClosed S₀ hS₀ hne₀ iter


/-- Key lemma: For non-blocky subsets, contributions cancel in d-cycles.
This is the heart of the q-Lucas theorem proof.

More precisely: partition non-blocky k-element subsets into equivalence classes
where two sets are equivalent if they differ only by cyclic shifts within blocks.
Each equivalence class has size m where 1 < m and m | d, and the sum of ω^(sum S)
over each class is 0 because the sums form an arithmetic progression with common
difference d/m, and ω^(d/m) is a primitive m-th root of unity. -/
theorem nonBlocky_contributions_cancel {K : Type*} [Field K] {ω : K} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 1 < d) (n k : ℕ) :
    ∑ S ∈ (kSubsets n k).filter (fun S => ¬IsDBlocky d n S),
      ω ^ (S.sum id) = 0 := by
  classical
  -- Case 1: If n < d, all subsets are d-blocky (no complete blocks to check)
  by_cases hnd : n < d
  · have hdiv : n / d = 0 := Nat.div_eq_of_lt hnd
    have hall_blocky : ∀ S ∈ kSubsets n k, IsDBlocky d n S := by
      intro S hS
      constructor
      · simp only [kSubsets, mem_powersetCard] at hS; exact hS.1
      · intro i hi; rw [hdiv] at hi; exact absurd hi (Nat.not_lt_zero i)
    have hempty : (kSubsets n k).filter (fun S => ¬IsDBlocky d n S) = ∅ := by
      ext S; constructor
      · intro hS; simp only [mem_filter] at hS; exact absurd (hall_blocky S hS.1) hS.2
      · intro hS; simp at hS
    rw [hempty, sum_empty]
  push Not at hnd
  -- Case 2: n ≥ d - the main case using d-cycle cancellation
  --
  -- Proof outline:
  -- For each non-blocky set S, there exists a "split block" i where S contains
  -- some but not all elements of {i*d, i*d+1, ..., i*d+d-1}.
  --
  -- We partition non-blocky sets into orbits under rotation within the smallest split block.
  -- Key insight: if S ∩ block_i has offsets J ⊆ {0,...,d-1} with 0 < |J| < d,
  -- then the orbit of S under rotation within block i has size m where m | d and 1 < m.
  -- (m is the period of J under cyclic rotation, which divides d and is > 1 since J ≠ ∅, {0,...,d-1})
  --
  -- Within each orbit:
  -- - The sums form an arithmetic progression with common difference |J| (mod d)
  -- - Let m = d / gcd(d, |J|). Then ω^|J| is an m-th root of unity with m > 1
  -- - By orbit_sum_eq_zero, ∑_{k=0}^{m-1} ω^(base + k*|J|) = 0
  -- - Therefore ∑_{orbit} ω^(sum S) = 0
  --
  -- Since non-blocky sets partition into such orbits, the total sum is 0.
  --
  -- The proof proceeds by defining:
  -- 1. blockOffsets d i S = {j < d : i*d + j ∈ S} - the offsets in block i
  -- 2. A rotation operation that cyclically shifts elements within a block
  -- 3. A canonical representative for each orbit (e.g., min offset = 0)
  --
  -- Key lemmas needed:
  -- (a) For non-blocky S with smallest split block i, let J = blockOffsets d i S.
  --     Then 0 < |J| < d.
  -- (b) Rotating S by 1 in block i changes sum(S) by |J| (mod d).
  -- (c) The orbit has size m = d / gcd(d, |J|) > 1.
  -- (d) ∑_{k=0}^{m-1} ω^(base + k*|J|) = 0 by orbit_sum_eq_zero (PROVED ABOVE).
  --
  -- The algebraic core (d) is proved by orbit_sum_eq_zero. The combinatorial infrastructure
  -- (a)-(c) follows from standard orbit-counting arguments for cyclic group actions.
  --
  -- Detailed proof:
  -- Let NonBlocky = (kSubsets n k).filter (¬IsDBlocky d n ·)
  -- For S ∈ NonBlocky, let i(S) = smallest split block index
  -- Let J(S) = blockOffsets d i(S) S, and j(S) = |J(S)|
  -- Note: 0 < j(S) < d since block i(S) is split
  --
  -- Define rotate : NonBlocky → NonBlocky by rotating in block i(S) by 1
  -- This is well-defined: rotating preserves cardinality and non-blocky property
  --
  -- The orbit of S under rotate has size m(S) = d / gcd(d, j(S))
  -- Since 0 < j(S) < d, we have gcd(d, j(S)) < d, so m(S) > 1
  --
  -- Within each orbit {S, rotate(S), ..., rotate^(m-1)(S)}:
  -- sum(rotate^k(S)) ≡ sum(S) + k * j(S) (mod d)
  -- So ∑_{orbit} ω^sum = ω^(sum S) * ∑_{k=0}^{m-1} ω^(k * j(S))
  --                    = ω^(sum S) * ∑_{k=0}^{m-1} (ω^j(S))^k = 0
  -- (by orbit_sum_eq_zero, since 0 < j(S) < d)
  -- Partitioning NonBlocky into orbits and summing gives 0.
  --
  -- Implementation note: The full formalization requires additional lemmas about rotation:
  -- 1. rotateSetInBlockK_injective: rotation is injective on the orbit
  -- 2. rotateSetInBlockK_preserves_subset: rotation preserves subset of [n]  
  -- 3. rotateSetInBlockK_preserves_card: rotation preserves cardinality
  -- 4. rotateSetInBlockK_preserves_nonBlocky: rotation preserves non-blocky property
  --
  -- The algebraic core (orbit_sum_eq_zero) is proved above. The combinatorial infrastructure
  -- for orbit partitioning requires these additional lemmas.
  --
  -- Proof sketch:
  -- 1. Partition non-blocky sets into orbits under rotation in the smallest split block
  -- 2. Each orbit has size m = d / gcd(d, j) > 1 where j = |blockOffsets|
  -- 3. The sum over each orbit is 0 by orbit_sum_eq_zero
  -- 4. Therefore the total sum is 0
  --
  -- We use a canonical representative approach:
  -- Define canonRep(S) = the element of S's orbit with minimum sum
  -- Then sum over non-blocky = sum over (canonReps × orbits)
  -- Each orbit sum is 0, so total is 0.
  --
  -- For this proof, we need helper lemmas about rotation preserving properties.
  
  -- Define the non-blocky set
  let NonBlocky := (kSubsets n k).filter (fun S => ¬IsDBlocky d n S)
  
  -- If NonBlocky is empty, we're done
  by_cases hNB_empty : NonBlocky = ∅
  · simp only [NonBlocky] at hNB_empty
    rw [hNB_empty, sum_empty]
  
  -- Otherwise, we need to show the sum is 0 using orbit cancellation
  -- The key is that each non-blocky set has a split block, and rotation within
  -- that block creates orbits whose sums cancel.
  
  -- For each S ∈ NonBlocky, let i = smallest split block index
  -- Let j = |blockOffsets d i S|, where 0 < j < d (since block is split)
  -- The orbit of S under rotation in block i is {rotate^k(S) : k ∈ range m}
  -- where m = d / gcd(d, j)
  
  -- Helper: rotation preserves membership in kSubsets
  have hrot_mem : ∀ S ∈ NonBlocky, ∀ i < n / d, ∀ iter : ℕ, 
      rotateSetInBlockK d i iter S ∈ kSubsets n k := by
    intro S hS i hi iter
    -- Rotation preserves subset of [n] and cardinality
    simp only [NonBlocky, mem_filter] at hS
    simp only [kSubsets, mem_powersetCard] at hS ⊢
    have hd_pos : 0 < d := by omega
    constructor
    · -- Subset property: rotation preserves subset of [n]
      exact rotateSetInBlockK_subset d n i hd_pos hi S hS.1.1 iter
    · -- Cardinality property: rotation preserves card
      rw [rotateSetInBlockK_card d i hd_pos S iter]
      exact hS.1.2
  
  -- Helper: rotation preserves non-blocky property
  have hrot_nonblocky : ∀ S ∈ NonBlocky, ∀ rotBlock < n / d, ∀ iter : ℕ,
      ¬IsDBlocky d n (rotateSetInBlockK d rotBlock iter S) := by
    intro S hS rotBlock hrotBlock iter
    simp only [NonBlocky, mem_filter] at hS
    -- S is non-blocky, so it has a split block
    have hS_sub : S ⊆ Finset.range n := by
      simp only [kSubsets, mem_powersetCard] at hS
      exact hS.1.1
    have hS_nb : ¬IsDBlocky d n S := hS.2
    -- Get the split block from S
    obtain ⟨splitBlock, hsplitBlock, hsplit⟩ := nonBlocky_has_split_block hS_sub hS_nb
    -- Key insight: rotation preserves the existence of a split block
    intro hcontra
    unfold IsDBlocky at hcontra
    have hrot_sub := rotateSetInBlockK_subset d n rotBlock (by omega : 0 < d) hrotBlock S hS_sub iter
    obtain ⟨_, hblocks⟩ := hcontra
    -- Block splitBlock was split in S, show it's still split after rotation
    have hj_split_after : isSplitBlock d n splitBlock (rotateSetInBlockK d rotBlock iter S) := by
      unfold isSplitBlock at hsplit ⊢
      constructor
      · exact hsplit.1
      constructor
      · -- 0 < |blockOffsets d splitBlock (rotate S)|
        by_cases hij : splitBlock = rotBlock
        · -- splitBlock = rotBlock: use blockOffsets_rotateSetInBlockK
          rw [hij, blockOffsets_rotateSetInBlockK d rotBlock (by omega : 0 < d) S iter]
          rw [hij] at hsplit
          exact hsplit.2.1
        · -- splitBlock ≠ rotBlock: rotation doesn't change block splitBlock
          rw [blockOffsets_rotateSetInBlockK_other d rotBlock splitBlock (fun h => hij h) S iter]
          exact hsplit.2.1
      · -- |blockOffsets d splitBlock (rotate S)| < d
        by_cases hij : splitBlock = rotBlock
        · rw [hij, blockOffsets_rotateSetInBlockK d rotBlock (by omega : 0 < d) S iter]
          rw [hij] at hsplit
          exact hsplit.2.2
        · rw [blockOffsets_rotateSetInBlockK_other d rotBlock splitBlock (fun h => hij h) S iter]
          exact hsplit.2.2
    -- Now derive contradiction: block splitBlock is split, but hblocks says all blocks are not split
    unfold isSplitBlock at hj_split_after
    specialize hblocks splitBlock hj_split_after.1
    rcases hblocks with hall | hnone
    · -- All elements of block splitBlock are in rotate(S)
      have h1 : (blockOffsets d splitBlock (rotateSetInBlockK d rotBlock iter S)).card = d := by
        simp only [blockOffsets]
        have : (Finset.range d).filter (fun off => splitBlock * d + off ∈ rotateSetInBlockK d rotBlock iter S) = 
               Finset.range d := by
          ext off
          simp only [mem_filter, mem_range]
          constructor
          · intro ⟨h, _⟩; exact h
          · intro h; exact ⟨h, hall off h⟩
        rw [this, card_range]
      omega
    · -- No elements of block splitBlock are in rotate(S)
      have h1 : (blockOffsets d splitBlock (rotateSetInBlockK d rotBlock iter S)).card = 0 := by
        simp only [blockOffsets]
        have hempty : (Finset.range d).filter (fun off => splitBlock * d + off ∈ rotateSetInBlockK d rotBlock iter S) = ∅ := by
          ext off
          simp only [mem_filter, mem_range]
          constructor
          · intro ⟨hoff_lt, h⟩; exact absurd h (hnone off hoff_lt)
          · intro h; simp at h
        rw [hempty, card_empty]
      omega
  
  -- Helper: for S ∈ NonBlocky with split block i and j = |blockOffsets d i S|,
  -- the orbit sum is 0
  have horbit_sum_zero : ∀ S ∈ NonBlocky, ∀ i < n / d, 
      isSplitBlock d n i S →
      let j := (blockOffsets d i S).card
      let m := d / Nat.gcd d j
      ∑ k ∈ Finset.range m, ω ^ ((rotateSetInBlockK d i k S).sum id) = 0 := by
    intro S hS i hi hsplit
    simp only
    -- Use rotateSetInBlockK_sum_pow to rewrite each term
    have hd_pos : 0 < d := by omega
    have hj_pos : 0 < (blockOffsets d i S).card := hsplit.2.1
    have hj_lt : (blockOffsets d i S).card < d := hsplit.2.2
    -- Each term ω^(sum(rotate^k(S))) = ω^(sum(S) + k * j)
    have hrewrite : ∀ k ∈ Finset.range (d / Nat.gcd d (blockOffsets d i S).card),
        ω ^ ((rotateSetInBlockK d i k S).sum id) = 
        ω ^ (S.sum id + k * (blockOffsets d i S).card) := by
      intro k _
      exact rotateSetInBlockK_sum_pow hω hd_pos i S k
    rw [Finset.sum_congr rfl hrewrite]
    -- Now apply orbit_sum_eq_zero
    exact orbit_sum_eq_zero hω hd (S.sum id) (blockOffsets d i S).card hj_pos hj_lt
  
  -- The main argument: apply sum_nonBlocky_subset_eq_zero directly to NonBlocky.
  -- The key insight is that NonBlocky itself is orbit-closed under rotation in any split block.
  -- This avoids the problematic case of proving orbit-closure for NonBlocky \ O.
  
  -- Prove orbit-closure for NonBlocky: rotation in SMALLEST split block preserves membership
  have hNB_closed : ∀ S ∈ NonBlocky, 
      (hne_S : (splitBlockIndices d n S).Nonempty) →
      let i_S := smallestSplitBlockIdx d n S hne_S
      ∀ iter, rotateSetInBlockK d i_S iter S ∈ NonBlocky := by
    intro S hS hne_S i_S iter
    simp only [NonBlocky, mem_filter]
    have hi_S : i_S < n / d := smallestSplitBlockIdx_lt hne_S
    constructor
    · exact hrot_mem S hS i_S hi_S iter
    · exact hrot_nonblocky S hS i_S hi_S iter
  
  -- Apply the helper lemma directly to NonBlocky
  exact sum_nonBlocky_subset_eq_zero hω hd n k hnd NonBlocky rfl 
    hrot_mem hrot_nonblocky horbit_sum_zero NonBlocky (fun x hx => hx) hNB_closed
/-- Helper: (i * d + j) / d = i when j < d -/
private lemma mul_div_add_mod' (i j d : ℕ) (hd : 0 < d) (hj : j < d) : (i * d + j) / d = i := by
  have h : i * d + j = d * i + j := by ring
  rw [h, Nat.mul_add_div hd, Nat.div_eq_of_lt hj, add_zero]

/-- Helper: x / d < n / d when x < (n / d) * d -/
private lemma div_lt_of_lt_mul' (x n d : ℕ) (h : x < (n / d) * d) : x / d < n / d := by
  have h1 : x / d * d ≤ x := Nat.div_mul_le_self x d
  have h2 : x / d * d < (n / d) * d := Nat.lt_of_le_of_lt h1 h
  exact Nat.lt_of_mul_lt_mul_right h2

/-- Helper: x = (x / d) * d + x % d -/
private lemma div_mod_eq' (x d : ℕ) (_hd : 0 < d) : x = (x / d) * d + x % d :=
  (Nat.div_add_mod' x d).symm

/-- Helper: (a * d + b) % d = b when b < d -/
private lemma mul_add_mod_left' (a b d : ℕ) (hb : b < d) : (a * d + b) % d = b := by
  rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

/-! #### Bijection between blocky subsets and component pairs -/

/-- The backward map: (block indices, partial elements) → blocky subset -/
private def componentsToSubset (d n : ℕ) (B P : Finset ℕ) : Finset ℕ :=
  let completeBlocks := B.biUnion (fun i => (Finset.range d).image (fun j => i * d + j))
  let partialElems := P.image (fun p => (n / d) * d + p)
  completeBlocks ∪ partialElems

/-- The forward map: blocky subset → (block indices, partial elements) -/
private def subsetToComponents (d n : ℕ) (S : Finset ℕ) : Finset ℕ × Finset ℕ :=
  let blockIndices := (Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S)
  let partialElems := (Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S)
  (blockIndices, partialElems)

/-- The subset produced by componentsToSubset is contained in [n] -/
private lemma componentsToSubset_subset (d n : ℕ) (_hd : 0 < d)
    (B : Finset ℕ) (hB : B ⊆ Finset.range (n / d))
    (P : Finset ℕ) (hP : P ⊆ Finset.range (n % d)) :
    componentsToSubset d n B P ⊆ Finset.range n := by
  intro x hx
  simp only [componentsToSubset, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
             Finset.mem_range] at hx ⊢
  rcases hx with ⟨i, hi, j, hj, rfl⟩ | ⟨p, hp, rfl⟩
  · have hi' : i < n / d := Finset.mem_range.mp (hB hi)
    calc i * d + j < i * d + d := Nat.add_lt_add_left hj _
      _ = (i + 1) * d := by ring
      _ ≤ (n / d) * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hi')
      _ ≤ n := Nat.div_mul_le_self n d
  · have hp' : p < n % d := Finset.mem_range.mp (hP hp)
    have h := Nat.div_add_mod n d
    linarith

/-- The cardinality of componentsToSubset -/
private lemma componentsToSubset_card (d n : ℕ) (hd : 0 < d)
    (B : Finset ℕ) (hB : B ⊆ Finset.range (n / d))
    (P : Finset ℕ) (hP : P ⊆ Finset.range (n % d)) :
    (componentsToSubset d n B P).card = B.card * d + P.card := by
  simp only [componentsToSubset]
  have hdisj : Disjoint
      (B.biUnion (fun i => (Finset.range d).image (fun j => i * d + j)))
      (P.image (fun p => (n / d) * d + p)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at ha hb
    obtain ⟨i, hi, j, hj, rfl⟩ := ha
    obtain ⟨p, hp, rfl⟩ := hb
    have hi' : i < n / d := Finset.mem_range.mp (hB hi)
    have hp' : p < n % d := Finset.mem_range.mp (hP hp)
    intro heq
    have h1 : i * d + j < (n / d) * d := by
      have : (i + 1) * d ≤ (n / d) * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hi')
      calc i * d + j < i * d + d := Nat.add_lt_add_left hj _
        _ = (i + 1) * d := by ring
        _ ≤ (n / d) * d := this
    linarith
  rw [Finset.card_union_of_disjoint hdisj]
  congr 1
  · rw [Finset.card_biUnion]
    · conv_lhs =>
        arg 2
        ext i
        rw [Finset.card_image_of_injective _ (fun a b hab => by omega : Function.Injective _)]
        rw [Finset.card_range]
      simp only [Finset.sum_const, smul_eq_mul]
    · intro i hi j hj hne
      simp only [Function.onFun, Finset.disjoint_iff_ne]
      intro a ha b hb
      simp only [Finset.mem_image, Finset.mem_range] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      intro heq
      have h1 : (i * d + a') / d = i := mul_div_add_mod' i a' d hd ha'
      have h2 : (j * d + b') / d = j := mul_div_add_mod' j b' d hd hb'
      have : i = j := by
        calc i = (i * d + a') / d := h1.symm
          _ = (j * d + b') / d := by rw [heq]
          _ = j := h2
      exact hne this
  · rw [Finset.card_image_of_injective]
    intro a b hab
    have : (n / d) * d + a = (n / d) * d + b := hab
    omega

/-- The subset produced by componentsToSubset is blocky -/
private lemma componentsToSubset_isBlocky (d n : ℕ) (hd : 0 < d)
    (B : Finset ℕ) (_hB : B ⊆ Finset.range (n / d))
    (P : Finset ℕ) (hP : P ⊆ Finset.range (n % d)) :
    ∀ i < n / d, (∀ j < d, i * d + j ∈ componentsToSubset d n B P) ∨
                 (∀ j < d, i * d + j ∉ componentsToSubset d n B P) := by
  intro i hi
  by_cases hiB : i ∈ B
  · left
    intro j hj
    simp only [componentsToSubset, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
               Finset.mem_range]
    left
    exact ⟨i, hiB, j, hj, rfl⟩
  · right
    intro j hj
    simp only [componentsToSubset, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
               Finset.mem_range]
    push Not
    constructor
    · intro i' hi' j' hj' heq
      have h1 : i' = i := by
        have h := congrArg (· / d) heq
        rw [mul_div_add_mod' i' j' d hd hj', mul_div_add_mod' i j d hd hj] at h
        exact h
      rw [h1] at hi'
      exact hiB hi'
    · intro p hp heq
      have hp' : p < n % d := Finset.mem_range.mp (hP hp)
      have h1 : i * d + j < (i + 1) * d := by
        have : (i + 1) * d = i * d + d := by ring
        rw [this]
        exact Nat.add_lt_add_left hj (i * d)
      have h2 : (i + 1) * d ≤ (n / d) * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hi)
      have h3 : i * d + j < (n / d) * d := Nat.lt_of_lt_of_le h1 h2
      have h4 : (n / d) * d ≤ (n / d) * d + p := Nat.le_add_right _ _
      have h5 : i * d + j < (n / d) * d + p := Nat.lt_of_lt_of_le h3 h4
      exact (Nat.ne_of_lt h5).symm heq

/-- When k % d > n % d, there are no blocky k-element subsets of [n] -/
private lemma blockySubsets_empty_of_gt (d n k : ℕ) (hd : 0 < d) (h : n % d < k % d) :
    blockySubsets d n k = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro S hS
  simp only [blockySubsets, kSubsets, Finset.mem_filter, Finset.mem_powersetCard] at hS
  obtain ⟨⟨hSsub, hScard⟩, _, hSblocky⟩ := hS
  -- The partial block region has at most n % d elements
  have hpartial_card : (S.filter (fun x => (n / d) * d ≤ x)).card ≤ n % d := by
    have hsub : S.filter (fun x => (n / d) * d ≤ x) ⊆ Finset.Ico ((n / d) * d) n := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      simp only [Finset.mem_Ico]
      exact ⟨hx.2, Finset.mem_range.mp (hSsub hx.1)⟩
    calc (S.filter (fun x => (n / d) * d ≤ x)).card
        ≤ (Finset.Ico ((n / d) * d) n).card := Finset.card_le_card hsub
      _ = n - (n / d) * d := Nat.card_Ico _ _
      _ = n % d := by have h := Nat.div_add_mod' n d; omega
  -- The complete block region has cardinality divisible by d (blocky condition)
  have hcomplete_div : d ∣ (S.filter (fun x => x < (n / d) * d)).card := by
    have key : (S.filter (fun x => x < (n / d) * d)).card =
               d * ((Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S)).card := by
      have heq : S.filter (fun x => x < (n / d) * d) =
                 ((Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S)).biUnion
                   (fun i => (Finset.range d).image (fun j => i * d + j)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨hxS, hxlt⟩
          have hi : x / d < n / d := div_lt_of_lt_mul' x n d hxlt
          use x / d
          constructor
          · constructor
            · exact hi
            · have hblocky_i := hSblocky (x / d) hi
              rcases hblocky_i with hall | hnone
              · exact hall
              · have hxmod : x % d < d := Nat.mod_lt x hd
                have := hnone (x % d) hxmod
                have hx_eq : x = (x / d) * d + x % d := div_mod_eq' x d hd
                rw [← hx_eq] at this
                exact absurd hxS this
          · use x % d
            refine ⟨Nat.mod_lt x hd, (div_mod_eq' x d hd).symm⟩
        · intro ⟨i, ⟨hi, hall⟩, j, hj, heq⟩
          rw [← heq]
          constructor
          · exact hall j hj
          · have : i + 1 ≤ n / d := hi
            calc i * d + j < i * d + d := Nat.add_lt_add_left hj _
              _ = (i + 1) * d := by ring
              _ ≤ (n / d) * d := Nat.mul_le_mul_right d this
      rw [heq, Finset.card_biUnion]
      · have hinj : ∀ i ∈ (Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S),
            ((Finset.range d).image (fun j => i * d + j)).card = d := by
          intro i _
          rw [Finset.card_image_of_injective]
          · exact Finset.card_range d
          · intro a b hab; simp only at hab; omega
        rw [Finset.sum_congr rfl hinj, Finset.sum_const, smul_eq_mul]; ring
      · intro i₁ hi₁ i₂ hi₂ hne
        simp only [Function.onFun, Finset.disjoint_iff_ne]
        intro a ha b hb
        simp only [Finset.mem_image, Finset.mem_range] at ha hb
        obtain ⟨j₁, hj₁, rfl⟩ := ha
        obtain ⟨j₂, hj₂, rfl⟩ := hb
        intro heq
        have h1 : i₁ = (i₁ * d + j₁) / d := (mul_div_add_mod' i₁ j₁ d hd hj₁).symm
        have h2 : i₂ = (i₂ * d + j₂) / d := (mul_div_add_mod' i₂ j₂ d hd hj₂).symm
        rw [h1, heq, ← h2] at hne; exact hne rfl
    rw [key]; exact Nat.dvd_mul_right d _
  -- S splits into complete and partial parts
  have hS_split : S.card = (S.filter (fun x => x < (n / d) * d)).card +
                          (S.filter (fun x => (n / d) * d ≤ x)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext x; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hx; by_cases hxlt : x < (n / d) * d
        · left; exact ⟨hx, hxlt⟩
        · right; exact ⟨hx, Nat.not_lt.mp hxlt⟩
      · intro hcase; rcases hcase with ⟨hx, _⟩ | ⟨hx, _⟩ <;> exact hx
    · rw [Finset.disjoint_iff_ne]; intro a ha b hb
      simp only [Finset.mem_filter] at ha hb; omega
  rw [hScard] at hS_split
  have hmod : k % d = (S.filter (fun x => (n / d) * d ≤ x)).card % d := by
    obtain ⟨m, hm⟩ := hcomplete_div
    rw [hS_split, hm]; simp [Nat.add_mod]
  have hle' : (S.filter (fun x => (n / d) * d ≤ x)).card % d ≤
             (S.filter (fun x => (n / d) * d ≤ x)).card := Nat.mod_le _ _
  omega

/-- Blocky subsets correspond to choosing which complete blocks to include,
plus choosing elements from the partial block. The count depends on divisibility.

A blocky k-element subset S of [n] is uniquely determined by:
1. Which complete d-blocks are fully in S (a subset of {0, ..., n/d - 1} of size k/d)
2. Which elements of the partial block are in S (a subset of {0, ..., n%d - 1} of size k%d)

This gives a bijection with pairs from
  (Finset.range (n/d)).powersetCard (k/d) × (Finset.range (n%d)).powersetCard (k%d)
which has cardinality (n/d).choose(k/d) * (n%d).choose(k%d).

When k%d > n%d, no such subsets exist (can't choose k%d elements from n%d available). -/
theorem blocky_subsets_count (d n k : ℕ) (hd : 0 < d) :
    (blockySubsets d n k).card =
    if k % d ≤ n % d then (n / d).choose (k / d) * (n % d).choose (k % d) else 0 := by
  by_cases hle : k % d ≤ n % d
  · simp only [hle, ↓reduceIte]
    -- Define the bijection functions
    let blockyToPair (S : Finset ℕ) : Finset ℕ × Finset ℕ :=
      ((Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S),
       (Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S))
    let pairToBlocky (pair : Finset ℕ × Finset ℕ) : Finset ℕ :=
      (pair.1.biUnion (fun i => (Finset.range d).image (fun j => i * d + j))) ∪
      (pair.2.image (fun j => (n / d) * d + j))
    let blockChoices : Finset (Finset ℕ × Finset ℕ) :=
      (Finset.range (n / d)).powersetCard (k / d) ×ˢ
      (Finset.range (n % d)).powersetCard (k % d)
    -- Helper: complete block region card = d * (number of full blocks)
    have complete_block_card : ∀ S : Finset ℕ,
        (∀ i < n / d, (∀ j < d, i * d + j ∈ S) ∨ (∀ j < d, i * d + j ∉ S)) →
        (S.filter (fun x => x < (n / d) * d)).card =
        d * ((Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S)).card := by
      intro S hSblocky
      have heq : S.filter (fun x => x < (n / d) * d) =
          ((Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S)).biUnion
            (fun i => (Finset.range d).image (fun j => i * d + j)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨hxS, hxlt⟩
          have hi : x / d < n / d := div_lt_of_lt_mul' x n d hxlt
          use x / d
          constructor
          · constructor
            · exact hi
            · rcases hSblocky (x / d) hi with hall | hnone
              · exact hall
              · have hxmod : x % d < d := Nat.mod_lt x hd
                have := hnone (x % d) hxmod
                have hx_eq : x = (x / d) * d + x % d := div_mod_eq' x d hd
                rw [← hx_eq] at this
                exact absurd hxS this
          · use x % d
            exact ⟨Nat.mod_lt x hd, (div_mod_eq' x d hd).symm⟩
        · intro ⟨i, ⟨hi, hall⟩, j, hj, heq⟩
          rw [← heq]
          exact ⟨hall j hj, by calc i * d + j < i * d + d := Nat.add_lt_add_left hj _
            _ = (i + 1) * d := by ring
            _ ≤ (n / d) * d := Nat.mul_le_mul_right d hi⟩
      rw [heq, Finset.card_biUnion]
      · have hinj : ∀ i ∈ (Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S),
            ((Finset.range d).image (fun j => i * d + j)).card = d := by
          intro i _; rw [Finset.card_image_of_injective]
          · exact Finset.card_range d
          · intro a b hab; simp only at hab; omega
        rw [Finset.sum_congr rfl hinj, Finset.sum_const, smul_eq_mul]; ring
      · intro i₁ hi₁ i₂ hi₂ hne
        simp only [Function.onFun, Finset.disjoint_iff_ne]
        intro a ha b hb
        simp only [Finset.mem_image, Finset.mem_range] at ha hb
        obtain ⟨j₁, hj₁, rfl⟩ := ha
        obtain ⟨j₂, hj₂, rfl⟩ := hb
        intro heq
        have h1 : i₁ = (i₁ * d + j₁) / d := (mul_div_add_mod' i₁ j₁ d hd hj₁).symm
        have h2 : i₂ = (i₂ * d + j₂) / d := (mul_div_add_mod' i₂ j₂ d hd hj₂).symm
        rw [h1, heq, ← h2] at hne; exact hne rfl
    -- Helper: partial block region card
    have partial_block_card : ∀ S : Finset ℕ, S ⊆ Finset.range n →
        (S.filter (fun x => (n / d) * d ≤ x)).card =
        ((Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S)).card := by
      intro S hSsub
      have heq : S.filter (fun x => (n / d) * d ≤ x) =
          ((Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S)).image
            (fun j => (n / d) * d + j) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨hxS, hxge⟩
          have hx_lt : x < n := Finset.mem_range.mp (hSsub hxS)
          have hn_eq : n = (n / d) * d + n % d := div_mod_eq' n d hd
          use x - (n / d) * d
          constructor
          · constructor
            · omega
            · convert hxS using 1; omega
          · omega
        · intro ⟨j, ⟨_, hj_in⟩, heq⟩; rw [← heq]; exact ⟨hj_in, by omega⟩
      rw [heq, Finset.card_image_of_injective]; intro a b hab; simp only at hab; omega
    -- Helper: S splits into complete and partial parts
    have S_split : ∀ S : Finset ℕ,
        S.card = (S.filter (fun x => x < (n / d) * d)).card +
                 (S.filter (fun x => (n / d) * d ≤ x)).card := by
      intro S
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext x; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hx; by_cases hxlt : x < (n / d) * d
          · left; exact ⟨hx, hxlt⟩
          · right; exact ⟨hx, Nat.not_lt.mp hxlt⟩
        · intro hcase; rcases hcase with ⟨hx, _⟩ | ⟨hx, _⟩ <;> exact hx
      · rw [Finset.disjoint_iff_ne]; intro a ha b hb
        simp only [Finset.mem_filter] at ha hb; omega
    -- Helper: snd_card < d
    have snd_lt : ∀ S : Finset ℕ,
        ((Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S)).card < d := by
      intro S
      calc ((Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S)).card
          ≤ (Finset.range (n % d)).card := Finset.card_filter_le _ _
        _ = n % d := Finset.card_range _
        _ < d := Nat.mod_lt n hd
    -- Prove the bijection
    have hbij : (blockySubsets d n k).card = blockChoices.card := by
      apply Finset.card_bij' (fun S _ => blockyToPair S) (fun pair _ => pairToBlocky pair)
      · -- blockyToPair maps blockySubsets to blockChoices
        intro S hS
        simp only [blockySubsets, kSubsets, Finset.mem_filter, Finset.mem_powersetCard] at hS
        obtain ⟨⟨hSsub, hScard⟩, _, hSblocky⟩ := hS
        simp only [blockChoices, Finset.mem_product, Finset.mem_powersetCard]
        have hcomplete := complete_block_card S hSblocky
        have hpartial := partial_block_card S hSsub
        have hsplit := S_split S
        rw [hScard, hcomplete, hpartial] at hsplit
        have hsnd_lt := snd_lt S
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · intro i hi; simp only [blockyToPair, Finset.mem_filter, Finset.mem_range] at hi
          exact Finset.mem_range.mpr hi.1
        · rw [hsplit, Nat.mul_add_div hd, Nat.div_eq_of_lt hsnd_lt, add_zero]
        · intro j hj; simp only [blockyToPair, Finset.mem_filter, Finset.mem_range] at hj
          exact Finset.mem_range.mpr hj.1
        · rw [hsplit, Nat.mul_add_mod, Nat.mod_eq_of_lt hsnd_lt]
      · -- pairToBlocky maps blockChoices to blockySubsets
        intro pair hpair
        simp only [blockChoices, Finset.mem_product, Finset.mem_powersetCard] at hpair
        obtain ⟨⟨h1sub, h1card⟩, ⟨h2sub, h2card⟩⟩ := hpair
        simp only [blockySubsets, kSubsets, Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · -- pairToBlocky pair ⊆ range n
          intro x hx
          simp only [pairToBlocky, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
            Finset.mem_range] at hx
          rcases hx with ⟨i, hi, j, hj, rfl⟩ | ⟨j, hj, rfl⟩
          · have hi_lt : i < n / d := Finset.mem_range.mp (h1sub hi)
            have hn : n = (n / d) * d + n % d := div_mod_eq' n d hd
            simp only [Finset.mem_range]; nlinarith
          · have hj_lt : j < n % d := Finset.mem_range.mp (h2sub hj)
            have hn : n = (n / d) * d + n % d := div_mod_eq' n d hd
            simp only [Finset.mem_range]; omega
        · -- card = k
          simp only [pairToBlocky]
          have hdisj : Disjoint (pair.1.biUnion (fun i => (Finset.range d).image (fun j => i * d + j)))
                                (pair.2.image (fun j => (n / d) * d + j)) := by
            rw [Finset.disjoint_iff_ne]
            intro a ha b hb
            simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at ha hb
            obtain ⟨i, hi, j, hj, rfl⟩ := ha
            obtain ⟨j', hj', rfl⟩ := hb
            have hi_lt : i < n / d := Finset.mem_range.mp (h1sub hi)
            intro heq; nlinarith
          rw [Finset.card_union_of_disjoint hdisj]
          have hcard1 : (pair.1.biUnion (fun i => (Finset.range d).image (fun j => i * d + j))).card =
                        pair.1.card * d := by
            rw [Finset.card_biUnion]
            · have hinj : ∀ i ∈ pair.1, ((Finset.range d).image (fun j => i * d + j)).card = d := by
                intro i _; rw [Finset.card_image_of_injective]
                · exact Finset.card_range d
                · intro a b hab; simp only at hab; omega
              rw [Finset.sum_congr rfl hinj, Finset.sum_const, smul_eq_mul]
            · intro i₁ hi₁ i₂ hi₂ hne
              simp only [Function.onFun, Finset.disjoint_iff_ne]
              intro a ha b hb
              simp only [Finset.mem_image, Finset.mem_range] at ha hb
              obtain ⟨j₁, hj₁, rfl⟩ := ha
              obtain ⟨j₂, hj₂, rfl⟩ := hb
              intro heq
              have h1 : i₁ = (i₁ * d + j₁) / d := (mul_div_add_mod' i₁ j₁ d hd hj₁).symm
              have h2 : i₂ = (i₂ * d + j₂) / d := (mul_div_add_mod' i₂ j₂ d hd hj₂).symm
              rw [h1, heq, ← h2] at hne; exact hne rfl
          have hcard2 : (pair.2.image (fun j => (n / d) * d + j)).card = pair.2.card := by
            rw [Finset.card_image_of_injective]; intro a b hab; simp only at hab; omega
          rw [hcard1, hcard2, h1card, h2card]
          have hk : k = (k / d) * d + k % d := div_mod_eq' k d hd
          omega
        · -- IsDBlocky
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [pairToBlocky, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
              Finset.mem_range] at hx
            rcases hx with ⟨i, hi, j, hj, rfl⟩ | ⟨j, hj, rfl⟩
            · have hi_lt : i < n / d := Finset.mem_range.mp (h1sub hi)
              have hn : n = (n / d) * d + n % d := div_mod_eq' n d hd
              simp only [Finset.mem_range]; nlinarith
            · have hj_lt : j < n % d := Finset.mem_range.mp (h2sub hj)
              have hn : n = (n / d) * d + n % d := div_mod_eq' n d hd
              simp only [Finset.mem_range]; omega
          · intro i hi_lt
            by_cases hi : i ∈ pair.1
            · left; intro j hj
              simp only [pairToBlocky, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
                Finset.mem_range]
              left; exact ⟨i, hi, j, hj, rfl⟩
            · right; intro j hj hcontra
              simp only [pairToBlocky, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
                Finset.mem_range] at hcontra
              rcases hcontra with ⟨i', hi', j', hj', heq⟩ | ⟨j', hj', heq⟩
              · have : i = i' := by
                  have hdiv : (i * d + j) / d = (i' * d + j') / d := by rw [heq]
                  rw [mul_div_add_mod' i j d hd hj, mul_div_add_mod' i' j' d hd hj'] at hdiv
                  exact hdiv
                rw [this] at hi; exact hi hi'
              · have hj'_lt : j' < n % d := Finset.mem_range.mp (h2sub hj')
                nlinarith
      · -- left_inv: pairToBlocky (blockyToPair S) = S
        intro S hS
        simp only [blockySubsets, kSubsets, Finset.mem_filter, Finset.mem_powersetCard] at hS
        obtain ⟨⟨hSsub, _⟩, _, hSblocky⟩ := hS
        ext x
        simp only [pairToBlocky, blockyToPair, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_range, Finset.mem_image]
        constructor
        · intro hx
          rcases hx with ⟨i, ⟨_, hi_all⟩, j, hj, heq⟩ | ⟨j, ⟨_, hj_in⟩, heq⟩
          · rw [← heq]; exact hi_all j hj
          · rw [← heq]; exact hj_in
        · intro hxS
          have hx_lt : x < n := Finset.mem_range.mp (hSsub hxS)
          by_cases hx_complete : x < (n / d) * d
          · left
            have hx_eq : x = (x / d) * d + x % d := div_mod_eq' x d hd
            have hi_lt : x / d < n / d := div_lt_of_lt_mul' x n d hx_complete
            have hj_lt : x % d < d := Nat.mod_lt x hd
            rcases hSblocky (x / d) hi_lt with hall | hnone
            · exact ⟨x / d, ⟨hi_lt, hall⟩, x % d, hj_lt, hx_eq.symm⟩
            · exfalso; have := hnone (x % d) hj_lt; rw [← hx_eq] at this; exact this hxS
          · right
            push Not at hx_complete
            have hn_eq : n = (n / d) * d + n % d := div_mod_eq' n d hd
            use x - (n / d) * d
            refine ⟨⟨by omega, ?_⟩, by omega⟩
            convert hxS using 1; omega
      · -- right_inv: blockyToPair (pairToBlocky pair) = pair
        intro pair hpair
        simp only [blockChoices, Finset.mem_product, Finset.mem_powersetCard] at hpair
        obtain ⟨⟨h1sub, _⟩, ⟨h2sub, _⟩⟩ := hpair
        ext i
        · -- First component
          simp only [blockyToPair, pairToBlocky, Finset.mem_filter, Finset.mem_range,
            Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
          constructor
          · intro ⟨hi, hall⟩
            specialize hall 0 hd; simp only [add_zero] at hall
            rcases hall with ⟨i', hi', j', hj', heq⟩ | ⟨j', hj', heq⟩
            · have : i = i' := by
                have hdiv : (i' * d + j') / d = (i * d) / d := by rw [heq]
                rw [mul_div_add_mod' i' j' d hd hj', Nat.mul_div_cancel i hd] at hdiv
                exact hdiv.symm
              rw [this]; exact hi'
            · exfalso
              have hj'_lt : j' < n % d := Finset.mem_range.mp (h2sub hj')
              have heq' : (n / d) * d + j' = i * d := heq
              have h1' : (n / d) * d ≤ i * d := by omega
              have h2' : i * d < (n / d + 1) * d := by nlinarith
              have hi_eq : i = n / d := by
                have := Nat.lt_of_mul_lt_mul_right h2'
                have := Nat.le_of_mul_le_mul_right h1' hd
                omega
              omega
          · intro hi
            have hi' : i < n / d := Finset.mem_range.mp (h1sub hi)
            exact ⟨hi', fun j hj => Or.inl ⟨i, hi, j, hj, rfl⟩⟩
        · -- Second component
          simp only [blockyToPair, pairToBlocky, Finset.mem_filter, Finset.mem_range,
            Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
          constructor
          · intro ⟨hj, hmem⟩
            rcases hmem with ⟨i', hi', j', hj', heq⟩ | ⟨j', hj', heq⟩
            · exfalso
              have hi'_lt : i' < n / d := Finset.mem_range.mp (h1sub hi')
              nlinarith
            · have : i = j' := by omega
              rw [this]; exact hj'
          · intro hj
            have hj' : i < n % d := Finset.mem_range.mp (h2sub hj)
            exact ⟨hj', Or.inr ⟨i, hj, rfl⟩⟩
    rw [hbij]
    simp only [blockChoices, Finset.card_product, Finset.card_powersetCard, Finset.card_range]
  · simp only [hle, ↓reduceIte]
    have h : n % d < k % d := Nat.lt_of_not_le hle
    rw [blockySubsets_empty_of_gt d n k hd h]
    simp

/-- Sum of elements in a complete d-block starting at i*d -/
private lemma sum_complete_block (i d : ℕ) :
    ((Finset.range d).image (fun j => i * d + j)).sum id = d * d * i + d * (d - 1) / 2 := by
  have hinj : Set.InjOn (fun j => i * d + j) (Finset.range d) := by
    intro a _ b _ hab
    simp only at hab
    omega
  rw [Finset.sum_image hinj]
  simp only [id]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.sum_range_id]
  ring

/-- Sum of elements in complete blocks for a set B of block indices -/
private lemma sum_complete_blocks (B : Finset ℕ) (d : ℕ) :
    (B.biUnion (fun i => (Finset.range d).image (fun j => i * d + j))).sum id =
    d * d * B.sum id + B.card * (d * (d - 1) / 2) := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert]
    have hdisj : Disjoint ((Finset.range d).image (fun j => a * d + j))
        (s.biUnion (fun i => (Finset.range d).image (fun j => i * d + j))) := by
      rw [Finset.disjoint_iff_ne]
      intro x hx y hy
      simp only [Finset.mem_image, Finset.mem_range] at hx
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hy
      obtain ⟨j₁, hj₁, rfl⟩ := hx
      obtain ⟨i, hi, j₂, hj₂, rfl⟩ := hy
      intro heq
      have h1 : (a * d + j₁) / d = a := mul_div_add_mod' a j₁ d (by omega) hj₁
      have h2 : (i * d + j₂) / d = i := mul_div_add_mod' i j₂ d (by omega) hj₂
      have haeqi : a = i := by rw [← h1, heq, h2]
      exact ha (haeqi ▸ hi)
    rw [Finset.sum_union hdisj, ih, sum_complete_block, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    simp only [id]
    ring

/-- Sum of partial block elements -/
private lemma sum_partial_block (P : Finset ℕ) (base : ℕ) :
    (P.image (fun p => base + p)).sum id = P.card * base + P.sum id := by
  have hinj : Set.InjOn (fun p => base + p) P := by
    intro a _ b _ hab
    simp only at hab
    omega
  rw [Finset.sum_image hinj]
  simp only [id]
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]

/-- Key divisibility lemma for the exponent adjustment in blocky_sum_eq.
The difference between the blocky exponent and the qBinomial exponent is divisible by d. -/
private lemma exponent_diff_dvd (k d : ℕ) (hd : 0 < d) :
    (d : ℤ) ∣ (((k / d) * d * (d - 1) / 2 : ℕ) : ℤ) - ((k * (k - 1) / 2 : ℕ) : ℤ) +
             ((((k % d) * ((k % d) - 1) / 2) : ℕ) : ℤ) := by
  set q := k / d
  set r := k % d
  have hk : k = q * d + r := (Nat.div_add_mod' k d).symm
  have heven_qd : 2 ∣ q * d * (d - 1) := by
    have h1 : 2 ∣ d * (d - 1) := (Nat.even_mul_pred_self d).two_dvd
    exact Nat.dvd_trans h1 ⟨q, by ring⟩
  have heven_k : 2 ∣ k * (k - 1) := (Nat.even_mul_pred_self k).two_dvd
  have heven_r : 2 ∣ r * (r - 1) := (Nat.even_mul_pred_self r).two_dvd
  obtain ⟨a, ha⟩ := heven_qd
  obtain ⟨b, hb⟩ := heven_k
  obtain ⟨c, hc⟩ := heven_r
  have ha' : q * d * (d - 1) / 2 = a := by omega
  have hb' : k * (k - 1) / 2 = b := by omega
  have hc' : r * (r - 1) / 2 = c := by omega
  rw [ha', hb', hc']
  have h2 : (2 : ℤ) * ((a : ℤ) - b + c) = (q : ℤ) * d * ((d : ℤ) - q * d - 2 * r) := by
    have eq1 : (2 : ℤ) * a = (q * d * (d - 1) : ℕ) := by simp [ha]
    have eq2 : (2 : ℤ) * b = (k * (k - 1) : ℕ) := by simp [hb]
    have eq3 : (2 : ℤ) * c = (r * (r - 1) : ℕ) := by simp [hc]
    have hk_eq : (k : ℤ) = q * d + r := by simp [hk]
    have hqd_expand : ((q * d * (d - 1) : ℕ) : ℤ) = (q : ℤ) * d * d - q * d := by
      cases d with
      | zero => omega
      | succ d' => simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_succ]; ring
    have hk_expand : ((k * (k - 1) : ℕ) : ℤ) = (k : ℤ) * k - k := by
      cases k with
      | zero => simp
      | succ k' => simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_succ]; ring
    have hr_expand : ((r * (r - 1) : ℕ) : ℤ) = (r : ℤ) * r - r := by
      cases r with
      | zero => simp
      | succ r' => simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_succ]; ring
    calc (2 : ℤ) * ((a : ℤ) - b + c)
        = 2 * a - 2 * b + 2 * c := by ring
      _ = (q * d * (d - 1) : ℕ) - (k * (k - 1) : ℕ) + (r * (r - 1) : ℕ) := by rw [eq1, eq2, eq3]
      _ = ((q : ℤ) * d * d - q * d) - ((k : ℤ) * k - k) + ((r : ℤ) * r - r) := by
          rw [hqd_expand, hk_expand, hr_expand]
      _ = q * d * ((d : ℤ) - q * d - 2 * r) := by rw [hk_eq]; ring
  have hdvd_2 : (d : ℤ) ∣ 2 * ((a : ℤ) - b + c) := by
    rw [h2]
    have h : (d : ℤ) ∣ (q : ℤ) * d := ⟨q, by ring⟩
    exact dvd_mul_of_dvd_left h _
  by_cases hd_odd : Odd d
  · have hgcd : Nat.gcd d 2 = 1 := hd_odd.coprime_two_right
    have : Int.gcd d 2 = 1 := by simp [Int.gcd, hgcd]
    exact Int.dvd_of_dvd_mul_right_of_gcd_one hdvd_2 this
  · simp only [Nat.not_odd_iff_even] at hd_odd
    obtain ⟨d', hd'⟩ := hd_odd
    have h4 : (2 : ℤ) * ((a : ℤ) - b + c) = 4 * q * d' * ((d' : ℤ) - q * d' - r) := by
      rw [h2, hd']; push_cast; ring
    have h_abc : (a : ℤ) - b + c = 2 * q * d' * ((d' : ℤ) - q * d' - r) := by linarith
    rw [h_abc, hd']
    exact ⟨(q : ℤ) * ((d' : ℤ) - q * d' - r), by push_cast; ring⟩

/-- The sum of contributions from blocky subsets gives the product formula.

For blocky subsets, the contribution factors because:
1. Complete blocks contribute d*d*i + d*(d-1)/2 each, and since ω^d = 1,
   the ω^{d*d*i} part is always 1.
2. The partial block contributes independently.
3. The bijection with (block indices, partial elements) pairs allows factoring. -/
theorem blocky_sum_eq {K : Type*} [Field K] {ω : K} {d : ℕ}
    (hω : IsPrimitiveRoot ω d) (hd : 0 < d) (n k : ℕ) :
    ∑ S ∈ blockySubsets d n k, ω ^ (S.sum id - (Finset.range k).sum id) =
    (n / d).choose (k / d) * Polynomial.aeval ω (qBinomial (n % d) (k % d)) := by
  -- Handle edge case k % d > n % d (no blocky subsets exist)
  by_cases hmod : k % d ≤ n % d
  · -- Main case: k % d ≤ n % d
    -- The key insight is that for a blocky subset S determined by (B, P):
    -- S.sum id = d*d*B.sum + |B|*d*(d-1)/2 + |P|*(n/d)*d + P.sum
    -- Since ω^d = 1, the terms d*d*B.sum and |P|*(n/d)*d contribute ω^0 = 1
    -- The |B|*d*(d-1)/2 term is constant across all blocky subsets with same |B|
    -- This allows factoring the sum

    -- Use the bijection from blocky_subsets_count
    let blockChoices : Finset (Finset ℕ × Finset ℕ) :=
      (Finset.range (n / d)).powersetCard (k / d) ×ˢ
      (Finset.range (n % d)).powersetCard (k % d)

    -- Define the bijection functions (same as in blocky_subsets_count)
    let blockyToPair (S : Finset ℕ) : Finset ℕ × Finset ℕ :=
      ((Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S),
       (Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S))
    let pairToBlocky (pair : Finset ℕ × Finset ℕ) : Finset ℕ :=
      (pair.1.biUnion (fun i => (Finset.range d).image (fun j => i * d + j))) ∪
      (pair.2.image (fun j => (n / d) * d + j))

    -- The baseline sum
    let baseline := (Finset.range k).sum id

    -- Rewrite using the bijection
    have hsum_eq : ∑ S ∈ blockySubsets d n k, ω ^ (S.sum id - baseline) =
        ∑ pair ∈ blockChoices, ω ^ ((pairToBlocky pair).sum id - baseline) := by
      -- Use sum_bij' with the bijection from blocky_subsets_count
      -- Helper: complete block region card = d * (number of full blocks)
      have complete_block_card : ∀ S : Finset ℕ,
          (∀ i < n / d, (∀ j < d, i * d + j ∈ S) ∨ (∀ j < d, i * d + j ∉ S)) →
          (S.filter (fun x => x < (n / d) * d)).card =
          d * ((Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S)).card := by
        intro S hSblocky
        have heq : S.filter (fun x => x < (n / d) * d) =
            ((Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S)).biUnion
              (fun i => (Finset.range d).image (fun j => i * d + j)) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
          constructor
          · intro ⟨hxS, hxlt⟩
            have hi : x / d < n / d := div_lt_of_lt_mul' x n d hxlt
            use x / d
            constructor
            · constructor
              · exact hi
              · rcases hSblocky (x / d) hi with hall | hnone
                · exact hall
                · have hxmod : x % d < d := Nat.mod_lt x hd
                  have := hnone (x % d) hxmod
                  have hx_eq : x = (x / d) * d + x % d := div_mod_eq' x d hd
                  rw [← hx_eq] at this
                  exact absurd hxS this
            · use x % d
              exact ⟨Nat.mod_lt x hd, (div_mod_eq' x d hd).symm⟩
          · intro ⟨i, ⟨hi, hall⟩, j, hj, heq⟩
            rw [← heq]
            exact ⟨hall j hj, by calc i * d + j < i * d + d := Nat.add_lt_add_left hj _
              _ = (i + 1) * d := by ring
              _ ≤ (n / d) * d := Nat.mul_le_mul_right d hi⟩
        rw [heq, Finset.card_biUnion]
        · have hinj : ∀ i ∈ (Finset.range (n / d)).filter (fun i => ∀ j < d, i * d + j ∈ S),
              ((Finset.range d).image (fun j => i * d + j)).card = d := by
            intro i _; rw [Finset.card_image_of_injective]
            · exact Finset.card_range d
            · intro a b hab; simp only at hab; omega
          rw [Finset.sum_congr rfl hinj, Finset.sum_const, smul_eq_mul]; ring
        · intro i₁ hi₁ i₂ hi₂ hne
          simp only [Function.onFun, Finset.disjoint_iff_ne]
          intro a ha b hb
          simp only [Finset.mem_image, Finset.mem_range] at ha hb
          obtain ⟨j₁, hj₁, rfl⟩ := ha
          obtain ⟨j₂, hj₂, rfl⟩ := hb
          intro heq
          have h1 : i₁ = (i₁ * d + j₁) / d := (mul_div_add_mod' i₁ j₁ d hd hj₁).symm
          have h2 : i₂ = (i₂ * d + j₂) / d := (mul_div_add_mod' i₂ j₂ d hd hj₂).symm
          rw [h1, heq, ← h2] at hne; exact hne rfl
      -- Helper: partial block region card
      have partial_block_card : ∀ S : Finset ℕ, S ⊆ Finset.range n →
          (S.filter (fun x => (n / d) * d ≤ x)).card =
          ((Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S)).card := by
        intro S hSsub
        have heq : S.filter (fun x => (n / d) * d ≤ x) =
            ((Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S)).image
              (fun j => (n / d) * d + j) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
          constructor
          · intro ⟨hxS, hxge⟩
            have hx_lt : x < n := Finset.mem_range.mp (hSsub hxS)
            have hn_eq : n = (n / d) * d + n % d := div_mod_eq' n d hd
            use x - (n / d) * d
            constructor
            · constructor
              · omega
              · convert hxS using 1; omega
            · omega
          · intro ⟨j, ⟨_, hj_in⟩, heq⟩; rw [← heq]; exact ⟨hj_in, by omega⟩
        rw [heq, Finset.card_image_of_injective]; intro a b hab; simp only at hab; omega
      -- Helper: S splits into complete and partial parts
      have S_split : ∀ S : Finset ℕ,
          S.card = (S.filter (fun x => x < (n / d) * d)).card +
                   (S.filter (fun x => (n / d) * d ≤ x)).card := by
        intro S
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext x; simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · intro hx; by_cases hxlt : x < (n / d) * d
            · left; exact ⟨hx, hxlt⟩
            · right; exact ⟨hx, Nat.not_lt.mp hxlt⟩
          · intro hcase; rcases hcase with ⟨hx, _⟩ | ⟨hx, _⟩ <;> exact hx
        · rw [Finset.disjoint_iff_ne]; intro a ha b hb
          simp only [Finset.mem_filter] at ha hb; omega
      -- Helper: snd_card < d
      have snd_lt : ∀ S : Finset ℕ,
          ((Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S)).card < d := by
        intro S
        calc ((Finset.range (n % d)).filter (fun j => (n / d) * d + j ∈ S)).card
            ≤ (Finset.range (n % d)).card := Finset.card_filter_le _ _
          _ = n % d := Finset.card_range _
          _ < d := Nat.mod_lt n hd
      -- Now apply sum_bij'
      apply Finset.sum_bij' (fun S _ => blockyToPair S) (fun pair _ => pairToBlocky pair)
      · -- blockyToPair maps blockySubsets to blockChoices
        intro S hS
        simp only [blockySubsets, kSubsets, Finset.mem_filter, Finset.mem_powersetCard] at hS
        obtain ⟨⟨hSsub, hScard⟩, _, hSblocky⟩ := hS
        simp only [blockChoices, Finset.mem_product, Finset.mem_powersetCard]
        have hcomplete := complete_block_card S hSblocky
        have hpartial := partial_block_card S hSsub
        have hsplit := S_split S
        rw [hScard, hcomplete, hpartial] at hsplit
        have hsnd_lt := snd_lt S
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · intro i hi; simp only [blockyToPair, Finset.mem_filter, Finset.mem_range] at hi
          exact Finset.mem_range.mpr hi.1
        · rw [hsplit, Nat.mul_add_div hd, Nat.div_eq_of_lt hsnd_lt, add_zero]
        · intro j hj; simp only [blockyToPair, Finset.mem_filter, Finset.mem_range] at hj
          exact Finset.mem_range.mpr hj.1
        · rw [hsplit, Nat.mul_add_mod, Nat.mod_eq_of_lt hsnd_lt]
      · -- pairToBlocky maps blockChoices to blockySubsets
        intro pair hpair
        simp only [blockChoices, Finset.mem_product, Finset.mem_powersetCard] at hpair
        obtain ⟨⟨h1sub, h1card⟩, ⟨h2sub, h2card⟩⟩ := hpair
        simp only [blockySubsets, kSubsets, Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · -- pairToBlocky pair ⊆ range n
          intro x hx
          simp only [pairToBlocky, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
            Finset.mem_range] at hx
          rcases hx with ⟨i, hi, j, hj, rfl⟩ | ⟨j, hj, rfl⟩
          · have hi_lt : i < n / d := Finset.mem_range.mp (h1sub hi)
            have hn : n = (n / d) * d + n % d := div_mod_eq' n d hd
            simp only [Finset.mem_range]; nlinarith
          · have hj_lt : j < n % d := Finset.mem_range.mp (h2sub hj)
            have hn : n = (n / d) * d + n % d := div_mod_eq' n d hd
            simp only [Finset.mem_range]; omega
        · -- card = k
          simp only [pairToBlocky]
          have hdisj : Disjoint (pair.1.biUnion (fun i => (Finset.range d).image (fun j => i * d + j)))
                                (pair.2.image (fun j => (n / d) * d + j)) := by
            rw [Finset.disjoint_iff_ne]
            intro a ha b hb
            simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at ha hb
            obtain ⟨i, hi, j, hj, rfl⟩ := ha
            obtain ⟨j', hj', rfl⟩ := hb
            have hi_lt : i < n / d := Finset.mem_range.mp (h1sub hi)
            intro heq; nlinarith
          rw [Finset.card_union_of_disjoint hdisj]
          have hcard1 : (pair.1.biUnion (fun i => (Finset.range d).image (fun j => i * d + j))).card =
                        pair.1.card * d := by
            rw [Finset.card_biUnion]
            · have hinj : ∀ i ∈ pair.1, ((Finset.range d).image (fun j => i * d + j)).card = d := by
                intro i _; rw [Finset.card_image_of_injective]
                · exact Finset.card_range d
                · intro a b hab; simp only at hab; omega
              rw [Finset.sum_congr rfl hinj, Finset.sum_const, smul_eq_mul]
            · intro i₁ hi₁ i₂ hi₂ hne
              simp only [Function.onFun, Finset.disjoint_iff_ne]
              intro a ha b hb
              simp only [Finset.mem_image, Finset.mem_range] at ha hb
              obtain ⟨j₁, hj₁, rfl⟩ := ha
              obtain ⟨j₂, hj₂, rfl⟩ := hb
              intro heq
              have h1 : i₁ = (i₁ * d + j₁) / d := (mul_div_add_mod' i₁ j₁ d hd hj₁).symm
              have h2 : i₂ = (i₂ * d + j₂) / d := (mul_div_add_mod' i₂ j₂ d hd hj₂).symm
              rw [h1, heq, ← h2] at hne; exact hne rfl
          have hcard2 : (pair.2.image (fun j => (n / d) * d + j)).card = pair.2.card := by
            rw [Finset.card_image_of_injective]; intro a b hab; simp only at hab; omega
          rw [hcard1, hcard2, h1card, h2card]
          have hk : k = (k / d) * d + k % d := div_mod_eq' k d hd
          omega
        · -- IsDBlocky
          refine ⟨?_, ?_⟩
          · intro x hx
            simp only [pairToBlocky, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
              Finset.mem_range] at hx
            rcases hx with ⟨i, hi, j, hj, rfl⟩ | ⟨j, hj, rfl⟩
            · have hi_lt : i < n / d := Finset.mem_range.mp (h1sub hi)
              have hn : n = (n / d) * d + n % d := div_mod_eq' n d hd
              simp only [Finset.mem_range]; nlinarith
            · have hj_lt : j < n % d := Finset.mem_range.mp (h2sub hj)
              have hn : n = (n / d) * d + n % d := div_mod_eq' n d hd
              simp only [Finset.mem_range]; omega
          · intro i hi_lt
            by_cases hi : i ∈ pair.1
            · left; intro j hj
              simp only [pairToBlocky, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
                Finset.mem_range]
              left; exact ⟨i, hi, j, hj, rfl⟩
            · right; intro j hj hcontra
              simp only [pairToBlocky, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
                Finset.mem_range] at hcontra
              rcases hcontra with ⟨i', hi', j', hj', heq⟩ | ⟨j', hj', heq⟩
              · have : i = i' := by
                  have hdiv : (i * d + j) / d = (i' * d + j') / d := by rw [heq]
                  rw [mul_div_add_mod' i j d hd hj, mul_div_add_mod' i' j' d hd hj'] at hdiv
                  exact hdiv
                rw [this] at hi; exact hi hi'
              · have hj'_lt : j' < n % d := Finset.mem_range.mp (h2sub hj')
                nlinarith
      · -- left_inv: pairToBlocky (blockyToPair S) = S
        intro S hS
        simp only [blockySubsets, kSubsets, Finset.mem_filter, Finset.mem_powersetCard] at hS
        obtain ⟨⟨hSsub, _⟩, _, hSblocky⟩ := hS
        ext x
        simp only [pairToBlocky, blockyToPair, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_range, Finset.mem_image]
        constructor
        · intro hx
          rcases hx with ⟨i, ⟨_, hi_all⟩, j, hj, heq⟩ | ⟨j, ⟨_, hj_in⟩, heq⟩
          · rw [← heq]; exact hi_all j hj
          · rw [← heq]; exact hj_in
        · intro hxS
          have hx_lt : x < n := Finset.mem_range.mp (hSsub hxS)
          by_cases hx_complete : x < (n / d) * d
          · left
            have hx_eq : x = (x / d) * d + x % d := div_mod_eq' x d hd
            have hi_lt : x / d < n / d := div_lt_of_lt_mul' x n d hx_complete
            have hj_lt : x % d < d := Nat.mod_lt x hd
            rcases hSblocky (x / d) hi_lt with hall | hnone
            · exact ⟨x / d, ⟨hi_lt, hall⟩, x % d, hj_lt, hx_eq.symm⟩
            · exfalso; have := hnone (x % d) hj_lt; rw [← hx_eq] at this; exact this hxS
          · right
            push Not at hx_complete
            have hn_eq : n = (n / d) * d + n % d := div_mod_eq' n d hd
            use x - (n / d) * d
            refine ⟨⟨by omega, ?_⟩, by omega⟩
            convert hxS using 1; omega
      · -- right_inv: blockyToPair (pairToBlocky pair) = pair
        intro pair hpair
        simp only [blockChoices, Finset.mem_product, Finset.mem_powersetCard] at hpair
        obtain ⟨⟨h1sub, _⟩, ⟨h2sub, _⟩⟩ := hpair
        ext i
        · -- First component
          simp only [blockyToPair, pairToBlocky, Finset.mem_filter, Finset.mem_range,
            Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
          constructor
          · intro ⟨hi, hall⟩
            specialize hall 0 hd; simp only [add_zero] at hall
            rcases hall with ⟨i', hi', j', hj', heq⟩ | ⟨j', hj', heq⟩
            · have : i = i' := by
                have hdiv : (i' * d + j') / d = (i * d) / d := by rw [heq]
                rw [mul_div_add_mod' i' j' d hd hj', Nat.mul_div_cancel i hd] at hdiv
                exact hdiv.symm
              rw [this]; exact hi'
            · exfalso
              have hj'_lt : j' < n % d := Finset.mem_range.mp (h2sub hj')
              have heq' : (n / d) * d + j' = i * d := heq
              have h1' : (n / d) * d ≤ i * d := by omega
              have h2' : i * d < (n / d + 1) * d := by nlinarith
              have hi_eq : i = n / d := by
                have := Nat.lt_of_mul_lt_mul_right h2'
                have := Nat.le_of_mul_le_mul_right h1' hd
                omega
              omega
          · intro hi
            have hi' : i < n / d := Finset.mem_range.mp (h1sub hi)
            exact ⟨hi', fun j hj => Or.inl ⟨i, hi, j, hj, rfl⟩⟩
        · -- Second component
          simp only [blockyToPair, pairToBlocky, Finset.mem_filter, Finset.mem_range,
            Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
          constructor
          · intro ⟨hj, hmem⟩
            rcases hmem with ⟨i', hi', j', hj', heq⟩ | ⟨j', hj', heq⟩
            · exfalso
              have hi'_lt : i' < n / d := Finset.mem_range.mp (h1sub hi')
              nlinarith
            · have : i = j' := by omega
              rw [this]; exact hj'
          · intro hj
            have hj' : i < n % d := Finset.mem_range.mp (h2sub hj)
            exact ⟨hj', Or.inr ⟨i, hj, rfl⟩⟩
      · -- The function value is preserved
        intro S hS
        simp only [blockySubsets, kSubsets, Finset.mem_filter, Finset.mem_powersetCard] at hS
        obtain ⟨⟨hSsub, _⟩, _, hSblocky⟩ := hS
        -- We need to show that pairToBlocky (blockyToPair S) = S
        have heq : pairToBlocky (blockyToPair S) = S := by
          ext x
          simp only [pairToBlocky, blockyToPair, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
            Finset.mem_range, Finset.mem_image]
          constructor
          · intro hx
            rcases hx with ⟨i, ⟨_, hi_all⟩, j, hj, heq⟩ | ⟨j, ⟨_, hj_in⟩, heq⟩
            · rw [← heq]; exact hi_all j hj
            · rw [← heq]; exact hj_in
          · intro hxS
            have hx_lt : x < n := Finset.mem_range.mp (hSsub hxS)
            by_cases hx_complete : x < (n / d) * d
            · left
              have hx_eq : x = (x / d) * d + x % d := div_mod_eq' x d hd
              have hi_lt : x / d < n / d := div_lt_of_lt_mul' x n d hx_complete
              have hj_lt : x % d < d := Nat.mod_lt x hd
              rcases hSblocky (x / d) hi_lt with hall | hnone
              · exact ⟨x / d, ⟨hi_lt, hall⟩, x % d, hj_lt, hx_eq.symm⟩
              · exfalso; have := hnone (x % d) hj_lt; rw [← hx_eq] at this; exact this hxS
            · right
              push Not at hx_complete
              have hn_eq : n = (n / d) * d + n % d := div_mod_eq' n d hd
              use x - (n / d) * d
              refine ⟨⟨by omega, ?_⟩, by omega⟩
              convert hxS using 1; omega
        simp only [heq]

    rw [hsum_eq]

    -- For each pair (B, P), compute the sum of pairToBlocky (B, P)
    have hpair_sum : ∀ pair ∈ blockChoices,
        (pairToBlocky pair).sum id =
        d * d * pair.1.sum id + pair.1.card * (d * (d - 1) / 2) +
        pair.2.card * ((n / d) * d) + pair.2.sum id := by
      intro pair hpair
      simp only [pairToBlocky]
      have hpair' : pair ∈ (Finset.range (n / d)).powersetCard (k / d) ×ˢ
          (Finset.range (n % d)).powersetCard (k % d) := hpair
      simp only [Finset.mem_product, Finset.mem_powersetCard] at hpair'
      obtain ⟨⟨hB, _⟩, ⟨hP, _⟩⟩ := hpair'
      have hdisj : Disjoint
          (pair.1.biUnion (fun i => (Finset.range d).image (fun j => i * d + j)))
          (pair.2.image (fun j => (n / d) * d + j)) := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb
        simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at ha hb
        obtain ⟨i, hi, j, hj, rfl⟩ := ha
        obtain ⟨p, hp, rfl⟩ := hb
        have hi' : i < n / d := Finset.mem_range.mp (hB hi)
        intro heq
        have h1 : i * d + j < (n / d) * d := by
          have : (i + 1) * d ≤ (n / d) * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hi')
          calc i * d + j < i * d + d := Nat.add_lt_add_left hj _
            _ = (i + 1) * d := by ring
            _ ≤ (n / d) * d := this
        omega
      rw [Finset.sum_union hdisj, sum_complete_blocks, sum_partial_block]
      ring

    -- Since ω^d = 1, we have ω^{d*d*x} = 1 and ω^{d*y} = 1
    have hω_d : ω ^ d = 1 := hω.pow_eq_one

    -- Factor the sum
    have hfactor : ∑ pair ∈ blockChoices, ω ^ ((pairToBlocky pair).sum id - baseline) =
        ∑ B ∈ (Finset.range (n / d)).powersetCard (k / d),
        ∑ P ∈ (Finset.range (n % d)).powersetCard (k % d),
        ω ^ ((pairToBlocky (B, P)).sum id - baseline) := by
      rw [← Finset.sum_product']

    rw [hfactor]

    -- The key simplification: the B-dependent parts become constant
    -- because ω^{d*d*B.sum} = (ω^d)^{d*B.sum} = 1
    -- and ω^{|B|*d*(d-1)/2} = ω^{(k/d)*d*(d-1)/2} is constant for fixed k

    -- Key lemma: powers are equal when exponents differ by a multiple of d
    have pow_eq_of_diff_dvd : ∀ a b : ℕ, (d : ℤ) ∣ ((a : ℤ) - b) → ω ^ a = ω ^ b := by
      intro a b hdiv
      obtain ⟨c, hc⟩ := hdiv
      by_cases hd' : d = 0
      · simp only [hd', Nat.cast_zero] at hc
        have hab : (a : ℤ) = b := by linarith
        simp only [Int.ofNat_inj.mp hab]
      · by_cases hc_pos : c ≥ 0
        · have hab : a = b + c.toNat * d := by
            have : (a : ℤ) = b + c * d := by linarith
            have hc_nat : c = c.toNat := (Int.toNat_of_nonneg hc_pos).symm
            rw [hc_nat] at this; omega
          rw [hab, pow_add, mul_comm, pow_mul]
          have h1 : (ω ^ c.toNat) ^ d = 1 := by
            rw [← pow_mul, mul_comm, pow_mul, hω_d, one_pow]
          rw [h1, one_mul]
        · push Not at hc_pos
          have hba : b = a + (-c).toNat * d := by
            have : (b : ℤ) = a + (-c) * d := by linarith
            have hc_nat : -c = (-c).toNat := (Int.toNat_of_nonneg (by linarith : -c ≥ 0)).symm
            rw [hc_nat] at this; omega
          rw [hba, pow_add, mul_comm, pow_mul]
          have h1 : (ω ^ (-c).toNat) ^ d = 1 := by
            rw [← pow_mul, mul_comm, pow_mul, hω_d, one_pow]
          simp only [h1, one_mul]

    -- For blocky subsets, the sum is always ≥ baseline (any k-subset has sum ≥ 0+1+...+(k-1))
    have hge : ∀ B P, B ∈ (Finset.range (n / d)).powersetCard (k / d) →
        P ∈ (Finset.range (n % d)).powersetCard (k % d) →
        (pairToBlocky (B, P)).sum id ≥ baseline := by
      intro B P hB hP
      -- First show (pairToBlocky (B, P)).card = k
      simp only [Finset.mem_powersetCard] at hB hP
      obtain ⟨hBsub, hBcard⟩ := hB
      obtain ⟨hPsub, hPcard⟩ := hP
      have hcard : (pairToBlocky (B, P)).card = k := by
        simp only [pairToBlocky]
        have hdisj : Disjoint (B.biUnion (fun i => (Finset.range d).image (fun j => i * d + j)))
                              (P.image (fun j => (n / d) * d + j)) := by
          rw [Finset.disjoint_iff_ne]
          intro a ha b hb
          simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at ha hb
          obtain ⟨i, hi, j, hj, rfl⟩ := ha
          obtain ⟨j', hj', rfl⟩ := hb
          have hi_lt : i < n / d := Finset.mem_range.mp (hBsub hi)
          intro heq; nlinarith
        rw [Finset.card_union_of_disjoint hdisj]
        have hcard1 : (B.biUnion (fun i => (Finset.range d).image (fun j => i * d + j))).card =
                      B.card * d := by
          rw [Finset.card_biUnion]
          · have hinj : ∀ i ∈ B, ((Finset.range d).image (fun j => i * d + j)).card = d := by
              intro i _; rw [Finset.card_image_of_injective]
              · exact Finset.card_range d
              · intro a b hab; simp only at hab; omega
            rw [Finset.sum_congr rfl hinj, Finset.sum_const, smul_eq_mul]
          · intro i₁ hi₁ i₂ hi₂ hne
            simp only [Function.onFun, Finset.disjoint_iff_ne]
            intro a ha b hb
            simp only [Finset.mem_image, Finset.mem_range] at ha hb
            obtain ⟨j₁, hj₁, rfl⟩ := ha
            obtain ⟨j₂, hj₂, rfl⟩ := hb
            intro heq
            have h1 : i₁ = (i₁ * d + j₁) / d := (mul_div_add_mod' i₁ j₁ d hd hj₁).symm
            have h2 : i₂ = (i₂ * d + j₂) / d := (mul_div_add_mod' i₂ j₂ d hd hj₂).symm
            rw [h1, heq, ← h2] at hne; exact hne rfl
        have hcard2 : (P.image (fun j => (n / d) * d + j)).card = P.card := by
          rw [Finset.card_image_of_injective]; intro a b hab; simp only at hab; omega
        rw [hcard1, hcard2, hBcard, hPcard]
        have hk : k = (k / d) * d + k % d := div_mod_eq' k d hd
        omega
      -- Now use the orderIsoOfFin argument
      have hbaseline : baseline = k * (k - 1) / 2 := Finset.sum_range_id k
      rw [hbaseline]
      have h : ∀ i : Fin k, (i : ℕ) ≤ (pairToBlocky (B, P)).orderIsoOfFin hcard i := by
        intro i
        cases k with
        | zero => exact i.elim0
        | succ m =>
          induction i using Fin.inductionOn with
          | zero => simp only [Fin.val_zero, zero_le]
          | succ j ih =>
            have hlt : ((pairToBlocky (B, P)).orderIsoOfFin hcard) (j.castSucc) <
                ((pairToBlocky (B, P)).orderIsoOfFin hcard) j.succ :=
              ((pairToBlocky (B, P)).orderIsoOfFin hcard).strictMono j.castSucc_lt_succ
            have h2 : (j.castSucc : ℕ) ≤
                (((pairToBlocky (B, P)).orderIsoOfFin hcard) j.castSucc : ℕ) := ih
            have hval : (j.castSucc : ℕ) = (j : ℕ) := Fin.val_castSucc j
            calc (j.succ : ℕ) = j + 1 := rfl
              _ ≤ (((pairToBlocky (B, P)).orderIsoOfFin hcard) j.castSucc : ℕ) + 1 := by
                  rw [hval] at h2; omega
              _ ≤ (((pairToBlocky (B, P)).orderIsoOfFin hcard) j.succ : ℕ) := by
                  have : (((pairToBlocky (B, P)).orderIsoOfFin hcard) j.castSucc : ℕ) <
                      (((pairToBlocky (B, P)).orderIsoOfFin hcard) j.succ : ℕ) := hlt
                  omega
      calc k * (k - 1) / 2
          = ∑ i : Fin k, (i : ℕ) := by
              rw [← Finset.sum_range_id]; rw [Finset.sum_range]
        _ ≤ ∑ i : Fin k, ((pairToBlocky (B, P)).orderIsoOfFin hcard i : ℕ) := by
            apply Finset.sum_le_sum; intro i _; exact h i
        _ = (pairToBlocky (B, P)).sum id := by
            have heq : ∑ i : Fin k, ((pairToBlocky (B, P)).orderIsoOfFin hcard i : ℕ) =
                ∑ x : ↥(pairToBlocky (B, P)), (x : ℕ) := by
              conv_lhs =>
                congr; · skip
                · ext i
                  rw [show ((pairToBlocky (B, P)).orderIsoOfFin hcard i : ℕ) =
                      (((pairToBlocky (B, P)).orderIsoOfFin hcard).toEquiv i : ℕ) from rfl]
              rw [Equiv.sum_comp ((pairToBlocky (B, P)).orderIsoOfFin hcard).toEquiv
                  (fun x : ↥(pairToBlocky (B, P)) => (x : ℕ))]
            rw [heq, ← Finset.sum_attach (pairToBlocky (B, P))]; rfl

    -- The inner sum is constant across all B
    have hinner_const : ∀ B₁ B₂, B₁ ∈ (Finset.range (n / d)).powersetCard (k / d) →
        B₂ ∈ (Finset.range (n / d)).powersetCard (k / d) →
        ∑ P ∈ (Finset.range (n % d)).powersetCard (k % d),
          ω ^ ((pairToBlocky (B₁, P)).sum id - baseline) =
        ∑ P ∈ (Finset.range (n % d)).powersetCard (k % d),
          ω ^ ((pairToBlocky (B₂, P)).sum id - baseline) := by
      intro B₁ B₂ hB₁ hB₂
      apply Finset.sum_congr rfl
      intro P hP
      have hB₁card : B₁.card = k / d := (Finset.mem_powersetCard.mp hB₁).2
      have hB₂card : B₂.card = k / d := (Finset.mem_powersetCard.mp hB₂).2
      have h1 := hpair_sum (B₁, P) (Finset.mem_product.mpr ⟨hB₁, hP⟩)
      have h2 := hpair_sum (B₂, P) (Finset.mem_product.mpr ⟨hB₂, hP⟩)
      simp only at h1 h2
      rw [hB₁card] at h1
      rw [hB₂card] at h2
      have hge1 := hge B₁ P hB₁ hP
      have hge2 := hge B₂ P hB₂ hP
      -- The difference is d*d*(B₁.sum - B₂.sum), a multiple of d
      set s1 := (pairToBlocky (B₁, P)).sum id with hs1
      set s2 := (pairToBlocky (B₂, P)).sum id with hs2
      set b1sum := B₁.sum id with hb1sum
      set b2sum := B₂.sum id with hb2sum
      have hdiff : (s1 : ℤ) - s2 = (d : ℤ) * d * ((b1sum : ℤ) - b2sum) := by
        simp only [h1, h2, Nat.cast_add, Nat.cast_mul]; ring
      have hdiff' : ((s1 - baseline : ℕ) : ℤ) - (s2 - baseline : ℕ) = (s1 : ℤ) - s2 := by
        rw [Int.ofNat_sub hge1, Int.ofNat_sub hge2]; ring
      have hdvd : (d : ℤ) ∣ ((s1 - baseline : ℕ) : ℤ) - (s2 - baseline : ℕ) := by
        rw [hdiff', hdiff]
        exact dvd_mul_of_dvd_left (dvd_mul_right (d : ℤ) d) _
      exact pow_eq_of_diff_dvd _ _ hdvd

    -- The cardinality of powersetCard is the binomial coefficient
    have hcard : ((Finset.range (n / d)).powersetCard (k / d)).card = (n / d).choose (k / d) := by
      rw [Finset.card_powersetCard, Finset.card_range]

    -- Factor out the sum over B using hinner_const
    by_cases hne : ((Finset.range (n / d)).powersetCard (k / d)).Nonempty
    · -- Non-empty case: factor out using a representative B₀
      have heq_all : ∀ B ∈ (Finset.range (n / d)).powersetCard (k / d),
          ∑ P ∈ (Finset.range (n % d)).powersetCard (k % d),
            ω ^ ((pairToBlocky (B, P)).sum id - baseline) =
          ∑ P ∈ (Finset.range (n % d)).powersetCard (k % d),
            ω ^ ((pairToBlocky (hne.choose, P)).sum id - baseline) := by
        intro B hB
        exact hinner_const B hne.choose hB (Exists.choose_spec hne)
      rw [Finset.sum_congr rfl heq_all, Finset.sum_const, nsmul_eq_mul, hcard]
      -- Now need to show inner sum = aeval ω (qBinomial (n%d) (k%d))
      -- The inner sum is over P ∈ powersetCard (k%d) (range (n%d))
      -- For each P, the exponent is (pairToBlocky (B₀, P)).sum id - baseline
      -- Using hpair_sum, this equals:
      --   d*d*B₀.sum + |B₀|*d*(d-1)/2 + |P|*(n/d)*d + P.sum - baseline
      -- Since ω^d = 1, the terms d*d*B₀.sum and |P|*(n/d)*d contribute 1
      -- The remaining exponent is |B₀|*d*(d-1)/2 + P.sum - baseline
      -- This should equal (constant) + (P.sum - partial_baseline) where constant is divisible by d
      --
      -- Key insight: the constant (k/d)*d*(d-1)/2 - baseline + partial_baseline is divisible by d
      -- This follows from the identity:
      --   2 * ((k/d)*d*(d-1)/2 - k*(k-1)/2 + (k%d)*(k%d-1)/2) = d * (k/d) * (d - (k/d)*d - 2*(k%d))
      -- and the fact that (k/d) * (d - (k/d)*d - 2*(k%d)) is always even
      -- (either k/d is even, or d - (k/d)*d - 2*(k%d) = ((k/d)-1)*d + 2*(k%d) with (k/d)-1 even)
      --
      -- It suffices to show the inner sums are equal
      congr 1
      -- Expand qBinomial
      unfold qBinomial
      rw [map_sum, ← Finset.powersetCard_eq_filter]
      apply Finset.sum_congr rfl
      intro P hP
      simp only [Polynomial.aeval_X_pow]
      -- Now show the exponents differ by a multiple of d
      have hB₀ := Exists.choose_spec hne
      have hB₀card : hne.choose.card = k / d := (Finset.mem_powersetCard.mp hB₀).2
      have hPcard : P.card = k % d := (Finset.mem_powersetCard.mp hP).2
      have hpair' := hpair_sum (hne.choose, P) (Finset.mem_product.mpr ⟨hB₀, hP⟩)
      simp only at hpair'
      rw [hB₀card, hPcard] at hpair'
      -- Show they differ by a multiple of d
      have hge' := hge hne.choose P hB₀ hP
      -- The qBinomial exponent baseline
      have hqbin_baseline : (Finset.range (k % d)).sum id = (k % d) * ((k % d) - 1) / 2 :=
        Finset.sum_range_id _
      have hqbin_ge : P.sum id ≥ (Finset.range (k % d)).sum id := by
        -- P is a k%d-subset of range (n%d), so P.sum ≥ sum of 0,1,...,(k%d-1)
        rw [hqbin_baseline]
        cases hm : k % d with
        | zero => simp
        | succ m =>
          have hPcard' : P.card = m + 1 := hPcard.trans hm
          have h : ∀ i : Fin (m + 1), (i : ℕ) ≤ P.orderIsoOfFin hPcard' i := by
            intro i
            induction i using Fin.inductionOn with
            | zero => simp only [Fin.val_zero, zero_le]
            | succ j ih =>
              have hlt : (P.orderIsoOfFin hPcard') (j.castSucc) < (P.orderIsoOfFin hPcard') j.succ :=
                (P.orderIsoOfFin hPcard').strictMono j.castSucc_lt_succ
              have h2 : (j.castSucc : ℕ) ≤ ((P.orderIsoOfFin hPcard') j.castSucc : ℕ) := ih
              have hval : (j.castSucc : ℕ) = (j : ℕ) := Fin.val_castSucc j
              have hlt' : ((P.orderIsoOfFin hPcard') j.castSucc : ℕ) <
                  ((P.orderIsoOfFin hPcard') j.succ : ℕ) := hlt
              calc (j.succ : ℕ) = j + 1 := rfl
                _ ≤ ((P.orderIsoOfFin hPcard') j.castSucc : ℕ) + 1 := by rw [hval] at h2; omega
                _ ≤ ((P.orderIsoOfFin hPcard') j.succ : ℕ) := by omega
          calc (m + 1) * ((m + 1) - 1) / 2
              = ∑ i : Fin (m + 1), (i : ℕ) := by rw [← Finset.sum_range_id]; rw [Finset.sum_range]
            _ ≤ ∑ i : Fin (m + 1), ((P.orderIsoOfFin hPcard') i : ℕ) := by
                apply Finset.sum_le_sum; intro i _; exact h i
            _ = P.sum id := by
                have heq : ∑ i : Fin (m + 1), ((P.orderIsoOfFin hPcard') i : ℕ) =
                    ∑ x : ↥P, (x : ℕ) := by
                  conv_lhs =>
                    congr; · skip
                    · ext i
                      rw [show ((P.orderIsoOfFin hPcard') i : ℕ) =
                          (((P.orderIsoOfFin hPcard').toEquiv i : ↥P) : ℕ) from rfl]
                  rw [Equiv.sum_comp ((P.orderIsoOfFin hPcard').toEquiv) (fun x : ↥P => (x : ℕ))]
                rw [heq, ← Finset.sum_attach P]; rfl
      apply pow_eq_of_diff_dvd
      -- Show the difference is divisible by d
      have hbaseline' : baseline = k * (k - 1) / 2 := Finset.sum_range_id k
      -- Set up the integers
      set blocky_sum := (pairToBlocky (hne.choose, P)).sum id
      set qbin_exp := P.sum id - (Finset.range (k % d)).sum id
      -- Key: rewrite (k/d) * (d*(d-1)/2) = (k/d)*d*(d-1)/2
      have heven : 2 ∣ d * (d - 1) := (Nat.even_mul_pred_self d).two_dvd
      have hrewrite : k / d * (d * (d - 1) / 2) = k / d * d * (d - 1) / 2 := by
        have h1 : k / d * (d * (d - 1) / 2) = k / d * (d * (d - 1)) / 2 := by
          rw [Nat.mul_div_assoc (k / d) heven]
        have h2 : k / d * d * (d - 1) / 2 = k / d * (d * (d - 1)) / 2 := by ring_nf
        rw [h1, h2]
      have hdiff : ((blocky_sum - baseline : ℕ) : ℤ) - (qbin_exp : ℕ) =
          ((d * d * hne.choose.sum id : ℕ) : ℤ) + (((k % d) * ((n / d) * d) : ℕ) : ℤ) +
          ((((k / d) * d * (d - 1) / 2 : ℕ) : ℤ) - ((k * (k - 1) / 2 : ℕ) : ℤ) +
           ((((k % d) * ((k % d) - 1) / 2) : ℕ) : ℤ)) := by
        rw [Int.ofNat_sub hge', Int.ofNat_sub hqbin_ge, hbaseline', hqbin_baseline, hpair', hrewrite]
        push_cast
        ring
      rw [hdiff]
      have h1 : (d : ℤ) ∣ ((d * d * hne.choose.sum id : ℕ) : ℤ) := by
        simp only [Nat.cast_mul]
        exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      have h2 : (d : ℤ) ∣ (((k % d) * ((n / d) * d) : ℕ) : ℤ) := by
        simp only [Nat.cast_mul]
        have : (d : ℤ) ∣ (((n / d) * d : ℕ) : ℤ) := by
          simp only [Nat.cast_mul]
          exact dvd_mul_of_dvd_right (dvd_refl _) _
        exact dvd_mul_of_dvd_right this _
      have h3 := exponent_diff_dvd k d hd
      exact Int.dvd_add (Int.dvd_add h1 h2) h3
    · -- Empty case: both sides are 0
      simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      -- Need to show aeval ω (qBinomial (n%d) (k%d)) = 0 or the product is 0
      -- If powersetCard (k/d) (range (n/d)) is empty, then k/d > n/d
      have hkd_gt : k / d > n / d := by
        by_contra h
        push Not at h
        have : ((Finset.range (n / d)).powersetCard (k / d)).Nonempty := by
          rw [Finset.powersetCard_nonempty]
          simp only [Finset.card_range]
          exact h
        exact hne this
      simp only [Nat.choose_eq_zero_of_lt hkd_gt, Nat.cast_zero, zero_mul]

  · -- Case k % d > n % d: no blocky subsets
    push Not at hmod
    have hempty : blockySubsets d n k = ∅ := blockySubsets_empty_of_gt d n k hd hmod
    rw [hempty, Finset.sum_empty]
    have hqbin : qBinomial (n % d) (k % d) = 0 := by
      unfold qBinomial
      apply Finset.sum_eq_zero
      intro S hS
      simp only [Finset.mem_filter, Finset.mem_powerset] at hS
      have : S.card ≤ (Finset.range (n % d)).card := Finset.card_le_card hS.1
      simp only [Finset.card_range] at this
      omega
    simp only [hqbin, map_zero, mul_zero]

/-! #### The Main Theorem -/

/-- **q-Lucas Theorem** (thm.sign.q-lucas)

Let `K` be a field, `d` a positive integer, and `ω` a primitive `d`-th root of unity in `K`.
For `n, k : ℕ`, write `n = q * d + r` and `k = u * d + v` where `0 ≤ r, v < d`.
Then:
  `[n choose k]_ω = (q choose u) * [r choose v]_ω`

This generalizes the formula for `[n choose k]_{-1}` (which is the case `d = 2`).

**Proof idea:** The proof uses a generalization of sign-reversing involutions to d-cycles.
The key insight is that for a primitive d-th root of unity ω, we have
  ∑_{i=0}^{d-1} ω^i = 0 (when d > 1)
This allows cancellation of terms that don't respect the "block structure" where blocks
are consecutive intervals of size d: {0,...,d-1}, {d,...,2d-1}, etc.

A k-element subset S of {0,...,n-1} can be decomposed into:
1. Which "full blocks" it contains (choosing k/d blocks from n/d available blocks)
2. Which elements of the "partial block" {(n/d)*d, ..., n-1} it contains

For subsets that don't respect the block structure, we can define a d-cycle that
permutes related subsets, and the sum of ω^(exponent) over each cycle is zero.
The remaining terms correspond to "blocky" subsets, giving the product formula.
-/
theorem qLucas {K : Type*} [Field K] (d : ℕ) (hd : 0 < d) (ω : K)
    (hω : IsPrimitiveRoot ω d) (n k : ℕ) :
    Polynomial.aeval ω (qBinomial n k) =
    (n / d).choose (k / d) * Polynomial.aeval ω (qBinomial (n % d) (k % d)) := by
  -- Case d = 1: ω = 1
  by_cases hd1 : d = 1
  · subst hd1
    have hω1 : ω = 1 := by
      have h := hω.pow_eq_one
      simp only [pow_one] at h
      exact h
    rw [hω1]
    simp only [Nat.div_one, Nat.mod_one]
    have h00 : qBinomial 0 0 = 1 := by
      unfold qBinomial
      simp only [range_zero, powerset_empty, filter_singleton, card_empty, sum_empty,
        ite_true, sum_singleton, Nat.sub_zero, sum_empty, pow_zero]
    rw [h00, map_one, mul_one]
    unfold qBinomial
    simp only [map_sum, Polynomial.aeval_X_pow, one_pow, sum_const]
    have hcard : ((range n).powerset.filter (fun S => S.card = k)).card = n.choose k := by
      conv_lhs => rw [← powersetCard_eq_filter]
      rw [card_powersetCard, card_range]
    rw [hcard, nsmul_eq_mul, mul_one]
  · -- d ≥ 2
    have hd2 : 1 < d := by omega
    -- Handle k > n case
    by_cases hnk : n < k
    · have hqbin : qBinomial n k = 0 := by
        unfold qBinomial
        apply sum_eq_zero
        intro S hS
        simp only [mem_filter, mem_powerset] at hS
        have : S.card ≤ (range n).card := card_le_card hS.1
        simp only [card_range] at this
        omega
      simp only [hqbin, map_zero]
      by_cases hkd : k / d > n / d
      · simp only [Nat.choose_eq_zero_of_lt hkd, Nat.cast_zero, zero_mul]
      · push Not at hkd
        have hmod : k % d > n % d := by
          have h1 : d * (n / d) + n % d = n := Nat.div_add_mod n d
          have h2 : d * (k / d) + k % d = k := Nat.div_add_mod k d
          by_contra h; push Not at h
          have : k ≤ n := by nlinarith
          omega
        have hqbin2 : qBinomial (n % d) (k % d) = 0 := by
          unfold qBinomial
          apply sum_eq_zero
          intro S hS
          simp only [mem_filter, mem_powerset] at hS
          have : S.card ≤ (range (n % d)).card := card_le_card hS.1
          simp only [card_range] at this
          omega
        simp only [hqbin2, map_zero, mul_zero]
    · -- k ≤ n
      push Not at hnk
      -- Case n < d: then n / d = 0, n % d = n
      by_cases hnd : n < d
      · have hn_div : n / d = 0 := Nat.div_eq_of_lt hnd
        have hn_mod : n % d = n := Nat.mod_eq_of_lt hnd
        rw [hn_div, hn_mod]
        by_cases hkd : k < d
        · have hk_div : k / d = 0 := Nat.div_eq_of_lt hkd
          have hk_mod : k % d = k := Nat.mod_eq_of_lt hkd
          rw [hk_div, hk_mod]
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
        · push Not at hkd
          -- Since k ≥ d > n and k ≤ n, we have a contradiction
          have : n < k := Nat.lt_of_lt_of_le hnd hkd
          omega
      · -- n ≥ d: the main case requiring d-cycle argument
        push Not at hnd
        -- The proof structure is:
        -- 1. Split the sum over k-subsets into blocky and non-blocky parts
        -- 2. Non-blocky contributions cancel (by nonBlocky_contributions_cancel)
        -- 3. Blocky contributions give the product formula (by blocky_sum_eq)
        --
        -- Formally: [n choose k]_ω = ∑_{S : k-subset of [n]} ω^(sum S - baseline)
        --         = ∑_{S blocky} ω^(sum S - baseline) + ∑_{S non-blocky} ω^(sum S - baseline)
        --         = (n/d choose k/d) * [n%d choose k%d]_ω + 0
        --
        -- The key lemmas are:
        -- - nonBlocky_contributions_cancel: non-blocky part is 0
        -- - blocky_sum_eq: blocky part gives the product
        -- Step 1: Rewrite qBinomial aeval as sum over kSubsets
        have haeval : Polynomial.aeval ω (qBinomial n k) =
            ∑ S ∈ kSubsets n k, ω ^ (S.sum id - (Finset.range k).sum id) := by
          unfold qBinomial kSubsets
          rw [map_sum]
          congr 1
          · rw [← powersetCard_eq_filter]
          · ext S
            simp only [Polynomial.aeval_X_pow]
        rw [haeval]
        -- Step 2: Split into blocky and non-blocky
        have hsplit : kSubsets n k =
            blockySubsets d n k ∪ (kSubsets n k).filter (fun S => ¬IsDBlocky d n S) := by
          unfold blockySubsets
          ext S
          simp only [mem_union, mem_filter]
          constructor
          · intro h
            by_cases hb : IsDBlocky d n S
            · exact Or.inl ⟨h, hb⟩
            · exact Or.inr ⟨h, hb⟩
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        have hdisj : Disjoint (blockySubsets d n k)
            ((kSubsets n k).filter (fun S => ¬IsDBlocky d n S)) := by
          unfold blockySubsets
          simp only [disjoint_filter]
          intro S _ hb hnb
          exact hnb hb
        rw [hsplit, sum_union hdisj]
        -- Step 3: Non-blocky part is 0
        have hne : ω ≠ 0 := hω.ne_zero (by omega : d ≠ 0)
        have hnonblocky : ∑ S ∈ (kSubsets n k).filter (fun S => ¬IsDBlocky d n S),
            ω ^ (S.sum id - (Finset.range k).sum id) = 0 := by
          -- Factor out the baseline
          let baseline := (Finset.range k).sum id
          -- For each S in the filter, S.sum id ≥ baseline
          have hge : ∀ S ∈ (kSubsets n k).filter (fun S => ¬IsDBlocky d n S),
              baseline ≤ S.sum id := by
            intro S hS
            simp only [mem_filter] at hS
            -- S is a k-subset, so S.sum id ≥ baseline = k*(k-1)/2
            unfold kSubsets at hS
            rw [mem_powersetCard] at hS
            obtain ⟨_, hScard⟩ := hS.1
            have h1 : baseline = k * (k - 1) / 2 := Finset.sum_range_id k
            rw [h1]
            -- The minimum sum of a k-element subset is k*(k-1)/2
            have h : ∀ i : Fin k, (i : ℕ) ≤ S.orderIsoOfFin hScard i := by
              intro i
              cases k with
              | zero => exact i.elim0
              | succ m =>
                induction i using Fin.inductionOn with
                | zero => simp only [Fin.val_zero, zero_le]
                | succ j ih =>
                  have hlt : (S.orderIsoOfFin hScard) (j.castSucc) <
                      (S.orderIsoOfFin hScard) j.succ :=
                    (S.orderIsoOfFin hScard).strictMono j.castSucc_lt_succ
                  have h2 : (j.castSucc : ℕ) ≤
                      ((S.orderIsoOfFin hScard) j.castSucc : ℕ) := ih
                  have hval : (j.castSucc : ℕ) = (j : ℕ) := Fin.val_castSucc j
                  calc (j.succ : ℕ) = j + 1 := rfl
                    _ ≤ ((S.orderIsoOfFin hScard) j.castSucc : ℕ) + 1 := by
                        rw [hval] at h2; omega
                    _ ≤ ((S.orderIsoOfFin hScard) j.succ : ℕ) := by
                        have : ((S.orderIsoOfFin hScard) j.castSucc : ℕ) <
                            ((S.orderIsoOfFin hScard) j.succ : ℕ) := hlt
                        omega
            calc k * (k - 1) / 2
                = ∑ i : Fin k, (i : ℕ) := by
                    rw [← Finset.sum_range_id]; rw [Finset.sum_range]
              _ ≤ ∑ i : Fin k, (S.orderIsoOfFin hScard i : ℕ) := by
                  apply Finset.sum_le_sum; intro i _; exact h i
              _ = S.sum id := by
                  have heq : ∑ i : Fin k, (S.orderIsoOfFin hScard i : ℕ) =
                      ∑ x : ↥S, (x : ℕ) := by
                    conv_lhs =>
                      congr; · skip
                      · ext i
                        rw [show (S.orderIsoOfFin hScard i : ℕ) =
                            ((S.orderIsoOfFin hScard).toEquiv i : ℕ) from rfl]
                    rw [Equiv.sum_comp (S.orderIsoOfFin hScard).toEquiv
                        (fun x : ↥S => (x : ℕ))]
                  rw [heq, ← Finset.sum_attach S]; rfl
          -- Factor out
          have hfactor : ∑ S ∈ (kSubsets n k).filter (fun S => ¬IsDBlocky d n S),
              ω ^ (S.sum id - baseline) =
              (ω ^ baseline)⁻¹ * ∑ S ∈ (kSubsets n k).filter (fun S => ¬IsDBlocky d n S),
              ω ^ (S.sum id) := by
            rw [mul_sum]
            apply sum_congr rfl
            intro S hS
            have hle := hge S hS
            rw [inv_mul_eq_div, eq_div_iff (pow_ne_zero baseline hne), mul_comm, ← pow_add]
            congr 1
            omega
          rw [hfactor, nonBlocky_contributions_cancel hω hd2 n k, mul_zero]
        rw [hnonblocky, add_zero]
        -- Step 4: Blocky part gives the product
        exact blocky_sum_eq hω hd n k

/-! ### q-Binomial Coefficients at q = -1

We compute `[n choose k]_{-1}` using the q-Lucas theorem with d=2 and ω=-1.
The result depends on the parities of `n` and `k`.

This is Exercise \ref{exe.sign.-1inom} in the source.
-/

/-- A blocky subset of `[n]` (when `n` is even) is a union of blocks `{0,1}, {2,3}, ...`.
Each block is either fully included or fully excluded. -/
def IsBlocky (n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.range n ∧
  ∀ i : ℕ, 2 * i + 1 < n → ((2 * i ∈ S) ↔ (2 * i + 1 ∈ S))

/-- **q-Binomial at q = -1** (exe.sign.-1inom, eq.sol.sign.-1inom.res)

For `n, k : ℕ`, the q-binomial coefficient `[n choose k]_{-1}` equals:
- `0` if `n` is even and `k` is odd
- `⌊n/2⌋ choose ⌊k/2⌋` otherwise

The proof uses the q-Lucas theorem with d=2 and ω=-1:
`[n choose k]_{-1} = (n/2 choose k/2) * [n%2 choose k%2]_{-1}`

The base cases are:
- `[0 choose 0]_{-1} = 1`
- `[0 choose 1]_{-1} = 0`
- `[1 choose 0]_{-1} = 1`
- `[1 choose 1]_{-1} = 1`

Therefore:
- If `Even n ∧ Odd k`: result is `(n/2 choose k/2) * 0 = 0`
- Otherwise: result is `(n/2 choose k/2) * 1 = (n/2 choose k/2)`
-/
theorem qBinom_neg_one (n k : ℕ) :
    (qBinomial n k).eval (-1) =
    if Even n ∧ Odd k then 0
    else (n / 2).choose (k / 2) := by
  classical
  -- Helper lemmas for base cases
  have h00 : (qBinomial 0 0).eval (-1) = 1 := by
    simp only [qBinomial, range_zero, powerset_empty, filter_singleton, card_empty,
      sum_empty, ite_true, sum_singleton, Nat.sub_zero, pow_zero,
      Polynomial.eval_one]
  have h01 : (qBinomial 0 1).eval (-1) = 0 := by
    simp only [qBinomial, Polynomial.eval_finsetSum]
    apply sum_eq_zero
    intro S hS
    simp only [mem_filter, mem_powerset] at hS
    have : S.card ≤ (range 0).card := card_le_card hS.1
    simp only [card_range] at this
    omega
  have h10 : (qBinomial 1 0).eval (-1) = 1 := by
    simp only [qBinomial, Polynomial.eval_finsetSum, Polynomial.eval_X_pow]
    have h : (range 1).powerset.filter (fun S => S.card = 0) = {∅} := by
      ext S; simp only [mem_filter, mem_powerset, mem_singleton, card_eq_zero]
      constructor; intro ⟨_, h2⟩; exact h2; intro h; simp [h]
    rw [h, sum_singleton]; simp
  have h11 : (qBinomial 1 1).eval (-1) = 1 := by
    simp only [qBinomial, Polynomial.eval_finsetSum, Polynomial.eval_X_pow]
    have h : (range 1).powerset.filter (fun S => S.card = 1) = {{0}} := by
      ext S; simp only [mem_filter, mem_powerset, mem_singleton]
      constructor
      · intro ⟨hS, hcard⟩
        have h0 : 0 ∈ S := by
          have : S ⊆ range 1 := hS
          have hne : S.Nonempty := by rw [← card_pos]; omega
          obtain ⟨x, hx⟩ := hne
          have : x ∈ range 1 := this hx
          simp only [mem_range] at this
          have : x = 0 := by omega
          rw [this] at hx; exact hx
        ext x; simp only [mem_singleton]
        constructor
        · intro hx; have : x ∈ range 1 := hS hx; simp only [mem_range] at this; omega
        · intro hx; rw [hx]; exact h0
      · intro hS; simp [hS]
    rw [h, sum_singleton]; simp only [sum_singleton, sum_range_one]; rfl

  -- Evaluate qBinomial (n%2) (k%2) at -1
  have h_mod2 : (qBinomial (n % 2) (k % 2)).eval (-1) =
      if n % 2 = 0 ∧ k % 2 = 1 then 0 else 1 := by
    have hn : n % 2 < 2 := Nat.mod_lt n (by norm_num)
    have hk : k % 2 < 2 := Nat.mod_lt k (by norm_num)
    interval_cases n % 2 <;> interval_cases k % 2 <;> simp_all

  -- The q-Lucas factorization for d=2, ω=-1
  have h_formula : (qBinomial n k).eval (-1) =
      (n / 2).choose (k / 2) * (qBinomial (n % 2) (k % 2)).eval (-1) := by
    -- Use qLucas with d=2, ω=-1 in ℚ
    have hω : IsPrimitiveRoot (-1 : ℚ) 2 := by
      refine IsPrimitiveRoot.mk_of_lt (-1) (by norm_num) (by ring) ?_
      intro l hl hlt
      interval_cases l
      norm_num
    have hLucas := qLucas 2 (by norm_num) (-1 : ℚ) hω n k
    -- Convert between ℤ and ℚ evaluations using injectivity
    have h1 : ((Polynomial.eval (-1 : ℤ) (qBinomial n k) : ℤ) : ℚ) =
        Polynomial.aeval (-1 : ℚ) (qBinomial n k) := by
      simp only [Polynomial.aeval_def]
      rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range]
      push_cast; rfl
    have h2 : ((Polynomial.eval (-1 : ℤ) (qBinomial (n % 2) (k % 2)) : ℤ) : ℚ) =
        Polynomial.aeval (-1 : ℚ) (qBinomial (n % 2) (k % 2)) := by
      simp only [Polynomial.aeval_def]
      rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range]
      push_cast; rfl
    apply Int.cast_injective (α := ℚ)
    rw [h1, hLucas, ← h2]
    push_cast; ring

  -- Combine the results
  rw [h_formula, h_mod2]
  have h_iff : (Even n ∧ Odd k) ↔ (n % 2 = 0 ∧ k % 2 = 1) := by
    simp only [Nat.even_iff, Nat.odd_iff]
  simp only [h_iff]
  by_cases h : n % 2 = 0 ∧ k % 2 = 1
  · obtain ⟨hn0, hk1⟩ := h
    simp only [hn0, hk1, and_self, ↓reduceIte, mul_zero]
    rfl
  · push Not at h
    have hn2 : n % 2 < 2 := Nat.mod_lt n (by norm_num)
    have hk2 : k % 2 < 2 := Nat.mod_lt k (by norm_num)
    by_cases hn0 : n % 2 = 0
    · have hk0 : k % 2 = 0 := by have := h hn0; omega
      simp only [hn0, hk0]
      norm_num
    · have hn1 : n % 2 = 1 := by omega
      simp only [hn1, one_ne_zero, false_and, ↓reduceIte, mul_one]

/-! ### Application: Sum of Signs of Acceptable Sets

We formalize the key step in the combinatorial proof of the negative hockey-stick identity:
the sum of signs of acceptable sets equals `(-1)^m * C(n-1, m)`.
-/

/-- The set of acceptable sets with non-acceptable partners consists exactly of
m-element subsets of `{0, ..., n-1}` that do not contain 0.

Note: We require `0 < n` because when `n = 0`, the partner of `∅` is `{0}` which
is not in `range 0`, but `∅.card = 0` may not equal `m`. -/
theorem acceptable_nonAcceptablePartner_iff (n m : ℕ) (hn : 0 < n) (I : Finset ℕ)
    (hI : I ∈ acceptableSets n m) :
    partner I ∉ acceptableSets n m ↔ (0 ∉ I ∧ I.card = m) := by
  simp only [acceptableSets, mem_filter, mem_powerset] at hI ⊢
  obtain ⟨hIsub, hIcard⟩ := hI
  constructor
  · -- (→) direction: partner I ∉ acceptableSets n m → 0 ∉ I ∧ I.card = m
    intro hpartner
    -- By contrapositive: if 0 ∈ I or I.card < m, then partner I ∈ acceptableSets n m
    by_contra h
    push Not at h
    apply hpartner
    constructor
    · -- partner I ⊆ range n
      intro x hx
      simp only [partner, mem_symmDiff, mem_singleton] at hx
      rcases hx with ⟨hxI, _⟩ | ⟨rfl, _⟩
      · exact hIsub hxI
      · exact mem_range.mpr hn
    · -- partner I.card ≤ m
      unfold partner
      by_cases h0 : 0 ∈ I
      · -- 0 ∈ I: partner I = I \ {0}, card decreases by 1
        have heq : symmDiff I {0} = I.erase 0 := by
          ext x
          simp only [mem_symmDiff, mem_singleton, mem_erase, ne_eq]
          constructor
          · rintro (⟨hxI, hx0⟩ | ⟨rfl, hxI⟩)
            · exact ⟨hx0, hxI⟩
            · exact absurd h0 hxI
          · rintro ⟨hx0, hxI⟩
            exact Or.inl ⟨hxI, hx0⟩
        rw [heq, card_erase_of_mem h0]
        omega
      · -- 0 ∉ I: partner I = I ∪ {0}, card increases by 1
        have heq : symmDiff I {0} = insert 0 I := by
          ext x
          simp only [mem_symmDiff, mem_singleton, mem_insert]
          constructor
          · rintro (⟨hxI, hx0⟩ | ⟨rfl, hxI⟩)
            · exact Or.inr hxI
            · exact Or.inl rfl
          · rintro (rfl | hxI)
            · exact Or.inr ⟨rfl, h0⟩
            · exact Or.inl ⟨hxI, fun hx0 => h0 (hx0 ▸ hxI)⟩
        rw [heq]
        simp only [h0, card_insert_eq_ite, ite_false]
        -- Since 0 ∉ I and h says 0 ∉ I → I.card ≠ m, we get I.card < m
        have hne := h h0
        omega
  · -- (←) direction: 0 ∉ I ∧ I.card = m → partner I ∉ acceptableSets n m
    rintro ⟨h0, hcard⟩
    -- partner I = I ∪ {0} since 0 ∉ I, so partner I.card = m + 1 > m
    intro hpartner
    obtain ⟨_, hpcard⟩ := hpartner
    unfold partner at hpcard
    have heq : symmDiff I {0} = insert 0 I := by
      ext x
      simp only [mem_symmDiff, mem_singleton, mem_insert]
      constructor
      · rintro (⟨hxI, hx0⟩ | ⟨rfl, hxI⟩)
        · exact Or.inr hxI
        · exact Or.inl rfl
      · rintro (rfl | hxI)
        · exact Or.inr ⟨rfl, h0⟩
        · exact Or.inl ⟨hxI, fun hx0 => h0 (hx0 ▸ hxI)⟩
    rw [heq] at hpcard
    simp only [h0, card_insert_eq_ite, ite_false, hcard] at hpcard
    omega

/-- Helper: membership in acceptableSets. -/
private lemma mem_acceptableSets_iff (n m : ℕ) (I : Finset ℕ) :
    I ∈ acceptableSets n m ↔ I ⊆ range n ∧ I.card ≤ m := by
  simp only [acceptableSets, mem_filter, mem_powerset]

/-- The "moving" sets: acceptable sets whose partners are also acceptable. -/
private def movingSets (n m : ℕ) : Finset (Finset ℕ) :=
  (acceptableSets n m).filter (fun I => partner I ∈ acceptableSets n m)

/-- The "fixed" sets: acceptable sets whose partners are not acceptable. -/
private def fixedSets (n m : ℕ) : Finset (Finset ℕ) :=
  (acceptableSets n m).filter (fun I => partner I ∉ acceptableSets n m)

private lemma moving_fixed_disjoint (n m : ℕ) : Disjoint (movingSets n m) (fixedSets n m) := by
  simp only [movingSets, fixedSets]
  rw [Finset.disjoint_filter]
  intro I _ hI
  simp only [not_not]
  exact hI

private lemma moving_fixed_union (n m : ℕ) : movingSets n m ∪ fixedSets n m = acceptableSets n m := by
  ext I
  simp only [movingSets, fixedSets, mem_union, mem_filter]
  constructor
  · intro h
    rcases h with ⟨hI, _⟩ | ⟨hI, _⟩ <;> exact hI
  · intro hI
    by_cases hp : partner I ∈ acceptableSets n m
    · left; exact ⟨hI, hp⟩
    · right; exact ⟨hI, hp⟩

private lemma partner_mem_movingSets (n m : ℕ) (I : Finset ℕ) (hI : I ∈ movingSets n m) :
    partner I ∈ movingSets n m := by
  simp only [movingSets, mem_filter] at hI ⊢
  constructor
  · exact hI.2
  · rw [partner_partner]; exact hI.1

/-- The sum over moving sets is zero by sign-reversing involution. -/
private lemma sum_movingSets_eq_zero (n m : ℕ) : ∑ I ∈ movingSets n m, setSign I = 0 := by
  apply Finset.sum_involution (fun I _ => partner I)
  · intro I _
    rw [partner_sign]
    ring
  · intro I _ hne heq
    have h := partner_sign I
    rw [heq] at h
    simp only [setSign] at h hne
    have : (-1 : ℤ) ^ I.card = 0 := by linarith
    simp at this
  · intro I hI
    exact partner_mem_movingSets n m I hI
  · intro I _
    exact partner_partner I

private lemma fixedSets_card_eq_m (n m : ℕ) (hn : 0 < n) (I : Finset ℕ) (hI : I ∈ fixedSets n m) :
    I.card = m := by
  simp only [fixedSets, mem_filter] at hI
  have := (acceptable_nonAcceptablePartner_iff n m hn I hI.1).mp hI.2
  exact this.2

private lemma fixedSets_setSign (n m : ℕ) (hn : 0 < n) (I : Finset ℕ) (hI : I ∈ fixedSets n m) :
    setSign I = (-1 : ℤ) ^ m := by
  simp only [setSign]
  rw [fixedSets_card_eq_m n m hn I hI]

private lemma fixedSets_eq (n m : ℕ) (hn : 0 < n) :
    fixedSets n m = ((range n).erase 0).powerset.filter (fun I => I.card = m) := by
  ext I
  constructor
  · intro hI
    simp only [fixedSets, mem_filter] at hI
    simp only [mem_filter, mem_powerset]
    obtain ⟨hIacc, hpartner⟩ := hI
    have hchar := (acceptable_nonAcceptablePartner_iff n m hn I hIacc).mp hpartner
    rw [mem_acceptableSets_iff] at hIacc
    constructor
    · intro x hx
      simp only [mem_erase, mem_range]
      constructor
      · intro heq; rw [heq] at hx; exact hchar.1 hx
      · exact mem_range.mp (hIacc.1 hx)
    · exact hchar.2
  · intro hI
    simp only [mem_filter, mem_powerset] at hI
    simp only [fixedSets, mem_filter]
    obtain ⟨hIsub, hIcard⟩ := hI
    have h0 : 0 ∉ I := by
      intro h0
      have := hIsub h0
      simp at this
    have hIacc : I ∈ acceptableSets n m := by
      rw [mem_acceptableSets_iff]
      constructor
      · intro x hx
        have := hIsub hx
        simp only [mem_erase, mem_range] at this
        exact mem_range.mpr this.2
      · omega
    constructor
    · exact hIacc
    · exact (acceptable_nonAcceptablePartner_iff n m hn I hIacc).mpr ⟨h0, hIcard⟩

private lemma card_fixedSets (n m : ℕ) (hn : 0 < n) :
    (fixedSets n m).card = (n - 1).choose m := by
  rw [fixedSets_eq n m hn]
  have h : ((range n).erase 0).powerset.filter (fun I => I.card = m) =
           ((range n).erase 0).powersetCard m := by
    ext I
    simp only [mem_filter, mem_powerset, mem_powersetCard]
  rw [h, card_powersetCard]
  have h0 : 0 ∈ range n := mem_range.mpr hn
  rw [card_erase_of_mem h0, card_range]

private lemma sum_fixedSets (n m : ℕ) (hn : 0 < n) :
    ∑ I ∈ fixedSets n m, setSign I = (-1 : ℤ) ^ m * ((n - 1).choose m) := by
  calc ∑ I ∈ fixedSets n m, setSign I
      = ∑ I ∈ fixedSets n m, (-1 : ℤ) ^ m := by
        apply sum_congr rfl
        intro I hI
        exact fixedSets_setSign n m hn I hI
    _ = (fixedSets n m).card * ((-1 : ℤ) ^ m) := by
        rw [sum_const, nsmul_eq_mul]
    _ = (-1 : ℤ) ^ m * ((n - 1).choose m) := by
        rw [card_fixedSets n m hn]
        ring

/-- The sum of signs of all acceptable sets equals `(-1)^m * C(n-1, m)`. -/
theorem sum_signs_acceptable (n m : ℕ) (hn : 0 < n) :
    ∑ I ∈ acceptableSets n m, setSign I =
    (-1 : ℤ) ^ m * ((n - 1).choose m) := by
  rw [← moving_fixed_union n m]
  rw [sum_union (moving_fixed_disjoint n m)]
  rw [sum_movingSets_eq_zero, sum_fixedSets n m hn]
  ring

end AlgebraicCombinatorics.SignedCounting
