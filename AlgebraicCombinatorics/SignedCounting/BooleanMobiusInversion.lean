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
# Boolean Möbius Inversion

This file formalizes the Boolean Möbius inversion formula, also known as the
Möbius inversion formula for the Boolean lattice.

## Main Results

* `booleanMobiusInversion`: Given functions `a` and `b` on subsets of a finite set `S`
  where `b I = ∑ J ⊆ I, a J` for all `I ⊆ S`, we have `a I = ∑ J ⊆ I, (-1)^|I \ J| * b J`

* `alternatingSum_superset_eq_iverson_a`: For `P ⊆ Q`, we have
  `∑_{I : P ⊆ I ⊆ Q} (-1)^|I| = (-1)^|P| * [P = Q]`

* `alternatingSum_superset_eq_iverson_b`: For `P ⊆ Q`, we have
  `∑_{I : P ⊆ I ⊆ Q} (-1)^|Q \ I| = [P = Q]`

## References

* Source: `AlgebraicCombinatorics/tex/SignedCounting/InclusionExclusion2.tex`
  - Section: `subsec.sign.pie.moeb-bool`
  - Theorem `thm.pie.moeb`
  - Lemma `lem.pie.two-sets-altsum`

## Tags

inclusion-exclusion, Möbius inversion, Boolean lattice, alternating sum
-/

open Finset BigOperators

variable {α : Type*} [DecidableEq α]

namespace BooleanMobius

/-! ### Alternating Sums over Supersets

These lemmas establish the key combinatorial identities needed for the Boolean
Möbius inversion formula.

The key insight is that for P ⊆ Q, the sum `∑_{I : P ⊆ I ⊆ Q} (-1)^|I|` equals
`(-1)^|P|` when P = Q and 0 otherwise. The proof uses the bijection from
`(Q \ P).powerset` to `Icc P Q` (via `Icc_eq_image_powerset`) and then applies
Mathlib's `sum_powerset_neg_one_pow_card`.
-/

/-- Lemma lem.pie.two-sets-altsum (a): For P ⊆ Q finite sets,
    `∑_{I : P ⊆ I ⊆ Q} (-1)^|I| = (-1)^|P| * [P = Q]`

    When P ≠ Q, the sum is 0. When P = Q, the only term is (-1)^|Q|.

    The proof uses the bijection `I ↦ I ∩ (Q \ P)` from `{I : P ⊆ I ⊆ Q}` to
    `(Q \ P).powerset`, and then applies `sum_powerset_neg_one_pow_card`.

    Label: eq.lem.pie.two-sets-altsum.a -/
theorem alternatingSum_superset_eq_iverson_a {P Q : Finset α} (hPQ : P ⊆ Q) :
    ∑ I ∈ Q.powerset.filter (fun I => P ⊆ I), (-1 : ℤ) ^ I.card =
      (-1) ^ P.card * if P = Q then 1 else 0 := by
  -- Rewrite the filter as Icc P Q
  have h1 : Q.powerset.filter (fun I => P ⊆ I) = Icc P Q := by
    rw [Icc_eq_filter_powerset]
  rw [h1]
  -- Use Icc_eq_image_powerset to express as image of (P ∪ ·) on (Q \ P).powerset
  rw [Icc_eq_image_powerset hPQ]
  -- Sum over the image
  rw [sum_image]
  · -- Key: (-1)^|P ∪ T| = (-1)^|P| * (-1)^|T| for T ⊆ Q \ P (since P and T are disjoint)
    have key : ∀ T ∈ (Q \ P).powerset, (-1 : ℤ) ^ (P ∪ T).card = (-1) ^ P.card * (-1) ^ T.card := by
      intro T hT
      rw [mem_powerset] at hT
      have hPT : Disjoint P T := disjoint_of_subset_right hT disjoint_sdiff_self_right
      rw [card_union_of_disjoint hPT, pow_add]
    calc ∑ T ∈ (Q \ P).powerset, (-1 : ℤ) ^ (P ∪ T).card
        = ∑ T ∈ (Q \ P).powerset, (-1 : ℤ) ^ P.card * (-1) ^ T.card := by
          apply sum_congr rfl
          intro T hT
          exact key T hT
      _ = (-1 : ℤ) ^ P.card * ∑ T ∈ (Q \ P).powerset, (-1) ^ T.card := by
          rw [mul_sum]
      _ = (-1 : ℤ) ^ P.card * (if Q \ P = ∅ then 1 else 0) := by
          rw [sum_powerset_neg_one_pow_card]
      _ = (-1 : ℤ) ^ P.card * (if P = Q then 1 else 0) := by
          -- Q \ P = ∅ ↔ Q ⊆ P ↔ P = Q (using hPQ : P ⊆ Q)
          congr 1
          simp only [sdiff_eq_empty_iff_subset]
          split_ifs with h1 h2 h2
          · rfl
          · exact absurd (hPQ.antisymm h1) h2
          · exact absurd (h2 ▸ Subset.refl _) h1
          · rfl
  · -- Injectivity: (P ∪ ·) is injective on (Q \ P).powerset
    intro x hx y hy hxy
    simp only [coe_powerset] at hx hy
    have hxP : Disjoint x P := disjoint_of_subset_left hx disjoint_sdiff_self_left
    have hyP : Disjoint y P := disjoint_of_subset_left hy disjoint_sdiff_self_left
    simp only at hxy
    -- From P ∪ x = P ∪ y and disjointness, we get x = y
    have hx' : (P ∪ x) \ P = x := by rw [union_comm, union_sdiff_self, hxP.sdiff_eq_left]
    have hy' : (P ∪ y) \ P = y := by rw [union_comm, union_sdiff_self, hyP.sdiff_eq_left]
    calc x = (P ∪ x) \ P := hx'.symm
      _ = (P ∪ y) \ P := by rw [hxy]
      _ = y := hy'

/-- Lemma lem.pie.two-sets-altsum (b): For P ⊆ Q finite sets,
    `∑_{I : P ⊆ I ⊆ Q} (-1)^|Q \ I| = [P = Q]`

    This follows from part (a) by the identity |Q \ I| ≡ |Q| + |I| (mod 2).

    Label: eq.lem.pie.two-sets-altsum.b -/
theorem alternatingSum_superset_eq_iverson_b {P Q : Finset α} (hPQ : P ⊆ Q) :
    ∑ I ∈ Q.powerset.filter (fun I => P ⊆ I), (-1 : ℤ) ^ (Q \ I).card =
      if P = Q then 1 else 0 := by
  -- Rewrite using Icc
  rw [← Icc_eq_filter_powerset]
  -- Use the bijection from (Q \ P).powerset to Icc P Q
  rw [Icc_eq_image_powerset hPQ]
  rw [sum_image]
  · -- Now we sum over (Q \ P).powerset
    -- For each J ⊆ Q \ P, the term is (-1)^|Q \ (P ∪ J)| = (-1)^|(Q \ P) \ J|
    have h1 : ∀ J ∈ (Q \ P).powerset, Q \ (P ∪ J) = (Q \ P) \ J := by
      intro J hJ
      rw [mem_powerset] at hJ
      ext x
      simp only [mem_sdiff, mem_union]
      constructor
      · intro ⟨hxQ, hxPJ⟩
        push Not at hxPJ
        exact ⟨⟨hxQ, hxPJ.1⟩, hxPJ.2⟩
      · intro ⟨⟨hxQ, hxP⟩, hxJ⟩
        exact ⟨hxQ, fun h => h.elim hxP hxJ⟩
    have h1' : ∀ J ∈ (Q \ P).powerset, (-1 : ℤ) ^ (Q \ (P ∪ J)).card = (-1) ^ ((Q \ P) \ J).card := by
      intro J hJ
      rw [h1 J hJ]
    rw [sum_congr rfl h1']
    -- Now we have ∑ J ∈ (Q \ P).powerset, (-1)^|(Q \ P) \ J|
    set R := Q \ P with hR_def
    -- For J ⊆ R, we have |R \ J| = |R| - |J|
    have h2 : ∀ J ∈ R.powerset, (R \ J).card = R.card - J.card := by
      intro J hJ
      rw [mem_powerset] at hJ
      exact card_sdiff_of_subset hJ
    -- And (-1)^(|R| - |J|) = (-1)^|R| * (-1)^|J|
    have h3 : ∀ J ∈ R.powerset, (-1 : ℤ) ^ (R \ J).card = (-1)^R.card * (-1)^J.card := by
      intro J hJ
      rw [h2 J hJ]
      rw [mem_powerset] at hJ
      have hle : J.card ≤ R.card := card_le_card hJ
      have key : (-1 : ℤ)^2 = 1 := by norm_num
      calc (-1 : ℤ)^(R.card - J.card) = (-1)^(R.card - J.card) * 1 := by ring
        _ = (-1)^(R.card - J.card) * ((-1)^J.card * (-1)^J.card) := by
            rw [← pow_add, ← two_mul, pow_mul, key, one_pow]
        _ = (-1)^(R.card - J.card) * (-1)^J.card * (-1)^J.card := by ring
        _ = (-1)^(R.card - J.card + J.card) * (-1)^J.card := by rw [pow_add]
        _ = (-1)^R.card * (-1)^J.card := by rw [Nat.sub_add_cancel hle]
    rw [sum_congr rfl h3]
    rw [← mul_sum]
    rw [sum_powerset_neg_one_pow_card]
    -- Now we have (-1)^|R| * (if R = ∅ then 1 else 0) = if P = Q then 1 else 0
    -- R = ∅ ↔ P = Q
    have hR_empty_iff : R = ∅ ↔ P = Q := by
      rw [hR_def]
      constructor
      · intro hR_empty
        rw [sdiff_eq_empty_iff_subset] at hR_empty
        exact Subset.antisymm hPQ hR_empty
      · intro hPQ_eq
        simp [hPQ_eq]
    -- Manual case split
    by_cases hR_empty : R = ∅
    · simp only [hR_empty, ite_true]
      have hPQ_eq : P = Q := hR_empty_iff.mp hR_empty
      simp [hPQ_eq]
    · simp only [hR_empty, ite_false]
      have hPQ_neq : P ≠ Q := fun h => hR_empty (hR_empty_iff.mpr h)
      simp [hPQ_neq]
  · -- Injectivity of the map J ↦ P ∪ J
    intro J1 hJ1 J2 hJ2 h
    simp only [coe_powerset] at hJ1 hJ2
    have hJ1' : J1 ⊆ Q \ P := hJ1
    have hJ2' : J2 ⊆ Q \ P := hJ2
    have heq : P ∪ J1 = P ∪ J2 := h
    ext x
    constructor <;> intro hx
    · have hxJ1 : x ∈ P ∪ J1 := mem_union_right P hx
      rw [heq] at hxJ1
      rcases mem_union.mp hxJ1 with hxP | hxJ2
      · exact absurd hxP (mem_sdiff.mp (hJ1' hx)).2
      · exact hxJ2
    · have hxJ2 : x ∈ P ∪ J2 := mem_union_right P hx
      rw [← heq] at hxJ2
      rcases mem_union.mp hxJ2 with hxP | hxJ1
      · exact absurd hxP (mem_sdiff.mp (hJ2' hx)).2
      · exact hxJ1

/-! ### Boolean Möbius Inversion

The main theorem states that if `b I = ∑_{J ⊆ I} a J` for all I ⊆ S, then
we can recover `a` from `b` via `a I = ∑_{J ⊆ I} (-1)^|I \ J| b J`.

This is a fundamental result in combinatorics, generalizing the inclusion-exclusion
principle.
-/

/-- A helper lemma for swapping sums over pairs (J, P) with P ⊆ J ⊆ Q
    to pairs (P, J) with P ⊆ J ⊆ Q. -/
lemma sum_powerset_powerset_swap {Q : Finset α} {A : Type*} [AddCommGroup A]
    (f : Finset α → Finset α → A) :
    ∑ J ∈ Q.powerset, ∑ P ∈ J.powerset, f J P =
    ∑ P ∈ Q.powerset, ∑ J ∈ Q.powerset.filter (fun J => P ⊆ J), f J P := by
  apply sum_comm'
  intro J P
  simp only [mem_powerset, mem_filter]
  -- Goal: J ⊆ Q ∧ P ⊆ J ↔ (J ⊆ Q ∧ P ⊆ J) ∧ P ⊆ Q
  constructor
  · intro ⟨hJQ, hPJ⟩
    exact ⟨⟨hJQ, hPJ⟩, hPJ.trans hJQ⟩
  · intro ⟨⟨hJQ, hPJ⟩, _⟩
    exact ⟨hJQ, hPJ⟩

/-- Boolean Möbius inversion formula (Theorem thm.pie.moeb):
    Let S be a finite set and A an additive abelian group.
    For each subset I of S, let a_I and b_I be elements of A.

    If `b I = ∑_{J ⊆ I} a J` for all I ⊆ S,
    then `a I = ∑_{J ⊆ I} (-1)^|I \ J| b J` for all I ⊆ S.

    Label: thm.pie.moeb, eq.thm.pie.moeb.ass, eq.thm.pie.moeb.claim -/
theorem booleanMobiusInversion {S : Finset α} {A : Type*} [AddCommGroup A]
    (a b : Finset α → A)
    (hab : ∀ I ⊆ S, b I = ∑ J ∈ I.powerset, a J) :
    ∀ I ⊆ S, a I = ∑ J ∈ I.powerset, (-1 : ℤ) ^ (I \ J).card • b J := by
  intro Q hQS
  -- We prove: a Q = ∑ J ⊆ Q, (-1)^|Q \ J| • b J
  -- First, expand b J
  have step1 : ∑ J ∈ Q.powerset, (-1 : ℤ) ^ (Q \ J).card • b J =
      ∑ J ∈ Q.powerset, (-1 : ℤ) ^ (Q \ J).card • ∑ P ∈ J.powerset, a P := by
    apply sum_congr rfl
    intro J hJ
    rw [mem_powerset] at hJ
    congr 1
    exact hab J (hJ.trans hQS)
  rw [step1]
  -- Distribute the smul
  have step2 : ∑ J ∈ Q.powerset, (-1 : ℤ) ^ (Q \ J).card • ∑ P ∈ J.powerset, a P =
      ∑ J ∈ Q.powerset, ∑ P ∈ J.powerset, (-1 : ℤ) ^ (Q \ J).card • a P := by
    apply sum_congr rfl
    intro J _
    rw [smul_sum]
  rw [step2]
  -- Swap the sums using our helper lemma
  rw [sum_powerset_powerset_swap]
  -- Factor out a P from the inner sum
  have step4 : ∑ P ∈ Q.powerset, ∑ J ∈ Q.powerset.filter (fun J => P ⊆ J), (-1 : ℤ) ^ (Q \ J).card • a P =
      ∑ P ∈ Q.powerset, (∑ J ∈ Q.powerset.filter (fun J => P ⊆ J), (-1 : ℤ) ^ (Q \ J).card) • a P := by
    apply sum_congr rfl
    intro P _
    rw [← sum_smul]
  rw [step4]
  -- Use alternatingSum_superset_eq_iverson_b
  have step5 : ∀ P ∈ Q.powerset, (∑ J ∈ Q.powerset.filter (fun J => P ⊆ J), (-1 : ℤ) ^ (Q \ J).card) • a P =
      (if P = Q then (1 : ℤ) else 0) • a P := by
    intro P hP
    rw [mem_powerset] at hP
    rw [alternatingSum_superset_eq_iverson_b hP]
  rw [sum_congr rfl step5]
  -- Simplify: only the P = Q term survives
  rw [sum_eq_single Q]
  · simp
  · intro P _ hPQ
    simp [hPQ]
  · intro hQ
    exfalso
    exact hQ (mem_powerset.mpr (Subset.refl Q))

/-- Alternative formulation of Boolean Möbius inversion using (-1)^|I \ J| as an integer.
    This is sometimes more convenient for computation. -/
theorem booleanMobiusInversion' {S : Finset α} {A : Type*} [AddCommGroup A] [Module ℤ A]
    (a b : Finset α → A)
    (hab : ∀ I ⊆ S, b I = ∑ J ∈ I.powerset, a J) :
    ∀ I ⊆ S, a I = ∑ J ∈ I.powerset, ((-1 : ℤ) ^ (I \ J).card) • b J := by
  exact booleanMobiusInversion a b hab

end BooleanMobius
