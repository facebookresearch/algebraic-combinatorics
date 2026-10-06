/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import AlgebraicCombinatorics.Permutations.Inversions1

/-!
# Signs of Permutations

This file formalizes the notion of the sign (signature) of a permutation and its properties.

The sign of a permutation σ ∈ Sₙ is defined as (-1)^ℓ(σ) where ℓ(σ) is the length
(number of inversions) of σ. This is a fundamental concept in combinatorics and algebra,
playing a crucial role in the definition of determinants and exterior powers.

## Main definitions

Most definitions are already in Mathlib:
* `Equiv.Perm.sign` - the sign of a permutation as a group homomorphism to ℤˣ
* `alternatingGroup` - the alternating group (kernel of the sign homomorphism)

We provide:
* `Equiv.Perm.IsEven` - a permutation is even if its sign is 1
* `Equiv.Perm.IsOdd` - a permutation is odd if its sign is -1

## Main results

### Properties of the sign (Proposition prop.perm.sign.props)

* `Equiv.Perm.sign_one` (a): sign(id) = 1
* `Equiv.Perm.sign_swap` (b): sign(t_{i,j}) = -1 for distinct i, j
* `Equiv.Perm.sign_cycle` (c): sign of a k-cycle is (-1)^(k-1)
* `Equiv.Perm.sign_mul` (d): sign(στ) = sign(σ) · sign(τ)
* `sign_prod_list` (e): sign of a product equals product of signs
* `Equiv.Perm.sign_inv` (f): sign(σ⁻¹) = sign(σ)
* `sign_eq_prod_pairs` (g): sign as product over pairs
* `prod_diff_comp_perm` (h): product formula for differences

### The sign homomorphism (Corollary cor.perm.sign.hom)

* `Equiv.Perm.sign` is a group homomorphism from Sₙ to {1, -1}

### The alternating group (Corollary cor.perm.altgp)

* `alternatingGroup.normal` - the alternating group is normal in Sₙ

### Counting even/odd permutations (Corollary cor.perm.num-even)

* `card_alternatingGroup` - |Aₙ| = n!/2 for n ≥ 2
* `sum_sign_eq_zero` - Σ_{σ ∈ Sₙ} sign(σ) = 0 for n ≥ 2

### Sign for finite sets (Proposition prop.perm.sign.X)

* Sign can be defined for permutations of any finite set X, independent of chosen bijection

## References

* [Darij Grinberg, *Notes on the combinatorial fundamentals of algebra*][detnotes]
* [Neil Strickland, *Combinatorics and algebra*][Strick13]

## Tags

permutation, sign, signature, alternating group, parity
-/

open Equiv Equiv.Perm Finset BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace Equiv.Perm

/-! ### Definition of sign

The sign of a permutation σ is (-1)^ℓ(σ) where ℓ(σ) is the length (number of inversions).
In Mathlib, this is `Equiv.Perm.sign`.

**Definition (def.perm.sign)**: For n ∈ ℕ, the sign of σ ∈ Sₙ is (-1)^ℓ(σ).
It is denoted (-1)^σ, sgn(σ), sign(σ), or ε(σ).
-/

section SignDefinition

/-!
### Proof that sign σ = (-1)^ℓ(σ)

The fundamental theorem connecting the Mathlib definition of `Equiv.Perm.sign`
(which uses a product formula) with the textbook definition sign(σ) = (-1)^ℓ(σ)
where ℓ(σ) is the number of inversions.

This formalizes **Definition (def.perm.sign)**.
-/

variable {n : ℕ}

/-- The sign of a permutation equals (-1)^ℓ(σ) where ℓ(σ) is the number of inversions.

**Definition (def.perm.sign)**: The sign of σ ∈ Sₙ is defined as (-1)^ℓ(σ),
where ℓ(σ) is the length (number of inversions) of σ.

This theorem proves that Mathlib's `Equiv.Perm.sign` equals the textbook definition. -/
theorem sign_eq_neg_one_pow_invCount (σ : Perm (Fin n)) :
    sign σ = (-1 : ℤˣ) ^ AlgebraicCombinatorics.Perm.invCount σ := by
  rw [σ.sign_eq_prod_prod_Ioi]
  rw [Finset.prod_sigma']
  -- The product equals (-1)^(number of pairs where σ i ≥ σ j, i < j)
  -- Since σ is injective, this equals the number of inversions
  have key : ∀ (s : Finset (Σ _ : Fin n, Fin n)),
      (∏ x ∈ s, (if σ x.1 < σ x.2 then (1 : ℤˣ) else -1)) =
      (-1 : ℤˣ) ^ (s.filter (fun x => ¬ σ x.1 < σ x.2)).card := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | @insert a s' ha ih =>
      rw [Finset.prod_insert ha]
      by_cases h : σ a.1 < σ a.2
      · simp only [h, ↓reduceIte, one_mul]
        rw [Finset.filter_insert, ite_eq_right (by simp [h]), ih]
      · simp only [h, ↓reduceIte]
        rw [Finset.filter_insert, ite_eq_left (by simp [h])]
        rw [Finset.card_insert_of_notMem (by simp [ha])]
        rw [pow_succ, mul_comm, ih]
  rw [key]
  congr 1
  -- Show the count of non-lt pairs equals invCount
  rw [AlgebraicCombinatorics.Perm.invCount, AlgebraicCombinatorics.Perm.inv]
  have equiv_card : ((univ.sigma fun a => Ioi a).filter (fun x => ¬σ x.1 < σ x.2)).card =
      (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.1 > σ p.2) Finset.univ).card := by
    let e : (Σ _ : Fin n, Fin n) ≃ (Fin n × Fin n) := Equiv.sigmaEquivProd (Fin n) (Fin n)
    rw [← Finset.card_map e.toEmbedding]
    congr 1
    ext ⟨i, j⟩
    simp only [mem_map, mem_filter, mem_sigma, mem_univ, mem_Ioi, true_and, not_lt,
      Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨⟨hab, hσ⟩, heq⟩⟩
      have heq' : (a, b) = (i, j) := heq
      simp only [Prod.mk.injEq] at heq'
      obtain ⟨rfl, rfl⟩ := heq'
      exact ⟨hab, lt_of_le_of_ne hσ (fun h => (ne_of_lt hab) (σ.injective h.symm))⟩
    · intro ⟨hij, hσ⟩
      exact ⟨⟨i, j⟩, ⟨⟨hij, le_of_lt hσ⟩, rfl⟩⟩
  exact equiv_card

/-- Corollary: sign as an integer equals (-1)^invCount.
**Definition (def.perm.sign)** -/
theorem sign_coe_eq_neg_one_pow_invCount (σ : Perm (Fin n)) :
    (sign σ : ℤ) = (-1 : ℤ) ^ AlgebraicCombinatorics.Perm.invCount σ := by
  rw [sign_eq_neg_one_pow_invCount]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

end SignDefinition

/-- A permutation is **even** if its sign is 1 (equivalently, if its length is even).
**Definition (def.perm.even-odd)** -/
def IsEven (σ : Perm α) : Prop := sign σ = 1

/-- A permutation is **odd** if its sign is -1 (equivalently, if its length is odd).
**Definition (def.perm.even-odd)** -/
def IsOdd (σ : Perm α) : Prop := sign σ = -1

theorem isEven_iff_sign_eq_one {σ : Perm α} : σ.IsEven ↔ sign σ = 1 := Iff.rfl

theorem isOdd_iff_sign_eq_neg_one {σ : Perm α} : σ.IsOdd ↔ sign σ = -1 := Iff.rfl

theorem isEven_iff_mem_alternatingGroup {σ : Perm α} :
    σ.IsEven ↔ σ ∈ alternatingGroup α :=
  mem_alternatingGroup.symm

theorem isOdd_iff_not_mem_alternatingGroup {σ : Perm α} :
    σ.IsOdd ↔ σ ∉ alternatingGroup α := by
  rw [isOdd_iff_sign_eq_neg_one, mem_alternatingGroup]
  constructor
  · intro h hcontra
    rw [h] at hcontra
    exact absurd hcontra (by decide)
  · intro h
    rcases Int.units_eq_one_or (sign σ) with hsign | hsign
    · exact absurd hsign h
    · exact hsign

/-- The identity permutation is even.
This is a useful base case when reasoning about permutation parity. -/
@[simp]
theorem isEven_one : IsEven (1 : Perm α) := by
  simp [IsEven]

/-- The identity permutation is not odd. -/
@[simp]
theorem not_isOdd_one : ¬IsOdd (1 : Perm α) := by
  simp [IsOdd]

/-- A transposition (swap) is an odd permutation.
This provides a cleaner interface when working with the `IsOdd` predicate
rather than directly with sign values. -/
theorem isOdd_swap {x y : α} (hxy : x ≠ y) : IsOdd (swap x y) := by
  simp [IsOdd, sign_swap hxy]

/-- Every permutation is either even or odd.
This follows from the fact that sign takes values in {1, -1}. -/
theorem isEven_or_isOdd (σ : Perm α) : σ.IsEven ∨ σ.IsOdd := by
  rcases Int.units_eq_one_or (sign σ) with h | h
  · left; exact h
  · right; exact h

/-- A permutation cannot be both even and odd. -/
theorem not_isEven_and_isOdd (σ : Perm α) : ¬(σ.IsEven ∧ σ.IsOdd) := by
  rintro ⟨heven, hodd⟩
  rw [isEven_iff_sign_eq_one] at heven
  rw [isOdd_iff_sign_eq_neg_one] at hodd
  rw [heven] at hodd
  exact absurd hodd (by decide)

/-! ### Properties of the sign (Proposition prop.perm.sign.props) -/

/-- **(a)** The sign of the identity permutation is 1.
**Proposition (prop.perm.sign.props)(a)** -/
theorem sign_id : sign (1 : Perm α) = 1 := sign_one

/-- **(b)** The sign of a transposition is -1.
**Proposition (prop.perm.sign.props)(b)** -/
theorem sign_transposition {x y : α} (hxy : x ≠ y) : sign (swap x y) = -1 :=
  sign_swap hxy

/-- **(c)** The sign of a k-cycle is (-1)^(k-1).
**Proposition (prop.perm.sign.props)(c)**

This follows from the fact that a k-cycle has support of size k and
sign(σ) = -(-1)^|support(σ)| for cycles. -/
theorem sign_isCycle {σ : Perm α} (hσ : σ.IsCycle) :
    sign σ = -(-1 : ℤˣ) ^ σ.support.card :=
  hσ.sign

/-- **(d)** The sign is multiplicative: sign(στ) = sign(σ) · sign(τ).
**Proposition (prop.perm.sign.props)(d)** -/
theorem sign_mul' (σ τ : Perm α) : sign (σ * τ) = sign σ * sign τ :=
  sign_mul σ τ

/-- **(e)** The sign of a product equals the product of signs.
**Proposition (prop.perm.sign.props)(e)** -/
theorem sign_prod_list (l : List (Perm α)) :
    sign l.prod = (l.map sign).prod :=
  map_list_prod sign l

/-- **(f)** The sign of the inverse equals the sign of the permutation.
**Proposition (prop.perm.sign.props)(f)** -/
theorem sign_inv' (σ : Perm α) : sign σ⁻¹ = sign σ :=
  sign_inv σ

/-! ### Product formula for sign (Proposition prop.perm.sign.props (g) and (h))

**(g)** For σ ∈ Sₙ:
  sign(σ) = ∏_{1 ≤ i < j ≤ n} (σ(i) - σ(j)) / (i - j)

**(h)** For any x₁, ..., xₙ in a commutative ring and σ ∈ Sₙ:
  ∏_{1 ≤ i < j ≤ n} (x_{σ(i)} - x_{σ(j)}) = sign(σ) · ∏_{1 ≤ i < j ≤ n} (xᵢ - xⱼ)
-/

/-- **(h)** Product of differences under permutation.
**Proposition (prop.perm.sign.props)(h)**

For any elements x₁, ..., xₙ of a commutative ring and σ ∈ Sₙ:
∏_{i < j} (x_{σ(i)} - x_{σ(j)}) = sign(σ) · ∏_{i < j} (xᵢ - xⱼ)
-/
theorem prod_diff_comp_perm {n : ℕ} {R : Type*} [CommRing R] (σ : Perm (Fin n)) (x : Fin n → R) :
    ∏ i, ∏ j ∈ Ioi i, (x (σ i) - x (σ j)) = sign σ * ∏ i, ∏ j ∈ Ioi i, (x i - x j) := by
  have hf : ∀ i j, x i - x j = -(x j - x i) := fun i j => by ring
  exact σ.prod_Ioi_comp_eq_sign_mul_prod hf

/-- **(g)** Sign as a product over pairs.
**Proposition (prop.perm.sign.props)(g)**

For σ ∈ Sₙ: sign(σ) = ∏_{1 ≤ i < j ≤ n} (σ(i) - σ(j)) / (i - j)

We state this in a slightly different but equivalent form using the indicator function. -/
theorem sign_eq_prod_pairs {n : ℕ} (σ : Perm (Fin n)) :
    sign σ = ∏ i, ∏ j ∈ Ioi i, (if σ i < σ j then 1 else -1) :=
  σ.sign_eq_prod_prod_Ioi

/-! ### The sign homomorphism (Corollary cor.perm.sign.hom)

The map σ ↦ sign(σ) from Sₙ to {1, -1} is a group homomorphism.
This is captured by `Equiv.Perm.sign : Perm α →* ℤˣ` being a `MonoidHom`.
-/

/-- **Corollary (cor.perm.sign.hom)**
The sign is a group homomorphism from Sₙ to {1, -1}.

In Mathlib, this is expressed by `Equiv.Perm.sign` being a `MonoidHom`. -/
theorem sign_hom_mul (σ τ : Perm α) : sign (σ * τ) = sign σ * sign τ :=
  sign_mul σ τ

/-! ### The alternating group (Corollary cor.perm.altgp)

The set of even permutations forms a normal subgroup of Sₙ, called the alternating group.
-/

/-- **Corollary (cor.perm.altgp)**
The set of all even permutations in Sₙ is a normal subgroup.
This is the alternating group Aₙ. -/
theorem alternatingGroup_isNormal : (alternatingGroup α).Normal :=
  alternatingGroup.normal

/-! ### Counting even and odd permutations (Corollary cor.perm.num-even)

For n ≥ 2, the number of even permutations equals the number of odd permutations,
and both equal n!/2.
-/

/-- **Corollary (cor.perm.num-even)**
The number of even permutations in Sₙ equals n!/2 for n ≥ 2.
More precisely, |Aₙ| = (card α)!/2. -/
theorem card_even_perms [Nontrivial α] :
    Fintype.card (alternatingGroup α) = (Fintype.card α).factorial / 2 :=
  card_alternatingGroup

/-- The number of odd permutations equals the number of even permutations.
This follows from the bijection σ ↦ σ * swap(a,b) for any distinct a, b. -/
theorem card_odd_eq_card_even [Nontrivial α] :
    (univ.filter fun σ : Perm α => sign σ = -1).card =
    (univ.filter fun σ : Perm α => sign σ = 1).card := by
  -- The bijection σ ↦ σ * s maps even to odd permutations
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  let s := swap a b
  have hs : sign s = -1 := sign_swap hab
  have hs_sq : s * s = 1 := swap_mul_self a b
  -- Define the bijection between even and odd permutations
  refine Finset.card_bij (fun σ _ => σ * s) ?_ ?_ ?_ |>.symm
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [sign_mul, hσ, hs, one_mul]
  · intro σ₁ _ σ₂ _ h
    exact mul_right_cancel h
  · intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    refine ⟨τ * s, ?_, ?_⟩
    · rw [sign_mul, hτ, hs]
      decide
    · rw [mul_assoc, hs_sq, mul_one]

/-- **Equation (eq.cor.perm.num-even.sum-sign)**
The sum of signs over all permutations is 0 for n ≥ 2.

∑_{σ ∈ Sₙ} sign(σ) = 0 for n ≥ 2
-/
theorem sum_sign_eq_zero [Nontrivial α] :
    ∑ σ : Perm α, (sign σ : ℤ) = 0 := by
  -- The sum equals (# even) * 1 + (# odd) * (-1)
  -- Since # even = # odd, this is 0
  have hodd_card := card_odd_eq_card_even (α := α)
  -- Split sum by sign value
  let evenPerms := (univ : Finset (Perm α)).filter (fun σ => sign σ = 1)
  let oddPerms := (univ : Finset (Perm α)).filter (fun σ => sign σ = -1)
  have hsplit : ∑ σ : Perm α, (sign σ : ℤ) =
      ∑ σ ∈ evenPerms, (sign σ : ℤ) + ∑ σ ∈ oddPerms, (sign σ : ℤ) := by
    rw [← sum_filter_add_sum_filter_not univ (fun σ : Perm α => sign σ = 1)]
    congr 1
    apply sum_congr
    · ext σ
      simp only [mem_filter, mem_univ, true_and, oddPerms]
      constructor
      · intro h
        rcases Int.units_eq_one_or (sign σ) with hs | hs
        · exact absurd hs h
        · exact hs
      · intro h hcontra
        rw [hcontra] at h
        exact absurd h (by decide)
    · intro _ _; rfl
  rw [hsplit]
  have heven_sum : ∑ σ ∈ evenPerms, (sign σ : ℤ) = evenPerms.card := by
    trans ∑ _ ∈ evenPerms, (1 : ℤ)
    · apply sum_congr rfl
      intro σ hσ
      simp only [mem_filter, mem_univ, true_and, evenPerms] at hσ
      simp [hσ]
    · simp
  have hodd_sum : ∑ σ ∈ oddPerms, (sign σ : ℤ) = -(oddPerms.card : ℤ) := by
    trans ∑ _ ∈ oddPerms, (-1 : ℤ)
    · apply sum_congr rfl
      intro σ hσ
      simp only [mem_filter, mem_univ, true_and, oddPerms] at hσ
      simp [hσ]
    · simp
  rw [heven_sum, hodd_sum, hodd_card]
  ring

/-! ### Sign for permutations of arbitrary finite sets (Proposition prop.perm.sign.X)

The sign can be defined for permutations of any finite set X, not just [n].
Given a bijection φ : X → [n], we define sign_φ(σ) = sign(φ ∘ σ ∘ φ⁻¹).
This is independent of the choice of φ.
-/

/-- **Proposition (prop.perm.sign.X)(a)**
The sign of a permutation of a finite set is independent of the chosen bijection.

For any bijections φ₁, φ₂ : X → [n], we have sign_{φ₁}(σ) = sign_{φ₂}(σ). -/
theorem sign_conj_eq {β : Type*} [DecidableEq β] [Fintype β]
    (σ : Perm α) (e : α ≃ β) :
    sign ((e.symm.trans σ).trans e) = sign σ :=
  sign_symm_trans_trans σ e

/-- **Proposition (prop.perm.sign.X)(b)**
The identity permutation of any finite set has sign 1. -/
theorem sign_id_finiteSet : sign (1 : Perm α) = 1 := sign_one

/-- **Proposition (prop.perm.sign.X)(c)**
The sign is multiplicative for permutations of any finite set. -/
theorem sign_mul_finiteSet (σ τ : Perm α) :
    sign (σ * τ) = sign σ * sign τ := sign_mul σ τ

end Equiv.Perm
