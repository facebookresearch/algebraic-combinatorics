/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# Basic definitions, transpositions, cycles and involutions

This file formalizes the basic definitions of permutations, transpositions, cycles,
and involutions from the Algebraic Combinatorics textbook.

## Main definitions

* `Equiv.Perm`: The type of permutations of a set (from Mathlib)
* `Equiv.swap`: The transposition swapping two elements (from Mathlib)
* `cyc`: The k-cycle `cyc_{i₁, i₂, ..., iₖ}` that cyclically permutes elements (def.perm.cycs)
* `Equiv.Perm.IsCycle`: Predicate for a permutation being a cycle (from Mathlib)
* `simpleTransposition`: The simple transposition swapping `i` and `i+1`
* `IsInvolution`: Predicate for a permutation being an involution

## Main results

* `symmetricGroup_card`: The symmetric group has `n!` elements
* `symmetricGroup_conj_iso`: Bijections induce isomorphisms of symmetric groups
* `transposition_apply_left`: `t_{i,j}(i) = j` (def.perm.tij)
* `transposition_apply_right`: `t_{i,j}(j) = i` (def.perm.tij)
* `transposition_apply_of_ne_of_ne`: `t_{i,j}(x) = x` for `x ≠ i, j` (def.perm.tij)
* `transposition_symm`: Transpositions are symmetric: `t_{i,j} = t_{j,i}`
* `transposition_sq_eq_one`: Transpositions are involutions: `t_{i,j}² = id`
* `num_transpositions`: The number of transpositions in S_X is C(|X|, 2)
* `simpleTransposition_eq_transposition`: `s_i = t_{i,i+1}` (def.perm.si)
* `simpleTransposition_apply_self`: `s_i(i) = i+1` (def.perm.si)
* `simpleTransposition_apply_succ`: `s_i(i+1) = i` (def.perm.si)
* `simpleTransposition_apply_of_ne`: `s_i(k) = k` for `k ≠ i, i+1` (def.perm.si)
* `simpleTransposition_support`: support of `s_i` is `{i, i+1}` (def.perm.si)
* `simpleTransposition_isSwap`: `s_i` is a swap (def.perm.si)
* `simpleTransposition_isCycle`: `s_i` is a 2-cycle (def.perm.si)
* `simpleTransposition_sq_eq_one`: Simple transpositions satisfy `s_i² = id`
* `simpleTransposition_comm`: Simple transpositions commute when `|i-j| > 1`
* `simpleTransposition_braid`: The braid relation `s_i s_{i+1} s_i = s_{i+1} s_i s_{i+1}`
* `cyc_pair`: 2-cycles are exactly transpositions: `cyc [i, j] = swap i j`
* `cyc_rotate`: Cyclic rotation doesn't change the cycle
* `cyc_apply_getElem`: The cycle sends `l[j]` to `l[(j+1) % l.length]`
* `cycle_eq_transposition`: 2-cycles are exactly transpositions
* `num_kCycles_formula`: The number of k-cycles in `S_n` is `C(n,k) * (k-1)!`

## References

See `AlgebraicCombinatorics/tex/Permutations/Basics.tex` for the LaTeX source.

## Design note: simpleTransposition duplication

The `simpleTransposition` function is defined in this file (`AlgebraicCombinatorics.simpleTransposition`)
and also in `Inversions2.lean` (`Equiv.Perm.simpleTransposition`). Both definitions produce the same
permutation (proven by `Equiv.Perm.simpleTransposition_eq_canonical`).

**Which to use:**
- Use `AlgebraicCombinatorics.simpleTransposition` (this file) for basic properties of simple
  transpositions as swaps/cycles
- Use `Equiv.Perm.simpleTransposition` (Inversions2.lean) when working with reduced words,
  length functions, and Coxeter-style arguments

## Tags

permutation, symmetric group, transposition, cycle, involution
-/

open Equiv Function Finset

namespace AlgebraicCombinatorics

/-! ## Basic definitions (def.perm.perm)

This section formalizes Definition `def.perm.perm` from the textbook:

**(a)** A *permutation* of X means a bijection from X to X.
In Mathlib, this is `Equiv.Perm X := X ≃ X`.

**(b)** The set of all permutations of X is a group under composition, called the
*symmetric group* of X, denoted `S_X`. Its neutral element is `id_X`, and its size is `|X|!`.
In Mathlib, `Equiv.Perm X` has a `Group` instance automatically.

**(c)** We write `αβ` for composition `α ∘ β` when `α, β ∈ S_X`. This sends each `x ∈ X`
to `α(β(x))`. In Mathlib, `(α * β) x = α (β x)`.

**(d)** If `α ∈ S_X` and `i ∈ ℤ`, then `α^i` denotes the i-th power of α in the group S_X.
- `α^i = α ∘ α ∘ ⋯ ∘ α` (i times) if `i ≥ 0`
- `α^0 = id_X`
- `α^(-1)` is the inverse of α

-/

/-- A permutation of a type `X` is a bijection from `X` to itself. (def.perm.perm (a))

In Mathlib, this is `Equiv.Perm X := X ≃ X`, i.e., the type of equivalences from `X` to `X`. -/
abbrev Permutation (X : Type*) := Equiv.Perm X

/-- The symmetric group of a type `X` is the group of all permutations of `X`.
    (def.perm.perm (b))

    In Mathlib, this is `Equiv.Perm X` with its natural `Group` instance. -/
abbrev SymmetricGroup (X : Type*) := Equiv.Perm X

/-! ### The n-th symmetric group (def.perm.Sn-iven)

In the textbook, `[n]` denotes the set `{1, 2, ..., n}`, which is an n-element set
for n ≥ 0 and empty for n ≤ 0.

In Lean/Mathlib, we use `Fin n = {0, 1, ..., n-1}` instead, which is also an n-element
set. This is a standard convention difference (0-indexed vs 1-indexed), but the
symmetric groups are isomorphic since both are n-element sets.

The symmetric group `S_[n]` (denoted `S_n`) is the group of all permutations of `[n]`.
Its size is `n!` when n ≥ 0. -/

/-- The set `[n]` from the textbook is represented by `Fin n` in Lean.

In the textbook (def.perm.Sn-iven), `[n]` denotes `{1, 2, ..., n}`.
In Lean, `Fin n` represents `{0, 1, ..., n-1}`.

Both are n-element sets for n ≥ 0, so their symmetric groups are isomorphic.
We use `Fin n` as it is the standard representation in Mathlib. -/
abbrev bracketN (n : ℕ) := Fin n

/-- The n-th symmetric group `S_n` is the group of permutations of `[n]`.
    (def.perm.Sn-iven)

In the textbook, `S_n` is defined as `S_[n]`, the symmetric group of `[n] = {1, 2, ..., n}`.
In Lean, we represent this as `Equiv.Perm (Fin n)`, the group of permutations of
`Fin n = {0, 1, ..., n-1}`.

The size of `S_n` is `n!` (see `sn_card`). -/
abbrev Sn (n : ℕ) := Equiv.Perm (Fin n)

-- Verify that the symmetric group is indeed a group (def.perm.perm (b))
example {X : Type*} : Group (Equiv.Perm X) := inferInstance

/-- The symmetric group of a finite type has `|X|!` elements. (def.perm.perm (b)) -/
theorem symmetricGroup_card (X : Type*) [Fintype X] [DecidableEq X] :
    Fintype.card (Equiv.Perm X) = Nat.factorial (Fintype.card X) :=
  Fintype.card_perm

/-- The symmetric group `S_n` has `n!` elements. (def.perm.Sn-iven)

This is the key cardinality result: `|S_n| = n!` -/
theorem sn_card (n : ℕ) : Fintype.card (Sn n) = Nat.factorial n := by
  simp [Sn, symmetricGroup_card, Fintype.card_fin]

/-- `S_0` is trivial (has exactly one element, the identity). -/
theorem sn_zero_card : Fintype.card (Sn 0) = 1 := by
  native_decide

/-- `S_1` is trivial (has exactly one element, the identity). -/
theorem sn_one_card : Fintype.card (Sn 1) = 1 := by
  native_decide

/-- `S_2` has exactly 2 elements. -/
theorem sn_two_card : Fintype.card (Sn 2) = 2 := by
  native_decide

/-- `S_3` has exactly 6 elements. -/
theorem sn_three_card : Fintype.card (Sn 3) = 6 := by
  native_decide

/-- `[n]` has exactly `n` elements. -/
theorem bracketN_card (n : ℕ) : Fintype.card (bracketN n) = n :=
  Fintype.card_fin n

/-- `S_n` is a finite group. -/
instance sn_fintype (n : ℕ) : Fintype (Sn n) := inferInstance

/-- `S_n` has decidable equality. -/
instance sn_decidableEq (n : ℕ) : DecidableEq (Sn n) := inferInstance

/-! ### Composition notation (def.perm.perm (c))

In the textbook, `αβ` denotes the composition `α ∘ β`, which sends `x` to `α(β(x))`.
In Mathlib, this is the group multiplication `α * β`. -/

/-- The composition `α * β` sends `x` to `α(β(x))`. (def.perm.perm (c)) -/
theorem perm_mul_apply {X : Type*} (α β : Equiv.Perm X) (x : X) :
    (α * β) x = α (β x) := rfl

/-- Composition is associative: `(αβ)γ = α(βγ)`. -/
theorem perm_mul_assoc {X : Type*} (α β γ : Equiv.Perm X) :
    (α * β) * γ = α * (β * γ) := mul_assoc α β γ

/-- The identity permutation is the neutral element: `id * α = α`. -/
theorem perm_one_mul {X : Type*} (α : Equiv.Perm X) : 1 * α = α := one_mul α

/-- The identity permutation is the neutral element: `α * id = α`. -/
theorem perm_mul_one {X : Type*} (α : Equiv.Perm X) : α * 1 = α := mul_one α

/-! ### Powers of permutations (def.perm.perm (d))

The i-th power `α^i` is defined for any integer `i`. -/

/-- `α^0 = id`. (def.perm.perm (d)) -/
theorem perm_pow_zero {X : Type*} (α : Equiv.Perm X) : α ^ (0 : ℕ) = 1 := pow_zero α

/-- `α^0 = id` for integer exponents. (def.perm.perm (d)) -/
theorem perm_zpow_zero {X : Type*} (α : Equiv.Perm X) : α ^ (0 : ℤ) = 1 := zpow_zero α

/-- `α^1 = α`. -/
theorem perm_pow_one {X : Type*} (α : Equiv.Perm X) : α ^ (1 : ℕ) = α := pow_one α

/-- For `i ≥ 0`, `α^i = α ∘ α ∘ ⋯ ∘ α` (i times). (def.perm.perm (d)) -/
theorem perm_pow_succ {X : Type*} (α : Equiv.Perm X) (n : ℕ) :
    α ^ (n + 1) = α ^ n * α := pow_succ α n

/-- Alternative form: `α^(n+1) = α * α^n`. -/
theorem perm_pow_succ' {X : Type*} (α : Equiv.Perm X) (n : ℕ) :
    α ^ (n + 1) = α * α ^ n := pow_succ' α n

/-- `α^(-1)` is the inverse of `α`. (def.perm.perm (d)) -/
theorem perm_zpow_neg_one {X : Type*} (α : Equiv.Perm X) : α ^ (-1 : ℤ) = α⁻¹ := zpow_neg_one α

/-- The inverse satisfies `α * α⁻¹ = id`. -/
theorem perm_mul_inv {X : Type*} (α : Equiv.Perm X) : α * α⁻¹ = 1 := mul_inv_cancel α

/-- The inverse satisfies `α⁻¹ * α = id`. -/
theorem perm_inv_mul {X : Type*} (α : Equiv.Perm X) : α⁻¹ * α = 1 := inv_mul_cancel α

/-- Applying `α^n` to `x` gives the n-fold application of `α`. -/
theorem perm_pow_apply {X : Type*} (α : Equiv.Perm X) (n : ℕ) (x : X) :
    (α ^ n) x = (α^[n]) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply, ih]
    rw [Function.iterate_succ_apply', Function.Commute.iterate_self _ n x]

/-- For integer powers, `α^(-n)` applies the inverse n times. -/
theorem perm_zpow_neg {X : Type*} (α : Equiv.Perm X) (n : ℕ) :
    α ^ (-(n : ℤ)) = (α⁻¹) ^ n := zpow_neg α n

/-! ## Conjugation isomorphism (prop.perm.Sf)

If `f : X ≃ Y` is a bijection, then the map `σ ↦ f ∘ σ ∘ f⁻¹` is a group isomorphism
from `S_X` to `S_Y`. -/

/-- Given a bijection `f : X ≃ Y`, conjugation by `f` gives a group isomorphism
    from `Perm X` to `Perm Y`. (prop.perm.Sf)

    For each permutation `σ` of `X`, the map `f ∘ σ ∘ f⁻¹ : Y → Y` is a permutation of `Y`.
    Furthermore, the map `S_f : S_X → S_Y, σ ↦ f ∘ σ ∘ f⁻¹` is a group isomorphism. -/
def symmetricGroup_conj_iso {X Y : Type*} (f : X ≃ Y) : Equiv.Perm X ≃* Equiv.Perm Y :=
  f.permCongrHom

/-- The conjugation isomorphism sends `σ` to `f ∘ σ ∘ f⁻¹`. -/
theorem symmetricGroup_conj_iso_apply {X Y : Type*} (f : X ≃ Y) (σ : Equiv.Perm X) :
    symmetricGroup_conj_iso f σ = f.permCongr σ := rfl

/-- For each permutation `σ` of `X`, the map `f ∘ σ ∘ f⁻¹ : Y → Y` is a permutation of `Y`.
    This is the first part of prop.perm.Sf. -/
theorem symmetricGroup_conj_isPerm {X Y : Type*} (f : X ≃ Y) (σ : Equiv.Perm X) :
    ∃ (τ : Equiv.Perm Y), ∀ y : Y, τ y = f (σ (f.symm y)) := by
  use f.permCongr σ
  intro y
  simp [Equiv.permCongr_apply]

/-- The conjugation map explicitly: `S_f(σ)(y) = f(σ(f⁻¹(y)))`. -/
@[simp]
theorem symmetricGroup_conj_iso_apply_val {X Y : Type*} (f : X ≃ Y) (σ : Equiv.Perm X) (y : Y) :
    symmetricGroup_conj_iso f σ y = f (σ (f.symm y)) := by
  simp [symmetricGroup_conj_iso, Equiv.permCongrHom, Equiv.permCongr_apply]

/-- The conjugation isomorphism is bijective (part of being an isomorphism). -/
theorem symmetricGroup_conj_iso_bijective {X Y : Type*} (f : X ≃ Y) :
    Function.Bijective (symmetricGroup_conj_iso f) :=
  (symmetricGroup_conj_iso f).bijective

/-- The conjugation isomorphism is a group homomorphism (part of being an isomorphism). -/
theorem symmetricGroup_conj_iso_mul {X Y : Type*} (f : X ≃ Y) (σ τ : Equiv.Perm X) :
    symmetricGroup_conj_iso f (σ * τ) = symmetricGroup_conj_iso f σ * symmetricGroup_conj_iso f τ :=
  (symmetricGroup_conj_iso f).map_mul σ τ

/-- The conjugation isomorphism preserves identity. -/
theorem symmetricGroup_conj_iso_one {X Y : Type*} (f : X ≃ Y) :
    symmetricGroup_conj_iso f 1 = 1 :=
  (symmetricGroup_conj_iso f).map_one

/-- The inverse of the conjugation isomorphism is conjugation by `f⁻¹`. -/
theorem symmetricGroup_conj_iso_symm {X Y : Type*} (f : X ≃ Y) :
    (symmetricGroup_conj_iso f).symm = symmetricGroup_conj_iso f.symm := by
  ext σ y
  simp [symmetricGroup_conj_iso, Equiv.permCongrHom]

/-- Symmetric groups of bijective sets are isomorphic. (Conclusion of prop.perm.Sf) -/
theorem symmetricGroup_iso_of_equiv {X Y : Type*} (f : X ≃ Y) :
    Nonempty (Equiv.Perm X ≃* Equiv.Perm Y) :=
  ⟨symmetricGroup_conj_iso f⟩

/-- If `Y = X` in prop.perm.Sf, then `S_f` is conjugation by `f` in the group `S_X`.
    (Remark after prop.perm.Sf) -/
theorem symmetricGroup_conj_iso_self {X : Type*} (f : Equiv.Perm X) (σ : Equiv.Perm X) :
    symmetricGroup_conj_iso f σ = f * σ * f⁻¹ := by
  ext x
  simp [symmetricGroup_conj_iso, Equiv.permCongrHom]

/-! ## Permutation notations (def.perm.notations)

This section formalizes Definition `def.perm.notations` from the textbook, which introduces
three notations for representing permutations:

**(a)** A *two-line notation* of σ is a 2×n-array where the top row contains elements of [n]
in some order, and the bottom row contains their images under σ.

**(b)** The *one-line notation* (OLN) of σ is the n-tuple (σ(1), σ(2), ..., σ(n)).

**(c)** The *cycle digraph* of σ is a directed graph with vertices 1, 2, ..., n and
arcs i → σ(i) for all i ∈ [n].

In Lean, we formalize these as follows:
- Two-line notation: a function that maps each element to its image (essentially the permutation itself)
- One-line notation: a `Fin n → Fin n` function, or equivalently a `Vector (Fin n) n`
- Cycle digraph: a `SimpleGraph` with edges determined by the permutation
-/

/-! ### Two-line notation (def.perm.notations (a))

A two-line notation of σ ∈ S_n is a 2×n-array where:
- The top row contains the elements p₁, p₂, ..., pₙ of [n] in some order
- The bottom row contains σ(p₁), σ(p₂), ..., σ(pₙ)

The most common form uses pᵢ = i, giving the array:
  ⎛ 1      2      ...  n    ⎞
  ⎝ σ(1)  σ(2)  ...  σ(n)  ⎠

In Lean, a permutation σ : Equiv.Perm (Fin n) already encodes this information:
the "two-line notation" is essentially the graph of σ as a function. -/

/-- The two-line notation of a permutation σ ∈ S_n, represented as a list of pairs
    [(1, σ(1)), (2, σ(2)), ..., (n, σ(n))].

    This corresponds to the standard two-line notation:
      ⎛ 1      2      ...  n    ⎞
      ⎝ σ(1)  σ(2)  ...  σ(n)  ⎠

    (def.perm.notations (a)) -/
def twoLineNotation {n : ℕ} (σ : Sn n) : List (Fin n × Fin n) :=
  (List.finRange n).map (fun i => (i, σ i))

/-- The two-line notation has length n. -/
theorem twoLineNotation_length {n : ℕ} (σ : Sn n) :
    (twoLineNotation σ).length = n := by
  simp [twoLineNotation]

/-- The i-th entry of the two-line notation is (i, σ(i)). -/
theorem twoLineNotation_getElem {n : ℕ} (σ : Sn n) (i : ℕ) (hi : i < n) :
    (twoLineNotation σ)[i]'(by simp [twoLineNotation]; omega) = (⟨i, hi⟩, σ ⟨i, hi⟩) := by
  simp only [twoLineNotation, List.getElem_map, List.getElem_finRange]
  simp only [Fin.cast_mk]

/-- The first components of the two-line notation are exactly 0, 1, ..., n-1. -/
theorem twoLineNotation_fst {n : ℕ} (σ : Sn n) :
    (twoLineNotation σ).map Prod.fst = List.finRange n := by
  simp only [twoLineNotation, List.map_map, Function.comp_def]
  simp only [List.map_id']

/-- The second components of the two-line notation are σ(0), σ(1), ..., σ(n-1). -/
theorem twoLineNotation_snd {n : ℕ} (σ : Sn n) :
    (twoLineNotation σ).map Prod.snd = (List.finRange n).map σ := by
  simp only [twoLineNotation, List.map_map, Function.comp_def]

/-- Two permutations are equal iff their two-line notations are equal. -/
theorem eq_iff_twoLineNotation_eq {n : ℕ} (σ τ : Sn n) :
    σ = τ ↔ twoLineNotation σ = twoLineNotation τ := by
  constructor
  · intro h; rw [h]
  · intro h
    ext i : 1
    have h1 := twoLineNotation_getElem σ i.val i.isLt
    have h2 := twoLineNotation_getElem τ i.val i.isLt
    have hi1 : i.val < (twoLineNotation σ).length := by simp [twoLineNotation]
    have hi2 : i.val < (twoLineNotation τ).length := by simp [twoLineNotation]
    have heq : (twoLineNotation σ)[i.val]'hi1 = (twoLineNotation τ)[i.val]'hi2 := by
      simp only [h]
    rw [h1, h2] at heq
    exact Prod.mk.inj heq |>.2

/-! ### One-line notation (def.perm.notations (b))

The one-line notation (OLN) of σ ∈ S_n is the n-tuple (σ(1), σ(2), ..., σ(n)).

In Lean, a permutation σ : Sn n = Equiv.Perm (Fin n) is already essentially its OLN,
since we can evaluate σ at any index. We provide explicit conversions. -/

/-- The one-line notation of a permutation σ ∈ S_n, as a list [σ(0), σ(1), ..., σ(n-1)].

    Note: We use 0-indexing (Fin n starts at 0), so this is [σ(0), σ(1), ..., σ(n-1)]
    rather than [σ(1), σ(2), ..., σ(n)] as in the textbook.

    (def.perm.notations (b)) -/
def oneLineNotation {n : ℕ} (σ : Sn n) : List (Fin n) :=
  (List.finRange n).map σ

/-- The one-line notation has length n. -/
theorem oneLineNotation_length {n : ℕ} (σ : Sn n) :
    (oneLineNotation σ).length = n := by
  simp [oneLineNotation]

/-- The i-th entry of the one-line notation is σ(i). -/
theorem oneLineNotation_getElem {n : ℕ} (σ : Sn n) (i : ℕ) (hi : i < n) :
    (oneLineNotation σ)[i]'(by simp [oneLineNotation]; omega) = σ ⟨i, hi⟩ := by
  simp only [oneLineNotation, List.getElem_map, List.getElem_finRange]
  simp only [Fin.cast_mk]

/-- The one-line notation contains no duplicates. -/
theorem oneLineNotation_nodup {n : ℕ} (σ : Sn n) :
    (oneLineNotation σ).Nodup := by
  simp only [oneLineNotation]
  apply List.Nodup.map σ.injective
  exact List.nodup_finRange n

/-- Two permutations are equal iff their one-line notations are equal. -/
theorem eq_iff_oneLineNotation_eq {n : ℕ} (σ τ : Sn n) :
    σ = τ ↔ oneLineNotation σ = oneLineNotation τ := by
  constructor
  · intro h; rw [h]
  · intro h
    ext i : 1
    have h1 := oneLineNotation_getElem σ i.val i.isLt
    have h2 := oneLineNotation_getElem τ i.val i.isLt
    have hi1 : i.val < (oneLineNotation σ).length := by simp [oneLineNotation]
    have hi2 : i.val < (oneLineNotation τ).length := by simp [oneLineNotation]
    have heq : (oneLineNotation σ)[i.val]'hi1 = (oneLineNotation τ)[i.val]'hi2 := by
      simp only [h]
    rw [h1, h2] at heq
    exact heq

/-- Convert a list to a permutation, if it's a valid one-line notation.
    Returns the permutation represented by the list. -/
noncomputable def oneLineNotationToPerm {n : ℕ} (l : List (Fin n)) (hl : l.length = n) (hnodup : l.Nodup) :
    Sn n :=
  Equiv.ofBijective (fun i => l[i.val]'(by omega)) ⟨by
    intro i j hij
    have hi' : i.val < l.length := by omega
    have hj' : j.val < l.length := by omega
    have hinj := List.Nodup.getElem_inj_iff hnodup (hi := hi') (hj := hj')
    simp only [Fin.ext_iff]
    exact hinj.mp hij, by
    intro y
    have hy : y ∈ l := by
      have hcard : l.toFinset.card = n := by
        rw [List.toFinset_card_of_nodup hnodup, hl]
      have hfull : l.toFinset = Finset.univ := by
        apply Finset.eq_univ_of_card
        simp [hcard]
      rw [← List.mem_toFinset, hfull]
      exact Finset.mem_univ y
    obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hy
    exact ⟨⟨i, by omega⟩, hiy⟩⟩

/-- Round-trip: converting a permutation to OLN and back gives the original permutation. -/
theorem oneLineNotationToPerm_oneLineNotation {n : ℕ} (σ : Sn n) :
    oneLineNotationToPerm (oneLineNotation σ) (oneLineNotation_length σ)
      (oneLineNotation_nodup σ) = σ := by
  ext i
  simp only [oneLineNotationToPerm, Equiv.ofBijective_apply, oneLineNotation,
             List.getElem_map, List.getElem_finRange, Fin.cast_mk]

/-! ### Cycle digraph (def.perm.notations (c))

The cycle digraph of σ ∈ S_n is a directed graph with:
- Vertices: 1, 2, ..., n (or 0, 1, ..., n-1 in 0-indexed form)
- Arcs: i → σ(i) for all i ∈ [n]

In Lean, we represent this as a `SimpleGraph` where there's an edge between i and j
iff σ(i) = j (and i ≠ j to avoid self-loops in the SimpleGraph sense).

Note: The cycle digraph is naturally a directed graph, but for simplicity we can also
consider the underlying undirected graph structure. -/

/-- The cycle digraph of a permutation σ, as an undirected simple graph.

    There is an edge between i and j iff σ(i) = j or σ(j) = i (and i ≠ j).
    This captures the "orbit structure" of the permutation.

    (def.perm.notations (c)) -/
def cycleDigraph {n : ℕ} (σ : Sn n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (σ i = j ∨ σ j = i)
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩⟩
  loopless := ⟨fun _ ⟨hn, _⟩ => hn rfl⟩

/-- Two vertices are adjacent in the cycle digraph iff one maps to the other under σ. -/
theorem cycleDigraph_adj_iff {n : ℕ} (σ : Sn n) (i j : Fin n) :
    (cycleDigraph σ).Adj i j ↔ i ≠ j ∧ (σ i = j ∨ σ j = i) := Iff.rfl

/-- If σ(i) = j and i ≠ j, then i and j are adjacent in the cycle digraph. -/
theorem cycleDigraph_adj_of_apply {n : ℕ} (σ : Sn n) {i j : Fin n}
    (h : σ i = j) (hne : i ≠ j) : (cycleDigraph σ).Adj i j :=
  ⟨hne, Or.inl h⟩

/-- Helper: (σ ^ k) (σ i) = σ ((σ ^ k) i) -/
private lemma zpow_apply_sigma {n : ℕ} (σ : Sn n) (k : ℤ) (i : Fin n) :
    (σ ^ k) (σ i) = σ ((σ ^ k) i) :=
  Equiv.Perm.zpow_apply_comm σ k 1 (x := i)

/-- Helper: (σ ^ k) (σ⁻¹ i) = σ⁻¹ ((σ ^ k) i) -/
private lemma zpow_apply_sigma_inv {n : ℕ} (σ : Sn n) (k : ℤ) (i : Fin n) :
    (σ ^ k) (σ⁻¹ i) = σ⁻¹ ((σ ^ k) i) := by
  simp only [← zpow_neg_one]
  exact Equiv.Perm.zpow_apply_comm σ k (-1) (x := i)

/-- The connected components of the cycle digraph correspond to the orbits of σ. -/
theorem cycleDigraph_connected_iff {n : ℕ} (σ : Sn n) (i j : Fin n) :
    (cycleDigraph σ).Reachable i j ↔ ∃ k : ℤ, (σ ^ k) i = j := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hadj ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨_, h | h⟩ := hadj
      · refine ⟨k + 1, ?_⟩
        rw [zpow_add_one, Equiv.Perm.mul_apply, zpow_apply_sigma, hk, h]
      · refine ⟨k - 1, ?_⟩
        rw [zpow_sub_one, Equiv.Perm.mul_apply, zpow_apply_sigma_inv, hk]
        simp [← h]
  · intro ⟨k, hk⟩
    induction k using Int.induction_on generalizing j with
    | zero =>
      simp only [zpow_zero, Equiv.Perm.coe_one, id_eq] at hk
      subst hk
      exact Relation.ReflTransGen.refl
    | succ n ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply, zpow_apply_sigma] at hk
      have h1 : Relation.ReflTransGen (cycleDigraph σ).Adj i ((σ ^ n) i) := ih ((σ ^ n) i) rfl
      by_cases heq : (σ ^ n) i = j
      · exact ih j heq
      · have hadj : (cycleDigraph σ).Adj ((σ ^ n) i) j := ⟨heq, Or.inl hk⟩
        exact h1.trans (Relation.ReflTransGen.single hadj)
    | pred n ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply, zpow_apply_sigma_inv] at hk
      have h1 : Relation.ReflTransGen (cycleDigraph σ).Adj i ((σ ^ (-(n : ℤ))) i) :=
        ih ((σ ^ (-(n : ℤ))) i) rfl
      by_cases heq : (σ ^ (-(n : ℤ))) i = j
      · exact ih j heq
      · have hadj : (cycleDigraph σ).Adj ((σ ^ (-(n : ℤ))) i) j := by
          refine ⟨heq, Or.inr ?_⟩
          simp [← hk]
        exact h1.trans (Relation.ReflTransGen.single hadj)

/-- The identity permutation has a cycle digraph with no edges. -/
theorem cycleDigraph_one {n : ℕ} : cycleDigraph (1 : Sn n) = ⊥ := by
  ext i j
  simp only [cycleDigraph_adj_iff, Equiv.Perm.coe_one, id_eq, SimpleGraph.bot_adj]
  constructor
  · intro ⟨hne, h⟩
    rcases h with rfl | rfl <;> exact hne rfl
  · intro h
    exact h.elim

/-- A transposition creates an edge between the swapped elements. -/
theorem cycleDigraph_swap_adj_iff {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : Fin n) :
    (cycleDigraph (Equiv.swap i j)).Adj a b ↔
      (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  simp only [cycleDigraph_adj_iff, Equiv.swap_apply_def]
  constructor
  · intro ⟨hne, h⟩
    rcases h with h | h
    · split_ifs at h with h1 h2
      · left; exact ⟨h1, h.symm⟩
      · right; exact ⟨h2, h.symm⟩
      · exact (hne h).elim
    · split_ifs at h with h1 h2
      · right; exact ⟨h.symm, h1⟩
      · left; exact ⟨h.symm, h2⟩
      · exact (hne h.symm).elim
  · intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
      exact ⟨hij, Or.inl (Equiv.swap_apply_left i j)⟩
    · rw [ha, hb]
      exact ⟨hij.symm, Or.inl (Equiv.swap_apply_right i j)⟩

/-! ## Transpositions (def.perm.tij)

A transposition `t_{i,j}` swaps `i` and `j` and fixes all other elements.

From the textbook (def.perm.tij):
> Let `i` and `j` be two distinct elements of a set `X`. Then, the transposition `t_{i,j}` is
> the permutation of `X` that sends `i` to `j`, sends `j` to `i`, and leaves all other
> elements of `X` unchanged.

In Mathlib, this is `Equiv.swap i j`. -/

/-- The transposition swapping `i` and `j`. In Mathlib, this is `Equiv.swap i j`.
    (def.perm.tij)

    A transposition `t_{i,j}` is the permutation of `X` that:
    - sends `i` to `j` (see `transposition_apply_left`)
    - sends `j` to `i` (see `transposition_apply_right`)
    - leaves all other elements unchanged (see `transposition_apply_of_ne_of_ne`) -/
abbrev transposition {X : Type*} [DecidableEq X] (i j : X) : Equiv.Perm X := Equiv.swap i j

/-- The transposition `t_{i,j}` sends `i` to `j`. (def.perm.tij) -/
@[simp]
theorem transposition_apply_left {X : Type*} [DecidableEq X] (i j : X) :
    transposition i j i = j :=
  Equiv.swap_apply_left i j

/-- The transposition `t_{i,j}` sends `j` to `i`. (def.perm.tij) -/
@[simp]
theorem transposition_apply_right {X : Type*} [DecidableEq X] (i j : X) :
    transposition i j j = i :=
  Equiv.swap_apply_right i j

/-- The transposition `t_{i,j}` leaves all other elements unchanged. (def.perm.tij) -/
theorem transposition_apply_of_ne_of_ne {X : Type*} [DecidableEq X] {i j x : X}
    (hi : x ≠ i) (hj : x ≠ j) : transposition i j x = x :=
  Equiv.swap_apply_of_ne_of_ne hi hj

/-- Transpositions are symmetric: `t_{i,j} = t_{j,i}`. -/
theorem transposition_symm {X : Type*} [DecidableEq X] (i j : X) :
    transposition i j = transposition j i :=
  Equiv.swap_comm i j

/-- A transposition is its own inverse: `t_{i,j}⁻¹ = t_{i,j}`. -/
theorem transposition_inv {X : Type*} [DecidableEq X] (i j : X) :
    (transposition i j)⁻¹ = transposition i j :=
  Equiv.symm_swap i j

/-- A transposition squared is the identity: `t_{i,j}² = id`. -/
theorem transposition_sq_eq_one {X : Type*} [DecidableEq X] (i j : X) :
    transposition i j * transposition i j = 1 := by
  ext x
  simp [transposition]

/-- Two swaps are equal iff their Sym2 images are equal. -/
private lemma swap_eq_swap_iff {X : Type*} [DecidableEq X] {x y a b : X} (hxy : x ≠ y) (_hab : a ≠ b) :
    Equiv.swap x y = Equiv.swap a b ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  constructor
  · intro h
    have hx : (Equiv.swap x y) x = (Equiv.swap a b) x := congrFun (congrArg DFunLike.coe h) x
    have hy : (Equiv.swap x y) y = (Equiv.swap a b) y := congrFun (congrArg DFunLike.coe h) y
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at hx hy
    by_cases hxa : x = a
    · subst hxa
      left
      exact ⟨rfl, by simp only [Equiv.swap_apply_left] at hx; exact hx⟩
    · have hxb : x = b := by
        have hswap : Equiv.swap a b x = y := by rw [← h]; simp [Equiv.swap_apply_left]
        rw [Equiv.swap_apply_def] at hswap
        split_ifs at hswap with h1
        · exact h1
        · exact (hxy hswap).elim
      subst hxb
      right
      exact ⟨rfl, by simp only [Equiv.swap_apply_right] at hx; exact hx⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact (Equiv.swap_comm y x).symm

/-- Two swaps are equal iff their Sym2 representations are equal. -/
private lemma swap_eq_iff_sym2_eq {X : Type*} [DecidableEq X] {x₁ y₁ x₂ y₂ : X}
    (h₁ : x₁ ≠ y₁) (h₂ : x₂ ≠ y₂) :
    Equiv.swap x₁ y₁ = Equiv.swap x₂ y₂ ↔ s(x₁, y₁) = s(x₂, y₂) := by
  rw [Sym2.eq_iff, swap_eq_swap_iff h₁ h₂]

/-- Extract a canonical pair from a swap. -/
private noncomputable def swapToPair {X : Type*} [DecidableEq X] (σ : Equiv.Perm X) (hσ : σ.IsSwap) : X × X :=
  let x := Classical.choose hσ
  let hx := Classical.choose_spec hσ
  let y := Classical.choose hx
  (x, y)

private lemma swapToPair_spec {X : Type*} [DecidableEq X] (σ : Equiv.Perm X) (hσ : σ.IsSwap) :
    (swapToPair σ hσ).1 ≠ (swapToPair σ hσ).2 ∧ σ = Equiv.swap (swapToPair σ hσ).1 (swapToPair σ hσ).2 := by
  unfold swapToPair
  simp only
  exact Classical.choose_spec (Classical.choose_spec hσ)

/-- The number of transpositions (2-cycles) in S_X is C(|X|, 2).
    This follows from the fact that each 2-element subset {i,j} of X gives rise to
    exactly one transposition t_{i,j}. (Example after def.perm.cycs in source) -/
theorem num_transpositions (X : Type*) [DecidableEq X] [Fintype X] :
    ∃ (S : Finset (Equiv.Perm X)),
      (∀ σ ∈ S, σ.IsSwap) ∧
      (∀ σ : Equiv.Perm X, σ.IsSwap → σ ∈ S) ∧
      S.card = Nat.choose (Fintype.card X) 2 := by
  -- The set of all swaps (using support = 2 as decidable characterization)
  let S := Finset.univ.filter (fun σ : Equiv.Perm X => σ.support.card = 2)
  use S
  constructor
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    exact Equiv.Perm.card_support_eq_two.mp hσ.2
  constructor
  · intro σ hσ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ σ, Equiv.Perm.card_support_eq_two.mpr hσ⟩
  · -- We need to show S.card = Nat.choose (Fintype.card X) 2
    -- This follows from a bijection with non-diagonal elements of Sym2 X
    let T := Finset.univ.filter (fun z : Sym2 X => ¬z.IsDiag)
    have hT : T.card = Nat.choose (Fintype.card X) 2 := by
      have h := @Sym2.card_subtype_not_diag X _ _
      simp only [Fintype.card_subtype] at h
      exact h
    rw [← hT]
    show (Finset.univ.filter (fun σ : Equiv.Perm X => σ.support.card = 2)).card = T.card
    -- Define the bijection: σ ↦ Sym2.mk (swapToPair σ)
    apply Finset.card_bij (fun σ hσ =>
      let h := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ).2
      let p := swapToPair σ h
      Sym2.mk p.1 p.2)
    -- hi : i maps S to T
    · intro σ hσ
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ _
      · let h := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ).2
        rw [Sym2.mk_isDiag_iff]
        exact (swapToPair_spec σ h).1
    -- i_inj : i is injective
    · intro σ₁ hσ₁ σ₂ hσ₂ heq
      have h₁ : σ₁.IsSwap := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ₁).2
      have h₂ : σ₂.IsSwap := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσ₂).2
      have hp₁ := swapToPair_spec σ₁ h₁
      have hp₂ := swapToPair_spec σ₂ h₂
      have hsym : Sym2.mk (swapToPair σ₁ h₁).1 (swapToPair σ₁ h₁).2 =
          Sym2.mk (swapToPair σ₂ h₂).1 (swapToPair σ₂ h₂).2 := heq
      have hswap : Equiv.swap (swapToPair σ₁ h₁).1 (swapToPair σ₁ h₁).2 =
                   Equiv.swap (swapToPair σ₂ h₂).1 (swapToPair σ₂ h₂).2 :=
        (swap_eq_iff_sym2_eq hp₁.1 hp₂.1).mpr hsym
      calc σ₁ = Equiv.swap (swapToPair σ₁ h₁).1 (swapToPair σ₁ h₁).2 := hp₁.2
           _ = Equiv.swap (swapToPair σ₂ h₂).1 (swapToPair σ₂ h₂).2 := hswap
           _ = σ₂ := hp₂.2.symm
    -- i_surj : i is surjective
    · intro z hz
      rw [Finset.mem_filter] at hz
      have hnd : ¬z.IsDiag := hz.2
      let p := z.out
      have hp : z = Sym2.mk p.1 p.2 := z.out_eq.symm
      have hne : p.1 ≠ p.2 := by
        intro h
        apply hnd
        rw [hp, Sym2.mk_isDiag_iff]
        exact h
      let σ := Equiv.swap p.1 p.2
      have hσS : σ ∈ S := by
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ _
        · rw [Equiv.Perm.card_support_eq_two]
          exact ⟨p.1, p.2, hne, rfl⟩
      use σ, hσS
      have h : σ.IsSwap := Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσS).2
      have hq := swapToPair_spec σ h
      have heq : Equiv.swap (swapToPair σ h).1 (swapToPair σ h).2 = Equiv.swap p.1 p.2 := hq.2.symm
      have hsym : Sym2.mk (swapToPair σ h).1 (swapToPair σ h).2 = Sym2.mk p.1 p.2 :=
        (swap_eq_iff_sym2_eq hq.1 hne).mp heq
      show Sym2.mk (swapToPair σ (Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσS).2)).1
        (swapToPair σ (Equiv.Perm.card_support_eq_two.mp (Finset.mem_filter.mp hσS).2)).2 = z
      rw [hp]
      exact hsym

/-! ## Simple transpositions (def.perm.si)

The simple transposition `s_i` swaps `i` and `i+1`. -/

/-- The simple transposition `s_i` swaps `i` and `i+1` in `Fin n`.
    Here `i : Fin (n - 1)` ensures `i+1 < n`.
    (def.perm.si)
    
    **This is the canonical definition** for simple transpositions in the codebase.
    
    **Equivalent definition in Inversions2.lean:**
    `Equiv.Perm.simpleTransposition` in `Inversions2.lean` defines the same permutation
    using a slightly different construction (with `castSucc`/`succ`). The equivalence is
    proven by `Equiv.Perm.simpleTransposition_eq_canonical`.
    
    See the equivalence lemmas `simpleTransposition_eq_swap_*` below for other formulations. -/
def simpleTransposition {n : ℕ} (i : Fin (n - 1)) : Sn n :=
  Equiv.swap ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩
             ⟨i.val + 1, by omega⟩

/-- Notation for simple transposition. -/
scoped notation "s[" i "]" => simpleTransposition i

/-- Simple transposition `s_i` equals the transposition `t_{i,i+1}`. (def.perm.si) -/
theorem simpleTransposition_eq_transposition {n : ℕ} (i : Fin (n - 1)) :
    simpleTransposition i = transposition
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩
      ⟨i.val + 1, by omega⟩ := rfl

/-- Simple transposition `s_i` sends `i` to `i+1`. (def.perm.si) -/
@[simp]
theorem simpleTransposition_apply_self {n : ℕ} (i : Fin (n - 1)) :
    simpleTransposition i ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩ = ⟨i.val + 1, by omega⟩ := by
  simp [simpleTransposition]

/-- Simple transposition `s_i` sends `i+1` to `i`. (def.perm.si) -/
@[simp]
theorem simpleTransposition_apply_succ {n : ℕ} (i : Fin (n - 1)) :
    simpleTransposition i ⟨i.val + 1, by omega⟩ = ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩ := by
  simp [simpleTransposition]

/-- Simple transposition `s_i` fixes any `k ≠ i, i+1`. (def.perm.si) -/
theorem simpleTransposition_apply_of_ne {n : ℕ} (i : Fin (n - 1)) (k : Fin n)
    (hi : k.val ≠ i.val) (hi1 : k.val ≠ i.val + 1) :
    simpleTransposition i k = k := by
  simp only [simpleTransposition]
  rw [Equiv.swap_apply_of_ne_of_ne]
  · intro h; rw [Fin.ext_iff] at h; exact hi h
  · intro h; rw [Fin.ext_iff] at h; exact hi1 h

/-- The support of a simple transposition is exactly {i, i+1}. (def.perm.si) -/
theorem simpleTransposition_support {n : ℕ} (i : Fin (n - 1)) :
    (simpleTransposition i).support = {⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩,
                                        ⟨i.val + 1, by omega⟩} := by
  simp only [simpleTransposition]
  rw [Equiv.Perm.support_swap]
  intro h
  rw [Fin.ext_iff] at h
  simp at h

/-- Simple transpositions are swaps (i.e., 2-cycles). (def.perm.si) -/
theorem simpleTransposition_isSwap {n : ℕ} (i : Fin (n - 1)) :
    (simpleTransposition i).IsSwap := by
  use ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩
  use ⟨i.val + 1, by omega⟩
  constructor
  · intro h; rw [Fin.ext_iff] at h; simp at h
  · rfl

/-- Simple transpositions are cycles (2-cycles). (def.perm.si) -/
theorem simpleTransposition_isCycle {n : ℕ} (i : Fin (n - 1)) :
    (simpleTransposition i).IsCycle := by
  apply Equiv.Perm.IsSwap.isCycle
  exact simpleTransposition_isSwap i

/-- The support of a simple transposition has cardinality 2. (def.perm.si) -/
theorem simpleTransposition_support_card {n : ℕ} (i : Fin (n - 1)) :
    (simpleTransposition i).support.card = 2 := by
  rw [simpleTransposition_support]
  rw [Finset.card_pair]
  intro h
  rw [Fin.ext_iff] at h
  simp at h

/-- Simple transposition is not the identity (for n ≥ 2). (def.perm.si) -/
theorem simpleTransposition_ne_one {n : ℕ} (i : Fin (n - 1)) :
    simpleTransposition i ≠ 1 := by
  intro h
  have := simpleTransposition_support_card i
  rw [h] at this
  simp at this

/-! ## Properties of simple transpositions (prop.perm.si.rules) -/

/-- Simple transpositions are involutions: `s_i² = id`. (prop.perm.si.rules (a)) -/
theorem simpleTransposition_sq_eq_one {n : ℕ} (i : Fin (n - 1)) :
    s[i] * s[i] = 1 := by
  simp only [simpleTransposition]
  ext x
  simp

/-- Simple transpositions are self-inverse: `s_i⁻¹ = s_i`. (prop.perm.si.rules (a)) -/
theorem simpleTransposition_inv {n : ℕ} (i : Fin (n - 1)) :
    s[i]⁻¹ = s[i] := by
  simp [simpleTransposition]

/-- Simple transpositions commute when `|i - j| > 1`. (prop.perm.si.rules (b)) -/
theorem simpleTransposition_comm {n : ℕ} (i j : Fin (n - 1))
    (h : (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i) :
    s[i] * s[j] = s[j] * s[i] := by
  have hi_lt : i.val < n - 1 := i.isLt
  have hj_lt : j.val < n - 1 := j.isLt
  -- Key fact: when |i - j| > 1, the pairs {i, i+1} and {j, j+1} are disjoint
  have hdisj : Equiv.Perm.Disjoint s[i] s[j] := by
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    intro x
    simp only [simpleTransposition]
    by_cases hx1 : x.val = i.val
    · right
      rw [Equiv.swap_apply_of_ne_of_ne] <;>
      · intro heq
        rw [Fin.ext_iff] at heq
        simp at heq
        rcases h with h | h <;> omega
    · by_cases hx2 : x.val = i.val + 1
      · right
        rw [Equiv.swap_apply_of_ne_of_ne] <;>
        · intro heq
          rw [Fin.ext_iff] at heq
          simp at heq
          rcases h with h | h <;> omega
      · left
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro heq
          rw [Fin.ext_iff] at heq
          simp at heq
          exact hx1 heq
        · intro heq
          rw [Fin.ext_iff] at heq
          simp at heq
          exact hx2 heq
  exact hdisj.commute.eq

/-- The braid relation: `s_i s_{i+1} s_i = s_{i+1} s_i s_{i+1}`. (prop.perm.si.rules (c)) -/
theorem simpleTransposition_braid {n : ℕ} (i : Fin (n - 2)) :
    let i' : Fin (n - 1) := ⟨i.val, by omega⟩
    let i1 : Fin (n - 1) := ⟨i.val + 1, by omega⟩
    s[i'] * s[i1] * s[i'] = s[i1] * s[i'] * s[i1] := by
  ext x
  simp only [simpleTransposition, Perm.mul_apply]
  -- Define the three key elements involved in the swaps
  set a : Fin n := ⟨i.val, by omega⟩ with ha
  set b : Fin n := ⟨i.val + 1, by omega⟩ with hb
  set c : Fin n := ⟨i.val + 2, by omega⟩ with hc
  -- Establish that a, b, c are all distinct
  have hab : a ≠ b := by simp [ha, hb, Fin.ext_iff]
  have hac : a ≠ c := by simp [ha, hc, Fin.ext_iff]
  have hbc : b ≠ c := by simp [hb, hc, Fin.ext_iff]
  have hca : c ≠ a := hac.symm
  have hcb : c ≠ b := hbc.symm
  -- Case analysis on x: either x ∈ {a, b, c} or x is fixed by both sides
  rcases Decidable.em (x = a) with rfl | hxa
  · -- x = a: both sides map a ↦ c
    rw [swap_apply_left, swap_apply_left, swap_apply_of_ne_of_ne hca hcb]
    rw [swap_apply_of_ne_of_ne hab hac, swap_apply_left, swap_apply_left]
  · rcases Decidable.em (x = b) with rfl | hxb
    · -- x = b: both sides fix b
      rw [swap_apply_right, swap_apply_of_ne_of_ne hab hac, swap_apply_left]
      rw [swap_apply_left, swap_apply_of_ne_of_ne hca hcb, swap_apply_right]
    · rcases Decidable.em (x = c) with rfl | hxc
      · -- x = c: both sides map c ↦ a
        simp only [swap_apply_of_ne_of_ne hca hcb, swap_apply_right,
                   swap_apply_of_ne_of_ne hab hac]
      · -- x ∉ {a, b, c}: both sides fix x
        simp only [swap_apply_of_ne_of_ne hxa hxb, swap_apply_of_ne_of_ne hxb hxc]

/-! ### Equivalence lemmas for simpleTransposition

The `simpleTransposition` function is the **canonical definition** for the simple transposition
`s_i` that swaps `i` and `i+1` in `Fin n`. Other files may define local versions with slightly
different signatures. These lemmas establish the equivalence between formulations.

**Alternative formulations in the codebase:**
1. `Equiv.Perm.simpleTransposition` in `Inversions2.lean` - uses `castSucc`/`succ` pattern
2. `simpleTransposition` in `SymmetricFunctions/Definitions.lean` - uses `Nat.lt_of_lt_pred`
3. `simpleTransposition` in `SchurBasics.lean` - takes `Fin N` with explicit proof `hk : k.val + 1 < N`

All these definitions compute the same permutation: `Equiv.swap k (k+1)`.
-/

/-- The canonical `simpleTransposition` equals `Equiv.swap` on the appropriate `Fin` elements.
    This is the fundamental characterization used to prove equivalence with other formulations. -/
theorem simpleTransposition_eq_swap {n : ℕ} (i : Fin (n - 1)) :
    simpleTransposition i = Equiv.swap
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1)⟩
      ⟨i.val + 1, by omega⟩ := rfl

/-- Alternative characterization: `simpleTransposition` using `castSucc` and `succ`.
    This matches the formulation in `Inversions2.lean`. -/
theorem simpleTransposition_eq_swap_castSucc_succ {n : ℕ} (i : Fin (n - 1)) (hn : n > 0) :
    simpleTransposition i = Equiv.swap
      (Fin.castLE (by omega) i.castSucc)
      (Fin.castLE (by omega) i.succ) := by
  simp only [simpleTransposition, Fin.castSucc, Fin.succ, Fin.castLE, Fin.castAdd]

/-- Alternative characterization: when given `k : Fin N` and a proof `hk : k.val + 1 < N`,
    this equals `Equiv.swap k ⟨k.val + 1, hk⟩`.
    This matches the formulation in `SchurBasics.lean`. -/
theorem simpleTransposition_eq_swap_explicit {N : ℕ} (k : Fin N) (hk : k.val + 1 < N) :
    let i : Fin (N - 1) := ⟨k.val, by omega⟩
    simpleTransposition i = Equiv.swap k ⟨k.val + 1, hk⟩ := by
  simp [simpleTransposition]

/-- Conversion from `Fin (N - 1)` index to explicit proof form.
    Given `i : Fin (N - 1)`, we can express `simpleTransposition i` as a swap
    with explicit bounds proofs. This matches the formulation in `Definitions.lean`. -/
theorem simpleTransposition_eq_swap_with_proofs {N : ℕ} (i : Fin (N - 1)) :
    simpleTransposition i = Equiv.swap
      ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩
      ⟨i.val + 1, Nat.lt_pred_iff.mp i.isLt⟩ := by
  simp [simpleTransposition]


/-! ## Cycles (def.perm.cycs)

A k-cycle is a permutation that cyclically permutes k elements and fixes all others.

The textbook defines `cyc_{i₁, i₂, ..., iₖ}` as the permutation that sends
- `i₁ ↦ i₂`
- `i₂ ↦ i₃`
- ...
- `iₖ₋₁ ↦ iₖ`
- `iₖ ↦ i₁`
and fixes all other elements.

In Mathlib, this is `List.formPerm`. The predicate `Equiv.Perm.IsCycle` captures
when a permutation is a cycle. -/

/-- The k-cycle `cyc_{i₁, i₂, ..., iₖ}` is the permutation that sends
    `i₁ ↦ i₂ ↦ i₃ ↦ ... ↦ iₖ ↦ i₁` and fixes all other elements.
    (def.perm.cycs)
    
    This is the constructive definition from the textbook. In Mathlib,
    this is `List.formPerm`. -/
def cyc {X : Type*} [DecidableEq X] (l : List X) : Equiv.Perm X := l.formPerm

/-- The cycle `cyc [i, j]` equals the transposition `swap i j`.
    This shows that 2-cycles are exactly transpositions. -/
theorem cyc_pair {X : Type*} [DecidableEq X] (i j : X) : cyc [i, j] = Equiv.swap i j :=
  List.formPerm_pair i j

/-- The cycle `cyc []` is the identity. -/
@[simp]
theorem cyc_nil {X : Type*} [DecidableEq X] : cyc ([] : List X) = 1 := List.formPerm_nil

/-- The cycle `cyc [x]` is the identity. -/
@[simp]
theorem cyc_singleton {X : Type*} [DecidableEq X] (x : X) : cyc [x] = 1 :=
  List.formPerm_singleton x

/-- The cycle applied to an element not in the list returns the element unchanged.
    This is the "otherwise" case in def.perm.cycs. -/
theorem cyc_apply_of_not_mem {X : Type*} [DecidableEq X] {l : List X} {x : X} (h : x ∉ l) :
    cyc l x = x :=
  List.formPerm_apply_of_notMem h

/-- A cycle sends each element to the next in the list. -/
theorem cyc_apply_cons_cons {X : Type*} [DecidableEq X] (x y : X) (l : List X) :
    cyc (x :: y :: l) = Equiv.swap x y * cyc (y :: l) :=
  List.formPerm_cons_cons x y l

/-- If the list has no duplicates and length ≥ 2, then `cyc l` is a cycle in the sense of IsCycle. -/
theorem cyc_isCycle {X : Type*} [DecidableEq X] {l : List X} (hl : l.Nodup) (hn : 2 ≤ l.length) : 
    (cyc l).IsCycle :=
  List.isCycle_formPerm hl hn

/-- For a list with no duplicates and `x` in the list, `cyc l x` is the next element in the list
    (wrapping around at the end). -/
theorem cyc_apply_eq_next {X : Type*} [DecidableEq X] {l : List X} (hl : l.Nodup) {x : X}
    (hx : x ∈ l) : cyc l x = l.next x hx :=
  List.formPerm_apply_mem_eq_next hl x hx

/-- The support of `cyc l` is contained in `l.toFinset`. -/
theorem cyc_support_subset {X : Type*} [DecidableEq X] [Fintype X] {l : List X} :
    (cyc l).support ⊆ l.toFinset :=
  List.support_formPerm_le l

/-- For a nodup list with length ≥ 2, the support of `cyc l` equals `l.toFinset`. -/
theorem cyc_support_eq_toFinset {X : Type*} [DecidableEq X] [Fintype X] {l : List X}
    (hl : l.Nodup) (hn : 2 ≤ l.length) : (cyc l).support = l.toFinset := by
  apply List.support_formPerm_of_nodup _ hl
  intro x h
  rw [h] at hn
  simp at hn

/-- Cyclic rotation of the list doesn't change the cycle.
    This formalizes the textbook statement that 
    `cyc_{i₁,i₂,...,iₖ} = cyc_{i₂,i₃,...,iₖ,i₁} = ... = cyc_{iₖ,i₁,...,iₖ₋₁}`. -/
theorem cyc_rotate {X : Type*} [DecidableEq X] {l : List X} (hl : l.Nodup) (n : ℕ) :
    cyc (l.rotate n) = cyc l :=
  List.formPerm_rotate l hl n

/-- The cycle `cyc [i₁, i₂, ..., iₖ]` equals `cyc [i₂, ..., iₖ, i₁]`. -/
theorem cyc_rotate_one {X : Type*} [DecidableEq X] {l : List X} (hl : l.Nodup) :
    cyc (l.rotate 1) = cyc l :=
  cyc_rotate hl 1

/-- The cycle sends `l[j]` to `l[(j+1) % l.length]` for a nodup list.
    This is the formal statement of def.perm.cycs from the textbook:
    "cyc_{i₁,...,iₖ}(p) = i_{j+1} if p = i_j for some j ∈ {1,...,k}" -/
theorem cyc_apply_getElem {X : Type*} [DecidableEq X] {l : List X} (hl : l.Nodup) (j : ℕ)
    (hj : j < l.length) :
    cyc l (l[j]) = l[(j + 1) % l.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hj)) :=
  List.formPerm_apply_getElem l hl j hj

/-- For k-cycles with k ≥ 2 distinct elements, the cycle uniquely determines the elements
    up to cyclic rotation. This is stated in the solution to exe.perm.cyc.how-many-kcyc. -/
theorem cyc_eq_cyc_iff_isRotated {X : Type*} [DecidableEq X] {l l' : List X} (hl : l.Nodup)
    (hl' : l'.Nodup) (hlen : 2 ≤ l.length) (_hlen' : 2 ≤ l'.length) :
    cyc l = cyc l' ↔ l ~r l' := by
  rw [show cyc l = l.formPerm from rfl, show cyc l' = l'.formPerm from rfl]
  constructor
  · intro h
    have := List.formPerm_eq_formPerm_iff hl hl' |>.mp h
    rcases this with hrot | ⟨h1, _⟩
    · exact hrot
    · omega
  · intro h
    exact List.formPerm_eq_of_isRotated hl h

/-- A permutation is a cycle if any two non-fixed points are related by repeated
    application of the permutation. -/
abbrev IsCycle {X : Type*} (σ : Equiv.Perm X) : Prop := Equiv.Perm.IsCycle σ

/-- The support of a cycle (the set of elements it moves). -/
abbrev cycleSupport {X : Type*} [DecidableEq X] [Fintype X] (σ : Equiv.Perm X) : Finset X :=
  σ.support

/-- A 2-cycle is exactly a transposition. (Example after def.perm.cycs) -/
theorem cycle_eq_transposition {X : Type*} [DecidableEq X] [Fintype X] {σ : Equiv.Perm X}
    (hσ : σ.IsCycle) (hcard : σ.support.card = 2) :
    ∃ i j : X, i ≠ j ∧ σ = Equiv.swap i j := by
  -- Since σ is a cycle with support of size 2, orderOf σ = 2
  have horder : orderOf σ = 2 := by rw [hσ.orderOf, hcard]
  -- So σ² = 1, meaning σ (σ x) = x for all x
  have hsq : σ * σ = 1 := by rw [← pow_two, ← horder]; exact pow_orderOf_eq_one σ
  -- Get a non-fixed point x from the cycle definition
  obtain ⟨x, hx, hcycle⟩ := hσ
  -- Then σ(σ(x)) = x by the above
  have hffx : σ (σ x) = x := by simpa using congr_fun (congrArg (·.toFun) hsq) x
  -- Reconstruct the IsCycle hypothesis
  have hσ' : σ.IsCycle := ⟨x, hx, hcycle⟩
  -- Use the Mathlib lemma that says σ = swap x (σ x)
  exact ⟨x, σ x, fun h => hx h.symm, hσ'.eq_swap_of_apply_apply_eq_self hx hffx⟩

/-! ## Counting k-cycles (exe.perm.cyc.how-many-kcyc)

The number of k-cycles in `S_n` (for k > 1) is `n(n-1)...(n-k+1)/k = C(n,k) * (k-1)!`. -/

/-- The number of k-cycles in `S_n` is `C(n,k) * (k-1)!` for k > 1.
    (exe.perm.cyc.how-many-kcyc)

    The formula counts the number of ways to choose k elements from n (giving C(n,k))
    and then arrange them in a cycle (giving (k-1)! since cyclic rotations are equivalent). -/
theorem num_kCycles_formula (n k : ℕ) (hk : 1 < k) (hkn : k ≤ n) :
    -- The number of k-cycles equals C(n,k) * (k-1)!
    -- This is because:
    -- - There are n(n-1)...(n-k+1) ways to choose an ordered k-tuple
    -- - Each k-cycle corresponds to exactly k such tuples (by cyclic rotation)
    -- - So the count is n(n-1)...(n-k+1)/k = C(n,k) * (k-1)!
    ∃ (S : Finset (Sn n)),
      (∀ σ ∈ S, σ.IsCycle ∧ σ.support.card = k) ∧
      (∀ σ : Sn n, σ.IsCycle → σ.support.card = k → σ ∈ S) ∧
      S.card = Nat.choose n k * Nat.factorial (k - 1) := by
  classical
  -- Define S as the set of all k-cycles
  let S := Finset.univ.filter (fun σ : Sn n => σ.IsCycle ∧ σ.support.card = k)
  use S
  refine ⟨?_, ?_, ?_⟩
  -- First property: every element of S is a k-cycle
  · intro σ hσ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact hσ
  -- Second property: every k-cycle is in S
  · intro σ hσ hcard
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hσ, hcard⟩
  -- Third property: S.card = C(n,k) * (k-1)!
    -- First show S equals the set {g | g.cycleType = {k}}
  · have hS_eq : S = Finset.univ.filter (fun σ => σ.cycleType = {k}) := by
      ext σ
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hσ, hcard⟩
        rw [hσ.cycleType, hcard]
      · intro h
        constructor
        · have : Multiset.card σ.cycleType = 1 := by simp only [h, Multiset.card_singleton]
          exact Equiv.Perm.card_cycleType_eq_one.mp this
        · have hσ : σ.IsCycle := by
            have : Multiset.card σ.cycleType = 1 := by simp only [h, Multiset.card_singleton]
            exact Equiv.Perm.card_cycleType_eq_one.mp this
          have heq : σ.cycleType = {σ.support.card} := hσ.cycleType
          rw [h] at heq
          simp only [Multiset.singleton_inj] at heq
          exact heq.symm
    rw [hS_eq]
    -- Now use card_of_cycleType_singleton from Mathlib
    have h2k : 2 ≤ k := hk
    have hkn' : k ≤ Fintype.card (Fin n) := by simp [hkn]
    have := Equiv.Perm.card_of_cycleType_singleton h2k hkn'
    simp only [Fintype.card_fin] at this
    convert this using 1
    ring

/-- For k = 1, the only "1-cycle" would be the identity, but IsCycle excludes the identity.
    So there are no 1-cycles satisfying IsCycle. -/
theorem no_1Cycles_isCycle (n : ℕ) (σ : Sn n) (hσ : σ.IsCycle) :
    2 ≤ σ.support.card :=
  -- IsCycle implies σ ≠ 1, which implies support has at least 2 elements
  hσ.two_le_card_support

/-! ## Involutions (def.perm.invol)

An involution is a permutation equal to its own inverse. -/

/-- A permutation is an involution if `σ ∘ σ = id`. (def.perm.invol)

From the textbook:
> An *involution* of X means a map f: X → X that satisfies f ∘ f = id.
> Clearly, an involution is always a permutation, and equals its own inverse.

Equivalent characterizations:
- `IsInvolution σ ↔ σ * σ = 1` (definition)
- `IsInvolution σ ↔ σ⁻¹ = σ` (see `isInvolution_iff_eq_inv`)
- `IsInvolution σ ↔ Function.Involutive σ` (see `isInvolution_iff_involutive`)
- `IsInvolution σ ↔ ∀ x, σ (σ x) = x` (see `isInvolution_iff_forall`)
-/
def IsInvolution {X : Type*} (σ : Equiv.Perm X) : Prop := σ * σ = 1

/-- Decidable instance for IsInvolution on finite types. -/
instance instDecidableIsInvolution {X : Type*} [Fintype X] [DecidableEq X]
    (σ : Equiv.Perm X) : Decidable (IsInvolution σ) :=
  inferInstanceAs (Decidable (σ * σ = 1))

/-- An involution is equal to its own inverse. -/
theorem IsInvolution.eq_inv {X : Type*} {σ : Equiv.Perm X} (h : IsInvolution σ) :
    σ⁻¹ = σ := by
  rw [← mul_left_cancel_iff (a := σ)]
  simp only [mul_inv_cancel]
  exact h.symm

/-- Characterization: σ is an involution iff σ⁻¹ = σ. -/
theorem isInvolution_iff_eq_inv {X : Type*} {σ : Equiv.Perm X} :
    IsInvolution σ ↔ σ⁻¹ = σ := by
  constructor
  · exact IsInvolution.eq_inv
  · intro h
    unfold IsInvolution
    calc σ * σ = σ * σ⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel σ

/-- Characterization: σ is an involution iff it is involutive as a function. -/
theorem isInvolution_iff_involutive {X : Type*} {σ : Equiv.Perm X} :
    IsInvolution σ ↔ Function.Involutive σ := by
  constructor
  · intro h x
    have : (σ * σ) x = x := by rw [h]; rfl
    simp only [Equiv.Perm.coe_mul, Function.comp_apply] at this
    exact this
  · intro h
    ext x
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq]
    exact h x

/-- Characterization: σ is an involution iff σ(σ(x)) = x for all x. -/
theorem isInvolution_iff_forall {X : Type*} {σ : Equiv.Perm X} :
    IsInvolution σ ↔ ∀ x, σ (σ x) = x :=
  isInvolution_iff_involutive

/-- An involution applied twice is the identity. -/
theorem IsInvolution.apply_apply {X : Type*} {σ : Equiv.Perm X} (h : IsInvolution σ) (x : X) :
    σ (σ x) = x :=
  isInvolution_iff_forall.mp h x

/-- The identity is an involution. -/
theorem isInvolution_one {X : Type*} : IsInvolution (1 : Equiv.Perm X) := by
  simp [IsInvolution]

/-- Any transposition is an involution. -/
theorem isInvolution_transposition {X : Type*} [DecidableEq X] (i j : X) :
    IsInvolution (transposition i j) :=
  transposition_sq_eq_one i j

/-- Simple transpositions are involutions. -/
theorem isInvolution_simpleTransposition {n : ℕ} (i : Fin (n - 1)) :
    IsInvolution (simpleTransposition i) :=
  simpleTransposition_sq_eq_one i

/-- The order of an involution divides 2. -/
theorem IsInvolution.orderOf_dvd_two {X : Type*} [Fintype X] {σ : Equiv.Perm X} (h : IsInvolution σ) :
    orderOf σ ∣ 2 := by
  have h2 : σ ^ 2 = 1 := by rw [sq]; exact h
  exact orderOf_dvd_of_pow_eq_one h2

/-- An involution has order 1 or 2. -/
theorem IsInvolution.orderOf_le_two {X : Type*} [Fintype X] {σ : Equiv.Perm X} (h : IsInvolution σ) :
    orderOf σ ≤ 2 :=
  Nat.le_of_dvd (by norm_num) h.orderOf_dvd_two

/-- An involution is the identity iff its order is 1. -/
theorem IsInvolution.eq_one_iff_orderOf_eq_one {X : Type*} {σ : Equiv.Perm X}
    (_h : IsInvolution σ) : σ = 1 ↔ orderOf σ = 1 := by
  constructor
  · intro h'; rw [h']; exact orderOf_one
  · intro h'; exact orderOf_eq_one_iff.mp h'

/-- A nontrivial involution has order exactly 2. -/
theorem IsInvolution.orderOf_eq_two_of_ne_one {X : Type*} [Fintype X] {σ : Equiv.Perm X}
    (h : IsInvolution σ) (hne : σ ≠ 1) : orderOf σ = 2 := by
  have hdvd := h.orderOf_dvd_two
  rcases Nat.dvd_prime Nat.prime_two |>.mp hdvd with h1 | h2
  · exact (hne (orderOf_eq_one_iff.mp h1)).elim
  · exact h2

/-- A k-cycle with k > 2 is never an involution. -/
theorem not_isInvolution_of_cycle_gt_two {X : Type*} [DecidableEq X] [Fintype X]
    {σ : Equiv.Perm X} (hσ : σ.IsCycle) (hcard : 2 < σ.support.card) :
    ¬IsInvolution σ := by
  intro h
  -- h says σ * σ = 1, i.e., σ² = 1
  -- This means orderOf σ divides 2
  have h2 : σ ^ 2 = 1 := by rw [sq]; exact h
  have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  -- For a cycle, orderOf σ = #σ.support
  rw [hσ.orderOf] at hdvd
  -- So #σ.support ∣ 2, which means #σ.support ≤ 2
  have hle : σ.support.card ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  -- But we have 2 < #σ.support, contradiction
  omega

/-- Products of disjoint transpositions are involutions.
    (This is stated informally in the source after def.perm.invol) -/
theorem isInvolution_of_disjoint_transpositions {X : Type*} [DecidableEq X]
    {pairs : List (X × X)}
    (hdisjoint : pairs.Pairwise (fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2))
    (hdistinct : ∀ p ∈ pairs, p.1 ≠ p.2) :
    IsInvolution (pairs.map (fun p => transposition p.1 p.2)).prod := by
  unfold IsInvolution
  induction pairs with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons]
    set t := transposition p.1 p.2
    set s := (ps.map (fun p => transposition p.1 p.2)).prod
    -- First show t and s commute (because they are disjoint)
    have hcomm : Commute t s := by
      apply Equiv.Perm.Disjoint.commute
      apply Equiv.Perm.disjoint_prod_right
      intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨q, hq_mem, hq_eq⟩ := hg
      subst hq_eq
      have hdisj := List.rel_of_pairwise_cons hdisjoint hq_mem
      obtain ⟨h1, h2, h3, h4⟩ := hdisj
      intro x
      simp only [transposition, Equiv.swap_apply_def]
      by_cases hxp1 : x = p.1
      · right
        subst hxp1
        simp only [h1, ite_false, h2]
      · by_cases hxp2 : x = p.2
        · right
          subst hxp2
          simp only [h3, ite_false, h4]
        · left
          simp only [t, transposition, Equiv.swap_apply_def, hxp1, hxp2, ite_false]
    -- Now use commutativity to rearrange: (t * s)² = t * s * t * s = t * t * s * s = 1 * 1 = 1
    have ht2 : t * t = 1 := transposition_sq_eq_one p.1 p.2
    have hs2 : s * s = 1 := by
      apply ih
      · exact List.Pairwise.of_cons hdisjoint
      · intro q hq
        exact hdistinct q (List.mem_cons.mpr (Or.inr hq))
    calc t * s * (t * s) = t * (s * t) * s := by group
      _ = t * (t * s) * s := by rw [hcomm.eq]
      _ = (t * t) * (s * s) := by group
      _ = 1 * 1 := by rw [ht2, hs2]
      _ = 1 := by group

-- The pair elements are in the support of the swap
private lemma swapToPair_mem_support {X : Type*} [DecidableEq X] [Fintype X]
    (σ : Equiv.Perm X) (hσ : σ.IsSwap) :
    (swapToPair σ hσ).1 ∈ σ.support ∧ (swapToPair σ hσ).2 ∈ σ.support := by
  have hne := (swapToPair_spec σ hσ).1
  have heq := (swapToPair_spec σ hσ).2
  have hsupp : σ.support = {(swapToPair σ hσ).1, (swapToPair σ hσ).2} := by
    conv_lhs => rw [heq]
    exact Equiv.Perm.support_swap hne
  simp only [hsupp, mem_insert, mem_singleton, true_or, or_true, and_self]

/-- The cycle digraph of an involution consists of 1-cycles and 2-cycles.
    (Stated informally at the end of the source) -/
theorem involution_cycle_structure {X : Type*} [DecidableEq X] [Fintype X]
    {σ : Equiv.Perm X} (h : IsInvolution σ) :
    ∀ c ∈ σ.cycleFactorsFinset, (c : Equiv.Perm X).support.card ≤ 2 := by
  intro c hc
  -- c is a cycle in the factorization of σ
  have hcycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
  have hca := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2
  -- Since c agrees with σ on its support, and σ² = 1, we have c² = 1
  have hc_sq : c * c = 1 := by
    ext x
    by_cases hx : x ∈ c.support
    · -- x is in the support of c, so c x = σ x
      simp only [Perm.coe_mul, Function.comp_apply, Perm.coe_one, id_eq]
      have hcx : c x = σ x := hca x hx
      -- c x is also in c.support (since c is a bijection on its support)
      have hcx_mem : c x ∈ c.support := by
        rw [Equiv.Perm.mem_support] at hx ⊢
        intro h_eq
        apply hx
        exact c.injective h_eq
      have hccx : c (c x) = σ (c x) := hca (c x) hcx_mem
      -- σ(σ x) = x since σ² = 1
      have hσσ : (σ * σ) x = x := by rw [h]; rfl
      simp only [Perm.coe_mul, Function.comp_apply] at hσσ
      -- c (c x) = σ (c x) = σ (σ x) = x
      calc c (c x) = σ (c x) := hccx
        _ = σ (σ x) := by rw [hcx]
        _ = x := hσσ
    · -- x is not in c.support, so c x = x
      simp only [Perm.coe_mul, Function.comp_apply, Perm.coe_one, id_eq]
      rw [Equiv.Perm.notMem_support.mp hx]
      rw [Equiv.Perm.notMem_support.mp hx]
  -- From c² = 1, we get orderOf c | 2
  have h_order_dvd : orderOf c ∣ 2 := by
    rw [← sq] at hc_sq
    exact orderOf_dvd_of_pow_eq_one hc_sq
  -- For a cycle, orderOf c = c.support.card
  have h_order_eq : orderOf c = c.support.card := hcycle.orderOf
  -- So c.support.card | 2, meaning c.support.card ∈ {1, 2}
  rw [h_order_eq] at h_order_dvd
  -- c.support.card divides 2, so it's 1 or 2
  rcases Nat.dvd_prime Nat.prime_two |>.mp h_order_dvd with h1 | h2
  · omega
  · omega

/-- An involution of a finite set is a product of disjoint transpositions.
    (Stated informally in the source) -/
theorem involution_is_product_of_disjoint_transpositions {X : Type*} [DecidableEq X] [Fintype X]
    {σ : Equiv.Perm X} (h : IsInvolution σ) :
    ∃ pairs : List (X × X),
      pairs.Pairwise (fun p q => p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) ∧
      (∀ p ∈ pairs, p.1 ≠ p.2) ∧
      σ = (pairs.map (fun p => transposition p.1 p.2)).prod := by
  -- Get the cycle factors of σ
  obtain ⟨l, hl_nodup, hl_eq⟩ := σ.cycleFactorsFinset.exists_list_nodup_eq
  -- Each cycle in l has support card = 2 (since it's a cycle with support ≤ 2)
  have h_support_eq_two : ∀ c ∈ l, c.support.card = 2 := by
    intro c hc
    have hc' : c ∈ σ.cycleFactorsFinset := by rw [← hl_eq]; exact List.mem_toFinset.mpr hc
    have hcycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc').1
    have hle := involution_cycle_structure h c hc'
    have hge := hcycle.two_le_card_support
    omega
  -- Each cycle is a swap
  have h_is_swap : ∀ c ∈ l, c.IsSwap := by
    intro c hc
    exact Equiv.Perm.card_support_eq_two.mp (h_support_eq_two c hc)
  -- Cycles are pairwise disjoint
  have h_disjoint : l.Pairwise Equiv.Perm.Disjoint := by
    have hpw := Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ
    rw [← hl_eq] at hpw
    rw [Set.Pairwise, List.coe_toFinset] at hpw
    exact hl_nodup.pairwise_of_forall_ne (fun a ha b hb hab => hpw ha hb hab)
  -- Construct pairs using swapToPair
  let pairs : List (X × X) := l.pmap (fun c hc => swapToPair c (h_is_swap c hc)) (fun _ hc => hc)
  use pairs
  constructor
  · -- Pairwise disjointness of pairs
    rw [List.pairwise_pmap]
    apply List.Pairwise.imp _ h_disjoint
    intro c₁ c₂ hdisj hc₁ hc₂
    have hp₁ := swapToPair_mem_support c₁ (h_is_swap c₁ hc₁)
    have hp₂ := swapToPair_mem_support c₂ (h_is_swap c₂ hc₂)
    have hdisj_supp : Disjoint c₁.support c₂.support := hdisj.disjoint_support
    rw [Finset.disjoint_iff_inter_eq_empty] at hdisj_supp
    constructor
    · intro heq
      have hmem : (swapToPair c₁ (h_is_swap c₁ hc₁)).1 ∈ c₁.support ∩ c₂.support := by
        rw [Finset.mem_inter]; exact ⟨hp₁.1, heq ▸ hp₂.1⟩
      rw [hdisj_supp] at hmem; exact Finset.notMem_empty _ hmem
    constructor
    · intro heq
      have hmem : (swapToPair c₁ (h_is_swap c₁ hc₁)).1 ∈ c₁.support ∩ c₂.support := by
        rw [Finset.mem_inter]; exact ⟨hp₁.1, heq ▸ hp₂.2⟩
      rw [hdisj_supp] at hmem; exact Finset.notMem_empty _ hmem
    constructor
    · intro heq
      have hmem : (swapToPair c₁ (h_is_swap c₁ hc₁)).2 ∈ c₁.support ∩ c₂.support := by
        rw [Finset.mem_inter]; exact ⟨hp₁.2, heq ▸ hp₂.1⟩
      rw [hdisj_supp] at hmem; exact Finset.notMem_empty _ hmem
    · intro heq
      have hmem : (swapToPair c₁ (h_is_swap c₁ hc₁)).2 ∈ c₁.support ∩ c₂.support := by
        rw [Finset.mem_inter]; exact ⟨hp₁.2, heq ▸ hp₂.2⟩
      rw [hdisj_supp] at hmem; exact Finset.notMem_empty _ hmem
  constructor
  · -- Each pair has distinct elements
    intro p hp
    simp only [pairs, List.mem_pmap] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    exact (swapToPair_spec c (h_is_swap c hc)).1
  · -- Product equals σ
    have h_map : pairs.map (fun p => Equiv.swap p.1 p.2) = l := by
      simp only [pairs]
      rw [List.map_pmap]
      have h_eq : ∀ c (hc : c ∈ l),
          Equiv.swap (swapToPair c (h_is_swap c hc)).1 (swapToPair c (h_is_swap c hc)).2 = c := by
        intro c hc
        exact (swapToPair_spec c (h_is_swap c hc)).2.symm
      rw [show (fun c hc => Equiv.swap (swapToPair c (h_is_swap c hc)).1
          (swapToPair c (h_is_swap c hc)).2) = (fun c _ => c) from funext₂ h_eq]
      simp
    have h_prod : l.prod = σ := by
      have hcomm : (l.toFinset : Set (Equiv.Perm X)).Pairwise Commute := by
        rw [hl_eq]; exact Equiv.Perm.cycleFactorsFinset_mem_commute σ
      have := Equiv.Perm.cycleFactorsFinset_noncommProd (f := σ)
        (Equiv.Perm.cycleFactorsFinset_mem_commute σ)
      have h1 : l.toFinset.noncommProd id hcomm = σ := by simp only [hl_eq]; exact this
      rw [Finset.noncommProd_toFinset l id hcomm hl_nodup] at h1
      simp at h1; exact h1
    rw [← h_prod, ← h_map]

end AlgebraicCombinatorics
