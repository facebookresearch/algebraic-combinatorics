/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# N-Partitions

This file provides the canonical definition of `NPartition N`, which represents
a weakly decreasing N-tuple of nonnegative integers (Definition def.sf.Npar in the source).

## Main definitions

* `IsNPartition` - predicate for N-tuples that are weakly decreasing
* `NPartition N` - a weakly decreasing N-tuple of nonnegative integers
* `NPartition.parts` - the entries of the partition as a function `Fin N → ℕ`
* `NPartition.antitone` - proof that the entries are weakly decreasing
* `NPartition.size` - the sum of all entries
* `NPartition.zero` - the zero partition (0, 0, ..., 0)
* `NPartition.add` - component-wise addition of N-partitions
* `NPartition.youngDiagram` - the Young diagram Y(λ) as a `Finset (Fin N × ℕ)`
* `NPartition.skewYoungDiagram` - the skew Young diagram Y(λ/μ) as a `Finset (Fin N × ℕ)`
* `NPartition.instFintypeBounded` - `Fintype` instance for partitions with bounded entries
* `NPartition.instFintypeSizeBounded` - `Fintype` instance for partitions with bounded size

## Design notes

This file provides the canonical `NPartition` structure. We use `antitone` as the
field name since it matches Mathlib conventions.

The weakly decreasing condition means: if `i ≤ j` then `parts j ≤ parts i`.
This is equivalent to `Antitone parts` in Mathlib terminology.

## Duplicate definitions

For historical reasons, there is a local `NPartition` definition in:

1. `PieriJacobiTrudi.lean` (`SymmetricFunctions.NPartition`):
   Uses `weaklyDecreasing` field name.

Both definitions are semantically equivalent (representing weakly decreasing
N-tuples of natural numbers). The local definition is retained to avoid large
refactoring of the extensive APIs built on top of it. Future work may consolidate
these definitions.

**Note**: `MonomialSymmetric.lean` and `SchurBasics.lean` have been migrated to use
the canonical definition via `abbrev` or direct import.

## Compatibility

For backwards compatibility with code using other field names:
- `NPartition.monotone` is an alias for `NPartition.antitone`
- `NPartition.weaklyDecreasing` is an alias for `NPartition.antitone`

## Migration Guide

The `NPartition` structure is defined in this file (canonical) and has one remaining
local definition:

| File                     | Namespace                       | Field name        | Status           |
|--------------------------|--------------------------------|-------------------|------------------|
| `NPartition.lean` (this) | (top-level)                    | `antitone`        | **Canonical**    |
| `PieriJacobiTrudi.lean`  | `SymmetricFunctions`           | `weaklyDecreasing`| Local (with bridge) |
| `MonomialSymmetric.lean` | `AlgebraicCombinatorics.SymmetricFunctions`   | (abbrev)          | ✓ Migrated       |
| `SchurBasics.lean`       | (top-level)                    | (import)          | ✓ Migrated       |

To migrate a file to use this shared definition:

1. Add `import AlgebraicCombinatorics.SymmetricFunctions.NPartition` to imports
2. Remove the local `structure NPartition` definition
3. If in a namespace, use `open NPartition` or create a local alias
4. Replace field accesses:
   - `.monotone` → `.antitone` or use the `monotone` alias theorem
   - `.weaklyDecreasing` → `.antitone` or use the `weaklyDecreasing` alias theorem
5. For constructors, use `NPartition.mk` with `antitone` field, or use `NPartition.mk'`
   which accepts the explicit predicate form

## References

* Source: AlgebraicCombinatorics/tex/SymmetricFunctions/MonomialSymmetric.tex (Definition def.sf.Npar)
-/

open Finset BigOperators

variable {N : ℕ}

/-! ## IsNPartition predicate

This predicate characterizes N-tuples that are weakly decreasing. It is equivalent
to `Antitone` for functions `Fin N → ℕ`. -/

/-- An N-partition predicate: an N-tuple is an N-partition if it is weakly decreasing.
    This is equivalent to `Antitone` for functions `Fin N → ℕ`.
    (Used throughout the source) -/
def IsNPartition (lam : Fin N → ℕ) : Prop :=
  ∀ i j : Fin N, i ≤ j → lam j ≤ lam i

/-- `IsNPartition` is decidable since it's a finite conjunction of decidable inequalities. -/
instance IsNPartition.instDecidable (lam : Fin N → ℕ) : Decidable (IsNPartition lam) :=
  inferInstanceAs (Decidable (∀ i j : Fin N, i ≤ j → lam j ≤ lam i))

/-- `IsNPartition` is equivalent to `Antitone`. -/
theorem isNPartition_iff_antitone {lam : Fin N → ℕ} : IsNPartition lam ↔ Antitone lam :=
  Iff.rfl

/-- The zero tuple is an N-partition (trivially weakly decreasing). -/
theorem isNPartition_zero : IsNPartition (0 : Fin N → ℕ) := by
  intro i j _
  simp only [Pi.zero_apply, le_refl]

/-- The sum of two N-partitions is an N-partition. -/
theorem IsNPartition.add {α β : Fin N → ℕ} (hα : IsNPartition α) (hβ : IsNPartition β) :
    IsNPartition (α + β) := by
  intro i j hij
  simp only [Pi.add_apply]
  exact Nat.add_le_add (hα i j hij) (hβ i j hij)

namespace NPartition

variable {N : ℕ}

end NPartition

/-- An N-partition is a weakly decreasing N-tuple of nonnegative integers.
    (Definition def.sf.Npar)

    This is represented as a function `Fin N → ℕ` that is antitone
    (i.e., `i ≤ j → parts j ≤ parts i`).

    The field is named `antitone` to match Mathlib conventions. -/
structure NPartition (N : ℕ) where
  /-- The entries of the N-partition as a function from `Fin N` to `ℕ` -/
  parts : Fin N → ℕ
  /-- The entries are weakly decreasing (antitone) -/
  antitone : Antitone parts

namespace NPartition

variable {N : ℕ}

/-! ## Compatibility aliases for field names -/

/-- Alias for `antitone` to match SchurBasics.lean naming convention.
    The weakly decreasing condition: if `i ≤ j` then `parts j ≤ parts i`. -/
theorem monotone (μ : NPartition N) : ∀ i j : Fin N, i ≤ j → μ.parts j ≤ μ.parts i :=
  μ.antitone

/-- Alias for `antitone` to match PieriJacobiTrudi.lean naming convention.
    The weakly decreasing condition: if `i ≤ j` then `parts j ≤ parts i`. -/
theorem weaklyDecreasing (μ : NPartition N) : ∀ i j : Fin N, i ≤ j → μ.parts j ≤ μ.parts i :=
  μ.antitone

/-- The antitone property as a function (for use in proofs). -/
theorem parts_antitone (μ : NPartition N) : Antitone μ.parts := μ.antitone

/-- An NPartition's parts satisfy the IsNPartition predicate.
    This connects the structure-based definition with the predicate-based definition. -/
theorem isNPartition (μ : NPartition N) : IsNPartition μ.parts :=
  μ.monotone

/-! ## Basic properties -/

/-- Two N-partitions are equal if and only if their parts are equal. -/
@[ext]
theorem ext {μ ν : NPartition N} (h : μ.parts = ν.parts) : μ = ν := by
  cases μ; cases ν; simp_all

/-- Extensionality in terms of pointwise equality. -/
theorem ext' {μ ν : NPartition N} : μ = ν ↔ ∀ i, μ.parts i = ν.parts i :=
  ⟨fun h _ => h ▸ rfl, fun h => ext (funext h)⟩

/-- Extensionality for pointwise equality (variant taking a proof for each index). -/
theorem ext_parts {μ ν : NPartition N} (h : ∀ i, μ.parts i = ν.parts i) : μ = ν :=
  ext (funext h)

/-- Extensionality in terms of parts equality. -/
theorem parts_ext_iff {μ ν : NPartition N} : μ = ν ↔ μ.parts = ν.parts :=
  ⟨fun h => h ▸ rfl, ext⟩

/-- Decidable equality for N-partitions. -/
instance instDecidableEq : DecidableEq (NPartition N) := fun μ ν =>
  decidable_of_iff (μ.parts = ν.parts) parts_ext_iff.symm

/-! ## The zero partition -/

/-- The zero N-partition (0, 0, ..., 0) -/
def zero : NPartition N where
  parts := fun _ => 0
  antitone := fun _ _ _ => le_refl 0

instance : Zero (NPartition N) := ⟨zero⟩

instance : Inhabited (NPartition N) := ⟨0⟩

@[simp]
theorem zero_parts : (0 : NPartition N).parts = fun _ => 0 := rfl

@[simp]
theorem zero_parts_apply (i : Fin N) : (0 : NPartition N).parts i = 0 := rfl

/-! ## Size (weight) of a partition -/

/-- The size (or weight) of an N-partition is the sum of its entries.
    If μ = (μ₁, μ₂, ..., μ_N), then |μ| = μ₁ + μ₂ + ... + μ_N. -/
def size (μ : NPartition N) : ℕ := ∑ i, μ.parts i

@[simp]
theorem size_eq_sum (μ : NPartition N) : μ.size = ∑ i, μ.parts i := rfl

@[simp]
theorem zero_size : (0 : NPartition N).size = 0 := by simp [size]

/-- Each entry of an N-partition is bounded by the size. -/
theorem parts_le_size (μ : NPartition N) (i : Fin N) : μ.parts i ≤ μ.size := by
  simp only [size]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- The first entry is the largest in an N-partition (when N > 0). -/
theorem parts_zero_max (μ : NPartition N) (i : Fin N) (hN : 0 < N) :
    μ.parts i ≤ μ.parts ⟨0, hN⟩ := by
  apply μ.antitone
  exact Nat.zero_le i.val

/-- The first entry of an N-partition equals the size iff all other entries are zero. -/
theorem parts_zero_eq_size_iff (μ : NPartition N) (hN : 0 < N) :
    μ.parts ⟨0, hN⟩ = μ.size ↔ ∀ i : Fin N, i.val ≠ 0 → μ.parts i = 0 := by
  constructor
  · intro h i hi
    have hle : μ.parts i ≤ μ.parts ⟨0, hN⟩ := by
      apply μ.antitone
      exact Nat.zero_le i.val
    have hsum : μ.size = μ.parts ⟨0, hN⟩ + ∑ j ∈ Finset.univ.filter (· ≠ ⟨0, hN⟩), μ.parts j := by
      simp only [size]
      rw [← Finset.add_sum_erase Finset.univ (fun j => μ.parts j) (Finset.mem_univ ⟨0, hN⟩)]
      congr 1
      apply Finset.sum_congr
      · ext x
        simp [Finset.mem_erase, Finset.mem_filter]
      · intro _ _; rfl
    rw [h] at hsum
    have : ∑ j ∈ Finset.univ.filter (· ≠ ⟨0, hN⟩), μ.parts j = 0 := by omega
    have hmem : i ∈ Finset.univ.filter (· ≠ (⟨0, hN⟩ : Fin N)) := by
      simp [Finset.mem_filter]
      intro heq
      simp only [Fin.ext_iff] at heq
      exact hi heq
    exact Finset.sum_eq_zero_iff.mp this i hmem
  · intro h
    simp only [size]
    rw [Finset.sum_eq_single ⟨0, hN⟩]
    · intro j _ hj
      apply h
      simp only [ne_eq, Fin.ext_iff] at hj
      exact hj
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- An N-partition with size 0 is the zero partition. -/
theorem eq_zero_of_size_eq_zero (μ : NPartition N) (h : μ.size = 0) : μ = 0 := by
  ext i
  simp only [zero_parts]
  have : μ.parts i ≤ μ.size := parts_le_size μ i
  omega

/-- An N-partition has size 0 if and only if it is the zero partition. -/
@[simp]
theorem size_eq_zero_iff (μ : NPartition N) : μ.size = 0 ↔ μ = 0 :=
  ⟨eq_zero_of_size_eq_zero μ, fun h => h ▸ zero_size⟩

/-- A non-zero N-partition has positive size. -/
theorem size_pos_of_ne_zero {μ : NPartition N} (h : μ ≠ 0) : 0 < μ.size := by
  rw [Nat.pos_iff_ne_zero]
  intro hsize
  exact h (size_eq_zero_iff μ |>.mp hsize)

/-! ## Addition of N-partitions

Component-wise addition of N-partitions. Since both partitions are antitone
(weakly decreasing), their component-wise sum is also antitone, so the result
is a valid N-partition without needing to sort.

This is the canonical `Add` instance for `NPartition`, used by all files including
`MonomialSymmetric.lean`.
-/

/-- Component-wise addition of N-partitions.
    Since both partitions are antitone (weakly decreasing), their sum is also antitone. -/
def add (μ ν : NPartition N) : NPartition N where
  parts i := μ.parts i + ν.parts i
  antitone := fun _ _ hij => Nat.add_le_add (μ.antitone hij) (ν.antitone hij)

instance : Add (NPartition N) := ⟨add⟩

/-- The parts of a sum of N-partitions equals the component-wise sum. -/
@[simp]
theorem add_parts (μ ν : NPartition N) (i : Fin N) : (μ + ν).parts i = μ.parts i + ν.parts i := rfl

/-- The size of a sum of N-partitions equals the sum of their sizes. -/
@[simp]
theorem add_size (μ ν : NPartition N) : (μ + ν).size = μ.size + ν.size := by
  simp only [size, add_parts]
  exact Finset.sum_add_distrib

/-- Addition of N-partitions is commutative. -/
theorem add_comm (μ ν : NPartition N) : μ + ν = ν + μ := by
  ext i
  simp [Nat.add_comm]

/-- Adding zero to an N-partition gives the same N-partition. -/
@[simp]
theorem add_zero (μ : NPartition N) : μ + 0 = μ := by
  ext i
  simp [add_parts]

/-- Adding an N-partition to zero gives the same N-partition. -/
@[simp]
theorem zero_add (μ : NPartition N) : 0 + μ = μ := by
  rw [add_comm, add_zero]

/-- Addition of N-partitions is associative. -/
theorem add_assoc (μ ν ρ : NPartition N) : μ + ν + ρ = μ + (ν + ρ) := by
  ext i
  simp [Nat.add_assoc]

/-- `NPartition N` forms an `AddCommMonoid` under component-wise addition.
    This enables using generic Mathlib lemmas about `AddCommMonoid` with `NPartition`. -/
instance : AddCommMonoid (NPartition N) where
  add_assoc := add_assoc
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  nsmul := nsmulRec

/-! ## Coercion to function -/

/-- Coercion to a function. -/
instance : CoeFun (NPartition N) (fun _ => Fin N → ℕ) := ⟨parts⟩

@[simp]
theorem coe_parts (μ : NPartition N) : (μ : Fin N → ℕ) = μ.parts := rfl

/-! ## Partial order (containment) -/

/-- Containment of partitions: μ ≤ ν means μᵢ ≤ νᵢ for all i -/
instance instLE : LE (NPartition N) where
  le μ ν := ∀ i, μ.parts i ≤ ν.parts i

theorem le_def (μ ν : NPartition N) : μ ≤ ν ↔ ∀ i, μ.parts i ≤ ν.parts i := Iff.rfl

/-- Alias for `le_def` matching SchurBasics.lean naming. -/
theorem le_iff {μ ν : NPartition N} : μ ≤ ν ↔ ∀ i, μ.parts i ≤ ν.parts i := Iff.rfl

instance instPreorder : Preorder (NPartition N) where
  le := (· ≤ ·)
  le_refl := fun μ i => le_refl (μ.parts i)
  le_trans := fun μ ν ρ hab hbc i => le_trans (hab i) (hbc i)

instance instPartialOrder : PartialOrder (NPartition N) where
  le_antisymm := fun _ _ hab hba => ext (funext fun i => le_antisymm (hab i) (hba i))

/-! ## Fintype instances for bounded partitions -/

set_option backward.isDefEq.respectTransparency false in
/-- The set of N-partitions with entries bounded by M is finite.
    This is useful for cardinality arguments in symmetric function theory. -/
noncomputable instance instFintypeBounded (M : ℕ) :
    Fintype { μ : NPartition N // ∀ i, μ.parts i ≤ M } := by
  -- Strategy: embed into Fin N → Fin (M + 1) which is finite
  let S := { f : Fin N → Fin (M + 1) // Antitone f }
  have hS : Fintype S := Subtype.fintype _
  let φ : { μ : NPartition N // ∀ i, μ.parts i ≤ M } → S := fun ⟨μ, hμ⟩ =>
    ⟨fun i => ⟨μ.parts i, Nat.lt_succ_of_le (hμ i)⟩, fun i j hij =>
      Fin.mk_le_mk.mpr (μ.antitone hij)⟩
  have hφ : Function.Injective φ := by
    intro ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩ heq
    simp only [S, φ, Subtype.mk.injEq] at heq
    ext i
    have : (⟨μ₁.parts i, _⟩ : Fin (M + 1)) = ⟨μ₂.parts i, _⟩ := congr_fun heq i
    exact Fin.mk.injEq _ _ _ _ ▸ this
  exact Fintype.ofInjective φ hφ

/-- The set of N-partitions with size bounded by n is finite.
    This follows from the fact that if size ≤ n, then all entries are ≤ n.
    This is needed for counting SSYT of bounded content. -/
noncomputable instance instFintypeSizeBounded (n : ℕ) :
    Fintype { μ : NPartition N // μ.size ≤ n } := by
  -- If size ≤ n, then all entries are ≤ n (since each entry ≤ size)
  -- So we can embed into the bounded-entry type
  let T := { μ : NPartition N // ∀ i, μ.parts i ≤ n }
  have hT : Fintype T := instFintypeBounded n
  let φ : { μ : NPartition N // μ.size ≤ n } → T := fun ⟨μ, hμ⟩ =>
    ⟨μ, fun i => le_trans (parts_le_size μ i) hμ⟩
  have hφ : Function.Injective φ := by
    intro ⟨μ₁, _⟩ ⟨μ₂, _⟩ heq
    simp only [T, φ, Subtype.mk.injEq] at heq
    exact Subtype.ext heq
  exact Fintype.ofInjective φ hφ

/-- The set of N-partitions with exact size n is finite.
    This is a subtype of the bounded-size type. -/
noncomputable instance instFintypeSizeEq (n : ℕ) :
    Fintype { μ : NPartition N // μ.size = n } := by
  have hBounded : Fintype { μ : NPartition N // μ.size ≤ n } := instFintypeSizeBounded n
  let φ : { μ : NPartition N // μ.size = n } → { μ : NPartition N // μ.size ≤ n } :=
    fun ⟨μ, hμ⟩ => ⟨μ, le_of_eq hμ⟩
  have hφ : Function.Injective φ := by
    intro ⟨μ₁, _⟩ ⟨μ₂, _⟩ heq
    simp only [φ, Subtype.mk.injEq] at heq
    exact Subtype.ext heq
  exact Fintype.ofInjective φ hφ

/-- The finite set of N-partitions with exact size n. -/
noncomputable def partitionsOfSize (n : ℕ) : Finset (NPartition N) :=
  (Finset.univ : Finset { μ : NPartition N // μ.size = n }).map
    ⟨Subtype.val, Subtype.val_injective⟩

/-- Membership in partitionsOfSize is characterized by size. -/
theorem mem_partitionsOfSize (μ : NPartition N) (n : ℕ) :
    μ ∈ partitionsOfSize n ↔ μ.size = n := by
  simp only [partitionsOfSize, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Subtype.exists, exists_prop]
  constructor
  · rintro ⟨ν, hν, rfl⟩
    exact hν
  · intro hμ
    exact ⟨μ, hμ, rfl⟩

/-- The set of N-partitions with size n is finite (Set.Finite version). -/
theorem finite_of_size (n : ℕ) : Set.Finite { μ : NPartition N | μ.size = n } := by
  haveI : Fintype { μ : NPartition N // μ.size = n } := instFintypeSizeEq n
  have : Finite { μ : NPartition N // μ.size = n } := inferInstance
  exact Set.finite_coe_iff.mp this

/-- Decidable instance for partition containment. -/
instance instDecidableLE : DecidableRel (fun (μ ν : NPartition N) => μ ≤ ν) :=
  fun _ _ => Fintype.decidableForallFintype

/-- The zero N-partition is the minimum element -/
theorem zero_le (μ : NPartition N) : (0 : NPartition N) ≤ μ := fun i => by
  simp only [zero_parts_apply]
  exact Nat.zero_le _

/-- μ ≤ ν implies |μ| ≤ |ν| -/
theorem size_le_of_le {μ ν : NPartition N} (h : μ ≤ ν) : μ.size ≤ ν.size := by
  unfold size
  apply Finset.sum_le_sum
  intro i _
  exact h i

/-! ## Length of a partition -/

/-- The length of an N-partition is the number of nonzero entries. -/
def length (μ : NPartition N) : ℕ := (Finset.univ.filter (fun i : Fin N => μ.parts i ≠ 0)).card

@[simp]
theorem zero_length : (0 : NPartition N).length = 0 := by
  simp only [length, zero_parts, ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty]

/-- An N-partition has length 0 if and only if it is the zero partition. -/
@[simp]
theorem length_eq_zero_iff {μ : NPartition N} : μ.length = 0 ↔ μ = 0 := by
  constructor
  · intro h
    simp only [length, Finset.card_eq_zero] at h
    have h' : ∀ i : Fin N, μ.parts i = 0 := by
      intro i
      by_contra hne
      have hmem : i ∈ Finset.univ.filter (fun j : Fin N => μ.parts j ≠ 0) := by
        simp [Finset.mem_filter, hne]
      simp [h] at hmem
    ext i
    simp only [zero_parts_apply]
    exact h' i
  · intro h
    rw [h]
    exact zero_length

/-- A nonzero N-partition has positive length. -/
theorem length_pos_of_ne_zero {μ : NPartition N} (h : μ ≠ 0) : 0 < μ.length := by
  rw [Nat.pos_iff_ne_zero]
  exact fun hz => h (length_eq_zero_iff.mp hz)


/-- The length is at most N. -/
theorem length_le (μ : NPartition N) : μ.length ≤ N := by
  simp only [length]
  calc (Finset.univ.filter (fun i : Fin N => μ.parts i ≠ 0)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = N := Finset.card_fin N

/-- An N-partition is finite (has finitely many nonzero entries). -/
theorem finite_support (μ : NPartition N) : Set.Finite {i | μ.parts i ≠ 0} :=
  Set.toFinite _

/-! ## Constructor with explicit predicate -/

/-- Construct an NPartition from a function and a proof that it satisfies the
    weakly decreasing predicate (in the explicit form used in SchurBasics.lean
    and PieriJacobiTrudi.lean). -/
def mk' (parts : Fin N → ℕ)
    (h : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i) : NPartition N where
  parts := parts
  antitone := h

@[simp]
theorem mk'_parts (parts : Fin N → ℕ) (h : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i) :
    (mk' parts h).parts = parts := rfl

@[simp]
theorem mk'_antitone (parts : Fin N → ℕ) (h : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i) :
    (mk' parts h).antitone = h := rfl

/-! ## Part accessor -/

/-- The i-th part of an N-partition (alias for `parts i`).
    This matches the naming in SchurBasics.lean. -/
def part (μ : NPartition N) (i : Fin N) : ℕ := μ.parts i

@[simp]
theorem part_eq_parts (μ : NPartition N) (i : Fin N) : μ.part i = μ.parts i := rfl

/-! ## Bijection with Nat.Partition (Proposition prop.sf.Npar-as-par)

There is a bijection between partitions of length ≤ N and N-partitions.
This is formalized in MonomialSymmetric.lean as `NPartition.equivPartition`.
Here we provide the basic conversion functions. -/

/-- Helper lemma: filtering out zeros doesn't change the sum. -/
private lemma filter_ne_zero_sum (m : Multiset ℕ) : (m.filter (· ≠ 0)).sum = m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.filter_cons, Multiset.sum_cons]
    split_ifs with ha
    · simp [ih]
    · push Not at ha; simp [ha, ih]

/-- Convert a partition (as a `Nat.Partition`) to an N-partition by padding with zeros.
    Requires that the partition has at most N parts.

    This corresponds to the map in Proposition prop.sf.Npar-as-par:
    (μ₁, μ₂, ..., μ_ℓ) ↦ (μ₁, μ₂, ..., μ_ℓ, 0, 0, ..., 0) -/
def ofPartition {n : ℕ} (p : Nat.Partition n) (_hp : Multiset.card p.parts ≤ N) : NPartition N where
  parts := fun i =>
    let sorted := p.parts.sort (· ≥ ·)
    if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0
  antitone := by
    intro i j hij
    simp only
    split_ifs with hi hj hj
    · -- Both in range: use that sorted list is decreasing
      have hsorted : (p.parts.sort (· ≥ ·)).Pairwise (· ≥ ·) :=
        Multiset.pairwise_sort (r := (· ≥ ·)) p.parts
      exact List.Pairwise.rel_get_of_le hsorted hij
    · -- i in range, j out of range: contradiction since i ≤ j
      omega
    · -- i out of range: 0 ≤ anything
      exact Nat.zero_le _
    · -- both out of range
      exact le_refl 0

/-- Convert an N-partition to a partition by removing trailing zeros. -/
def toPartition (μ : NPartition N) : Nat.Partition μ.size where
  parts := (Finset.univ.val.map μ.parts).filter (· ≠ 0)
  parts_pos := by
    intro i hi
    simp only [Multiset.mem_filter, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and] at hi
    omega
  parts_sum := by
    simp only [size]
    have h : (Finset.univ.val.map μ.parts).sum = ∑ i, μ.parts i := by
      simp [Finset.sum_eq_multiset_sum]
    rw [← h]
    exact filter_ne_zero_sum _

set_option backward.isDefEq.respectTransparency false in
/-- The size of ofPartition p equals n (the sum of the original partition).
    (Proposition prop.sf.Npar-as-par, well-definedness)

    Label: prop.sf.Npar-as-par.size -/
theorem ofPartition_size {n : ℕ} (p : Nat.Partition n) (hp : Multiset.card p.parts ≤ N) :
    (ofPartition p hp).size = n := by
  simp only [size, ofPartition]
  set sorted := p.parts.sort (· ≥ ·) with hsorted_def
  have hlen : sorted.length = Multiset.card p.parts := Multiset.length_sort (· ≥ ·)
  have hsum : sorted.sum = n := by
    rw [← Multiset.sum_coe, Multiset.sort_eq p.parts (· ≥ ·)]
    exact p.parts_sum
  have hsorted_len : sorted.length ≤ N := by rw [hlen]; exact hp
  -- Key: the sum over Fin N equals the sum of the sorted list
  have key : ∑ i : Fin N, (if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0) = sorted.sum := by
    -- sorted.sum = ∑ i : Fin sorted.length, sorted.get i
    have h1 : sorted.sum = ∑ i : Fin sorted.length, sorted.get i := by
      conv_lhs => rw [← List.ofFn_get sorted]
      rw [List.sum_ofFn]
    rw [h1]
    -- Create an embedding from Fin sorted.length to Fin N
    have hemb : ∀ i : Fin sorted.length, (i : ℕ) < N := fun i => Nat.lt_of_lt_of_le i.isLt hsorted_len
    let emb : Fin sorted.length ↪ Fin N := ⟨fun i => ⟨i.val, hemb i⟩, by
      intro i j h; simp only [Fin.mk.injEq] at h; exact Fin.ext h⟩
    -- Split the sum over Fin N into indices in range and out of range
    have h2 : ∑ i : Fin N, (if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0) =
              ∑ i ∈ Finset.univ.map emb, (if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0) +
              ∑ i ∈ Finset.univ \ Finset.univ.map emb, (if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0) := by
      rw [← Finset.sum_union (Finset.disjoint_sdiff)]
      congr 1
      simp [Finset.union_sdiff_of_subset (Finset.subset_univ _)]
    rw [h2]
    -- The sum over indices out of range is 0
    have h3 : ∑ i ∈ Finset.univ \ Finset.univ.map emb, (if h : i.val < sorted.length then sorted.get ⟨i.val, h⟩ else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_map, true_and] at hi
      have : ¬ (i.val < sorted.length) := by
        intro hlt
        apply hi
        use ⟨i.val, hlt⟩
        simp [emb]
      simp [this]
    rw [h3, Nat.add_zero, Finset.sum_map]
    congr 1
    ext i
    simp [emb]
  rw [key, hsum]

/-- The number of non-zero parts of an N-partition is at most N.
    (Proposition prop.sf.Npar-as-par, boundedness) -/
theorem toPartition_card_le (μ : NPartition N) :
    Multiset.card μ.toPartition.parts ≤ N := by
  simp only [toPartition]
  calc Multiset.card ((Finset.univ.val.map μ.parts).filter (· ≠ 0))
      ≤ Multiset.card (Finset.univ.val.map μ.parts) :=
        Multiset.card_le_card (Multiset.filter_le _ _)
    _ = Multiset.card (Finset.univ (α := Fin N)).val := by rw [Multiset.card_map]
    _ = N := by simp

/-! ## Young Diagram (Definition def.sf.ydiag)

The Young diagram Y(λ) of an N-partition λ is the set of cells (i, j) where
i ∈ [N] and j ∈ [λ_i].

Note: Mathlib has `YoungDiagram` which is more general (infinite diagrams).
Here we define a version specific to N-partitions. -/

/-- The Young diagram Y(λ) of an N-partition λ is the set of cells (i, j) where
    i ∈ Fin N and j < λ_i.
    Definition def.sf.ydiag in the source.

    Note: Mathlib has `YoungDiagram` which is more general (infinite diagrams).
    Here we define a version specific to N-partitions. -/
def youngDiagram (μ : NPartition N) : Finset (Fin N × ℕ) :=
  Finset.univ.biUnion fun i => (Finset.range (μ.parts i)).map
    ⟨fun j => (i, j), fun _ _ h => by simp at h; exact h⟩

/-- Membership in a Young diagram: (i, j) ∈ Y(λ) iff j < λ_i.
    This is the 0-indexed version of the textbook condition j ∈ [λ_i].
    Definition def.sf.ydiag in the source. -/
theorem mem_youngDiagram {μ : NPartition N} {c : Fin N × ℕ} :
    c ∈ μ.youngDiagram ↔ c.2 < μ.parts c.1 := by
  simp only [youngDiagram, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨i, j, hj, rfl⟩
    exact hj
  · intro h
    exact ⟨c.1, c.2, h, rfl⟩

/-- Alternative characterization: membership in terms of the row index -/
theorem mem_youngDiagram' {μ : NPartition N} {i : Fin N} {j : ℕ} :
    (i, j) ∈ μ.youngDiagram ↔ j < μ.parts i := mem_youngDiagram

/-- The Young diagram is empty iff the partition is zero.
    This follows from the definition: Y(λ) = {(i,j) | j < λ_i}, which is empty iff all λ_i = 0. -/
theorem youngDiagram_eq_empty_iff {μ : NPartition N} :
    μ.youngDiagram = ∅ ↔ μ = 0 := by
  constructor
  · intro h
    ext i
    by_contra hne
    have : (i, 0) ∈ μ.youngDiagram := by
      rw [mem_youngDiagram]
      exact Nat.pos_of_ne_zero hne
    rw [h] at this
    exact Finset.notMem_empty _ this
  · intro h
    rw [h]
    ext c
    simp only [mem_youngDiagram, zero_parts_apply, Nat.not_lt_zero, Finset.notMem_empty]

/-- The Young diagram is nonempty iff the partition is nonzero -/
theorem youngDiagram_nonempty_iff {μ : NPartition N} :
    μ.youngDiagram.Nonempty ↔ μ ≠ 0 := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, youngDiagram_eq_empty_iff]

/-- The row i of the Young diagram has exactly μ.parts i elements.
    This captures the definition that row i has λ_i boxes. -/
theorem youngDiagram_row_card (μ : NPartition N) (i : Fin N) :
    (μ.youngDiagram.filter fun c => c.1 = i).card = μ.parts i := by
  have h : μ.youngDiagram.filter (fun c => c.1 = i) =
           (Finset.range (μ.parts i)).map ⟨fun j => (i, j), fun _ _ h => by simp at h; exact h⟩ := by
    ext c
    simp only [Finset.mem_filter, mem_youngDiagram, Finset.mem_map, Finset.mem_range,
               Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨hj, hi⟩
      refine ⟨c.2, by rw [hi] at hj; exact hj, ?_⟩
      rw [Prod.mk.injEq]
      exact ⟨hi.symm, rfl⟩
    · intro ⟨j, hj, hc⟩
      rw [Prod.mk.injEq] at hc
      constructor
      · rw [← hc.1, ← hc.2]; exact hj
      · exact hc.1.symm
  rw [h, Finset.card_map, Finset.card_range]

/-- Cells in a Young diagram have bounded column indices -/
theorem youngDiagram_snd_lt_parts {μ : NPartition N} {c : Fin N × ℕ}
    (h : c ∈ μ.youngDiagram) : c.2 < μ.parts c.1 := mem_youngDiagram.mp h

/-- The Young diagram is bounded by the first row length (when N > 0).
    Since λ is weakly decreasing, all columns are at most λ_0. -/
theorem youngDiagram_subset_prod (μ : NPartition N) (hN : 0 < N) :
    μ.youngDiagram ⊆ Finset.univ ×ˢ Finset.range (μ.parts ⟨0, hN⟩) := by
  intro c hc
  rw [mem_youngDiagram] at hc
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
  calc c.2 < μ.parts c.1 := hc
    _ ≤ μ.parts ⟨0, hN⟩ := μ.antitone (Nat.zero_le _)

/-- Version of `youngDiagram_subset_prod` using `[NeZero N]` typeclass.
    Useful for code that already has `[NeZero N]` in scope. -/
theorem youngDiagram_subset_prod' {N : ℕ} [NeZero N] (μ : NPartition N) :
    μ.youngDiagram ⊆ Finset.univ ×ˢ Finset.range (μ.parts 0) := by
  intro c hc
  rw [mem_youngDiagram] at hc
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
  calc c.2 < μ.parts c.1 := hc
    _ ≤ μ.parts 0 := μ.antitone (Fin.zero_le _)

/-- The cell (i, 0) is in the Young diagram iff μ_i > 0.
    This characterizes which rows are nonempty. -/
theorem mem_youngDiagram_zero_col {μ : NPartition N} {i : Fin N} :
    (i, 0) ∈ μ.youngDiagram ↔ 0 < μ.parts i := by
  rw [mem_youngDiagram]

/-- Decidability of membership in Young diagram -/
instance youngDiagram_decidableMem (μ : NPartition N) :
    DecidablePred (· ∈ μ.youngDiagram) := fun c =>
  decidable_of_iff (c.2 < μ.parts c.1) mem_youngDiagram.symm

set_option backward.isDefEq.respectTransparency false in
/-- The total number of cells in the Young diagram equals the size of the partition. -/
theorem youngDiagram_card (μ : NPartition N) : μ.youngDiagram.card = μ.size := by
  simp only [size]
  -- The Young diagram is the disjoint union of rows
  have hdisjoint : Set.PairwiseDisjoint (Finset.univ : Finset (Fin N))
      (fun i => (Finset.range (μ.parts i)).map ⟨fun j => (i, j), fun _ _ h => by simp at h; exact h⟩) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at ha hb
    obtain ⟨_, _, rfl⟩ := ha
    obtain ⟨_, _, rfl⟩ := hb
    simp only [Prod.mk.injEq, ne_eq, not_and]
    intro heq _
    exact hij heq
  rw [youngDiagram, Finset.card_biUnion hdisjoint]
  congr 1
  funext i
  simp only [Finset.card_map, Finset.card_range]

/-- The zero N-partition has empty Young diagram -/
@[simp]
theorem youngDiagram_zero : (0 : NPartition N).youngDiagram = ∅ := by
  ext c
  simp only [mem_youngDiagram, zero_parts_apply, Nat.not_lt_zero]
  simp

/-- μ ≤ ν is equivalent to Y(μ) ⊆ Y(ν).
    This is the key equivalence for partition containment. -/
theorem le_iff_youngDiagram_subset {μ ν : NPartition N} :
    μ ≤ ν ↔ μ.youngDiagram ⊆ ν.youngDiagram := by
  rw [le_iff]
  constructor
  · intro h c hc
    rw [mem_youngDiagram] at hc ⊢
    exact lt_of_lt_of_le hc (h c.1)
  · intro h i
    by_contra hne
    push Not at hne
    have hmem : (i, ν.parts i) ∈ μ.youngDiagram := by
      rw [mem_youngDiagram]
      exact hne
    have hnotmem : (i, ν.parts i) ∉ ν.youngDiagram := by
      rw [mem_youngDiagram]
      exact Nat.lt_irrefl _
    exact hnotmem (h hmem)

/-! ## Skew Young Diagram (Definition def.sf.skew-diag)

**This is the canonical `Finset` version of skew Young diagrams.**

The skew Young diagram Y(λ/μ) of two N-partitions λ and μ (where μ ⊆ λ componentwise)
is the set of cells in Y(λ) but not in Y(μ). In other words:
  Y(λ/μ) = {(i, j) | μ_i ≤ j < λ_i}

This uses 0-indexed columns (j starts from 0), following Mathlib/programming conventions.

**Alternative definitions:**
- `AlgebraicCombinatorics.skewYoungDiagram` in LittlewoodRichardson.lean returns a `Set`
  and uses 1-indexed columns: {(i, j) | μ_i < j ≤ λ_i}. This matches textbook conventions.
- `skewYoungDiagram` in SchurBasics.lean is a duplicate that requires `[NeZero N]`.
  Prefer this canonical version when possible.

The two indexing conventions are equivalent via the bijection (i, j) ↔ (i, j+1).
See `SchurBasics.skewYoungDiagram_equiv_LR` for the equivalence proof. -/

/-- The skew Young diagram Y(λ/μ) is the set difference Y(λ) \ Y(μ).
    This consists of cells (i, j) where μ_i ≤ j < λ_i.
    Definition def.sf.skew-diag in the source.

    **This is the canonical `Finset` version of skew Young diagrams.**
    
    Other versions exist for different use cases:
    - `AlgebraicCombinatorics.skewYoungDiagram` in LittlewoodRichardson.lean returns a `Set`
      and uses 1-indexed columns (textbook convention)
    - `skewYoungDiagram` in SchurBasics.lean is a duplicate that requires `[NeZero N]`
      (prefer this canonical version)

    **Indexing Convention**: Uses 0-indexed columns (Mathlib convention).
    - Here: (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i
    - LittlewoodRichardson: (i, j) ∈ Y(λ/μ) iff μ_i < j ≤ λ_i (1-indexed)
    
    The bijection (i, j) ↔ (i, j+1) converts between conventions.
    See `SchurBasics.skewYoungDiagram_equiv_LR` for the equivalence proof. -/
def skewYoungDiagram (lam mu : NPartition N) : Finset (Fin N × ℕ) :=
  lam.youngDiagram \ mu.youngDiagram

/-- Membership in a skew Young diagram: (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i.
    This is the 0-indexed version of the textbook condition μ_i < j ≤ λ_i. -/
theorem mem_skewYoungDiagram {lam mu : NPartition N} {c : Fin N × ℕ} :
    c ∈ skewYoungDiagram lam mu ↔ mu.parts c.1 ≤ c.2 ∧ c.2 < lam.parts c.1 := by
  simp only [skewYoungDiagram, Finset.mem_sdiff, mem_youngDiagram]
  constructor
  · intro ⟨hlt, hnotmem⟩
    exact ⟨Nat.not_lt.mp hnotmem, hlt⟩
  · intro ⟨hle, hlt⟩
    exact ⟨hlt, Nat.not_lt.mpr hle⟩

/-- Alternative characterization: membership in terms of row index -/
theorem mem_skewYoungDiagram' {lam mu : NPartition N} {i : Fin N} {j : ℕ} :
    (i, j) ∈ skewYoungDiagram lam mu ↔ j ∈ Finset.Ico (mu.parts i) (lam.parts i) := by
  rw [mem_skewYoungDiagram, Finset.mem_Ico]

/-- The skew diagram Y(λ/λ) is empty. -/
@[simp]
theorem skewYoungDiagram_self (lam : NPartition N) :
    skewYoungDiagram lam lam = ∅ := by
  ext c
  rw [mem_skewYoungDiagram]
  simp only [Finset.notMem_empty, iff_false, not_and, not_lt]
  intro h
  exact h

/-- The skew diagram Y(λ/0) equals Y(λ). -/
@[simp]
theorem skewYoungDiagram_zero' (lam : NPartition N) :
    skewYoungDiagram lam 0 = lam.youngDiagram := by
  ext c
  simp only [mem_skewYoungDiagram, mem_youngDiagram, zero_parts_apply]
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; exact ⟨Nat.zero_le _, h⟩

/-- The skew diagram is contained in the larger Young diagram. -/
theorem skewYoungDiagram_subset_youngDiagram (lam mu : NPartition N) :
    skewYoungDiagram lam mu ⊆ lam.youngDiagram := by
  intro c hc
  rw [mem_skewYoungDiagram] at hc
  rw [mem_youngDiagram]
  exact hc.2

/-- Decidability of membership in skew Young diagram -/
instance skewYoungDiagram_decidableMem (lam mu : NPartition N) :
    DecidablePred (· ∈ skewYoungDiagram lam mu) := fun c =>
  decidable_of_iff (mu.parts c.1 ≤ c.2 ∧ c.2 < lam.parts c.1) mem_skewYoungDiagram.symm

set_option backward.isDefEq.respectTransparency false in
/-- The cardinality of a skew Young diagram. -/
theorem skewYoungDiagram_card (lam mu : NPartition N) :
    (skewYoungDiagram lam mu).card = ∑ i, (lam.parts i - mu.parts i) := by
  simp only [skewYoungDiagram]
  -- Use the fact that Y(λ) \ Y(μ) partitions into rows
  have h : lam.youngDiagram \ mu.youngDiagram =
      Finset.univ.biUnion fun i =>
        (Finset.Ico (mu.parts i) (lam.parts i)).map
          ⟨fun j => (i, j), fun _ _ h => by simp at h; exact h⟩ := by
    ext c
    simp only [Finset.mem_sdiff, mem_youngDiagram, Finset.mem_biUnion, Finset.mem_univ,
               true_and, Finset.mem_map, Finset.mem_Ico, Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨hlt, hnotmem⟩
      refine ⟨c.1, c.2, ?_, rfl⟩
      exact ⟨Nat.not_lt.mp hnotmem, hlt⟩
    · intro ⟨i, j, ⟨hle, hlt⟩, heq⟩
      rw [← heq]
      exact ⟨hlt, Nat.not_lt.mpr hle⟩
  rw [h]
  have hdisjoint : Set.PairwiseDisjoint (Finset.univ : Finset (Fin N))
      (fun i => (Finset.Ico (mu.parts i) (lam.parts i)).map
        ⟨fun j => (i, j), fun _ _ h => by simp at h; exact h⟩) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_map, Finset.mem_Ico, Function.Embedding.coeFn_mk] at ha hb
    obtain ⟨_, _, rfl⟩ := ha
    obtain ⟨_, _, rfl⟩ := hb
    simp only [Prod.mk.injEq, ne_eq, not_and]
    intro heq _
    exact hij heq
  rw [Finset.card_biUnion hdisjoint]
  congr 1
  funext i
  simp only [Finset.card_map, Nat.card_Ico]

/-- The skew diagram is empty iff λ ≤ μ componentwise. -/
theorem skewYoungDiagram_eq_empty_iff {lam mu : NPartition N} :
    skewYoungDiagram lam mu = ∅ ↔ ∀ i, lam.parts i ≤ mu.parts i := by
  constructor
  · intro h i
    by_contra hne
    push Not at hne
    have : (i, mu.parts i) ∈ skewYoungDiagram lam mu := by
      rw [mem_skewYoungDiagram]
      exact ⟨le_refl _, hne⟩
    rw [h] at this
    exact Finset.notMem_empty _ this
  · intro h
    ext c
    simp only [Finset.notMem_empty, iff_false]
    rw [mem_skewYoungDiagram]
    intro ⟨hle, hlt⟩
    have := h c.1
    omega

/-! ## Row and Column Partitions

Special partitions consisting of a single row or column, used in the
Pieri rules and connections to symmetric functions. These are moved from
PieriJacobiTrudi.lean as part of the consolidation effort. -/

/-- The row partition (n, 0, 0, ..., 0) with n boxes in the first row.
    This is the partition corresponding to h_n (complete homogeneous symmetric polynomial).
    Requires N > 0 to have at least one row. -/
def rowPartition (N : ℕ) (n : ℕ) (_hN : 0 < N) : NPartition N where
  parts := fun i => if i.val = 0 then n else 0
  antitone := by
    intro i j hij
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceIte]
      split_ifs <;> omega
    · by_cases hj : j.val = 0
      · omega  -- i > 0 but j = 0 contradicts i ≤ j
      · simp only [hj, ↓reduceIte, hi]; rfl

/-- The row partition has size n. -/
@[simp]
theorem rowPartition_size (N : ℕ) (n : ℕ) (hN : 0 < N) :
    (rowPartition N n hN).size = n := by
  simp only [rowPartition, size]
  rw [Finset.sum_eq_single ⟨0, hN⟩]
  · simp
  · intro b _ hb
    simp only [ite_eq_right_iff]
    intro h
    exact (hb (Fin.ext h)).elim
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The first part of the row partition is n. -/
@[simp]
theorem rowPartition_parts_zero (N : ℕ) (n : ℕ) (hN : 0 < N) :
    (rowPartition N n hN).parts ⟨0, hN⟩ = n := by simp [rowPartition]

/-- All other parts of the row partition are 0. -/
@[simp]
theorem rowPartition_parts_pos (N : ℕ) (n : ℕ) (hN : 0 < N) (i : Fin N) (hi : 0 < i.val) :
    (rowPartition N n hN).parts i = 0 := by
  simp only [rowPartition]
  simp only [ite_eq_right_iff]
  omega

/-- The cardinality of elements of `Fin N` with value less than `n` is `n` (when `n ≤ N`).
    This is a specialized form of `Fin.card_filter_val_lt` for the case when `n ≤ N`.

    Used for proving properties of `colPartition`. -/
lemma card_filter_fin_val_lt (N n : ℕ) (hn : n ≤ N) :
    (Finset.univ.filter (fun i : Fin N => i.val < n)).card = n := by
  have h := @Fin.card_filter_val_lt N n
  simp only [min_eq_right hn] at h
  exact h

/-- The sum of indicators `if i.val < n then 1 else 0` over `Fin N` equals `n` (when `n ≤ N`).

    Used for proving properties of `colPartition`. -/
lemma sum_ite_fin_val_lt_eq (N n : ℕ) (hn : n ≤ N) :
    (∑ i : Fin N, if i.val < n then 1 else 0) = n := by
  have h1 : (∑ i : Fin N, if i.val < n then 1 else 0) =
            (Finset.univ.filter (fun i : Fin N => i.val < n)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [h1]
  exact card_filter_fin_val_lt N n hn

/-- The column partition (1, 1, ..., 1, 0, ..., 0) with n ones (n boxes in first column).
    This is the partition corresponding to e_n (elementary symmetric polynomial).
    Requires n ≤ N (can't have more rows than N). -/
def colPartition (N : ℕ) (n : ℕ) (_hn : n ≤ N) : NPartition N where
  parts := fun i => if i.val < n then 1 else 0
  antitone := by
    intro i j hij
    simp only
    by_cases hi : i.val < n
    · by_cases hj : j.val < n
      · simp [hi, hj]
      · simp [hi, hj]
    · by_cases hj : j.val < n
      · omega -- i.val >= n but j.val < n contradicts i ≤ j
      · simp [hi, hj]

/-- The column partition has size n. -/
@[simp]
theorem colPartition_size (N : ℕ) (n : ℕ) (hn : n ≤ N) :
    (colPartition N n hn).size = n := by
  simp only [colPartition, size]
  exact sum_ite_fin_val_lt_eq N n hn

/-- The first n parts of the column partition are 1. -/
@[simp]
theorem colPartition_parts_lt (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : i.val < n) :
    (colPartition N n hn).parts i = 1 := by simp [colPartition, hi]

/-- Parts beyond n in the column partition are 0. -/
@[simp]
theorem colPartition_parts_ge (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : n ≤ i.val) :
    (colPartition N n hn).parts i = 0 := by simp [colPartition, Nat.not_lt.mpr hi]

/-! ## Transpose of a partition

The transpose of a partition λ is denoted λᵗ and satisfies:
(λᵗ)ᵢ = |{j : λⱼ ≥ i+1}| for each i.

Since we work with fixed-length tuples, we define a predicate `IsTranspose`
that captures when two tuples represent transpose partitions. -/

/-- The transpose of a partition.
    See Exercise exe.pars.transpose in the source.
    The transpose λᵗ satisfies: (λᵗ)ᵢ = |{j : λⱼ ≥ i+1}| for each i.
    The length of the transpose equals the first (largest) part of λ. -/
noncomputable def transpose (μ : NPartition N) (hN : 0 < N) : NPartition (μ.parts ⟨0, hN⟩) where
  parts := fun i => (Finset.univ.filter fun j : Fin N => i.val + 1 ≤ μ.parts j).card
  antitone := by
    intro i j hij
    apply Finset.card_le_card
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact le_trans (Nat.add_le_add_right hij 1) hr

/-- Predicate asserting that `lamt` is the transpose of `lam`.
    The transpose λᵗ of a partition λ satisfies:
    (λᵗ)ᵢ = |{j : λⱼ ≥ i}| for each i.

    Since we work with fixed-length tuples, this predicate captures
    when two tuples represent transpose partitions (possibly with trailing zeros). -/
def IsTranspose {M : ℕ} (lam : Fin N → ℕ) (lamt : Fin M → ℕ) : Prop :=
  (∀ i : Fin M, lamt i = (Finset.univ.filter fun j : Fin N => i.val + 1 ≤ lam j).card) ∧
  (∀ j : Fin N, lam j = (Finset.univ.filter fun i : Fin M => j.val + 1 ≤ lamt i).card)

/-- The zero partition is its own transpose. -/
theorem zero_isTranspose : IsTranspose (fun _ : Fin N => 0) (fun _ : Fin N => 0) := by
  constructor
  · intro i
    have h : (Finset.univ.filter fun j : Fin N => i.val + 1 ≤ (0 : ℕ)) = ∅ := by
      simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
      intro j
      exact Nat.not_succ_le_zero _
    rw [h]
    simp
  · intro j
    have h : (Finset.univ.filter fun i : Fin N => j.val + 1 ≤ (0 : ℕ)) = ∅ := by
      simp only [Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
      intro i
      exact Nat.not_succ_le_zero _
    rw [h]
    simp

end NPartition

/-! ## Namespace aliases for migration

NOTE: The aliases below are commented out because they conflict with existing local
`NPartition` definitions in MonomialSymmetric.lean and PieriJacobiTrudi.lean.
To migrate a file to use the shared definition:
1. Import this file
2. Remove the local `structure NPartition` definition
3. Uncomment the appropriate alias below, OR use `open _root_.NPartition`

-- namespace AlgComb.SymmetricFunctions
-- abbrev NPartition := _root_.NPartition
-- end AlgComb.SymmetricFunctions

-- Note: We don't create a `SymmetricFunctions.NPartition` alias here because
-- PieriJacobiTrudi.lean already defines its own `SymmetricFunctions.NPartition`
-- structure. Migration of PieriJacobiTrudi.lean is tracked separately.
-/
