/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.Determinants.LGV2
import AlgebraicCombinatorics.SymmetricFunctions.OmegaInvolution
import AlgebraicCombinatorics.SymmetricFunctions.NPartition
import AlgebraicCombinatorics.SymmetricFunctions.LittlewoodRichardson

/-!
# The Pieri Rules and Jacobi-Trudi Identities

This file formalizes the Pieri rules for multiplying Schur polynomials by complete
homogeneous or elementary symmetric polynomials, and the Jacobi-Trudi identities
expressing skew Schur polynomials as determinants.

## Main definitions

* `NPartition`: An N-partition is a weakly decreasing N-tuple of nonnegative integers
* `NPartition.IsTranspose`: Predicate asserting that two partitions are transposes
* `SkewPartition`: A skew partition λ/μ is a pair of partitions with μ ⊆ λ
* `SkewPartition.isHorizontalStrip`: A skew partition is a horizontal strip if no two
  boxes in Y(λ/μ) lie in the same column
* `SkewPartition.isVerticalStrip`: A skew partition is a vertical strip if no two
  boxes in Y(λ/μ) lie in the same row
* `SkewPartition.isHorizontalNStrip`: A horizontal n-strip has exactly n boxes
* `SkewPartition.isVerticalNStrip`: A vertical n-strip has exactly n boxes
* `isHorizontalStripFun`: Canonical unbundled horizontal strip predicate with `(lam, mu)` order
* `isVerticalStripFun`: Canonical unbundled vertical strip predicate with `(lam, mu)` order
* `SSYT`: A semistandard Young tableau of shape λ
* `SkewSSYT`: A semistandard Young tableau of skew shape λ/μ
* `LatticePath`: A lattice path in ℤ² using north and east steps
* `Nipat`: A non-intersecting path tuple (for LGV lemma connection)

## Main results

* `pieri_horizontal`: h_n · s_μ = ∑_{λ/μ is horizontal n-strip} s_λ (Theorem thm.sf.pieri(a))
* `pieri_vertical`: e_n · s_μ = ∑_{λ/μ is vertical n-strip} s_λ (Theorem thm.sf.pieri(b))
* `horizontalStrip_iff_entries`: Characterization of horizontal strips via partition entries
    (Proposition prop.sf.strips.entries(a))
* `verticalStrip_iff_entries`: Characterization of vertical strips via partition entries
    (Proposition prop.sf.strips.entries(b))
* `jacobiTrudi_h`: s_{λ/μ} = det(h_{λᵢ - μⱼ - i + j}) (Theorem thm.sf.jt-h)
* `jacobiTrudi_e`: s_{λ/μ} = det(e_{λᵢᵗ - μⱼᵗ - i + j}) (Theorem thm.sf.jt-e)

## References

* Source: AlgebraicCombinatorics/tex/SymmetricFunctions/PieriJacobiTrudi.tex
* [Stanley, *Enumerative Combinatorics, Vol. 2*][Stanley-EC2]
* [Grinberg-Reiner, *Hopf algebras in combinatorics*][GriRei]

## Implementation notes

We work with N-partitions as length-N lists of weakly decreasing nonnegative integers.
Schur polynomials are defined via semistandard Young tableaux (SSYT).
The Jacobi-Trudi identities are proved using the Lindström-Gessel-Viennot lemma
(see AlgebraicCombinatorics/Determinants/LGV2.lean).

For h_n and e_n with negative n, we use the convention h_n = 0 and e_n = 0.

Note: In the source, M is the length of the partition tuples (for Jacobi-Trudi),
while N is the number of variables (entries in tableaux come from [N]).
We use a single parameter N for simplicity in this formalization.

### Strip Definition Conventions

There are three representations for horizontal/vertical strip predicates:

1. **Bundled (`SkewPartition.isHorizontalStrip`)**: Takes a `SkewPartition N` directly.
   Use when working with bundled skew partitions.

2. **Unbundled canonical (`isHorizontalStripFun`)**: Takes `(lam mu : Fin N → ℕ)` with
   argument order matching the mathematical notation λ/μ. **Preferred for new code.**

See `SkewPartition.isHorizontalStrip_iff_isHorizontalStripFun` for the equivalence lemma.
-/

open Finset BigOperators Matrix MvPolynomial

namespace SymmetricFunctions

variable {M N : ℕ} {R : Type*} [CommRing R]

/-!
## N-Partitions

An N-partition is a weakly decreasing N-tuple of nonnegative integers.

**DEPRECATION NOTE:** This is a local definition within the `SymmetricFunctions` namespace.
A canonical definition exists at the top level in `NPartition.lean` (see
`AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean`). New code should prefer
the canonical definition. This local definition uses `weaklyDecreasing` as the field name,
while the canonical definition uses `antitone` (which matches Mathlib conventions).
Both are semantically equivalent.

**Migration support:** An equivalence `NPartition.equivShared` is provided below
to convert between the local and shared definitions. This enables gradual migration:
- Use `NPartition.toShared` to convert local → shared
- Use `NPartition.ofShared` to convert shared → local
- Both preserve `parts`, `size`, and the `≤` relation

**Note:** `MonomialSymmetric.lean` and `SchurBasics.lean` have been migrated to use
the canonical definition. This file retains the local definition to avoid large
refactoring of the extensive APIs built on top of it.
-/

/-- An N-partition is a list of length N with weakly decreasing nonnegative entries.
    This corresponds to Definition def.sf.N-par in the source.

    **Note:** This is `SymmetricFunctions.NPartition`, a local definition.
    A canonical top-level `NPartition` exists in `NPartition.lean` with the same
    semantics (using `antitone` as the field name instead of `weaklyDecreasing`).
    See the section docstring for details. -/
structure NPartition (N : ℕ) where
  /-- The parts of the partition -/
  parts : Fin N → ℕ
  /-- The parts are weakly decreasing -/
  weaklyDecreasing : ∀ i j : Fin N, i ≤ j → parts j ≤ parts i

namespace NPartition

variable {N : ℕ}

/-- Two N-partitions are equal if their parts are equal. -/
@[ext]
theorem ext {lam mu : NPartition N} (h : lam.parts = mu.parts) : lam = mu := by
  cases lam; cases mu; simp_all

/-- Decidable equality for N-partitions. -/
instance instDecidableEq : DecidableEq (NPartition N) := fun lam mu =>
  decidable_of_iff (lam.parts = mu.parts) ⟨ext, fun h => h ▸ rfl⟩

/-- The zero partition (0, 0, ..., 0) -/
def zero (N : ℕ) : NPartition N where
  parts := fun _ => 0
  weaklyDecreasing := fun _ _ _ => le_refl 0

instance : Zero (NPartition N) := ⟨zero N⟩

/-- The size (sum of parts) of an N-partition -/
def size (lam : NPartition N) : ℕ := ∑ i, lam.parts i

/-- Containment of partitions: μ ⊆ λ means μᵢ ≤ λᵢ for all i -/
def partLE (mu lam : NPartition N) : Prop := ∀ i, mu.parts i ≤ lam.parts i

instance : LE (NPartition N) := ⟨partLE⟩

theorem le_def (mu lam : NPartition N) : mu ≤ lam ↔ ∀ i, mu.parts i ≤ lam.parts i := Iff.rfl

/-- Decidable instance for partition containment. -/
instance instDecidableLE : DecidableRel (fun (a b : NPartition N) => a ≤ b) :=
  fun _ _ => Fintype.decidableForallFintype

/-- The transpose of a partition.
    See Exercise exe.pars.transpose in the source.
    The transpose λᵗ satisfies: (λᵗ)ᵢ = |{j : λⱼ ≥ i+1}| for each i.
    The length of the transpose equals the first (largest) part of λ. -/
noncomputable def transpose (lam : NPartition N) (hN : 0 < N) : NPartition (lam.parts ⟨0, hN⟩) where
  parts := fun i => (Finset.univ.filter fun j : Fin N => i.val + 1 ≤ lam.parts j).card
  weaklyDecreasing := by
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

/-! ### Transpose Box Equivalence

For Young tableaux, the transpose property gives a key equivalence:
a box (i, j) is in the diagram λ iff box (j, i) is in the transpose λᵗ.
In the counting formulation: j + 1 ≤ λ_i iff i + 1 ≤ λᵗ_j.

This equivalence is fundamental for proving that the transpose preserves
the number of boxes and for the Bender-Knuth bijection. -/

/-- Double counting lemma: summing cardinalities of filter sets over rows equals
    summing over columns. This is used to prove that transpose preserves size. -/
private lemma sum_card_filter_eq_sum_card_filter {M : ℕ} (P : Fin N → Fin M → Prop)
    [∀ i j, Decidable (P i j)] :
    ∑ i : Fin N, (Finset.univ.filter fun j : Fin M => P i j).card =
    ∑ j : Fin M, (Finset.univ.filter fun i : Fin N => P i j).card := by
  have h1 : ∀ i : Fin N, (Finset.univ.filter fun j : Fin M => P i j).card =
      ∑ j : Fin M, if P i j then 1 else 0 := fun i => by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h2 : ∀ j : Fin M, (Finset.univ.filter fun i : Fin N => P i j).card =
      ∑ i : Fin N, if P i j then 1 else 0 := fun j => by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [h1, h2]
  rw [Finset.sum_comm]

/-- Helper: cardinality of {r : Fin N | r ≤ i} equals i.val + 1. -/
private lemma card_filter_le_fin (i : Fin N) :
    (Finset.univ.filter fun r : Fin N => r ≤ i).card = i.val + 1 := by
  have h : (Finset.univ.filter fun r : Fin N => r ≤ i) = Finset.Iic i := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
  rw [h, Fin.card_Iic]

/-- The transpose box equivalence: for weakly decreasing partitions λ and λᵗ
    satisfying the transpose property, box (i, j) is in λ iff (j, i) is in λᵗ.

    This is the key lemma that relates the two counting conditions:
    j + 1 ≤ λ_i ↔ i + 1 ≤ λᵗ_j

    The proof uses the weakly decreasing property: if j + 1 ≤ λ_i, then all
    rows 0, 1, ..., i have at least j + 1 boxes, so λᵗ_j ≥ i + 1. -/
theorem IsTranspose.box_equiv {M : ℕ} {lam : Fin N → ℕ} {lamt : Fin M → ℕ}
    (hlam_mono : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hlamt_mono : ∀ i j : Fin M, i ≤ j → lamt j ≤ lamt i)
    (htranspose : IsTranspose lam lamt)
    (i : Fin N) (j : Fin M) :
    j.val + 1 ≤ lam i ↔ i.val + 1 ≤ lamt j := by
  constructor
  · intro h
    rw [htranspose.1 j]
    have h_subset : (Finset.univ.filter fun r : Fin N => r ≤ i) ⊆
                    (Finset.univ.filter fun r : Fin N => j.val + 1 ≤ lam r) := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact le_trans h (hlam_mono r i hr)
    calc i.val + 1 = (Finset.univ.filter fun r : Fin N => r ≤ i).card := (card_filter_le_fin i).symm
      _ ≤ (Finset.univ.filter fun r : Fin N => j.val + 1 ≤ lam r).card := Finset.card_le_card h_subset
  · intro h
    rw [htranspose.2 i]
    have h_subset : (Finset.univ.filter fun c : Fin M => c ≤ j) ⊆
                    (Finset.univ.filter fun c : Fin M => i.val + 1 ≤ lamt c) := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact le_trans h (hlamt_mono c j hc)
    calc j.val + 1 = (Finset.univ.filter fun c : Fin M => c ≤ j).card := (card_filter_le_fin j).symm
      _ ≤ (Finset.univ.filter fun c : Fin M => i.val + 1 ≤ lamt c).card := Finset.card_le_card h_subset

/-- The transpose of a partition preserves the sum of parts (number of boxes).

    This is a fundamental property of Young tableau transposition:
    |λ| = |λᵗ| (the size of the partition equals the size of its transpose).

    The proof uses double counting: both ∑ᵢ λᵢ and ∑ⱼ λᵗⱼ count the total
    number of boxes in the Young diagram, just organized differently. -/
theorem IsTranspose.sum_eq {M : ℕ} {lam : Fin N → ℕ} {lamt : Fin M → ℕ}
    (hlam_mono : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hlamt_mono : ∀ i j : Fin M, i ≤ j → lamt j ≤ lamt i)
    (htranspose : IsTranspose lam lamt) :
    ∑ i : Fin N, lam i = ∑ j : Fin M, lamt j := by
  -- Use htranspose to rewrite both sides
  have h_lhs : ∑ i : Fin N, lam i =
      ∑ i : Fin N, (Finset.univ.filter fun j : Fin M => i.val + 1 ≤ lamt j).card := by
    apply Finset.sum_congr rfl
    intro i _
    exact htranspose.2 i
  have h_rhs : ∑ j : Fin M, lamt j =
      ∑ j : Fin M, (Finset.univ.filter fun i : Fin N => j.val + 1 ≤ lam i).card := by
    apply Finset.sum_congr rfl
    intro j _
    exact htranspose.1 j
  rw [h_lhs, h_rhs]
  -- The key: use box_equiv to show the predicates are equivalent
  have h_equiv : ∀ i j, (i.val + 1 ≤ lamt j) ↔ (j.val + 1 ≤ lam i) := fun i j =>
    (htranspose.box_equiv hlam_mono hlamt_mono i j).symm
  -- Rewrite LHS using the equivalence
  have h_filter_eq : ∀ i : Fin N,
      (Finset.univ.filter fun j : Fin M => i.val + 1 ≤ lamt j) =
      (Finset.univ.filter fun j : Fin M => j.val + 1 ≤ lam i) := fun i => by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_equiv i j
  simp_rw [h_filter_eq]
  exact sum_card_filter_eq_sum_card_filter (fun i j => j.val + 1 ≤ lam i)

/-! ### Row and Column Partitions

Special partitions consisting of a single row or column, used in the
alternative proof of Pieri rules via Littlewood-Richardson. -/

/-- The row partition (n, 0, 0, ..., 0) with n boxes in the first row.
    This is the partition corresponding to h_n (complete homogeneous symmetric polynomial).
    Requires N > 0 to have at least one row. -/
def rowPartition (N : ℕ) (n : ℕ) (_hN : 0 < N) : NPartition N where
  parts := fun i => if i.val = 0 then n else 0
  weaklyDecreasing := by
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

/-- The column partition (1, 1, ..., 1, 0, ..., 0) with n ones (n boxes in first column).
    This is the partition corresponding to e_n (elementary symmetric polynomial).
    Requires n ≤ N (can't have more rows than N). -/
def colPartition (N : ℕ) (n : ℕ) (_hn : n ≤ N) : NPartition N where
  parts := fun i => if i.val < n then 1 else 0
  weaklyDecreasing := by
    intro i j hij
    by_cases hi : i.val < n
    · split_ifs <;> omega
    · split_ifs <;> omega

/-- The column partition has size n. -/
@[simp]
theorem colPartition_size (N : ℕ) (n : ℕ) (hn : n ≤ N) :
    (colPartition N n hn).size = n := by
  simp only [colPartition, size]
  exact _root_.NPartition.sum_ite_fin_val_lt_eq N n hn

/-- The first n parts of the column partition are 1. -/
@[simp]
theorem colPartition_parts_lt (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : i.val < n) :
    (colPartition N n hn).parts i = 1 := by simp [colPartition, hi]

/-- Parts beyond n in the column partition are 0. -/
@[simp]
theorem colPartition_parts_ge (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : n ≤ i.val) :
    (colPartition N n hn).parts i = 0 := by simp [colPartition, Nat.not_lt.mpr hi]

end NPartition

/-!
## NPartition Type Equivalence

This section provides an equivalence between the local `SymmetricFunctions.NPartition`
and the shared `_root_.NPartition` definition from `NPartition.lean`.

This enables gradual migration: code can use the local definition while having
access to theorems proved about the shared definition (and vice versa).
-/

section NPartitionEquiv

variable {N : ℕ}

/-- Convert a local `SymmetricFunctions.NPartition` to the shared `_root_.NPartition`. -/
def NPartition.toShared (μ : NPartition N) : _root_.NPartition N :=
  _root_.NPartition.mk' μ.parts μ.weaklyDecreasing

/-- Convert a shared `_root_.NPartition` to the local `SymmetricFunctions.NPartition`. -/
def NPartition.ofShared (μ : _root_.NPartition N) : NPartition N where
  parts := μ.parts
  weaklyDecreasing := μ.weaklyDecreasing

/-- Converting to shared and back is the identity. -/
@[simp]
theorem NPartition.ofShared_toShared (μ : NPartition N) :
    NPartition.ofShared (NPartition.toShared μ) = μ := by
  ext; rfl

/-- Converting from shared and back is the identity. -/
@[simp]
theorem NPartition.toShared_ofShared (μ : _root_.NPartition N) :
    NPartition.toShared (NPartition.ofShared μ) = μ := by
  ext; rfl

/-- The equivalence between local and shared NPartition types. -/
def NPartition.equivShared : NPartition N ≃ _root_.NPartition N where
  toFun := NPartition.toShared
  invFun := NPartition.ofShared
  left_inv := NPartition.ofShared_toShared
  right_inv := NPartition.toShared_ofShared

/-- Converting to shared preserves parts. -/
@[simp]
theorem NPartition.toShared_parts (μ : NPartition N) :
    (NPartition.toShared μ).parts = μ.parts := rfl

/-- Converting from shared preserves parts. -/
@[simp]
theorem NPartition.ofShared_parts (μ : _root_.NPartition N) :
    (NPartition.ofShared μ).parts = μ.parts := rfl

/-- Converting to shared preserves size. -/
@[simp]
theorem NPartition.toShared_size (μ : NPartition N) :
    (NPartition.toShared μ).size = μ.size := rfl

/-- Converting from shared preserves size. -/
@[simp]
theorem NPartition.ofShared_size (μ : _root_.NPartition N) :
    (NPartition.ofShared μ).size = μ.size := rfl

/-- The zero partitions correspond under the equivalence. -/
@[simp]
theorem NPartition.toShared_zero : NPartition.toShared (0 : NPartition N) = 0 := by
  ext i; rfl

/-- The zero partitions correspond under the equivalence. -/
@[simp]
theorem NPartition.ofShared_zero : NPartition.ofShared (0 : _root_.NPartition N) = 0 := by
  ext i; rfl

/-- The equivalence preserves the LE relation. -/
theorem NPartition.toShared_le_iff (μ ν : NPartition N) :
    NPartition.toShared μ ≤ NPartition.toShared ν ↔ μ ≤ ν := by
  simp only [_root_.NPartition.le_def, NPartition.le_def, NPartition.toShared_parts]

/-- The equivalence preserves the LE relation. -/
theorem NPartition.ofShared_le_iff (μ ν : _root_.NPartition N) :
    NPartition.ofShared μ ≤ NPartition.ofShared ν ↔ μ ≤ ν := by
  simp only [_root_.NPartition.le_def, NPartition.le_def, NPartition.ofShared_parts]

end NPartitionEquiv

/-!
## Transpose Bridge Lemmas

These lemmas connect the local `SymmetricFunctions.NPartition.transpose` with the
canonical `_root_.NPartition.transpose` via the `toShared`/`ofShared` equivalence.

Both definitions compute the same thing: (λᵗ)ᵢ = |{j : λⱼ ≥ i+1}| for each i.
The bridge lemmas make this equivalence explicit, enabling code using the local
definition to interoperate with theorems proved about the canonical definition.
-/

section TransposeBridge

variable {N : ℕ}

/-- The transpose of the local `SymmetricFunctions.NPartition` equals the transpose of
    the shared `_root_.NPartition` (via the `toShared`/`ofShared` equivalence).

    This is the bridge lemma connecting the two transpose definitions.
    Since both definitions compute (λᵗ)ᵢ = |{j : λⱼ ≥ i+1}|, they are definitionally equal
    when the parts are the same. -/
theorem NPartition.transpose_toShared_eq (lam : NPartition N) (hN : 0 < N) :
    (lam.transpose hN).toShared = (lam.toShared).transpose hN := by
  ext i
  rfl

/-- The transpose of a shared `_root_.NPartition` converted to local equals the local
    transpose of the converted partition.

    This is the inverse direction of the bridge lemma. -/
theorem NPartition.ofShared_transpose_eq (lam : _root_.NPartition N) (hN : 0 < N) :
    NPartition.ofShared (lam.transpose hN) = (NPartition.ofShared lam).transpose hN := by
  ext i
  rfl

/-- The transpose commutes with the equivalence. -/
theorem NPartition.equivShared_transpose (lam : NPartition N) (hN : 0 < N) :
    NPartition.equivShared (lam.transpose hN) =
      (NPartition.equivShared lam).transpose hN :=
  NPartition.transpose_toShared_eq lam hN

end TransposeBridge

/-!
## Helper Lemmas for Sym-SSYT Bijection

These lemmas establish the connection between `Sym (Fin N) n` (multisets of size n)
and weakly increasing sequences, which is key for proving that h_n equals the
Schur polynomial of the row partition.
-/

section SymSSYTHelpers

variable {N : ℕ}

/-- Product over a multiset equals product over its sorted list.
    Since sorting preserves the multiset, the products are equal. -/
private lemma multiset_prod_eq_sorted_prod {α : Type*} [LinearOrder α] {β : Type*} [CommMonoid β]
    (m : Multiset α) (f : α → β) :
    (m.map f).prod = ((m.sort (· ≤ ·)).map f).prod := by
  have h : (m.sort (· ≤ ·) : Multiset α) = m := Multiset.sort_eq m (· ≤ ·)
  conv_lhs => rw [← h]
  rfl

/-- Product over a list equals product over Fin indices.
    This converts a list product to a fintype product. -/
private lemma list_prod_map_eq_fin_prod {α : Type*} {β : Type*} [CommMonoid β]
    (L : List α) (f : α → β) :
    (L.map f).prod = ∏ j : Fin L.length, f (L.get j) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Fin.prod_univ_succ]
    conv_lhs => rw [ih]
    rfl

/-- A sorted multiset gives a weakly increasing sequence.
    This is because `Multiset.sort` produces a sorted list. -/
private lemma sorted_weakly_increasing {α : Type*} [LinearOrder α] (m : Multiset α) :
    ∀ i j : Fin (m.sort (· ≤ ·)).length, i ≤ j →
      (m.sort (· ≤ ·)).get i ≤ (m.sort (· ≤ ·)).get j := by
  intro i j hij
  apply List.Pairwise.rel_get_of_le
  · exact Multiset.pairwise_sort m (· ≤ ·)
  · exact hij

/-- Convert a Sym to a weakly increasing function.
    The sorted list of a multiset gives a canonical weakly increasing sequence. -/
def symToWeaklyIncreasing (n : ℕ) (s : Sym (Fin N) n) :
    { f : Fin n → Fin N // ∀ i j, i ≤ j → f i ≤ f j } := by
  have hlen : (s.1.sort (· ≤ ·)).length = n := by rw [Multiset.length_sort]; exact s.2
  refine ⟨fun i => (s.1.sort (· ≤ ·)).get ⟨i.val, by rw [hlen]; exact i.isLt⟩, ?_⟩
  intro i j hij
  apply sorted_weakly_increasing
  exact hij

/-- The monomial from a Sym equals the product over its weakly increasing representation.
    This is a key lemma for connecting h_n to Schur polynomials. -/
theorem sym_monomial_eq_weaklyIncreasing_prod {R : Type*} [CommRing R] (n : ℕ) (s : Sym (Fin N) n) :
    (s.1.map (MvPolynomial.X (R := R))).prod =
    ∏ j : Fin n, MvPolynomial.X ((symToWeaklyIncreasing n s).val j) := by
  rw [multiset_prod_eq_sorted_prod]
  rw [list_prod_map_eq_fin_prod]
  have hlen : (s.1.sort (· ≤ ·)).length = n := by rw [Multiset.length_sort]; exact s.2
  apply Finset.prod_equiv (finCongr hlen)
  · simp
  · intro j _
    simp [finCongr, symToWeaklyIncreasing]

/-- Convert a weakly increasing function back to a Sym.
    This is the inverse of symToWeaklyIncreasing. -/
def weaklyIncreasingToSym (n : ℕ) (f : Fin n → Fin N) : Sym (Fin N) n :=
  ⟨Multiset.ofList ((List.finRange n).map f), by simp⟩

/-- The round-trip from Sym to weakly increasing and back gives the same Sym.
    This shows that symToWeaklyIncreasing and weaklyIncreasingToSym form a bijection. -/
theorem weaklyIncreasingToSym_symToWeaklyIncreasing (n : ℕ) (s : Sym (Fin N) n) :
    weaklyIncreasingToSym n (symToWeaklyIncreasing n s).val = s := by
  unfold weaklyIncreasingToSym symToWeaklyIncreasing
  congr 1
  have hlen : (s.1.sort (· ≤ ·)).length = n := by rw [Multiset.length_sort]; exact s.2
  -- Show the lists are equal as multisets
  have h1 : ((List.finRange n).map (fun i => (s.1.sort (· ≤ ·)).get ⟨i.val, by rw [hlen]; exact i.isLt⟩)) =
            s.1.sort (· ≤ ·) := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_finRange, hlen]
    · intro i hi1 hi2
      simp only [List.getElem_map, List.getElem_finRange, List.get_eq_getElem]
      simp only [Fin.cast, Fin.val_mk]
  simp only [h1]
  exact Multiset.sort_eq s.1 (· ≤ ·)

/-- Sorting a weakly increasing list gives back the same list.
    This is key for the surjectivity of symToRowSSYT. -/
private lemma sort_weaklyIncreasing_list_eq {n : ℕ} (f : Fin n → Fin N)
    (hf : ∀ i j, i ≤ j → f i ≤ f j) :
    ((Multiset.ofList ((List.finRange n).map f)).sort (· ≤ ·)) = (List.finRange n).map f := by
  rw [Multiset.coe_sort]
  apply List.mergeSort_eq_self
  rw [List.pairwise_map]
  apply List.Pairwise.imp _ (List.pairwise_lt_finRange n)
  intro a b hab
  exact hf a b (le_of_lt hab)

end SymSSYTHelpers

/-!
## Skew Partitions and Strips

Definition def.sf.strips: A skew partition λ/μ is a pair (μ, λ) of N-partitions.
Horizontal and vertical strips are special cases where the skew diagram has
no two boxes in the same column or row, respectively.
-/

/-- A skew partition λ/μ is a pair of N-partitions with μ ⊆ λ.
    Definition def.sf.strips(a). -/
structure SkewPartition (N : ℕ) where
  /-- The outer partition λ -/
  outer : NPartition N
  /-- The inner partition μ -/
  inner : NPartition N
  /-- The containment condition μ ⊆ λ -/
  contained : inner ≤ outer

namespace SkewPartition

variable {N : ℕ}

/-- The size of a skew partition |Y(λ/μ)| = |λ| - |μ| -/
def size (s : SkewPartition N) : ℕ := s.outer.size - s.inner.size

/-- A skew partition λ/μ is a horizontal strip if no two boxes of Y(λ/μ)
    lie in the same column.
    Definition def.sf.strips(b).

    **Bundled definition:** This is the preferred version when working with `SkewPartition N`.

    **Related definitions:**
    - `isHorizontalStripFun`: Canonical unbundled version with `(lam, mu)` argument order

    **Equivalence:** `s.isHorizontalStrip ↔ isHorizontalStripFun s.outer.parts s.inner.parts`
    (see `SkewPartition.isHorizontalStrip_iff_isHorizontalStripFun`) -/
def isHorizontalStrip (s : SkewPartition N) : Prop :=
  ∀ i : Fin N, ∀ hi : i.val + 1 < N,
    s.inner.parts i ≥ s.outer.parts ⟨i.val + 1, hi⟩

/-- A skew partition λ/μ is a vertical strip if no two boxes of Y(λ/μ)
    lie in the same row.
    Definition def.sf.strips(c).

    **Bundled definition:** This is the preferred version when working with `SkewPartition N`.

    **Related definitions:**
    - `isVerticalStripFun`: Canonical unbundled version with `(lam, mu)` argument order

    **Equivalence:** `s.isVerticalStrip ↔ isVerticalStripFun s.outer.parts s.inner.parts`
    (see `SkewPartition.isVerticalStrip_iff_isVerticalStripFun`) -/
def isVerticalStrip (s : SkewPartition N) : Prop :=
  ∀ i : Fin N, s.outer.parts i ≤ s.inner.parts i + 1

/-- A skew partition is a horizontal n-strip if it is a horizontal strip
    with |Y(λ/μ)| = n.
    Definition def.sf.strips(d). -/
def isHorizontalNStrip (s : SkewPartition N) (n : ℕ) : Prop :=
  s.isHorizontalStrip ∧ s.size = n

/-- A skew partition is a vertical n-strip if it is a vertical strip
    with |Y(λ/μ)| = n.
    Definition def.sf.strips(e). -/
def isVerticalNStrip (s : SkewPartition N) (n : ℕ) : Prop :=
  s.isVerticalStrip ∧ s.size = n

/-!
### Characterization of Strips

Proposition prop.sf.strips.entries: Horizontal and vertical strips can be
characterized in terms of the entries of the partitions.
-/

/-- Horizontal strip characterization (Proposition prop.sf.strips.entries(a))
    Label: prop.sf.strips.entries

    A skew partition λ/μ is a horizontal strip iff
    λ₁ ≥ μ₁ ≥ λ₂ ≥ μ₂ ≥ ⋯ ≥ λ_N ≥ μ_N. -/
theorem horizontalStrip_iff_entries (s : SkewPartition N) :
    s.isHorizontalStrip ↔
      ∀ i : Fin N, ∀ hi : i.val + 1 < N,
        s.outer.parts i ≥ s.inner.parts i ∧
        s.inner.parts i ≥ s.outer.parts ⟨i.val + 1, hi⟩ := by
  constructor
  · intro h i hi
    exact ⟨s.contained i, h i hi⟩
  · intro h i hi
    exact (h i hi).2

/-- Vertical strip characterization (Proposition prop.sf.strips.entries(b))
    Label: prop.sf.strips.entries

    A skew partition λ/μ is a vertical strip iff
    μᵢ ≤ λᵢ ≤ μᵢ + 1 for each i ∈ [N]. -/
theorem verticalStrip_iff_entries (s : SkewPartition N) :
    s.isVerticalStrip ↔
      ∀ i : Fin N, s.inner.parts i ≤ s.outer.parts i ∧
        s.outer.parts i ≤ s.inner.parts i + 1 := by
  constructor
  · intro h i
    exact ⟨s.contained i, h i⟩
  · intro h i
    exact (h i).2

/-!
### Decidability and Basic API for Strips

These instances and lemmas make the strip predicates computable and provide
basic API for working with strips.
-/

/-- Decidable instance for `isHorizontalStrip`. -/
instance instDecidableIsHorizontalStrip (s : SkewPartition N) : Decidable s.isHorizontalStrip :=
  Fintype.decidableForallFintype

/-- Decidable instance for `isVerticalStrip`. -/
instance instDecidableIsVerticalStrip (s : SkewPartition N) : Decidable s.isVerticalStrip :=
  Fintype.decidableForallFintype

/-- Decidable instance for `isHorizontalNStrip`. -/
instance instDecidableIsHorizontalNStrip (s : SkewPartition N) (n : ℕ) :
    Decidable (s.isHorizontalNStrip n) :=
  instDecidableAnd

/-- Decidable instance for `isVerticalNStrip`. -/
instance instDecidableIsVerticalNStrip (s : SkewPartition N) (n : ℕ) :
    Decidable (s.isVerticalNStrip n) :=
  instDecidableAnd

/-- A horizontal n-strip has size n. -/
theorem isHorizontalNStrip.size_eq {s : SkewPartition N} {n : ℕ} (h : s.isHorizontalNStrip n) :
    s.size = n := h.2

/-- A vertical n-strip has size n. -/
theorem isVerticalNStrip.size_eq {s : SkewPartition N} {n : ℕ} (h : s.isVerticalNStrip n) :
    s.size = n := h.2

/-- A horizontal n-strip is a horizontal strip. -/
theorem isHorizontalNStrip.isHorizontalStrip {s : SkewPartition N} {n : ℕ}
    (h : s.isHorizontalNStrip n) : s.isHorizontalStrip := h.1

/-- A vertical n-strip is a vertical strip. -/
theorem isVerticalNStrip.isVerticalStrip {s : SkewPartition N} {n : ℕ}
    (h : s.isVerticalNStrip n) : s.isVerticalStrip := h.1

/-- The empty skew partition (λ = μ) is a horizontal 0-strip. -/
theorem empty_isHorizontalNStrip (lam : NPartition N) :
    (⟨lam, lam, fun _ => le_refl _⟩ : SkewPartition N).isHorizontalNStrip 0 := by
  constructor
  · intro i hi
    exact lam.weaklyDecreasing ⟨i.val, i.isLt⟩ ⟨i.val + 1, hi⟩ (Nat.le_succ _)
  · simp [size, NPartition.size]

/-- The empty skew partition (λ = μ) is a vertical 0-strip. -/
theorem empty_isVerticalNStrip (lam : NPartition N) :
    (⟨lam, lam, fun _ => le_refl _⟩ : SkewPartition N).isVerticalNStrip 0 := by
  constructor
  · intro i
    exact Nat.le_succ _
  · simp [size, NPartition.size]

/-!
### Examples from the textbook

These examples verify that our definitions match Definition def.sf.strips from
the source (AlgebraicCombinatorics/tex/SymmetricFunctions/PieriJacobiTrudi.tex).
-/

section Examples

/-- Example (a) from the textbook: λ = (8,7,4,3), μ = (7,4,4,1).
    This is a horizontal 6-strip but NOT a vertical strip. -/
def exampleA_outer : NPartition 4 where
  parts := ![8, 7, 4, 3]
  weaklyDecreasing := by decide

def exampleA_inner : NPartition 4 where
  parts := ![7, 4, 4, 1]
  weaklyDecreasing := by decide

def exampleA : SkewPartition 4 where
  outer := exampleA_outer
  inner := exampleA_inner
  contained := by decide

-- This is a horizontal strip
example : exampleA.isHorizontalStrip := by decide

-- This is NOT a vertical strip (row 2 has 3 boxes: 7-4=3 > 1)
example : ¬exampleA.isVerticalStrip := by decide

-- This is a horizontal 6-strip
example : exampleA.isHorizontalNStrip 6 := by decide

/-- Example (b) from the textbook: λ = (3,3,2,1), μ = (2,2,1,0).
    This is a vertical 4-strip but NOT a horizontal strip. -/
def exampleB_outer : NPartition 4 where
  parts := ![3, 3, 2, 1]
  weaklyDecreasing := by decide

def exampleB_inner : NPartition 4 where
  parts := ![2, 2, 1, 0]
  weaklyDecreasing := by decide

def exampleB : SkewPartition 4 where
  outer := exampleB_outer
  inner := exampleB_inner
  contained := by decide

-- This is a vertical strip (each row has at most 1 box: λᵢ ≤ μᵢ + 1)
example : exampleB.isVerticalStrip := by decide

-- This is NOT a horizontal strip (column 3 has 2 boxes)
example : ¬exampleB.isHorizontalStrip := by decide

-- This is a vertical 4-strip
example : exampleB.isVerticalNStrip 4 := by decide

/-- Example (c) from the textbook: λ = (4,3,1,1), μ = (3,2,1,0).
    This is BOTH a horizontal 3-strip AND a vertical 3-strip. -/
def exampleC_outer : NPartition 4 where
  parts := ![4, 3, 1, 1]
  weaklyDecreasing := by decide

def exampleC_inner : NPartition 4 where
  parts := ![3, 2, 1, 0]
  weaklyDecreasing := by decide

def exampleC : SkewPartition 4 where
  outer := exampleC_outer
  inner := exampleC_inner
  contained := by decide

-- This is both horizontal and vertical
example : exampleC.isHorizontalStrip := by decide
example : exampleC.isVerticalStrip := by decide

-- This is both a horizontal 3-strip and a vertical 3-strip
example : exampleC.isHorizontalNStrip 3 := by decide
example : exampleC.isVerticalNStrip 3 := by decide

/-- Example (d) from the textbook: λ = (3,3,2,1), μ = (1,1,1,1).
    This is NEITHER a horizontal strip NOR a vertical strip. -/
def exampleD_outer : NPartition 4 where
  parts := ![3, 3, 2, 1]
  weaklyDecreasing := by decide

def exampleD_inner : NPartition 4 where
  parts := ![1, 1, 1, 1]
  weaklyDecreasing := by decide

def exampleD : SkewPartition 4 where
  outer := exampleD_outer
  inner := exampleD_inner
  contained := by decide

-- This is neither horizontal nor vertical
example : ¬exampleD.isHorizontalStrip := by decide
example : ¬exampleD.isVerticalStrip := by decide

end Examples

end SkewPartition

/-!
## Schur Polynomials

We use Mathlib's symmetric polynomial infrastructure and define Schur polynomials
via semistandard Young tableaux (SSYT).
-/

/-- A semistandard Young tableau (SSYT) of shape λ with entries in [N].
    The entries are weakly increasing along rows and strictly increasing down columns.
    Definition def.sf.ssyt.

    **Note:** This is one of two SSYT definitions in this project:
    - **This definition** (`SymmetricFunctions.SSYT`): Uses dependent types
      `entries : (i : Fin N) → (j : Fin (lam.parts i)) → Fin N`. Standalone structure.
      No `[NeZero N]` requirement. Field names: `rowWeak`, `colStrict`.
    - **Alternative definition** (`SchurBasics.SSYT` in `SchurBasics.lean`): Uses
      `entry : Fin N × ℕ → Fin N` with a support condition. Extends `YoungTableau`.
      Requires `[NeZero N]`. Field names: `row_weak`, `col_strict`.

    The equivalence between these definitions is established in `SSYTEquiv.lean` via
    `SSYTEquiv.ssytEquiv`. Use `SSYTEquiv.toSchurBasicsSSYT` and `SSYTEquiv.toSFSSYT`
    to convert between representations.

    **When to use which:**
    - Use this definition when the dependent type ensures bounds checking at compile time,
      or when `[NeZero N]` is not available.
    - Use `SchurBasics.SSYT` when working with cell coordinates `(i, j)` directly, or when
      extending the `YoungTableau` structure is beneficial. -/
structure SSYT (lam : NPartition N) where
  /-- The entries of the tableau -/
  entries : (i : Fin N) → (j : Fin (lam.parts i)) → Fin N
  /-- Entries are weakly increasing along rows -/
  rowWeak : ∀ i : Fin N, ∀ j k : Fin (lam.parts i), j ≤ k →
    entries i j ≤ entries i k
  /-- Entries are strictly increasing down columns -/
  colStrict : ∀ i : Fin N, ∀ hi : i.val + 1 < N, ∀ j : Fin (lam.parts i),
    ∀ hj : j.val < (lam.parts ⟨i.val + 1, hi⟩),
    entries i j < entries ⟨i.val + 1, hi⟩ ⟨j.val, hj⟩

/-- A semistandard Young tableau of skew shape λ/μ with entries in [N].
    Definition def.sf.skew-schur.

    For a skew tableau, the column-strict condition requires that entries
    are strictly increasing down columns, where column j of Y(λ/μ) consists
    of boxes (i, j) with μᵢ < j ≤ λᵢ.

    **Note:** This is one of two SkewSSYT definitions in this project:
    - **This definition** (`SymmetricFunctions.SkewSSYT`): Uses dependent types. Takes
      `s : SkewPartition N` as a single bundled argument. No `[NeZero N]` requirement.
      Field names: `rowWeak`, `colStrict`.
    - **Alternative definition** (`SchurBasics.SkewSSYT` in `SchurBasics.lean`): Uses
      `entry : Fin N × ℕ → Fin N` with a support condition. Extends `SkewYoungTableau`.
      Takes `lam mu : NPartition N` as separate arguments. Requires `[NeZero N]`.
      Field names: `row_weak`, `col_strict`.

    See `SSYTEquiv.lean` for conversions between representations. -/
structure SkewSSYT (s : SkewPartition N) where
  /-- The entries of the tableau, only for boxes in Y(λ/μ).
      Entry (i, k) corresponds to box (i, μᵢ + k + 1) in Y(λ/μ). -/
  entries : (i : Fin N) → (k : Fin (s.outer.parts i - s.inner.parts i)) → Fin N
  /-- Entries are weakly increasing along rows -/
  rowWeak : ∀ i : Fin N, ∀ j k : Fin (s.outer.parts i - s.inner.parts i),
    j ≤ k → entries i j ≤ entries i k
  /-- Entries are strictly increasing down columns.
      If boxes (i, c) and (i', c) are both in Y(λ/μ) with i < i', then
      T(i, c) < T(i', c). Here c = μᵢ + k + 1 for some k.
      The condition checks: for row i and column offset k, if row i+1 also
      contains column μᵢ + k + 1 (i.e., μᵢ + k + 1 > μᵢ₊₁ and μᵢ + k + 1 ≤ λᵢ₊₁),
      then the entry in row i is strictly less than the entry in row i+1. -/
  colStrict : ∀ i : Fin N, ∀ hi : i.val + 1 < N,
    ∀ k : Fin (s.outer.parts i - s.inner.parts i),
    -- The absolute column is μᵢ + k + 1. For this to be in row i+1:
    -- 1. μᵢ + k + 1 > μᵢ₊₁ (column is after the inner partition in row i+1)
    -- 2. μᵢ + k + 1 ≤ λᵢ₊₁ (column is within the outer partition in row i+1)
    ∀ _hcol : s.inner.parts i + k.val + 1 > s.inner.parts ⟨i.val + 1, hi⟩ ∧
             s.inner.parts i + k.val + 1 ≤ s.outer.parts ⟨i.val + 1, hi⟩,
    -- The offset in row i+1 for the same column
    let k' : ℕ := s.inner.parts i + k.val - s.inner.parts ⟨i.val + 1, hi⟩
    ∀ hk' : k' < s.outer.parts ⟨i.val + 1, hi⟩ - s.inner.parts ⟨i.val + 1, hi⟩,
    entries i k < entries ⟨i.val + 1, hi⟩ ⟨k', hk'⟩

/-- The monomial x^T associated to a tableau T.
    x_T = ∏_{(i,j) ∈ Y(λ)} x_{T(i,j)} -/
noncomputable def SSYT.toMonomial {lam : NPartition N} (T : SSYT lam) :
    MvPolynomial (Fin N) R :=
  ∏ i : Fin N, ∏ j : Fin (lam.parts i), MvPolynomial.X (T.entries i j)

/-- Two skew SSYT are equal if their entries are equal. -/
theorem SkewSSYT.eq_of_entries_eq {s : SkewPartition N} {T1 T2 : SkewSSYT s}
    (h : T1.entries = T2.entries) : T1 = T2 := by
  cases T1; cases T2
  simp only at h
  subst h
  rfl

/-- For N = 1, all SkewSSYT of a given shape are equal.
    This is because all entries must be in Fin 1 = {0}, so there's only one possible entry.
    This is useful for proving special cases of the Bender-Knuth bijection. -/
instance SkewSSYT.instSubsingletonOne (s : SkewPartition 1) : Subsingleton (SkewSSYT s) := by
  constructor
  intro T1 T2
  apply SkewSSYT.eq_of_entries_eq
  funext i k
  exact Subsingleton.elim (T1.entries i k) (T2.entries i k)

/-- Two SSYT are equal if their entries are equal. -/
theorem SSYT.eq_of_entries_eq {lam : NPartition N} {T1 T2 : SSYT lam}
    (h : T1.entries = T2.entries) : T1 = T2 := by
  cases T1; cases T2
  simp only at h
  subst h
  rfl

/-- The monomial x^T associated to a skew tableau T. -/
noncomputable def SkewSSYT.toMonomial {s : SkewPartition N} (T : SkewSSYT s) :
    MvPolynomial (Fin N) R :=
  ∏ i : Fin N, ∏ j : Fin (s.outer.parts i - s.inner.parts i),
    MvPolynomial.X (T.entries i j)

/-- Column-strictness extends to non-adjacent rows.
    If column c appears in rows i and j with i < j, then T(i, c) < T(j, c).

    This is a key lemma for the nipat-SSYT bijection: it shows that the
    column-strict condition for adjacent rows implies strict inequality
    for any two rows that share a column. The proof uses strong induction
    on the row distance j - i, with the base case being adjacent rows
    (directly using `T.colStrict`) and the inductive case going through
    an intermediate row j' = j - 1. -/
lemma SkewSSYT.colStrict_nonadjacent {s : SkewPartition N}
    (T : SkewSSYT s) (i j : Fin N) (hij : i < j)
    (k : Fin (s.outer.parts i - s.inner.parts i))
    (k' : Fin (s.outer.parts j - s.inner.parts j))
    (hcol_eq : s.inner.parts i + k.val = s.inner.parts j + k'.val) :
    T.entries i k < T.entries j k' := by
  -- Use strong induction on j.val - i.val
  obtain ⟨d, hd_eq⟩ : ∃ d, j.val - i.val = d + 1 := ⟨j.val - i.val - 1, by omega⟩
  induction d using Nat.strong_induction_on generalizing i j k k' with
  | _ d ih =>
    by_cases hd : d = 0
    · -- Base case: adjacent rows (j = i + 1)
      have hj_eq : j.val = i.val + 1 := by omega
      have hi_lt : i.val + 1 < N := by omega
      -- Show j = ⟨i.val + 1, hi_lt⟩
      have hj_fin : j = ⟨i.val + 1, hi_lt⟩ := by
        apply Fin.ext
        exact hj_eq
      subst hj_fin
      -- Now we can apply T.colStrict
      have hcol : s.inner.parts i + k.val + 1 > s.inner.parts ⟨i.val + 1, hi_lt⟩ ∧
                  s.inner.parts i + k.val + 1 ≤ s.outer.parts ⟨i.val + 1, hi_lt⟩ := by
        constructor
        · omega
        · have hk'_lt := k'.isLt
          omega
      -- The offset in row i+1 for the same column
      let k''_val := s.inner.parts i + k.val - s.inner.parts ⟨i.val + 1, hi_lt⟩
      have hk''_eq : k''_val = k'.val := by omega
      have hk''_lt : k''_val < s.outer.parts ⟨i.val + 1, hi_lt⟩ - s.inner.parts ⟨i.val + 1, hi_lt⟩ := by
        rw [hk''_eq]
        exact k'.isLt
      have hres := T.colStrict i hi_lt k hcol hk''_lt
      -- Convert types
      convert hres using 2
      apply Fin.ext
      exact hk''_eq.symm
    · -- Inductive case: j.val - i.val > 1
      have hd_gt : d > 0 := by omega
      have hj_gt : j.val > i.val + 1 := by omega
      -- Find intermediate row j' = j.val - 1
      let j' : Fin N := ⟨j.val - 1, by omega⟩
      have hij' : i < j' := by simp only [j', Fin.lt_def]; omega
      have hj'j : j' < j := by simp only [j', Fin.lt_def]; omega
      -- Key facts from partition monotonicity
      have h_inner_j_le_j' : s.inner.parts j ≤ s.inner.parts j' :=
        s.inner.weaklyDecreasing j' j (le_of_lt hj'j)
      have h_outer_j_le_j' : s.outer.parts j ≤ s.outer.parts j' :=
        s.outer.weaklyDecreasing j' j (le_of_lt hj'j)
      -- The column s.inner.parts i + k.val must appear in row j' too
      have hcol_in_j' : s.inner.parts j' < s.inner.parts i + k.val + 1 ∧
                        s.inner.parts i + k.val + 1 ≤ s.outer.parts j' := by
        constructor
        · have h_inner_j'_le_i : s.inner.parts j' ≤ s.inner.parts i :=
            s.inner.weaklyDecreasing i j' (le_of_lt hij')
          omega
        · have hk'_lt := k'.isLt
          omega
      -- Define k'' as the offset in row j' for the same column
      let k''_val := s.inner.parts i + k.val - s.inner.parts j'
      have hk''_lt : k''_val < s.outer.parts j' - s.inner.parts j' := by
        simp only [k''_val]
        have h_inner_j'_le_i : s.inner.parts j' ≤ s.inner.parts i :=
          s.inner.weaklyDecreasing i j' (le_of_lt hij')
        have hk_lt := k.isLt
        have hk'_lt := k'.isLt
        omega
      let k'' : Fin (s.outer.parts j' - s.inner.parts j') := ⟨k''_val, hk''_lt⟩
      have hcol_eq' : s.inner.parts i + k.val = s.inner.parts j' + k''.val := by
        simp only [k'', k''_val]
        have h_inner_j'_le_i : s.inner.parts j' ≤ s.inner.parts i :=
          s.inner.weaklyDecreasing i j' (le_of_lt hij')
        omega
      -- Apply IH for i → j'
      have hdiff' : j'.val - i.val - 1 < d := by simp only [j']; omega
      have hdiff'_eq : j'.val - i.val = (j'.val - i.val - 1) + 1 := by omega
      have h1 : T.entries i k < T.entries j' k'' :=
        ih (j'.val - i.val - 1) hdiff' i j' hij' k k'' hcol_eq' hdiff'_eq
      -- Apply IH for j' → j
      have hcol_eq'' : s.inner.parts j' + k''.val = s.inner.parts j + k'.val := by
        simp only [k'', k''_val]
        have h_inner_j'_le_i : s.inner.parts j' ≤ s.inner.parts i :=
          s.inner.weaklyDecreasing i j' (le_of_lt hij')
        omega
      have hdiff'' : j.val - j'.val - 1 < d := by simp only [j']; omega
      have hdiff''_eq : j.val - j'.val = (j.val - j'.val - 1) + 1 := by simp only [j']; omega
      have h2 : T.entries j' k'' < T.entries j k' :=
        ih (j.val - j'.val - 1) hdiff'' j' j hj'j k'' k' hcol_eq'' hdiff''_eq
      -- Combine by transitivity
      exact lt_trans h1 h2

/-!
### Finiteness of SSYT

The set of semistandard Young tableaux of a given shape is finite because:
1. The shape has finitely many cells
2. Each cell can contain one of finitely many values (elements of Fin N)
3. The SSYT conditions (row-weak, column-strict) define a subset of all fillings
-/

/-- A filling of a skew shape is a function assigning a value in Fin N to each cell.
    We use `abbrev` instead of `def` to ensure type class inference can see through this. -/
abbrev SkewFilling (s : SkewPartition N) :=
  (i : Fin N) → (k : Fin (s.outer.parts i - s.inner.parts i)) → Fin N

/-- The type of fillings of a skew shape is finite. -/
instance skewFilling_fintype (s : SkewPartition N) : Fintype (SkewFilling s) := inferInstance

/-- Predicate for a filling satisfying the SSYT row-weak condition. -/
def isRowWeak (s : SkewPartition N) (f : SkewFilling s) : Prop :=
  ∀ i : Fin N, ∀ j k : Fin (s.outer.parts i - s.inner.parts i),
    j ≤ k → f i j ≤ f i k

/-- Predicate for a filling satisfying the SSYT column-strict condition.
    This is a simplified version that checks the condition for adjacent rows. -/
def isColStrict (s : SkewPartition N) (f : SkewFilling s) : Prop :=
  ∀ i : Fin N, ∀ hi : i.val + 1 < N,
    ∀ k : Fin (s.outer.parts i - s.inner.parts i),
    ∀ _hcol : s.inner.parts i + k.val + 1 > s.inner.parts ⟨i.val + 1, hi⟩ ∧
             s.inner.parts i + k.val + 1 ≤ s.outer.parts ⟨i.val + 1, hi⟩,
    let k' : ℕ := s.inner.parts i + k.val - s.inner.parts ⟨i.val + 1, hi⟩
    ∀ hk' : k' < s.outer.parts ⟨i.val + 1, hi⟩ - s.inner.parts ⟨i.val + 1, hi⟩,
    f i k < f ⟨i.val + 1, hi⟩ ⟨k', hk'⟩

/-- Combined predicate for SSYT conditions. -/
def isSSYTFilling (s : SkewPartition N) (f : SkewFilling s) : Prop :=
  isRowWeak s f ∧ isColStrict s f

/-- The row-weak predicate is decidable. -/
instance isRowWeak_decidable (s : SkewPartition N) (f : SkewFilling s) :
    Decidable (isRowWeak s f) :=
  Fintype.decidableForallFintype

/-- The column-strict predicate is decidable. -/
instance isColStrict_decidable (s : SkewPartition N) (f : SkewFilling s) :
    Decidable (isColStrict s f) :=
  Fintype.decidableForallFintype

/-- The SSYT predicate is decidable. -/
instance isSSYTFilling_decidable (s : SkewPartition N) (f : SkewFilling s) :
    Decidable (isSSYTFilling s f) :=
  instDecidableAnd

/-- The finite set of all fillings satisfying SSYT conditions. -/
noncomputable def ssytFillingFinset (s : SkewPartition N) : Finset (SkewFilling s) :=
  Finset.univ.filter (isSSYTFilling s)

/-- Convert a SkewSSYT to a filling. -/
def SkewSSYT.toFilling {s : SkewPartition N} (T : SkewSSYT s) : SkewFilling s :=
  T.entries

/-- A filling satisfying SSYT conditions can be converted to a SkewSSYT. -/
def fillingToSkewSSYT {s : SkewPartition N} (f : SkewFilling s)
    (hf : isSSYTFilling s f) : SkewSSYT s where
  entries := f
  rowWeak := hf.1
  colStrict := hf.2

/-- A filling of a non-skew shape λ. -/
abbrev Filling (lam : NPartition N) := (i : Fin N) → Fin (lam.parts i) → Fin N

/-- Fintype instance for fillings of non-skew shapes. -/
instance filling_fintype (lam : NPartition N) : Fintype (Filling lam) := inferInstance

/-- Row-weak predicate for fillings of non-skew shapes. -/
def isRowWeakFilling (lam : NPartition N) (f : Filling lam) : Prop :=
  ∀ i : Fin N, ∀ j k : Fin (lam.parts i), j ≤ k → f i j ≤ f i k

/-- Column-strict predicate for fillings of non-skew shapes. -/
def isColStrictFilling (lam : NPartition N) (f : Filling lam) : Prop :=
  ∀ i : Fin N, ∀ hi : i.val + 1 < N, ∀ j : Fin (lam.parts i),
    ∀ hj : j.val < (lam.parts ⟨i.val + 1, hi⟩),
    f i j < f ⟨i.val + 1, hi⟩ ⟨j.val, hj⟩

/-- Combined SSYT predicate for non-skew fillings. -/
def isSSYTFillingNonSkew (lam : NPartition N) (f : Filling lam) : Prop :=
  isRowWeakFilling lam f ∧ isColStrictFilling lam f

/-- Decidability of row-weak for non-skew fillings. -/
instance isRowWeakFilling_decidable (lam : NPartition N) (f : Filling lam) :
    Decidable (isRowWeakFilling lam f) := Fintype.decidableForallFintype

/-- Decidability of column-strict for non-skew fillings. -/
instance isColStrictFilling_decidable (lam : NPartition N) (f : Filling lam) :
    Decidable (isColStrictFilling lam f) := Fintype.decidableForallFintype

/-- Decidability of SSYT predicate for non-skew fillings. -/
instance isSSYTFillingNonSkew_decidable (lam : NPartition N) (f : Filling lam) :
    Decidable (isSSYTFillingNonSkew lam f) := instDecidableAnd

/-- Finset of valid fillings for non-skew shapes. -/
noncomputable def ssytFillingFinsetNonSkew (lam : NPartition N) : Finset (Filling lam) :=
  Finset.univ.filter (isSSYTFillingNonSkew lam)

/-- Convert a valid filling to an SSYT. -/
def fillingToSSYT (lam : NPartition N) (f : Filling lam)
    (hf : isSSYTFillingNonSkew lam f) : SSYT lam where
  entries := f
  rowWeak := hf.1
  colStrict := hf.2

/-- An SSYT's entries form a valid filling. -/
lemma SSYT.entries_isSSYTFillingNonSkew {lam : NPartition N} (T : SSYT lam) :
    isSSYTFillingNonSkew lam T.entries := ⟨T.rowWeak, T.colStrict⟩

/-- An SSYT's entries are in the valid filling finset. -/
lemma SSYT.entries_mem_ssytFillingFinsetNonSkew {lam : NPartition N} (T : SSYT lam) :
    T.entries ∈ ssytFillingFinsetNonSkew lam := by
  simp only [ssytFillingFinsetNonSkew, Finset.mem_filter, Finset.mem_univ, true_and]
  exact T.entries_isSSYTFillingNonSkew

/-- The set of all SSYT of shape λ.
    This is finite because it's a subset of all fillings, which is finite. -/
noncomputable def ssytFinset (lam : NPartition N) : Finset (SSYT lam) :=
  (ssytFillingFinsetNonSkew lam).attach.map ⟨
    fun ⟨f, hf⟩ => fillingToSSYT lam f (Finset.mem_filter.mp hf).2,
    fun ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ h => by
      simp only [Subtype.mk.injEq]
      have : (fillingToSSYT lam f₁ (Finset.mem_filter.mp hf₁).2).entries =
             (fillingToSSYT lam f₂ (Finset.mem_filter.mp hf₂).2).entries := by
        simp only [fillingToSSYT] at h
        cases h
        rfl
      exact this
  ⟩

/-- Every SSYT is in ssytFinset. -/
theorem ssytFinset_mem (lam : NPartition N) (T : SSYT lam) : T ∈ ssytFinset lam := by
  simp only [ssytFinset, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
  refine ⟨T.entries, T.entries_mem_ssytFillingFinsetNonSkew, ?_⟩
  simp only [fillingToSSYT]
  cases T
  rfl

/-- The set of all skew SSYT of shape λ/μ.
    This is finite because it's a subset of all fillings, which is finite. -/
noncomputable def skewSSYTFinset (s : SkewPartition N) : Finset (SkewSSYT s) :=
  -- We construct this by mapping from the finite set of valid fillings
  -- The noncomputable is needed because we need to construct SkewSSYT from fillings
  (ssytFillingFinset s).attach.map ⟨
    fun ⟨f, hf⟩ => fillingToSkewSSYT f (Finset.mem_filter.mp hf).2,
    fun ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ h => by
      simp only [Subtype.mk.injEq]
      have : (fillingToSkewSSYT f₁ (Finset.mem_filter.mp hf₁).2).entries =
             (fillingToSkewSSYT f₂ (Finset.mem_filter.mp hf₂).2).entries := by
        simp only [fillingToSkewSSYT] at h
        cases h
        rfl
      exact this
  ⟩

/-- A SkewSSYT's entries form a valid SSYT filling. -/
lemma SkewSSYT.toFilling_isSSYTFilling {s : SkewPartition N} (T : SkewSSYT s) :
    isSSYTFilling s T.toFilling := ⟨T.rowWeak, T.colStrict⟩

/-- A SkewSSYT's entries are in ssytFillingFinset. -/
lemma SkewSSYT.entries_mem_ssytFillingFinset {s : SkewPartition N} (T : SkewSSYT s) :
    T.entries ∈ ssytFillingFinset s := by
  simp only [ssytFillingFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact T.toFilling_isSSYTFilling

/-- Every skew SSYT is a member of skewSSYTFinset.
    This follows from the definition of skewSSYTFinset as the set of ALL skew SSYT. -/
theorem skewSSYTFinset_mem (s : SkewPartition N) (T : SkewSSYT s) :
    T ∈ skewSSYTFinset s := by
  -- T.entries is a filling that satisfies SSYT conditions
  -- We need to show T is in the image of the map
  simp only [skewSSYTFinset, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
  -- We need to find T.entries in ssytFillingFinset s that maps to T
  refine ⟨T.entries, T.entries_mem_ssytFillingFinset, ?_⟩
  -- Show that fillingToSkewSSYT T.entries _ = T
  simp only [fillingToSkewSSYT]
  -- Need to show that the resulting SkewSSYT equals T
  cases T
  rfl

/-- The Schur polynomial s_λ defined as the sum over all SSYT of shape λ.
    Definition def.sf.schur. -/
noncomputable def schur (lam : NPartition N) : MvPolynomial (Fin N) R :=
  ∑ T ∈ ssytFinset lam, T.toMonomial

/-! ### The Schur polynomial of the zero partition

For the zero partition (0, 0, ..., 0), all rows have 0 entries, so there is
exactly one SSYT of this shape (the empty tableau). Its monomial is 1. -/

/-- The unique SSYT of shape 0 (the empty tableau).
    Since all rows have 0 entries, the entries function is vacuously defined. -/
def SSYT.unique : SSYT (0 : NPartition N) where
  entries := fun _ j => Fin.elim0 j
  rowWeak := fun _ j => Fin.elim0 j
  colStrict := fun _ _ j => Fin.elim0 j

/-- Any SSYT of shape 0 equals the unique empty tableau. -/
theorem SSYT.eq_unique (T : SSYT (0 : NPartition N)) : T = SSYT.unique := by
  apply SSYT.eq_of_entries_eq
  funext i j
  exact Fin.elim0 j

/-- The monomial of the unique SSYT of shape 0 is 1. -/
@[simp]
theorem SSYT.toMonomial_unique : (SSYT.unique (N := N)).toMonomial (R := R) = 1 := by
  simp only [SSYT.toMonomial]
  have h : ∀ i : Fin N, ∏ j : Fin ((0 : NPartition N).parts i),
      MvPolynomial.X (SSYT.unique.entries i j) = (1 : MvPolynomial (Fin N) R) := by
    intro i
    haveI : IsEmpty (Fin ((0 : NPartition N).parts i)) := by
      change IsEmpty (Fin 0)
      exact Fin.isEmpty
    exact Fintype.prod_empty _
  simp only [h, Finset.prod_const_one]

/-- The finite set of SSYT of shape 0 is the singleton containing the unique empty tableau. -/
theorem ssytFinset_zero : ssytFinset (0 : NPartition N) = {SSYT.unique} := by
  ext T
  constructor
  · intro _
    simp only [Finset.mem_singleton]
    exact T.eq_unique
  · intro hT
    simp only [Finset.mem_singleton] at hT
    rw [hT]
    exact ssytFinset_mem 0 SSYT.unique

/-- The Schur polynomial of the zero partition is 1.
    This is because the only SSYT of shape 0 is the empty tableau with monomial 1. -/
@[simp]
theorem schur_zero : schur (0 : NPartition N) = (1 : MvPolynomial (Fin N) R) := by
  simp only [schur, ssytFinset_zero, Finset.sum_singleton, SSYT.toMonomial_unique]

/-- The skew Schur polynomial s_{λ/μ} defined as the sum over all skew SSYT.
    Definition def.sf.skew-schur. -/
noncomputable def skewSchur (s : SkewPartition N) : MvPolynomial (Fin N) R :=
  ∑ T ∈ skewSSYTFinset s, T.toMonomial

/-- Convert an SSYT to a SkewSSYT when the inner partition is zero.
    This is an identity on entries since lam i - 0 = lam i definitionally. -/
def ssytToSkewSSYT (lam : Fin N → ℕ) (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (T : SSYT ⟨lam, hlam⟩) :
    SkewSSYT ⟨⟨lam, hlam⟩, ⟨fun _ => 0, fun _ _ _ => le_refl 0⟩, fun _ => Nat.zero_le _⟩ where
  entries i k := T.entries i k  -- lam i - 0 = lam i definitionally
  rowWeak i j k hjk := T.rowWeak i j k hjk
  colStrict i hi k hcol hk' := by
    simp only [Nat.zero_add, Nat.sub_zero] at hk' hcol ⊢
    exact T.colStrict i hi k hk'

/-- Convert a SkewSSYT to an SSYT when the inner partition is zero.
    This is the inverse of ssytToSkewSSYT. -/
def skewSSYTToSSYT (lam : Fin N → ℕ) (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨fun _ => 0, fun _ _ _ => le_refl 0⟩, fun _ => Nat.zero_le _⟩) :
    SSYT ⟨lam, hlam⟩ where
  entries i j := T.entries i j  -- lam i - 0 = lam i definitionally
  rowWeak i j k hjk := T.rowWeak i j k hjk
  colStrict i hi j hj := by
    change j.val < lam ⟨i.val + 1, hi⟩ at hj
    have hcol : j.val + 1 > 0 ∧ j.val + 1 ≤ lam ⟨i.val + 1, hi⟩ := by constructor <;> omega
    have hk' : j.val < lam ⟨i.val + 1, hi⟩ := hj
    have h := T.colStrict i hi j (by simp only [Nat.zero_add, Nat.sub_zero]; exact hcol)
      (by simp only [Nat.zero_add, Nat.sub_zero]; exact hk')
    simp only [Nat.zero_add, Nat.sub_zero] at h
    exact h

/-- ssytToSkewSSYT and skewSSYTToSSYT are inverses (direction 1). -/
lemma ssytToSkewSSYT_skewSSYTToSSYT (lam : Fin N → ℕ) (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (T : SSYT ⟨lam, hlam⟩) :
    skewSSYTToSSYT lam hlam (ssytToSkewSSYT lam hlam T) = T := by
  cases T; rfl

/-- ssytToSkewSSYT and skewSSYTToSSYT are inverses (direction 2). -/
lemma skewSSYTToSSYT_ssytToSkewSSYT (lam : Fin N → ℕ) (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨fun _ => 0, fun _ _ _ => le_refl 0⟩, fun _ => Nat.zero_le _⟩) :
    ssytToSkewSSYT lam hlam (skewSSYTToSSYT lam hlam T) = T := by
  cases T; rfl

/-- ssytToSkewSSYT preserves monomials. -/
lemma ssytToSkewSSYT_toMonomial (lam : Fin N → ℕ) (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (T : SSYT ⟨lam, hlam⟩) :
    (ssytToSkewSSYT lam hlam T).toMonomial = T.toMonomial (R := R) := rfl

/-- When the inner partition is zero, the skew Schur polynomial equals the regular Schur polynomial.
    This is because the skew shape λ/0 is just the shape λ. -/
theorem skewSchur_zero_eq_schur (lam : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
    skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨fun _ => 0, fun _ _ _ => le_refl 0⟩, fun _ => Nat.zero_le _⟩ =
    schur (R := R) ⟨lam, hlam⟩ := by
  -- Both sides are sums over tableaux. When inner = 0, SkewSSYT is essentially the same as SSYT
  -- since outer.parts i - 0 = outer.parts i for all i.
  unfold skewSchur schur
  -- Use sum_bij with the bijection ssytToSkewSSYT
  symm
  apply Finset.sum_bij (fun T _ => ssytToSkewSSYT lam hlam T)
  · -- ssytToSkewSSYT maps elements to skewSSYTFinset
    intro T _
    exact skewSSYTFinset_mem _ _
  · -- ssytToSkewSSYT is injective
    intro T₁ _ T₂ _ h
    have : skewSSYTToSSYT lam hlam (ssytToSkewSSYT lam hlam T₁) =
           skewSSYTToSSYT lam hlam (ssytToSkewSSYT lam hlam T₂) := by rw [h]
    simp only [ssytToSkewSSYT_skewSSYTToSSYT] at this
    exact this
  · -- ssytToSkewSSYT is surjective
    intro T' _
    refine ⟨skewSSYTToSSYT lam hlam T', ssytFinset_mem _ _, ?_⟩
    exact skewSSYTToSSYT_ssytToSkewSSYT lam hlam T'
  · -- ssytToSkewSSYT preserves monomials
    intro T _
    exact ssytToSkewSSYT_toMonomial lam hlam T

/-!
## The Pieri Rules

Theorem thm.sf.pieri: The Pieri rules express products h_n · s_μ and e_n · s_μ
as sums of Schur polynomials.
-/

/-!
### Enumeration of Horizontal and Vertical Strip Partitions

For a fixed N-partition μ and size n, we enumerate all N-partitions λ such that
λ/μ is a horizontal (resp. vertical) n-strip. The key observation is that each
λ_i is bounded:
- Lower bound: λ_i ≥ μ_i (containment)
- Upper bound: λ_i ≤ μ_{i-1} for i > 0 (horizontal strip condition)
- Upper bound: λ_0 ≤ μ_0 + n (since |λ| = |μ| + n)

This makes the enumeration finite.
-/

/-- The bound for each λ_i when forming a horizontal strip with μ.
    λ_i must satisfy μ_i ≤ λ_i ≤ bound_i where:
    - For i = 0: bound_0 = μ_0 + n (since |λ| - |μ| = n and all parts are bounded by λ_0)
    - For i > 0: bound_i = μ_{i-1} (horizontal strip condition: μ_{i-1} ≥ λ_i) -/
def horizontalStripUpperBound (mu : NPartition N) (n : ℕ) (i : Fin N) : ℕ :=
  if h : i.val = 0 then mu.parts ⟨0, Nat.pos_of_ne_zero (by omega : N ≠ 0)⟩ + n
  else mu.parts ⟨i.val - 1, by omega⟩

/-- A function from Fin N to ℕ that could potentially form a horizontal n-strip with μ.
    This is the set of all functions bounded by the horizontal strip constraints. -/
def potentialHorizontalStrips (mu : NPartition N) (n : ℕ) : Finset (Fin N → ℕ) :=
  Fintype.piFinset (fun i => Finset.Icc (mu.parts i) (horizontalStripUpperBound mu n i))

/-- Check if a function forms a valid N-partition (weakly decreasing). -/
def isWeaklyDecreasing (f : Fin N → ℕ) : Prop :=
  ∀ i j : Fin N, i ≤ j → f j ≤ f i

instance (f : Fin N → ℕ) : Decidable (isWeaklyDecreasing f) :=
  Fintype.decidableForallFintype

/-- Check if |λ| - |μ| = n. -/
def hasSizeDiff (mu lam : Fin N → ℕ) (n : ℕ) : Prop :=
  (∑ i, lam i) = (∑ i, mu i) + n

instance (mu lam : Fin N → ℕ) (n : ℕ) : Decidable (hasSizeDiff mu lam n) :=
  inferInstanceAs (Decidable (_ = _))

/-- A skew partition λ/μ is a horizontal strip if no two boxes lie in the same column.
    Equivalently: μ_i ≥ λ_{i+1} for all i.

    The argument order `(lam, mu)` matches standard mathematical notation λ/μ.

    **Related definitions:**
    - `SkewPartition.isHorizontalStrip`: Bundled version for `SkewPartition N` -/
def isHorizontalStripFun (lam mu : Fin N → ℕ) : Prop :=
  ∀ i : Fin N, ∀ hi : i.val + 1 < N, mu i ≥ lam ⟨i.val + 1, hi⟩

/-- A skew partition λ/μ is a vertical strip if no two boxes lie in the same row.
    Equivalently: λ_i ≤ μ_i + 1 for all i.

    The argument order `(lam, mu)` matches standard mathematical notation λ/μ.

    **Related definitions:**
    - `SkewPartition.isVerticalStrip`: Bundled version for `SkewPartition N` -/
def isVerticalStripFun (lam mu : Fin N → ℕ) : Prop :=
  ∀ i : Fin N, lam i ≤ mu i + 1

/-- Decidable instance for horizontal strip predicate. -/
instance instDecidableIsHorizontalStripFun (lam mu : Fin N → ℕ) :
    Decidable (isHorizontalStripFun lam mu) :=
  Fintype.decidableForallFintype

/-- Decidable instance for vertical strip predicate. -/
instance instDecidableIsVerticalStripFun (lam mu : Fin N → ℕ) :
    Decidable (isVerticalStripFun lam mu) :=
  Fintype.decidableForallFintype

/-- Convert a valid function to an NPartition. -/
def toNPartition (f : Fin N → ℕ) (hf : isWeaklyDecreasing f) : NPartition N where
  parts := f
  weaklyDecreasing := hf

/-- The set of N-partitions λ such that λ/μ is a horizontal n-strip.

    This is the set of all N-partitions λ satisfying:
    1. μ ⊆ λ (containment): μ_i ≤ λ_i for all i
    2. Horizontal strip: μ_i ≥ λ_{i+1} for all i < N
    3. Size: |λ| - |μ| = n

    The set is finite because each λ_i is bounded. -/
def horizontalNStripPartitions (mu : NPartition N) (n : ℕ) : Finset (NPartition N) :=
  (potentialHorizontalStrips mu n).filter (fun f =>
    isWeaklyDecreasing f ∧ isHorizontalStripFun f mu.parts ∧ hasSizeDiff mu.parts f n
  ) |>.attach.image (fun ⟨f, hf⟩ =>
    let hf' := Finset.mem_filter.mp hf
    toNPartition f hf'.2.1)

/-- The bound for each λ_i when forming a vertical strip with μ.
    λ_i must satisfy μ_i ≤ λ_i ≤ μ_i + 1 (vertical strip condition). -/
def verticalStripUpperBound (mu : NPartition N) (i : Fin N) : ℕ :=
  mu.parts i + 1

/-- A function from Fin N to ℕ that could potentially form a vertical n-strip with μ. -/
def potentialVerticalStrips (mu : NPartition N) : Finset (Fin N → ℕ) :=
  Fintype.piFinset (fun i => Finset.Icc (mu.parts i) (verticalStripUpperBound mu i))

/-- The set of N-partitions λ such that λ/μ is a vertical n-strip.

    This is the set of all N-partitions λ satisfying:
    1. μ ⊆ λ (containment): μ_i ≤ λ_i for all i
    2. Vertical strip: λ_i ≤ μ_i + 1 for all i
    3. Size: |λ| - |μ| = n

    The set is finite because each λ_i ∈ {μ_i, μ_i + 1}. -/
def verticalNStripPartitions (mu : NPartition N) (n : ℕ) : Finset (NPartition N) :=
  (potentialVerticalStrips mu).filter (fun f =>
    isWeaklyDecreasing f ∧ isVerticalStripFun f mu.parts ∧ hasSizeDiff mu.parts f n
  ) |>.attach.image (fun ⟨f, hf⟩ =>
    let hf' := Finset.mem_filter.mp hf
    toNPartition f hf'.2.1)

/-!
### Properties of Horizontal Strip Partitions
-/

/-- If λ ∈ horizontalNStripPartitions μ n, then μ ⊆ λ. -/
theorem horizontalNStripPartitions_contained (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ horizontalNStripPartitions mu n) :
    mu ≤ lam := by
  simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter, potentialHorizontalStrips, Fintype.mem_piFinset,
    Finset.mem_Icc] at hf
  intro i
  have hfi : mu.parts i ≤ f i := (hf.1 i).1
  simp only [← heq, toNPartition]
  exact hfi

/-- If λ ∈ horizontalNStripPartitions μ n, then λ/μ is a horizontal strip. -/
theorem horizontalNStripPartitions_isHorizontalStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ horizontalNStripPartitions mu n) :
    (⟨lam, mu, horizontalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isHorizontalStrip := by
  simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  intro i hi
  simp only [← heq, toNPartition]
  exact hf.2.2.1 i hi

/-- If λ ∈ horizontalNStripPartitions μ n, then |λ| - |μ| = n. -/
theorem horizontalNStripPartitions_size (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ horizontalNStripPartitions mu n) :
    lam.size - mu.size = n := by
  simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  rw [← heq]
  simp only [toNPartition, NPartition.size, hasSizeDiff] at hf ⊢
  omega

/-- If λ ∈ horizontalNStripPartitions μ n, then the skew partition λ/μ is a horizontal n-strip.
    This combines the horizontal strip condition and size condition into a single predicate. -/
theorem horizontalNStripPartitions_isHorizontalNStrip' (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ horizontalNStripPartitions mu n) :
    (⟨lam, mu, horizontalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isHorizontalNStrip n := by
  have hcontained := horizontalNStripPartitions_contained mu n lam hlam
  simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  constructor
  · -- horizontal strip condition
    intro i hi
    have heq_parts : lam.parts = f := by rw [← heq]; rfl
    simp only [heq_parts]
    exact hf.2.2.1 i hi
  · -- size condition
    simp only [SkewPartition.size, NPartition.size]
    have heq_parts : lam.parts = f := by rw [← heq]; rfl
    rw [heq_parts]
    simp only [hasSizeDiff] at hf
    have hle : ∑ i, mu.parts i ≤ ∑ i, f i := by
      apply Finset.sum_le_sum
      intro i _
      simp only [potentialHorizontalStrips, Fintype.mem_piFinset, Finset.mem_Icc] at hf
      exact (hf.1 i).1
    have hsize : ∑ i, f i = ∑ i, mu.parts i + n := hf.2.2.2
    omega

/-!
### Properties of Vertical Strip Partitions
-/

/-- If λ ∈ verticalNStripPartitions μ n, then μ ⊆ λ. -/
theorem verticalNStripPartitions_contained (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ verticalNStripPartitions mu n) :
    mu ≤ lam := by
  simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter, potentialVerticalStrips, Fintype.mem_piFinset,
    Finset.mem_Icc] at hf
  intro i
  have hfi : mu.parts i ≤ f i := (hf.1 i).1
  simp only [← heq, toNPartition]
  exact hfi

/-- If λ ∈ verticalNStripPartitions μ n, then λ/μ is a vertical strip. -/
theorem verticalNStripPartitions_isVerticalStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ verticalNStripPartitions mu n) :
    (⟨lam, mu, verticalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isVerticalStrip := by
  simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  intro i
  simp only [← heq, toNPartition]
  exact hf.2.2.1 i

/-- If λ ∈ verticalNStripPartitions μ n, then |λ| - |μ| = n. -/
theorem verticalNStripPartitions_size (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ verticalNStripPartitions mu n) :
    lam.size - mu.size = n := by
  simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  rw [← heq]
  simp only [toNPartition, NPartition.size, hasSizeDiff] at hf ⊢
  omega

/-- If λ ∈ verticalNStripPartitions μ n, then the skew partition λ/μ is a vertical n-strip.
    This combines the vertical strip condition and size condition into a single predicate. -/
theorem verticalNStripPartitions_isVerticalNStrip' (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hlam : lam ∈ verticalNStripPartitions mu n) :
    (⟨lam, mu, verticalNStripPartitions_contained mu n lam hlam⟩ : SkewPartition N).isVerticalNStrip n := by
  have hcontained := verticalNStripPartitions_contained mu n lam hlam
  simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hlam
  obtain ⟨f, hf, heq⟩ := hlam
  simp only [Finset.mem_filter] at hf
  constructor
  · -- vertical strip condition
    intro i
    have heq_parts : lam.parts = f := by rw [← heq]; rfl
    rw [heq_parts]
    exact hf.2.2.1 i
  · -- size condition
    simp only [SkewPartition.size, NPartition.size]
    have heq_parts : lam.parts = f := by rw [← heq]; rfl
    rw [heq_parts]
    simp only [hasSizeDiff] at hf
    have hle : ∑ i, mu.parts i ≤ ∑ i, f i := by
      apply Finset.sum_le_sum
      intro i _
      simp only [potentialVerticalStrips, Fintype.mem_piFinset, Finset.mem_Icc] at hf
      exact (hf.1 i).1
    have hsize : ∑ i, f i = ∑ i, mu.parts i + n := hf.2.2.2
    omega

/-!
### Membership Characterization for Strip Partitions

These theorems provide complete characterizations of membership in
`horizontalNStripPartitions` and `verticalNStripPartitions`, useful for
proving that specific partitions belong to these sets.
-/

/-- Complete characterization of membership in `horizontalNStripPartitions`.

    An N-partition λ is in `horizontalNStripPartitions μ n` if and only if:
    1. μ ⊆ λ (containment): μ_i ≤ λ_i for all i
    2. λ/μ is a horizontal strip: μ_i ≥ λ_{i+1} for all i < N
    3. |λ| - |μ| = n (size constraint)
    4. Each λ_i is bounded by `horizontalStripUpperBound μ n i`

    This characterization is useful for proving that specific partitions
    belong to `horizontalNStripPartitions μ n`. -/
theorem mem_horizontalNStripPartitions_iff (mu : NPartition N) (n : ℕ) (lam : NPartition N) :
    lam ∈ horizontalNStripPartitions mu n ↔
      (∀ i, mu.parts i ≤ lam.parts i) ∧
      isHorizontalStripFun lam.parts mu.parts ∧
      hasSizeDiff mu.parts lam.parts n ∧
      (∀ i, lam.parts i ≤ horizontalStripUpperBound mu n i) := by
  constructor
  · -- Forward direction: membership implies conditions
    intro hlam
    simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
      true_and, Subtype.exists] at hlam
    obtain ⟨f, hf, heq⟩ := hlam
    simp only [Finset.mem_filter, potentialHorizontalStrips, Fintype.mem_piFinset,
      Finset.mem_Icc] at hf
    have hparts : lam.parts = f := by
      simp only [← heq, toNPartition]
    constructor
    · -- containment
      intro i
      rw [hparts]
      exact (hf.1 i).1
    constructor
    · -- horizontal strip
      rw [hparts]
      exact hf.2.2.1
    constructor
    · -- size diff
      rw [hparts]
      exact hf.2.2.2
    · -- upper bound
      intro i
      rw [hparts]
      exact (hf.1 i).2
  · -- Backward direction: conditions imply membership
    intro ⟨hcontained, hstrip, hsize, hbound⟩
    simp only [horizontalNStripPartitions, Finset.mem_image, Finset.mem_attach,
      true_and, Subtype.exists]
    refine ⟨lam.parts, ?_, rfl⟩
    simp only [Finset.mem_filter, potentialHorizontalStrips, Fintype.mem_piFinset,
      Finset.mem_Icc]
    exact ⟨fun i => ⟨hcontained i, hbound i⟩, lam.weaklyDecreasing, hstrip, hsize⟩

/-- Complete characterization of membership in `verticalNStripPartitions`.

    An N-partition λ is in `verticalNStripPartitions μ n` if and only if:
    1. μ ⊆ λ (containment): μ_i ≤ λ_i for all i
    2. λ/μ is a vertical strip: λ_i ≤ μ_i + 1 for all i
    3. |λ| - |μ| = n (size constraint)

    This characterization is useful for proving that specific partitions
    belong to `verticalNStripPartitions μ n`. -/
theorem mem_verticalNStripPartitions_iff (mu : NPartition N) (n : ℕ) (lam : NPartition N) :
    lam ∈ verticalNStripPartitions mu n ↔
      (∀ i, mu.parts i ≤ lam.parts i) ∧
      isVerticalStripFun lam.parts mu.parts ∧
      hasSizeDiff mu.parts lam.parts n := by
  constructor
  · -- Forward direction: membership implies conditions
    intro hlam
    simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
      true_and, Subtype.exists] at hlam
    obtain ⟨f, hf, heq⟩ := hlam
    simp only [Finset.mem_filter, potentialVerticalStrips, Fintype.mem_piFinset,
      Finset.mem_Icc] at hf
    have hparts : lam.parts = f := by
      simp only [← heq, toNPartition]
    constructor
    · -- containment
      intro i
      rw [hparts]
      exact (hf.1 i).1
    constructor
    · -- vertical strip
      rw [hparts]
      exact hf.2.2.1
    · -- size diff
      rw [hparts]
      exact hf.2.2.2
  · -- Backward direction: conditions imply membership
    intro ⟨hcontained, hstrip, hsize⟩
    simp only [verticalNStripPartitions, Finset.mem_image, Finset.mem_attach,
      true_and, Subtype.exists]
    refine ⟨lam.parts, ?_, rfl⟩
    simp only [Finset.mem_filter, potentialVerticalStrips, Fintype.mem_piFinset,
      Finset.mem_Icc, verticalStripUpperBound]
    constructor
    · intro i
      exact ⟨hcontained i, hstrip i⟩
    exact ⟨lam.weaklyDecreasing, hstrip, hsize⟩

/-- Helper lemma relating `SkewPartition.size` to `hasSizeDiff` for horizontal strips. -/
lemma hasSizeDiff_of_isHorizontalNStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hcontained : mu ≤ lam)
    (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isHorizontalNStrip n) :
    hasSizeDiff mu.parts lam.parts n := by
  simp only [hasSizeDiff]
  have hsize := hstrip.2
  simp only [SkewPartition.size, NPartition.size] at hsize
  have hle : (∑ i, mu.parts i) ≤ (∑ i, lam.parts i) := by
    apply Finset.sum_le_sum
    intro i _
    exact hcontained i
  omega

/-- Helper lemma relating `SkewPartition.size` to `hasSizeDiff` for vertical strips. -/
lemma hasSizeDiff_of_isVerticalNStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hcontained : mu ≤ lam)
    (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isVerticalNStrip n) :
    hasSizeDiff mu.parts lam.parts n := by
  simp only [hasSizeDiff]
  have hsize := hstrip.2
  simp only [SkewPartition.size, NPartition.size] at hsize
  have hle : (∑ i, mu.parts i) ≤ (∑ i, lam.parts i) := by
    apply Finset.sum_le_sum
    intro i _
    exact hcontained i
  omega

/-- Simplified membership criterion for horizontal strip partitions using SkewPartition API.

    This theorem bridges the gap between the `horizontalNStripPartitions` finset
    and the `SkewPartition.isHorizontalNStrip` predicate. -/
theorem mem_horizontalNStripPartitions_of_isHorizontalNStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hcontained : mu ≤ lam)
    (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isHorizontalNStrip n)
    (hbound : ∀ i, lam.parts i ≤ horizontalStripUpperBound mu n i) :
    lam ∈ horizontalNStripPartitions mu n := by
  rw [mem_horizontalNStripPartitions_iff]
  exact ⟨hcontained, hstrip.1, hasSizeDiff_of_isHorizontalNStrip mu n lam hcontained hstrip, hbound⟩

/-- Simplified membership criterion for vertical strip partitions using SkewPartition API.

    This theorem bridges the gap between the `verticalNStripPartitions` finset
    and the `SkewPartition.isVerticalNStrip` predicate. -/
theorem mem_verticalNStripPartitions_of_isVerticalNStrip (mu : NPartition N) (n : ℕ)
    (lam : NPartition N) (hcontained : mu ≤ lam)
    (hstrip : (⟨lam, mu, hcontained⟩ : SkewPartition N).isVerticalNStrip n) :
    lam ∈ verticalNStripPartitions mu n := by
  rw [mem_verticalNStripPartitions_iff]
  exact ⟨hcontained, hstrip.1, hasSizeDiff_of_isVerticalNStrip mu n lam hcontained hstrip⟩

/-!
### Infrastructure for Pieri Rule Proofs

The Pieri rules require a bijection between:
- Domain: `Sym (Fin N) n × SSYT μ` (multisets of size n paired with tableaux of shape μ)
- Codomain: `⨆_{λ ∈ horizontalNStripPartitions μ n} SSYT λ` (tableaux of shapes forming horizontal n-strips)

This bijection is the RSK row insertion. Below we provide lemmas that show how the
RHS of the Pieri rule can be rewritten as a sum over a sigma type, making the
structure of the proof clear.
-/

/-!
### Alternative Approach: Pieri Rules via Littlewood-Richardson

An alternative proof of the Pieri rules derives them from the Littlewood-Richardson rule.
The key observations are:

1. **h_n = s_{(n,0,...,0)}**: The complete homogeneous symmetric polynomial h_n equals
   the Schur polynomial indexed by the row partition (n, 0, ..., 0).

2. **e_n = s_{(1,1,...,1,0,...,0)}**: The elementary symmetric polynomial e_n equals
   the Schur polynomial indexed by the column partition with n ones.

3. **Littlewood-Richardson specialization**: When ν = (n, 0, ..., 0), the ν-Yamanouchi
   tableaux of shape λ/μ correspond exactly to horizontal n-strips (or vertical n-strips
   for the column partition case).

The infrastructure for this approach requires:
- `NPartition.rowPartition`: The partition (n, 0, ..., 0) ✓ (defined above)
- `NPartition.colPartition`: The partition (1, 1, ..., 1, 0, ..., 0) ✓ (defined above)
- `hsymm_eq_schur_rowPartition`: h_n = s_{rowPartition} ✓ (proved below)
- `esymm_eq_schur_colPartition`: e_n = s_{colPartition} ✓ (proved below)
- Characterization of Yamanouchi tableaux for row/column partitions (partial: reverse direction proved)

This approach is documented in Exercise exe.sf.pieri of the source text.
The Pieri rules themselves are left as exercises (see `pieri_horizontal`, `pieri_vertical`).
-/

/-! ### Yamanouchi Tableaux Infrastructure for Row/Column Partitions

This section provides infrastructure for working with row and column partitions
in the context of Yamanouchi tableaux (defined in `LittlewoodRichardson.lean`).

**Mathematical Background:**

The key insight connecting the Littlewood-Richardson rule to Pieri rules is that
Yamanouchi tableaux for row and column partitions have a simple characterization:

**For row partition ν = (n, 0, ..., 0):**
A semistandard tableau T of shape λ/μ is ν-Yamanouchi iff:
1. All entries of T are 0 (the first row index)
2. λ/μ is a horizontal strip (no two cells in same column)

This is because:
- The Yamanouchi condition requires ν + cont(col_{≥j}(T)) to be weakly decreasing for all j > 0
- For ν = (n, 0, ..., 0), adding any content to position i > 0 would violate this
- So all entries must be 0, and semistandardness forces at most one cell per column

**For column partition ν = (1, 1, ..., 1, 0, ..., 0) with n ones:**
A semistandard tableau T of shape λ/μ is ν-Yamanouchi iff:
1. Entries form a valid "staircase" pattern (entry in row i is at least i)
2. λ/μ is a vertical strip (no two cells in same row)

This is because:
- The Yamanouchi condition with column partition ensures votes are spread across rows
- Semistandardness with at most one entry per row gives vertical strip

**What's provided here:**
- `rowPartitionFun`, `colPartitionFun`: Functions extracting partition parts
- Simp lemmas for accessing row/column partition values
- Proofs that these are valid N-partitions

**Note:** The reverse direction `allEntriesZero_implies_isYamanouchi_rowPartition` is proved below:
for row partition ν = (n, 0, ..., 0), if all entries of a semistandard tableau are 0,
then it is ν-Yamanouchi.
-/

/-- Row partition as a function (for use with LittlewoodRichardson.IsYamanouchi). -/
def rowPartitionFun (N : ℕ) (n : ℕ) (hN : 0 < N) : Fin N → ℕ :=
  (NPartition.rowPartition N n hN).parts

/-- Column partition as a function (for use with LittlewoodRichardson.IsYamanouchi). -/
def colPartitionFun (N : ℕ) (n : ℕ) (hn : n ≤ N) : Fin N → ℕ :=
  (NPartition.colPartition N n hn).parts

/-- The row partition function has n at position 0 and 0 elsewhere. -/
@[simp]
theorem rowPartitionFun_zero (N : ℕ) (n : ℕ) (hN : 0 < N) :
    rowPartitionFun N n hN ⟨0, hN⟩ = n := by
  simp [rowPartitionFun, NPartition.rowPartition]

@[simp]
theorem rowPartitionFun_pos (N : ℕ) (n : ℕ) (hN : 0 < N) (i : Fin N) (hi : 0 < i.val) :
    rowPartitionFun N n hN i = 0 := by
  simp only [rowPartitionFun, NPartition.rowPartition]
  simp only [ite_eq_right_iff]
  omega

/-- The column partition function has 1 at positions < n and 0 elsewhere. -/
@[simp]
theorem colPartitionFun_lt (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : i.val < n) :
    colPartitionFun N n hn i = 1 := by
  simp [colPartitionFun, NPartition.colPartition, hi]

@[simp]
theorem colPartitionFun_ge (N : ℕ) (n : ℕ) (hn : n ≤ N) (i : Fin N) (hi : n ≤ i.val) :
    colPartitionFun N n hn i = 0 := by
  simp [colPartitionFun, NPartition.colPartition, Nat.not_lt.mpr hi]

/-- The row partition function is an N-partition (weakly decreasing). -/
theorem rowPartitionFun_isNPartition (N : ℕ) (n : ℕ) (hN : 0 < N) :
    _root_.IsNPartition (rowPartitionFun N n hN) :=
  (NPartition.rowPartition N n hN).weaklyDecreasing

/-- The column partition function is an N-partition (weakly decreasing). -/
theorem colPartitionFun_isNPartition (N : ℕ) (n : ℕ) (hn : n ≤ N) :
    _root_.IsNPartition (colPartitionFun N n hn) :=
  (NPartition.colPartition N n hn).weaklyDecreasing

/-! ### Yamanouchi Tableaux Characterization for Row/Column Partitions

This section provides the key characterization theorems connecting Yamanouchi tableaux
with horizontal and vertical strips. These theorems enable the alternative proof of
Pieri rules via the Littlewood-Richardson rule.

**Mathematical Background:**

For the row partition ν = (n, 0, ..., 0):
- A semistandard tableau T of shape λ/μ is ν-Yamanouchi iff all entries are 0
  and λ/μ is a horizontal strip.
- This is because adding any content to position i > 0 would violate the
  weakly decreasing property of ν + cont(col_{≥j}(T)).

For the column partition ν = (1, 1, ..., 1, 0, ..., 0) with n ones:
- A semistandard tableau T of shape λ/μ is ν-Yamanouchi iff entries follow
  a specific pattern and λ/μ is a vertical strip.
-/

/-!
### Equivalences Between Strip Definitions

The following lemmas establish equivalences between the bundled and unbundled
representations of horizontal/vertical strip predicates:

1. **Bundled:** `SkewPartition.isHorizontalStrip` / `SkewPartition.isVerticalStrip`
   - Input: `SkewPartition N` (bundled outer/inner partitions)
   - Used in: Main theorems like `pieri_horizontal`, `pieri_vertical`

2. **Unbundled (canonical):** `isHorizontalStripFun` / `isVerticalStripFun`
   - Input: `(lam mu : Fin N → ℕ)` with argument order `(lam, mu)` matching λ/μ notation
   - Used in: `horizontalNStripPartitions`, `verticalNStripPartitions`, and
     integration with `LittlewoodRichardson.Tableau`
-/

/-- The bundled `SkewPartition.isHorizontalStrip` is equivalent to the canonical
    unbundled `isHorizontalStripFun` applied to the outer and inner partitions. -/
theorem SkewPartition.isHorizontalStrip_iff_isHorizontalStripFun (s : SkewPartition N) :
    s.isHorizontalStrip ↔ isHorizontalStripFun s.outer.parts s.inner.parts := Iff.rfl

/-- The bundled `SkewPartition.isVerticalStrip` is equivalent to the canonical
    unbundled `isVerticalStripFun` applied to the outer and inner partitions. -/
theorem SkewPartition.isVerticalStrip_iff_isVerticalStripFun (s : SkewPartition N) :
    s.isVerticalStrip ↔ isVerticalStripFun s.outer.parts s.inner.parts := Iff.rfl

/-- All entries of a tableau are 0 (the first row index).
    This is the key property for row partition Yamanouchi tableaux. -/
def allEntriesZero {lam mu : Fin N → ℕ} (T : AlgebraicCombinatorics.Tableau lam mu) : Prop :=
  ∀ c : {c : Fin N × ℕ // c ∈ AlgebraicCombinatorics.skewYoungDiagram lam mu}, (T c).val = 0

/-- Decidable instance for allEntriesZero when the diagram is finite. -/
noncomputable instance instDecidableAllEntriesZero {lam mu : Fin N → ℕ}
    (T : AlgebraicCombinatorics.Tableau lam mu) : Decidable (allEntriesZero T) := by
  haveI : Fintype {c : Fin N × ℕ // c ∈ AlgebraicCombinatorics.skewYoungDiagram lam mu} :=
    Set.Finite.fintype (AlgebraicCombinatorics.skewYoungDiagram_finite lam mu)
  exact Fintype.decidableForallFintype

/-- When all entries of a tableau are 0, the content at any position k > 0 is 0.
    This is because no cell has entry k when all entries are 0. -/
lemma contentColGeq_zero_of_allEntriesZero {lam mu : Fin N → ℕ}
    (T : AlgebraicCombinatorics.Tableau lam mu)
    (hZero : allEntriesZero T) (j : ℕ) (k : Fin N) (hk : 0 < k.val) :
    AlgebraicCombinatorics.contentColGeq T j k = 0 := by
  unfold AlgebraicCombinatorics.contentColGeq
  rw [Nat.card_eq_zero]
  left
  constructor
  intro ⟨⟨c, hc_mem, _⟩, hTc⟩
  have h0 : (T ⟨c, hc_mem⟩).val = 0 := hZero ⟨c, hc_mem⟩
  have : k.val = 0 := by rw [← hTc]; exact h0
  omega

/-- **Row partition Yamanouchi characterization (reverse direction):**
    If all entries of T are 0 and T is semistandard, then T is ν-Yamanouchi
    for ν = (n, 0, ..., 0). -/
theorem allEntriesZero_implies_isYamanouchi_rowPartition
    {lam mu : Fin N → ℕ} (hN : 0 < N)
    (T : AlgebraicCombinatorics.Tableau lam mu)
    (hSS : AlgebraicCombinatorics.IsSemistandard T)
    (hZero : allEntriesZero T) :
    ∀ n : ℕ, AlgebraicCombinatorics.IsYamanouchi (rowPartitionFun N n hN) T := by
  intro n
  constructor
  · exact hSS
  · intro j hj i k hik
    simp only [Pi.add_apply]
    -- When all entries are 0, the content at any position k > 0 is 0
    -- So ν + cont = (n + cont_0, 0, ..., 0) which is weakly decreasing
    by_cases hi : i.val = 0
    · by_cases hk : k.val = 0
      · have : i = k := Fin.ext (by omega)
        rw [this]
      · -- k > 0, so rowPartitionFun k = 0 and contentColGeq T j k = 0
        have hk_pos : 0 < k.val := Nat.pos_of_ne_zero hk
        have h1 : rowPartitionFun N n hN k = 0 := rowPartitionFun_pos N n hN k hk_pos
        have h2 : AlgebraicCombinatorics.contentColGeq T j k = 0 :=
          contentColGeq_zero_of_allEntriesZero T hZero j k hk_pos
        simp only [h1, h2]
        omega
    · -- i > 0, so k ≥ i > 0, thus both rowPartitionFun and contentColGeq are 0
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi
      have hk_pos : 0 < k.val := by have : i.val ≤ k.val := hik; omega
      have h1i : rowPartitionFun N n hN i = 0 := rowPartitionFun_pos N n hN i hi_pos
      have h1k : rowPartitionFun N n hN k = 0 := rowPartitionFun_pos N n hN k hk_pos
      have h2i : AlgebraicCombinatorics.contentColGeq T j i = 0 :=
        contentColGeq_zero_of_allEntriesZero T hZero j i hi_pos
      have h2k : AlgebraicCombinatorics.contentColGeq T j k = 0 :=
        contentColGeq_zero_of_allEntriesZero T hZero j k hk_pos
      simp only [h1i, h1k, h2i, h2k]
      omega

/-! ### Note on Horizontal Strips and Semistandard Tableaux

**WARNING:** The statement "horizontal strip + semistandard ⟹ all entries 0" is FALSE.

**Counterexample:** N = 2, λ = (2, 1), μ = (1, 0)
- This is a horizontal strip: μ₀ = 1 ≥ λ₁ = 1 ✓
- Cells: (0, 2) and (1, 1) — in different columns
- Any assignment is semistandard (vacuously, since no two cells share a row or column)
- In particular, T(0, 2) = 1 gives a non-zero entry

**WARNING:** The statement "Yamanouchi w.r.t. row partition ⟹ all entries 0" is also FALSE
without the horizontal strip hypothesis!

**Counterexample:** N = 3, λ = (2, 2, 0), μ = (0, 0, 0), n = 1, ν = (1, 0, 0)
- This is NOT a horizontal strip (both row 0 and row 1 have 2 cells)
- The tableau T with T(0,1) = 0, T(0,2) = 1, T(1,1) = 1, T(1,2) = 2 is semistandard
- At j = 1: ν + contentColGeq T 1 = (1, 0, 0) + (1, 2, 1) = (2, 2, 1), an N-partition ✓
- At j = 2: ν + contentColGeq T 2 = (1, 0, 0) + (0, 1, 1) = (1, 1, 1), an N-partition ✓
- So T is (1, 0, 0)-Yamanouchi, but has positive entries 1 and 2!

The correct characterization requires BOTH being a horizontal strip AND being Yamanouchi
with respect to a row partition.
-/

/-- Convert a Sym to an SSYT of row partition shape.
    The sorted multiset gives a weakly increasing sequence for row 0. -/
def symToRowSSYT (hN : 0 < N) (n : ℕ) (s : Sym (Fin N) n) :
    SSYT (NPartition.rowPartition N n hN) where
  entries i j :=
    -- Row 0 has n boxes, other rows have 0 boxes
    if hi : i.val = 0 then
      -- In row 0, use the sorted multiset
      have hj_lt : j.val < n := by
        have hj := j.isLt
        simp only [NPartition.rowPartition, hi, ↓reduceIte] at hj
        exact hj
      (symToWeaklyIncreasing n s).val ⟨j.val, hj_lt⟩
    else
      -- Other rows are empty, so this is impossible
      (Fin.elim0 (by
        have hj := j.isLt
        simp only [NPartition.rowPartition, hi, ↓reduceIte] at hj
        exact ⟨j.val, hj⟩ : Fin 0))
  rowWeak i j k hjk := by
    simp only
    split_ifs with hi
    · -- Row 0: use weakly increasing property
      exact (symToWeaklyIncreasing n s).property _ _ hjk
    · -- Other rows are empty
      have hj := j.isLt
      simp only [NPartition.rowPartition, hi, ↓reduceIte] at hj
      exact (Nat.not_lt_zero j.val hj).elim
  colStrict i hi j hj := by
    -- Column strictness is vacuous since only row 0 has boxes
    -- Row i+1 has 0 boxes since i.val + 1 ≠ 0
    have hparts : (NPartition.rowPartition N n hN).parts ⟨i.val + 1, hi⟩ = 0 := by
      simp only [NPartition.rowPartition]
      have : (⟨i.val + 1, hi⟩ : Fin N).val ≠ 0 := Nat.succ_ne_zero i.val
      simp only [this, ↓reduceIte]
    rw [hparts] at hj
    exact (Nat.not_lt_zero j.val hj).elim

/-- Convert an SSYT of row partition shape back to a Sym.
    Row 0 entries form a weakly increasing sequence which gives a multiset. -/
def rowSSYTToSym (hN : 0 < N) (n : ℕ) (T : SSYT (NPartition.rowPartition N n hN)) :
    Sym (Fin N) n := by
  -- Row 0 has n boxes
  have hrow0 : (NPartition.rowPartition N n hN).parts ⟨0, hN⟩ = n := by
    simp [NPartition.rowPartition]
  -- Extract entries from row 0
  let entries0 : Fin n → Fin N := fun j => T.entries ⟨0, hN⟩ ⟨j.val, by rw [hrow0]; exact j.isLt⟩
  exact weaklyIncreasingToSym n entries0

/-- symToRowSSYT and rowSSYTToSym are inverses (Sym → SSYT → Sym). -/
theorem rowSSYTToSym_symToRowSSYT (hN : 0 < N) (n : ℕ) (s : Sym (Fin N) n) :
    rowSSYTToSym hN n (symToRowSSYT hN n s) = s := by
  unfold rowSSYTToSym symToRowSSYT
  -- The function is equivalent to (symToWeaklyIncreasing n s).val
  convert weaklyIncreasingToSym_symToWeaklyIncreasing n s using 1

/-- symToRowSSYT preserves monomials. -/
theorem symToRowSSYT_toMonomial (hN : 0 < N) (n : ℕ) (s : Sym (Fin N) n) :
    (symToRowSSYT hN n s).toMonomial (R := R) = (s.1.map MvPolynomial.X).prod := by
  -- The product over the single-row tableau equals the Sym monomial
  -- This follows from sym_monomial_eq_weaklyIncreasing_prod
  unfold SSYT.toMonomial symToRowSSYT
  simp only
  -- The product over i : Fin N simplifies because only i = 0 contributes
  rw [Finset.prod_eq_single ⟨0, hN⟩]
  · -- Main case: i = 0
    rw [sym_monomial_eq_weaklyIncreasing_prod]
    apply Finset.prod_congr rfl
    intro j _
    congr 1
  · -- Other rows contribute 1 (empty product)
    intro i _ hi
    have hi_pos : 0 < i.val := by
      by_contra h
      push_neg at h
      have : i.val = 0 := Nat.eq_zero_of_le_zero h
      apply hi
      ext
      exact this
    have hparts : (NPartition.rowPartition N n hN).parts i = 0 :=
      NPartition.rowPartition_parts_pos N n hN i hi_pos
    -- Since parts i = 0, Fin (parts i) is empty, so the product is 1
    haveI hemp : IsEmpty (Fin ((NPartition.rowPartition N n hN).parts i)) := by
      simp only [hparts]
      exact Fin.isEmpty
    exact Fintype.prod_empty _
  · -- ⟨0, hN⟩ ∈ univ is always true
    intro h
    exact (h (Finset.mem_univ _)).elim

/-- The complete homogeneous symmetric polynomial h_n equals the Schur polynomial
    indexed by the row partition (n, 0, ..., 0).

    This is because:
    - The only SSYT of shape (n, 0, ..., 0) is a single row of n boxes
    - A single row SSYT with entries from Fin N is exactly a weakly increasing sequence
    - Such sequences correspond to multisets of size n from Fin N
    - The monomial of such a tableau is exactly (s.1.map X).prod for s : Sym (Fin N) n

    This lemma enables deriving the horizontal Pieri rule from Littlewood-Richardson. -/
theorem hsymm_eq_schur_rowPartition (hN : 0 < N) (n : ℕ) :
    hsymm (Fin N) R n = schur (NPartition.rowPartition N n hN) := by
  -- Both sides are sums of monomials
  -- hsymm sums over Sym (Fin N) n
  -- schur sums over SSYT of row partition shape
  -- We use symToRowSSYT as a bijection
  unfold hsymm schur
  apply Finset.sum_bij (fun s _ => symToRowSSYT hN n s)
  · -- symToRowSSYT maps to ssytFinset
    intro s _
    exact ssytFinset_mem _ _
  · -- symToRowSSYT is injective
    intro s₁ _ s₂ _ h
    have h' : rowSSYTToSym hN n (symToRowSSYT hN n s₁) =
              rowSSYTToSym hN n (symToRowSSYT hN n s₂) := by rw [h]
    simp only [rowSSYTToSym_symToRowSSYT] at h'
    exact h'
  · -- symToRowSSYT is surjective onto ssytFinset
    intro T _
    refine ⟨rowSSYTToSym hN n T, Finset.mem_univ _, ?_⟩
    -- Need to show symToRowSSYT (rowSSYTToSym T) = T
    -- This requires showing that for a weakly increasing sequence,
    -- sorting gives back the same sequence
    apply SSYT.eq_of_entries_eq
    funext i j
    unfold symToRowSSYT rowSSYTToSym weaklyIncreasingToSym
    simp only
    split_ifs with hi
    · -- Row 0 case: need to show sorted entries = original entries
      have hrow0 : (NPartition.rowPartition N n hN).parts ⟨0, hN⟩ = n := by
        simp [NPartition.rowPartition]
      -- Define the entries function from row 0
      let entries0 : Fin n → Fin N := fun k =>
        T.entries ⟨0, hN⟩ ⟨k.val, by rw [hrow0]; exact k.isLt⟩
      -- entries0 is weakly increasing by SSYT row condition
      have h_weak : ∀ a b : Fin n, a ≤ b → entries0 a ≤ entries0 b := by
        intro a b hab
        exact T.rowWeak ⟨0, hN⟩ _ _ hab
      -- Use the helper lemma: sorting a weakly increasing list gives the same list
      have hsort := sort_weaklyIncreasing_list_eq entries0 h_weak
      -- Goal: sorted[j.val] = T.entries i j where i.val = 0
      have hi_eq : i = ⟨0, hN⟩ := Fin.ext hi
      subst hi_eq
      -- After subst, need: sorted[j.val] = T.entries ⟨0, hN⟩ j
      have hlen : ((Multiset.ofList ((List.finRange n).map entries0)).sort (· ≤ ·)).length = n := by
        rw [hsort]; simp
      simp only [symToWeaklyIncreasing, List.get_eq_getElem]
      -- Goal: sorted[j.val] = T.entries ⟨0, hN⟩ j
      -- where sorted = (ofList (finRange.map entries0)).sort
      -- Use List.getElem_of_eq to rewrite sorted to the original list
      have hj_bound : j.val < ((Multiset.ofList ((List.finRange n).map entries0)).sort (· ≤ ·)).length := by
        simp only [hlen]; exact j.isLt
      rw [List.getElem_of_eq hsort hj_bound]
      -- Now goal is: (finRange.map entries0)[j.val] = T.entries ⟨0, hN⟩ j
      simp only [List.getElem_map, List.getElem_finRange]
      -- entries0 ⟨j.val, _⟩ = T.entries ⟨0, hN⟩ ⟨j.val, _⟩ by definition
      -- And T.entries ⟨0, hN⟩ ⟨j.val, _⟩ = T.entries ⟨0, hN⟩ j by Fin.ext
      rfl
    · -- Non-row-0 case: vacuously true since j is from Fin 0
      have hj := j.isLt
      simp only [NPartition.rowPartition, hi, ↓reduceIte] at hj
      exact (Nat.not_lt_zero j.val hj).elim
  · -- Monomial preservation
    intro s _
    exact (symToRowSSYT_toMonomial hN n s).symm

/-- Convert a subset of size n to an SSYT of column partition shape.
    The sorted subset gives a strictly increasing sequence for column 0. -/
def finsetToColSSYT (n : ℕ) (hn : n ≤ N) (s : Finset (Fin N)) (hs : s.card = n) :
    SSYT (NPartition.colPartition N n hn) where
  entries i j :=
    if hi : i.val < n then
      (s.sort (· ≤ ·)).get ⟨i.val, by rw [Finset.length_sort, hs]; exact hi⟩
    else
      (Fin.elim0 (by
        have hj := j.isLt
        simp only [NPartition.colPartition, hi, ↓reduceIte] at hj
        exact ⟨j.val, hj⟩ : Fin 0))
  rowWeak i j k _ := by
    simp only
    split_ifs with hi
    · rfl
    · have hj := j.isLt
      simp only [NPartition.colPartition, hi, ↓reduceIte] at hj
      exact (Nat.not_lt_zero j.val hj).elim
  colStrict i hi j hj := by
    simp only
    have hi_lt_n : i.val < n := by
      have hj' := j.isLt
      simp only [NPartition.colPartition] at hj'
      by_cases h : i.val < n
      · exact h
      · simp only [h, ↓reduceIte] at hj'
        exact (Nat.not_lt_zero j.val hj').elim
    have hi1_lt_n : i.val + 1 < n := by
      simp only [NPartition.colPartition] at hj
      by_cases h : i.val + 1 < n
      · exact h
      · simp only [h, ↓reduceIte] at hj
        exact (Nat.not_lt_zero j.val hj).elim
    simp only [hi_lt_n, hi1_lt_n]
    have hlen1 : i.val < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort, hs]; omega
    have hlen2 : i.val + 1 < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort, hs]; omega
    have hlt : (⟨i.val, hlen1⟩ : Fin (s.sort (· ≤ ·)).length) < ⟨i.val + 1, hlen2⟩ := by
      simp only [Fin.lt_def]; omega
    convert s.sortedLT_sort hlt

/-- Helper for extracting entry from column SSYT -/
def colSSYTEntry (n : ℕ) (hn : n ≤ N) (T : SSYT (NPartition.colPartition N n hn))
    (k : ℕ) (hk : k < n) : Fin N :=
  have hkN : k < N := Nat.lt_of_lt_of_le hk hn
  have h0 : 0 < (NPartition.colPartition N n hn).parts ⟨k, hkN⟩ := by
    simp [NPartition.colPartition, hk]
  T.entries ⟨k, hkN⟩ ⟨0, h0⟩

/-- Inverse bijection: SSYT(colPartition) → Finset -/
def colSSYTToFinset (n : ℕ) (hn : n ≤ N) (T : SSYT (NPartition.colPartition N n hn)) :
    Finset (Fin N) :=
  Finset.univ.image (fun k : Fin n => colSSYTEntry n hn T k.val k.isLt)

/-- Column entries are strictly increasing - consecutive case -/
theorem colSSYTEntry_succ_lt (n : ℕ) (hn : n ≤ N)
    (T : SSYT (NPartition.colPartition N n hn))
    (k : ℕ) (hk : k < n) (hk1 : k + 1 < n) :
    colSSYTEntry n hn T k hk < colSSYTEntry n hn T (k + 1) hk1 := by
  unfold colSSYTEntry
  have hkN : k < N := Nat.lt_of_lt_of_le hk hn
  have hk1N : k + 1 < N := Nat.lt_of_lt_of_le hk1 hn
  have hj : (0 : ℕ) < (NPartition.colPartition N n hn).parts ⟨k + 1, hk1N⟩ := by
    simp [NPartition.colPartition, hk1]
  exact T.colStrict ⟨k, hkN⟩ hk1N ⟨0, by simp [NPartition.colPartition, hk]⟩ hj

/-- Column entries are strictly increasing - general case -/
theorem colSSYTEntry_strictMono (n : ℕ) (hn : n ≤ N)
    (T : SSYT (NPartition.colPartition N n hn))
    (k₁ k₂ : ℕ) (hk₁ : k₁ < n) (hk₂ : k₂ < n) (hlt : k₁ < k₂) :
    colSSYTEntry n hn T k₁ hk₁ < colSSYTEntry n hn T k₂ hk₂ := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hlt
  clear hlt
  induction d generalizing k₁ with
  | zero =>
    simp only [Nat.add_zero] at hd
    subst hd
    exact colSSYTEntry_succ_lt n hn T k₁ hk₁ hk₂
  | succ d ih =>
    have hk1p1_lt_n : k₁ + 1 < n := by omega
    have h1 := colSSYTEntry_succ_lt n hn T k₁ hk₁ hk1p1_lt_n
    have h2 := ih (k₁ + 1) hk1p1_lt_n (by omega)
    exact lt_trans h1 h2

/-- The image has cardinality n because entries are strictly increasing -/
theorem colSSYTToFinset_card (n : ℕ) (hn : n ≤ N)
    (T : SSYT (NPartition.colPartition N n hn)) :
    (colSSYTToFinset n hn T).card = n := by
  unfold colSSYTToFinset
  rw [Finset.card_image_of_injective]
  · simp
  · intro k₁ k₂ heq
    simp only at heq
    by_contra hne
    rcases Nat.lt_trichotomy k₁.val k₂.val with hlt | heq' | hgt
    · have hstrict := colSSYTEntry_strictMono n hn T k₁.val k₂.val k₁.isLt k₂.isLt hlt
      rw [heq] at hstrict
      exact lt_irrefl _ hstrict
    · exact hne (Fin.ext heq')
    · have hstrict := colSSYTEntry_strictMono n hn T k₂.val k₁.val k₂.isLt k₁.isLt hgt
      rw [heq] at hstrict
      exact lt_irrefl _ hstrict

/-- Sorting colSSYTToFinset gives back the original entries as a list -/
theorem colSSYTToFinset_sort_eq (n : ℕ) (hn : n ≤ N)
    (T : SSYT (NPartition.colPartition N n hn)) :
    (colSSYTToFinset n hn T).sort (· ≤ ·) =
    List.ofFn (fun k : Fin n => colSSYTEntry n hn T k.val k.isLt) := by
  -- colSSYTToFinset = univ.image f = (List.ofFn f).toFinset
  unfold colSSYTToFinset
  rw [Fin.univ_image_def]
  -- Now use List.toFinset_sort
  have hinj : Function.Injective (fun k : Fin n => colSSYTEntry n hn T k.val k.isLt) := by
    intro k₁ k₂ heq
    by_contra hne
    rcases Nat.lt_trichotomy k₁.val k₂.val with hlt | heq' | hgt
    · have hstrict := colSSYTEntry_strictMono n hn T k₁.val k₂.val k₁.isLt k₂.isLt hlt
      simp only at heq
      rw [heq] at hstrict
      exact lt_irrefl _ hstrict
    · exact hne (Fin.ext heq')
    · have hstrict := colSSYTEntry_strictMono n hn T k₂.val k₁.val k₂.isLt k₁.isLt hgt
      simp only at heq
      rw [heq] at hstrict
      exact lt_irrefl _ hstrict
  rw [List.toFinset_sort (· ≤ ·) (List.nodup_ofFn.mpr hinj)]
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact le_of_lt (colSSYTEntry_strictMono n hn T i.val j.val i.isLt j.isLt hij)

/-- Helper: product over `Fin (if P then 1 else 0)` simplifies based on P -/
private lemma prod_fin_ite {α : Type*} [CommMonoid α] (P : Prop) [Decidable P]
    (f : Fin (if P then 1 else 0) → α) :
    ∏ j : Fin (if P then 1 else 0), f j =
    if h : P then f ⟨0, by simp [h]⟩ else 1 := by
  split_ifs with h
  · have heq : (if P then 1 else 0) = 1 := if_pos h
    rw [Fintype.prod_eq_single (⟨0, by simp [heq]⟩ : Fin (if P then 1 else 0))]
    intro b hb
    have hb0 : b.val = 0 := by
      have hlt : b.val < (if P then 1 else 0) := b.isLt
      simp only [h, ite_true] at hlt
      omega
    exact (hb (Fin.ext hb0)).elim
  · have heq : (if P then 1 else 0) = 0 := if_neg h
    have hEmpty : IsEmpty (Fin (if P then 1 else 0)) := by rw [heq]; exact Fin.isEmpty
    haveI : IsEmpty (Fin (if P then 1 else 0)) := hEmpty
    exact Fintype.prod_empty f

/-- Helper: product over list map equals product over finset -/
private lemma list_map_prod_eq_finset_prod {α : Type*} [DecidableEq α] {M : Type*} [CommMonoid M]
    (l : List α) (f : α → M) (hl : l.Nodup) :
    (l.map f).prod = ∏ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    have hnodup' : l.Nodup := hl.2
    have hna : a ∉ l := hl.1
    simp only [List.map_cons, List.prod_cons, List.toFinset_cons]
    rw [Finset.prod_insert (by simp [hna])]
    congr 1
    exact ih hnodup'

/-- finsetToColSSYT preserves monomials -/
theorem finsetToColSSYT_toMonomial (n : ℕ) (hn : n ≤ N) (s : Finset (Fin N)) (hs : s.card = n) :
    (finsetToColSSYT n hn s hs).toMonomial (R := R) = ∏ i ∈ s, MvPolynomial.X i := by
  -- The proof establishes that the monomial of the column SSYT equals the product over s.
  -- The SSYT has entries in rows 0..n-1 (each with 1 box), and no boxes elsewhere.
  -- For rows i < n: one box with entry = (s.sort).get i
  -- For rows i ≥ n: no boxes (empty product = 1)
  -- So the monomial is ∏_{i < n} X((s.sort).get i) = ∏_{x ∈ s} X(x)
  unfold SSYT.toMonomial
  -- Step 1: Simplify inner product using prod_fin_ite
  have h1 : ∀ i : Fin N, ∏ j : Fin ((NPartition.colPartition N n hn).parts i),
      MvPolynomial.X ((finsetToColSSYT n hn s hs).entries i j) =
      if hi : i.val < n then
        MvPolynomial.X ((s.sort (· ≤ ·)).get ⟨i.val, by rw [Finset.length_sort, hs]; exact hi⟩)
      else (1 : MvPolynomial (Fin N) R) := by
    intro i
    simp only [NPartition.colPartition]
    rw [prod_fin_ite (i.val < n)]
    split_ifs with hi <;> simp only [finsetToColSSYT, hi, dite_true]
  conv_lhs => arg 2; ext i; rw [h1 i]
  -- Step 2: Product over Fin N with condition equals product over Fin n
  rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ) (p := fun i : Fin N => i.val < n)]
  have h2 : ∏ i ∈ Finset.univ.filter (fun i : Fin N => ¬i.val < n),
      (if hi : i.val < n then
        MvPolynomial.X ((s.sort (· ≤ ·)).get ⟨i.val, by rw [Finset.length_sort, hs]; exact hi⟩)
      else (1 : MvPolynomial (Fin N) R)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hi, dite_false]
  rw [h2, mul_one]
  -- Step 3: Reindex from filter to image
  have h_bij : (Finset.univ.filter (fun i : Fin N => i.val < n)) =
      Finset.univ.image (fun k : Fin n => ⟨k.val, lt_of_lt_of_le k.isLt hn⟩) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · intro ⟨k, hk⟩
      rw [Fin.ext_iff] at hk
      rw [← hk]
      exact k.isLt
  rw [h_bij, Finset.prod_image]
  · -- Step 4: Simplify dite with known condition
    have h3 : ∀ k : Fin n, (if hi : (⟨k.val, lt_of_lt_of_le k.isLt hn⟩ : Fin N).val < n then
        MvPolynomial.X ((s.sort (· ≤ ·)).get ⟨(⟨k.val, lt_of_lt_of_le k.isLt hn⟩ : Fin N).val,
          by rw [Finset.length_sort, hs]; exact hi⟩)
      else (1 : MvPolynomial (Fin N) R)) =
      MvPolynomial.X ((s.sort (· ≤ ·)).get ⟨k.val, by rw [Finset.length_sort, hs]; exact k.isLt⟩) := by
      intro k
      simp only [k.isLt, dite_true]
    simp_rw [h3]
    -- Step 5: Product over Fin n equals product over s via sorted list
    have hlen : (s.sort (· ≤ ·)).length = n := by rw [Finset.length_sort, hs]
    rw [← List.prod_ofFn]
    have h4 : List.ofFn (fun k : Fin n =>
        (MvPolynomial.X ((s.sort (· ≤ ·)).get ⟨k.val, by rw [hlen]; exact k.isLt⟩) :
          MvPolynomial (Fin N) R)) =
        (s.sort (· ≤ ·)).map MvPolynomial.X := by
      apply List.ext_get
      · simp only [List.length_ofFn, List.length_map, hlen]
      · intro i _ _; simp only [List.get_eq_getElem, List.getElem_ofFn, List.getElem_map]
    rw [h4, list_map_prod_eq_finset_prod _ _ (s.sort_nodup (· ≤ ·)), s.sort_toFinset (· ≤ ·)]
  · -- Injectivity of the embedding Fin n → Fin N
    intro k₁ _ k₂ _ heq
    simp only [Fin.mk.injEq] at heq
    exact Fin.ext heq


/-- The elementary symmetric polynomial e_n equals the Schur polynomial
    indexed by the column partition (1, 1, ..., 1, 0, ..., 0) with n ones.

    This is because:
    - The only SSYT of shape (1, 1, ..., 1, 0, ..., 0) is a single column of n boxes
    - A single column SSYT with entries from Fin N must have strictly increasing entries
    - Such sequences correspond to subsets of size n from Fin N
    - The monomial of such a tableau is exactly ∏_{i ∈ s} X_i for s : Finset (Fin N)

    This lemma enables deriving the vertical Pieri rule from Littlewood-Richardson.

    **Proof structure**:
    1. Both sides are sums of monomials
    2. esymm sums over powersetCard n univ with monomial ∏_{i ∈ s} X_i
    3. schur sums over SSYT of shape (1,...,1,0,...,0) with monomial T.toMonomial
    4. For column partition, SSYT entries in column 0 form strictly increasing sequences
    5. The bijection: s ↦ SSYT with entries = sorted(s) in column 0
    6. Weight preservation: ∏_{i ∈ s} X_i = T.toMonomial -/
theorem esymm_eq_schur_colPartition (n : ℕ) (hn : n ≤ N) :
    esymm (Fin N) R n = schur (NPartition.colPartition N n hn) := by
  -- The proof establishes a bijection between:
  -- - Finset (Fin N) of size n (subsets of size n)
  -- - SSYT of shape (1, 1, ..., 1, 0, ..., 0) (single-column tableaux)
  -- Both have the same monomials.
  unfold esymm schur
  apply Finset.sum_bij (fun s hs => finsetToColSSYT n hn s (Finset.mem_powersetCard.mp hs).2)
  · -- finsetToColSSYT maps to ssytFinset
    intro s _
    exact ssytFinset_mem _ _
  · -- finsetToColSSYT is injective
    intro s₁ hs₁ s₂ hs₂ heq
    have h1 : s₁.card = n := (Finset.mem_powersetCard.mp hs₁).2
    have h2 : s₂.card = n := (Finset.mem_powersetCard.mp hs₂).2
    -- The entries of the SSYT determine the sorted list, which determines the set
    ext x
    have hlen1 : (s₁.sort (· ≤ ·)).length = n := by rw [Finset.length_sort, h1]
    have hlen2 : (s₂.sort (· ≤ ·)).length = n := by rw [Finset.length_sort, h2]
    constructor
    · intro hx
      -- x ∈ s₁ means x appears in s₁.sort at some index
      have hmem1 : x ∈ s₁.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hx
      rw [List.mem_iff_get] at hmem1
      obtain ⟨idx, hget1⟩ := hmem1
      have hidx_lt : idx.val < n := by rw [← hlen1]; exact idx.isLt
      -- The entry at position idx in finsetToColSSYT s₁ is x
      have hentry1 : (finsetToColSSYT n hn s₁ h1).entries ⟨idx.val, Nat.lt_of_lt_of_le hidx_lt hn⟩
          ⟨0, by simp [NPartition.colPartition, hidx_lt]⟩ = x := by
        simp only [finsetToColSSYT]
        simp only [hidx_lt, ↓reduceDIte, hget1]
      -- Since finsetToColSSYT s₁ = finsetToColSSYT s₂, the same entry in s₂ is x
      rw [heq] at hentry1
      simp only [finsetToColSSYT, hidx_lt, ↓reduceDIte] at hentry1
      have hmem2 : (s₂.sort (· ≤ ·)).get ⟨idx.val, by rw [hlen2]; exact hidx_lt⟩ ∈ s₂.sort (· ≤ ·) :=
        List.get_mem _ _
      rw [← hentry1]
      exact (Finset.mem_sort (· ≤ ·)).mp hmem2
    · intro hx
      -- Symmetric argument
      have hmem2 : x ∈ s₂.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hx
      rw [List.mem_iff_get] at hmem2
      obtain ⟨idx, hget2⟩ := hmem2
      have hidx_lt : idx.val < n := by rw [← hlen2]; exact idx.isLt
      have hentry2 : (finsetToColSSYT n hn s₂ h2).entries ⟨idx.val, Nat.lt_of_lt_of_le hidx_lt hn⟩
          ⟨0, by simp [NPartition.colPartition, hidx_lt]⟩ = x := by
        simp only [finsetToColSSYT]
        simp only [hidx_lt, ↓reduceDIte, hget2]
      rw [← heq] at hentry2
      simp only [finsetToColSSYT, hidx_lt, ↓reduceDIte] at hentry2
      have hmem1 : (s₁.sort (· ≤ ·)).get ⟨idx.val, by rw [hlen1]; exact hidx_lt⟩ ∈ s₁.sort (· ≤ ·) :=
        List.get_mem _ _
      rw [← hentry2]
      exact (Finset.mem_sort (· ≤ ·)).mp hmem1
  · -- finsetToColSSYT is surjective onto ssytFinset
    intro T _
    -- The proof shows that for any SSYT T of column partition shape,
    -- colSSYTToFinset T is a preimage under finsetToColSSYT.
    -- This follows because:
    -- 1. colSSYTToFinset extracts the entries of T (which form a strictly increasing sequence)
    -- 2. Sorting colSSYTToFinset gives back the original entries
    -- 3. finsetToColSSYT on this sorted set reconstructs T
    have hcard := colSSYTToFinset_card n hn T
    refine ⟨colSSYTToFinset n hn T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
    -- Show the two SSYTs have equal entries
    have hsort := colSSYTToFinset_sort_eq n hn T
    -- Two SSYTs are equal iff their entries are equal
    cases' T with T_entries T_rowWeak T_colStrict
    simp only [finsetToColSSYT]
    congr 1
    funext i
    funext j
    by_cases hi : i.val < n
    · -- Case i.val < n: both have an entry in column 0
      simp only [hi, dite_true]
      -- The sorted list of colSSYTToFinset is List.ofFn (colSSYTEntry ...)
      -- j must be ⟨0, _⟩ since parts i = 1 for i.val < n
      have hj0 : j.val = 0 := by
        have hj_lt := j.isLt
        simp only [NPartition.colPartition, hi, ite_true] at hj_lt
        omega
      -- Get the entry at position i.val from the sorted list
      -- LHS: sorted_list.get ⟨i.val, _⟩
      -- RHS: T_entries i j
      -- Using hsort: sorted_list = List.ofFn (colSSYTEntry ...)
      -- So LHS = colSSYTEntry n hn T i.val hi = T_entries ⟨i.val, _⟩ ⟨0, _⟩
      simp only [hsort, List.get_eq_getElem, List.getElem_ofFn]
      -- Now show colSSYTEntry equals T_entries
      unfold colSSYTEntry
      simp only []  -- normalizes goal for congr
      -- Need to show T_entries ⟨i.val, _⟩ ⟨0, _⟩ = T_entries i j
      -- This follows because j.val = 0
      congr 1
      exact Fin.ext hj0.symm
    · -- Case i.val ≥ n: both have no entries (Fin 0 for column index)
      simp only [hi, dite_false]
      -- j : Fin (parts i) where parts i = 0 for i.val ≥ n
      have hj_absurd := j.isLt
      simp only [NPartition.colPartition, hi, ite_false] at hj_absurd
      exact (Nat.not_lt_zero j.val hj_absurd).elim
  · -- Monomial preservation
    intro s hs
    exact (finsetToColSSYT_toMonomial n hn s (Finset.mem_powersetCard.mp hs).2).symm


/-- First Pieri rule (Theorem thm.sf.pieri(a))
    Label: exe.sf.pieri

    h_n · s_μ = ∑_{λ/μ is horizontal n-strip} s_λ

    where h_n is the n-th complete homogeneous symmetric polynomial.

    This is Exercise exe.sf.pieri in the TeX source. The proof requires the
    Robinson-Schensted-Knuth (RSK) row insertion bijection, which is not yet
    formalized in this project. -/
theorem pieri_horizontal (n : ℕ) (mu : NPartition N) :
    hsymm (Fin N) R n * schur mu =
      ∑ lam ∈ horizontalNStripPartitions mu n, schur lam := by
  sorry -- [exercise] Exercise exe.sf.pieri from TeX source (requires RSK row insertion)

/-- Second Pieri rule (Theorem thm.sf.pieri(b))
    Label: exe.sf.pieri

    e_n · s_μ = ∑_{λ/μ is vertical n-strip} s_λ

    where e_n is the n-th elementary symmetric polynomial.

    This is Exercise exe.sf.pieri in the TeX source. The proof requires the
    Robinson-Schensted-Knuth (RSK) column insertion bijection, or alternatively
    can be derived from `pieri_horizontal` via the ω-involution. -/
theorem pieri_vertical (n : ℕ) (mu : NPartition N) :
    esymm (Fin N) R n * schur mu =
      ∑ lam ∈ verticalNStripPartitions mu n, schur lam := by
  sorry -- [exercise] Exercise exe.sf.pieri from TeX source (requires RSK column insertion)

/-!
## The Jacobi-Trudi Identities

The Jacobi-Trudi identities express skew Schur polynomials as determinants
of matrices involving h_n or e_n.
-/

/-- Extended h_n: h_n = 0 for n < 0, h_0 = 1.
    This is needed since the Jacobi-Trudi formula may have negative indices. -/
noncomputable def hsymmExt (n : ℤ) : MvPolynomial (Fin N) R :=
  if 0 ≤ n then hsymm (Fin N) R n.toNat else 0

/-- hsymmExt is symmetric. -/
theorem hsymmExt_isSymmetric (n : ℤ) : (hsymmExt (N := N) (R := R) n).IsSymmetric := by
  unfold hsymmExt
  split_ifs with h
  · exact hsymm_isSymmetric (Fin N) R n.toNat
  · exact IsSymmetric.zero

/-- The Jacobi-Trudi matrix for h (first Jacobi-Trudi formula).
    Entry (i,j) is h_{λᵢ - μⱼ - i + j}. -/
noncomputable def jacobiTrudiMatrixH (lam mu : Fin N → ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R) :=
  Matrix.of fun i j =>
    hsymmExt ((lam i : ℤ) - (mu j : ℤ) - (i.val : ℤ) + (j.val : ℤ))

/-- Second Jacobi-Trudi formula (Exercise exe.sf.jt-e)
    Label: thm.sf.jt-e
    Status: EXERCISE (exe.sf.jt-e in tex source)

    s_{λ/μ} = det((e_{λᵢᵗ - μⱼᵗ - i + j})_{1 ≤ i,j ≤ N})

    where λᵗ and μᵗ are the transposes of λ and μ, and e_n denotes the n-th
    elementary symmetric polynomial (with e_n = 0 for n < 0).

    This is a 6-point exercise with no hint provided in the TeX source.

    ## References

    - [Stanley, EC2, Theorem 7.16.1]
    - [Grinberg-Reiner, Section 2.4]
    - [Fulton, Young Tableaux, Section 4.3] -/
theorem jacobiTrudi_e (lam mu : Fin N → ℕ)
    (lamt muT : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hlamt : ∀ i j : Fin N, i ≤ j → lamt j ≤ lamt i)
    (hmuT : ∀ i j : Fin N, i ≤ j → muT j ≤ muT i)
    (hcontained : ∀ i, mu i ≤ lam i)
    (htranspose_lam : NPartition.IsTranspose lam lamt)
    (htranspose_mu : NPartition.IsTranspose mu muT)
    :
    skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ =
      (Matrix.of fun i j =>
        let n := (lamt i : ℤ) - (muT j : ℤ) - (i.val : ℤ) + (j.val : ℤ)
        if 0 ≤ n then esymm (Fin N) R n.toNat else 0).det := by
  sorry -- [exercise]

/-!
## LGV Lemma Connection

The proof of the first Jacobi-Trudi formula uses the LGV lemma.
We outline the key constructions here.
-/

/-!
### Source and Target Vertices for Jacobi-Trudi

For the Jacobi-Trudi identity, we define:
- Source vertices: Aᵢ = (μᵢ - i, 1) for i ∈ [N]
- Target vertices: Bⱼ = (λⱼ - j, N) for j ∈ [N]

These vertices satisfy the sorting conditions required by the LGV lemma
(Corollary cor.lgv.kpaths.wt-np):
- x-coordinates are weakly decreasing: x(A₁) ≥ x(A₂) ≥ ... ≥ x(Aₖ)
- y-coordinates are constant (trivially weakly increasing)
-/

/-- The source vertex A_i = (μ_i - i, 1) for the Jacobi-Trudi LGV setup.
    Here 1 represents the "starting height" in the lattice. -/
def jacobiTrudiSourceX (mu : Fin N → ℕ) (i : Fin N) : ℤ :=
  (mu i : ℤ) - (i.val : ℤ)

/-- The target vertex B_j = (λ_j - j, N) for the Jacobi-Trudi LGV setup.
    Here N represents the "ending height" in the lattice. -/
def jacobiTrudiTargetX (lam : Fin N → ℕ) (j : Fin N) : ℤ :=
  (lam j : ℤ) - (j.val : ℤ)

/-- The source x-coordinates are weakly decreasing.
    This follows from the partition being weakly decreasing:
    μᵢ - i ≥ μⱼ - j when i ≤ j, since μᵢ ≥ μⱼ and i ≤ j. -/
theorem jacobiTrudiSourceX_antitone (mu : Fin N → ℕ)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i) :
    ∀ i j : Fin N, i ≤ j → jacobiTrudiSourceX mu j ≤ jacobiTrudiSourceX mu i := by
  intro i j hij
  unfold jacobiTrudiSourceX
  have h1 : (mu j : ℤ) ≤ (mu i : ℤ) := Int.ofNat_le.mpr (hmu i j hij)
  have h2 : (i.val : ℤ) ≤ (j.val : ℤ) := Int.ofNat_le.mpr (Fin.val_fin_le.mpr hij)
  omega

/-- The target x-coordinates are weakly decreasing.
    This follows from the partition being weakly decreasing. -/
theorem jacobiTrudiTargetX_antitone (lam : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
    ∀ i j : Fin N, i ≤ j → jacobiTrudiTargetX lam j ≤ jacobiTrudiTargetX lam i := by
  intro i j hij
  unfold jacobiTrudiTargetX
  have h1 : (lam j : ℤ) ≤ (lam i : ℤ) := Int.ofNat_le.mpr (hlam i j hij)
  have h2 : (i.val : ℤ) ≤ (j.val : ℤ) := Int.ofNat_le.mpr (Fin.val_fin_le.mpr hij)
  omega

/-- The path from A_i to B_j has length λ_j - μ_i - j + i (when non-negative).
    This equals the index of h in the Jacobi-Trudi matrix entry (j, i). -/
theorem jacobiTrudiPathLength (lam mu : Fin N → ℕ) (i j : Fin N) :
    jacobiTrudiTargetX lam j - jacobiTrudiSourceX mu i =
      (lam j : ℤ) - (mu i : ℤ) - (j.val : ℤ) + (i.val : ℤ) := by
  unfold jacobiTrudiTargetX jacobiTrudiSourceX
  ring

/-- The Jacobi-Trudi matrix entry (i, j) equals h_{path length from A_j to B_i}.
    Note: The path is from source A_j to target B_i. This matches the LGV convention
    where M_{i,j} = ∑_{p : A_i → B_j} w(p), but with the matrix transposed.
    Equivalently, the Jacobi-Trudi matrix is the transpose of the LGV path weight matrix. -/
theorem jacobiTrudiMatrixH_eq_pathLength (lam mu : Fin N → ℕ) (i j : Fin N) :
    jacobiTrudiMatrixH (R := R) lam mu i j =
      hsymmExt (N := N) (R := R) (jacobiTrudiTargetX lam i - jacobiTrudiSourceX mu j) := by
  unfold jacobiTrudiMatrixH jacobiTrudiTargetX jacobiTrudiSourceX
  simp only [Matrix.of_apply]
  congr 1
  ring

/-- A lattice path in ℤ² from (a, 1) to (c, N) using north and east steps.
    This is the type of paths relevant for the Jacobi-Trudi proof. -/
structure LatticePath (a c : ℤ) where
  /-- The sequence of heights at which east-steps are taken.
      A path from (a, 1) to (c, N) has exactly (c - a) east-steps
      (when c ≥ a), and each east-step occurs at some height in [1, N]. -/
  eastStepHeights : List (Fin N)
  /-- The heights form a weakly increasing sequence (path goes north or east) -/
  weaklyIncreasing : eastStepHeights.IsChain (· ≤ ·)
  /-- The number of east-steps equals c - a (when non-negative) -/
  length_eq : eastStepHeights.length = (c - a).toNat

/-- The weight of a lattice path is the product of x_j for each east-step at height j.
    This corresponds to the weight function w in the source. -/
noncomputable def LatticePath.weight {a c : ℤ} (p : LatticePath (N := N) a c) :
    MvPolynomial (Fin N) R :=
  (p.eastStepHeights.map (fun j => MvPolynomial.X j)).prod

/-- Extensionality lemma for lattice paths. -/
@[ext]
theorem LatticePath.ext {a c : ℤ} {p q : LatticePath (N := N) a c}
    (h : p.eastStepHeights = q.eastStepHeights) : p = q := by
  cases p; cases q; simp_all

/-- Convert a lattice path to a Sym element (multiset of heights). -/
def LatticePath.toSym {a c : ℤ} (p : LatticePath (N := N) a c) : Sym (Fin N) (c - a).toNat :=
  ⟨↑p.eastStepHeights, by simp [p.length_eq]⟩

/-- Convert a Sym element (multiset) to a lattice path by sorting. -/
noncomputable def symToLatticePath {a c : ℤ} (s : Sym (Fin N) (c - a).toNat) :
    LatticePath (N := N) a c where
  eastStepHeights := s.1.sort (· ≤ ·)
  weaklyIncreasing := List.Pairwise.isChain (Multiset.pairwise_sort s.1 (· ≤ ·))
  length_eq := by rw [Multiset.length_sort]; exact s.2

/-- Converting a path to Sym and back gives the original path. -/
lemma symToLatticePath_toSym {a c : ℤ} (p : LatticePath (N := N) a c) :
    symToLatticePath (p.toSym) = p := by
  apply LatticePath.ext
  simp only [symToLatticePath, LatticePath.toSym]
  have hsort_eq : ((↑p.eastStepHeights : Multiset (Fin N)).sort (· ≤ ·) : Multiset (Fin N)) =
                  (↑p.eastStepHeights : Multiset (Fin N)) :=
    Multiset.sort_eq (↑p.eastStepHeights : Multiset (Fin N)) (· ≤ ·)
  have hperm : ((↑p.eastStepHeights : Multiset (Fin N)).sort (· ≤ ·)).Perm p.eastStepHeights :=
    Quotient.exact hsort_eq
  exact hperm.eq_of_pairwise' (Multiset.pairwise_sort (↑p.eastStepHeights : Multiset (Fin N)) (· ≤ ·))
                               p.weaklyIncreasing.pairwise

/-- Converting a Sym to a path and back gives the original Sym. -/
lemma toSym_symToLatticePath {a c : ℤ} (s : Sym (Fin N) (c - a).toNat) :
    (symToLatticePath s).toSym = s := by
  apply Sym.coe_injective
  simp only [LatticePath.toSym, symToLatticePath, Sym.coe_mk]
  exact Multiset.sort_eq s.1 (· ≤ ·)

/-- The equivalence between lattice paths and Sym (multisets). -/
noncomputable def latticePathSymEquiv {a c : ℤ} :
    LatticePath (N := N) a c ≃ Sym (Fin N) (c - a).toNat where
  toFun := LatticePath.toSym
  invFun := symToLatticePath
  left_inv := symToLatticePath_toSym
  right_inv := toSym_symToLatticePath

/-- Fintype instance for LatticePath via the equivalence with Sym. -/
noncomputable instance {a c : ℤ} : Fintype (LatticePath (N := N) a c) :=
  Fintype.ofEquiv _ latticePathSymEquiv.symm

/-- The weight of a path obtained from sorting a Sym equals the Sym product. -/
lemma symToLatticePath_weight {a c : ℤ} (s : Sym (Fin N) (c - a).toNat) :
    (symToLatticePath s).weight (R := R) = (s.1.map (fun j => X j)).prod := by
  simp only [symToLatticePath, LatticePath.weight]
  have hsort : ↑(s.1.sort (· ≤ ·)) = s.1 := Multiset.sort_eq s.1 (· ≤ ·)
  conv_rhs => rw [← hsort, Multiset.map_coe, Multiset.prod_coe]

/-- The set of all lattice paths from (a, 1) to (c, N).
    Empty when c < a (no valid paths), otherwise all paths. -/
noncomputable def latticePathFinset (a c : ℤ) : Finset (LatticePath (N := N) a c) :=
  if 0 ≤ c - a then Finset.univ else ∅

/-- Observation 1 from the proof of Theorem thm.sf.jt-h:
    The sum of path weights from (a, 1) to (c, N) in ℤ² equals h_{c-a}.

    This follows from Proposition prop.lgv.1-paths.ct.
    The key insight is that the weakly increasing sequences of length n
    with entries in [N] are in bijection with multisets of size n from [N],
    which are exactly what h_n counts. -/
theorem pathWeightSum_eq_hsymm (a c : ℤ) :
    ∑ p ∈ latticePathFinset (N := N) a c, p.weight (R := R) = hsymmExt (N := N) (R := R) (c - a) := by
  unfold hsymmExt latticePathFinset
  split_ifs with h
  · -- Case c - a ≥ 0: use the bijection between paths and Sym
    have heq : ∑ p : LatticePath (N := N) a c, p.weight (R := R) =
               ∑ s : Sym (Fin N) (c - a).toNat, (symToLatticePath s).weight (R := R) := by
      apply Finset.sum_equiv latticePathSymEquiv
      · intro p; simp
      · intro p _; simp [latticePathSymEquiv, symToLatticePath_toSym]
    rw [heq]
    rw [Finset.sum_congr rfl (fun s _ => symToLatticePath_weight s)]
    -- hsymm is defined as ∑ s : Sym (Fin N) n, (s.1.map X).prod
    rfl
  · -- Case c - a < 0: both sides are 0
    simp

/-- A non-intersecting path tuple (nipat) from sources A to targets B.
    For Jacobi-Trudi, A_i = (μᵢ - i, 1) and B_i = (λᵢ - i, N). -/
structure Nipat (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) where
  /-- The tuple of paths, one for each i ∈ [N] -/
  paths : (i : Fin N) → LatticePath (N := N)
    ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
  /-- The paths satisfy column-strictness: for i < j, if east steps k (in path i)
      and k' (in path j) correspond to the same tableau column (mu i + k = mu j + k'),
      then the height of path i at step k is strictly less than the height of path j at step k'.
      This is the key property that makes the nipat-SSYT bijection work. -/
  colStrictPaths : ∀ i j : Fin N, i < j →
    ∀ k : ℕ, ∀ hk : k < (paths i).eastStepHeights.length,
    ∀ k' : ℕ, ∀ hk' : k' < (paths j).eastStepHeights.length,
    mu i + k = mu j + k' →
    (paths i).eastStepHeights[k] < (paths j).eastStepHeights[k']

/-- A rectangular Jacobi--Trudi path tuple: `M` paths whose east-step heights
lie in the alphabet `Fin N`.  This separates the determinant size from the
number of variables while retaining the path representation used below. -/
structure RectNipat (N : ℕ) (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) where
  paths : (i : Fin M) → LatticePath (N := N)
    ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
  colStrictPaths : ∀ i j : Fin M, i < j →
    ∀ k : ℕ, ∀ hk : k < (paths i).eastStepHeights.length,
    ∀ k' : ℕ, ∀ hk' : k' < (paths j).eastStepHeights.length,
    mu i + k = mu j + k' →
    (paths i).eastStepHeights[k] < (paths j).eastStepHeights[k']

/-- Weight of a rectangular path tuple. -/
noncomputable def RectNipat.weight {lam mu : Fin M → ℕ}
    {hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : RectNipat N lam mu hlam hmu hcontained) :
    MvPolynomial (Fin N) R :=
  ∏ i : Fin M, (np.paths i).weight

/-- Rectangular path tuples are finite because each component path is finite and
the column condition cuts out a subtype of their finite product. -/
noncomputable instance RectNipat.fintype (N : ℕ) (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    Fintype (RectNipat N lam mu hlam hmu hcontained) := by
  let Paths :=
    (i : Fin M) → LatticePath (N := N)
      ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
  let Good (paths : Paths) : Prop :=
    ∀ i j : Fin M, i < j →
      ∀ k : ℕ, ∀ hk : k < (paths i).eastStepHeights.length,
      ∀ k' : ℕ, ∀ hk' : k' < (paths j).eastStepHeights.length,
      mu i + k = mu j + k' →
      (paths i).eastStepHeights[k] < (paths j).eastStepHeights[k']
  let e : RectNipat N lam mu hlam hmu hcontained ≃ {p : Paths // Good p} :=
    { toFun := fun p => ⟨p.paths, p.colStrictPaths⟩
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun p => by cases p; rfl
      right_inv := fun p => by cases p; rfl }
  exact Fintype.ofEquiv _ e.symm

/-- The weight of a nipat is the product of the weights of its component paths. -/
noncomputable def Nipat.weight {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) : MvPolynomial (Fin N) R :=
  ∏ i : Fin N, (np.paths i).weight

/-- Helper lemma: in a weakly increasing chain, elements at smaller indices are ≤ elements at larger indices. -/
private lemma List.IsChain.getElem_le_getElem_of_le {α : Type*} [Preorder α]
    {l : List α} (h : l.IsChain (· ≤ ·)) {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (hij : i ≤ j) : l[i] ≤ l[j] := by
  induction j with
  | zero => simp_all
  | succ j ih =>
    by_cases hj' : i = j + 1
    · simp [hj']
    · by_cases hij' : i ≤ j
      · have hj'' : j < l.length := by omega
        have h1 : l[i] ≤ l[j] := ih hj'' hij'
        rw [List.isChain_iff_getElem] at h
        have h2 := h j hj
        exact Trans.trans h1 h2
      · omega

/-- The bijection between nipats and SSYT, sending a nipat to the tableau
    whose i-th row contains the heights of east-steps in path i. -/
noncomputable def nipatToSSYT {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) :
    SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ where
  entries := fun i k => (np.paths i).eastStepHeights.get ⟨k.val, by
    have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
      rw [(np.paths i).length_eq]
      simp only [sub_sub_sub_cancel_right]
      have h : mu i ≤ lam i := hcontained i
      omega
    rw [hlen]; exact k.isLt⟩
  rowWeak := fun i j k hjk => by
    simp only [List.get_eq_getElem]
    have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
      rw [(np.paths i).length_eq]
      simp only [sub_sub_sub_cancel_right]
      have h : mu i ≤ lam i := hcontained i
      omega
    have hj_lt : j.val < (np.paths i).eastStepHeights.length := by rw [hlen]; exact j.isLt
    have hk_lt : k.val < (np.paths i).eastStepHeights.length := by rw [hlen]; exact k.isLt
    exact List.IsChain.getElem_le_getElem_of_le (np.paths i).weaklyIncreasing hj_lt hk_lt hjk
  colStrict := fun i hi k hcol hk' => by
    simp only [List.get_eq_getElem]
    -- Unfold the skew partition structure to get direct access to mu and lam
    simp only [] at hcol  -- normalizes hypothesis for omega
    -- Now hcol : mu i + k.val + 1 > mu (i+1) ∧ mu i + k.val + 1 ≤ lam (i+1)
    -- Use explicit index for row i+1
    have hij : i < (⟨i.val + 1, hi⟩ : Fin N) := by simp only [Fin.lt_def]; omega
    -- Path length for row i
    have hlen_i : (np.paths i).eastStepHeights.length = lam i - mu i := by
      rw [(np.paths i).length_eq]
      simp only [sub_sub_sub_cancel_right]
      simp
    have hk_lt : k.val < (np.paths i).eastStepHeights.length := by 
      rw [hlen_i]; exact k.isLt
    -- Path length for row i+1
    have hlen_j : (np.paths ⟨i.val + 1, hi⟩).eastStepHeights.length = 
        lam ⟨i.val + 1, hi⟩ - mu ⟨i.val + 1, hi⟩ := by
      rw [(np.paths ⟨i.val + 1, hi⟩).length_eq]
      simp only [sub_sub_sub_cancel_right]
      simp
    have hk'_lt : (mu i + k.val - mu ⟨i.val + 1, hi⟩) < 
        (np.paths ⟨i.val + 1, hi⟩).eastStepHeights.length := by 
      rw [hlen_j]
      have h1 := hcol.1
      have h2 := hcol.2
      omega
    -- The column condition: mu i + k = mu (i+1) + k'
    have hcol_eq : mu i + k.val = mu ⟨i.val + 1, hi⟩ + (mu i + k.val - mu ⟨i.val + 1, hi⟩) := by
      have h1 := hcol.1
      omega
    -- Apply colStrictPaths
    exact np.colStrictPaths i ⟨i.val + 1, hi⟩ hij k.val hk_lt 
      (mu i + k.val - mu ⟨i.val + 1, hi⟩) hk'_lt hcol_eq

/-- Helper to create a LatticePath from tableau entries for a single row.
    Given entries for row i of a tableau, creates the corresponding lattice path
    with east-steps at the heights given by the entries. -/
def mkLatticePathFromEntries (lam mu : ℕ) (i : ℕ)
    (entries : Fin (lam - mu) → Fin N)
    (hrowWeak : ∀ j k : Fin (lam - mu), j ≤ k → entries j ≤ entries k) :
    LatticePath (N := N) ((mu : ℤ) - (i : ℤ)) ((lam : ℤ) - (i : ℤ)) where
  eastStepHeights := List.ofFn entries
  weaklyIncreasing := by
    rw [List.isChain_iff_pairwise, List.pairwise_ofFn]
    intro j k hjk
    exact hrowWeak j k (le_of_lt hjk)
  length_eq := by
    simp only [List.length_ofFn, sub_sub_sub_cancel_right]
    simp

/-- The inverse bijection from SSYT to nipats, sending a tableau to the nipat
    whose i-th path has east-steps at the heights given by row i of the tableau. -/
noncomputable def ssytToNipat {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩) :
    Nipat lam mu hlam hmu hcontained where
  paths := fun i => mkLatticePathFromEntries (lam i) (mu i) i.val (T.entries i) (T.rowWeak i)
  colStrictPaths := fun i j hij k hk k' hk' hcol_eq => by
    -- Need to show: (paths i).eastStepHeights[k] < (paths j).eastStepHeights[k']
    -- This follows from T.colStrict_nonadjacent.
    -- The column condition hcol_eq : mu i + k = mu j + k' ensures we're in the same column.
    simp only [mkLatticePathFromEntries]
    rw [List.getElem_ofFn, List.getElem_ofFn]
    -- Convert bounds
    have hk_fin : k < lam i - mu i := by simp [mkLatticePathFromEntries] at hk; exact hk
    have hk'_fin : k' < lam j - mu j := by simp [mkLatticePathFromEntries] at hk'; exact hk'
    -- Apply the column-strict lemma for non-adjacent rows
    exact T.colStrict_nonadjacent i j hij ⟨k, hk_fin⟩ ⟨k', hk'_fin⟩ hcol_eq

/-- Two nipats with equal paths are equal. -/
theorem Nipat.eq_of_paths_eq {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np1 np2 : Nipat lam mu hlam hmu hcontained)
    (h : np1.paths = np2.paths) : np1 = np2 := by
  obtain ⟨p1, ni1⟩ := np1
  obtain ⟨p2, ni2⟩ := np2
  simp only at h
  subst h
  rfl

/-- ssytToNipat is a left inverse of nipatToSSYT. -/
theorem ssytToNipat_nipatToSSYT {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) :
    ssytToNipat (nipatToSSYT np) = np := by
  apply Nipat.eq_of_paths_eq
  funext i
  apply LatticePath.ext
  simp only [ssytToNipat, nipatToSSYT, mkLatticePathFromEntries]
  -- Need to show: List.ofFn (fun k => (np.paths i).eastStepHeights[k]) = (np.paths i).eastStepHeights
  have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
    rw [(np.paths i).length_eq]
    simp only [sub_sub_sub_cancel_right]
    have h : mu i ≤ lam i := hcontained i
    omega
  -- The key is that List.ofFn of getElem gives back the original list
  -- We need to show the LHS equals the RHS by showing they have the same elements
  apply List.ext_getElem
  · simp only [List.length_ofFn, hlen]
  · intro n h1 h2
    simp only [List.getElem_ofFn, List.get_eq_getElem]

/-- The length of path i's eastStepHeights equals lam i - mu i. -/
lemma nipat_path_length {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) (i : Fin N) :
    (np.paths i).eastStepHeights.length = lam i - mu i := by
  rw [(np.paths i).length_eq]
  simp only [sub_sub_sub_cancel_right]
  have h : mu i ≤ lam i := hcontained i
  omega

/-- Specification lemma for nipatToSSYT: the entries of row i are the heights
    of the east-steps in path i. This captures the key property of the bijection. -/
lemma nipatToSSYT_entries {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) (i : Fin N) (k : Fin (lam i - mu i)) :
    (nipatToSSYT np).entries i k = (np.paths i).eastStepHeights.get ⟨k.val, by
      rw [nipat_path_length np i]; exact k.isLt⟩ := by
  simp only [nipatToSSYT, List.get_eq_getElem]

/-- Specification lemma for ssytToNipat: the east-step heights of path i are the entries
    of row i of the tableau. This is the inverse specification to nipatToSSYT_entries. -/
lemma ssytToNipat_paths {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩) (i : Fin N) (k : Fin (lam i - mu i)) :
    ((ssytToNipat T).paths i).eastStepHeights.get ⟨k.val, by
      rw [nipat_path_length (ssytToNipat T) i]; exact k.isLt⟩ = T.entries i k := by
  simp only [ssytToNipat, mkLatticePathFromEntries, List.get_ofFn]
  congr 1

/-- nipatToSSYT is a left inverse of ssytToNipat. -/
theorem nipatToSSYT_ssytToNipat {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩) :
    nipatToSSYT (ssytToNipat T) = T := by
  apply SkewSSYT.eq_of_entries_eq
  funext i k
  rw [nipatToSSYT_entries, ssytToNipat_paths]

/-- Converting a list product to a finset product over indices. -/
private lemma list_prod_map_X_eq_finset_prod (l : List (Fin N)) (n : ℕ) (h : l.length = n) :
    (l.map (fun j => MvPolynomial.X (R := R) j)).prod =
    ∏ k : Fin n, MvPolynomial.X (l.get ⟨k.val, by rw [h]; exact k.isLt⟩) := by
  subst h
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.get_cons_succ, List.get]
    rw [mul_comm, ih, mul_comm]

/-- The weight of a nipat equals the monomial of the corresponding tableau. -/
theorem nipatToSSYT_weight {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) :
    np.weight (R := R) = (nipatToSSYT np).toMonomial := by
  unfold Nipat.weight SkewSSYT.toMonomial
  congr 1
  funext i
  unfold LatticePath.weight
  have hlen := nipat_path_length np i
  rw [list_prod_map_X_eq_finset_prod _ _ hlen]
  congr 1

/-- Observation 2 from the proof of Theorem thm.sf.jt-h:
    There is a bijection between nipats from 𝐀 to 𝐁 and SSYT(λ/μ).

    The bijection sends a nipat 𝐩 = (p₁, ..., pₖ) to the tableau T(𝐩)
    where the entries in row i are the heights of the east-steps of pᵢ.

    Moreover, the weight of a nipat equals the monomial x_T of the
    corresponding tableau. -/
theorem nipat_ssyt_bijection (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    ∃ f : Nipat lam mu hlam hmu hcontained →
        SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩,
      Function.Bijective f ∧
      ∀ np, np.weight (R := R) = (f np).toMonomial := by
  use nipatToSSYT
  constructor
  · -- Prove bijectivity using ssytToNipat as the inverse
    constructor
    · -- Injective: if nipatToSSYT np1 = nipatToSSYT np2, then np1 = np2
      intro np1 np2 h
      rw [← ssytToNipat_nipatToSSYT np1, ← ssytToNipat_nipatToSSYT np2, h]
    · -- Surjective: for any T, there exists np such that nipatToSSYT np = T
      intro T
      use ssytToNipat T
      exact nipatToSSYT_ssytToNipat T
  · -- Weight preservation
    exact nipatToSSYT_weight

/-! ### Fintype instance for Nipat via the bijection with SkewSSYT

The `Nipat` type is finite because it is in bijection with `SkewSSYT`, which is finite.
We establish this by constructing an equivalence using `nipatToSSYT` and `ssytToNipat`. -/

/-- Fintype instance for SkewSSYT via the equivalence with valid fillings. -/
noncomputable instance SkewSSYT.fintype (s : SkewPartition N) : Fintype (SkewSSYT s) := by
  let S := {f : SkewFilling s // isSSYTFilling s f}
  let e : S ≃ SkewSSYT s := {
    toFun := fun ⟨f, hf⟩ => fillingToSkewSSYT f hf
    invFun := fun T => ⟨T.entries, T.toFilling_isSSYTFilling⟩
    left_inv := fun ⟨f, hf⟩ => by simp [fillingToSkewSSYT]
    right_inv := fun T => by cases T; rfl
  }
  exact Fintype.ofEquiv S e

/-- The equivalence between Nipat and SkewSSYT, established by the bijection functions. -/
noncomputable def nipatSSYTEquiv (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    Nipat lam mu hlam hmu hcontained ≃
      SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ where
  toFun := nipatToSSYT
  invFun := ssytToNipat
  left_inv := ssytToNipat_nipatToSSYT
  right_inv := nipatToSSYT_ssytToNipat

/-- Fintype instance for Nipat via the equivalence with SkewSSYT. -/
noncomputable instance Nipat.fintype (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    Fintype (Nipat lam mu hlam hmu hcontained) :=
  Fintype.ofEquiv _ (nipatSSYTEquiv lam mu hlam hmu hcontained).symm

/-- The finite set of all nipats for given partitions λ/μ. -/
noncomputable def nipatFinset' (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    Finset (Nipat lam mu hlam hmu hcontained) :=
  Finset.univ

/-- The sum of nipat weights equals the sum of SSYT monomials.
    This follows from the bijection and weight preservation. -/
theorem nipatWeightSum_eq_ssytSum (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) =
      ∑ T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩, T.toMonomial := by
  -- Use the equivalence nipatSSYTEquiv to rewrite the sum
  -- The key facts are:
  -- 1. nipatSSYTEquiv is an equivalence (bijection)
  -- 2. nipatToSSYT_weight: np.weight = (nipatToSSYT np).toMonomial
  -- The proof follows by Equiv.sum_comp
  let e := nipatSSYTEquiv lam mu hlam hmu hcontained
  have h1 : ∀ np, np.weight (R := R) = (e np).toMonomial := nipatToSSYT_weight
  simp_rw [h1]
  exact Equiv.sum_comp e (fun T => T.toMonomial)

/-- The sum of nipat weights equals skewSchur.
    This combines the bijection with the definition of skewSchur. -/
theorem nipatWeightSum_eq_skewSchur (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) =
      skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ := by
  rw [nipatWeightSum_eq_ssytSum]
  -- skewSchur is defined as ∑ T ∈ skewSSYTFinset s, T.toMonomial
  -- We need to show this equals ∑ T : SkewSSYT s, T.toMonomial
  unfold skewSchur
  -- The sum over skewSSYTFinset equals the sum over all SkewSSYT
  symm
  apply Finset.sum_bij (fun T _ => T)
  · intro T _; exact Finset.mem_univ T
  · intro T₁ _ T₂ _ h; exact h
  · intro T _; exact ⟨T, skewSSYTFinset_mem _ T, rfl⟩
  · intro T _; rfl

/-!
### LGV Infrastructure for Jacobi-Trudi

The proof of `det_jacobiTrudiMatrixH_eq_nipatSum` requires bridging this file's
`LatticePath` and `Nipat` types with the LGV infrastructure in LGV2.lean.

We define:
1. Source vertices A_i = (μ_i - i, 1) and target vertices B_j = (λ_j - j, N) in ℤ²
2. An arc weight function that assigns X_j to east-steps at height j
3. Helper lemmas connecting the path weight sum to h_n

The key insight is that:
- The Jacobi-Trudi matrix entry (i, j) = h_{λᵢ - μⱼ - i + j}
- This equals the sum of path weights from A_j to B_i
- By LGV nonpermutable, det = sum over non-intersecting path tuples
- Non-intersecting path tuples correspond exactly to our Nipat type
-/

/-- The source k-vertex for the Jacobi-Trudi LGV setup: A_i = (μ_i - i, 1).
    The y-coordinate 1 represents the starting height in the lattice. -/
def jacobiTrudiSourceVertex (mu : Fin N → ℕ) : LGV.kVertex (ℤ × ℤ) N :=
  fun i => (jacobiTrudiSourceX mu i, 1)

/-- The target k-vertex for the Jacobi-Trudi LGV setup: B_j = (λ_j - j, N).
    The y-coordinate N represents the ending height in the lattice. -/
def jacobiTrudiTargetVertex (lam : Fin N → ℕ) : LGV.kVertex (ℤ × ℤ) N :=
  fun j => (jacobiTrudiTargetX lam j, N)

/-- Rectangular source tuple: `M` sources, independently of alphabet height `N`. -/
def jacobiTrudiSourceVertexRect (mu : Fin M → ℕ) : LGV.kVertex (ℤ × ℤ) M :=
  fun i => ((mu i : ℤ) - (i.val : ℤ), 1)

/-- Rectangular target tuple: `M` targets at alphabet height `N`. -/
def jacobiTrudiTargetVertexRect (N : ℕ) (lam : Fin M → ℕ) :
    LGV.kVertex (ℤ × ℤ) M :=
  fun i => ((lam i : ℤ) - (i.val : ℤ), N)

/-- The source vertices have x-coordinates that are weakly decreasing. -/
theorem jacobiTrudiSourceVertex_xDecreasing (mu : Fin N → ℕ)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i) :
    LGV.xDecreasing (jacobiTrudiSourceVertex mu) := by
  intro i j hij
  simp only [LGV.xCoord, jacobiTrudiSourceVertex]
  exact jacobiTrudiSourceX_antitone mu hmu i j hij

/-- The source vertices have y-coordinates that are constant (trivially increasing). -/
theorem jacobiTrudiSourceVertex_yIncreasing (mu : Fin N → ℕ) :
    LGV.yIncreasing (jacobiTrudiSourceVertex mu) := by
  intro i j _
  simp only [LGV.yCoord, jacobiTrudiSourceVertex, le_refl]

/-- The target vertices have x-coordinates that are weakly decreasing. -/
theorem jacobiTrudiTargetVertex_xDecreasing (lam : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
    LGV.xDecreasing (jacobiTrudiTargetVertex lam) := by
  intro i j hij
  simp only [LGV.xCoord, jacobiTrudiTargetVertex]
  exact jacobiTrudiTargetX_antitone lam hlam i j hij

/-- The target vertices have y-coordinates that are constant (trivially increasing). -/
theorem jacobiTrudiTargetVertex_yIncreasing (lam : Fin N → ℕ) :
    LGV.yIncreasing (jacobiTrudiTargetVertex lam) := by
  intro i j _
  simp only [LGV.yCoord, jacobiTrudiTargetVertex, le_refl]

/-- The arc weight function for the Jacobi-Trudi proof.
    East-steps at height j (where 1 ≤ j ≤ N) are weighted by X_{j-1}.
    North-steps are weighted by 1.

    Note: The lattice uses y-coordinates 1 to N, but Fin N uses 0 to N-1.
    An east-step at y-coordinate y gets weight X_{y-1} when 1 ≤ y ≤ N. -/
noncomputable def jacobiTrudiArcWeight :
    LGV.ArcWeight LGV.integerLattice (MvPolynomial (Fin N) R) :=
  fun u v _ =>
    -- An arc from u to v is either an east-step (x increases) or north-step (y increases)
    if v.1 = u.1 + 1 ∧ v.2 = u.2 then
      -- East-step at height u.2: weight is X_{u.2 - 1} if 1 ≤ u.2 ≤ N, else 1
      if h : 1 ≤ u.2 ∧ u.2 ≤ N then
        MvPolynomial.X ⟨(u.2 - 1).toNat, by omega⟩
      else 1
    else
      -- North-step: weight is 1
      1

/-- Extract y-coordinates at east-step positions from a path vertex list.
    For a path from (a, 1) to (c, N), this gives the sequence of y-coordinates
    where east-steps occur. The sequence is weakly increasing and has length (c - a).

    This is a helper function for constructing the bijection between LGV paths and Sym. -/
def extractEastStepYCoords (vertices : List (ℤ × ℤ)) : List ℤ :=
  match vertices with
  | [] => []
  | [_] => []
  | u :: v :: rest =>
    if v.1 = u.1 + 1 then  -- east-step (x increases by 1)
      u.2 :: extractEastStepYCoords (v :: rest)
    else  -- north-step (y increases by 1)
      extractEastStepYCoords (v :: rest)



/-!
## LGV-Nipat Bijection Infrastructure

The following lemmas establish the connection between LGV's `PathTuple.isNonIntersecting`
and our `Nipat.colStrictPaths`. This is needed for step 4 of the Jacobi-Trudi proof.

The key insight is that for lattice paths from (μᵢ - i, 1) to (λᵢ - i, N):
- Two paths intersect (share a vertex) iff they share a point (x, y) for some x, y
- In the integer lattice, paths can only go north or east
- If path i and path j (with i < j) share a vertex, then at some column c,
  they have the same height
- This violates column-strictness (which requires path j to be strictly higher
  than path i at the same column)

Conversely, column-strictness implies non-intersection.

### Bijection Overview

The bijection between LGV paths and our LatticePath works as follows:

**LGV Path → LatticePath:**
An LGV path from (a, 1) to (c, N) in the integer lattice is a sequence of vertices
where each step is either east (+1 in x) or north (+1 in y). We extract the
y-coordinates at which east-steps occur (converted to Fin N by subtracting 1).

**LatticePath → LGV Path:**
A LatticePath has eastStepHeights : List (Fin N) which is weakly increasing.
We construct the LGV path by starting at (a, 1) and making north-steps until
we reach the first east-step height + 1, then east, then more north-steps, etc.

**Weight Preservation:**
- jacobiTrudiArcWeight assigns X_{y-1} to east-steps at height y (for 1 ≤ y ≤ N)
- North-steps are assigned weight 1
- LatticePath.weight = ∏ h ∈ eastStepHeights, X_h
- These match since the bijection maps y-coordinate y to height h = y - 1

**Non-intersection ↔ Column-strictness:**
For paths from sources A_i = (μ_i - i, 1) to targets B_i = (λ_i - i, N):
- Two LGV paths intersect iff they share a vertex (x, y)
- At any x-coordinate, path i has a well-defined y-coordinate (height)
- If paths i < j share vertex (x, y), then at column (x - (μ_i - i)) in path i
  and column (x - (μ_j - j)) in path j, both paths have height y
- Since μ_i - i > μ_j - j (by sorting), the column indices satisfy:
  col_i = x - μ_i + i and col_j = x - μ_j + j
  If μ_i + col_i = μ_j + col_j (same tableau column), then col_i = col_j + (μ_j - μ_i)
- Column-strictness requires height_i < height_j at same tableau column
- Intersection would give height_i = height_j = y, violating column-strictness
-/

/-- Extract the y-coordinates of east-steps from an LGV path vertex list.
    For a path from (a, 1) to (c, N), this returns the y-coordinates at which
    each east-step occurs. -/
def lgvPathEastStepYCoords (vertices : List (ℤ × ℤ)) : List ℤ :=
  match vertices with
  | [] => []
  | [_] => []
  | v₀ :: v₁ :: rest =>
    -- Check if v₀ → v₁ is an east-step (x increases by 1, y stays same)
    if v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2 then
      v₀.2 :: lgvPathEastStepYCoords (v₁ :: rest)
    else
      lgvPathEastStepYCoords (v₁ :: rest)

/-- Helper: x-coordinate is monotone along a path in the integer lattice -/
private lemma x_coord_monotone_along_path (vertices : List (ℤ × ℤ))
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (h_ne : vertices ≠ []) :
    (vertices.head h_ne).1 ≤ (vertices.getLast h_ne).1 := by
  induction vertices with
  | nil => exact absurd rfl h_ne
  | cons v₀ vs ih =>
    cases vs with
    | nil => simp
    | cons v₁ rest =>
      have h_arc : LGV.integerLattice.arc v₀ v₁ := by
        have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
        simp at this
        exact this
      have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
          LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
            ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
        have := h_arcs (i + 1) hi'
        simp at this ⊢
        exact this
      have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil v₁ rest
      have ih' := ih h_arcs' h_ne'
      simp only [List.head_cons, List.getLast_cons h_ne'] at ih' ⊢
      -- v₀.1 ≤ v₁.1 from the arc, and v₁.1 ≤ getLast.1 from IH
      rcases h_arc with ⟨hx, _⟩ | ⟨hx, _⟩
      · -- East-step: v₁.1 = v₀.1 + 1
        omega
      · -- North-step: v₁.1 = v₀.1
        omega

/-- The number of east-steps equals the x-displacement.
    This is a key property for the bijection. -/
theorem lgvPathEastStepYCoords_length_eq_xDisplacement (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩)) :
    (lgvPathEastStepYCoords vertices).length =
      ((vertices.getLast h_ne).1 - (vertices.head h_ne).1).toNat := by
  -- Each east-step increases x by 1, north-steps don't change x
  -- So total east-steps = final x - initial x
  induction vertices with
  | nil => exact absurd rfl h_ne
  | cons v₀ vs ih =>
    cases vs with
    | nil =>
      simp [lgvPathEastStepYCoords]
    | cons v₁ rest =>
      have h_arc : LGV.integerLattice.arc v₀ v₁ := by
        have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
        simp at this
        exact this
      have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
          LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
            ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
        have := h_arcs (i + 1) hi'
        simp at this ⊢
        exact this
      have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil v₁ rest
      have ih' := ih h_ne' h_arcs'
      -- Get the monotonicity bound for toNat
      have h_mono := x_coord_monotone_along_path (v₁ :: rest) h_arcs' h_ne'
      simp only [List.head_cons] at h_mono
      simp only [lgvPathEastStepYCoords]
      rcases h_arc with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · -- East-step: v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2
        simp only [hx, hy, and_self, ↓reduceIte, List.length_cons]
        rw [ih']
        simp only [List.head_cons, List.getLast_cons h_ne']
        -- Need: (getLast.1 - v₁.1).toNat + 1 = (getLast.1 - v₀.1).toNat
        -- where v₁.1 = v₀.1 + 1
        -- From h_mono: v₁.1 ≤ getLast.1, i.e., v₀.1 + 1 ≤ getLast.1
        omega
      · -- North-step: v₁.1 = v₀.1 ∧ v₁.2 = v₀.2 + 1
        have h_not_east : ¬(v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2) := by omega
        simp only [h_not_east, ↓reduceIte]
        rw [ih']
        simp only [List.head_cons, List.getLast_cons h_ne']
        -- Since v₁.1 = v₀.1, the toNat expressions are equal
        congr 1
        omega

/-- Helper lemma: y-coordinates are non-decreasing along any path in the integer lattice. -/
private lemma lgvPath_y_nondecreasing (vertices : List (ℤ × ℤ))
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (i j : ℕ) (hi : i < vertices.length) (hj : j < vertices.length) (hij : i ≤ j) :
    (vertices.get ⟨i, hi⟩).2 ≤ (vertices.get ⟨j, hj⟩).2 := by
  induction j with
  | zero => simp_all
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hik
    · rfl
    · have hk : k < vertices.length := Nat.lt_of_succ_lt hj
      have hik' : i ≤ k := Nat.lt_succ_iff.mp hik
      have h1 := ih hk hik'
      have harc := h_arcs k hj
      simp only [LGV.integerLattice] at harc
      rcases harc with ⟨_, hy⟩ | ⟨_, hy⟩ <;> omega

/-- Helper lemma: all y-coordinates in lgvPathEastStepYCoords are y-coordinates of vertices. -/
private lemma lgvPathEastStepYCoords_mem (vertices : List (ℤ × ℤ)) (y : ℤ)
    (hy : y ∈ lgvPathEastStepYCoords vertices) :
    ∃ i : ℕ, ∃ hi : i < vertices.length, (vertices.get ⟨i, hi⟩).2 = y := by
  induction vertices with
  | nil => simp [lgvPathEastStepYCoords] at hy
  | cons v₀ tl ih =>
    cases tl with
    | nil => simp [lgvPathEastStepYCoords] at hy
    | cons v₁ rest =>
      simp only [lgvPathEastStepYCoords] at hy
      split_ifs at hy with h_east
      · cases hy with
        | head =>
          exact ⟨0, by simp, rfl⟩
        | tail _ hmem =>
          obtain ⟨i, hi, heq⟩ := ih hmem
          simp only [List.length_cons] at hi
          have hi' : i + 1 < (v₀ :: v₁ :: rest).length := by simp; omega
          refine ⟨i + 1, hi', ?_⟩
          simp only [List.get_eq_getElem]
          have : (v₀ :: v₁ :: rest)[i + 1]'hi' = (v₁ :: rest)[i]'hi := by simp
          rw [this, ← heq]
          simp [List.get_eq_getElem]
      · obtain ⟨i, hi, heq⟩ := ih hy
        simp only [List.length_cons] at hi
        have hi' : i + 1 < (v₀ :: v₁ :: rest).length := by simp; omega
        refine ⟨i + 1, hi', ?_⟩
        simp only [List.get_eq_getElem]
        have : (v₀ :: v₁ :: rest)[i + 1]'hi' = (v₁ :: rest)[i]'hi := by simp
        rw [this, ← heq]
        simp [List.get_eq_getElem]

/-- Helper lemma: head of lgvPathEastStepYCoords is a y-coordinate of some vertex. -/
private lemma lgvPathEastStepYCoords_head_mem (vertices : List (ℤ × ℤ)) (y : ℤ)
    (hy : y ∈ (lgvPathEastStepYCoords vertices).head?) :
    ∃ i : ℕ, ∃ hi : i < vertices.length, (vertices.get ⟨i, hi⟩).2 = y := by
  have hmem : y ∈ lgvPathEastStepYCoords vertices := by
    cases h : lgvPathEastStepYCoords vertices with
    | nil => simp [h] at hy
    | cons hd tl => simp [h] at hy; rw [hy]; simp
  exact lgvPathEastStepYCoords_mem vertices y hmem

/-- East-step y-coordinates are weakly increasing (paths go north or east). -/
theorem lgvPathEastStepYCoords_weaklyIncreasing (vertices : List (ℤ × ℤ))
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩)) :
    (lgvPathEastStepYCoords vertices).IsChain (· ≤ ·) := by
  -- The proof proceeds by induction on the vertex list.
  -- For each east-step, we show its y-coordinate is ≤ the next east-step's y-coordinate
  -- because y can only increase (north-steps) or stay the same (east-steps) along the path.
  induction vertices with
  | nil => exact List.isChain_nil
  | cons v₀ tl ih =>
    cases tl with
    | nil => exact List.isChain_nil
    | cons v₁ rest =>
      simp only [lgvPathEastStepYCoords]
      split_ifs with h_east
      · -- v₀ → v₁ is an east-step
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
            LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
          exact h_arcs (i + 1) hi'
        have ih' := ih h_arcs'
        rw [List.isChain_cons]
        constructor
        · -- Show v₀.2 ≤ head of lgvPathEastStepYCoords (v₁ :: rest)
          intro y hy
          obtain ⟨i, hi, heq⟩ := lgvPathEastStepYCoords_head_mem (v₁ :: rest) y hy
          -- v₀.2 = v₁.2 (from east-step) and v₁.2 ≤ (v₁ :: rest)[i].2 by monotonicity
          have hv01 : v₀.2 = v₁.2 := h_east.2.symm
          have hmono := lgvPath_y_nondecreasing (v₁ :: rest) h_arcs' 0 i (by simp) hi (Nat.zero_le _)
          simp at hmono
          rw [hv01, ← heq]
          exact hmono
        · exact ih'
      · -- v₀ → v₁ is a north-step, so the result is just lgvPathEastStepYCoords (v₁ :: rest)
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
            LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
          exact h_arcs (i + 1) hi'
        exact ih h_arcs'

/-- All y-coordinates in the east-step list are ≥ the starting y-coordinate.
    This is a key lemma for proving uniqueness of paths from east-step coordinates. -/
private lemma lgvPathEastStepYCoords_ge_start (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (y : ℤ) (hy : y ∈ lgvPathEastStepYCoords vertices) :
    (vertices.head h_ne).2 ≤ y := by
  match vertices with
  | [] => simp at h_ne
  | [v] => simp [lgvPathEastStepYCoords] at hy
  | v₀ :: v₁ :: rest =>
    simp only [lgvPathEastStepYCoords] at hy
    have h_arc : LGV.integerLattice.arc v₀ v₁ := by
      have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
      simp at this; exact this
    have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
        LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
          ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
      intro i hi
      have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
      exact h_arcs (i + 1) hi'
    split_ifs at hy with h_east
    · simp only [List.mem_cons] at hy
      rcases hy with rfl | hy'
      · simp [List.head_cons]
      · have ih := lgvPathEastStepYCoords_ge_start (v₁ :: rest) (List.cons_ne_nil _ _) h_arcs' y hy'
        simp only [List.head_cons] at ih ⊢
        have hv01 : v₀.2 = v₁.2 := h_east.2.symm
        omega
    · have ih := lgvPathEastStepYCoords_ge_start (v₁ :: rest) (List.cons_ne_nil _ _) h_arcs' y hy
      simp only [List.head_cons] at ih ⊢
      rcases h_arc with ⟨hx, hy_eq⟩ | ⟨hx, hy_eq⟩
      · exfalso; apply h_east; exact ⟨hx, hy_eq⟩
      · omega

/-- East-step y-coordinates are bounded between start and end y-coordinates. -/
theorem lgvPathEastStepYCoords_bounded (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (y : ℤ) (hy : y ∈ lgvPathEastStepYCoords vertices) :
    (vertices.head h_ne).2 ≤ y ∧ y ≤ (vertices.getLast h_ne).2 := by
  -- y is a y-coordinate of some vertex
  obtain ⟨i, hi, heq⟩ := lgvPathEastStepYCoords_mem vertices y hy
  constructor
  · -- head.2 ≤ y
    have h_head : (vertices.head h_ne).2 = (vertices.get ⟨0, List.length_pos_of_ne_nil h_ne⟩).2 := by
      simp [List.head_eq_getElem]
    rw [h_head, ← heq]
    exact lgvPath_y_nondecreasing vertices h_arcs 0 i (List.length_pos_of_ne_nil h_ne) hi (Nat.zero_le _)
  · -- y ≤ getLast.2
    have h_last : (vertices.getLast h_ne).2 =
        (vertices.get ⟨vertices.length - 1, Nat.sub_lt (List.length_pos_of_ne_nil h_ne) Nat.one_pos⟩).2 := by
      simp [List.getLast_eq_getElem]
    rw [h_last, ← heq]
    have hlen : vertices.length - 1 < vertices.length := Nat.sub_lt (List.length_pos_of_ne_nil h_ne) Nat.one_pos
    have hi_le : i ≤ vertices.length - 1 := by omega
    exact lgvPath_y_nondecreasing vertices h_arcs i (vertices.length - 1) hi hlen hi_le

/-- Helper: if the first east-step y-coord exists, it is ≥ start.2.
    This is because y-coords are non-decreasing along the path. -/
private lemma lgvPathEastStepYCoords_head_ge_start (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (y : ℤ) (hy : y ∈ (lgvPathEastStepYCoords vertices).head?) :
    (vertices.head h_ne).2 ≤ y := by
  cases vertices with
  | nil => exact absurd rfl h_ne
  | cons v₀ tl =>
    cases tl with
    | nil => simp [lgvPathEastStepYCoords] at hy
    | cons v₁ rest =>
      simp only [lgvPathEastStepYCoords, List.head_cons] at hy ⊢
      split_ifs at hy with h_east
      · simp at hy; omega
      · have h_arc : LGV.integerLattice.arc v₀ v₁ := by
          have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
          simp at this; exact this
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
            LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
          have := h_arcs (i + 1) hi'
          simp at this ⊢; exact this
        have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil v₁ rest
        have hv1_le_y := lgvPathEastStepYCoords_head_ge_start (v₁ :: rest) h_ne' h_arcs' y hy
        simp only [List.head_cons] at hv1_le_y
        simp only [LGV.integerLattice] at h_arc
        rcases h_arc with ⟨hx, hvy⟩ | ⟨_, hvy⟩
        · exfalso; apply h_east; exact ⟨hx, hvy⟩
        · omega
termination_by vertices.length

/-- Auxiliary lemma: the k-th element of lgvPathEastStepYCoords corresponds to a vertex
    at x-coordinate start_x + k, AND that vertex is the start of an east step.
    This is the core induction for lgvPathEastStepYCoords_at_x. -/
private lemma lgvPathEastStepYCoords_at_x_aux (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (k : ℕ) (hk : k < (lgvPathEastStepYCoords vertices).length) :
    ∃ (idx : ℕ) (hidx : idx < vertices.length),
      (vertices.get ⟨idx, hidx⟩).1 = (vertices.head h_ne).1 + k ∧
      (vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords vertices)[k] ∧
      (∀ hidx_next : idx + 1 < vertices.length,
        (vertices.get ⟨idx + 1, hidx_next⟩).1 = (vertices.get ⟨idx, hidx⟩).1 + 1 ∧
        (vertices.get ⟨idx + 1, hidx_next⟩).2 = (vertices.get ⟨idx, hidx⟩).2) := by
  induction vertices generalizing k with
  | nil => simp [lgvPathEastStepYCoords] at hk
  | cons v₀ tl ih =>
    cases tl with
    | nil => simp [lgvPathEastStepYCoords] at hk
    | cons v₁ rest =>
      simp only [lgvPathEastStepYCoords] at hk ⊢
      have h_arcs' : ∀ j : ℕ, ∀ hj : j + 1 < (v₁ :: rest).length,
          LGV.integerLattice.arc ((v₁ :: rest).get ⟨j, Nat.lt_of_succ_lt hj⟩)
            ((v₁ :: rest).get ⟨j + 1, hj⟩) := by
        intro j hj
        have hj' : (j + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hj ⊢; omega
        have := h_arcs (j + 1) hj'
        simp at this ⊢; exact this
      have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil _ _
      have harc := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
      simp at harc
      simp only [LGV.integerLattice] at harc
      split_ifs at hk ⊢ with h_east
      · -- v₀ → v₁ is an east step
        obtain ⟨heast_x, heast_y⟩ := h_east
        cases k with
        | zero =>
          -- The 0th element is v₀.2, and x = start_x + 0 = v₀.1
          refine ⟨0, by simp, ?_, ?_, ?_⟩
          · simp [List.head_cons]
          · rfl
          · intro hidx_next
            simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ]
            exact ⟨heast_x, heast_y⟩
        | succ k' =>
          -- Use IH on the tail
          simp at hk
          have ih' := ih h_ne' h_arcs' k' hk
          obtain ⟨idx, hidx, hx, hy, heast_step⟩ := ih'
          simp only [List.get_eq_getElem, List.head_cons] at hx
          have hidx' : idx + 1 < (v₀ :: v₁ :: rest).length := by
            simp only [List.length_cons] at hidx ⊢; omega
          refine ⟨idx + 1, hidx', ?_, ?_, ?_⟩
          · simp only [List.get_eq_getElem, List.head_cons]
            have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
            rw [heq, hx]
            omega
          · simp only [List.get_eq_getElem] at hy ⊢
            have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
            rw [heq, hy]
            simp [List.getElem_cons_succ]
          · intro hidx_next
            have hidx_tail : idx + 1 < (v₁ :: rest).length := by simp at hidx_next hidx ⊢; omega
            have heast_tail := heast_step hidx_tail
            simp only [List.get_eq_getElem] at heast_tail ⊢
            constructor
            · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
              have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
              rw [h1, h2]; exact heast_tail.1
            · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
              have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
              rw [h1, h2]; exact heast_tail.2
      · -- v₀ → v₁ is a north step
        -- The list is just lgvPathEastStepYCoords (v₁ :: rest)
        -- Use IH
        have ih' := ih h_ne' h_arcs' k hk
        obtain ⟨idx, hidx, hx, hy, heast_step⟩ := ih'
        simp only [List.get_eq_getElem, List.head_cons] at hx
        have hidx' : idx + 1 < (v₀ :: v₁ :: rest).length := by
          simp only [List.length_cons] at hidx ⊢; omega
        refine ⟨idx + 1, hidx', ?_, ?_, ?_⟩
        · simp only [List.get_eq_getElem, List.head_cons]
          have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
          rw [heq, hx]
          -- v₁.1 = v₀.1 from north step
          rcases harc with ⟨hx', hy'⟩ | ⟨hx', _⟩
          · -- East step, but h_east says not
            simp at h_east
            have hne : v₁.2 ≠ v₀.2 := h_east hx'
            exact absurd hy' hne
          · omega
        · simp only [List.get_eq_getElem] at hy ⊢
          have heq : (v₀ :: v₁ :: rest)[idx + 1]'hidx' = (v₁ :: rest)[idx]'hidx := by simp
          rw [heq, hy]
        · intro hidx_next
          have hidx_tail : idx + 1 < (v₁ :: rest).length := by simp at hidx_next hidx ⊢; omega
          have heast_tail := heast_step hidx_tail
          simp only [List.get_eq_getElem] at heast_tail ⊢
          constructor
          · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
            have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
            rw [h1, h2]; exact heast_tail.1
          · have h1 : (v₀ :: v₁ :: rest)[idx + 1 + 1]'hidx_next = (v₁ :: rest)[idx + 1]'hidx_tail := by simp
            have h2 : (v₀ :: v₁ :: rest)[idx + 1]'(Nat.lt_of_succ_lt hidx_next) = (v₁ :: rest)[idx]'hidx := by simp
            rw [h1, h2]; exact heast_tail.2

/-- The k-th east-step y-coordinate equals the y-coordinate at x = start_x + k.

    This lemma establishes that `lgvPathEastStepYCoords[k]` is the y-coordinate of the
    path at x-coordinate start_x + k, where start_x is the x-coordinate of the first vertex.

    The k-th east step occurs at x = start_x + k because:
    - The path starts at x = start_x
    - Each east step increases x by 1
    - The k-th east step is preceded by exactly k east steps (indices 0, 1, ..., k-1)
    - So the k-th east step starts at x = start_x + k -/
theorem lgvPathEastStepYCoords_at_x (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (k : ℕ) (hk : k < (lgvPathEastStepYCoords p.vertices).length) :
    ∃ (idx : ℕ) (hidx : idx < p.vertices.length),
      (p.vertices.get ⟨idx, hidx⟩).1 = p.start.1 + k ∧
      (p.vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords p.vertices)[k] := by
  have h := lgvPathEastStepYCoords_at_x_aux p.vertices p.nonempty p.arcs_valid k hk
  obtain ⟨idx, hidx, hx, hy, _⟩ := h
  refine ⟨idx, hidx, ?_, hy⟩
  simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem] at hx ⊢
  convert hx using 2

/-- The index returned by lgvPathEastStepYCoords_at_x is the start of an east step.
    If idx + 1 < vertices.length, then the step from idx to idx+1 is an east step. -/
theorem lgvPathEastStepYCoords_at_x_is_east_step (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (k : ℕ) (hk : k < (lgvPathEastStepYCoords p.vertices).length)
    (idx : ℕ) (hidx : idx < p.vertices.length)
    (_hx : (p.vertices.get ⟨idx, hidx⟩).1 = p.start.1 + k)
    (hy : (p.vertices.get ⟨idx, hidx⟩).2 = (lgvPathEastStepYCoords p.vertices)[k])
    (hidx_next : idx + 1 < p.vertices.length) :
    (p.vertices.get ⟨idx + 1, hidx_next⟩).1 = (p.vertices.get ⟨idx, hidx⟩).1 + 1 ∧
    (p.vertices.get ⟨idx + 1, hidx_next⟩).2 = (p.vertices.get ⟨idx, hidx⟩).2 := by
  -- Use the strengthened auxiliary lemma which proves this directly
  have h := lgvPathEastStepYCoords_at_x_aux p.vertices p.nonempty p.arcs_valid k hk
  obtain ⟨idx', hidx', hx', hy', heast_step⟩ := h

  -- The step from idx to idx+1 is either east or north
  have harc := p.arcs_valid idx hidx_next
  rcases harc with ⟨heast_x, heast_y⟩ | ⟨hnorth_x, hnorth_y⟩
  · -- East step: this is what we want to prove
    constructor
    · have h1 : (p.vertices.get ⟨idx, Nat.lt_of_succ_lt hidx_next⟩).1 =
                (p.vertices.get ⟨idx, hidx⟩).1 := rfl
      rw [← h1]; exact heast_x
    · have h1 : (p.vertices.get ⟨idx, Nat.lt_of_succ_lt hidx_next⟩).2 =
                (p.vertices.get ⟨idx, hidx⟩).2 := rfl
      rw [← h1]; exact heast_y
  · -- North step: contradiction
    -- We show idx = idx' using the fact that the path has no duplicate vertices
    -- (since integer lattice is acyclic)

    -- First, show that the vertices at idx and idx' are equal
    have hv_eq : p.vertices.get ⟨idx, hidx⟩ = p.vertices.get ⟨idx', hidx'⟩ := by
      ext
      · -- x-coordinates equal: both are start.x + k
        simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem] at _hx hx'
        have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
        have hx1 : (p.vertices.get ⟨idx, hidx⟩).1 = (p.vertices[0]'hlen).1 + k := _hx
        have hx2 : (p.vertices.get ⟨idx', hidx'⟩).1 = (p.vertices[0]'hlen).1 + k := by
          simp only [List.get_eq_getElem] at hx' ⊢
          convert hx' using 2
        omega
      · -- y-coordinates equal: both are ycoords[k]
        rw [hy, hy']

    -- The path has no duplicate vertices (since integer lattice is acyclic)
    have hnodup := LGV.SimpleDigraph.Path.vertices_nodup_of_acyclic LGV.integerLattice_acyclic p
    rw [List.nodup_iff_injective_getElem] at hnodup

    -- Since vertices at idx and idx' are equal, idx = idx'
    have hidx_eq : idx = idx' := by
      have hinj := @hnodup ⟨idx, hidx⟩ ⟨idx', hidx'⟩
      simp only [Fin.mk.injEq] at hinj
      simp only [List.get_eq_getElem] at hv_eq
      exact hinj hv_eq

    -- Now use the east step property from the aux lemma
    -- The east step property says: step from idx' to idx'+1 is east (x+1, y same)
    -- But hnorth_x says: step from idx to idx+1 has x unchanged
    -- Since idx = idx', this is a contradiction

    have hidx_next' : idx' + 1 < p.vertices.length := by rw [← hidx_eq]; exact hidx_next
    have heast := heast_step hidx_next'
    simp only [List.get_eq_getElem] at heast

    -- heast.1 says x(idx'+1) = x(idx') + 1
    -- hnorth_x says x(idx+1) = x(idx)
    -- Since idx = idx', we have x(idx'+1) = x(idx') and x(idx'+1) = x(idx') + 1
    -- This gives 0 = 1, contradiction

    have hx_east : p.vertices[idx' + 1].1 = p.vertices[idx'].1 + 1 := heast.1
    have hx_north : p.vertices[idx + 1].1 = p.vertices[idx].1 := by
      have := hnorth_x
      simp only [List.get_eq_getElem] at this
      exact this
    -- Substitute idx = idx' into hx_north
    subst hidx_eq
    -- Now hx_north : p.vertices[idx' + 1].1 = p.vertices[idx'].1
    -- And hx_east : p.vertices[idx' + 1].1 = p.vertices[idx'].1 + 1
    -- This gives: p.vertices[idx'].1 = p.vertices[idx'].1 + 1, contradiction
    omega

/-- Helper: x-coordinate is monotone (non-decreasing) along a path in the integer lattice.
    This follows from the fact that each step is either east (x+1) or north (x unchanged). -/
private lemma integerLattice_path_x_monotone (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (i j : ℕ) (hi : i < p.vertices.length) (hj : j < p.vertices.length) (hij : i ≤ j) :
    (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j, hj⟩).1 := by
  induction j with
  | zero => simp only [Nat.le_zero] at hij; subst hij; rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hik
    · rfl
    · have hk : k < p.vertices.length := Nat.lt_of_succ_lt hj
      have h1 := ih hk (Nat.lt_succ_iff.mp hik)
      have hstep := LGV.integerLattice_path_x_step p k hj
      rcases hstep with h | h <;> omega

/-- Helper: if x-coordinates differ strictly, then indices differ strictly.
    Contrapositive of x-monotonicity. -/
private lemma integerLattice_path_x_lt_implies_idx_lt (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (i j : ℕ) (hi : i < p.vertices.length) (hj : j < p.vertices.length)
    (hx : (p.vertices.get ⟨i, hi⟩).1 < (p.vertices.get ⟨j, hj⟩).1) : i < j := by
  by_contra h; push_neg at h
  have := integerLattice_path_x_monotone p j i hj hi h; omega

/-- Helper: at a fixed x-coordinate, the y-coordinates of vertices form a contiguous range
    starting from the first vertex at that x. 
    
    If vertex i has x = x₀ and vertex j has x = x₀ with i < j, then for any y in 
    [y_i, y_j], there exists a vertex k with i ≤ k ≤ j having (x₀, y).
    
    This follows from the fact that y changes by 0 or 1 at each step, and x stays the same
    during north steps (y increases by 1). -/
private lemma integerLattice_path_y_contiguous_at_x (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (x₀ : ℤ)
    (i j : ℕ) (hi : i < p.vertices.length) (hj : j < p.vertices.length) (hij : i ≤ j)
    (hx_i : (p.vertices.get ⟨i, hi⟩).1 = x₀)
    (hx_j : (p.vertices.get ⟨j, hj⟩).1 = x₀)
    (y : ℤ) (hy_lo : (p.vertices.get ⟨i, hi⟩).2 ≤ y) (hy_hi : y ≤ (p.vertices.get ⟨j, hj⟩).2) :
    ∃ (k : ℕ) (hk : k < p.vertices.length), i ≤ k ∧ k ≤ j ∧ 
      (p.vertices.get ⟨k, hk⟩).1 = x₀ ∧ (p.vertices.get ⟨k, hk⟩).2 = y := by
  -- Use discrete IVT on y-coordinates
  -- The y-coordinate at index i is y_i, at index j is y_j, and y ∈ [y_i, y_j]
  -- Since y changes by 0 or 1 at each step, there exists k with y_k = y
  induction j generalizing y with
  | zero =>
    simp only [Nat.le_zero] at hij
    subst hij
    exact ⟨0, hi, le_refl 0, le_refl 0, hx_i, by omega⟩
  | succ j' ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hij'
    · -- i = j' + 1
      exact ⟨j' + 1, hj, le_refl _, le_refl _, hx_j, by omega⟩
    · -- i < j' + 1, so i ≤ j'
      have hj'_lt : j' < p.vertices.length := Nat.lt_of_succ_lt hj
      -- Check if x at j' equals x₀
      have hstep := LGV.integerLattice_path_x_step p j' hj
      rcases hstep with hnorth | heast
      · -- North step: x(j'+1) - x(j') = 0, so x(j'+1) = x(j')
        -- Also y(j'+1) = y(j') + 1 (north step increases y by 1)
        have hx_j'_eq : (p.vertices.get ⟨j' + 1, hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 := by
          have h1 : (p.vertices.get ⟨j' + 1, hj⟩).1 - (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = 0 := hnorth
          have h2 : (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 := rfl
          omega
        have hx_j' : (p.vertices.get ⟨j', hj'_lt⟩).1 = x₀ := by
          rw [hx_j] at hx_j'_eq
          exact hx_j'_eq.symm
        -- Get y-coordinate relation
        have hy_j'_eq : (p.vertices.get ⟨j' + 1, hj⟩).2 = (p.vertices.get ⟨j', hj'_lt⟩).2 + 1 := by
          have harc := p.arcs_valid j' hj
          rcases harc with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · -- East step: x increases by 1, y stays same
            -- But we know x(j'+1) - x(j') = 0 from hnorth, contradiction
            have h1 : (p.vertices.get ⟨j' + 1, hj⟩).1 = (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 + 1 := hx
            have h2 : (p.vertices.get ⟨j' + 1, hj⟩).1 - (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = 0 := hnorth
            omega
          · -- North step: x stays same, y increases by 1
            have h2 : (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).2 = (p.vertices.get ⟨j', hj'_lt⟩).2 := rfl
            omega
        -- If y = y(j'+1), we're done
        by_cases hy_eq_j : y = (p.vertices.get ⟨j' + 1, hj⟩).2
        · exact ⟨j' + 1, hj, Nat.le_of_lt hij', le_refl _, hx_j, hy_eq_j.symm⟩
        · -- y < y(j'+1), so y ≤ y(j') = y(j'+1) - 1
          have hy_le_j' : y ≤ (p.vertices.get ⟨j', hj'_lt⟩).2 := by
            rw [hy_j'_eq] at hy_hi
            have := ne_iff_lt_or_gt.mp hy_eq_j
            rcases this with h | h
            · omega
            · omega
          -- Apply IH to find vertex at index ≤ j' with y-coordinate y
          have := ih hj'_lt (Nat.lt_succ_iff.mp hij') hx_j' y hy_lo hy_le_j'
          obtain ⟨k, hk, hik, hkj', hx_k, hy_k⟩ := this
          exact ⟨k, hk, hik, Nat.le_succ_of_le hkj', hx_k, hy_k⟩
      · -- East step: x(j'+1) - x(j') = 1, so x(j'+1) = x(j') + 1
        -- Since x(j'+1) = x₀, we have x(j') = x₀ - 1 ≠ x₀
        have hx_j'_eq : (p.vertices.get ⟨j' + 1, hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 + 1 := by
          have h1 : (p.vertices.get ⟨j' + 1, hj⟩).1 - (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = 1 := heast
          have h2 : (p.vertices.get ⟨j', Nat.lt_of_succ_lt hj⟩).1 = (p.vertices.get ⟨j', hj'_lt⟩).1 := rfl
          omega
        have hx_j' : (p.vertices.get ⟨j', hj'_lt⟩).1 = x₀ - 1 := by
          rw [hx_j] at hx_j'_eq
          omega
        -- If i = j', then x(i) = x₀ but x(j') = x₀ - 1, contradiction
        have hi_ne_j' : i ≠ j' := by
          intro heq
          subst heq
          rw [hx_i] at hx_j'
          omega
        -- So i < j'
        have hi_lt_j' : i < j' := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hij') hi_ne_j'
        -- x is non-decreasing, so x(i) ≤ x(j')
        have hx_i_le : (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j', hj'_lt⟩).1 := 
          integerLattice_path_x_monotone p i j' hi hj'_lt (Nat.le_of_lt hi_lt_j')
        -- But x(i) = x₀ and x(j') = x₀ - 1 < x₀, contradiction
        rw [hx_i, hx_j'] at hx_i_le
        omega

/-- Key lemma: for two non-intersecting paths, if one is above the other at some x-coordinate,
    it stays above at all greater x-coordinates where both paths have vertices.

    This is the "paths don't cross" property for x-coordinates.
    The proof uses discrete IVT: if the y-difference ever becomes ≤ 0, there must be
    a point where it equals 0, meaning the paths share a vertex (contradiction). -/
theorem paths_above_at_x_stays_above (p p' : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hni : ∀ v, v ∈ p.vertices → v ∉ p'.vertices)
    (x₀ : ℤ) -- x-coordinate where p' is above p
    -- Both paths have vertices at x₀
    (hx₀_p : ∃ (idx : ℕ) (hidx : idx < p.vertices.length), (p.vertices.get ⟨idx, hidx⟩).1 = x₀)
    (hx₀_p' : ∃ (idx : ℕ) (hidx : idx < p'.vertices.length), (p'.vertices.get ⟨idx, hidx⟩).1 = x₀)
    -- p' is strictly above p at x₀
    (h_above : ∀ (idx_p : ℕ) (hidx_p : idx_p < p.vertices.length)
               (idx_p' : ℕ) (hidx_p' : idx_p' < p'.vertices.length),
               (p.vertices.get ⟨idx_p, hidx_p⟩).1 = x₀ →
               (p'.vertices.get ⟨idx_p', hidx_p'⟩).1 = x₀ →
               (p'.vertices.get ⟨idx_p', hidx_p'⟩).2 > (p.vertices.get ⟨idx_p, hidx_p⟩).2)
    -- A greater x-coordinate x₁
    (x₁ : ℤ) (hx₁ : x₁ ≥ x₀)
    -- Both paths have vertices at x₁
    (hx₁_p : ∃ (idx : ℕ) (hidx : idx < p.vertices.length), (p.vertices.get ⟨idx, hidx⟩).1 = x₁)
    (hx₁_p' : ∃ (idx : ℕ) (hidx : idx < p'.vertices.length), (p'.vertices.get ⟨idx, hidx⟩).1 = x₁) :
    ∀ (idx_p : ℕ) (hidx_p : idx_p < p.vertices.length)
      (idx_p' : ℕ) (hidx_p' : idx_p' < p'.vertices.length),
      (p.vertices.get ⟨idx_p, hidx_p⟩).1 = x₁ →
      (p'.vertices.get ⟨idx_p', hidx_p'⟩).1 = x₁ →
      (p'.vertices.get ⟨idx_p', hidx_p'⟩).2 > (p.vertices.get ⟨idx_p, hidx_p⟩).2 := by
  -- The proof uses discrete IVT on the y-difference.
  -- If p' drops to or below p at some x > x₀, there must be a crossing point.
  intro idx_p hidx_p idx_p' hidx_p' hx_p hx_p'
  by_contra h_not_above
  push_neg at h_not_above
  -- Get witnesses for x₀
  obtain ⟨idx₀_p, hidx₀_p, hx₀_p_eq⟩ := hx₀_p
  obtain ⟨idx₀_p', hidx₀_p', hx₀_p'_eq⟩ := hx₀_p'
  -- At x₀, p' is strictly above p
  have h_above_at_x₀ := h_above idx₀_p hidx₀_p idx₀_p' hidx₀_p' hx₀_p_eq hx₀_p'_eq
  -- Define y-coordinate at x for each path (using the unique vertex at that x)
  -- The key insight: at x₁, if y_p' ≤ y_p, then by discrete IVT on x-coordinates,
  -- there exists some x ∈ [x₀, x₁] where y_p' = y_p, meaning paths share a vertex.
  --
  -- Use the sum-based approach: at x₀, sum_p = x₀ + y_p, sum_p' = x₀ + y_p'
  -- Since y_p' > y_p at x₀, sum_p' > sum_p.
  -- At x₁, if y_p' ≤ y_p, then sum_p' ≤ sum_p.
  -- By discrete IVT on sums, there's a sum s where both paths have the same y.
  -- Since x + y = s for both, and y is the same, x is the same.
  -- So paths share a vertex, contradiction.
  let y_p_x₀ := (p.vertices.get ⟨idx₀_p, hidx₀_p⟩).2
  let y_p'_x₀ := (p'.vertices.get ⟨idx₀_p', hidx₀_p'⟩).2
  let y_p_x₁ := (p.vertices.get ⟨idx_p, hidx_p⟩).2
  let y_p'_x₁ := (p'.vertices.get ⟨idx_p', hidx_p'⟩).2
  -- Sums at x₀ and x₁
  let s_p_x₀ := x₀ + y_p_x₀
  let s_p'_x₀ := x₀ + y_p'_x₀
  let s_p_x₁ := x₁ + y_p_x₁
  let s_p'_x₁ := x₁ + y_p'_x₁
  -- At x₀: s_p'_x₀ > s_p_x₀ (since y_p'_x₀ > y_p_x₀)
  have hs₀ : s_p'_x₀ > s_p_x₀ := by simp only [s_p'_x₀, s_p_x₀]; omega
  -- At x₁: s_p'_x₁ ≤ s_p_x₁ (since y_p'_x₁ ≤ y_p_x₁ and both have x = x₁)
  have hs₁ : s_p'_x₁ ≤ s_p_x₁ := by simp only [s_p'_x₁, s_p_x₁]; omega
  -- The sums at vertices are determined by their index
  have hsum_p_x₀ := LGV.integerLattice_path_vertex_sum p idx₀_p hidx₀_p
  have hsum_p'_x₀ := LGV.integerLattice_path_vertex_sum p' idx₀_p' hidx₀_p'
  have hsum_p_x₁ := LGV.integerLattice_path_vertex_sum p idx_p hidx_p
  have hsum_p'_x₁ := LGV.integerLattice_path_vertex_sum p' idx_p' hidx_p'
  -- Case split: x₁ = x₀ or x₁ > x₀
  rcases eq_or_lt_of_le hx₁ with hx_eq | hx_gt
  · -- Case x₁ = x₀: contradiction with h_above and h_not_above
    subst hx_eq
    have := h_above idx_p hidx_p idx_p' hidx_p' hx_p hx_p'
    omega
  · -- Case x₁ > x₀: use discrete IVT
    -- Define the y-difference function on sum values
    let y_p_fn (s : ℤ) : ℤ :=
      let idx := (s - p.start.1 - p.start.2).toNat
      if h : idx < p.vertices.length then (p.vertices.get ⟨idx, h⟩).2 else 0
    let y_p'_fn (s : ℤ) : ℤ :=
      let idx := (s - p'.start.1 - p'.start.2).toNat
      if h : idx < p'.vertices.length then (p'.vertices.get ⟨idx, h⟩).2 else 0
    let diff (s : ℤ) : ℤ := y_p'_fn s - y_p_fn s
    -- The key constraint: idx₀_p' < idx_p' (since x strictly increases from x₀ to x₁)
    have hidx_p'_mono : idx₀_p' < idx_p' := by
      have := integerLattice_path_x_lt_implies_idx_lt p' idx₀_p' idx_p' hidx₀_p' hidx_p'
      simp only [hx₀_p'_eq, hx_p'] at this
      exact this hx_gt
    -- Similarly for p: idx₀_p < idx_p
    have hidx_p_mono : idx₀_p < idx_p := by
      have := integerLattice_path_x_lt_implies_idx_lt p idx₀_p idx_p hidx₀_p hidx_p
      simp only [hx₀_p_eq, hx_p] at this
      exact this hx_gt
    -- The sum range for p' from x₀ to x₁ is [s_p'_x₀, s_p'_x₁]
    -- Since s_p'_x₁ ≤ s_p_x₁ and s_p'_x₀ < s_p'_x₁, we have s_p'_x₀ ≤ s_p_x₁
    have hs_p'_x₀_lt_sp'x₁ : s_p'_x₀ < s_p'_x₁ := by
      simp only [s_p'_x₀, s_p'_x₁]; omega
    have hs_p'_x₀_le_spx₁ : s_p'_x₀ ≤ s_p_x₁ := le_trans (le_of_lt hs_p'_x₀_lt_sp'x₁) hs₁
    -- Index bounds for the overlapping sum range
    have hidx_p_sp'x₀ : (s_p'_x₀ - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      simp only [s_p'_x₀, s_p_x₀, s_p_x₁] at hs₀ hs_p'_x₀_le_spx₁; omega
    have hidx_p'_sp'x₀ : (s_p'_x₀ - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      simp only [s_p'_x₀]; omega
    have hidx_p_sp'x₁ : (s_p'_x₁ - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      simp only [s_p'_x₁, s_p_x₁] at hs₁; omega
    have hidx_p'_sp'x₁ : (s_p'_x₁ - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      simp only [s_p'_x₁]; omega
    -- At s_p'_x₀, the index in p' is idx₀_p'
    have heq_idx_p'_sp'x₀ : (s_p'_x₀ - p'.start.1 - p'.start.2).toNat = idx₀_p' := by
      simp only [s_p'_x₀]; omega
    -- At s_p'_x₁, the index in p' is idx_p'
    have heq_idx_p'_sp'x₁ : (s_p'_x₁ - p'.start.1 - p'.start.2).toNat = idx_p' := by
      simp only [s_p'_x₁]; omega
    -- At s_p'_x₀, the x-coordinate of p is ≥ x₀
    have hx_p_at_sp'x₀ : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 ≥ x₀ := by
      have hidx_ge : (s_p'_x₀ - p.start.1 - p.start.2).toNat ≥ idx₀_p := by
        simp only [s_p'_x₀, s_p_x₀] at hs₀; omega
      have := integerLattice_path_x_monotone p idx₀_p (s_p'_x₀ - p.start.1 - p.start.2).toNat
        hidx₀_p hidx_p_sp'x₀ hidx_ge
      omega
    -- At s_p'_x₀, y_p' > y_p (or they share a vertex, contradiction)
    have hdiff_sp'x₀ : diff s_p'_x₀ > 0 := by
      simp only [diff, y_p_fn, y_p'_fn, hidx_p_sp'x₀, hidx_p'_sp'x₀, dite_true]
      by_contra h_le
      push_neg at h_le
      have hsum_p_at_sp'x₀ := LGV.integerLattice_path_vertex_sum p
        (s_p'_x₀ - p.start.1 - p.start.2).toNat hidx_p_sp'x₀
      have hy_p'_val : (p'.vertices.get ⟨(s_p'_x₀ - p'.start.1 - p'.start.2).toNat, hidx_p'_sp'x₀⟩).2 = y_p'_x₀ := by
        have : (s_p'_x₀ - p'.start.1 - p'.start.2).toNat = idx₀_p' := heq_idx_p'_sp'x₀
        simp only [List.get_eq_getElem, y_p'_x₀, this]
      have heq_y : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).2 = y_p'_x₀ := by
        simp only [hy_p'_val] at h_le
        have hsum : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 +
               (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).2 = s_p'_x₀ := by
          simp only [s_p'_x₀] at hsum_p_at_sp'x₀ ⊢; omega
        omega
      have heq_x : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 = x₀ := by
        have hsum : (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).1 +
               (p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩).2 = s_p'_x₀ := by
          simp only [s_p'_x₀] at hsum_p_at_sp'x₀ ⊢; omega
        omega
      have hv_eq : p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩ =
                   p'.vertices.get ⟨idx₀_p', hidx₀_p'⟩ := by
        apply Prod.ext
        · simp only [heq_x, hx₀_p'_eq]
        · simp only [heq_y]; rfl
      have hmem_p : p.vertices.get ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩ ∈ p.vertices :=
        List.get_mem p.vertices ⟨(s_p'_x₀ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₀⟩
      have hmem_p' : p'.vertices.get ⟨idx₀_p', hidx₀_p'⟩ ∈ p'.vertices :=
        List.get_mem p'.vertices ⟨idx₀_p', hidx₀_p'⟩
      rw [hv_eq] at hmem_p
      exact hni _ hmem_p hmem_p'
    -- At s_p'_x₁, diff ≤ 0
    have hdiff_sp'x₁ : diff s_p'_x₁ ≤ 0 := by
      simp only [diff, y_p_fn, y_p'_fn, hidx_p_sp'x₁, hidx_p'_sp'x₁, dite_true]
      have hy_p'_val : (p'.vertices.get ⟨(s_p'_x₁ - p'.start.1 - p'.start.2).toNat, hidx_p'_sp'x₁⟩).2 = y_p'_x₁ := by
        have : (s_p'_x₁ - p'.start.1 - p'.start.2).toNat = idx_p' := heq_idx_p'_sp'x₁
        simp only [List.get_eq_getElem, y_p'_x₁, this]
      have hsum_p_at_sp'x₁ := LGV.integerLattice_path_vertex_sum p
        (s_p'_x₁ - p.start.1 - p.start.2).toNat hidx_p_sp'x₁
      have hx_p_le : (p.vertices.get ⟨(s_p'_x₁ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₁⟩).1 ≤ x₁ := by
        have hidx_le : (s_p'_x₁ - p.start.1 - p.start.2).toNat ≤ idx_p := by
          simp only [s_p'_x₁, s_p_x₁] at hs₁; omega
        have := integerLattice_path_x_monotone p (s_p'_x₁ - p.start.1 - p.start.2).toNat idx_p
          hidx_p_sp'x₁ hidx_p hidx_le
        omega
      simp only [hy_p'_val]
      have hsum : (p.vertices.get ⟨(s_p'_x₁ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₁⟩).1 +
             (p.vertices.get ⟨(s_p'_x₁ - p.start.1 - p.start.2).toNat, hidx_p_sp'x₁⟩).2 = s_p'_x₁ := by
        simp only [s_p'_x₁] at hsum_p_at_sp'x₁ ⊢; omega
      omega
    -- The difference function changes by at most 1 at each step
    have hdiff_step : ∀ s : ℤ, s_p'_x₀ ≤ s → s < s_p'_x₁ → |diff (s + 1) - diff s| ≤ 1 := by
      intro s hs_lo hs_hi
      simp only [diff, y_p_fn, y_p'_fn]
      have hs_p_lo : s ≥ p.start.1 + p.start.2 := by
        simp only [s_p'_x₀, s_p_x₀] at hs_lo hs₀; omega
      have hs_p_hi : s < p.finish.1 + p.finish.2 := by
        have hlen := LGV.integerLattice_path_length_eq p
        simp only [s_p'_x₁, s_p_x₁] at hs_hi hs₁; omega
      have hs_p'_lo : s ≥ p'.start.1 + p'.start.2 := by
        simp only [s_p'_x₀] at hs_lo; omega
      have hs_p'_hi : s < p'.finish.1 + p'.finish.2 := by
        have hlen := LGV.integerLattice_path_length_eq p'
        simp only [s_p'_x₁] at hs_hi; omega
      have hidx_p_s : (s - p.start.1 - p.start.2).toNat < p.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p; omega
      have hidx_p'_s : (s - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p'; omega
      have hidx_p_s1 : (s + 1 - p.start.1 - p.start.2).toNat < p.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p; omega
      have hidx_p'_s1 : (s + 1 - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
        have hlen := LGV.integerLattice_path_length_eq p'; omega
      simp only [hidx_p_s, hidx_p'_s, hidx_p_s1, hidx_p'_s1, dite_true]
      have heq_idx_p : (s + 1 - p.start.1 - p.start.2).toNat = (s - p.start.1 - p.start.2).toNat + 1 := by omega
      have heq_idx_p' : (s + 1 - p'.start.1 - p'.start.2).toNat = (s - p'.start.1 - p'.start.2).toNat + 1 := by omega
      have hstep_p_idx : (s - p.start.1 - p.start.2).toNat + 1 < p.vertices.length := by omega
      have hstep_p'_idx : (s - p'.start.1 - p'.start.2).toNat + 1 < p'.vertices.length := by omega
      have harc_p := p.arcs_valid (s - p.start.1 - p.start.2).toNat hstep_p_idx
      have harc_p' := p'.arcs_valid (s - p'.start.1 - p'.start.2).toNat hstep_p'_idx
      rcases harc_p with ⟨_, hy_p⟩ | ⟨_, hy_p⟩ <;>
      rcases harc_p' with ⟨_, hy_p'⟩ | ⟨_, hy_p'⟩ <;>
      · simp only [heq_idx_p, heq_idx_p', abs_le]
        constructor <;> omega
    -- Apply discrete IVT
    obtain ⟨s_eq, hs_eq_lo, hs_eq_hi, hdiff_eq⟩ := LGV.discrete_ivt (le_of_lt hs_p'_x₀_lt_sp'x₁) diff
      hdiff_step (le_of_lt hdiff_sp'x₀) hdiff_sp'x₁
    -- At s_eq, both paths have the same y-coordinate
    have hidx_p_seq : (s_eq - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      simp only [s_p'_x₀, s_p_x₀, s_p'_x₁, s_p_x₁] at hs_eq_lo hs_eq_hi hs₀ hs₁; omega
    have hidx_p'_seq : (s_eq - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      simp only [s_p'_x₀, s_p'_x₁] at hs_eq_lo hs_eq_hi; omega
    simp only [diff, y_p_fn, y_p'_fn, hidx_p_seq, hidx_p'_seq, dite_true, sub_eq_zero] at hdiff_eq
    -- Both paths have the same sum value at s_eq
    have hsum_p_seq := LGV.integerLattice_path_vertex_sum p (s_eq - p.start.1 - p.start.2).toNat hidx_p_seq
    have hsum_p'_seq := LGV.integerLattice_path_vertex_sum p' (s_eq - p'.start.1 - p'.start.2).toNat hidx_p'_seq
    -- Since x + y = s_eq for both, and y_p = y_p', we have x_p = x_p'
    have hx_eq : (p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩).1 =
                 (p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩).1 := by omega
    have hy_eq : (p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩).2 =
                 (p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩).2 := by omega
    -- The vertices are equal
    have hv_eq : p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩ =
                 p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩ :=
      Prod.ext hx_eq hy_eq
    -- This contradicts non-intersection
    have hmem_p : p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩ ∈ p.vertices :=
      List.get_mem p.vertices ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩
    have hmem_p' : p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩ ∈ p'.vertices :=
      List.get_mem p'.vertices ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩
    rw [hv_eq] at hmem_p
    exact hni _ hmem_p hmem_p'

/-!
### LGV Path to LatticePath Bijection

We now construct the explicit bijection between LGV paths from (a, 1) to (c, N) and
our `LatticePath a c` type. This is needed for `lgv_pathWeightSum_eq_hsymmExt`.

The bijection:
- **LGV Path → LatticePath**: Extract east-step y-coordinates using `lgvPathEastStepYCoords`,
  then convert from ℤ (in range [1, N]) to Fin N by subtracting 1.
- **LatticePath → LGV Path**: Given a weakly increasing list of Fin N, construct the unique
  path that makes east-steps at the specified heights.

Weight preservation follows from the definition of `jacobiTrudiArcWeight`:
- East-step at y-coordinate y gets weight X_{y-1}
- North-steps get weight 1
- This matches `LatticePath.weight = ∏ h ∈ eastStepHeights, X_h`
-/

/-- Convert east-step y-coordinates (in ℤ, range [1, N]) to Fin N elements.
    This is a helper for the LGV path to LatticePath bijection. -/
def lgvYCoordsToFinN (ycoords : List ℤ) (h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N) : List (Fin N) :=
  ycoords.pmap (fun y hy => ⟨(y - 1).toNat, by have := h y hy; omega⟩) (fun y hy => hy)

/-- The length of lgvYCoordsToFinN equals the length of the input list. -/
lemma lgvYCoordsToFinN_length (ycoords : List ℤ) (h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N) :
    (lgvYCoordsToFinN ycoords h).length = ycoords.length := by
  simp [lgvYCoordsToFinN, List.length_pmap]

/-- The k-th element of lgvYCoordsToFinN equals (ycoords[k] - 1).toNat.
    Since ycoords[k] ∈ [1, N], we have (lgvYCoordsToFinN ycoords h)[k].val + 1 = ycoords[k]. -/
lemma lgvYCoordsToFinN_getElem (ycoords : List ℤ) (h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N)
    (k : ℕ) (hk : k < ycoords.length)
    (hk' : k < (lgvYCoordsToFinN ycoords h).length := by rw [lgvYCoordsToFinN_length]; exact hk) :
    ((lgvYCoordsToFinN ycoords h)[k]).val + 1 = ycoords[k] := by
  simp only [lgvYCoordsToFinN, List.getElem_pmap]
  have hmem : ycoords[k] ∈ ycoords := List.getElem_mem hk
  have hbnd := h _ hmem
  omega

/-- The converted list preserves the chain property (weakly increasing). -/
lemma lgvYCoordsToFinN_isChain (ycoords : List ℤ) (h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N)
    (hchain : ycoords.IsChain (· ≤ ·)) :
    (lgvYCoordsToFinN ycoords h).IsChain (· ≤ ·) := by
  unfold lgvYCoordsToFinN
  -- Convert to Pairwise form which is easier to work with for pmap
  rw [List.isChain_iff_pairwise] at hchain ⊢
  apply List.Pairwise.pmap hchain
  intro a ha b hb hab
  simp only [Fin.le_def]
  have ha' := h a ha
  have hb' := h b hb
  omega

/-- The conversion lgvYCoordsToFinN is injective when both lists have elements in [1, N].

    The proof uses the fact that y ↦ (y - 1).toNat is injective on [1, N]:
    if (y₁ - 1).toNat = (y₂ - 1).toNat and both y₁, y₂ ∈ [1, N], then y₁ = y₂.

    **Proof sketch:**
    1. The lengths are equal (pmap preserves length)
    2. At each position i, the Fin N values are equal (from heq)
    3. Since y ↦ (y - 1).toNat is injective on [1, N], the original values are equal -/
lemma lgvYCoordsToFinN_injective (l₁ l₂ : List ℤ)
    (h₁ : ∀ y ∈ l₁, 1 ≤ y ∧ y ≤ N) (h₂ : ∀ y ∈ l₂, 1 ≤ y ∧ y ≤ N)
    (heq : lgvYCoordsToFinN l₁ h₁ = lgvYCoordsToFinN l₂ h₂) : l₁ = l₂ := by
  -- First show lengths are equal
  have hlen : l₁.length = l₂.length := by
    have := congrArg List.length heq
    simp only [lgvYCoordsToFinN, List.length_pmap] at this
    exact this
  -- Then show elements are equal at each position
  apply List.ext_get hlen
  intro i hi₁ hi₂
  -- From heq, the i-th Fin N values are equal
  have hmem₁ : l₁[i] ∈ l₁ := List.getElem_mem hi₁
  have hmem₂ : l₂[i] ∈ l₂ := List.getElem_mem hi₂
  have h1i := h₁ _ hmem₁
  have h2i := h₂ _ hmem₂
  -- Extract the equality of Fin N values at position i
  have hi₁' : i < (lgvYCoordsToFinN l₁ h₁).length := by
    simp only [lgvYCoordsToFinN, List.length_pmap]
    exact hi₁
  have hi₂' : i < (lgvYCoordsToFinN l₂ h₂).length := by
    simp only [lgvYCoordsToFinN, List.length_pmap]
    exact hi₂
  have heq_i : (lgvYCoordsToFinN l₁ h₁)[i]'hi₁' = (lgvYCoordsToFinN l₂ h₂)[i]'hi₂' := by
    simp only [heq]
  -- Use getElem_pmap to relate the pmap values to the original list values
  simp only [lgvYCoordsToFinN] at heq_i
  rw [List.getElem_pmap, List.getElem_pmap] at heq_i
  -- heq_i now says the Fin N values are equal
  simp only [Fin.mk.injEq] at heq_i
  -- heq_i : (l₁[i] - 1).toNat = (l₂[i] - 1).toNat
  -- Since both are in [1, N], this implies l₁[i] = l₂[i]
  have h1 : 0 ≤ l₁[i] - 1 := by omega
  have h2 : 0 ≤ l₂[i] - 1 := by omega
  have ha' := Int.toNat_of_nonneg h1
  have hb' := Int.toNat_of_nonneg h2
  simp only [List.get_eq_getElem]
  omega

/-- Helper: lgvYCoordsToFinN inverts the map (fun h => h.val + 1).
    If `l = heights.map (fun h => h.val + 1)`, then `lgvYCoordsToFinN l h = heights`. -/
lemma lgvYCoordsToFinN_map_val_add_one_eq (heights : List (Fin N)) {l : List ℤ}
    (heq : l = heights.map (fun h => (h.val : ℤ) + 1))
    (h : ∀ y ∈ l, 1 ≤ y ∧ y ≤ N) :
    lgvYCoordsToFinN l h = heights := by
  subst heq
  unfold lgvYCoordsToFinN
  apply List.ext_getElem
  · simp [List.length_pmap]
  · intro i hi₁ hi₂
    simp only [List.getElem_pmap, List.getElem_map, Fin.ext_iff]
    have : (((heights[i]).val : ℤ) + 1 - 1).toNat = (heights[i]).val := by omega
    exact this

/-- Convert an LGV path from (a, 1) to (c, N) to a LatticePath.
    This extracts the east-step heights and converts them to Fin N. -/
noncomputable def lgvPathToLatticePath (a c : ℤ) (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hstart : p.start = (a, 1)) (hfinish : p.finish = (c, (N : ℤ))) :
    LatticePath (N := N) a c where
  eastStepHeights :=
    let ycoords := lgvPathEastStepYCoords p.vertices
    let h : ∀ y ∈ ycoords, 1 ≤ y ∧ y ≤ N := by
      intro y hy
      have hbnd := lgvPathEastStepYCoords_bounded p.vertices p.nonempty p.arcs_valid y hy
      simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart hfinish
      rw [hstart, hfinish] at hbnd
      simp at hbnd
      exact hbnd
    lgvYCoordsToFinN ycoords h
  weaklyIncreasing := by
    apply lgvYCoordsToFinN_isChain
    exact lgvPathEastStepYCoords_weaklyIncreasing p.vertices p.arcs_valid
  length_eq := by
    rw [lgvYCoordsToFinN_length]
    rw [lgvPathEastStepYCoords_length_eq_xDisplacement p.vertices p.nonempty p.arcs_valid]
    simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart hfinish
    simp only [hstart, hfinish]

/-- Coordinate sum strictly increases along arcs in the integer lattice. -/
private lemma coordSum_strict_inc (u v : ℤ × ℤ) (h : LGV.integerLattice.arc u v) :
    u.1 + u.2 < v.1 + v.2 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega

/-- Coordinate sum is monotone along paths in the integer lattice. -/
private lemma coordSum_head_le_last (vertices : List (ℤ × ℤ)) (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) :
    (vertices.head h_ne).1 + (vertices.head h_ne).2 ≤
    (vertices.getLast h_ne).1 + (vertices.getLast h_ne).2 := by
  match vertices with
  | [] => simp at h_ne
  | [v] => simp
  | v₀ :: v₁ :: rest =>
    have h_arc : LGV.integerLattice.arc v₀ v₁ := by
      have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
      simp at this; exact this
    have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
        LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
          ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
      intro i hi
      have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
      exact h_arcs (i + 1) hi'
    have ih := coordSum_head_le_last (v₁ :: rest) (List.cons_ne_nil _ _) h_arcs'
    simp only [List.head_cons, List.getLast_cons (List.cons_ne_nil _ _)] at ih ⊢
    have hstep := coordSum_strict_inc v₀ v₁ h_arc
    omega

/-- Coordinate sum strictly increases for paths of length ≥ 2. -/
private lemma coordSum_head_lt_last_of_length_ge_two (vertices : List (ℤ × ℤ)) (h_ne : vertices ≠ [])
    (h_len : vertices.length ≥ 2)
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) :
    (vertices.head h_ne).1 + (vertices.head h_ne).2 <
    (vertices.getLast h_ne).1 + (vertices.getLast h_ne).2 := by
  match vertices with
  | [] => simp at h_ne
  | [v] => simp at h_len
  | v₀ :: v₁ :: rest =>
    have h_arc : LGV.integerLattice.arc v₀ v₁ := by
      have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
      simp at this; exact this
    have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
        LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
          ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
      intro i hi
      have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
      exact h_arcs (i + 1) hi'
    have ih := coordSum_head_le_last (v₁ :: rest) (List.cons_ne_nil _ _) h_arcs'
    simp only [List.head_cons, List.getLast_cons (List.cons_ne_nil _ _)] at ih ⊢
    have hstep := coordSum_strict_inc v₀ v₁ h_arc
    omega

/-- Auxiliary lemma for lgvPath_vertices_eq_of_eastStepYCoords_eq. -/
private lemma lgvPath_vertices_eq_aux (vs₁ vs₂ : List (ℤ × ℤ))
    (h_ne₁ : vs₁ ≠ []) (h_ne₂ : vs₂ ≠ [])
    (h_arcs₁ : ∀ i : ℕ, ∀ hi : i + 1 < vs₁.length,
      LGV.integerLattice.arc (vs₁.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vs₁.get ⟨i + 1, hi⟩))
    (h_arcs₂ : ∀ i : ℕ, ∀ hi : i + 1 < vs₂.length,
      LGV.integerLattice.arc (vs₂.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vs₂.get ⟨i + 1, hi⟩))
    (hstart : vs₁.head h_ne₁ = vs₂.head h_ne₂)
    (hfinish : vs₁.getLast h_ne₁ = vs₂.getLast h_ne₂)
    (hcoords : lgvPathEastStepYCoords vs₁ = lgvPathEastStepYCoords vs₂) :
    vs₁ = vs₂ := by
  induction h : vs₁.length + vs₂.length using Nat.strong_induction_on generalizing vs₁ vs₂ with
  | _ n ih =>
    match hvs₁ : vs₁, hvs₂ : vs₂ with
    | [v₁], [v₂] =>
      simp only [List.head_cons] at hstart
      rw [hstart]
    | [v₁], v₂ :: w₂ :: rest₂ =>
      exfalso
      simp only [List.head_cons, List.getLast_singleton] at hstart hfinish
      have h_len : (v₂ :: w₂ :: rest₂).length ≥ 2 := by simp
      have hlt := coordSum_head_lt_last_of_length_ge_two (v₂ :: w₂ :: rest₂)
        (List.cons_ne_nil _ _) h_len h_arcs₂
      simp only [List.head_cons] at hlt
      have hlast_eq : (v₂ :: w₂ :: rest₂).getLast (List.cons_ne_nil _ _) = v₁ := hfinish.symm
      have hcontra : v₂.1 + v₂.2 < v₂.1 + v₂.2 :=
        calc v₂.1 + v₂.2 < ((v₂ :: w₂ :: rest₂).getLast _).1 + ((v₂ :: w₂ :: rest₂).getLast _).2 := hlt
          _ = v₁.1 + v₁.2 := by rw [hlast_eq]
          _ = v₂.1 + v₂.2 := by rw [hstart]
      omega
    | v₁ :: w₁ :: rest₁, [v₂] =>
      exfalso
      simp only [List.head_cons, List.getLast_singleton] at hstart hfinish
      have h_len : (v₁ :: w₁ :: rest₁).length ≥ 2 := by simp
      have hlt := coordSum_head_lt_last_of_length_ge_two (v₁ :: w₁ :: rest₁)
        (List.cons_ne_nil _ _) h_len h_arcs₁
      simp only [List.head_cons] at hlt
      have hlast_eq : (v₁ :: w₁ :: rest₁).getLast (List.cons_ne_nil _ _) = v₂ := hfinish
      have hcontra : v₁.1 + v₁.2 < v₁.1 + v₁.2 :=
        calc v₁.1 + v₁.2 < ((v₁ :: w₁ :: rest₁).getLast _).1 + ((v₁ :: w₁ :: rest₁).getLast _).2 := hlt
          _ = v₂.1 + v₂.2 := by rw [hlast_eq]
          _ = v₁.1 + v₁.2 := by rw [← hstart]
      omega
    | v₁ :: w₁ :: rest₁, v₂ :: w₂ :: rest₂ =>
      simp only [List.head_cons] at hstart
      have h_arc₁ : LGV.integerLattice.arc v₁ w₁ := by
        have := h_arcs₁ 0 (by simp : 0 + 1 < (v₁ :: w₁ :: rest₁).length)
        simp at this; exact this
      have h_arc₂ : LGV.integerLattice.arc v₂ w₂ := by
        have := h_arcs₂ 0 (by simp : 0 + 1 < (v₂ :: w₂ :: rest₂).length)
        simp at this; exact this
      rcases h_arc₁ with ⟨hx₁, hy₁⟩ | ⟨hx₁, hy₁⟩ <;>
      rcases h_arc₂ with ⟨hx₂, hy₂⟩ | ⟨hx₂, hy₂⟩
      · -- Both east steps
        have hw_eq : w₁ = w₂ := by
          ext
          · rw [hx₁, hx₂]; congr 1; exact congrArg Prod.fst hstart
          · rw [hy₁, hy₂]; exact congrArg Prod.snd hstart
        have h_arcs₁' : ∀ i : ℕ, ∀ hi : i + 1 < (w₁ :: rest₁).length,
            LGV.integerLattice.arc ((w₁ :: rest₁).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₁ :: rest₁).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₁ :: w₁ :: rest₁).length := by simp at hi ⊢; omega
          exact h_arcs₁ (i + 1) hi'
        have h_arcs₂' : ∀ i : ℕ, ∀ hi : i + 1 < (w₂ :: rest₂).length,
            LGV.integerLattice.arc ((w₂ :: rest₂).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₂ :: rest₂).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₂ :: w₂ :: rest₂).length := by simp at hi ⊢; omega
          exact h_arcs₂ (i + 1) hi'
        have hstart' : (w₁ :: rest₁).head (List.cons_ne_nil _ _) =
            (w₂ :: rest₂).head (List.cons_ne_nil _ _) := hw_eq
        have hfinish' : (w₁ :: rest₁).getLast (List.cons_ne_nil _ _) =
            (w₂ :: rest₂).getLast (List.cons_ne_nil _ _) := by
          rw [← List.getLast_cons (List.cons_ne_nil w₁ rest₁),
              ← List.getLast_cons (List.cons_ne_nil w₂ rest₂)]
          exact hfinish
        have hcoords' : lgvPathEastStepYCoords (w₁ :: rest₁) =
            lgvPathEastStepYCoords (w₂ :: rest₂) := by
          simp only [lgvPathEastStepYCoords, hx₁, hy₁, hx₂, hy₂, and_self, ↓reduceIte] at hcoords
          exact (List.cons_eq_cons.mp hcoords).2
        have hlen : (w₁ :: rest₁).length + (w₂ :: rest₂).length < n := by
          simp only [List.length_cons] at h ⊢; omega
        have ih_result := ih ((w₁ :: rest₁).length + (w₂ :: rest₂).length) hlen
            (w₁ :: rest₁) (w₂ :: rest₂)
            (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
            h_arcs₁' h_arcs₂' hstart' hfinish' hcoords' rfl
        rw [List.cons_eq_cons, List.cons_eq_cons]
        exact ⟨hstart, List.cons_eq_cons.mp ih_result⟩
      · -- First east, second north: contradiction
        exfalso
        simp only [lgvPathEastStepYCoords, hx₁, hy₁, and_self, ↓reduceIte] at hcoords
        have h_not_cond₂ : ¬(w₂.1 = v₂.1 + 1 ∧ w₂.2 = v₂.2) := by omega
        simp only [h_not_cond₂, ↓reduceIte] at hcoords
        have h_arcs₂' : ∀ i : ℕ, ∀ hi : i + 1 < (w₂ :: rest₂).length,
            LGV.integerLattice.arc ((w₂ :: rest₂).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₂ :: rest₂).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₂ :: w₂ :: rest₂).length := by simp at hi ⊢; omega
          exact h_arcs₂ (i + 1) hi'
        cases h_rhs : lgvPathEastStepYCoords (w₂ :: rest₂) with
        | nil => rw [h_rhs] at hcoords; exact List.cons_ne_nil _ _ hcoords
        | cons y ys =>
          rw [h_rhs] at hcoords
          have h_y_eq : v₁.2 = y := (List.cons_eq_cons.mp hcoords).1
          have hmem : y ∈ lgvPathEastStepYCoords (w₂ :: rest₂) := by
            rw [h_rhs]; exact List.Mem.head _
          have h_y_ge := lgvPathEastStepYCoords_ge_start (w₂ :: rest₂)
              (List.cons_ne_nil _ _) h_arcs₂' y hmem
          simp only [List.head_cons] at h_y_ge
          have hw2_y : w₂.2 = v₁.2 + 1 := by
            rw [hy₂]; exact congrArg (· + 1) (congrArg Prod.snd hstart.symm)
          omega
      · -- First north, second east: contradiction
        exfalso
        simp only [lgvPathEastStepYCoords, hx₂, hy₂, and_self, ↓reduceIte] at hcoords
        have h_not_cond₁ : ¬(w₁.1 = v₁.1 + 1 ∧ w₁.2 = v₁.2) := by omega
        simp only [h_not_cond₁, ↓reduceIte] at hcoords
        have h_arcs₁' : ∀ i : ℕ, ∀ hi : i + 1 < (w₁ :: rest₁).length,
            LGV.integerLattice.arc ((w₁ :: rest₁).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₁ :: rest₁).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₁ :: w₁ :: rest₁).length := by simp at hi ⊢; omega
          exact h_arcs₁ (i + 1) hi'
        cases h_lhs : lgvPathEastStepYCoords (w₁ :: rest₁) with
        | nil => rw [h_lhs] at hcoords; exact List.cons_ne_nil _ _ hcoords.symm
        | cons y ys =>
          rw [h_lhs] at hcoords
          have h_y_eq : y = v₂.2 := (List.cons_eq_cons.mp hcoords.symm).1.symm
          have hmem : y ∈ lgvPathEastStepYCoords (w₁ :: rest₁) := by
            rw [h_lhs]; exact List.Mem.head _
          have h_y_ge := lgvPathEastStepYCoords_ge_start (w₁ :: rest₁)
              (List.cons_ne_nil _ _) h_arcs₁' y hmem
          simp only [List.head_cons] at h_y_ge
          have hw1_y : w₁.2 = v₂.2 + 1 := by
            rw [hy₁]; exact congrArg (· + 1) (congrArg Prod.snd hstart)
          omega
      · -- Both north steps
        have hw_eq : w₁ = w₂ := by
          ext
          · rw [hx₁, hx₂]; exact congrArg Prod.fst hstart
          · rw [hy₁, hy₂]; exact congrArg (· + 1) (congrArg Prod.snd hstart)
        have h_arcs₁' : ∀ i : ℕ, ∀ hi : i + 1 < (w₁ :: rest₁).length,
            LGV.integerLattice.arc ((w₁ :: rest₁).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₁ :: rest₁).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₁ :: w₁ :: rest₁).length := by simp at hi ⊢; omega
          exact h_arcs₁ (i + 1) hi'
        have h_arcs₂' : ∀ i : ℕ, ∀ hi : i + 1 < (w₂ :: rest₂).length,
            LGV.integerLattice.arc ((w₂ :: rest₂).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((w₂ :: rest₂).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v₂ :: w₂ :: rest₂).length := by simp at hi ⊢; omega
          exact h_arcs₂ (i + 1) hi'
        have hstart' : (w₁ :: rest₁).head (List.cons_ne_nil _ _) =
            (w₂ :: rest₂).head (List.cons_ne_nil _ _) := hw_eq
        have hfinish' : (w₁ :: rest₁).getLast (List.cons_ne_nil _ _) =
            (w₂ :: rest₂).getLast (List.cons_ne_nil _ _) := by
          rw [← List.getLast_cons (List.cons_ne_nil w₁ rest₁),
              ← List.getLast_cons (List.cons_ne_nil w₂ rest₂)]
          exact hfinish
        have hcoords' : lgvPathEastStepYCoords (w₁ :: rest₁) =
            lgvPathEastStepYCoords (w₂ :: rest₂) := by
          simp only [lgvPathEastStepYCoords] at hcoords
          have h_not_cond₁ : ¬(w₁.1 = v₁.1 + 1 ∧ w₁.2 = v₁.2) := by omega
          have h_not_cond₂ : ¬(w₂.1 = v₂.1 + 1 ∧ w₂.2 = v₂.2) := by omega
          simp only [h_not_cond₁, h_not_cond₂, ↓reduceIte] at hcoords
          exact hcoords
        have hlen : (w₁ :: rest₁).length + (w₂ :: rest₂).length < n := by
          simp only [List.length_cons] at h ⊢; omega
        have ih_result := ih ((w₁ :: rest₁).length + (w₂ :: rest₂).length) hlen
            (w₁ :: rest₁) (w₂ :: rest₂)
            (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
            h_arcs₁' h_arcs₂' hstart' hfinish' hcoords' rfl
        rw [List.cons_eq_cons, List.cons_eq_cons]
        exact ⟨hstart, List.cons_eq_cons.mp ih_result⟩

/-!
### Injectivity of lgvPathToLatticePath

The key lemma for the bijection is that `lgvPathToLatticePath` is injective.
This follows from the fact that paths in the integer lattice from the same start
to the same end are uniquely determined by their east-step y-coordinates.
-/

/-- Key uniqueness lemma: Paths in the integer lattice from the same start to the same end
    with the same east-step y-coordinates must have the same vertices.

    This is the fundamental lemma for proving injectivity of `lgvPathToLatticePath`.

    **Proof idea**: At each vertex (x, y), the next step is uniquely determined:
    - If y appears in the remaining east-step y-coordinates, we go east
    - Otherwise, we go north
    Since both paths have the same start and the same east-step y-coordinates,
    they must make the same choices at each step, hence have the same vertices.

    The proof proceeds by strong induction on the total number of steps remaining.
    At each step, we show the next vertex is determined by whether the current
    y-coordinate matches the next east-step height. -/
theorem lgvPath_vertices_eq_of_eastStepYCoords_eq
    (p₁ p₂ : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hstart : p₁.start = p₂.start)
    (hfinish : p₁.finish = p₂.finish)
    (hcoords : lgvPathEastStepYCoords p₁.vertices = lgvPathEastStepYCoords p₂.vertices) :
    p₁.vertices = p₂.vertices :=
  lgvPath_vertices_eq_aux p₁.vertices p₂.vertices p₁.nonempty p₂.nonempty
    p₁.arcs_valid p₂.arcs_valid hstart hfinish hcoords

/-- Corollary: lgvPathToLatticePath is injective on paths with the same start and end.

    If two LGV paths from (a, 1) to (c, N) map to the same LatticePath,
    then they have the same vertices (and hence are equal as paths). -/
theorem lgvPathToLatticePath_injective (a c : ℤ)
    (p₁ p₂ : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hstart₁ : p₁.start = (a, 1)) (hfinish₁ : p₁.finish = (c, (N : ℤ)))
    (hstart₂ : p₂.start = (a, 1)) (hfinish₂ : p₂.finish = (c, (N : ℤ)))
    (heq : lgvPathToLatticePath a c p₁ hstart₁ hfinish₁ =
           lgvPathToLatticePath a c p₂ hstart₂ hfinish₂) :
    p₁ = p₂ := by
  -- The LatticePaths are equal iff their eastStepHeights are equal.
  -- eastStepHeights = lgvYCoordsToFinN (lgvPathEastStepYCoords vertices) ...
  -- Since lgvYCoordsToFinN is injective (it's a pmap that preserves the list structure),
  -- equal eastStepHeights implies equal lgvPathEastStepYCoords.
  -- By lgvPath_vertices_eq_of_eastStepYCoords_eq, the paths have the same vertices.
  -- Paths with the same vertices are equal.
  have hcoords : lgvPathEastStepYCoords p₁.vertices = lgvPathEastStepYCoords p₂.vertices := by
    -- Extract from heq that the eastStepHeights are equal
    have h := congrArg LatticePath.eastStepHeights heq
    simp only [lgvPathToLatticePath] at h
    -- Use lgvYCoordsToFinN_injective to conclude the y-coordinates are equal
    have hbnd₁ : ∀ y ∈ lgvPathEastStepYCoords p₁.vertices, 1 ≤ y ∧ y ≤ N := by
      intro y hy
      have hbnd := lgvPathEastStepYCoords_bounded p₁.vertices p₁.nonempty p₁.arcs_valid y hy
      simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart₁ hfinish₁
      rw [hstart₁, hfinish₁] at hbnd
      simp at hbnd
      exact hbnd
    have hbnd₂ : ∀ y ∈ lgvPathEastStepYCoords p₂.vertices, 1 ≤ y ∧ y ≤ N := by
      intro y hy
      have hbnd := lgvPathEastStepYCoords_bounded p₂.vertices p₂.nonempty p₂.arcs_valid y hy
      simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart₂ hfinish₂
      rw [hstart₂, hfinish₂] at hbnd
      simp at hbnd
      exact hbnd
    exact lgvYCoordsToFinN_injective _ _ hbnd₁ hbnd₂ h
  have hstart : p₁.start = p₂.start := by rw [hstart₁, hstart₂]
  have hfinish : p₁.finish = p₂.finish := by rw [hfinish₁, hfinish₂]
  have hvertices := lgvPath_vertices_eq_of_eastStepYCoords_eq p₁ p₂ hstart hfinish hcoords
  -- Two paths are equal iff their vertices are equal
  cases p₁; cases p₂
  simp only [LGV.SimpleDigraph.Path.mk.injEq] at hvertices ⊢
  exact hvertices

/-!
### LatticePath to LGV Path Bijection: Inverse Direction

We construct the inverse of `lgvPathToLatticePath`, converting a `LatticePath` back to
an LGV `SimpleDigraph.Path`. This completes the bidirectional conversion between the
two lattice path representations.

**Representation equivalence**:
- `LGV.LatticePath` (in LGV1.lean): `List LatticeStep` (sequence of east/north steps)
- `SymmetricFunctions.LatticePath` (here): `eastStepHeights : List (Fin N)` with constraints

The bijection works because:
1. A path from (a, 1) to (c, N) is uniquely determined by its east-step heights
2. East-step heights form a weakly increasing sequence of length (c - a).toNat
3. This is exactly the data in a LatticePath

**Construction algorithm**:
Given eastStepHeights = [h₀, h₁, ...], construct vertices by:
1. Start at (a, 1)
2. For each height hᵢ (which represents y-coordinate hᵢ.val + 1):
   - Go north until y = hᵢ.val + 1
   - Go east
3. Finally go north until y = N
-/

/-- Build vertices from east-step heights using fuel-based recursion.
    This is the core algorithm for constructing an LGV path from a LatticePath.

    Parameters:
    - N: the height bound (y-coordinates range in [1, N])
    - x, y: current position
    - heights: remaining east-step heights to process
    - fuel: recursion fuel (ensures termination)

    The algorithm:
    - If no heights remain, go north until y = N
    - Otherwise, if y < next_height + 1, go north
    - Otherwise (y = next_height + 1), go east and consume the height -/
private def buildVerticesAux (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ) : List (ℤ × ℤ) :=
  match fuel with
  | 0 => [(x, y)]
  | fuel' + 1 =>
    match heights with
    | [] =>
      if y < N then (x, y) :: buildVerticesAux N x (y + 1) [] fuel'
      else [(x, y)]
    | h :: rest =>
      let targetY := (h.val : ℤ) + 1
      if y < targetY then
        (x, y) :: buildVerticesAux N x (y + 1) heights fuel'
      else
        (x, y) :: buildVerticesAux N (x + 1) y rest fuel'

/-- Build the vertices of an LGV path from a LatticePath's east-step heights.

    The fuel is set to (c - a).toNat + N, which is an upper bound on the number
    of vertices: (c - a) east-steps + (N - 1) north-steps + 1 endpoint. -/
private def buildVertices (a c : ℤ) (N : ℕ) (eastStepHeights : List (Fin N)) : List (ℤ × ℤ) :=
  let maxSteps := (c - a).toNat + N
  buildVerticesAux N a 1 eastStepHeights maxSteps

/-- The vertices built by buildVerticesAux are never empty. -/
private lemma buildVerticesAux_nonempty (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ) :
    buildVerticesAux N x y heights fuel ≠ [] := by
  induction fuel generalizing x y heights with
  | zero => simp [buildVerticesAux]
  | succ n ih =>
    simp only [buildVerticesAux]
    cases heights with
    | nil => split_ifs <;> simp
    | cons h rest => simp only [ne_eq]; split_ifs <;> simp

/-- The vertices built by buildVertices are never empty. -/
private lemma buildVertices_nonempty (a c : ℤ) (N : ℕ) (eastStepHeights : List (Fin N)) :
    buildVertices a c N eastStepHeights ≠ [] := by
  simp only [buildVertices]
  exact buildVerticesAux_nonempty N a 1 eastStepHeights _

/-- The first vertex built by buildVerticesAux is (x, y). -/
private lemma buildVerticesAux_head (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ 1 ∨ heights = []) :
    (buildVerticesAux N x y heights fuel).head (buildVerticesAux_nonempty N x y heights fuel) = (x, y) := by
  cases fuel with
  | zero => simp [buildVerticesAux]
  | succ n =>
    simp only [buildVerticesAux]
    cases heights with
    | nil => split_ifs <;> simp
    | cons h rest => simp only; split_ifs with h1 <;> simp

/-- The first vertex built by buildVertices is (a, 1) when N ≥ 1. -/
private lemma buildVertices_head (a c : ℤ) (N : ℕ) (eastStepHeights : List (Fin N)) (hN : N ≥ 1) :
    (buildVertices a c N eastStepHeights).head (buildVertices_nonempty a c N eastStepHeights) = (a, 1) := by
  simp only [buildVertices]
  apply buildVerticesAux_head
  left
  omega
/-- Helper: get the first element of buildVerticesAux using array notation. -/
private lemma buildVerticesAux_head_getElem (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (h : 0 < (buildVerticesAux N x y heights fuel).length) :
    (buildVerticesAux N x y heights fuel)[0] = (x, y) := by
  cases fuel with
  | zero => simp [buildVerticesAux]
  | succ n =>
    cases heights with
    | nil =>
      simp only [buildVerticesAux]
      split_ifs <;> simp
    | cons hd rest =>
      simp only [buildVerticesAux]
      split_ifs <;> simp

/-- Helper: the length of buildVerticesAux is at least 1. -/
private lemma buildVerticesAux_length_pos (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ) :
    0 < (buildVerticesAux N x y heights fuel).length :=
  List.length_pos_of_ne_nil (buildVerticesAux_nonempty N x y heights fuel)

/-- All x-coordinates in buildVerticesAux are ≥ the starting x-coordinate.
    This is because we only move north (same x) or east (x + 1). -/
private lemma buildVerticesAux_x_ge (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (idx : ℕ) (hidx : idx < (buildVerticesAux N x y heights fuel).length) :
    (buildVerticesAux N x y heights fuel)[idx].1 ≥ x := by
  induction fuel generalizing x y heights idx with
  | zero =>
    simp only [buildVerticesAux, List.length_singleton] at hidx
    have : idx = 0 := by omega
    subst this
    simp only [buildVerticesAux, List.getElem_singleton, ge_iff_le, le_refl]
  | succ n ih =>
    cases heights with
    | nil =>
      simp only [buildVerticesAux] at hidx ⊢
      split_ifs at hidx ⊢ with hy_lt
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N x (y + 1) [] n).length := by
            simp only [List.length_cons] at hidx; omega
          have hih := ih x (y + 1) [] idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hih ⊢
          exact hih
      · simp only [List.length_singleton] at hidx
        have : idx = 0 := by omega
        subst this
        simp only [List.getElem_singleton, ge_iff_le, le_refl]
    | cons h rest =>
      simp only [buildVerticesAux] at hidx ⊢
      split_ifs at hidx ⊢ with hy_lt
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N x (y + 1) (h :: rest) n).length := by
            simp only [List.length_cons] at hidx; omega
          have hih := ih x (y + 1) (h :: rest) idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hih ⊢
          exact hih
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N (x + 1) y rest n).length := by
            simp only [List.length_cons] at hidx; omega
          have hge := ih (x + 1) y rest idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hge ⊢
          omega

/-- Y-coordinate upper bound invariant for buildVerticesAux.
    At x-coordinate x + j (after j east steps), the y-coordinate is at most heights[j].val + 1.
    This is because we haven't made the j-th east step yet. -/
private lemma buildVerticesAux_y_upper_bound (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ heights.length + (N - y.toNat)) (hy : 1 ≤ y) (hyN : y ≤ N)
    (hchain : heights.IsChain (· ≤ ·))
    (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1)
    (idx : ℕ) (hidx : idx < (buildVerticesAux N x y heights fuel).length)
    (j : ℕ) (hj : j < heights.length)
    (hx_eq : (buildVerticesAux N x y heights fuel)[idx].1 = x + j) :
    (buildVerticesAux N x y heights fuel)[idx].2 ≤ (heights[j]).val + 1 := by
  induction fuel generalizing x y heights idx j with
  | zero =>
    simp only [buildVerticesAux, List.length_singleton] at hidx
    have hidx_eq : idx = 0 := by omega
    subst hidx_eq
    simp only [buildVerticesAux, List.getElem_singleton] at hx_eq ⊢
    have hj_eq : j = 0 := by omega
    subst hj_eq
    have h0 : heights[0] ∈ heights := List.getElem_mem hj
    exact hbounds heights[0] h0
  | succ n ih =>
    cases heights with
    | nil => simp at hj
    | cons h rest =>
      simp only [buildVerticesAux] at hidx hx_eq ⊢
      split_ifs at hidx hx_eq ⊢ with hy_lt
      · -- North case: y < h.val + 1
        cases idx with
        | zero =>
          simp only [List.getElem_cons_zero] at hx_eq ⊢
          have hj_eq : j = 0 := by omega
          subst hj_eq
          simp only [List.getElem_cons_zero]
          omega
        | succ idx' =>
          simp only [List.length_cons] at hidx
          have hidx' : idx' < (buildVerticesAux N x (y + 1) (h :: rest) n).length := by omega
          simp only [List.getElem_cons_succ] at hx_eq ⊢
          have hfuel' : n ≥ (h :: rest).length + (N - (y + 1).toNat) := by
            simp only [List.length_cons] at hfuel ⊢
            have hy_pos : 0 ≤ y := by omega
            have h1 : (y + 1).toNat = y.toNat + 1 := by omega
            rw [h1]
            have hle : y.toNat < N := by
              have hh := h.isLt
              have hthis : y < N := by omega
              have htonat : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy_pos
              omega
            omega
          have hbounds' : ∀ h' ∈ (h :: rest), (y + 1) ≤ (h'.val : ℤ) + 1 := by
            intro h' hmem
            cases List.mem_cons.mp hmem with
            | inl heq => subst heq; omega
            | inr hrest =>
              have hrel : h ≤ h' := hchain.rel_cons hrest
              have hval : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
              omega
          have hyN' : y + 1 ≤ N := by
            have hh := h.isLt
            have hb := hbounds h List.mem_cons_self
            omega
          exact ih x (y + 1) (h :: rest) hfuel' (by omega) hyN' hchain hbounds' idx' hidx' j hj hx_eq
      · -- East case: y ≥ h.val + 1
        cases idx with
        | zero =>
          simp only [List.getElem_cons_zero] at hx_eq ⊢
          have hj_eq : j = 0 := by omega
          subst hj_eq
          simp only [List.getElem_cons_zero]
          have hb := hbounds h List.mem_cons_self
          omega
        | succ idx' =>
          simp only [List.length_cons] at hidx
          have hidx' : idx' < (buildVerticesAux N (x + 1) y rest n).length := by omega
          simp only [List.getElem_cons_succ] at hx_eq ⊢
          have hx_ge := buildVerticesAux_x_ge N (x + 1) y rest n idx' hidx'
          have hj_pos : j ≥ 1 := by omega
          have hj' : j - 1 < rest.length := by simp only [List.length_cons] at hj; omega
          have hfuel' : n ≥ rest.length + (N - y.toNat) := by
            simp only [List.length_cons] at hfuel; omega
          have hchain' : rest.IsChain (· ≤ ·) := hchain.tail
          have hbounds' : ∀ h' ∈ rest, y ≤ (h'.val : ℤ) + 1 := by
            intro h' hmem
            have hrel : h ≤ h' := hchain.rel_cons hmem
            have hh_bound : y ≤ (h.val : ℤ) + 1 := hbounds h List.mem_cons_self
            have h_ge : ¬ y < (h.val : ℤ) + 1 := hy_lt
            have hy_eq : y = (h.val : ℤ) + 1 := by omega
            have hval : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
            omega
          have hx_eq' : (buildVerticesAux N (x + 1) y rest n)[idx'].1 = (x + 1) + ↑(j - 1) := by
            have h1 : (x : ℤ) + j = (x + 1) + ((j : ℤ) - 1) := by ring
            have h2 : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
            rw [h2, ← h1, ← hx_eq]
          have ih_result := ih (x + 1) y rest hfuel' hy hyN hchain' hbounds' idx' hidx' (j - 1) hj' hx_eq'
          have hval_eq : (rest[j - 1] : Fin N).val = ((h :: rest)[j]'hj : Fin N).val := by
            cases j with
            | zero => omega
            | succ k => simp only [List.getElem_cons_succ, Nat.succ_sub_one]
          calc (buildVerticesAux N (x + 1) y rest n)[idx'].2
              ≤ ↑↑rest[j - 1] + 1 := ih_result
            _ = ↑((h :: rest)[j]'hj : Fin N).val + 1 := by rw [hval_eq]

/-- All y-coordinates in buildVerticesAux are ≥ the starting y-coordinate.
    This is because we only move north (y + 1) or east (same y), never south. -/
private lemma buildVerticesAux_y_ge (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (idx : ℕ) (hidx : idx < (buildVerticesAux N x y heights fuel).length) :
    (buildVerticesAux N x y heights fuel)[idx].2 ≥ y := by
  induction fuel generalizing x y heights idx with
  | zero =>
    simp only [buildVerticesAux, List.length_singleton] at hidx
    have : idx = 0 := by omega
    subst this
    simp only [buildVerticesAux, List.getElem_singleton, ge_iff_le, le_refl]
  | succ n ih =>
    cases heights with
    | nil =>
      simp only [buildVerticesAux] at hidx ⊢
      split_ifs at hidx ⊢ with hy_lt
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N x (y + 1) [] n).length := by
            simp only [List.length_cons] at hidx; omega
          have hih := ih x (y + 1) [] idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hih ⊢
          omega
      · simp only [List.length_singleton] at hidx
        have : idx = 0 := by omega
        subst this
        simp only [List.getElem_singleton, ge_iff_le, le_refl]
    | cons h rest =>
      simp only [buildVerticesAux] at hidx ⊢
      split_ifs at hidx ⊢ with hy_lt
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N x (y + 1) (h :: rest) n).length := by
            simp only [List.length_cons] at hidx; omega
          have hih := ih x (y + 1) (h :: rest) idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hih ⊢
          omega
      · cases idx with
        | zero =>
          simp only [List.getElem_cons_zero, ge_iff_le, le_refl]
        | succ idx' =>
          have hidx' : idx' < (buildVerticesAux N (x + 1) y rest n).length := by
            simp only [List.length_cons] at hidx; omega
          have hge := ih (x + 1) y rest idx' hidx'
          simp only [ge_iff_le, List.getElem_cons_succ] at hge ⊢
          exact hge

/-- Y-coordinate lower bound invariant for buildVerticesAux.
    At x-coordinate x + j (after j east steps) where j > 0, the y-coordinate is at least heights[j-1].val + 1.
    This is because the (j-1)-th east step happened at y = heights[j-1].val + 1, and we never go south. -/
private lemma buildVerticesAux_y_lower_bound (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ heights.length + (N - y.toNat)) (hy : 1 ≤ y) (hyN : y ≤ N)
    (hchain : heights.IsChain (· ≤ ·))
    (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1)
    (idx : ℕ) (hidx : idx < (buildVerticesAux N x y heights fuel).length)
    (j : ℕ) (hj : j < heights.length) (hj_pos : 0 < j)
    (hx_eq : (buildVerticesAux N x y heights fuel)[idx].1 = x + j) :
    (buildVerticesAux N x y heights fuel)[idx].2 ≥ (heights[j - 1]).val + 1 := by
  induction fuel generalizing x y heights idx j with
  | zero =>
    simp only [buildVerticesAux, List.length_singleton] at hidx
    have hidx_eq : idx = 0 := by omega
    subst hidx_eq
    simp only [buildVerticesAux, List.getElem_singleton] at hx_eq
    -- At fuel = 0, x_coord = x, so j = 0, but hj_pos says j > 0, contradiction
    omega
  | succ n ih =>
    cases heights with
    | nil => simp at hj
    | cons h rest =>
      simp only [buildVerticesAux] at hidx hx_eq ⊢
      split_ifs at hidx hx_eq ⊢ with hy_lt
      · -- North case: y < h.val + 1
        cases idx with
        | zero =>
          simp only [List.getElem_cons_zero] at hx_eq
          -- At idx = 0, x_coord = x, so j = 0, but hj_pos says j > 0, contradiction
          omega
        | succ idx' =>
          simp only [List.length_cons] at hidx
          have hidx' : idx' < (buildVerticesAux N x (y + 1) (h :: rest) n).length := by omega
          simp only [List.getElem_cons_succ] at hx_eq ⊢
          have hfuel' : n ≥ (h :: rest).length + (N - (y + 1).toNat) := by
            simp only [List.length_cons] at hfuel ⊢
            have hy_pos : 0 ≤ y := by omega
            have h1 : (y + 1).toNat = y.toNat + 1 := by omega
            rw [h1]
            have hle : y.toNat < N := by
              have hh := h.isLt
              have hthis : y < N := by omega
              have htonat : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy_pos
              omega
            omega
          have hbounds' : ∀ h' ∈ (h :: rest), (y + 1) ≤ (h'.val : ℤ) + 1 := by
            intro h' hmem
            cases List.mem_cons.mp hmem with
            | inl heq => subst heq; omega
            | inr hrest =>
              have hrel : h ≤ h' := hchain.rel_cons hrest
              have hval : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
              omega
          have hyN' : y + 1 ≤ N := by
            have hh := h.isLt
            have hb := hbounds h List.mem_cons_self
            omega
          exact ih x (y + 1) (h :: rest) hfuel' (by omega) hyN' hchain hbounds' idx' hidx' j hj hj_pos hx_eq
      · -- East case: y ≥ h.val + 1, so y = h.val + 1 exactly (since y ≤ h.val + 1 from hbounds)
        have hy_eq : y = (h.val : ℤ) + 1 := by
          have hb := hbounds h List.mem_cons_self
          omega
        cases idx with
        | zero =>
          simp only [List.getElem_cons_zero] at hx_eq
          -- At idx = 0, x_coord = x, so j = 0, but hj_pos says j > 0, contradiction
          omega
        | succ idx' =>
          simp only [List.length_cons] at hidx
          have hidx' : idx' < (buildVerticesAux N (x + 1) y rest n).length := by omega
          simp only [List.getElem_cons_succ] at hx_eq ⊢
          have hx_ge := buildVerticesAux_x_ge N (x + 1) y rest n idx' hidx'
          -- After the east step, we're at x+1 with rest heights
          -- If j = 1, we need y ≥ heights[0].val + 1 = h.val + 1, which is true since y = h.val + 1
          -- If j > 1, we use IH with j-1
          cases j with
          | zero => omega  -- contradicts hj_pos
          | succ j' =>
            cases j' with
            | zero =>
              -- j = 1, need y ≥ heights[0].val + 1 = h.val + 1
              simp only [Nat.sub_self, List.getElem_cons_zero, ge_iff_le]
              -- The y-coordinate at idx' in the recursive call is ≥ y (since we never go south)
              have hy_lower := buildVerticesAux_y_ge N (x + 1) y rest n idx' hidx'
              calc (h.val : ℤ) + 1 = y := by omega
                _ ≤ (buildVerticesAux N (x + 1) y rest n)[idx'].2 := hy_lower
            | succ j'' =>
              -- j = j'' + 2 > 1, use IH with j - 1 = j'' + 1
              have hj' : j'' + 1 < rest.length := by simp only [List.length_cons] at hj; omega
              have hj'_pos : 0 < j'' + 1 := by omega
              have hfuel' : n ≥ rest.length + (N - y.toNat) := by
                simp only [List.length_cons] at hfuel; omega
              have hchain' : rest.IsChain (· ≤ ·) := hchain.tail
              have hbounds' : ∀ h' ∈ rest, y ≤ (h'.val : ℤ) + 1 := by
                intro h' hmem
                have hrel : h ≤ h' := hchain.rel_cons hmem
                have hval : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
                omega
              have hx_eq' : (buildVerticesAux N (x + 1) y rest n)[idx'].1 = (x + 1) + ↑(j'' + 1) := by
                have h1 : (x : ℤ) + (j'' + 2) = (x + 1) + (j'' + 1) := by ring
                have h2 : (j'' + 1 + 1 : ℕ) = j'' + 2 := by ring
                have h3 : ((j'' + 1 + 1 : ℕ) : ℤ) = ((j'' + 2 : ℕ) : ℤ) := by omega
                have h4 : ((j'' + 1 : ℕ) : ℤ) = (j'' : ℤ) + 1 := by omega
                omega
              have ih_result := ih (x + 1) y rest hfuel' hy hyN hchain' hbounds' idx' hidx' (j'' + 1) hj' hj'_pos hx_eq'
              -- ih_result says y_coord ≥ rest[j'' + 1 - 1].val + 1 = rest[j''].val + 1
              -- We need y_coord ≥ (h :: rest)[j'' + 2 - 1].val + 1 = (h :: rest)[j'' + 1].val + 1 = rest[j''].val + 1
              simp only [Nat.succ_sub_one, List.getElem_cons_succ]
              exact ih_result

/-- Consecutive vertices in buildVerticesAux satisfy the arc relation.
    Each step is either north (y+1) or east (x+1).
    
    **Proof sketch** (by induction on fuel):
    - Base case (fuel = 0): list is [(x, y)], length 1, no arcs to check (vacuously true)
    - Inductive case: split on heights (nil vs cons h rest)
      - For nil: split on y < N
        - If y < N: first vertex is (x, y), second is head of buildVerticesAux N x (y+1) [] n = (x, y+1)
          This is a north arc. Then apply IH for remaining arcs.
        - If y ≥ N: list is [(x, y)], length 1, no arcs
      - For cons h rest: split on y < h.val + 1
        - If y < h.val + 1: first arc is (x, y) → (x, y+1) (north), then apply IH
        - If y ≥ h.val + 1: first arc is (x, y) → (x+1, y) (east), then apply IH
    
    **Key technical issue**: The if-then-else in the goal must be simplified using the
    hypothesis (e.g., `simp only [hlt, ↓reduceIte]`), but this interacts poorly with
    List.get indexing. May need explicit `convert` or rewrites. -/
private lemma buildVerticesAux_arcs_valid (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ heights.length + (N - y.toNat)) (hy : 1 ≤ y) (hyN : y ≤ N) :
    ∀ i : ℕ, ∀ hi : i + 1 < (buildVerticesAux N x y heights fuel).length,
      LGV.integerLattice.arc
        ((buildVerticesAux N x y heights fuel).get ⟨i, Nat.lt_of_succ_lt hi⟩)
        ((buildVerticesAux N x y heights fuel).get ⟨i + 1, hi⟩) := by
  induction fuel generalizing x y heights with
  | zero =>
    intro i hi
    simp only [buildVerticesAux, List.length_singleton] at hi
    omega
  | succ n ih =>
    intro i hi
    simp only [buildVerticesAux] at hi ⊢
    cases heights with
    | nil =>
      by_cases hy_lt : y < (N : ℤ)
      · -- y < N: list is (x, y) :: buildVerticesAux N x (y + 1) [] n
        simp only [List.get_eq_getElem, hy_lt, ↓reduceIte] at hi ⊢
        cases i with
        | zero =>
          -- Arc from (x, y) to (x, y + 1)
          have hne : buildVerticesAux N x (y + 1) [] n ≠ [] := buildVerticesAux_nonempty N x (y + 1) [] n
          have h1 : (buildVerticesAux N x (y + 1) [] n).head hne = (x, y + 1) := by
            apply buildVerticesAux_head; right; rfl
          simp only [List.getElem_cons_zero, List.getElem_cons_succ,
            List.head_eq_getElem_zero hne] at h1 ⊢
          rw [h1]
          rw [LGV.integerLattice_arc_iff]
          right; rfl
        | succ j =>
          simp only [List.getElem_cons_succ]
          have hi' : j + 1 < (buildVerticesAux N x (y + 1) [] n).length := by
            simp only [List.length_cons] at hi; omega
          have hfuel' : n ≥ ([] : List (Fin N)).length + (N - (y + 1).toNat) := by
            simp only [List.length_nil, zero_add]
            have hy_pos : 0 ≤ y := by omega
            have h1 : (y + 1).toNat = y.toNat + 1 := by
              have := Int.toNat_of_nonneg hy_pos; omega
            rw [h1]
            simp only [List.length_nil, zero_add] at hfuel
            omega
          have result := ih x (y + 1) [] hfuel' (by omega) (by omega) j hi'
          simp only [List.get_eq_getElem] at result
          exact result
      · -- y ≥ N: list is [(x, y)]
        simp only [hy_lt, ↓reduceIte, List.length_singleton] at hi
        omega
    | cons h rest =>
      by_cases hy_lt : y < (h.val : ℤ) + 1
      · -- y < h.val + 1: list is (x, y) :: buildVerticesAux N x (y + 1) (h :: rest) n
        simp only [List.get_eq_getElem, hy_lt, ↓reduceIte] at hi ⊢
        cases i with
        | zero =>
          have hne : buildVerticesAux N x (y + 1) (h :: rest) n ≠ [] :=
            buildVerticesAux_nonempty N x (y + 1) (h :: rest) n
          have h1 : (buildVerticesAux N x (y + 1) (h :: rest) n).head hne = (x, y + 1) := by
            apply buildVerticesAux_head
            left
            simp only [List.length_cons] at hfuel
            have hy_pos : 0 ≤ y := by omega
            have hN_y : N - y.toNat ≥ 1 := by
              have hh := h.isLt
              have h1 : y ≤ h.val := by omega
              have h2 : y.toNat = y := Int.toNat_of_nonneg hy_pos
              omega
            omega
          simp only [List.getElem_cons_zero, List.getElem_cons_succ,
            List.head_eq_getElem_zero hne] at h1 ⊢
          rw [h1]
          rw [LGV.integerLattice_arc_iff]
          right; rfl
        | succ j =>
          simp only [List.getElem_cons_succ]
          have hi' : j + 1 < (buildVerticesAux N x (y + 1) (h :: rest) n).length := by
            simp only [List.length_cons] at hi; omega
          have hfuel' : n ≥ (h :: rest).length + (N - (y + 1).toNat) := by
            simp only [List.length_cons]
            have hy_pos : 0 ≤ y := by omega
            have h1 : (y + 1).toNat = y.toNat + 1 := by
              have := Int.toNat_of_nonneg hy_pos; omega
            rw [h1]
            simp only [List.length_cons] at hfuel
            omega
          have hyN' : y + 1 ≤ N := by have hh := h.isLt; omega
          have result := ih x (y + 1) (h :: rest) hfuel' (by omega) hyN' j hi'
          simp only [List.get_eq_getElem] at result
          exact result
      · -- y ≥ h.val + 1: list is (x, y) :: buildVerticesAux N (x + 1) y rest n
        simp only [List.get_eq_getElem, hy_lt, ↓reduceIte] at hi ⊢
        cases i with
        | zero =>
          have hne : buildVerticesAux N (x + 1) y rest n ≠ [] :=
            buildVerticesAux_nonempty N (x + 1) y rest n
          have h1 : (buildVerticesAux N (x + 1) y rest n).head hne = (x + 1, y) := by
            apply buildVerticesAux_head
            cases rest with
            | nil => right; rfl
            | cons _ _ =>
              left
              simp only [List.length_cons] at hfuel
              omega
          simp only [List.getElem_cons_zero, List.getElem_cons_succ,
            List.head_eq_getElem_zero hne] at h1 ⊢
          rw [h1]
          rw [LGV.integerLattice_arc_iff]
          left; rfl
        | succ j =>
          simp only [List.getElem_cons_succ]
          have hi' : j + 1 < (buildVerticesAux N (x + 1) y rest n).length := by
            simp only [List.length_cons] at hi; omega
          have hfuel' : n ≥ rest.length + (N - y.toNat) := by
            simp only [List.length_cons] at hfuel; omega
          have result := ih (x + 1) y rest hfuel' hy hyN j hi'
          simp only [List.get_eq_getElem] at result
          exact result

/-- Helper: toNat of (y + 1) equals toNat of y plus 1 when y is nonnegative. -/
private lemma toNat_add_one_of_nonneg (y : ℤ) (hy_pos : 0 ≤ y) : (y + 1).toNat = y.toNat + 1 := by
  have h1 : (y + 1) = (y.toNat : ℤ) + 1 := by rw [Int.toNat_of_nonneg hy_pos]
  conv_lhs => rw [h1]
  simp only [Int.toNat_natCast_add_one]

/-- The last vertex built by buildVerticesAux is (x + heights.length, N) when fuel is sufficient.
    
    **Proof sketch** (by induction on fuel with generalized x, y, heights):
    - Base case (fuel = 0): list is [(x, y)], so getLast = (x, y).
      Need to show (x, y) = (x + heights.length, N).
      From hfuel: 0 ≥ heights.length + (N - y.toNat), so heights = [] and y = N.
      Then x + [].length = x and we're done.
    - Inductive case: split on heights (nil vs cons)
      - For nil: split on y < N
        - If y < N: getLast of (x,y) :: buildVerticesAux N x (y+1) [] n
          = getLast of buildVerticesAux N x (y+1) [] n (since list is nonempty)
          By IH, this is (x + [].length, N) = (x, N) = (x + 0, N). ✓
        - If y ≥ N: list is [(x, y)], so getLast = (x, y) = (x + 0, N) since y = N. ✓
      - For cons h rest: split on y < h.val + 1
        - If y < h.val + 1: getLast = getLast of buildVerticesAux N x (y+1) (h::rest) n
          By IH with same heights, this is (x + (h::rest).length, N). ✓
        - If y ≥ h.val + 1: getLast = getLast of buildVerticesAux N (x+1) y rest n
          By IH with rest, this is ((x+1) + rest.length, N) = (x + (h::rest).length, N). ✓
    
    **Key**: The hchain and hbounds hypotheses ensure the algorithm processes heights
    in order and doesn't skip any. -/
private lemma buildVerticesAux_getLast (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ heights.length + (N - y.toNat)) (hy : 1 ≤ y) (hyN : y ≤ N)
    (_hN : 0 < N)
    (hchain : heights.IsChain (· ≤ ·))
    (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1) :
    (buildVerticesAux N x y heights fuel).getLast (buildVerticesAux_nonempty N x y heights fuel) =
    (x + heights.length, (N : ℤ)) := by
  induction fuel generalizing x y heights with
  | zero =>
    simp only [buildVerticesAux, List.getLast_singleton]
    have hlen : heights.length = 0 := by omega
    have h2 : N ≤ y.toNat := by omega
    have hynonneg : 0 ≤ y := by omega
    have hyN' : y.toNat ≤ N := by
      have := Int.toNat_of_nonneg hynonneg
      omega
    have htonat_eq : y.toNat = N := le_antisymm hyN' h2
    have hy_eq : y = N := by
      have := Int.toNat_of_nonneg hynonneg
      omega
    rw [hlen, hy_eq]
    ring_nf
  | succ n ih =>
    cases heights with
    | nil =>
      simp only [List.length_nil]
      simp only [buildVerticesAux]
      split_ifs with hy_lt
      · -- y < N, so we recurse north
        simp only [List.getLast_cons (buildVerticesAux_nonempty N x (y + 1) [] n)]
        have hfuel' : n ≥ ([] : List (Fin N)).length + (N - (y + 1).toNat) := by
          simp only [List.length_nil, zero_add]
          have hy_pos : 0 ≤ y := by omega
          have h1 : (y + 1).toNat = y.toNat + 1 := toNat_add_one_of_nonneg y hy_pos
          rw [h1]
          simp only [List.length_nil, zero_add] at hfuel
          omega
        have ih_result := ih x (y + 1) ([] : List (Fin N)) hfuel' (by omega) (by omega)
          List.isChain_nil (by simp)
        simp only [List.length_nil, Nat.cast_zero, add_zero] at ih_result ⊢
        exact ih_result
      · -- y ≥ N, so y = N
        simp only [List.getLast_singleton]
        have : y = N := by
          have h1 : y ≤ N := hyN
          have h2 : ¬ y < N := hy_lt
          omega
        simp [this]
    | cons h rest =>
      simp only [buildVerticesAux]
      split_ifs with hy_lt
      · -- North case: y < h.val + 1
        simp only [List.getLast_cons (buildVerticesAux_nonempty N x (y + 1) (h :: rest) n)]
        have hy_pos : 0 ≤ y := by omega
        have h1 : (y + 1).toNat = y.toNat + 1 := toNat_add_one_of_nonneg y hy_pos
        have hfuel' : n ≥ (h :: rest).length + (N - (y + 1).toNat) := by
          simp only [List.length_cons] at hfuel ⊢
          rw [h1]
          have hle : y.toNat < N := by
            have hh := h.isLt
            have : y < N := by omega
            have htonat : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy_pos
            omega
          omega
        have hbounds' : ∀ h' ∈ (h :: rest), (y + 1) ≤ (h'.val : ℤ) + 1 := by
          intro h' hmem
          cases List.mem_cons.mp hmem with
          | inl heq =>
            subst heq
            omega
          | inr hrest =>
            have hrel : h ≤ h' := hchain.rel_cons hrest
            have : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
            omega
        have hyN' : y + 1 ≤ N := by
          have hh := h.isLt
          have hb := hbounds h List.mem_cons_self
          omega
        have ih_result := ih x (y + 1) (h :: rest) hfuel' (by omega) hyN' hchain hbounds'
        exact ih_result
      · -- East case: y ≥ h.val + 1
        simp only [List.getLast_cons (buildVerticesAux_nonempty N (x + 1) y rest n)]
        have hfuel' : n ≥ rest.length + (N - y.toNat) := by
          simp only [List.length_cons] at hfuel
          omega
        have hchain' : rest.IsChain (· ≤ ·) := hchain.tail
        have hbounds' : ∀ h' ∈ rest, y ≤ (h'.val : ℤ) + 1 := by
          intro h' hmem
          have hrel : h ≤ h' := hchain.rel_cons hmem
          have hh_bound : y ≤ (h.val : ℤ) + 1 := hbounds h List.mem_cons_self
          have h_ge : ¬ y < (h.val : ℤ) + 1 := hy_lt
          have hy_eq : y = (h.val : ℤ) + 1 := by omega
          have : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
          omega
        have ih_result := ih (x + 1) y rest hfuel' hy hyN hchain' hbounds'
        simp only [List.length_cons]
        convert ih_result using 1
        push_cast
        ring_nf

/-- Wrapper: buildVertices produces valid arcs. -/
private lemma buildVertices_arcs_valid (a c : ℤ) (N : ℕ) (eastStepHeights : List (Fin N))
    (_hN : 0 < N) (hlen : eastStepHeights.length = (c - a).toNat) (_h : 0 ≤ c - a) :
    ∀ i : ℕ, ∀ hi : i + 1 < (buildVertices a c N eastStepHeights).length,
      LGV.integerLattice.arc
        ((buildVertices a c N eastStepHeights).get ⟨i, Nat.lt_of_succ_lt hi⟩)
        ((buildVertices a c N eastStepHeights).get ⟨i + 1, hi⟩) := by
  simp only [buildVertices]
  apply buildVerticesAux_arcs_valid
  · simp only [hlen]; omega
  · omega
  · omega

/-- Wrapper: buildVertices ends at (c, N). -/
private lemma buildVertices_getLast (a c : ℤ) (N : ℕ) (eastStepHeights : List (Fin N))
    (hN : 0 < N) (hlen : eastStepHeights.length = (c - a).toNat) (h : 0 ≤ c - a)
    (hchain : eastStepHeights.IsChain (· ≤ ·)) :
    (buildVertices a c N eastStepHeights).getLast (buildVertices_nonempty a c N eastStepHeights) =
    (c, (N : ℤ)) := by
  simp only [buildVertices]
  have hbounds : ∀ h ∈ eastStepHeights, (1 : ℤ) ≤ (h.val : ℤ) + 1 := by
    intro h _; omega
  have hfuel : (c - a).toNat + N ≥ eastStepHeights.length + (N - (1 : ℤ).toNat) := by
    simp only [hlen, Int.toNat_one]; omega
  have hlast := buildVerticesAux_getLast N a 1 eastStepHeights ((c - a).toNat + N)
    hfuel (by omega) (by omega) hN hchain hbounds
  simp only [hlen] at hlast
  -- hlast says the last vertex is (a + (c-a).toNat, N)
  -- We need to show this equals (c, N)
  -- Since 0 ≤ c - a, we have (c - a).toNat = c - a (as integers)
  -- So a + (c - a).toNat = a + (c - a) = c
  rw [hlast]
  congr 1
  have hca : (c - a).toNat = c - a := Int.toNat_of_nonneg h
  omega



/-- Y-coordinate upper bound at x = a + k: the y-coordinate is at most heights[k].val + 1.

    This captures the key property that at x-coordinate a + k (after k east steps),
    the path has not yet passed the k-th east step height. The east step at position k
    happens at y = heights[k].val + 1, so any vertex at x = a + k has y ≤ heights[k].val + 1.

    This is used in the surjectivity proof to show that paths with column-strict heights
    cannot share vertices. -/
private lemma buildVertices_y_upper_bound_at_x (a c : ℤ) (N : ℕ) (heights : List (Fin N))
    (_hN : 0 < N) (hlen : heights.length = (c - a).toNat) (_h : 0 ≤ c - a)
    (hchain : heights.IsChain (· ≤ ·))
    (idx : ℕ) (hidx : idx < (buildVertices a c N heights).length)
    (k : ℕ) (hk : k < heights.length)
    (hx_eq : (buildVertices a c N heights)[idx].1 = a + k) :
    (buildVertices a c N heights)[idx].2 ≤ (heights[k]).val + 1 := by
  simp only [buildVertices] at hidx hx_eq ⊢
  have hfuel : (c - a).toNat + N ≥ heights.length + (N - (1 : ℤ).toNat) := by
    simp only [hlen, Int.toNat_one]; omega
  have hbounds : ∀ h ∈ heights, (1 : ℤ) ≤ (h.val : ℤ) + 1 := by
    intro h _; omega
  exact buildVerticesAux_y_upper_bound N a 1 heights ((c - a).toNat + N)
    hfuel (by omega) (by omega) hchain hbounds idx hidx k hk hx_eq


/-- Y-coordinate lower bound at x = a + k for k > 0: the y-coordinate is at least heights[k-1].val + 1.

    This captures the key property that at x-coordinate a + k (after k east steps),
    the path has already passed the (k-1)-th east step height. The east step at position k-1
    happens at y = heights[k-1].val + 1, so any vertex at x = a + k has y ≥ heights[k-1].val + 1.

    This is used in the surjectivity proof to show that paths with column-strict heights
    cannot share vertices. -/
private lemma buildVertices_y_lower_bound_at_x (a c : ℤ) (N : ℕ) (heights : List (Fin N))
    (_hN : 0 < N) (hlen : heights.length = (c - a).toNat) (_h : 0 ≤ c - a)
    (hchain : heights.IsChain (· ≤ ·))
    (idx : ℕ) (hidx : idx < (buildVertices a c N heights).length)
    (k : ℕ) (hk : k < heights.length) (hk_pos : 0 < k)
    (hx_eq : (buildVertices a c N heights)[idx].1 = a + k) :
    (buildVertices a c N heights)[idx].2 ≥ (heights[k - 1]).val + 1 := by
  simp only [buildVertices] at hidx hx_eq ⊢
  have hfuel : (c - a).toNat + N ≥ heights.length + (N - (1 : ℤ).toNat) := by
    simp only [hlen, Int.toNat_one]; omega
  have hbounds : ∀ h ∈ heights, (1 : ℤ) ≤ (h.val : ℤ) + 1 := by
    intro h _; omega
  exact buildVerticesAux_y_lower_bound N a 1 heights ((c - a).toNat + N)
    hfuel (by omega) (by omega) hchain hbounds idx hidx k hk hk_pos hx_eq

/-- Y-coordinate lower bound at x = a + heights.length (last column): y ≥ heights[last] + 1.

    At the last column (after all east steps), the y-coordinate is at least the last
    east-step height plus 1. This is because the last east step happens at y = heights[last] + 1,
    and after that we only go north.

    This complements `buildVertices_y_lower_bound_at_x` which handles k < heights.length. -/
private lemma buildVertices_y_lower_bound_at_last_column (a c : ℤ) (N : ℕ) (heights : List (Fin N))
    (hN : 0 < N) (hlen : heights.length = (c - a).toNat) (_h : 0 ≤ c - a)
    (hchain : heights.IsChain (· ≤ ·))
    (hlen_pos : 0 < heights.length)
    (idx : ℕ) (hidx : idx < (buildVertices a c N heights).length)
    (hx_eq : (buildVertices a c N heights)[idx].1 = a + heights.length) :
    (buildVertices a c N heights)[idx].2 ≥ (heights[heights.length - 1]).val + 1 := by
  -- At x = a + heights.length, all east steps have been consumed.
  -- The y-coordinate is at least heights[last] + 1.
  -- This follows from buildVertices_y_lower_bound_at_x with k = heights.length - 1 + 1 = heights.length
  -- But that lemma requires k < heights.length, so we need a different approach.
  --
  -- Alternative: use the fact that at the last column, we've made heights.length east steps,
  -- so we're at or past the last east-step height.
  --
  -- The proof uses buildVertices_y_lower_bound_at_x for k = heights.length - 1 < heights.length,
  -- noting that at x = a + heights.length, we must have passed through x = a + (heights.length - 1) + 1.
  -- At that point, y ≥ heights[heights.length - 2] + 1 (if heights.length > 1).
  -- But we need y ≥ heights[heights.length - 1] + 1.
  --
  -- Actually, the key is that at x = a + k, the y-coordinate is at least heights[k-1] + 1.
  -- At x = a + heights.length = a + (heights.length - 1) + 1, this gives y ≥ heights[heights.length - 2] + 1.
  -- But we need heights[heights.length - 1] + 1.
  --
  -- The correct approach: after the last east step (at x = a + heights.length - 1 → a + heights.length),
  -- the y-coordinate is exactly heights[heights.length - 1] + 1. After that, we only go north,
  -- so any vertex at x = a + heights.length has y ≥ heights[heights.length - 1] + 1.
  --
  -- We prove this by induction on the buildVerticesAux structure.
  simp only [buildVertices] at hidx hx_eq ⊢
  -- We need to show that at x = a + heights.length, y ≥ heights[last] + 1
  -- This follows from the structure of buildVerticesAux: when heights is empty,
  -- we only go north, so y is preserved or increased.
  -- The last east step sets y = heights[last] + 1, so after that y ≥ heights[last] + 1.
  have hfuel : (c - a).toNat + N ≥ heights.length + (N - (1 : ℤ).toNat) := by
    simp only [hlen, Int.toNat_one]; omega
  -- Use the fact that at x = a + heights.length, all heights have been consumed
  -- and y ≥ heights[last] + 1 from the last east step
  have key : ∀ (x y : ℤ) (heights' : List (Fin N)) (fuel : ℕ)
      (hfuel' : fuel ≥ heights'.length + (N - y.toNat))
      (hy : 1 ≤ y) (hyN : y ≤ N)
      (hchain' : heights'.IsChain (· ≤ ·))
      (hbounds : ∀ h' ∈ heights', y ≤ (h'.val : ℤ) + 1)
      (idx' : ℕ) (hidx' : idx' < (buildVerticesAux N x y heights' fuel).length)
      (hx_eq' : (buildVerticesAux N x y heights' fuel)[idx'].1 = x + heights'.length)
      (hlen_pos' : heights'.length > 0),
      (buildVerticesAux N x y heights' fuel)[idx'].2 ≥ (heights'[heights'.length - 1]'(by omega)).val + 1 := by
    intro x' y' heights' fuel hfuel' hy hyN hchain' hbounds idx' hidx' hx_eq' hlen_pos'
    induction fuel generalizing x' y' heights' idx' with
    | zero =>
      simp only [buildVerticesAux, List.length_singleton] at hidx'
      have hidx_eq : idx' = 0 := by omega
      subst hidx_eq
      simp only [buildVerticesAux, List.getElem_singleton] at hx_eq'
      -- x' = x' + heights'.length implies heights'.length = 0, contradicting hlen_pos'
      omega
    | succ n ih =>
      cases heights' with
      | nil => simp at hlen_pos'
      | cons h rest =>
        simp only [buildVerticesAux] at hidx' hx_eq' ⊢
        split_ifs at hidx' hx_eq' ⊢ with hy_lt
        · -- North case: y' < h.val + 1
          cases idx' with
          | zero =>
            simp only [List.getElem_cons_zero] at hx_eq'
            -- x' = x' + (h :: rest).length implies (h :: rest).length = 0, contradiction
            simp only [List.length_cons] at hx_eq'
            omega
          | succ idx'' =>
            simp only [List.length_cons] at hidx'
            have hidx'' : idx'' < (buildVerticesAux N x' (y' + 1) (h :: rest) n).length := by omega
            simp only [List.getElem_cons_succ] at hx_eq' ⊢
            have hfuel'' : n ≥ (h :: rest).length + (N - (y' + 1).toNat) := by
              simp only [List.length_cons] at hfuel' ⊢
              have hy_pos : 0 ≤ y' := by omega
              have h1 : (y' + 1).toNat = y'.toNat + 1 := by omega
              rw [h1]
              have hle : y'.toNat < N := by
                have hh := h.isLt
                have hthis : y' < N := by omega
                have htonat : (y'.toNat : ℤ) = y' := Int.toNat_of_nonneg hy_pos
                omega
              omega
            have hbounds' : ∀ h' ∈ (h :: rest), (y' + 1) ≤ (h'.val : ℤ) + 1 := by
              intro h' hmem
              cases List.mem_cons.mp hmem with
              | inl heq => subst heq; omega
              | inr hrest =>
                have hrel : h ≤ h' := hchain'.rel_cons hrest
                have hval : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
                omega
            have hyN' : y' + 1 ≤ N := by
              have hh := h.isLt
              have hb := hbounds h List.mem_cons_self
              omega
            exact ih x' (y' + 1) (h :: rest) hfuel'' (by omega) hyN' hchain' hbounds' idx'' hidx'' hx_eq'
              (by simp only [List.length_cons]; omega)
        · -- East case: y' ≥ h.val + 1
          have hy_eq : y' = (h.val : ℤ) + 1 := by
            have hb := hbounds h List.mem_cons_self
            omega
          cases idx' with
          | zero =>
            simp only [List.getElem_cons_zero] at hx_eq'
            -- x' = x' + (h :: rest).length implies (h :: rest).length = 0, contradiction
            simp only [List.length_cons] at hx_eq'
            omega
          | succ idx'' =>
            simp only [List.length_cons] at hidx'
            have hidx'' : idx'' < (buildVerticesAux N (x' + 1) y' rest n).length := by omega
            simp only [List.getElem_cons_succ] at hx_eq' ⊢
            -- After east step, we're at x' + 1 with rest heights
            -- rest.length = (h :: rest).length - 1
            have hrest_len : rest.length = (h :: rest).length - 1 := by simp
            -- At x' + 1 + rest.length = x' + (h :: rest).length
            have hx_eq'' : (buildVerticesAux N (x' + 1) y' rest n)[idx''].1 = (x' + 1) + rest.length := by
              simp only [List.length_cons] at hx_eq'
              have h1 : (x' : ℤ) + (rest.length + 1) = (x' + 1) + rest.length := by ring
              omega
            cases rest with
            | nil =>
              -- rest is empty, so we're at the last column
              -- The y-coordinate is y' = h.val + 1 = heights[0].val + 1
              simp only [List.length_nil] at hx_eq''
              have hy_ge := buildVerticesAux_y_ge N (x' + 1) y' [] n idx'' hidx''
              simp only [List.length_cons, List.length_nil]
              calc (h.val : ℤ) + 1 = y' := by omega
                _ ≤ (buildVerticesAux N (x' + 1) y' [] n)[idx''].2 := hy_ge
            | cons h' rest' =>
              -- rest is non-empty, apply IH
              have hfuel'' : n ≥ (h' :: rest').length + (N - y'.toNat) := by
                simp only [List.length_cons] at hfuel' ⊢
                omega
              have hchain'' : (h' :: rest').IsChain (· ≤ ·) := hchain'.tail
              have hbounds'' : ∀ h'' ∈ (h' :: rest'), y' ≤ (h''.val : ℤ) + 1 := by
                intro h'' hmem
                -- h'' ∈ h' :: rest' means h'' ∈ rest (since rest = h' :: rest')
                -- hchain' is for h :: rest = h :: h' :: rest'
                -- We need h ≤ h'' which follows from hchain'.rel_cons
                have hmem' : h'' ∈ (h :: h' :: rest') := List.mem_cons_of_mem h hmem
                have hrel : h ≤ h'' := hchain'.rel_cons hmem
                have hval : (h.val : ℤ) ≤ h''.val := Int.ofNat_le.mpr hrel
                omega
              have ih_result := ih (x' + 1) y' (h' :: rest') hfuel'' (by omega) (by omega) hchain'' hbounds''
                idx'' hidx'' hx_eq'' (by simp only [List.length_cons]; omega)
              -- ih_result says y ≥ (h' :: rest')[last].val + 1
              -- We need y ≥ (h :: h' :: rest')[last].val + 1 = (h' :: rest')[last].val + 1
              simp only [List.length_cons, Nat.add_one_sub_one] at ih_result ⊢
              exact ih_result
  have hbounds : ∀ h' ∈ heights, (1 : ℤ) ≤ (h'.val : ℤ) + 1 := fun _ _ => by omega
  exact key a 1 heights ((c - a).toNat + N) hfuel (by omega) (by omega) hchain hbounds idx hidx hx_eq hlen_pos


/-- Helper: pathWeightAux with jacobiTrudiArcWeight equals the product over lgvPathEastStepYCoords.

    This is the key lemma relating the arc-based weight computation to the east-step height list.
    For each east-step at y-coordinate y (where 1 ≤ y ≤ N), the arc weight is X_{(y-1).toNat}.
    North-steps have weight 1 and don't contribute to the product.

    The proof proceeds by induction on the vertex list:
    - Base case: single vertex has weight 1 and no east-steps
    - Inductive case: for v₀ :: v₁ :: rest, the first arc is either:
      * East-step: contributes X_{v₀.2 - 1} to weight and v₀.2 to lgvPathEastStepYCoords
      * North-step: contributes 1 to weight and nothing to lgvPathEastStepYCoords

    The induction hypothesis applies to the tail (v₁ :: rest). -/
private lemma pathWeightAux_eq_prod_eastStepYCoords (vertices : List (ℤ × ℤ))
    (h_ne : vertices ≠ [])
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (h_bounded : ∀ y ∈ lgvPathEastStepYCoords vertices, 1 ≤ y ∧ y ≤ N) :
    LGV.pathWeightAux (jacobiTrudiArcWeight (N := N) (R := R)) vertices h_arcs =
    ((lgvPathEastStepYCoords vertices).pmap
      (fun y hy => MvPolynomial.X (R := R)
        (⟨(y - 1).toNat, by have := h_bounded y hy; omega⟩ : Fin N))
      (fun _ hy => hy)).prod := by
  -- Proof by induction on the vertex list structure
  -- For each east-step at height y, jacobiTrudiArcWeight gives X_{y-1}
  -- For north-steps, the weight is 1
  -- lgvPathEastStepYCoords collects exactly the east-step heights
  induction vertices with
  | nil => exact absurd rfl h_ne
  | cons v₀ vs ih =>
    cases vs with
    | nil =>
      simp only [LGV.pathWeightAux, lgvPathEastStepYCoords, List.pmap, List.prod_nil]
    | cons v₁ rest =>
      have h_arc : LGV.integerLattice.arc v₀ v₁ := by
        have := h_arcs 0 (by simp : 0 + 1 < (v₀ :: v₁ :: rest).length)
        simp at this
        exact this
      have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
          LGV.integerLattice.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
            ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
        have := h_arcs (i + 1) hi'
        simp at this ⊢
        exact this
      have h_ne' : v₁ :: rest ≠ [] := List.cons_ne_nil v₁ rest

      simp only [LGV.integerLattice] at h_arc
      rcases h_arc with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · -- East-step case: v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2
        simp only [lgvPathEastStepYCoords, hx, hy, and_self, ↓reduceIte]
        simp only [LGV.pathWeightAux]
        simp only [jacobiTrudiArcWeight, hx, hy, and_self, ↓reduceIte]

        have h_bounded' : ∀ y ∈ lgvPathEastStepYCoords (v₁ :: rest), 1 ≤ y ∧ y ≤ N := by
          intro y hy'
          apply h_bounded y
          simp only [lgvPathEastStepYCoords, hx, hy, and_self, ↓reduceIte]
          exact List.mem_cons_of_mem _ hy'

        have h_v0_bounded : 1 ≤ v₀.2 ∧ v₀.2 ≤ N := by
          apply h_bounded v₀.2
          simp only [lgvPathEastStepYCoords, hx, hy, and_self, ↓reduceIte]
          exact List.mem_cons_self

        simp only [h_v0_bounded]

        have ih' := ih h_ne' h_arcs' h_bounded'

        simp only [List.pmap, List.prod_cons]
        congr 1
        rw [ih']
        congr 1
        apply List.pmap_congr_left
        intro x hx hx' h₂
        rfl

      · -- North-step case: v₁.1 = v₀.1 ∧ v₁.2 = v₀.2 + 1
        have h_not_east : ¬(v₁.1 = v₀.1 + 1 ∧ v₁.2 = v₀.2) := by omega
        have heq : lgvPathEastStepYCoords (v₀ :: v₁ :: rest) = lgvPathEastStepYCoords (v₁ :: rest) := by
          simp only [lgvPathEastStepYCoords, h_not_east, ↓reduceIte]
        
        simp only [LGV.pathWeightAux, jacobiTrudiArcWeight, h_not_east, ↓reduceIte, one_mul]
        
        have h_bounded' : ∀ y ∈ lgvPathEastStepYCoords (v₁ :: rest), 1 ≤ y ∧ y ≤ N := by
          intro y hy'
          apply h_bounded y
          rw [heq]
          exact hy'

        have ih' := ih h_ne' h_arcs' h_bounded'
        rw [ih']
        congr 1
        simp only [heq]
        -- The two sides are definitionally equal, but have different proof terms
        -- Use proof irrelevance via List.pmap_congr_left
        apply List.pmap_congr_left
        intro x hx hx' h₂
        rfl

/-- Helper lemma: pathWeightAux with jacobiTrudiArcWeight equals the product over
    lgvPathEastStepYCoords converted to Fin N.

    This is the key lemma relating the arc-based weight computation to the east-step height list.
    For each east-step at y-coordinate y (where 1 ≤ y ≤ N), the arc weight is X_{(y-1).toNat}.
    North-steps have weight 1 and don't contribute to the product. -/
private lemma pathWeightAux_eq_map_prod_lgvYCoords (vertices : List (ℤ × ℤ))
    (h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      LGV.integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vertices.get ⟨i + 1, hi⟩))
    (h_bounded : ∀ y ∈ lgvPathEastStepYCoords vertices, 1 ≤ y ∧ y ≤ N) :
    LGV.pathWeightAux (jacobiTrudiArcWeight (N := N) (R := R)) vertices h_arcs =
    (List.map (fun j => X j) (lgvYCoordsToFinN (lgvPathEastStepYCoords vertices) h_bounded)).prod := by
  induction vertices with
  | nil =>
    simp [LGV.pathWeightAux, lgvPathEastStepYCoords, lgvYCoordsToFinN]
  | cons v vs ih =>
    cases vs with
    | nil =>
      simp [LGV.pathWeightAux, lgvPathEastStepYCoords, lgvYCoordsToFinN]
    | cons v' rest =>
      simp only [LGV.pathWeightAux, lgvPathEastStepYCoords]
      have h_arc : LGV.integerLattice.arc v v' := by
        have := h_arcs 0 (by simp : 0 + 1 < (v :: v' :: rest).length)
        simp at this
        exact this
      rcases h_arc with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · -- East-step case: v'.1 = v.1 + 1, v'.2 = v.2
        have heast : v'.1 = v.1 + 1 ∧ v'.2 = v.2 := ⟨hx, hy⟩
        simp only [heast, and_self, ↓reduceIte]
        simp only [lgvYCoordsToFinN, List.pmap, List.map]
        rw [List.prod_cons]
        -- Prepare the induction hypothesis arguments
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v' :: rest).length,
            LGV.integerLattice.arc ((v' :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v' :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v :: v' :: rest).length := by simp at hi ⊢; omega
          have := h_arcs (i + 1) hi'
          simp at this ⊢
          exact this
        have h_bounded' : ∀ y ∈ lgvPathEastStepYCoords (v' :: rest), 1 ≤ y ∧ y ≤ N := by
          intro y hy
          apply h_bounded y
          simp only [lgvPathEastStepYCoords, heast, and_self, ↓reduceIte, List.mem_cons]
          right
          exact hy
        -- Show the first factors are equal
        have hv2_bounded : 1 ≤ v.2 ∧ v.2 ≤ N := by
          apply h_bounded v.2
          simp [lgvPathEastStepYCoords, heast]
        have hfirst : jacobiTrudiArcWeight (N := N) (R := R) v v' (Or.inl heast) =
            X ⟨(v.2 - 1).toNat, by have := hv2_bounded; omega⟩ := by
          unfold jacobiTrudiArcWeight
          simp only [heast, and_self, ↓reduceIte, hv2_bounded, dif_pos]
        -- The goal is: jacobiTrudiArcWeight * pathWeightAux = X * (map X pmap).prod
        -- Use hfirst for the first factor
        rw [hfirst]
        -- Now goal is: X * pathWeightAux = X * (map X pmap).prod
        -- Show the second factors are equal using IH
        rw [ih h_arcs' h_bounded']
        -- Now goal is: X * (map X (lgvYCoordsToFinN ...)).prod = X * (map X pmap).prod
        -- The two pmap expressions differ only in proof arguments
        simp only [lgvYCoordsToFinN]
        -- The two sides differ in the proof argument to pmap, but produce the same Fin N values
        -- Use List.map_pmap to convert to a form where we can use congr
        rw [List.map_pmap, List.map_pmap]
        -- Now both sides are pmap of (fun y _ => X ⟨(y-1).toNat, _⟩)
        -- The function doesn't use the proof, so the results are equal
        -- The two pmaps have the same underlying list and produce the same values
        -- because the Fin N constructor only depends on (y-1).toNat, not on the proof
        -- Goal: X _ * (pmap f l h₁).prod = X _ * (pmap f l h₂).prod
        -- The first factors are equal (both are X ⟨(v.2 - 1).toNat, _⟩)
        -- The second factors are equal because the pmaps produce the same list
        apply congrArg₂ (· * ·) rfl
        apply congrArg List.prod
        apply List.ext_getElem (by simp [List.length_pmap])
        intro i h1 h2
        simp only [List.getElem_pmap]
      · -- North-step case: v'.1 = v.1, v'.2 = v.2 + 1
        have hnorth : ¬(v'.1 = v.1 + 1 ∧ v'.2 = v.2) := by omega
        simp only [hnorth, ↓reduceIte]
        -- For north-step, jacobiTrudiArcWeight = 1
        have hw1 : jacobiTrudiArcWeight (N := N) (R := R) v v' (Or.inr ⟨hx, hy⟩) = 1 := by
          unfold jacobiTrudiArcWeight
          simp only [hnorth, ↓reduceIte]
        rw [hw1, one_mul]
        -- Use IH
        have h_arcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v' :: rest).length,
            LGV.integerLattice.arc ((v' :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩)
              ((v' :: rest).get ⟨i + 1, hi⟩) := by
          intro i hi
          have hi' : (i + 1) + 1 < (v :: v' :: rest).length := by simp at hi ⊢; omega
          have := h_arcs (i + 1) hi'
          simp at this ⊢
          exact this
        have h_bounded' : ∀ y ∈ lgvPathEastStepYCoords (v' :: rest), 1 ≤ y ∧ y ≤ N := by
          intro y hy
          apply h_bounded y
          simp only [lgvPathEastStepYCoords, hnorth, ↓reduceIte]
          exact hy
        rw [ih h_arcs' h_bounded']

theorem lgvPathToLatticePath_weight_eq (a c : ℤ) (p : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hstart : p.start = (a, 1)) (hfinish : p.finish = (c, (N : ℤ))) :
    LGV.pathWeight (jacobiTrudiArcWeight (N := N) (R := R)) p =
    (lgvPathToLatticePath a c p hstart hfinish).weight (R := R) := by
  unfold LGV.pathWeight lgvPathToLatticePath LatticePath.weight
  simp only
  -- Apply the helper lemma
  apply pathWeightAux_eq_map_prod_lgvYCoords

/-- Helper: buildVerticesAux always starts with (x, y). -/
private lemma buildVerticesAux_head' (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ) :
    ∃ tail, buildVerticesAux N x y heights fuel = (x, y) :: tail := by
  cases fuel with
  | zero => exact ⟨[], rfl⟩
  | succ n =>
    cases heights with
    | nil =>
      simp only [buildVerticesAux]
      split_ifs with h
      · exact ⟨buildVerticesAux N x (y + 1) [] n, rfl⟩
      · exact ⟨[], rfl⟩
    | cons h rest =>
      simp only [buildVerticesAux]
      split_ifs with hlt
      · exact ⟨buildVerticesAux N x (y + 1) (h :: rest) n, rfl⟩
      · exact ⟨buildVerticesAux N (x + 1) y rest n, rfl⟩

/-- Helper for lgvPathEastStepYCoords when we know the next vertex is a north step. -/
private lemma lgvPathEastStepYCoords_cons_north_gen (x y : ℤ) (tail : List (ℤ × ℤ))
    (hhead : ∃ tail', tail = (x, y + 1) :: tail') :
    lgvPathEastStepYCoords ((x, y) :: tail) = lgvPathEastStepYCoords tail := by
  obtain ⟨tail', heq⟩ := hhead
  subst heq
  simp only [lgvPathEastStepYCoords]
  have h : ¬(x = x + 1 ∧ y + 1 = y) := by omega
  simp only [h, ↓reduceIte]

/-- Helper for lgvPathEastStepYCoords when we know the next vertex is an east step. -/
private lemma lgvPathEastStepYCoords_cons_east_gen (x y : ℤ) (tail : List (ℤ × ℤ))
    (hhead : ∃ tail', tail = (x + 1, y) :: tail') :
    lgvPathEastStepYCoords ((x, y) :: tail) = y :: lgvPathEastStepYCoords tail := by
  obtain ⟨tail', heq⟩ := hhead
  subst heq
  simp only [lgvPathEastStepYCoords]
  simp only [and_self, ↓reduceIte]

/-- Main induction lemma: lgvPathEastStepYCoords extracts the heights from buildVerticesAux. -/
private lemma lgvPathEastStepYCoords_buildVerticesAux (N : ℕ) (x y : ℤ) (heights : List (Fin N)) (fuel : ℕ)
    (hfuel : fuel ≥ heights.length + (N - y.toNat)) (hy : 1 ≤ y) (hyN : y ≤ N)
    (hchain : heights.IsChain (· ≤ ·))
    (hbounds : ∀ h ∈ heights, y ≤ (h.val : ℤ) + 1) :
    lgvPathEastStepYCoords (buildVerticesAux N x y heights fuel) =
      heights.map (fun h => (h.val : ℤ) + 1) := by
  induction fuel generalizing x y heights with
  | zero =>
    simp only [buildVerticesAux, lgvPathEastStepYCoords]
    have hlen : heights.length = 0 := by omega
    cases heights with
    | nil => rfl
    | cons _ _ => simp at hlen
  | succ n ih =>
    cases heights with
    | nil =>
      simp only [List.map_nil]
      by_cases hy_lt : y < (N : ℤ)
      · simp only [buildVerticesAux, hy_lt, ↓reduceIte]
        have hhead := buildVerticesAux_head' N x (y + 1) [] n
        rw [lgvPathEastStepYCoords_cons_north_gen x y _ hhead]
        -- Apply IH
        have hy_pos : 0 ≤ y := by omega
        have h1 : (y + 1).toNat = y.toNat + 1 := by
          have := Int.toNat_of_nonneg hy_pos; omega
        have hfuel' : n ≥ ([] : List (Fin N)).length + (N - (y + 1).toNat) := by
          simp only [List.length_nil, zero_add] at hfuel ⊢
          rw [h1]; omega
        exact ih x (y + 1) [] hfuel' (by omega) (by omega) List.isChain_nil (by simp)
      · simp only [buildVerticesAux, hy_lt, ↓reduceIte, lgvPathEastStepYCoords]
    | cons h rest =>
      by_cases hy_lt : y < (h.val : ℤ) + 1
      · -- North step case
        simp only [buildVerticesAux, hy_lt, ↓reduceIte]
        have hhead := buildVerticesAux_head' N x (y + 1) (h :: rest) n
        rw [lgvPathEastStepYCoords_cons_north_gen x y _ hhead]
        -- Apply IH
        have hy_pos : 0 ≤ y := by omega
        have h1 : (y + 1).toNat = y.toNat + 1 := by
          have := Int.toNat_of_nonneg hy_pos; omega
        have hfuel' : n ≥ (h :: rest).length + (N - (y + 1).toNat) := by
          simp only [List.length_cons] at hfuel ⊢
          rw [h1]
          have hle : y.toNat < N := by
            have hh := h.isLt
            have : y < N := by omega
            have htonat : (y.toNat : ℤ) = y := Int.toNat_of_nonneg hy_pos
            omega
          omega
        have hbounds' : ∀ h' ∈ (h :: rest), (y + 1) ≤ (h'.val : ℤ) + 1 := by
          intro h' hmem
          cases List.mem_cons.mp hmem with
          | inl heq => subst heq; omega
          | inr hrest =>
            have hrel : h ≤ h' := hchain.rel_cons hrest
            have : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
            omega
        have hyN' : y + 1 ≤ N := by have hh := h.isLt; omega
        exact ih x (y + 1) (h :: rest) hfuel' (by omega) hyN' hchain hbounds'
      · -- East step case: y ≥ h.val + 1
        simp only [buildVerticesAux, hy_lt, ↓reduceIte]
        have hhead := buildVerticesAux_head' N (x + 1) y rest n
        rw [lgvPathEastStepYCoords_cons_east_gen x y _ hhead]
        simp only [List.map_cons]
        have hy_eq : y = (h.val : ℤ) + 1 := by
          have hb := hbounds h List.mem_cons_self
          omega
        rw [hy_eq]
        congr 1
        -- Apply IH for rest
        have hfuel' : n ≥ rest.length + (N - y.toNat) := by
          simp only [List.length_cons] at hfuel
          omega
        have hchain' : rest.IsChain (· ≤ ·) := hchain.tail
        have hbounds' : ∀ h' ∈ rest, y ≤ (h'.val : ℤ) + 1 := by
          intro h' hmem
          have hrel : h ≤ h' := hchain.rel_cons hmem
          have h_ge : (h.val : ℤ) ≤ h'.val := Int.ofNat_le.mpr hrel
          have hb := hbounds h List.mem_cons_self
          omega
        rw [← hy_eq]
        exact ih (x + 1) y rest hfuel' hy hyN hchain' hbounds'

/-- Key lemma for surjectivity: the east-step y-coordinates of buildVertices equal
    the input heights shifted by 1.

    This is the inverse direction of the lgvPathToLatticePath bijection:
    building an LGV path from a LatticePath's heights and extracting the heights back
    gives the original heights.

    The proof requires showing that buildVerticesAux produces east-steps exactly at
    the heights h.val + 1 for each h in the input list. -/
private lemma lgvPathEastStepYCoords_buildVertices (a c : ℤ) (heights : List (Fin N))
    (_hN : 0 < N) (hlen : heights.length = (c - a).toNat) (_h : 0 ≤ c - a)
    (hchain : heights.IsChain (· ≤ ·)) :
    lgvPathEastStepYCoords (buildVertices a c N heights) =
      heights.map (fun h => (h.val : ℤ) + 1) := by
  -- Apply the auxiliary lemma with appropriate parameters
  unfold buildVertices
  apply lgvPathEastStepYCoords_buildVerticesAux
  · -- hfuel: (c - a).toNat + N ≥ heights.length + (N - 1.toNat)
    simp only [Int.toNat_one]
    rw [hlen]
    omega
  · -- hy: 1 ≤ 1
    omega
  · -- hyN: 1 ≤ N
    omega
  · -- hchain
    exact hchain
  · -- hbounds: all heights have h.val ≥ 0, so 1 ≤ h.val + 1
    intro h' _
    have hh := h'.isLt
    omega

/-- The LGV path weight sum equals the LatticePath weight sum.
    This is proved using lgvPathToLatticePath as a bijection.

    The proof establishes that lgvPathToLatticePath is a bijection by showing:
    1. Injectivity: paths with the same east-step heights are equal
    2. Surjectivity: every LatticePath corresponds to an LGV path
    3. Weight preservation: lgvPathToLatticePath_weight_eq

    The bijection works because:
    - A path from (a, 1) to (c, N) is uniquely determined by its east-step heights
    - East-step heights form a weakly increasing sequence of length (c - a)
    - This is exactly the data in a LatticePath -/
theorem lgv_pathWeightSum_eq_latticePathSum (a c : ℤ) (h : 0 ≤ c - a) (hN : 0 < N) :
    LGV.pathWeightSum LGV.integerLattice_pathFinite (jacobiTrudiArcWeight (N := N) (R := R))
      (a, 1) (c, (N : ℤ)) = ∑ lp : LatticePath (N := N) a c, lp.weight (R := R) := by
  -- Both sides are sums over equivalent combinatorial objects.
  -- We use Finset.sum_bij with lgvPathToLatticePath.
  unfold LGV.pathWeightSum
  apply Finset.sum_bij
    (i := fun p hp => lgvPathToLatticePath a c p
      (by simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp; exact hp.1)
      (by simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp; exact hp.2))
    (hi := fun _ _ => Finset.mem_univ _)
    (i_inj := fun p₁ hp₁ p₂ hp₂ heq => by
        -- Injectivity: Use lgvPathToLatticePath_injective
        simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp₁ hp₂
        exact lgvPathToLatticePath_injective a c p₁ p₂ hp₁.1 hp₁.2 hp₂.1 hp₂.2 heq)
    (i_surj := fun lp _ => by
      -- Surjectivity: every LatticePath comes from some LGV path
      -- We construct the LGV path from lp.eastStepHeights using buildVertices.
      let vertices := buildVertices a c N lp.eastStepHeights
      have hne := buildVertices_nonempty a c N lp.eastStepHeights
      have harcs := buildVertices_arcs_valid a c N lp.eastStepHeights hN lp.length_eq h
      have hstart := buildVertices_head a c N lp.eastStepHeights hN
      have hfinish := buildVertices_getLast a c N lp.eastStepHeights hN lp.length_eq h lp.weaklyIncreasing
      -- Construct the path
      let p : LGV.SimpleDigraph.Path LGV.integerLattice := ⟨vertices, hne, harcs⟩
      use p
      -- Goal is: p ∈ pathsFromTo ∧ lgvPathToLatticePath p = lp
      refine ⟨?_, ?_⟩
      · -- Show p is in pathsFromTo
        simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        exact ⟨hstart, hfinish⟩
      · -- Show lgvPathToLatticePath p = lp
        -- Use lgvPathEastStepYCoords_buildVertices to show the east-step heights match
        apply LatticePath.ext
        simp only [lgvPathToLatticePath]
        -- Need to show: lgvYCoordsToFinN (lgvPathEastStepYCoords vertices) h' = lp.eastStepHeights
        -- where vertices = buildVertices a c N lp.eastStepHeights
        -- By lgvPathEastStepYCoords_buildVertices:
        --   lgvPathEastStepYCoords vertices = lp.eastStepHeights.map (fun h => h.val + 1)
        -- Then lgvYCoordsToFinN converts back to lp.eastStepHeights
        have heq := lgvPathEastStepYCoords_buildVertices a c lp.eastStepHeights hN lp.length_eq h lp.weaklyIncreasing
        -- Use lgvYCoordsToFinN_map_val_add_one_eq to complete the proof
        exact lgvYCoordsToFinN_map_val_add_one_eq lp.eastStepHeights heq _)
    (h := fun p hp => by
      simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
      exact lgvPathToLatticePath_weight_eq a c p hp.1 hp.2)

/-- Key infrastructure lemma: The LGV path weight sum from (a, 1) to (c, N) with
    jacobiTrudiArcWeight equals hsymmExt(c - a).

    This connects the LGV framework (using SimpleDigraph.Path in integerLattice)
    to our LatticePath representation (using eastStepHeights).

    The proof uses lgv_pathWeightSum_eq_latticePathSum to establish a weight-preserving
    bijection between LGV paths and LatticePaths, then applies pathWeightSum_eq_hsymm.

    This is a key infrastructure lemma needed for det_jacobiTrudiMatrixH_eq_nipatSum. -/
theorem lgv_pathWeightSum_eq_hsymmExt (a c : ℤ) (hN : 0 < N) :
    LGV.pathWeightSum LGV.integerLattice_pathFinite (jacobiTrudiArcWeight (N := N) (R := R))
      (a, 1) (c, (N : ℤ)) = hsymmExt (N := N) (R := R) (c - a) := by
  by_cases h : 0 ≤ c - a
  · -- Case c - a ≥ 0: Use lgv_pathWeightSum_eq_latticePathSum and pathWeightSum_eq_hsymm
    rw [lgv_pathWeightSum_eq_latticePathSum a c h hN]
    have hpath := pathWeightSum_eq_hsymm (N := N) (R := R) a c
    unfold latticePathFinset at hpath
    simp only [h, ↓reduceIte] at hpath
    exact hpath
  · -- Case c - a < 0: both sides are 0
    push_neg at h
    unfold hsymmExt
    simp only [Int.not_le.mpr h, ↓reduceIte]
    unfold LGV.pathWeightSum
    have hempty : LGV.pathsFromTo LGV.integerLattice LGV.integerLattice_pathFinite
        (a, 1) (c, ↑N) = ∅ := by
      ext p
      simp only [LGV.pathsFromTo, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      constructor
      · intro ⟨hstart, hfinish⟩
        have hle : p.start.1 ≤ p.finish.1 := by
          have hne := p.nonempty
          have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil hne
          suffices ∀ i j : ℕ, (hi : i < p.vertices.length) → (hj : j < p.vertices.length) →
              i ≤ j → (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j, hj⟩).1 by
            have hlast : p.vertices.length - 1 < p.vertices.length :=
              Nat.sub_lt hlen Nat.one_pos
            have h := this 0 (p.vertices.length - 1) hlen hlast (Nat.zero_le _)
            simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at h ⊢
            convert h using 2 <;> simp [List.head_eq_getElem, List.getLast_eq_getElem]
          intro i j hi hj hij
          induction j with
          | zero => simp_all
          | succ k ih =>
            by_cases hik : i = k + 1
            · simp [hik]
            · have hik' : i ≤ k := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hij hik)
              have hk : k < p.vertices.length := Nat.lt_of_succ_lt hj
              have h1 := ih hk hik'
              have harc := p.arcs_valid k hj
              simp only [LGV.integerLattice] at harc
              rcases harc with ⟨hx, _⟩ | ⟨hx, _⟩
              · omega
              · omega
        rw [hstart, hfinish] at hle
        omega
      · intro hp
        simp at hp
    rw [hempty]
    simp

/-- The Jacobi-Trudi matrix is the transpose of the LGV path weight matrix.

    This is a key step in the proof of det_jacobiTrudiMatrixH_eq_nipatSum.
    The (i,j) entry of jacobiTrudiMatrixH is h_{λᵢ - μⱼ - i + j}, which equals
    the path weight sum from source A_j to target B_i. This is exactly the (j,i)
    entry of the path weight matrix, hence the transpose relationship.

    The proof uses lgv_pathWeightSum_eq_hsymmExt to connect the LGV path weight sum
    to hsymmExt, which is how jacobiTrudiMatrixH entries are defined. -/
theorem jacobiTrudiMatrixH_eq_pathWeightMatrix_transpose (lam mu : Fin N → ℕ) :
    jacobiTrudiMatrixH (R := R) lam mu =
      (LGV.pathWeightMatrix LGV.integerLattice_pathFinite
        (jacobiTrudiArcWeight (N := N) (R := R))
        (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam))ᵀ := by
  ext i j
  rw [jacobiTrudiMatrixH_eq_pathLength]
  simp only [Matrix.transpose_apply, LGV.pathWeightMatrix, Matrix.of_apply]
  simp only [jacobiTrudiSourceVertex, jacobiTrudiTargetVertex]
  -- Since i : Fin N exists, we have N > 0
  have hN : 0 < N := Fin.pos i
  rw [← lgv_pathWeightSum_eq_hsymmExt _ _ hN]

/-- Corollary: The determinant of jacobiTrudiMatrixH equals the determinant of the
    path weight matrix. This follows from det(Mᵀ) = det(M). -/
theorem det_jacobiTrudiMatrixH_eq_det_pathWeightMatrix (lam mu : Fin N → ℕ) :
    (jacobiTrudiMatrixH (R := R) lam mu).det =
      (LGV.pathWeightMatrix LGV.integerLattice_pathFinite
        (jacobiTrudiArcWeight (N := N) (R := R))
        (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam)).det := by
  rw [jacobiTrudiMatrixH_eq_pathWeightMatrix_transpose, Matrix.det_transpose]

/-!
### LGV-Nipat Bijection: PathTuple to Nipat Conversion

The following definitions and lemmas establish the conversion from LGV PathTuples
to our Nipat type. This is used to prove `lgv_nipatWeightSum_eq_nipatSum`.
-/

/-- Helper lemma: If two non-intersecting paths have one path above the other at some sum value,
    the upper path stays above at all subsequent sum values.

    This is a key lemma for proving column-strictness from non-intersection.
    The proof uses discrete IVT: if the y-difference ever becomes ≤ 0, there must be
    a point where it equals 0, meaning the paths share a vertex (contradiction). -/
private lemma path_above_stays_above (p p' : LGV.SimpleDigraph.Path LGV.integerLattice)
    (hni : ∀ v, v ∈ p.vertices → v ∉ p'.vertices)
    (s₀ : ℤ) -- the sum value (x + y) where p' is above p
    -- Indices for both paths at sum s₀
    (hs₀_p : s₀ ≥ p.start.1 + p.start.2)
    (hs₀_p' : s₀ ≥ p'.start.1 + p'.start.2)
    (hs₀_p_end : s₀ ≤ p.finish.1 + p.finish.2)
    (hs₀_p'_end : s₀ ≤ p'.finish.1 + p'.finish.2)
    -- p' is strictly above p at s₀
    (h_above : ∀ (hidx_p : (s₀ - p.start.1 - p.start.2).toNat < p.vertices.length)
               (hidx_p' : (s₀ - p'.start.1 - p'.start.2).toNat < p'.vertices.length),
               (p'.vertices.get ⟨(s₀ - p'.start.1 - p'.start.2).toNat, hidx_p'⟩).2 >
               (p.vertices.get ⟨(s₀ - p.start.1 - p.start.2).toNat, hidx_p⟩).2)
    -- A later sum value s₁
    (s₁ : ℤ) (hs₁ : s₁ ≥ s₀)
    (hs₁_p_end : s₁ ≤ p.finish.1 + p.finish.2)
    (hs₁_p'_end : s₁ ≤ p'.finish.1 + p'.finish.2) :
    ∀ (hidx_p : (s₁ - p.start.1 - p.start.2).toNat < p.vertices.length)
      (hidx_p' : (s₁ - p'.start.1 - p'.start.2).toNat < p'.vertices.length),
      (p'.vertices.get ⟨(s₁ - p'.start.1 - p'.start.2).toNat, hidx_p'⟩).2 >
      (p.vertices.get ⟨(s₁ - p.start.1 - p.start.2).toNat, hidx_p⟩).2 := by
  intro hidx_p hidx_p'
  -- Define the y-difference function: diff(s) = y_p'(s) - y_p(s)
  -- At s₀, diff > 0. If diff ever becomes ≤ 0, by discrete IVT there's a point where diff = 0,
  -- meaning both paths have the same (x, y), contradicting non-intersection.
  by_contra h_not_above
  push_neg at h_not_above
  -- Define y-coordinate functions for each path at a given sum value
  let y_p (s : ℤ) : ℤ :=
    let idx := (s - p.start.1 - p.start.2).toNat
    if h : idx < p.vertices.length then (p.vertices.get ⟨idx, h⟩).2 else 0
  let y_p' (s : ℤ) : ℤ :=
    let idx := (s - p'.start.1 - p'.start.2).toNat
    if h : idx < p'.vertices.length then (p'.vertices.get ⟨idx, h⟩).2 else 0
  let diff (s : ℤ) : ℤ := y_p' s - y_p s
  -- At s₀, diff > 0
  have hidx_p_s₀ : (s₀ - p.start.1 - p.start.2).toNat < p.vertices.length := by
    have hlen := LGV.integerLattice_path_length_eq p
    omega
  have hidx_p'_s₀ : (s₀ - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
    have hlen := LGV.integerLattice_path_length_eq p'
    omega
  have hdiff_s₀ : diff s₀ > 0 := by
    simp only [diff, y_p, y_p', hidx_p_s₀, hidx_p'_s₀, dite_true]
    exact sub_pos.mpr (h_above hidx_p_s₀ hidx_p'_s₀)
  -- At s₁, diff ≤ 0
  have hdiff_s₁ : diff s₁ ≤ 0 := by
    simp only [diff, y_p, y_p', hidx_p, hidx_p', dite_true]
    omega
  -- The difference function changes by at most 1 at each step
  have hdiff_step : ∀ s : ℤ, s₀ ≤ s → s < s₁ → |diff (s + 1) - diff s| ≤ 1 := by
    intro s hs_lo hs_hi
    simp only [diff, y_p, y_p']
    -- Both paths take steps of size 1 in y-coordinate
    have hs_p_lo : s ≥ p.start.1 + p.start.2 := le_trans hs₀_p hs_lo
    have hs_p_hi : s < p.finish.1 + p.finish.2 := by
      have := LGV.integerLattice_path_length_eq p
      omega
    have hs_p'_lo : s ≥ p'.start.1 + p'.start.2 := le_trans hs₀_p' hs_lo
    have hs_p'_hi : s < p'.finish.1 + p'.finish.2 := by
      have := LGV.integerLattice_path_length_eq p'
      omega
    have hidx_p_s : (s - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      omega
    have hidx_p'_s : (s - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      omega
    have hidx_p_s1 : (s + 1 - p.start.1 - p.start.2).toNat < p.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p
      omega
    have hidx_p'_s1 : (s + 1 - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
      have hlen := LGV.integerLattice_path_length_eq p'
      omega
    simp only [hidx_p_s, hidx_p'_s, hidx_p_s1, hidx_p'_s1, dite_true]
    -- The y-coordinate changes by 0 or 1 at each step
    have heq_idx_p : (s + 1 - p.start.1 - p.start.2).toNat = (s - p.start.1 - p.start.2).toNat + 1 := by omega
    have heq_idx_p' : (s + 1 - p'.start.1 - p'.start.2).toNat = (s - p'.start.1 - p'.start.2).toNat + 1 := by omega
    have hstep_p_idx : (s - p.start.1 - p.start.2).toNat + 1 < p.vertices.length := by omega
    have hstep_p'_idx : (s - p'.start.1 - p'.start.2).toNat + 1 < p'.vertices.length := by omega
    have harc_p := p.arcs_valid (s - p.start.1 - p.start.2).toNat hstep_p_idx
    have harc_p' := p'.arcs_valid (s - p'.start.1 - p'.start.2).toNat hstep_p'_idx
    -- Each arc changes y by 0 or 1
    rcases harc_p with ⟨_, hy_p⟩ | ⟨_, hy_p⟩ <;>
    rcases harc_p' with ⟨_, hy_p'⟩ | ⟨_, hy_p'⟩ <;>
    · simp only [heq_idx_p, heq_idx_p', abs_le]
      constructor <;> omega
  -- Apply discrete IVT to get a point where diff = 0
  have hs₀_le_s₁ : s₀ ≤ s₁ := hs₁
  obtain ⟨s_eq, hs_eq_lo, hs_eq_hi, hdiff_eq⟩ := LGV.discrete_ivt hs₀_le_s₁ diff hdiff_step (le_of_lt hdiff_s₀) hdiff_s₁
  -- At s_eq, both paths have the same y-coordinate
  have hidx_p_seq : (s_eq - p.start.1 - p.start.2).toNat < p.vertices.length := by
    have hlen := LGV.integerLattice_path_length_eq p
    omega
  have hidx_p'_seq : (s_eq - p'.start.1 - p'.start.2).toNat < p'.vertices.length := by
    have hlen := LGV.integerLattice_path_length_eq p'
    omega
  simp only [diff, y_p, y_p', hidx_p_seq, hidx_p'_seq, dite_true, sub_eq_zero] at hdiff_eq
  -- Both paths have the same sum value at s_eq, so same x + y = s_eq
  have hsum_p := LGV.integerLattice_path_vertex_sum p (s_eq - p.start.1 - p.start.2).toNat hidx_p_seq
  have hsum_p' := LGV.integerLattice_path_vertex_sum p' (s_eq - p'.start.1 - p'.start.2).toNat hidx_p'_seq
  -- Since x + y = s_eq for both, and y_p = y_p', we have x_p = x_p'
  -- So both paths visit the same vertex (x, y)
  have hx_eq : (p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩).1 =
               (p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩).1 := by
    omega
  have hy_eq : (p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩).2 =
               (p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩).2 := by
    omega
  -- The vertices are equal
  have hv_eq : p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩ =
               p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩ :=
    Prod.ext hx_eq hy_eq
  -- This contradicts non-intersection
  have hmem_p : p.vertices.get ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩ ∈ p.vertices :=
    List.get_mem p.vertices ⟨(s_eq - p.start.1 - p.start.2).toNat, hidx_p_seq⟩
  have hmem_p' : p'.vertices.get ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩ ∈ p'.vertices :=
    List.get_mem p'.vertices ⟨(s_eq - p'.start.1 - p'.start.2).toNat, hidx_p'_seq⟩
  rw [hv_eq] at hmem_p
  exact hni _ hmem_p hmem_p'

/-- Convert an LGV PathTuple to a tuple of LatticePaths.
    Each path is converted using lgvPathToLatticePath. -/
private noncomputable def pathTupleToLatticePaths (N : ℕ) (lam mu : Fin M → ℕ)
    (pt : LGV.PathTuple LGV.integerLattice M
      (jacobiTrudiSourceVertexRect mu) (jacobiTrudiTargetVertexRect N lam)) :
    (i : Fin M) → LatticePath (N := N)
      ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ)) :=
  fun i => lgvPathToLatticePath
    ((mu i : ℤ) - (i.val : ℤ))
    ((lam i : ℤ) - (i.val : ℤ))
    (pt.paths i)
    (by unfold jacobiTrudiSourceVertexRect at pt; exact pt.starts i)
    (by unfold jacobiTrudiTargetVertexRect at pt; exact pt.finishes i)

/-- Key lemma: Non-intersection of LGV paths implies column-strictness of the converted paths.

    This is the fundamental connection between the two representations:
    - LGV: paths don't share any vertex (isNonIntersecting)
    - Nipat: paths satisfy column-strictness (colStrictPaths)

    The proof uses the fact that for sorted source/target vertices:
    - If paths i < j share a vertex (x, y), they would have the same height at some column
    - This violates column-strictness which requires strict ordering

    **Proof sketch:**
    Suppose paths i and j (with i < j) share a vertex (x, y).
    - Path i goes from (μᵢ - i, 1) to (λᵢ - i, N)
    - Path j goes from (μⱼ - j, 1) to (λⱼ - j, N)
    - At x-coordinate x, both paths have y-coordinate y
    - The east-step at column k in path i (where μᵢ - i + k = x) has height y
    - The east-step at column k' in path j (where μⱼ - j + k' = x) has height y
    - If μᵢ + k = μⱼ + k' (same tableau column), then heights should be strictly ordered
    - But both have height y, contradiction -/
private lemma isNonIntersecting_implies_colStrictPaths (N : ℕ) (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i)
    (pt : LGV.PathTuple LGV.integerLattice M
      (jacobiTrudiSourceVertexRect mu) (jacobiTrudiTargetVertexRect N lam))
    (hni : pt.isNonIntersecting) :
    ∀ i j : Fin M, i < j →
      ∀ k : ℕ, ∀ hk : k < ((pathTupleToLatticePaths N lam mu pt) i).eastStepHeights.length,
      ∀ k' : ℕ, ∀ hk' : k' < ((pathTupleToLatticePaths N lam mu pt) j).eastStepHeights.length,
      mu i + k = mu j + k' →
      ((pathTupleToLatticePaths N lam mu pt) i).eastStepHeights[k] <
        ((pathTupleToLatticePaths N lam mu pt) j).eastStepHeights[k'] := by
  -- The proof uses strong induction on j - i.
  -- For any i < j, we show h_i[k] < h_j[k'] when mu i + k = mu j + k'.
  --
  -- Base case (j = i + 1): We show that if h_i[k] ≥ h_j[k'], paths share a vertex.
  -- The key insight is that at x = (μ_i - i) + k - 1 = (μ_j - j) + k',
  -- path i is at y = h_i[k].val + 1 and path j is at y = h_j[k'].val + 1.
  -- If h_i[k] ≥ h_j[k'], then path i's y ≥ path j's y at this x-coordinate.
  -- But path j starts to the left of path i (at y = 1), so if they don't share
  -- a vertex, path j must be strictly above path i at all shared x-coordinates.
  -- This would force h_j[k'] > h_i[k], contradiction.
  --
  -- Inductive case (j > i + 1): Use transitivity through l = i + 1.
  intro i j hij k hk k' hk' hcol
  -- Use strong induction on the difference j - i
  have h_diff_pos : 0 < j.val - i.val := Nat.sub_pos_of_lt hij
  obtain ⟨d, hd⟩ : ∃ d, j.val - i.val = d + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_diff_pos)
  induction d using Nat.strong_induction_on generalizing i j k k' with
  | _ d ih =>
    by_cases hcons : d = 0
    · -- Base case: j = i + 1 (consecutive rows)
      subst hcons
      have hj_eq : j.val = i.val + 1 := by omega
      -- Proof by contradiction: assume h_i[k] ≥ h_j[k']
      by_contra h_not_lt
      push_neg at h_not_lt
      -- We show paths share a vertex, contradicting hni
      have hij_ne : i ≠ j := Fin.ne_of_lt hij
      apply hni i j hij_ne
      -- The shared vertex is (μ_i - i, 1) - the starting point of path i.
      use ((mu i : ℤ) - (i.val : ℤ), 1)
      constructor
      · -- (μ_i - i, 1) is the start of path i
        have hstart := pt.starts i
        unfold jacobiTrudiSourceVertexRect at hstart
        rw [← hstart]
        exact List.head_mem (pt.paths i).nonempty
      · -- Path j visits (μ_i - i, 1)
        -- This is the key step. We need to show that path j passes through
        -- the starting point of path i.
        --
        -- The proof is by contradiction using the discrete IVT approach.
        -- We show that if path j doesn't visit (μ_i - i, 1), then h_j[k'] > h_i[k],
        -- contradicting h_not_lt.
        --
        -- Set up: path j goes from (μ_j - j, 1) to (λ_j - j, N)
        -- Since j = i + 1 and μ is weakly decreasing, μ_j - j < μ_i - i
        -- So path j starts strictly to the left of (μ_i - i, 1)
        --
        -- Key facts:
        -- 1. Path j visits x = μ_i - i (since it starts left and ends right of this x)
        -- 2. If path j doesn't visit (μ_i - i, 1), then at x = μ_i - i, path j has y > 1
        -- 3. Since paths don't share any vertex, path j stays strictly above path i
        -- 4. At x = μ_i - i + k, this means h_j[k'] > h_i[k]
        --
        -- This contradicts h_not_lt, so path j must visit (μ_i - i, 1).
        by_contra h_not_in_j
        -- Path j's start and end
        have hstart_j := pt.starts j
        have hfinish_j := pt.finishes j
        unfold jacobiTrudiSourceVertexRect at hstart_j
        unfold jacobiTrudiTargetVertexRect at hfinish_j
        -- Path j starts at (μ_j - j, 1) which is strictly left of (μ_i - i, 1)
        have hmu_j_lt : (mu j : ℤ) - (j.val : ℤ) < (mu i : ℤ) - (i.val : ℤ) := by
          have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij)
          omega
        -- Path j ends at x = λ_j - j. We need this to be ≥ μ_i - i + k.
        -- From hcol: mu i + k = mu j + k', and k' < lam j - mu j
        -- So mu i + k < lam j, hence μ_i - i + k < λ_j - j + 1
        have hlen_j : ((pathTupleToLatticePaths N lam mu pt) j).eastStepHeights.length = lam j - mu j := by
          have h := ((pathTupleToLatticePaths N lam mu pt) j).length_eq
          have hcont_j : mu j ≤ lam j := hcontained j
          simp only [sub_sub_sub_cancel_right] at h
          omega
        have hk'_bound : k' < lam j - mu j := by rw [← hlen_j]; exact hk'
        have h_col_bound : mu i + k < lam j := by omega
        -- Now we derive the contradiction from h_not_lt.
        -- The key insight is that if path j doesn't visit (μ_i - i, 1),
        -- then path j is strictly above path i at x = μ_i - i.
        -- Since paths don't intersect, path j stays above path i.
        -- At x = μ_i - i + k, this means h_j[k'] > h_i[k].
        --
        -- The east step heights satisfy:
        -- - h_i[k] is the y-coordinate (minus 1) of path i's k-th east step
        -- - h_j[k'] is the y-coordinate (minus 1) of path j's k'-th east step
        -- - Both east steps occur at the same x-coordinate
        --
        -- Since path j is above path i at x = μ_i - i, and paths don't intersect,
        -- path j stays above path i. So at x = μ_i - i + k, y_j > y_i.
        -- This means h_j[k'].val + 1 > h_i[k].val + 1, so h_j[k'] > h_i[k].
        -- But h_not_lt says h_i[k] ≥ h_j[k'], contradiction.
        have h_heights : ((pathTupleToLatticePaths N lam mu pt) j).eastStepHeights[k'] >
            ((pathTupleToLatticePaths N lam mu pt) i).eastStepHeights[k] := by
          -- The proof uses path_above_stays_above (the sum-based version) and
          -- lgvPathEastStepYCoords_at_x to connect eastStepHeights to actual y-coordinates.
          --
          -- Key insight: At x = μ_i - i, path i is at y = 1 (its start), while path j
          -- is at y > 1 (since it doesn't visit (μ_i - i, 1)). The sum values at these
          -- points are s_i = μ_i - i + 1 and s_j = μ_i - i + y_j > s_i.
          -- By path_above_stays_above, path j stays above path i at all later sums.
          --
          -- At x = μ_i - i + k, the east-step y-coordinates are related to the heights.
          -- By lgvPathEastStepYCoords_at_x, the y-coordinate at x = μ_i - i + k for path i
          -- is eastStepHeights[k].val + 1, and similarly for path j.
          --
          -- Since path j is above path i at x = μ_i - i, and paths don't intersect,
          -- path j stays above at x = μ_i - i + k, giving h_j[k'] > h_i[k].
          --
          -- Get the LGV paths
          let p_i := pt.paths i
          let p_j := pt.paths j
          -- Path i starts at (μ_i - i, 1)
          have hstart_i := pt.starts i
          unfold jacobiTrudiSourceVertexRect at hstart_i
          -- At x = μ_i - i, path i is at y = 1 (sum = μ_i - i + 1)
          -- At x = μ_i - i, path j is at y > 1 (since it doesn't visit (μ_i - i, 1))
          -- The sum for path j at x = μ_i - i is s_j = μ_i - i + y_j where y_j > 1
          -- Use path_above_stays_above with s₀ = μ_i - i + 1 (sum where path i starts)
          -- and s₁ = sum at x = μ_i - i + k
          --
          -- First, establish that path j visits x = μ_i - i at some y > 1
          have hj_visits_x₀ : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
              (p_j.vertices.get ⟨idx, hidx⟩).1 = (mu i : ℤ) - (i.val : ℤ) ∧
              (p_j.vertices.get ⟨idx, hidx⟩).2 > 1 := by
            -- Path j starts at (μ_j - j, 1) and ends at (λ_j - j, N)
            -- Since μ_j - j < μ_i - i < λ_j - j (from bounds), path j visits x = μ_i - i
            have hx_in_range : (mu j : ℤ) - (j.val : ℤ) < (mu i : ℤ) - (i.val : ℤ) ∧
                (mu i : ℤ) - (i.val : ℤ) ≤ (lam j : ℤ) - (j.val : ℤ) := by
              constructor
              · exact hmu_j_lt
              · have h1 : mu i + k < lam j := h_col_bound
                have h2 : k < lam i - mu i := by
                  have hlen_i : ((pathTupleToLatticePaths N lam mu pt) i).eastStepHeights.length = lam i - mu i := by
                    have h := ((pathTupleToLatticePaths N lam mu pt) i).length_eq
                    have hcont_i : mu i ≤ lam i := hcontained i
                    simp only [sub_sub_sub_cancel_right] at h
                    omega
                  rw [← hlen_i]; exact hk
                omega
            -- Path j is monotone in x, so it visits all x in [start.x, finish.x]
            -- Find the first vertex with x = μ_i - i
            -- This vertex has y > 1 since (μ_i - i, 1) is not in path j
            have hbd := LGV.integerLattice_path_vertices_bounded p_j
            have hlen := LGV.integerLattice_path_length_eq p_j
            rw [hstart_j, hfinish_j] at hlen hbd
            -- The x-coordinate increases from μ_j - j to λ_j - j
            -- At some index, x = μ_i - i
            -- Use that x increases by 0 or 1 at each step (integerLattice_path_x_step)
            -- Find idx such that x = μ_i - i
            -- Since start.x < μ_i - i ≤ finish.x, such idx exists
            -- The proof uses discrete IVT on x-coordinates
            --
            -- First, find an index where x = μ_i - i using discrete IVT
            -- Define x_coord(idx) = (p_j.vertices.get idx).1
            -- At idx = 0, x = μ_j - j < μ_i - i
            -- At idx = length - 1, x = λ_j - j ≥ μ_i - i
            -- x increases by 0 or 1 at each step
            -- By IVT, there exists idx with x = μ_i - i
            have hlen_pos : 0 < p_j.vertices.length := List.length_pos_of_ne_nil p_j.nonempty
            have hlast : p_j.vertices.length - 1 < p_j.vertices.length := Nat.sub_lt hlen_pos Nat.one_pos
            -- x at start < μ_i - i
            have hx_start : (p_j.vertices.get ⟨0, hlen_pos⟩).1 < (mu i : ℤ) - (i.val : ℤ) := by
              have hstart_eq : p_j.vertices.get ⟨0, hlen_pos⟩ = p_j.start := by
                simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
              rw [hstart_eq, hstart_j]
              exact hx_in_range.1
            -- x at end ≥ μ_i - i
            have hx_end : (p_j.vertices.get ⟨p_j.vertices.length - 1, hlast⟩).1 ≥ (mu i : ℤ) - (i.val : ℤ) := by
              have hfinish_eq : p_j.vertices.get ⟨p_j.vertices.length - 1, hlast⟩ = p_j.finish := by
                simp only [LGV.SimpleDigraph.Path.finish, List.getLast_eq_getElem, List.get_eq_getElem]
              rw [hfinish_eq, hfinish_j]
              exact hx_in_range.2
            -- Use discrete IVT to find the index
            -- The x-coordinate function: f(idx) = x(idx) - (μ_i - i)
            -- f(0) < 0 and f(length-1) ≥ 0
            -- |f(idx+1) - f(idx)| ≤ 1 (since x increases by 0 or 1)
            -- By IVT, there exists idx with f(idx) = 0
            let f (idx : ℕ) (hidx : idx < p_j.vertices.length) : ℤ :=
              (p_j.vertices.get ⟨idx, hidx⟩).1 - ((mu i : ℤ) - (i.val : ℤ))
            have hf_start : f 0 hlen_pos < 0 := by simp only [f]; omega
            have hf_end : f (p_j.vertices.length - 1) hlast ≥ 0 := by simp only [f]; omega
            -- Find the first index where f ≥ 0
            -- This index has f = 0 (since f increases by at most 1 and f(prev) < 0)
            have h_exists : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
                (p_j.vertices.get ⟨idx, hidx⟩).1 = (mu i : ℤ) - (i.val : ℤ) := by
              -- Use Nat.find to get the smallest index where x ≥ target
              let target : ℤ := (mu i : ℤ) - (i.val : ℤ)
              let P : ℕ → Prop := fun idx => ∃ hidx : idx < p_j.vertices.length,
                  (p_j.vertices.get ⟨idx, hidx⟩).1 ≥ target
              have hP_dec : DecidablePred P := by
                intro idx
                by_cases h : idx < p_j.vertices.length
                · exact decidable_of_iff ((p_j.vertices.get ⟨idx, h⟩).1 ≥ target)
                    ⟨fun hf => ⟨h, hf⟩, fun ⟨_, hf⟩ => hf⟩
                · exact isFalse (fun ⟨hidx, _⟩ => h hidx)
              have hP_exists : ∃ idx, P idx := ⟨p_j.vertices.length - 1, hlast, hx_end⟩
              let idx₀ := Nat.find hP_exists
              have hidx₀_lt : idx₀ < p_j.vertices.length := (Nat.find_spec hP_exists).choose
              have hx_idx₀_ge : (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 ≥ target :=
                (Nat.find_spec hP_exists).choose_spec
              -- Show idx₀ > 0 (since x at 0 < target)
              have hidx₀_pos : idx₀ > 0 := by
                by_contra h
                push_neg at h
                have hidx₀_eq_zero : idx₀ = 0 := Nat.eq_zero_of_le_zero h
                have h1 : (p_j.vertices.get ⟨0, hlen_pos⟩).1 ≥ target := by
                  have heq' : (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 =
                             (p_j.vertices.get ⟨0, hlen_pos⟩).1 := by
                    simp only [hidx₀_eq_zero]
                  rw [← heq']; exact hx_idx₀_ge
                simp only [target] at h1
                omega
              -- At idx₀ - 1, x < target (by minimality of idx₀)
              have hidx₀_pred_lt : idx₀ - 1 < p_j.vertices.length :=
                Nat.lt_of_lt_of_le (Nat.sub_lt hidx₀_pos Nat.one_pos) (Nat.le_of_lt hidx₀_lt)
              have hx_pred_lt : (p_j.vertices.get ⟨idx₀ - 1, hidx₀_pred_lt⟩).1 < target := by
                by_contra h
                push_neg at h
                have : P (idx₀ - 1) := ⟨hidx₀_pred_lt, h⟩
                have : idx₀ ≤ idx₀ - 1 := Nat.find_le this
                omega
              -- The step from idx₀ - 1 to idx₀ increases x by 0 or 1
              have hstep_idx : idx₀ - 1 + 1 < p_j.vertices.length := by omega
              have hstep := LGV.integerLattice_path_x_step p_j (idx₀ - 1) hstep_idx
              -- idx₀ - 1 + 1 = idx₀
              have heq : idx₀ - 1 + 1 = idx₀ := Nat.sub_add_cancel hidx₀_pos
              -- So x increases by 0 or 1 from idx₀ - 1 to idx₀
              -- Since x(idx₀ - 1) < target ≤ x(idx₀) and x increases by at most 1, x(idx₀) = target
              have hx_idx₀_eq : (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 = target := by
                have h1 : (p_j.vertices.get ⟨idx₀ - 1 + 1, hstep_idx⟩).1 =
                          (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 := by
                  simp only [Nat.sub_add_cancel hidx₀_pos]
                have h2 : (p_j.vertices.get ⟨idx₀ - 1, Nat.lt_of_succ_lt hstep_idx⟩).1 =
                          (p_j.vertices.get ⟨idx₀ - 1, hidx₀_pred_lt⟩).1 := rfl
                rcases hstep with hstep0 | hstep1
                · -- x(idx₀) = x(idx₀ - 1), but x(idx₀ - 1) < target ≤ x(idx₀), contradiction
                  rw [h1, h2] at hstep0
                  omega
                · -- x(idx₀) = x(idx₀ - 1) + 1
                  rw [h1, h2] at hstep1
                  omega
              exact ⟨idx₀, hidx₀_lt, hx_idx₀_eq⟩
            obtain ⟨idx, hidx, hx_eq⟩ := h_exists
            -- Now show y > 1 at this index
            -- If y = 1, then vertex is (μ_i - i, 1), which is not in path j
            refine ⟨idx, hidx, hx_eq, ?_⟩
            by_contra hy_le
            push_neg at hy_le
            -- y ≤ 1, but y ≥ 1 (since path starts at y = 1 and y increases)
            have hy_ge : (p_j.vertices.get ⟨idx, hidx⟩).2 ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded p_j idx hidx
              rw [hstart_j] at hbd
              exact hbd.2.2.1
            have hy_eq : (p_j.vertices.get ⟨idx, hidx⟩).2 = 1 := by omega
            -- So vertex is (μ_i - i, 1)
            have hv_eq : p_j.vertices.get ⟨idx, hidx⟩ = ((mu i : ℤ) - (i.val : ℤ), 1) := by
              ext <;> [exact hx_eq; exact hy_eq]
            -- But (μ_i - i, 1) is not in path j
            have hmem : p_j.vertices.get ⟨idx, hidx⟩ ∈ p_j.vertices := List.get_mem p_j.vertices ⟨idx, hidx⟩
            rw [hv_eq] at hmem
            exact h_not_in_j hmem

          obtain ⟨idx_j_x₀, hidx_j_x₀, hx_j_x₀, hy_j_x₀⟩ := hj_visits_x₀
          -- Key insight for the base case (j = i + 1):
          -- At x = x₀ = μ_i - i, path i starts at y = 1, while path j is at y > 1.
          -- Since paths don't intersect, this "path j above path i" property is maintained.
          --
          -- Define x₀ (path i's starting x-coordinate) and x₁ (where we compare heights)
          let x₀ : ℤ := (mu i : ℤ) - (i.val : ℤ)
          let x₁ : ℤ := (mu i : ℤ) - (i.val : ℤ) + k
          
          -- Path i has a vertex at x₀ (its start)
          have hx₀_p_i : ∃ (idx : ℕ) (hidx : idx < p_i.vertices.length),
              (p_i.vertices.get ⟨idx, hidx⟩).1 = x₀ := by
            have hlen_pos : 0 < p_i.vertices.length := List.length_pos_of_ne_nil p_i.nonempty
            refine ⟨0, hlen_pos, ?_⟩
            have hstart_eq : p_i.vertices.get ⟨0, hlen_pos⟩ = p_i.start := by
              simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
            rw [hstart_eq, hstart_i]
          
          -- Path j has a vertex at x₀ (from hj_visits_x₀)
          have hx₀_p_j : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
              (p_j.vertices.get ⟨idx, hidx⟩).1 = x₀ := ⟨idx_j_x₀, hidx_j_x₀, hx_j_x₀⟩
          
          -- Non-intersection: path i and j share no vertices
          have hni_ij : ∀ v, v ∈ p_i.vertices → v ∉ p_j.vertices := by
            intro v hv_in_i hv_in_j
            apply hni i j hij_ne
            exact ⟨v, hv_in_i, hv_in_j⟩
          
          -- At x₀, path j's y > path i's y for ALL pairs of vertices at x₀
          -- This is the key lemma: path i at x₀ has only vertices with y ∈ {1, 2, ..., m}
          -- where m is the max y of path i at x₀. Path j at x₀ has y > 1 and disjoint
          -- from path i's y-values, so path j's y > m ≥ path i's y.
          have h_above_at_x₀ : ∀ (idx_p : ℕ) (hidx_p : idx_p < p_i.vertices.length)
              (idx_p' : ℕ) (hidx_p' : idx_p' < p_j.vertices.length),
              (p_i.vertices.get ⟨idx_p, hidx_p⟩).1 = x₀ →
              (p_j.vertices.get ⟨idx_p', hidx_p'⟩).1 = x₀ →
              (p_j.vertices.get ⟨idx_p', hidx_p'⟩).2 > (p_i.vertices.get ⟨idx_p, hidx_p⟩).2 := by
            intro idx_p hidx_p idx_p' hidx_p' hx_p hx_p'
            -- Path i at x₀ has y ≥ 1 (starts at y = 1)
            -- Path i's vertices at x₀ are consecutive y-values starting from 1
            -- Path j at x₀ has y > 1 (from hj_visits_x₀) and disjoint from path i
            -- 
            -- Key insight: at x₀ = start.x of path i, path i's vertices at x₀
            -- form a consecutive sequence {(x₀, 1), (x₀, 2), ..., (x₀, m)}.
            -- Path j's vertices at x₀ are disjoint (non-intersection) and have y > 1.
            -- So path j's y-values at x₀ are in ℕ≥2 \ {2, ..., m} = {m+1, m+2, ...}.
            -- Therefore path j's y > m ≥ path i's y at x₀.
            --
            -- The proof uses that path i at x₀ starts at y = 1 (index 0).
            have hlen_pos_i : 0 < p_i.vertices.length := List.length_pos_of_ne_nil p_i.nonempty
            have hstart_at_x₀ : (p_i.vertices.get ⟨0, hlen_pos_i⟩).1 = x₀ := by
              have hstart_eq : p_i.vertices.get ⟨0, hlen_pos_i⟩ = p_i.start := by
                simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
              rw [hstart_eq, hstart_i]
            have hstart_y : (p_i.vertices.get ⟨0, hlen_pos_i⟩).2 = 1 := by
              have hstart_eq : p_i.vertices.get ⟨0, hlen_pos_i⟩ = p_i.start := by
                simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
              rw [hstart_eq, hstart_i]
            -- Path i's vertex at idx_p has x = x₀ and y ≥ 1
            have hy_p_ge : (p_i.vertices.get ⟨idx_p, hidx_p⟩).2 ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded p_i idx_p hidx_p
              rw [hstart_i] at hbd
              exact hbd.2.2.1
            -- The y-coordinate at idx_p is between 1 and some max value
            -- Use integerLattice_path_y_contiguous_at_x to show path i covers all y in [1, y_p]
            -- Since path j's vertex at idx_p' has the same x = x₀ and y > 1,
            -- and paths don't intersect, path j's y must be > path i's max y at x₀.
            --
            -- Simpler argument: path i at x₀ has consecutive y-values from 1.
            -- If path j at x₀ has y = y_j, and y_j ≤ y_p, then (x₀, y_j) is in path i
            -- (by contiguity), contradicting non-intersection.
            by_contra h_not_above
            push_neg at h_not_above
            -- So y_j ≤ y_p
            let y_p := (p_i.vertices.get ⟨idx_p, hidx_p⟩).2
            let y_j := (p_j.vertices.get ⟨idx_p', hidx_p'⟩).2
            -- y_j ≥ 1 (from hy_j_x₀ we know y > 1 for the specific idx_j_x₀, but we need it for idx_p')
            have hy_j_ge : y_j ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded p_j idx_p' hidx_p'
              rw [hstart_j] at hbd
              exact hbd.2.2.1
            -- Use integerLattice_path_y_contiguous_at_x: path i covers all y in [1, y_p] at x₀
            -- Since y_j ∈ [1, y_p] (by hy_j_ge and h_not_above), (x₀, y_j) ∈ path i
            have h_contiguous := integerLattice_path_y_contiguous_at_x p_i x₀
              0 idx_p hlen_pos_i hidx_p (Nat.zero_le _) hstart_at_x₀ hx_p y_j
              (by simp only [y_j]; rw [hstart_y]; exact hy_j_ge) h_not_above
            obtain ⟨k_i, hk_i, _, _, hx_k_i, hy_k_i⟩ := h_contiguous
            -- So path i has vertex (x₀, y_j) at index k_i
            have hv_i : p_i.vertices.get ⟨k_i, hk_i⟩ = (x₀, y_j) := by
              ext <;> [exact hx_k_i; exact hy_k_i]
            -- Path j has vertex (x₀, y_j) at index idx_p'
            have hv_j : p_j.vertices.get ⟨idx_p', hidx_p'⟩ = (x₀, y_j) := by
              ext <;> [exact hx_p'; rfl]
            -- But (x₀, y_j) is in both paths, contradicting non-intersection
            have hmem_i : (x₀, y_j) ∈ p_i.vertices := by
              rw [← hv_i]; exact List.get_mem p_i.vertices ⟨k_i, hk_i⟩
            have hmem_j : (x₀, y_j) ∈ p_j.vertices := by
              rw [← hv_j]; exact List.get_mem p_j.vertices ⟨idx_p', hidx_p'⟩
            exact hni_ij (x₀, y_j) hmem_i hmem_j
          
          -- Now use paths_above_at_x_stays_above to extend to x₁
          -- First, establish that both paths visit x₁
          -- Path i visits x₁ at its k-th east step
          have hx₁_ge_x₀ : x₁ ≥ x₀ := by simp only [x₁, x₀]; omega
          
          -- Get the y-coordinates at x₁ from lgvPathEastStepYCoords_at_x
          -- For path i: the k-th east step is at x = start_x + k = μ_i - i + k = x₁
          have hk_lt_ycoords_i : k < (lgvPathEastStepYCoords p_i.vertices).length := by
            have hlen_eq : (lgvPathEastStepYCoords p_i.vertices).length = 
                ((pathTupleToLatticePaths N lam mu pt) i).eastStepHeights.length := by
              simp only [pathTupleToLatticePaths, lgvPathToLatticePath, p_i]
              simp only [lgvYCoordsToFinN, List.length_pmap]
            rw [hlen_eq]; exact hk
          have h_i_at_x₁ := lgvPathEastStepYCoords_at_x p_i k hk_lt_ycoords_i
          obtain ⟨idx_i_x₁, hidx_i_x₁, hx_i_x₁, hy_i_x₁⟩ := h_i_at_x₁
          -- Verify x-coordinate matches x₁
          have hx_i_x₁_eq : (p_i.vertices.get ⟨idx_i_x₁, hidx_i_x₁⟩).1 = x₁ := by
            rw [hx_i_x₁]
            -- p_i.start.1 = (mu i : ℤ) - (i.val : ℤ) from hstart_i
            have hstart_x : p_i.start.1 = (mu i : ℤ) - (i.val : ℤ) := by
              simp only [p_i, hstart_i]
            rw [hstart_x]
          
          -- For path j: the k'-th east step is at x = start_x + k' = μ_j - j + k'
          -- We need to show this equals x₁ = μ_i - i + k
          -- From hcol: mu i + k = mu j + k', so μ_i - i + k = μ_j - j + k' + (j - i)
          -- Since j = i + 1, we get μ_i - i + k = μ_j - j + k' + 1
          -- So path j's k'-th east step is at x = x₁ - 1, and AFTER the east step, path j is at x₁
          have hk'_lt_ycoords_j : k' < (lgvPathEastStepYCoords p_j.vertices).length := by
            have hlen_eq : (lgvPathEastStepYCoords p_j.vertices).length = 
                ((pathTupleToLatticePaths N lam mu pt) j).eastStepHeights.length := by
              simp only [pathTupleToLatticePaths, lgvPathToLatticePath, p_j]
              simp only [lgvYCoordsToFinN, List.length_pmap]
            rw [hlen_eq]; exact hk'
          have h_j_at_kprime := lgvPathEastStepYCoords_at_x p_j k' hk'_lt_ycoords_j
          obtain ⟨idx_j_kprime, hidx_j_kprime, hx_j_kprime, hy_j_kprime⟩ := h_j_at_kprime
          -- Path j's k'-th east step starts at x = μ_j - j + k'
          have hx_j_kprime_val : (p_j.vertices.get ⟨idx_j_kprime, hidx_j_kprime⟩).1 = 
              (mu j : ℤ) - (j.val : ℤ) + k' := by
            rw [hx_j_kprime]
            have hstart_x : p_j.start.1 = (mu j : ℤ) - (j.val : ℤ) := by
              simp only [p_j, hstart_j]
            rw [hstart_x]
          -- The x-coordinate where path j's k'-th east step starts
          -- From hcol: mu i + k = mu j + k'
          -- So μ_j - j + k' = μ_j + k' - j = (μ_i + k) - j = μ_i + k - (i + 1) = μ_i - i + k - 1 = x₁ - 1
          have hx_j_eq_x₁_minus_1 : (mu j : ℤ) - (j.val : ℤ) + k' = x₁ - 1 := by
            simp only [x₁]
            have h1 : (mu i : ℕ) + k = (mu j : ℕ) + k' := hcol
            have h2 : j.val = i.val + 1 := hj_eq
            omega
          -- After the east step, path j is at x = x₁
          -- The east step increases x by 1, so the next vertex is at x = x₁
          -- Use lgvPathEastStepYCoords_at_x_is_east_step to get the next vertex
          have hidx_j_next : idx_j_kprime + 1 < p_j.vertices.length := by
            -- The k'-th east step is not the last step (path ends at y = N, not at this east step)
            -- Actually, we need to show idx_j_kprime + 1 < length
            -- This follows from the fact that there are more vertices after the east step
            -- The path ends at (λ_j - j, N), and the k'-th east step is at x = x₁ - 1 < λ_j - j
            -- So there are more vertices after this east step
            have hfinish_x : p_j.finish.1 = (lam j : ℤ) - (j.val : ℤ) := by
              rw [hfinish_j]
            have hx_lt_finish : (p_j.vertices.get ⟨idx_j_kprime, hidx_j_kprime⟩).1 < p_j.finish.1 := by
              rw [hx_j_kprime_val, hfinish_x, hx_j_eq_x₁_minus_1]
              simp only [x₁]
              -- Need: μ_i - i + k - 1 < λ_j - j
              -- From h_col_bound: mu i + k < lam j
              -- So μ_i + k < λ_j, hence μ_i - i + k < λ_j - i = λ_j - j + (j - i) = λ_j - j + 1
              -- So μ_i - i + k - 1 < λ_j - j
              omega
            -- If idx_j_kprime is the last index, then the vertex is the finish
            by_contra h_last
            push_neg at h_last
            -- h_last : p_j.vertices.length ≤ idx_j_kprime + 1
            -- We know idx_j_kprime < p_j.vertices.length (from hidx_j_kprime)
            -- So idx_j_kprime + 1 ≤ p_j.vertices.length
            -- Combined with h_last, we get idx_j_kprime + 1 = p_j.vertices.length
            have hidx_eq_last : idx_j_kprime = p_j.vertices.length - 1 := by
              have h1 : idx_j_kprime + 1 ≤ p_j.vertices.length := hidx_j_kprime
              have h2 : p_j.vertices.length ≤ idx_j_kprime + 1 := h_last
              omega
            have hfinish_eq : p_j.vertices.get ⟨idx_j_kprime, hidx_j_kprime⟩ = p_j.finish := by
              simp only [LGV.SimpleDigraph.Path.finish, List.getLast_eq_getElem, List.get_eq_getElem]
              congr 1
            rw [hfinish_eq] at hx_lt_finish
            exact (lt_irrefl _ hx_lt_finish)
          have h_east_step := lgvPathEastStepYCoords_at_x_is_east_step p_j k' hk'_lt_ycoords_j
            idx_j_kprime hidx_j_kprime hx_j_kprime hy_j_kprime hidx_j_next
          -- The next vertex is at x = x₁ with the same y-coordinate
          have hx_j_next : (p_j.vertices.get ⟨idx_j_kprime + 1, hidx_j_next⟩).1 = x₁ := by
            rw [h_east_step.1, hx_j_kprime_val, hx_j_eq_x₁_minus_1]
            ring
          have hy_j_next : (p_j.vertices.get ⟨idx_j_kprime + 1, hidx_j_next⟩).2 = 
              (lgvPathEastStepYCoords p_j.vertices)[k'] := by
            rw [h_east_step.2, hy_j_kprime]
          
          -- Now apply paths_above_at_x_stays_above
          have hx₁_p_i : ∃ (idx : ℕ) (hidx : idx < p_i.vertices.length),
              (p_i.vertices.get ⟨idx, hidx⟩).1 = x₁ := ⟨idx_i_x₁, hidx_i_x₁, hx_i_x₁_eq⟩
          have hx₁_p_j : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
              (p_j.vertices.get ⟨idx, hidx⟩).1 = x₁ := ⟨idx_j_kprime + 1, hidx_j_next, hx_j_next⟩
          
          have h_above_at_x₁ := paths_above_at_x_stays_above p_i p_j hni_ij x₀ hx₀_p_i hx₀_p_j
            h_above_at_x₀ x₁ hx₁_ge_x₀ hx₁_p_i hx₁_p_j
          
          -- Apply to our specific indices
          have h_y_comparison := h_above_at_x₁ idx_i_x₁ hidx_i_x₁ (idx_j_kprime + 1) hidx_j_next
            hx_i_x₁_eq hx_j_next
          -- h_y_comparison : y_j > y_i at x₁
          -- y_i = lgvPathEastStepYCoords p_i.vertices [k] = eastStepHeights[k].val + 1
          -- y_j = lgvPathEastStepYCoords p_j.vertices [k'] = eastStepHeights[k'].val + 1
          
          -- Convert to eastStepHeights comparison
          -- eastStepHeights[k] = lgvYCoordsToFinN (lgvPathEastStepYCoords ...) [k]
          -- lgvYCoordsToFinN maps y to (y - 1).toNat as Fin N
          -- So eastStepHeights[k].val = (lgvPathEastStepYCoords ...)[k] - 1
          simp only [pathTupleToLatticePaths, lgvPathToLatticePath] at hk hk' ⊢
          -- Need to show: eastStepHeights[k'] > eastStepHeights[k]
          -- i.e., (lgvYCoordsToFinN ...)[k'].val > (lgvYCoordsToFinN ...)[k].val
          -- i.e., (lgvPathEastStepYCoords p_j.vertices)[k'] - 1 > (lgvPathEastStepYCoords p_i.vertices)[k] - 1
          -- i.e., (lgvPathEastStepYCoords p_j.vertices)[k'] > (lgvPathEastStepYCoords p_i.vertices)[k]
          -- This follows from h_y_comparison since y_i = ycoords[k] and y_j = ycoords[k']
          rw [hy_i_x₁] at h_y_comparison
          rw [hy_j_next] at h_y_comparison
          -- h_y_comparison : (lgvPathEastStepYCoords p_j.vertices)[k'] > (lgvPathEastStepYCoords p_i.vertices)[k]
          -- Convert to Fin comparison
          have hfinish_i := pt.finishes i
          unfold jacobiTrudiTargetVertexRect at hfinish_i
          have hbnd_i : ∀ y ∈ lgvPathEastStepYCoords p_i.vertices, 1 ≤ y ∧ y ≤ N := by
            intro y hy
            have hbnd := lgvPathEastStepYCoords_bounded p_i.vertices p_i.nonempty p_i.arcs_valid y hy
            simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart_i hfinish_i
            rw [hstart_i, hfinish_i] at hbnd
            simp at hbnd
            exact hbnd
          have hbnd_j : ∀ y ∈ lgvPathEastStepYCoords p_j.vertices, 1 ≤ y ∧ y ≤ N := by
            intro y hy
            have hbnd := lgvPathEastStepYCoords_bounded p_j.vertices p_j.nonempty p_j.arcs_valid y hy
            simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart_j hfinish_j
            rw [hstart_j, hfinish_j] at hbnd
            simp at hbnd
            exact hbnd
          have hk_mem : (lgvPathEastStepYCoords p_i.vertices)[k] ∈ lgvPathEastStepYCoords p_i.vertices :=
            List.getElem_mem hk_lt_ycoords_i
          have hk'_mem : (lgvPathEastStepYCoords p_j.vertices)[k'] ∈ lgvPathEastStepYCoords p_j.vertices :=
            List.getElem_mem hk'_lt_ycoords_j
          have hbnd_k := hbnd_i _ hk_mem
          have hbnd_k' := hbnd_j _ hk'_mem
          -- The Fin values are (y - 1).toNat
          simp only [lgvYCoordsToFinN, List.getElem_pmap]
          -- Goal: Fin.mk ((ycoords_j[k'] - 1).toNat) _ > Fin.mk ((ycoords_i[k] - 1).toNat) _
          simp only [Fin.lt_def]
          -- Goal: (ycoords_j[k'] - 1).toNat > (ycoords_i[k] - 1).toNat
          have h1 : ((lgvPathEastStepYCoords p_i.vertices)[k] - 1).toNat = 
              (lgvPathEastStepYCoords p_i.vertices)[k].toNat - 1 := by
            have hge : (lgvPathEastStepYCoords p_i.vertices)[k] ≥ 1 := hbnd_k.1
            omega
          have h2 : ((lgvPathEastStepYCoords p_j.vertices)[k'] - 1).toNat = 
              (lgvPathEastStepYCoords p_j.vertices)[k'].toNat - 1 := by
            have hge : (lgvPathEastStepYCoords p_j.vertices)[k'] ≥ 1 := hbnd_k'.1
            omega
          rw [h1, h2]
          omega

        -- Now derive contradiction
        exact absurd h_heights (not_lt.mpr h_not_lt)
    · -- Inductive case: j > i + 1
      -- Use the intermediate row l = i + 1
      have h_j_gt : j.val > i.val + 1 := by omega
      have hl_lt_N : i.val + 1 < M := by
        have := j.is_lt
        omega
      let l : Fin M := ⟨i.val + 1, hl_lt_N⟩
      -- k_l = μ_i + k - μ_l is the index for row l at the same tableau column
      have hmu_l : mu l ≤ mu i := hmu i l (Fin.le_of_lt (by simp only [l, Fin.lt_def]; omega : i < l))
      have hlam_l : lam j ≤ lam l := hlam l j (by simp only [l, Fin.le_iff_val_le_val]; omega)
      let k_l : ℕ := mu i + k - mu l
      have hk_l_eq : mu l + k_l = mu i + k := by
        show mu l + (mu i + k - mu l) = mu i + k
        omega
      -- Verify k_l is a valid index
      have hk_l_lt : k_l < ((pathTupleToLatticePaths N lam mu pt) l).eastStepHeights.length := by
        -- k_l = mu i + k - mu l < lam l - mu l
        -- This follows from mu i + k = mu j + k' < lam j ≤ lam l
        -- First establish that length = lam l - mu l
        have hlen_l : ((pathTupleToLatticePaths N lam mu pt) l).eastStepHeights.length = lam l - mu l := by
          have h := ((pathTupleToLatticePaths N lam mu pt) l).length_eq
          -- h : length = ((lam l : ℤ) - l.val - ((mu l : ℤ) - l.val)).toNat
          have hcont_l : mu l ≤ lam l := hcontained l
          simp only [sub_sub_sub_cancel_right] at h
          omega
        rw [hlen_l]
        -- Now goal is k_l < lam l - mu l
        -- From hk' : k' < length_j = lam j - mu j
        have hlen_j : ((pathTupleToLatticePaths N lam mu pt) j).eastStepHeights.length = lam j - mu j := by
          have h := ((pathTupleToLatticePaths N lam mu pt) j).length_eq
          have hcont_j : mu j ≤ lam j := hcontained j
          simp only [sub_sub_sub_cancel_right] at h
          omega
        have hk'_bound : k' < lam j - mu j := by rw [← hlen_j]; exact hk'
        have h1 : mu j + k' < lam j := by omega
        have h2 : mu i + k < lam j := by omega
        have h3 : mu i + k ≤ lam l := Nat.le_of_lt (Nat.lt_of_lt_of_le h2 hlam_l)
        show k_l < lam l - mu l
        simp only [k_l]
        omega
      -- Apply IH for (i, l) with d' = 0 < d
      have h_i_lt_l : i < l := by
        simp only [l, Fin.lt_def]
        omega
      have h_d1_pos : 0 < l.val - i.val := by simp [l]
      have h_d1_eq : l.val - i.val = 0 + 1 := by simp [l]
      have h1 : ((pathTupleToLatticePaths N lam mu pt) i).eastStepHeights[k] <
          ((pathTupleToLatticePaths N lam mu pt) l).eastStepHeights[k_l] := by
        have h_d1_lt : 0 < d := by omega
        exact ih 0 h_d1_lt i l h_i_lt_l k hk k_l hk_l_lt hk_l_eq.symm h_d1_pos h_d1_eq
      -- Apply IH for (l, j) with d' = j - l - 1 < d
      have h_l_lt_j : l < j := by simp [l]; exact h_j_gt
      have h_d2_pos : 0 < j.val - l.val := Nat.sub_pos_of_lt h_l_lt_j
      have h_d2_eq : j.val - l.val = (d - 1) + 1 := by simp [l]; omega
      have h_d2_lt : d - 1 < d := Nat.sub_lt (by omega : 0 < d) Nat.one_pos
      have hcol_l : mu l + k_l = mu j + k' := by rw [hk_l_eq, hcol]
      have h2 : ((pathTupleToLatticePaths N lam mu pt) l).eastStepHeights[k_l] <
          ((pathTupleToLatticePaths N lam mu pt) j).eastStepHeights[k'] := by
        exact ih (d - 1) h_d2_lt l j h_l_lt_j k_l hk_l_lt k' hk' hcol_l h_d2_pos h_d2_eq
      -- Combine by transitivity
      exact Fin.lt_trans h1 h2

/-- Convert a non-intersecting PathTuple to a Nipat. -/
private noncomputable def pathTupleToRectNipat (N : ℕ) (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i)
    (pt : LGV.PathTuple LGV.integerLattice M
      (jacobiTrudiSourceVertexRect mu) (jacobiTrudiTargetVertexRect N lam))
    (hni : pt.isNonIntersecting) :
    RectNipat N lam mu hlam hmu hcontained where
  paths := pathTupleToLatticePaths N lam mu pt
  colStrictPaths :=
    isNonIntersecting_implies_colStrictPaths N lam mu hlam hmu hcontained pt hni

/-- Weight preservation: The LGV pathTupleWeight equals the Nipat weight under conversion. -/
private lemma pathTupleToRectNipat_weight (N : ℕ) (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i)
    (pt : LGV.PathTuple LGV.integerLattice M
      (jacobiTrudiSourceVertexRect mu) (jacobiTrudiTargetVertexRect N lam))
    (hni : pt.isNonIntersecting) :
    LGV.pathTupleWeight (jacobiTrudiArcWeight (N := N) (R := R)) pt.paths =
      (pathTupleToRectNipat N lam mu hlam hmu hcontained pt hni).weight (R := R) := by
  -- The weight of a PathTuple is ∏ᵢ pathWeight(pᵢ)
  -- The weight of a Nipat is ∏ᵢ (paths i).weight
  -- By lgvPathToLatticePath_weight_eq, these are equal for each path
  unfold LGV.pathTupleWeight RectNipat.weight pathTupleToRectNipat
    pathTupleToLatticePaths
  simp only
  apply Finset.prod_congr rfl
  intro i _
  exact lgvPathToLatticePath_weight_eq
    ((mu i : ℤ) - (i.val : ℤ))
    ((lam i : ℤ) - (i.val : ℤ))
    (pt.paths i)
    (by unfold jacobiTrudiSourceVertexRect at pt; exact pt.starts i)
    (by unfold jacobiTrudiTargetVertexRect at pt; exact pt.finishes i)

/-- The LGV nipat weight sum equals our Nipat weight sum.

    This connects the two representations of non-intersecting path tuples:
    - LGV: `PathTuple` with `isNonIntersecting` (no shared vertices)
    - Ours: `Nipat` with `colStrictPaths` (column-strictness)

    The bijection works as follows:
    - An LGV path from (a, 1) to (c, N) is encoded by its east-step heights
    - This is exactly our `LatticePath` type
    - Non-intersection of LGV paths ↔ column-strictness of east-step heights

    The proof uses `pathTupleToNipat` to convert LGV nipats to our Nipat type,
    with weight preservation via `pathTupleToNipat_weight`. -/
theorem lgv_nipatWeightSum_eq_rectNipatSum (N : ℕ) (lam mu : Fin M → ℕ)
    (hheight : M ≠ 0 → 0 < N)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    LGV.nipatWeightSum LGV.integerLattice_pathFinite
      (jacobiTrudiArcWeight (N := N) (R := R))
      (jacobiTrudiSourceVertexRect mu) (jacobiTrudiTargetVertexRect N lam)
      (Equiv.refl (Fin M)) =
    ∑ np : RectNipat N lam mu hlam hmu hcontained, np.weight (R := R) := by
  -- The proof establishes a weight-preserving bijection between:
  -- 1. LGV nipats: elements of nipatFinset with isNonIntersecting
  -- 2. Our Nipat: tuples of LatticePaths with colStrictPaths
  --
  -- Strategy: Use Finset.sum_bij with pathTupleToNipat as the bijection function.
  -- - pathTupleToNipat: converts non-intersecting PathTuples to Nipats
  -- - pathTupleToNipat_weight: proves weight preservation
  -- - Injectivity: follows from lgvPathToLatticePath being injective
  -- - Surjectivity: requires constructing the inverse (nipatToPathTuple)
  --
  -- Unfold the LHS
  unfold LGV.nipatWeightSum
  -- Use sum_bij to establish the equality
  refine Finset.sum_bij
    (fun pt hpt => pathTupleToRectNipat N lam mu hlam hmu hcontained pt
      ((LGV.mem_nipatFinset_iff LGV.integerLattice_pathFinite pt).mp hpt))
    ?_ ?_ ?_ ?_
  -- 1. The function maps into Finset.univ
  · intro pt hpt
    exact Finset.mem_univ _
  -- 2. Injectivity: if pathTupleToNipat pt₁ = pathTupleToNipat pt₂, then pt₁ = pt₂
  · intro pt₁ hpt₁ pt₂ hpt₂ heq
    -- pathTupleToNipat extracts paths via pathTupleToLatticePaths, which uses lgvPathToLatticePath
    -- lgvPathToLatticePath extracts east-step heights, which uniquely determine the path
    -- Therefore, equal Nipats imply equal PathTuples
    have hpaths : (pathTupleToRectNipat N lam mu hlam hmu hcontained pt₁
        ((LGV.mem_nipatFinset_iff LGV.integerLattice_pathFinite pt₁).mp hpt₁)).paths =
        (pathTupleToRectNipat N lam mu hlam hmu hcontained pt₂
        ((LGV.mem_nipatFinset_iff LGV.integerLattice_pathFinite pt₂).mp hpt₂)).paths :=
      congr_arg RectNipat.paths heq
    simp only [pathTupleToRectNipat] at hpaths
    -- hpaths : pathTupleToLatticePaths ... pt₁ = pathTupleToLatticePaths ... pt₂
    -- Need to show pt₁ = pt₂, i.e., pt₁.paths = pt₂.paths (as functions)
    ext i
    -- Goal: pt₁.paths i = pt₂.paths i
    have hi := congrFun hpaths i
    simp only [pathTupleToLatticePaths] at hi
    -- hi : lgvPathToLatticePath ... (pt₁.paths i) ... = lgvPathToLatticePath ... (pt₂.paths i) ...
    -- lgvPathToLatticePath extracts eastStepHeights
    -- Two paths with same start/end and same eastStepHeights are equal
    -- Use lgvPathToLatticePath_injective
    exact lgvPathToLatticePath_injective
      ((mu i : ℤ) - (i.val : ℤ))
      ((lam i : ℤ) - (i.val : ℤ))
      (pt₁.paths i) (pt₂.paths i)
      (by unfold jacobiTrudiSourceVertexRect at pt₁; exact pt₁.starts i)
      (by unfold jacobiTrudiTargetVertexRect at pt₁; exact pt₁.finishes i)
      (by unfold jacobiTrudiSourceVertexRect at pt₂; exact pt₂.starts i)
      (by unfold jacobiTrudiTargetVertexRect at pt₂; exact pt₂.finishes i)
      hi
  -- 3. Surjectivity: for every np : Nipat, there exists pt ∈ nipatFinset with pathTupleToNipat pt = np
  · intro np _
    -- We construct the inverse: given a Nipat, construct the corresponding PathTuple.
    -- For each path np.paths i : LatticePath, we build an LGV path using buildVertices.
    --
    -- First, we need N ≥ 1 for the buildVertices lemmas
    by_cases hM : M = 0
    · -- If M = 0, there are no path indices.
      subst hM
      -- Construct the trivial PathTuple (no paths)
      let pt : LGV.PathTuple LGV.integerLattice 0
          (jacobiTrudiSourceVertexRect mu) (jacobiTrudiTargetVertexRect N lam) :=
        ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
      use pt
      refine ⟨?_, ?_⟩
      · -- pt is in nipatFinset
        simp only [LGV.mem_nipatFinset_iff, LGV.PathTuple.isNonIntersecting]
        exact fun i => Fin.elim0 i
      · -- pathTupleToNipat pt = np
        simp only [pathTupleToRectNipat]
        cases np with | mk paths colStrict =>
        congr 1
        funext i
        exact Fin.elim0 i
    · -- N ≥ 1
      have hN_pos : 0 < N := hheight hM
      have hN_ge : N ≥ 1 := hN_pos
      -- For each i, construct the LGV path from np.paths i
      -- Define the path function
      let pathFn : (i : Fin M) → LGV.SimpleDigraph.Path LGV.integerLattice := fun i =>
        let lp := np.paths i
        let a := (mu i : ℤ) - (i.val : ℤ)
        let c := (lam i : ℤ) - (i.val : ℤ)
        let vertices := buildVertices a c N lp.eastStepHeights
        let hne := buildVertices_nonempty a c N lp.eastStepHeights
        -- Need to show c - a ≥ 0 for arcs_valid
        have h_ca : 0 ≤ c - a := by
          simp only [c, a]
          have hcont := hcontained i
          omega
        let harcs := buildVertices_arcs_valid a c N lp.eastStepHeights hN_pos lp.length_eq h_ca
        ⟨vertices, hne, harcs⟩
      -- Verify start conditions
      have hstarts : ∀ i, (pathFn i).start = jacobiTrudiSourceVertexRect mu i := fun i => by
        simp only [pathFn, LGV.SimpleDigraph.Path.start]
        have hne := buildVertices_nonempty ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
            N (np.paths i).eastStepHeights
        have h := buildVertices_head ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
            N (np.paths i).eastStepHeights hN_ge
        simp only [jacobiTrudiSourceVertexRect]
        rw [← h]
      -- Verify finish conditions
      have hfinishes : ∀ i, (pathFn i).finish = jacobiTrudiTargetVertexRect N lam i := fun i => by
        simp only [pathFn, LGV.SimpleDigraph.Path.finish]
        have h_ca : 0 ≤ ((lam i : ℤ) - (i.val : ℤ)) - ((mu i : ℤ) - (i.val : ℤ)) := by
          have hcont := hcontained i
          omega
        have hne := buildVertices_nonempty ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
            N (np.paths i).eastStepHeights
        have h := buildVertices_getLast ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
            N (np.paths i).eastStepHeights hN_pos (np.paths i).length_eq h_ca
            (np.paths i).weaklyIncreasing
        simp only [jacobiTrudiTargetVertexRect]
        rw [← h]
      -- Construct the PathTuple
      let pt : LGV.PathTuple LGV.integerLattice M
          (jacobiTrudiSourceVertexRect mu) (jacobiTrudiTargetVertexRect N lam) :=
        ⟨pathFn, hstarts, hfinishes⟩
      -- Show pt is non-intersecting
      have hni : pt.isNonIntersecting := by
        -- Non-intersection follows from column-strictness
        -- If paths i and j share a vertex (x, y), then at the same x-coordinate,
        -- both paths have the same y-coordinate. This means they have east-steps
        -- at the same column with the same height, violating column-strictness.
        intro i j hij hinter
        simp only [LGV.pathsIntersect] at hinter
        obtain ⟨⟨x, y⟩, hi_mem, hj_mem⟩ := hinter
        -- WLOG assume i < j (use lt_or_gt_of_ne)
        rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
        · -- Case i < j
          -- The shared vertex (x, y) means both paths pass through (x, y)
          -- This contradicts column-strictness via the following argument:
          --
          -- 1. Path i starts at (mu_i - i, 1), path j starts at (mu_j - j, 1)
          -- 2. Since mu is weakly decreasing and i < j, we have mu_i ≥ mu_j
          -- 3. Therefore mu_i - i > mu_j - j (path i starts to the RIGHT of path j)
          --
          -- 4. If (x, y) is shared, then x = (mu_i - i) + k_i = (mu_j - j) + k_j
          --    for some k_i < heights_i.length and k_j < heights_j.length
          -- 5. From mu_i - i > mu_j - j and x equal, we get k_i < k_j
          --
          -- 6. For buildVertices, at x-coordinate x = a + k:
          --    - The path has vertices with y in range [heights[k-1].val+1, heights[k].val+1]
          --    - Where heights[-1] is interpreted as 0 (so range starts at 1)
          --
          -- 7. For the ranges to overlap (sharing y), we need:
          --    heights_i[k_i].val + 1 ≥ heights_j[k_j-1].val + 1  (i's upper ≥ j's lower)
          --    heights_j[k_j].val + 1 ≥ heights_i[k_i-1].val + 1  (j's upper ≥ i's lower)
          --
          -- 8. But column-strictness at tableau column mu_i + k_i = mu_j + k_j - (j - i)
          --    gives constraints that make overlap impossible.
          --
          -- The proof uses the converse direction: isNonIntersecting_implies_colStrictPaths
          -- shows that non-intersection implies column-strictness. Here we show that
          -- column-strictness implies non-intersection by contrapositive.
          --
          -- Key insight: At x = mu_i - i (start of path i), path i is at y = 1.
          -- Path j at this x-coordinate must be at y > 1 (by column-strictness).
          -- Since both paths are monotone in y along x, and path j is above path i
          -- at x = mu_i - i, path j stays above path i at all shared x-coordinates.
          -- Therefore, they cannot share a vertex.
          exfalso
          -- Path i starts at (mu i - i, 1), ends at (lam i - i, N)
          have hstart_i : (pathFn i).start = ((mu i : ℤ) - (i.val : ℤ), 1) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.start]
            exact buildVertices_head _ _ N _ hN_ge
          have hfinish_i : (pathFn i).finish = ((lam i : ℤ) - (i.val : ℤ), (N : ℤ)) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.finish]
            have h_ca : 0 ≤ ((lam i : ℤ) - (i.val : ℤ)) - ((mu i : ℤ) - (i.val : ℤ)) := by
              have hcont := hcontained i; omega
            exact buildVertices_getLast _ _ N _ hN_pos (np.paths i).length_eq h_ca
                (np.paths i).weaklyIncreasing
          -- Path j starts at (mu j - j, 1), ends at (lam j - j, N)
          have hstart_j : (pathFn j).start = ((mu j : ℤ) - (j.val : ℤ), 1) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.start]
            exact buildVertices_head _ _ N _ hN_ge
          have hfinish_j : (pathFn j).finish = ((lam j : ℤ) - (j.val : ℤ), (N : ℤ)) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.finish]
            have h_ca : 0 ≤ ((lam j : ℤ) - (j.val : ℤ)) - ((mu j : ℤ) - (j.val : ℤ)) := by
              have hcont := hcontained j; omega
            exact buildVertices_getLast _ _ N _ hN_pos (np.paths j).length_eq h_ca
                (np.paths j).weaklyIncreasing
          -- Note: pt.paths = pathFn, so we can use hi_mem and hj_mem directly
          simp only [pt] at hi_mem hj_mem
          -- Get bounds on x for the shared vertex (x, y)
          -- From path i: mu_i - i ≤ x ≤ lam_i - i
          have hi_mem' := List.mem_iff_get.mp hi_mem
          obtain ⟨⟨idx_i, hidx_i⟩, heq_i⟩ := hi_mem'
          have hbd_i := LGV.integerLattice_path_vertices_bounded (pathFn i) idx_i hidx_i
          rw [hstart_i, hfinish_i] at hbd_i
          -- heq_i : (pathFn i).vertices.get ⟨idx_i, hidx_i⟩ = (x, y)
          have heq_i_x : ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 = x := by
            rw [heq_i]
          have heq_i_y : ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).2 = y := by
            rw [heq_i]
          have hx_lo_i : (mu i : ℤ) - (i.val : ℤ) ≤ x := by rw [← heq_i_x]; exact hbd_i.1
          have hx_hi_i : x ≤ (lam i : ℤ) - (i.val : ℤ) := by rw [← heq_i_x]; exact hbd_i.2.1
          -- From path j: mu_j - j ≤ x ≤ lam_j - j
          have hj_mem' := List.mem_iff_get.mp hj_mem
          obtain ⟨⟨idx_j, hidx_j⟩, heq_j⟩ := hj_mem'
          have hbd_j := LGV.integerLattice_path_vertices_bounded (pathFn j) idx_j hidx_j
          rw [hstart_j, hfinish_j] at hbd_j
          have heq_j_x : ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).1 = x := by
            rw [heq_j]
          have heq_j_y : ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).2 = y := by
            rw [heq_j]
          have hx_lo_j : (mu j : ℤ) - (j.val : ℤ) ≤ x := by rw [← heq_j_x]; exact hbd_j.1
          have hx_hi_j : x ≤ (lam j : ℤ) - (j.val : ℤ) := by rw [← heq_j_x]; exact hbd_j.2.1
          -- Case split: is path i a vertical line (lam_i = mu_i)?
          by_cases hvert : lam i = mu i
          · -- Case A: path i is vertical at x = mu_i - i
            -- From hx_lo_i and hx_hi_i with lam_i = mu_i: x = mu_i - i
            have hx_eq : x = (mu i : ℤ) - (i.val : ℤ) := by omega
            -- From hlam: lam_j ≤ lam_i = mu_i
            have hlam_j : lam j ≤ lam i := hlam i j (Fin.le_of_lt hij_lt)
            -- Since j > i and lam_j ≤ mu_i: lam_j - j < mu_i - i
            have hcontra : (lam j : ℤ) - (j.val : ℤ) < (mu i : ℤ) - (i.val : ℤ) := by
              omega
            -- But x ≤ lam_j - j and x = mu_i - i, contradiction
            omega
          · -- Case B: path i has east steps (lam_i > mu_i)
            -- Column-strictness ensures path j is above path i at their common x-range
            push_neg at hvert
            have hlam_gt : lam i > mu i := Nat.lt_of_le_of_ne (hcontained i) (Ne.symm hvert)
            -- Path i starts strictly to the right of path j
            have hstart_lt : (mu j : ℤ) - (j.val : ℤ) < (mu i : ℤ) - (i.val : ℤ) := by
              have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij_lt)
              omega
            -- Key insight: At x = mu_i - i (start of path i), path i is at y = 1.
            -- Path j at this x must be at y > 1 by column-strictness.
            -- Using paths_above_at_x_stays_above, path j stays above path i at all x.
            -- But they share (x, y), so y_j = y_i = y, contradiction.
            --
            -- The proof requires showing that at any x where both paths have vertices,
            -- path j's y-coordinate is strictly greater than path i's y-coordinate.
            -- This follows from:
            -- 1. At x₀ = mu_i - i (start of path i), path i has y = 1
            -- 2. Path j at x₀ has y > 1 (by column-strictness: heights_j[m-1] > heights_i[0] ≥ 0)
            -- 3. By discrete IVT, if paths share (x, y) with x ≥ x₀, then the "above" property
            --    at x₀ combined with y_j = y_i at x implies paths share a vertex at some x' ≤ x.
            -- 4. This shared vertex contradicts the "above" property.
            --
            -- The detailed proof requires careful vertex analysis using buildVertices structure
            -- and the lgvPathEastStepYCoords lemmas. The key column-strictness argument:
            -- - At x₀, path j has taken m = (mu_i - mu_j) + (j - i) east steps
            -- - Column-strictness at column mu_i: heights_i[0] < heights_j[mu_i - mu_j]
            -- - Since m - 1 ≥ mu_i - mu_j and heights are weakly increasing:
            --   heights_j[m-1] ≥ heights_j[mu_i - mu_j] > heights_i[0] ≥ 0
            -- - So heights_j[m-1] ≥ 1, meaning path j is at y ≥ 2 > 1 at x₀
            --
            -- Detailed proof:
            -- The shared vertex (x, y) satisfies:
            -- - mu_i - i ≤ x ≤ lam_i - i (from path i bounds)
            -- - mu_j - j ≤ x ≤ lam_j - j (from path j bounds)
            -- Let k = x - (mu_i - i) be the number of east steps path i has taken to reach x.
            -- Let k' = x - (mu_j - j) be the number of east steps path j has taken to reach x.
            -- Then k' = k + (mu_i - mu_j) + (j - i).
            --
            -- At x, path i has y in range [heights_i[k-1].val + 1, heights_i[k].val + 1]
            -- (with heights_i[-1] = 0 for k = 0).
            -- At x, path j has y in range [heights_j[k'-1].val + 1, heights_j[k'].val + 1].
            --
            -- For paths to share y at x, these ranges must overlap:
            -- heights_j[k'-1].val + 1 ≤ heights_i[k].val + 1 (j's lower ≤ i's upper)
            --
            -- But by column-strictness (with tableau column mu_i + k = mu_j + (k' - (j - i))):
            -- heights_i[k] < heights_j[k' - (j - i)] = heights_j[(mu_i - mu_j) + k]
            --
            -- Since heights are weakly increasing and k' - 1 ≥ (mu_i - mu_j) + k:
            -- heights_j[k'-1] ≥ heights_j[(mu_i - mu_j) + k] > heights_i[k]
            --
            -- This contradicts heights_j[k'-1] ≤ heights_i[k] (from range overlap).
            --
            -- The technical challenge is extracting k from the vertex membership and
            -- relating it to the eastStepHeights structure. This requires the
            -- buildVertices_y_at_x infrastructure.
            --
            -- Proof using sum-based reasoning:
            -- At shared vertex (x, y), both paths have the same x + y value.
            -- The sum x + y = start_sum + idx, where idx is the vertex index.
            -- For path i: x + y = (mu_i - i + 1) + idx_i
            -- For path j: x + y = (mu_j - j + 1) + idx_j
            -- So idx_j - idx_i = (mu_i - mu_j) + (j - i)
            --
            -- The number of east steps k = x - start_x.
            -- For path i: k_i = x - (mu_i - i)
            -- For path j: k_j = x - (mu_j - j) = k_i + (mu_i - mu_j) + (j - i)
            --
            -- The y-coordinate y = 1 + (idx - k) (number of north steps + 1).
            -- Since y is the same for both: idx_i - k_i = idx_j - k_j = y - 1
            --
            -- Key constraint: at a vertex with k east steps and y-coordinate y,
            -- we have heights[k-1] < y - 1 ≤ heights[k] (for k > 0), or
            -- 0 ≤ y - 1 ≤ heights[0] (for k = 0).
            --
            -- For paths to share (x, y):
            -- - Path i: y - 1 ≤ heights_i[k_i] (upper bound)
            -- - Path j: y - 1 > heights_j[k_j - 1] (lower bound, for k_j > 0)
            --
            -- Actually, the constraint is: heights[k-1] + 1 ≤ y ≤ heights[k] + 1
            -- i.e., heights[k-1] ≤ y - 1 ≤ heights[k]
            --
            -- For overlap: heights_j[k_j-1] ≤ y - 1 ≤ heights_i[k_i]
            -- So heights_j[k_j-1] ≤ heights_i[k_i]
            --
            -- But by column-strictness: heights_i[k_i] < heights_j[k_i + (mu_i - mu_j)]
            -- And since k_j - 1 ≥ k_i + (mu_i - mu_j) and heights_j weakly increasing:
            -- heights_j[k_j-1] ≥ heights_j[k_i + (mu_i - mu_j)] > heights_i[k_i]
            -- Contradiction!
            --
            -- Define k_i and k_j
            let k_i := (x - ((mu i : ℤ) - (i.val : ℤ))).toNat
            let k_j := (x - ((mu j : ℤ) - (j.val : ℤ))).toNat
            -- Show k_j = k_i + (mu_i - mu_j) + (j - i)
            have hk_rel : k_j = k_i + (mu i - mu j) + (j.val - i.val) := by
              simp only [k_i, k_j]
              have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij_lt)
              have hx_ge_i : x ≥ (mu i : ℤ) - (i.val : ℤ) := hx_lo_i
              have hx_ge_j : x ≥ (mu j : ℤ) - (j.val : ℤ) := hx_lo_j
              omega
            -- Show k_i < heights_i.length
            have hk_i_lt : k_i < (np.paths i).eastStepHeights.length := by
              simp only [k_i]
              have hlen := (np.paths i).length_eq
              simp only [sub_sub_sub_cancel_right] at hlen
              have hcont := hcontained i
              have hx_hi : x ≤ (lam i : ℤ) - (i.val : ℤ) := hx_hi_i
              have hx_ge : x ≥ (mu i : ℤ) - (i.val : ℤ) := hx_lo_i
              -- x ≤ lam_j - j < lam_i - i (since lam_j ≤ lam_i and j > i)
              have hlam_ji : lam j ≤ lam i := hlam i j (Fin.le_of_lt hij_lt)
              have hx_lt : x < (lam i : ℤ) - (i.val : ℤ) := by
                have h1 : x ≤ (lam j : ℤ) - (j.val : ℤ) := hx_hi_j
                omega
              have hnneg : (lam i : ℤ) - (mu i : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
              have hlt : x - ((mu i : ℤ) - (i.val : ℤ)) < (lam i : ℤ) - (mu i : ℤ) := by omega
              rw [hlen]
              have h1 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg2
              have h2 : (((lam i : ℤ) - (mu i : ℤ)).toNat : ℤ) = (lam i : ℤ) - (mu i : ℤ) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Show k_i + (mu_i - mu_j) < heights_j.length (for column-strictness)
            have hk_col_lt : k_i + (mu i - mu j) < (np.paths j).eastStepHeights.length := by
              simp only [k_i]
              have hlen := (np.paths j).length_eq
              simp only [sub_sub_sub_cancel_right] at hlen
              have hx_hi : x ≤ (lam j : ℤ) - (j.val : ℤ) := hx_hi_j
              have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij_lt)
              have hcont := hcontained j
              have hx_ge : x ≥ (mu i : ℤ) - (i.val : ℤ) := hx_lo_i
              have hnneg : (lam j : ℤ) - (mu j : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
              have hlt : x - ((mu i : ℤ) - (i.val : ℤ)) + ((mu i : ℤ) - (mu j : ℤ)) < (lam j : ℤ) - (mu j : ℤ) := by omega
              rw [hlen]
              have h1 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg2
              have h2 : (((lam j : ℤ) - (mu j : ℤ)).toNat : ℤ) = (lam j : ℤ) - (mu j : ℤ) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Show k_j > 0 (path j has taken at least one east step to reach x)
            have hk_j_pos : k_j > 0 := by
              simp only [k_j]
              have hx_ge : x ≥ (mu i : ℤ) - (i.val : ℤ) := hx_lo_i
              have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij_lt)
              omega
            -- Show k_j - 1 ≥ k_i + (mu_i - mu_j)
            have hk_j_ge : k_j - 1 ≥ k_i + (mu i - mu j) := by
              rw [hk_rel]
              have hij_pos : j.val - i.val ≥ 1 := Nat.sub_pos_of_lt hij_lt
              omega
            -- Apply column-strictness at column mu_i + k_i
            have hcol_eq : mu i + k_i = mu j + (k_i + (mu i - mu j)) := by
              have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij_lt)
              omega
            have hcolstrict := np.colStrictPaths i j hij_lt k_i hk_i_lt
                (k_i + (mu i - mu j)) hk_col_lt hcol_eq
            -- Apply weakly increasing property of heights_j
            have hk_j_lt : k_j - 1 < (np.paths j).eastStepHeights.length := by
              have hlen : (np.paths j).eastStepHeights.length = lam j - mu j := by
                have h := (np.paths j).length_eq
                simp only [sub_sub_sub_cancel_right] at h
                have hcont := hcontained j
                omega
              rw [hlen]
              simp only [k_j]
              have hx_hi : x ≤ (lam j : ℤ) - (j.val : ℤ) := hx_hi_j
              have hcont := hcontained j
              omega
            have hweakly := List.IsChain.getElem_le_getElem_of_le (np.paths j).weaklyIncreasing
                hk_col_lt hk_j_lt hk_j_ge
            -- Derive: heights_j[k_j-1] > heights_i[k_i]
            have hcontra : (np.paths j).eastStepHeights[k_j - 1] > (np.paths i).eastStepHeights[k_i] :=
              lt_of_lt_of_le hcolstrict hweakly
            -- Now we need to show this contradicts the shared vertex
            -- The shared vertex (x, y) requires y to be in both paths' y-ranges
            -- For path i at x: y ≤ heights_i[k_i] + 1
            -- For path j at x: y > heights_j[k_j-1] + 1 (actually y ≥ heights_j[k_j-1] + 1)
            --
            -- Wait, the ranges are:
            -- Path i at x: heights_i[k_i-1] + 1 ≤ y ≤ heights_i[k_i] + 1
            -- Path j at x: heights_j[k_j-1] + 1 ≤ y ≤ heights_j[k_j] + 1
            --
            -- For overlap: heights_j[k_j-1] + 1 ≤ heights_i[k_i] + 1
            -- i.e., heights_j[k_j-1] ≤ heights_i[k_i]
            --
            -- But hcontra says heights_j[k_j-1] > heights_i[k_i]
            -- So the ranges don't overlap, contradiction!
            --
            -- To formalize this, we need lemmas about the y-range at each x.
            -- For now, we use the sum-based approach with lgvPathEastStepYCoords.
            --
            -- At the shared vertex (x, y):
            -- - For path i: y is the y-coordinate at some vertex with x-coordinate x
            -- - The y-coordinate at the k_i-th east step is heights_i[k_i] + 1
            -- - All vertices at x have y ≤ heights_i[k_i] + 1
            --
            -- Similarly for path j: y ≥ heights_j[k_j-1] + 1 (for k_j > 0)
            --
            -- So heights_j[k_j-1] + 1 ≤ y ≤ heights_i[k_i] + 1
            -- i.e., heights_j[k_j-1] ≤ heights_i[k_i]
            --
            -- But hcontra says heights_j[k_j-1] > heights_i[k_i], contradiction!
            --
            -- The formal proof requires establishing the y-bounds, which needs
            -- additional lemmas about buildVertices. For now, we note that
            -- the key inequality hcontra is established, and the y-bound
            -- lemmas are the remaining infrastructure needed.
            --
            -- Use the sum-based reasoning to derive contradiction
            -- At shared vertex (x, y), both paths have sum x + y
            -- Path i: sum = (mu_i - i) + 1 + idx_i, so idx_i = x + y - (mu_i - i) - 1
            -- Path j: sum = (mu_j - j) + 1 + idx_j, so idx_j = x + y - (mu_j - j) - 1
            --
            -- The number of north steps is idx - k = (x + y - start - 1) - (x - start) = y - 1
            -- So at vertex (x, y), the path has taken y - 1 north steps.
            --
            -- The constraint from buildVertices:
            -- After k east steps and n north steps (n = idx - k = y - 1), we have:
            -- - The k-th east step happens at y = heights[k] + 1
            -- - So after k east steps, y ≤ heights[k] + 1, i.e., y - 1 ≤ heights[k]
            -- - Before the k-th east step (if k > 0), y ≥ heights[k-1] + 1, i.e., y - 1 ≥ heights[k-1]
            --
            -- For path i at (x, y): y - 1 ≤ heights_i[k_i]
            -- For path j at (x, y): y - 1 ≥ heights_j[k_j - 1] (since k_j > 0)
            --
            -- So heights_j[k_j - 1] ≤ y - 1 ≤ heights_i[k_i]
            -- This gives heights_j[k_j - 1] ≤ heights_i[k_i]
            --
            -- But hcontra says heights_j[k_j - 1] > heights_i[k_i]
            -- Contradiction!
            --
            -- To formalize, we need to prove:
            -- 1. For path i at (x, y): (y - 1).toNat ≤ heights_i[k_i].val
            -- 2. For path j at (x, y): heights_j[k_j - 1].val ≤ (y - 1).toNat
            --
            -- These follow from the buildVertices structure, but require careful
            -- analysis. For now, we use omega to derive the contradiction from
            -- the established inequalities.
            --
            -- The y-coordinate y satisfies 1 ≤ y ≤ N (from path bounds)
            have hy_ge : y ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded (pathFn i) idx_i hidx_i
              have h := hbd.2.2.1
              rw [hstart_i] at h
              rw [heq_i_y] at h
              exact h
            have hy_le : y ≤ N := by
              have hbd := LGV.integerLattice_path_vertices_bounded (pathFn i) idx_i hidx_i
              have h := hbd.2.2.2
              rw [hfinish_i] at h
              rw [heq_i_y] at h
              exact h
            -- The y-1 value is in [0, N-1], which is the range of Fin N values
            -- heights_i[k_i] and heights_j[k_j-1] are Fin N values
            -- We need to show: heights_j[k_j-1].val > heights_i[k_i].val
            -- This follows directly from hcontra (Fin comparison is by val)
            have hval_contr : (np.paths j).eastStepHeights[k_j - 1].val >
                              (np.paths i).eastStepHeights[k_i].val := hcontra
            -- Apply y-bound lemmas to derive contradiction
            -- For path i at (x, y): y ≤ heights_i[k_i].val + 1
            -- For path j at (x, y): y ≥ heights_j[k_j-1].val + 1
            --
            -- Set up for buildVertices_y_upper_bound_at_x on path i
            let a_i := (mu i : ℤ) - (i.val : ℤ)
            let c_i := (lam i : ℤ) - (i.val : ℤ)
            have h_ca_i : 0 ≤ c_i - a_i := by
              simp only [c_i, a_i]; have hcont := hcontained i; omega
            -- (pathFn i).vertices = buildVertices a_i c_i N (np.paths i).eastStepHeights
            have hvertices_i : (pathFn i).vertices = buildVertices a_i c_i N (np.paths i).eastStepHeights := by
              simp only [pathFn, a_i, c_i]
            -- hidx_i : idx_i < (pathFn i).vertices.length
            have hidx_i' : idx_i < (buildVertices a_i c_i N (np.paths i).eastStepHeights).length := by
              rw [← hvertices_i]; exact hidx_i
            -- heq_i_x says ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 = x
            -- We need: (buildVertices a_i c_i N heights_i)[idx_i].1 = a_i + k_i
            have hx_eq_i : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 = a_i + k_i := by
              have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 =
                  ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 := by
                simp only [hvertices_i, List.get_eq_getElem]
              rw [h1, heq_i_x]
              simp only [k_i, a_i]
              have hnneg : x - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
              have h2 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Apply buildVertices_y_upper_bound_at_x
            have hy_upper : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].2 ≤
                ((np.paths i).eastStepHeights[k_i]).val + 1 :=
              buildVertices_y_upper_bound_at_x a_i c_i N (np.paths i).eastStepHeights hN_pos
                (np.paths i).length_eq h_ca_i (np.paths i).weaklyIncreasing idx_i hidx_i' k_i hk_i_lt hx_eq_i
            -- Convert to y ≤ heights_i[k_i].val + 1
            have hy_upper' : y ≤ ((np.paths i).eastStepHeights[k_i]).val + 1 := by
              have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].2 =
                  ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).2 := by
                simp only [hvertices_i, List.get_eq_getElem]
              rw [h1, heq_i_y] at hy_upper
              exact hy_upper
            -- Set up for buildVertices_y_lower_bound_at_x on path j
            let a_j := (mu j : ℤ) - (j.val : ℤ)
            let c_j := (lam j : ℤ) - (j.val : ℤ)
            have h_ca_j : 0 ≤ c_j - a_j := by
              simp only [c_j, a_j]; have hcont := hcontained j; omega
            have hvertices_j : (pathFn j).vertices = buildVertices a_j c_j N (np.paths j).eastStepHeights := by
              simp only [pathFn, a_j, c_j]
            have hidx_j' : idx_j < (buildVertices a_j c_j N (np.paths j).eastStepHeights).length := by
              rw [← hvertices_j]; exact hidx_j
            have hx_eq_j : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 = a_j + k_j := by
              have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 =
                  ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).1 := by
                simp only [hvertices_j, List.get_eq_getElem]
              rw [h1, heq_j_x]
              simp only [k_j, a_j]
              have hnneg : x - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
              have h2 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Need k_j < heights_j.length for the lower bound lemma
            -- We have k_j - 1 < heights_j.length from hk_j_lt
            -- If k_j = heights_j.length, then x = lam_j - j (endpoint of path j)
            -- At the endpoint, path j has y = N. But path i at x has y ≤ heights_i[k_i] + 1.
            -- Since x ≤ lam_i - i (from path i bounds) and lam_j - j < lam_i - i (from i < j, lam decreasing),
            -- if x = lam_j - j, then x < lam_i - i, so path i hasn't reached its endpoint.
            -- This means y < N for path i (since only the endpoint has y = N).
            -- Contradiction: y = N (from path j) and y < N (from path i).
            have hk_j_strict : k_j < (np.paths j).eastStepHeights.length := by
              have hlen : (np.paths j).eastStepHeights.length = lam j - mu j := by
                have h := (np.paths j).length_eq
                simp only [sub_sub_sub_cancel_right] at h
                have hcont := hcontained j
                omega
              rw [hlen]
              simp only [k_j]
              have hx_hi : x ≤ (lam j : ℤ) - (j.val : ℤ) := hx_hi_j
              have hcont := hcontained j
              have hnneg : (lam j : ℤ) - (mu j : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
              by_cases hx_eq : x = (lam j : ℤ) - (j.val : ℤ)
              · -- If x = lam_j - j, derive contradiction
                exfalso
                -- At x = lam_j - j, k_j = heights_j.length
                have hk_j_eq : k_j = lam j - mu j := by
                  simp only [k_j, hx_eq]
                  have hnneg3 : (lam j : ℤ) - (j.val : ℤ) - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
                  omega
                have hlen_j : (np.paths j).eastStepHeights.length = lam j - mu j := hlen
                -- Use the upper bound from path i: y ≤ heights_i[k_i] + 1
                have hy_upper_i := hy_upper'
                -- heights_j[k_j - 1] > heights_i[k_i]
                have hcontra_val : (np.paths j).eastStepHeights[k_j - 1].val > (np.paths i).eastStepHeights[k_i].val := hcontra
                -- At x = lam_j - j, k_j - 1 = heights_j.length - 1
                have hk_j_minus_1 : k_j - 1 = (np.paths j).eastStepHeights.length - 1 := by
                  rw [hk_j_eq, hlen_j]
                -- At x = lam_j - j, path j is in its last column
                -- All vertices in this column have y ≥ heights_j[last] + 1
                have hlen_pos : 0 < (np.paths j).eastStepHeights.length := by
                  rw [hlen_j]; omega
                have hy_ge_last : y ≥ ((np.paths j).eastStepHeights[(np.paths j).eastStepHeights.length - 1]).val + 1 := by
                  -- At x = a_j + heights_j.length, path j is in its last column
                  -- The y-coordinate is at least heights_j[last] + 1
                  -- Use buildVertices_y_lower_bound_at_last_column
                  have hx_eq_j_last : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 =
                      a_j + (np.paths j).eastStepHeights.length := by
                    have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 =
                        ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).1 := by
                      simp only [hvertices_j, List.get_eq_getElem]
                    rw [h1, heq_j_x, hx_eq]
                    simp only [a_j, hlen_j]
                    omega
                  have hy_lower_last := buildVertices_y_lower_bound_at_last_column a_j c_j N
                    (np.paths j).eastStepHeights hN_pos (np.paths j).length_eq h_ca_j
                    (np.paths j).weaklyIncreasing hlen_pos idx_j hidx_j' hx_eq_j_last
                  have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].2 =
                      ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).2 := by
                    simp only [hvertices_j, List.get_eq_getElem]
                  rw [h1, heq_j_y] at hy_lower_last
                  exact hy_lower_last
                have hcontra_val' : (np.paths j).eastStepHeights[(np.paths j).eastStepHeights.length - 1].val >
                    (np.paths i).eastStepHeights[k_i].val := by
                  have h : k_j - 1 = (np.paths j).eastStepHeights.length - 1 := hk_j_minus_1
                  simp only [h] at hcontra_val
                  exact hcontra_val
                omega
              · -- x < lam_j - j, so k_j < lam_j - mu_j = heights.length
                have hx_lt : x < (lam j : ℤ) - (j.val : ℤ) := by
                  have h := hx_hi; omega
                have h1 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                  Int.toNat_of_nonneg hnneg2
                have h2 : (((lam j : ℤ) - (mu j : ℤ)).toNat : ℤ) = (lam j : ℤ) - (mu j : ℤ) :=
                  Int.toNat_of_nonneg hnneg
                omega
            -- Apply buildVertices_y_lower_bound_at_x
            have hy_lower : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].2 ≥
                ((np.paths j).eastStepHeights[k_j - 1]).val + 1 :=
              buildVertices_y_lower_bound_at_x a_j c_j N (np.paths j).eastStepHeights hN_pos
                (np.paths j).length_eq h_ca_j (np.paths j).weaklyIncreasing idx_j hidx_j' k_j hk_j_strict hk_j_pos hx_eq_j
            -- Convert to y ≥ heights_j[k_j-1].val + 1
            have hy_lower' : y ≥ ((np.paths j).eastStepHeights[k_j - 1]).val + 1 := by
              have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].2 =
                  ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).2 := by
                simp only [hvertices_j, List.get_eq_getElem]
              rw [h1, heq_j_y] at hy_lower
              exact hy_lower
            -- Combine: heights_j[k_j-1].val + 1 ≤ y ≤ heights_i[k_i].val + 1
            -- So heights_j[k_j-1].val ≤ heights_i[k_i].val
            -- But hval_contr says heights_j[k_j-1].val > heights_i[k_i].val
            omega
        · -- Case j < i: symmetric argument (swap i and j)
          exfalso
          -- Path j starts at (mu j - j, 1), ends at (lam j - j, N)
          have hstart_j : (pathFn j).start = ((mu j : ℤ) - (j.val : ℤ), 1) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.start]
            exact buildVertices_head _ _ N _ hN_ge
          have hfinish_j : (pathFn j).finish = ((lam j : ℤ) - (j.val : ℤ), (N : ℤ)) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.finish]
            have h_ca : 0 ≤ ((lam j : ℤ) - (j.val : ℤ)) - ((mu j : ℤ) - (j.val : ℤ)) := by
              have hcont := hcontained j; omega
            exact buildVertices_getLast _ _ N _ hN_pos (np.paths j).length_eq h_ca
                (np.paths j).weaklyIncreasing
          -- Path i starts at (mu i - i, 1), ends at (lam i - i, N)
          have hstart_i : (pathFn i).start = ((mu i : ℤ) - (i.val : ℤ), 1) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.start]
            exact buildVertices_head _ _ N _ hN_ge
          have hfinish_i : (pathFn i).finish = ((lam i : ℤ) - (i.val : ℤ), (N : ℤ)) := by
            simp only [pathFn, LGV.SimpleDigraph.Path.finish]
            have h_ca : 0 ≤ ((lam i : ℤ) - (i.val : ℤ)) - ((mu i : ℤ) - (i.val : ℤ)) := by
              have hcont := hcontained i; omega
            exact buildVertices_getLast _ _ N _ hN_pos (np.paths i).length_eq h_ca
                (np.paths i).weaklyIncreasing
          -- Note: pt.paths = pathFn, so we can use hi_mem and hj_mem directly
          simp only [pt] at hi_mem hj_mem
          -- Get bounds on x for the shared vertex (x, y)
          -- From path j: mu_j - j ≤ x ≤ lam_j - j
          have hj_mem' := List.mem_iff_get.mp hj_mem
          obtain ⟨⟨idx_j, hidx_j⟩, heq_j⟩ := hj_mem'
          have hbd_j := LGV.integerLattice_path_vertices_bounded (pathFn j) idx_j hidx_j
          rw [hstart_j, hfinish_j] at hbd_j
          have heq_j_x : ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).1 = x := by
            rw [heq_j]
          have heq_j_y : ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).2 = y := by
            rw [heq_j]
          have hx_lo_j : (mu j : ℤ) - (j.val : ℤ) ≤ x := by rw [← heq_j_x]; exact hbd_j.1
          have hx_hi_j : x ≤ (lam j : ℤ) - (j.val : ℤ) := by rw [← heq_j_x]; exact hbd_j.2.1
          -- From path i: mu_i - i ≤ x ≤ lam_i - i
          have hi_mem' := List.mem_iff_get.mp hi_mem
          obtain ⟨⟨idx_i, hidx_i⟩, heq_i⟩ := hi_mem'
          have hbd_i := LGV.integerLattice_path_vertices_bounded (pathFn i) idx_i hidx_i
          rw [hstart_i, hfinish_i] at hbd_i
          have heq_i_x : ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 = x := by
            rw [heq_i]
          have heq_i_y : ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).2 = y := by
            rw [heq_i]
          have hx_lo_i : (mu i : ℤ) - (i.val : ℤ) ≤ x := by rw [← heq_i_x]; exact hbd_i.1
          have hx_hi_i : x ≤ (lam i : ℤ) - (i.val : ℤ) := by rw [← heq_i_x]; exact hbd_i.2.1
          -- Case split: is path j a vertical line (lam_j = mu_j)?
          by_cases hvert : lam j = mu j
          · -- Case A: path j is vertical at x = mu_j - j
            -- From hx_lo_j and hx_hi_j with lam_j = mu_j: x = mu_j - j
            have hx_eq : x = (mu j : ℤ) - (j.val : ℤ) := by omega
            -- From hlam: lam_i ≤ lam_j = mu_j
            have hlam_i : lam i ≤ lam j := hlam j i (Fin.le_of_lt hji_lt)
            -- Since i > j and lam_i ≤ mu_j: lam_i - i < mu_j - j
            have hcontra : (lam i : ℤ) - (i.val : ℤ) < (mu j : ℤ) - (j.val : ℤ) := by
              omega
            -- But x ≤ lam_i - i and x = mu_j - j, contradiction
            omega
          · -- Case B: path j has east steps (lam_j > mu_j)
            -- This case requires the path_above_stays_above infrastructure
            -- Column-strictness ensures path i is above path j at their common x-range
            push_neg at hvert
            have hlam_gt : lam j > mu j := Nat.lt_of_le_of_ne (hcontained j) (Ne.symm hvert)
            -- Path j starts strictly to the right of path i
            have hstart_lt : (mu i : ℤ) - (i.val : ℤ) < (mu j : ℤ) - (j.val : ℤ) := by
              have hmu_ji : mu i ≤ mu j := hmu j i (Fin.le_of_lt hji_lt)
              omega
            -- The x-coordinate x is in the range where both paths overlap
            -- At x = mu_j - j (start of path j), path j is at y = 1
            -- Path i at this x must be at y > 1 by column-strictness
            -- Using path_above_stays_above, path i stays above path j
            -- But they share (x, y), so y_i = y_j = y, contradiction
            --
            -- Detailed proof (symmetric to Case i < j):
            -- The shared vertex (x, y) satisfies:
            -- - mu_j - j ≤ x ≤ lam_j - j (from path j bounds)
            -- - mu_i - i ≤ x ≤ lam_i - i (from path i bounds)
            -- Let k = x - (mu_j - j) be the number of east steps path j has taken to reach x.
            -- Let k' = x - (mu_i - i) be the number of east steps path i has taken to reach x.
            -- Then k' = k + (mu_j - mu_i) + (i - j).
            --
            -- At x, path j has y in range [heights_j[k-1].val + 1, heights_j[k].val + 1]
            -- (with heights_j[-1] = 0 for k = 0).
            -- At x, path i has y in range [heights_i[k'-1].val + 1, heights_i[k'].val + 1].
            --
            -- For paths to share y at x, these ranges must overlap:
            -- heights_i[k'-1].val + 1 ≤ heights_j[k].val + 1 (i's lower ≤ j's upper)
            --
            -- But by column-strictness (with j < i and tableau column mu_j + k = mu_i + (k' - (i - j))):
            -- heights_j[k] < heights_i[k' - (i - j)] = heights_i[(mu_j - mu_i) + k]
            --
            -- Since heights are weakly increasing and k' - 1 ≥ (mu_j - mu_i) + k:
            -- heights_i[k'-1] ≥ heights_i[(mu_j - mu_i) + k] > heights_j[k]
            --
            -- This contradicts heights_i[k'-1] ≤ heights_j[k] (from range overlap).
            --
            -- The technical challenge is extracting k from the vertex membership and
            -- relating it to the eastStepHeights structure. This requires the
            -- buildVertices_y_at_x infrastructure.
            --
            -- Symmetric proof to Case i < j:
            -- Define k_j and k_i (number of east steps for each path to reach x)
            let k_j := (x - ((mu j : ℤ) - (j.val : ℤ))).toNat
            let k_i := (x - ((mu i : ℤ) - (i.val : ℤ))).toNat
            -- Show k_i = k_j + (mu_j - mu_i) + (i - j)
            have hk_rel : k_i = k_j + (mu j - mu i) + (i.val - j.val) := by
              simp only [k_i, k_j]
              have hmu_ji : mu i ≤ mu j := hmu j i (Fin.le_of_lt hji_lt)
              have hx_ge_i : x ≥ (mu i : ℤ) - (i.val : ℤ) := hx_lo_i
              have hx_ge_j : x ≥ (mu j : ℤ) - (j.val : ℤ) := hx_lo_j
              have h1 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                Int.toNat_of_nonneg (by omega)
              have h2 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                Int.toNat_of_nonneg (by omega)
              omega
            -- Show k_j < heights_j.length (path j hasn't finished all east steps)
            -- In the j < i case, we have x ≤ lam_i - i < lam_j - j (since lam_i ≤ lam_j and i > j)
            -- So x < lam_j - j, which means k_j < heights_j.length
            have hk_j_lt : k_j < (np.paths j).eastStepHeights.length := by
              have hlen : (np.paths j).eastStepHeights.length = lam j - mu j := by
                have h := (np.paths j).length_eq
                simp only [sub_sub_sub_cancel_right] at h
                have hcont := hcontained j
                omega
              rw [hlen]
              simp only [k_j]
              have hx_hi : x ≤ (lam i : ℤ) - (i.val : ℤ) := hx_hi_i
              have hlam_ji : lam i ≤ lam j := hlam j i (Fin.le_of_lt hji_lt)
              have hcont := hcontained j
              have hnneg : (lam j : ℤ) - (mu j : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
              -- Key: x ≤ lam_i - i < lam_j - j
              have hx_lt_lam_j : x < (lam j : ℤ) - (j.val : ℤ) := by omega
              have h1 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg2
              have h2 : (((lam j : ℤ) - (mu j : ℤ)).toNat : ℤ) = (lam j : ℤ) - (mu j : ℤ) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Show k_j + (mu_j - mu_i) < heights_i.length (for column-strictness)
            have hk_col_lt : k_j + (mu j - mu i) < (np.paths i).eastStepHeights.length := by
              simp only [k_j]
              have hlen := (np.paths i).length_eq
              simp only [sub_sub_sub_cancel_right] at hlen
              have hx_hi : x ≤ (lam i : ℤ) - (i.val : ℤ) := hx_hi_i
              have hmu_ji : mu i ≤ mu j := hmu j i (Fin.le_of_lt hji_lt)
              have hcont := hcontained i
              have hx_ge : x ≥ (mu j : ℤ) - (j.val : ℤ) := hx_lo_j
              have hnneg : (lam i : ℤ) - (mu i : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
              have hlt : x - ((mu j : ℤ) - (j.val : ℤ)) + ((mu j : ℤ) - (mu i : ℤ)) < (lam i : ℤ) - (mu i : ℤ) := by omega
              rw [hlen]
              have h1 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg2
              have h2 : (((lam i : ℤ) - (mu i : ℤ)).toNat : ℤ) = (lam i : ℤ) - (mu i : ℤ) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Show k_i > 0 (path i has taken at least one east step to reach x)
            have hk_i_pos : k_i > 0 := by
              simp only [k_i]
              have hx_ge : x ≥ (mu j : ℤ) - (j.val : ℤ) := hx_lo_j
              have hmu_ji : mu i ≤ mu j := hmu j i (Fin.le_of_lt hji_lt)
              omega
            -- Show k_i - 1 ≥ k_j + (mu_j - mu_i)
            have hk_i_ge : k_i - 1 ≥ k_j + (mu j - mu i) := by
              rw [hk_rel]
              have hji_pos : i.val - j.val ≥ 1 := Nat.sub_pos_of_lt hji_lt
              omega
            -- Apply column-strictness at column mu_j + k_j
            have hcol_eq : mu j + k_j = mu i + (k_j + (mu j - mu i)) := by
              have hmu_ji : mu i ≤ mu j := hmu j i (Fin.le_of_lt hji_lt)
              omega
            have hcolstrict := np.colStrictPaths j i hji_lt k_j hk_j_lt
                (k_j + (mu j - mu i)) hk_col_lt hcol_eq
            -- Apply weakly increasing property of heights_i
            have hk_i_lt : k_i - 1 < (np.paths i).eastStepHeights.length := by
              have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
                have h := (np.paths i).length_eq
                simp only [sub_sub_sub_cancel_right] at h
                have hcont := hcontained i
                omega
              rw [hlen]
              simp only [k_i]
              have hx_hi : x ≤ (lam i : ℤ) - (i.val : ℤ) := hx_hi_i
              have hcont := hcontained i
              omega
            have hweakly := List.IsChain.getElem_le_getElem_of_le (np.paths i).weaklyIncreasing
                hk_col_lt hk_i_lt hk_i_ge
            -- Derive: heights_i[k_i-1] > heights_j[k_j]
            have hcontra : (np.paths i).eastStepHeights[k_i - 1] > (np.paths j).eastStepHeights[k_j] :=
              lt_of_lt_of_le hcolstrict hweakly
            -- Get y bounds
            have hy_ge : y ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded (pathFn j) idx_j hidx_j
              have h := hbd.2.2.1
              rw [hstart_j] at h
              rw [heq_j_y] at h
              exact h
            have hy_le : y ≤ N := by
              have hbd := LGV.integerLattice_path_vertices_bounded (pathFn j) idx_j hidx_j
              have h := hbd.2.2.2
              rw [hfinish_j] at h
              rw [heq_j_y] at h
              exact h
            have hval_contr : (np.paths i).eastStepHeights[k_i - 1].val >
                              (np.paths j).eastStepHeights[k_j].val := hcontra
            -- Apply y-bound lemmas to derive contradiction
            -- For path j at (x, y): y ≤ heights_j[k_j].val + 1
            -- For path i at (x, y): y ≥ heights_i[k_i-1].val + 1
            --
            -- Set up for buildVertices_y_upper_bound_at_x on path j
            let a_j := (mu j : ℤ) - (j.val : ℤ)
            let c_j := (lam j : ℤ) - (j.val : ℤ)
            have h_ca_j : 0 ≤ c_j - a_j := by
              simp only [c_j, a_j]; have hcont := hcontained j; omega
            have hvertices_j : (pathFn j).vertices = buildVertices a_j c_j N (np.paths j).eastStepHeights := by
              simp only [pathFn, a_j, c_j]
            have hidx_j' : idx_j < (buildVertices a_j c_j N (np.paths j).eastStepHeights).length := by
              rw [← hvertices_j]; exact hidx_j
            have hx_eq_j : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 = a_j + k_j := by
              have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].1 =
                  ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).1 := by
                simp only [hvertices_j, List.get_eq_getElem]
              rw [h1, heq_j_x]
              simp only [k_j, a_j]
              have hnneg : x - ((mu j : ℤ) - (j.val : ℤ)) ≥ 0 := by omega
              have h2 : ((x - ((mu j : ℤ) - (j.val : ℤ))).toNat : ℤ) = x - ((mu j : ℤ) - (j.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Apply buildVertices_y_upper_bound_at_x on path j
            have hy_upper : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].2 ≤
                ((np.paths j).eastStepHeights[k_j]).val + 1 :=
              buildVertices_y_upper_bound_at_x a_j c_j N (np.paths j).eastStepHeights hN_pos
                (np.paths j).length_eq h_ca_j (np.paths j).weaklyIncreasing idx_j hidx_j' k_j hk_j_lt hx_eq_j
            -- Convert to y ≤ heights_j[k_j].val + 1
            have hy_upper' : y ≤ ((np.paths j).eastStepHeights[k_j]).val + 1 := by
              have h1 : (buildVertices a_j c_j N (np.paths j).eastStepHeights)[idx_j].2 =
                  ((pathFn j).vertices.get ⟨idx_j, hidx_j⟩).2 := by
                simp only [hvertices_j, List.get_eq_getElem]
              rw [h1, heq_j_y] at hy_upper
              exact hy_upper
            -- Set up for buildVertices_y_lower_bound_at_x on path i
            let a_i := (mu i : ℤ) - (i.val : ℤ)
            let c_i := (lam i : ℤ) - (i.val : ℤ)
            have h_ca_i : 0 ≤ c_i - a_i := by
              simp only [c_i, a_i]; have hcont := hcontained i; omega
            have hvertices_i : (pathFn i).vertices = buildVertices a_i c_i N (np.paths i).eastStepHeights := by
              simp only [pathFn, a_i, c_i]
            have hidx_i' : idx_i < (buildVertices a_i c_i N (np.paths i).eastStepHeights).length := by
              rw [← hvertices_i]; exact hidx_i
            have hx_eq_i : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 = a_i + k_i := by
              have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 =
                  ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 := by
                simp only [hvertices_i, List.get_eq_getElem]
              rw [h1, heq_i_x]
              simp only [k_i, a_i]
              have hnneg : x - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
              have h2 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                Int.toNat_of_nonneg hnneg
              omega
            -- Need k_i < heights_i.length for the lower bound lemma
            -- Handle the edge case where x = lam_i - i (path i at endpoint)
            have hk_i_strict : k_i < (np.paths i).eastStepHeights.length := by
              have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
                have h := (np.paths i).length_eq
                simp only [sub_sub_sub_cancel_right] at h
                have hcont := hcontained i
                omega
              rw [hlen]
              simp only [k_i]
              have hx_hi : x ≤ (lam i : ℤ) - (i.val : ℤ) := hx_hi_i
              have hcont := hcontained i
              have hnneg : (lam i : ℤ) - (mu i : ℤ) ≥ 0 := by omega
              have hnneg2 : x - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
              by_cases hx_eq : x = (lam i : ℤ) - (i.val : ℤ)
              · -- If x = lam_i - i, derive contradiction
                exfalso
                -- At x = lam_i - i, k_i = heights_i.length
                have hk_i_eq : k_i = lam i - mu i := by
                  simp only [k_i, hx_eq]
                  have hnneg3 : (lam i : ℤ) - (i.val : ℤ) - ((mu i : ℤ) - (i.val : ℤ)) ≥ 0 := by omega
                  omega
                have hlen_i : (np.paths i).eastStepHeights.length = lam i - mu i := hlen
                -- Use the upper bound from path j: y ≤ heights_j[k_j] + 1
                have hy_upper_j := hy_upper'
                -- heights_i[k_i - 1] > heights_j[k_j]
                have hcontra_val : (np.paths i).eastStepHeights[k_i - 1].val > (np.paths j).eastStepHeights[k_j].val := hcontra
                -- At x = lam_i - i, k_i - 1 = heights_i.length - 1
                have hk_i_minus_1 : k_i - 1 = (np.paths i).eastStepHeights.length - 1 := by
                  rw [hk_i_eq, hlen_i]
                -- At x = lam_i - i, path i is in its last column
                -- All vertices in this column have y ≥ heights_i[last] + 1
                have hlen_pos : 0 < (np.paths i).eastStepHeights.length := by
                  rw [hlen_i]; omega
                have hy_ge_last : y ≥ ((np.paths i).eastStepHeights[(np.paths i).eastStepHeights.length - 1]).val + 1 := by
                  -- At x = a_i + heights_i.length, path i is in its last column
                  -- The y-coordinate is at least heights_i[last] + 1
                  -- Use buildVertices_y_lower_bound_at_last_column
                  have hx_eq_i_last : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 =
                      a_i + (np.paths i).eastStepHeights.length := by
                    have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].1 =
                        ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).1 := by
                      simp only [hvertices_i, List.get_eq_getElem]
                    rw [h1, heq_i_x, hx_eq]
                    simp only [a_i, hlen_i]
                    omega
                  have hy_lower_last := buildVertices_y_lower_bound_at_last_column a_i c_i N
                    (np.paths i).eastStepHeights hN_pos (np.paths i).length_eq h_ca_i
                    (np.paths i).weaklyIncreasing hlen_pos idx_i hidx_i' hx_eq_i_last
                  have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].2 =
                      ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).2 := by
                    simp only [hvertices_i, List.get_eq_getElem]
                  rw [h1, heq_i_y] at hy_lower_last
                  exact hy_lower_last
                have hcontra_val' : (np.paths i).eastStepHeights[(np.paths i).eastStepHeights.length - 1].val >
                    (np.paths j).eastStepHeights[k_j].val := by
                  have h : k_i - 1 = (np.paths i).eastStepHeights.length - 1 := hk_i_minus_1
                  simp only [h] at hcontra_val
                  exact hcontra_val
                omega
              · -- x < lam_i - i, so k_i < lam_i - mu_i = heights.length
                have hx_lt : x < (lam i : ℤ) - (i.val : ℤ) := by
                  have h := hx_hi; omega
                have h1 : ((x - ((mu i : ℤ) - (i.val : ℤ))).toNat : ℤ) = x - ((mu i : ℤ) - (i.val : ℤ)) :=
                  Int.toNat_of_nonneg hnneg2
                have h2 : (((lam i : ℤ) - (mu i : ℤ)).toNat : ℤ) = (lam i : ℤ) - (mu i : ℤ) :=
                  Int.toNat_of_nonneg hnneg
                omega
            -- Apply buildVertices_y_lower_bound_at_x
            have hy_lower : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].2 ≥
                ((np.paths i).eastStepHeights[k_i - 1]).val + 1 :=
              buildVertices_y_lower_bound_at_x a_i c_i N (np.paths i).eastStepHeights hN_pos
                (np.paths i).length_eq h_ca_i (np.paths i).weaklyIncreasing idx_i hidx_i' k_i hk_i_strict hk_i_pos hx_eq_i
            -- Convert to y ≥ heights_i[k_i-1].val + 1
            have hy_lower' : y ≥ ((np.paths i).eastStepHeights[k_i - 1]).val + 1 := by
              have h1 : (buildVertices a_i c_i N (np.paths i).eastStepHeights)[idx_i].2 =
                  ((pathFn i).vertices.get ⟨idx_i, hidx_i⟩).2 := by
                simp only [hvertices_i, List.get_eq_getElem]
              rw [h1, heq_i_y] at hy_lower
              exact hy_lower
            -- Combine: heights_i[k_i-1].val + 1 ≤ y ≤ heights_j[k_j].val + 1
            -- So heights_i[k_i-1].val ≤ heights_j[k_j].val
            -- But hval_contr says heights_i[k_i-1].val > heights_j[k_j].val
            omega
      use pt
      refine ⟨?_, ?_⟩
      · -- Show pt ∈ nipatFinset
        rw [LGV.mem_nipatFinset_iff]
        exact hni
      · -- Show pathTupleToNipat pt = np
        -- Need to show the two Nipat structures are equal
        -- This follows from the fact that lgvPathToLatticePath ∘ buildVertices = id
        simp only [pathTupleToRectNipat]
        congr 1
        funext i
        simp only [pathTupleToLatticePaths, pt, pathFn]
        -- Need to show: lgvPathToLatticePath ... = np.paths i
        -- This follows from lgvPathEastStepYCoords_buildVertices
        apply LatticePath.ext
        simp only [lgvPathToLatticePath]
        have h_ca : 0 ≤ ((lam i : ℤ) - (i.val : ℤ)) - ((mu i : ℤ) - (i.val : ℤ)) := by
          have hcont := hcontained i
          omega
        have heq := lgvPathEastStepYCoords_buildVertices
            ((mu i : ℤ) - (i.val : ℤ)) ((lam i : ℤ) - (i.val : ℤ))
            (np.paths i).eastStepHeights hN_pos (np.paths i).length_eq h_ca
            (np.paths i).weaklyIncreasing
        exact lgvYCoordsToFinN_map_val_add_one_eq (np.paths i).eastStepHeights heq _
  -- 4. Weight preservation
  · intro pt hpt
    exact pathTupleToRectNipat_weight N lam mu hlam hmu hcontained pt
      ((LGV.mem_nipatFinset_iff LGV.integerLattice_pathFinite pt).mp hpt)

/-- At equal path-count and alphabet sizes, rectangular path tuples are the
original `Nipat` objects. -/
private noncomputable def rectNipatSelfEquiv (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    RectNipat N lam mu hlam hmu hcontained ≃
      Nipat lam mu hlam hmu hcontained where
  toFun p := ⟨p.paths, p.colStrictPaths⟩
  invFun p := ⟨p.paths, p.colStrictPaths⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- Compatibility wrapper retaining the original fixed-size bridge theorem. -/
theorem lgv_nipatWeightSum_eq_nipatSum (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    LGV.nipatWeightSum LGV.integerLattice_pathFinite
      (jacobiTrudiArcWeight (N := N) (R := R))
      (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam)
      (Equiv.refl (Fin N)) =
    ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) := by
  have hrect :=
    lgv_nipatWeightSum_eq_rectNipatSum (R := R) N lam mu
      (fun h => Nat.pos_of_ne_zero h) hlam hmu hcontained
  rw [show jacobiTrudiSourceVertex mu = jacobiTrudiSourceVertexRect mu by rfl,
    show jacobiTrudiTargetVertex lam = jacobiTrudiTargetVertexRect N lam by rfl]
  rw [hrect]
  let e := rectNipatSelfEquiv lam mu hlam hmu hcontained
  calc
    ∑ p : RectNipat N lam mu hlam hmu hcontained, p.weight (R := R) =
        ∑ p : RectNipat N lam mu hlam hmu hcontained,
          (e p).weight (R := R) := by rfl
    _ = ∑ p : Nipat lam mu hlam hmu hcontained, p.weight (R := R) :=
      Equiv.sum_comp e (fun p => p.weight)

/-- Key lemma: The Jacobi-Trudi matrix determinant equals the sum of nipat weights.

    This is the core connection between the LGV lemma and the Jacobi-Trudi formula.
    The proof follows from:
    1. jacobiTrudiMatrixH entries are h_{λᵢ - μⱼ - i + j} = pathWeightSum from A_j to B_i
    2. By LGV nonpermutable lemma, det(pathWeightMatrix) = sum over nipats
    3. The Nipat type captures exactly the non-intersecting path tuples -/
theorem det_jacobiTrudiMatrixH_eq_nipatSum (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    (jacobiTrudiMatrixH (R := R) lam mu).det =
      ∑ np : Nipat lam mu hlam hmu hcontained, np.weight (R := R) := by
  -- Step 1-2: Reduce to determinant of path weight matrix
  rw [det_jacobiTrudiMatrixH_eq_det_pathWeightMatrix]
  -- Step 3: Apply LGV nonpermutable
  rw [LGV.lgv_nonpermutable (jacobiTrudiArcWeight (N := N) (R := R))
      (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam)
      (jacobiTrudiSourceVertex_xDecreasing mu hmu)
      (jacobiTrudiSourceVertex_yIncreasing mu)
      (jacobiTrudiTargetVertex_xDecreasing lam hlam)
      (jacobiTrudiTargetVertex_yIncreasing lam)]
  -- Step 4: Connect LGV nipats to our Nipat type
  exact lgv_nipatWeightSum_eq_nipatSum lam mu hlam hmu hcontained

/-- First Jacobi-Trudi formula (Theorem thm.sf.jt-h)
    Label: thm.sf.jt-h

    s_{λ/μ} = det((h_{λᵢ - μⱼ - i + j})_{1 ≤ i,j ≤ M})

    The proof uses the Lindström-Gessel-Viennot lemma with appropriate
    source and target vertices in the integer lattice ℤ².

    ## Proof Strategy

    **Step 1: Set up the LGV framework**
    Define source vertices Aᵢ = (μᵢ - i, 1) and target vertices Bⱼ = (λⱼ - j, N) in ℤ².
    The path weight matrix M_{i,j} = ∑_{p : Aᵢ → Bⱼ} w(p) where w(p) is the product
    of x_h for each east-step at height h.

    **Step 2: Identify M with the Jacobi-Trudi matrix**
    By `pathWeightSum_eq_hsymm`, M_{i,j} = h_{λⱼ - μᵢ - j + i} = h_{λⱼ - μᵢ - (j - i)}.
    Note: The textbook uses 1-indexed notation; our Lean formalization uses 0-indexed.
    The matrix entry (i,j) is h_{λᵢ - μⱼ - i + j} in the textbook convention.

    **Step 3: Apply the LGV lemma**
    By `lgv_nonpermutable` (Corollary cor.lgv.kpaths.wt-np), since the source and
    target vertices satisfy the sorting conditions (x-decreasing, y-increasing),
    we have:
      det(M) = ∑_{nipats from 𝐀 to 𝐁} w(nipat)
    where the sum is only over non-intersecting path tuples (nipats).

    **Step 4: Establish the nipat-SSYT bijection**
    By `nipat_ssyt_bijection`, there is a weight-preserving bijection between
    nipats from 𝐀 to 𝐁 and SSYT of skew shape λ/μ:
    - The nipat (p₁, ..., pₖ) maps to the tableau T where row i contains
      the heights of east-steps in path pᵢ (in weakly increasing order).
    - Non-intersection of paths ensures column-strictness of the tableau.
    - The weight w(nipat) = ∏ᵢ w(pᵢ) equals the monomial x^T.

    **Step 5: Conclude**
    det(M) = ∑_{nipats} w(nipat) = ∑_{SSYT T of shape λ/μ} x^T = s_{λ/μ}

    ## Key Lemmas Required

    1. `pathWeightSum_eq_hsymm`: Path weight sums equal h_n (Observation 1)
    2. `nipat_ssyt_bijection`: Bijection between nipats and SSYT (Observation 2)
    3. `lgv_nonpermutable`: LGV lemma for sorted vertices (from LGV2.lean)
    4. Sorting conditions on A and B vertices (follows from partition monotonicity)

    ## References
    - TeX source: AlgebraicCombinatorics/tex/SymmetricFunctions/PieriJacobiTrudi.tex
    - LGV infrastructure: AlgebraicCombinatorics/Determinants/LGV2.lean
-/
theorem jacobiTrudi_h (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ =
      (jacobiTrudiMatrixH (R := R) lam mu).det := by
  -- The proof combines two key lemmas:
  -- 1. det_jacobiTrudiMatrixH_eq_nipatSum: det(J) = Σ nipat weights
  -- 2. nipatWeightSum_eq_skewSchur: Σ nipat weights = skewSchur
  rw [det_jacobiTrudiMatrixH_eq_nipatSum, nipatWeightSum_eq_skewSchur]


/-!
## Special Cases

When μ = 0 (the empty partition), we get formulas for non-skew Schur polynomials.
-/

/-- The Schur polynomial for a partition λ equals the skew Schur polynomial for λ/0.
    This follows from the fact that a skew partition λ/0 is just the partition λ,
    so SSYT(λ) and SkewSSYT(λ/0) are in natural bijection. -/
lemma schur_eq_skewSchur_zero (lam : NPartition N) :
    schur (R := R) lam = skewSchur (R := R) ⟨lam, 0, fun _ => Nat.zero_le _⟩ := by
  exact (skewSchur_zero_eq_schur lam.parts lam.weaklyDecreasing).symm

/-- Jacobi-Trudi for non-skew Schur polynomials:
    s_λ = det((h_{λᵢ - i + j})_{1 ≤ i,j ≤ N}) -/
theorem jacobiTrudi_h_nonSkew (lam : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
    schur (R := R) ⟨lam, hlam⟩ =
      (jacobiTrudiMatrixH (R := R) lam (fun _ => 0)).det := by
  -- First, relate schur to skewSchur with inner = 0
  rw [schur_eq_skewSchur_zero]
  -- The zero function is weakly decreasing
  have hmu : ∀ i j : Fin N, i ≤ j → (fun _ : Fin N => 0) j ≤ (fun _ : Fin N => 0) i := by
    intros; rfl
  -- Zero is contained in any partition
  have hcontained : ∀ i, (fun _ : Fin N => 0) i ≤ lam i := fun _ => Nat.zero_le _
  -- Apply the general Jacobi-Trudi formula
  exact jacobiTrudi_h (R := R) lam (fun _ => 0) hlam hmu hcontained

/-!
## Symmetry of Skew Schur Polynomials via Jacobi-Trudi

The Jacobi-Trudi formula provides an alternative proof that skew Schur polynomials
are symmetric, without relying on the Bender-Knuth involution.

**Key insight**: The Jacobi-Trudi matrix has entries h_{λᵢ - μⱼ - i + j}, where h_n
is the n-th complete homogeneous symmetric polynomial. Since each h_n is symmetric
and the determinant is a polynomial in the entries, the determinant is also symmetric.

This provides a **sorry-free** proof of symmetry for skew Schur polynomials,
complementing the Bender-Knuth approach in SchurBasics.lean (which is also sorry-free).
-/

/-- If all entries of a matrix are symmetric polynomials, then the determinant is symmetric.
    This is because rename σ commutes with det, and rename σ fixes each symmetric entry. -/
theorem det_isSymmetric_of_entries_symmetric (M : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R))
    (h : ∀ i j, (M i j).IsSymmetric) : M.det.IsSymmetric := by
  intro σ
  simp only [Matrix.det_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [Units.smul_def, map_zsmul]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact h (τ i) i σ

/-- The Jacobi-Trudi matrix (h-version) has symmetric entries. -/
theorem jacobiTrudiMatrixH_entries_isSymmetric (lam mu : Fin N → ℕ) (i j : Fin N) :
    (jacobiTrudiMatrixH (R := R) lam mu i j).IsSymmetric := by
  unfold jacobiTrudiMatrixH
  simp only [Matrix.of_apply]
  exact hsymmExt_isSymmetric _

/-- The determinant of the Jacobi-Trudi matrix (h-version) is symmetric. -/
theorem jacobiTrudiMatrixH_det_isSymmetric (lam mu : Fin N → ℕ) :
    (jacobiTrudiMatrixH (R := R) lam mu).det.IsSymmetric := by
  apply det_isSymmetric_of_entries_symmetric
  exact jacobiTrudiMatrixH_entries_isSymmetric lam mu

/-- **Skew Schur polynomials are symmetric (via Jacobi-Trudi).**

    This provides a sorry-free proof of symmetry using the Jacobi-Trudi formula,
    complementing the Bender-Knuth approach in SchurBasics.lean.

    The proof works by:
    1. Using `jacobiTrudi_h` to express skewSchur as det(jacobiTrudiMatrixH)
    2. Showing each entry h_{λᵢ - μⱼ - i + j} is symmetric (via `hsymmExt_isSymmetric`)
    3. Concluding the determinant is symmetric (via `det_isSymmetric_of_entries_symmetric`)

    Theorem \ref{thm.sf.skew-schur-symm} in the source. -/
theorem skewSchur_isSymmetric_jacobiTrudi (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    (skewSchur (R := R) ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩).IsSymmetric := by
  rw [jacobiTrudi_h lam mu hlam hmu hcontained]
  exact jacobiTrudiMatrixH_det_isSymmetric lam mu

/-- **Schur polynomials are symmetric (via Jacobi-Trudi).**

    This is a corollary of `skewSchur_isSymmetric_jacobiTrudi` with μ = 0.

    Theorem \ref{thm.sf.schur-symm}(a) in the source. -/
theorem schur_isSymmetric_jacobiTrudi (lam : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i) :
    (schur (R := R) ⟨lam, hlam⟩).IsSymmetric := by
  rw [schur_eq_skewSchur_zero]
  have hmu : ∀ i j : Fin N, i ≤ j → (fun _ : Fin N => 0) j ≤ (fun _ : Fin N => 0) i := by
    intros; rfl
  have hcontained : ∀ i, (fun _ : Fin N => 0) i ≤ lam i := fun _ => Nat.zero_le _
  exact skewSchur_isSymmetric_jacobiTrudi lam (fun _ => 0) hlam hmu hcontained

end SymmetricFunctions
