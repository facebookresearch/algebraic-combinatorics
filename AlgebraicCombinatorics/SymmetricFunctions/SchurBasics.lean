/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.SymmetricFunctions.LittlewoodRichardson
import AlgebraicCombinatorics.SymmetricFunctions.NPartition
import AlgebraicCombinatorics.Permutations.Basics

/-!
# Schur Polynomials

This file formalizes the basics of Schur polynomials, including:
- Alternants and the ρ vector
- Young diagrams for N-partitions
- Semistandard Young tableaux (SSYT)
- Schur polynomials as sums over SSYT
- Skew Young diagrams and skew Schur polynomials

The main result is that Schur polynomials are symmetric (Theorem `thm.sf.schur-symm` and
`thm.sf.skew-schur-symm` in the source).

## Main Definitions

- `NPartition N`: An N-partition is an N-tuple of natural numbers that is weakly decreasing
- `rhoVector N`: The N-tuple (N-1, N-2, ..., 0)
- `alternant α`: The alternant a_α = det(x_i^{α_j})
- `NPartition.youngDiagram`: The Young diagram Y(λ) of an N-partition λ
- `SSYT`: Semistandard Young tableaux of shape λ
- `schurPoly`: The Schur polynomial s_λ
- `SkewYoungDiagram`: Skew Young diagrams Y(λ/μ)
- `skewSchurPoly`: The skew Schur polynomial s_{λ/μ}

## References

Based on the LaTeX source `AlgebraicCombinatorics/tex/SymmetricFunctions/SchurBasics.tex`

## Tags

Schur polynomial, Young diagram, semistandard tableau, alternant, symmetric polynomial
-/

noncomputable section

open Finset Matrix Polynomial MvPolynomial BigOperators

variable (N : ℕ) [NeZero N]

/-!
## N-Partitions

This file uses the canonical `NPartition` definition from
`AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean`.

The canonical definition uses `antitone` as the field name, but provides
a `monotone` alias theorem for compatibility. The weakly decreasing
condition means: if `i ≤ j` then `parts j ≤ parts i`.
-/

/-! ## The ρ vector

Definition \ref{def.sf.alternants}(a) in the source defines the ρ vector as the N-tuple
(N-1, N-2, ..., 0). In Lean, we use 0-based indexing via `Fin N`, so:
- ρ(0) = N - 1
- ρ(1) = N - 2
- ...
- ρ(N-1) = 0

For example, when N = 3, we have ρ = (2, 1, 0).
-/

/-- The ρ vector is the N-tuple (N-1, N-2, ..., 0).
    Definition \ref{def.sf.alternants}(a) in the source.

    Note: The textbook uses 1-based indexing with ρ_j = N - j for j ∈ [N].
    In Lean with 0-based indexing, this becomes ρ(i) = N - 1 - i for i ∈ Fin N.

    This is an abbreviation for `AlgebraicCombinatorics.rho N` from LittlewoodRichardson.lean. -/
abbrev rhoVector (N : ℕ) : Fin N → ℕ := AlgebraicCombinatorics.rho N

omit [NeZero N] in
/-- The i-th component of ρ equals N - 1 - i -/
theorem rhoVector_val (i : Fin N) : rhoVector N i = N - 1 - i.val :=
  AlgebraicCombinatorics.rho_apply i

omit [NeZero N] in
/-- The ρ vector is strictly decreasing -/
theorem rhoVector_strictAnti : StrictAnti (rhoVector N) :=
  AlgebraicCombinatorics.rho_strictAnti

omit [NeZero N] in
/-- The ρ vector is weakly decreasing -/
theorem rhoVector_antitone : Antitone (rhoVector N) :=
  AlgebraicCombinatorics.rho_antitone

/-- The first component ρ_0 = N - 1 -/
theorem rhoVector_zero : rhoVector N ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩ = N - 1 :=
  AlgebraicCombinatorics.rho_zero (Nat.pos_of_ne_zero (NeZero.ne N))

/-- The last component ρ_{N-1} = 0 -/
theorem rhoVector_last : rhoVector N ⟨N - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne N)) one_pos⟩ = 0 :=
  AlgebraicCombinatorics.rho_last (Nat.pos_of_ne_zero (NeZero.ne N))

omit [NeZero N] in
/-- The sum of the ρ vector equals N(N-1)/2, which is the triangular number T_{N-1}.
    This follows from ∑_{i=0}^{N-1} (N-1-i) = ∑_{k=0}^{N-1} k = N(N-1)/2. -/
theorem rhoVector_sum : ∑ i : Fin N, rhoVector N i = N * (N - 1) / 2 :=
  AlgebraicCombinatorics.rho_sum

/-- The ρ vector as an N-partition (when N > 0) -/
def rhoPartition (N : ℕ) [NeZero N] : NPartition N where
  parts := rhoVector N
  antitone := rhoVector_antitone N


/-! ## Alternants

Definition \ref{def.sf.alternants}(b) in the source defines the alternant a_α for an
N-tuple α = (α_1, α_2, ..., α_N) as the determinant:

  a_α = det((x_i^{α_j})_{1≤i≤N, 1≤j≤N})

where entry (i, j) is x_i^{α_j}. This is a polynomial in R[x_1, ..., x_N].

In our implementation, we use:
  alternant N α = det(Matrix.of (fun i j => X j ^ α i))

This gives entry (i, j) = x_j^{α_i}, which is the transpose of the textbook matrix.
Since det(A) = det(A^T), both definitions yield the same polynomial.

For example, when N = 3 and α = (5, 3, 0), the textbook matrix is:
  | x_1^5  x_1^3  x_1^0 |
  | x_2^5  x_2^3  x_2^0 |
  | x_3^5  x_3^3  x_3^0 |

and our matrix is the transpose of this.
-/

variable {R : Type*} [CommRing R]

/-- The alternant a_α for an N-tuple α.
    Definition \ref{def.sf.alternants}(b) in the source.

    This is an abbreviation for `AlgebraicCombinatorics.alternant` from LittlewoodRichardson.lean,
    which defines it as ∑_{σ ∈ S_N} sign(σ) · x^(σ·α). This equals the determinant-based
    definition det(x_j^{α_i}) by `AlgebraicCombinatorics.alternant_eq_det`.

    The explicit `N` parameter is kept for backward compatibility with existing code. -/
noncomputable abbrev alternant (N : ℕ) (α : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  AlgebraicCombinatorics.alternant α

/-- Alternative definition matching the textbook convention exactly:
    entry (i, j) = x_i^{α_j}. This equals `alternant` since det(A) = det(A^T). -/
def alternantTextbook (N : ℕ) (α : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  Matrix.det (Matrix.of fun i j => (X i : MvPolynomial (Fin N) R) ^ α j)

omit [NeZero N] in
/-- The two alternant definitions are equal.
    This uses `AlgebraicCombinatorics.alternant_eq_det` to bridge the sum-based
    alternant definition with the determinant-based alternantTextbook. -/
theorem alternantTextbook_eq_alternant (α : Fin N → ℕ) :
    alternantTextbook (R := R) N α = alternant N α := by
  unfold alternantTextbook alternant
  rw [AlgebraicCombinatorics.alternant_eq_det]
  unfold AlgebraicCombinatorics.alternantMatrix
  rw [← Matrix.det_transpose]
  congr 1

/-- The Vandermonde alternant a_ρ equals the Vandermonde product ∏_{i<j}(x_i - x_j).
    Equation \ref{eq.def.sf.alternants.arho=vdm} in the source.

    This is the classical Vandermonde determinant identity. The matrix for a_ρ is:
      | x_1^{N-1}  x_1^{N-2}  ...  x_1^0 |
      | x_2^{N-1}  x_2^{N-2}  ...  x_2^0 |
      |    ...        ...     ...   ...  |
      | x_N^{N-1}  x_N^{N-2}  ...  x_N^0 |
-/
theorem alternant_rho_eq_vandermonde :
    alternant (R := R) N (rhoVector N) =
      ∏ i : Fin N, ∏ j ∈ Finset.filter (· > i) Finset.univ, (X i - X j) := by
  -- Helper lemmas
  have rhoVector_rev : ∀ j : Fin N, rhoVector N (Fin.rev j) = j.val := fun j => by
    simp [AlgebraicCombinatorics.rho, Fin.rev]
    have hj := j.isLt; omega
  have filter_gt_eq_Ioi : ∀ i : Fin N, Finset.filter (· > i) Finset.univ = Finset.Ioi i := fun i => by
    ext j; simp [Finset.mem_Ioi]
  have prod_sub_neg : ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (X j - X i : MvPolynomial (Fin N) R) =
      (-1 : MvPolynomial (Fin N) R) ^ (N * (N - 1) / 2) * ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (X i - X j) := by
    have hfactor : ∀ i j : Fin N, X j - X i = (-1 : MvPolynomial (Fin N) R) * (X i - X j) := fun i j => by ring
    have h1 : ∀ i : Fin N, ∏ j ∈ Finset.Ioi i, (X j - X i : MvPolynomial (Fin N) R) =
              ∏ j ∈ Finset.Ioi i, ((-1) * (X i - X j)) := fun i =>
      Finset.prod_congr rfl fun j _ => hfactor i j
    simp only [h1, Finset.prod_mul_distrib, Finset.prod_const, Fin.card_Ioi]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    cases N with
    | zero => simp
    | succ n =>
      have heq : ∀ i : Fin (n + 1), n + 1 - 1 - i.val = n - i.val := fun i => by omega
      have : ∑ i : Fin (n + 1), (n + 1 - 1 - i.val) = ∑ i : Fin (n + 1), (n - i.val) :=
        Finset.sum_congr rfl fun i _ => heq i
      rw [this, Fin.sum_univ_eq_sum_range (f := fun i => n - i)]
      have hsym : ∑ k ∈ Finset.range (n + 1), (n - k) = ∑ k ∈ Finset.range (n + 1), k := by
        rw [← Finset.sum_range_reflect]
        apply Finset.sum_congr rfl; intro j hj; simp only [Finset.mem_range] at hj; omega
      rw [hsym, Finset.sum_range_id]
  have units_neg_one_pow_cast : ∀ k : ℕ, (((-1 : ℤˣ) ^ k : ℤˣ) : MvPolynomial (Fin N) R) =
               (-1 : MvPolynomial (Fin N) R) ^ k := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [pow_succ, Units.val_mul, Int.cast_mul, ih]
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
  have sign_revPerm : Equiv.Perm.sign (Fin.revPerm (n := N)) = (-1 : ℤˣ) ^ (N * (N - 1) / 2) := by
    rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
    have h : ∀ i j : Fin N, i < j → ¬(Fin.revPerm i < Fin.revPerm j) := fun i j hij => by
      simp only [Fin.revPerm_apply, not_lt]; exact Fin.rev_le_rev.mpr (le_of_lt hij)
    have h2 : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i, (if Fin.revPerm i < Fin.revPerm j then (1 : ℤˣ) else -1) = -1 :=
      fun i j hj => ite_eq_right (h i j (Finset.mem_Ioi.mp hj))
    simp only [Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (h2 i)), Finset.prod_const, Fin.card_Ioi]
    have key : ∏ x : Fin N, (-1 : ℤˣ) ^ (N - 1 - x.val) = (-1) ^ (∑ x : Fin N, (N - 1 - x.val)) := by
      rw [← Finset.prod_pow_eq_pow_sum]
    rw [key]; congr 1
    cases N with
    | zero => simp
    | succ n =>
      have heq : ∀ i : Fin (n + 1), n + 1 - 1 - i.val = n - i.val := fun i => by omega
      have : ∑ i : Fin (n + 1), (n + 1 - 1 - i.val) = ∑ i : Fin (n + 1), (n - i.val) :=
        Finset.sum_congr rfl fun i _ => heq i
      rw [this, Fin.sum_univ_eq_sum_range (f := fun i => n - i)]
      have hsym : ∑ k ∈ Finset.range (n + 1), (n - k) = ∑ k ∈ Finset.range (n + 1), k := by
        rw [← Finset.sum_range_reflect]
        apply Finset.sum_congr rfl; intro j hj; simp only [Finset.mem_range] at hj; omega
      rw [hsym, Finset.sum_range_id]
  -- Main proof
  simp_rw [filter_gt_eq_Ioi]
  -- Convert from sum-based alternant to determinant form
  unfold alternant
  rw [AlgebraicCombinatorics.alternant_eq_det]
  unfold AlgebraicCombinatorics.alternantMatrix
  rw [← Matrix.det_transpose]
  have h1 : (Matrix.of fun i j => (X j : MvPolynomial (Fin N) R) ^ rhoVector N i).transpose.submatrix id Fin.rev =
            Matrix.vandermonde (X : Fin N → MvPolynomial (Fin N) R) := by
    ext i j; simp only [Matrix.submatrix, Matrix.transpose, Matrix.of_apply, Matrix.vandermonde_apply, id_eq]
    rw [rhoVector_rev j]
  have h2 : (Matrix.of fun i j => (X j : MvPolynomial (Fin N) R) ^ rhoVector N i).transpose.submatrix id Fin.rev =
            (Matrix.of fun i j => (X j : MvPolynomial (Fin N) R) ^ rhoVector N i).transpose.submatrix id (Fin.revPerm (n := N)) := by
    ext i j; simp only [Matrix.submatrix, Fin.revPerm_apply, id_eq]
  have h3 : Matrix.det ((Matrix.of fun i j => (X j : MvPolynomial (Fin N) R) ^ rhoVector N i).transpose.submatrix id (Fin.revPerm (n := N))) =
            Equiv.Perm.sign (Fin.revPerm (n := N)) * Matrix.det (Matrix.of fun i j => (X j : MvPolynomial (Fin N) R) ^ rhoVector N i).transpose :=
    Matrix.det_permute' (Fin.revPerm (n := N)) _
  have hsign_sq : (Equiv.Perm.sign (Fin.revPerm (n := N)) : MvPolynomial (Fin N) R) * Equiv.Perm.sign (Fin.revPerm (n := N)) = 1 := by
    have h : Equiv.Perm.sign (Fin.revPerm (n := N)) * Equiv.Perm.sign (Fin.revPerm (n := N)) = (1 : ℤˣ) := by
      have := Int.units_sq (Equiv.Perm.sign (Fin.revPerm (n := N))); rw [sq] at this; exact this
    calc (Equiv.Perm.sign (Fin.revPerm (n := N)) : MvPolynomial (Fin N) R) * Equiv.Perm.sign (Fin.revPerm (n := N))
        = ((Equiv.Perm.sign (Fin.revPerm (n := N)) * Equiv.Perm.sign (Fin.revPerm (n := N)) : ℤˣ) : MvPolynomial (Fin N) R) := by
          simp only [Units.val_mul, Int.cast_mul]
      _ = ((1 : ℤˣ) : MvPolynomial (Fin N) R) := by rw [h]
      _ = 1 := by simp
  have hvdm : Matrix.det (Matrix.vandermonde (X : Fin N → MvPolynomial (Fin N) R)) =
              Equiv.Perm.sign (Fin.revPerm (n := N)) * Matrix.det (Matrix.of fun i j => (X j : MvPolynomial (Fin N) R) ^ rhoVector N i).transpose := by
    rw [← h1, h2, h3]
  have h4 : Matrix.det (Matrix.of fun i j => (X j : MvPolynomial (Fin N) R) ^ rhoVector N i).transpose =
            Equiv.Perm.sign (Fin.revPerm (n := N)) * Matrix.det (Matrix.vandermonde (X : Fin N → MvPolynomial (Fin N) R)) := by
    calc Matrix.det (Matrix.of fun i j => (X j : MvPolynomial (Fin N) R) ^ rhoVector N i).transpose
        = 1 * Matrix.det (Matrix.of fun i j => (X j : MvPolynomial (Fin N) R) ^ rhoVector N i).transpose := by ring
      _ = (Equiv.Perm.sign (Fin.revPerm (n := N)) * Equiv.Perm.sign (Fin.revPerm (n := N))) *
          Matrix.det (Matrix.of fun i j => (X j : MvPolynomial (Fin N) R) ^ rhoVector N i).transpose := by rw [hsign_sq]
      _ = Equiv.Perm.sign (Fin.revPerm (n := N)) * (Equiv.Perm.sign (Fin.revPerm (n := N)) *
          Matrix.det (Matrix.of fun i j => (X j : MvPolynomial (Fin N) R) ^ rhoVector N i).transpose) := by ring
      _ = Equiv.Perm.sign (Fin.revPerm (n := N)) * Matrix.det (Matrix.vandermonde (X : Fin N → MvPolynomial (Fin N) R)) := by rw [← hvdm]
  rw [h4, Matrix.det_vandermonde, prod_sub_neg, sign_revPerm]
  rw [units_neg_one_pow_cast, ← mul_assoc]
  have hsq : ((-1 : MvPolynomial (Fin N) R) ^ (N * (N - 1) / 2)) * ((-1) ^ (N * (N - 1) / 2)) = 1 := by
    rw [← pow_add]
    have heven : Even ((N * (N - 1) / 2) + (N * (N - 1) / 2)) := ⟨N * (N - 1) / 2, by ring⟩
    rw [Even.neg_one_pow heven]
  rw [hsq, one_mul]

/-! ## Young Diagrams for N-partitions

The Young diagram infrastructure is now provided by `NPartition.lean`.
See `NPartition.youngDiagram`, `NPartition.mem_youngDiagram`, etc.
-/

/-! ## Young Tableaux -/

/-- A Young tableau of shape lam is a filling of the Young diagram Y(lam) with elements of [N].
    Definition \ref{def.sf.ytab} in the source. -/
structure YoungTableau {N : ℕ} [NeZero N] (lam : NPartition N) where
  /-- The filling function -/
  entry : Fin N × ℕ → Fin N
  /-- The entry is only meaningful for cells in the diagram -/
  support : ∀ c, c ∉ lam.youngDiagram → entry c = 0

namespace YoungTableau

variable {N : ℕ} [NeZero N] {lam : NPartition N}

/-- Two Young tableaux are equal iff their entries agree. -/
@[ext]
theorem ext {T₁ T₂ : YoungTableau lam} (h : ∀ c, T₁.entry c = T₂.entry c) : T₁ = T₂ := by
  cases T₁; cases T₂
  simp only [mk.injEq]
  funext c
  exact h c

/-- Coercion to function, allowing T c notation. -/
instance : CoeFun (YoungTableau lam) (fun _ => Fin N × ℕ → Fin N) := ⟨entry⟩

/-- Entry at row i, column j. -/
def entryAt (T : YoungTableau lam) (i : Fin N) (j : ℕ) : Fin N := T.entry (i, j)

/-- The number of cells in the tableau (equals the size of the Young diagram). -/
def size (_T : YoungTableau lam) : ℕ := lam.youngDiagram.card

/-- The size of a Young tableau equals the cardinality of its Young diagram. -/
@[simp]
theorem size_eq (T : YoungTableau lam) : T.size = lam.youngDiagram.card := rfl

/-- Entry outside the diagram is zero. -/
theorem entry_of_not_mem (T : YoungTableau lam) {c : Fin N × ℕ}
    (hc : c ∉ lam.youngDiagram) : T.entry c = 0 :=
  T.support c hc

/-- Entry at a cell (i, j) where j ≥ lam_i is zero. -/
theorem entry_of_ge (T : YoungTableau lam) {i : Fin N} {j : ℕ}
    (hj : lam.parts i ≤ j) : T.entry (i, j) = 0 := by
  apply T.support
  rw [NPartition.mem_youngDiagram]
  simp only [not_lt]
  exact hj

/-- Entry at a cell (i, j) is in the diagram iff j < lam_i. -/
theorem entry_mem_iff (_T : YoungTableau lam) {i : Fin N} {j : ℕ} :
    (i, j) ∈ lam.youngDiagram ↔ j < lam.parts i :=
  NPartition.mem_youngDiagram

/-- The size of a tableau equals the sum of parts of the partition. -/
theorem size_eq_sum_parts (T : YoungTableau lam) : T.size = ∑ i, lam.parts i := by
  unfold size NPartition.youngDiagram
  rw [Finset.card_biUnion]
  · simp only [Finset.card_map, Finset.card_range]
  · intro i _ j _ hij
    unfold Function.onFun
    rw [Finset.disjoint_left]
    intro c hci hcj
    simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk] at hci hcj
    obtain ⟨a, _, ha⟩ := hci
    obtain ⟨b, _, hb⟩ := hcj
    rw [← ha, Prod.mk.injEq] at hb
    exact hij hb.1.symm

end YoungTableau

/-- A semistandard Young tableau (SSYT) is a tableau where:
    - entries increase weakly along each row (left to right)
    - entries increase strictly down each column (top to bottom)

    Definition \ref{def.sf.ssyt} in the source.

    Formally, a Young tableau T : Y(λ) → [N] is semistandard if and only if:
    - T(i, j) ≤ T(i, j+1) for any (i, j) ∈ Y(λ) with (i, j+1) ∈ Y(λ)
    - T(i, j) < T(i+1, j) for any (i, j) ∈ Y(λ) with (i+1, j) ∈ Y(λ)

    The set of all semistandard Young tableaux of shape λ is denoted SSYT(λ).

    **Note:** This is one of two SSYT definitions in this project:
    - **This definition** (`SchurBasics.SSYT`): Uses `entry : Fin N × ℕ → Fin N` with a support
      condition that entries outside the Young diagram are 0. Extends `YoungTableau`.
      Requires `[NeZero N]`. Field names: `row_weak`, `col_strict`.
    - **Alternative definition** (`SymmetricFunctions.SSYT` in `PieriJacobiTrudi.lean`): Uses
      dependent types `entries : (i : Fin N) → (j : Fin (lam.parts i)) → Fin N`. Standalone
      structure. No `[NeZero N]` requirement. Field names: `rowWeak`, `colStrict`.

    The equivalence between these definitions is established in `SSYTEquiv.lean` via
    `SSYTEquiv.ssytEquiv`. Use `SSYTEquiv.toSchurBasicsSSYT` and `SSYTEquiv.toSFSSYT`
    to convert between representations.

    **When to use which:**
    - Use this definition when working with cell coordinates `(i, j)` directly, or when
      extending the `YoungTableau` structure is beneficial.
    - Use `SymmetricFunctions.SSYT` when the dependent type ensures bounds checking at
      compile time, or when `[NeZero N]` is not available. -/
structure SSYT {N : ℕ} [NeZero N] (lam : NPartition N) extends YoungTableau lam where
  /-- Entries increase weakly along rows -/
  row_weak : ∀ i : Fin N, ∀ j₁ j₂ : ℕ, (i, j₂) ∈ lam.youngDiagram → j₁ < j₂ →
    entry (i, j₁) ≤ entry (i, j₂)
  /-- Entries increase strictly down columns -/
  col_strict : ∀ i₁ i₂ : Fin N, ∀ j : ℕ, (i₂, j) ∈ lam.youngDiagram → i₁ < i₂ →
    entry (i₁, j) < entry (i₂, j)

namespace SSYT

variable {N : ℕ} [NeZero N] {lam : NPartition N}

/-! ### Basic Properties -/

/-- Two SSYTs are equal iff their entries agree on all cells. -/
@[ext]
theorem ext {T₁ T₂ : SSYT lam} (h : ∀ c, T₁.entry c = T₂.entry c) : T₁ = T₂ := by
  cases T₁; cases T₂
  simp only [mk.injEq]
  exact YoungTableau.ext h

/-- Row-weak property extended to non-strict inequality. -/
theorem row_weak_of_le (T : SSYT lam) {i : Fin N} {j₁ j₂ : ℕ}
    (h : (i, j₂) ∈ lam.youngDiagram) (hle : j₁ ≤ j₂) :
    T.entry (i, j₁) ≤ T.entry (i, j₂) := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · rfl
  · exact T.row_weak i j₁ j₂ h hlt

/-- Column-weak property (derived from col_strict). -/
theorem col_weak (T : SSYT lam) {i₁ i₂ : Fin N} {j : ℕ}
    (h : (i₂, j) ∈ lam.youngDiagram) (hle : i₁ ≤ i₂) :
    T.entry (i₁, j) ≤ T.entry (i₂, j) := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · rfl
  · exact le_of_lt (T.col_strict i₁ i₂ j h hlt)

/-! ### Entry Bounds -/

/-- In a semistandard tableau, entry values in a column are at least the row index.
    This is because entries strictly increase down columns, starting from some value ≥ 0. -/
theorem entry_ge_row (T : SSYT lam) (i : Fin N) {j : ℕ}
    (h : (i, j) ∈ lam.youngDiagram) : i.val ≤ (T.entry (i, j)).val := by
  induction' hi : i.val with n ih generalizing i
  · exact Nat.zero_le _
  · have hn : n < N := by omega
    have hi' : (⟨n, hn⟩, j) ∈ lam.youngDiagram := by
      rw [NPartition.mem_youngDiagram] at h ⊢
      calc j < lam.parts i := h
        _ ≤ lam.parts ⟨n, hn⟩ := lam.monotone ⟨n, hn⟩ i (by simp only [Fin.le_def]; omega)
    have hlt : T.entry (⟨n, hn⟩, j) < T.entry (i, j) :=
      T.col_strict ⟨n, hn⟩ i j h (by simp only [Fin.lt_def]; omega)
    have hih : n ≤ (T.entry (⟨n, hn⟩, j)).val := ih ⟨n, hn⟩ hi' rfl
    omega

/-- Entries in the first column are at least the row index. -/
theorem entry_col_zero_ge_row (T : SSYT lam) (i : Fin N)
    (h : (i, 0) ∈ lam.youngDiagram) : i.val ≤ (T.entry (i, 0)).val :=
  T.entry_ge_row i h

/-- Entry values are bounded by N - 1 (since entries are in Fin N). -/
theorem entry_lt_N (T : SSYT lam) (c : Fin N × ℕ) : (T.entry c).val < N :=
  (T.entry c).isLt

/-! ### The Highest Weight Tableau -/

/-- The "highest weight" SSYT has entry i in every cell of row i.
    This is the semistandard tableau where each entry is the smallest possible value
    that an entry could have in that position (the row index).

    For example, for the partition (4, 2, 1), the highest weight tableau is:
    ```
    0 0 0 0
    1 1
    2
    ```
    where each row i is filled with the value i. -/
def highestWeight (lam : NPartition N) : SSYT lam where
  entry := fun c => if (c.1, c.2) ∈ lam.youngDiagram then c.1 else 0
  support := fun c hc => by simp [hc]
  row_weak := fun i j₁ j₂ h _ => by
    have h1 : (i, j₁) ∈ lam.youngDiagram := by
      rw [NPartition.mem_youngDiagram] at h ⊢
      exact Nat.lt_of_lt_of_le (Nat.lt_of_succ_le (Nat.succ_le_of_lt ‹j₁ < j₂›)) (Nat.le_of_lt h)
    simp [h, h1]
  col_strict := fun i₁ i₂ j h hi => by
    have h1 : (i₁, j) ∈ lam.youngDiagram := by
      rw [NPartition.mem_youngDiagram] at h ⊢
      calc j < lam.parts i₂ := h
        _ ≤ lam.parts i₁ := lam.monotone i₁ i₂ (le_of_lt hi)
    simp [h, h1, hi]

@[simp]
theorem highestWeight_entry_of_mem (c : Fin N × ℕ) (h : c ∈ lam.youngDiagram) :
    (highestWeight lam).entry c = c.1 := by
  simp [highestWeight, h]

@[simp]
theorem highestWeight_entry_of_not_mem (c : Fin N × ℕ) (h : c ∉ lam.youngDiagram) :
    (highestWeight lam).entry c = 0 := by
  simp [highestWeight, h]

/-- The highest weight tableau exists for any partition. -/
instance (lam : NPartition N) : Inhabited (SSYT lam) := ⟨highestWeight lam⟩

/-- The highest weight tableau has the property that T(i,j) = i for all cells in the diagram. -/
theorem highestWeight_entry_eq_row (i : Fin N) (j : ℕ) (h : (i, j) ∈ lam.youngDiagram) :
    (highestWeight lam).entry (i, j) = i := by
  simp [h]

/-- The highest weight tableau achieves the minimum possible entry at each cell. -/
theorem highestWeight_entry_le (T : SSYT lam) (c : Fin N × ℕ) (h : c ∈ lam.youngDiagram) :
    (highestWeight lam).entry c ≤ T.entry c := by
  simp only [highestWeight_entry_of_mem c h]
  exact T.entry_ge_row c.1 h

end SSYT

/-! ## Monomials from tableaux -/

/-- The monomial x_T associated to a Young tableau T.
    Definition \ref{def.sf.ytab.xT} in the source.
    x_T = ∏_{c ∈ Y(lam)} x_{T(c)} -/
def YoungTableau.monomial {N : ℕ} [NeZero N] {lam : NPartition N}
    (T : YoungTableau lam) : MvPolynomial (Fin N) ℤ :=
  ∏ c ∈ lam.youngDiagram, X (T.entry c)

namespace YoungTableau

variable {N : ℕ} [NeZero N] {lam : NPartition N}

/-! ### API lemmas for YoungTableau.monomial (Definition def.sf.ytab.xT)

These lemmas provide the alternative characterization of x_T as a product of powers,
matching the third form of the definition:
  x_T = ∏_{k=1}^N x_k^{(# of times k appears in T)}
-/

/-- The number of times a value k appears in a Young tableau T.
    This is the count #{c ∈ Y(λ) | T(c) = k}. -/
def occurrences (T : YoungTableau lam) (k : Fin N) : ℕ :=
  (lam.youngDiagram.filter fun c => T.entry c = k).card

/-- The monomial x_T equals the product ∏_{k=1}^N x_k^{#{times k appears in T}}.
    This is the third form of the definition in def.sf.ytab.xT:
    x_T = ∏_{k=1}^N x_k^{(# of times k appears in T)} -/
theorem monomial_eq_prod_pow (T : YoungTableau lam) :
    T.monomial = ∏ k : Fin N, X k ^ T.occurrences k := by
  unfold monomial occurrences
  -- Use prod_fiberwise to partition by entry value
  have h := Finset.prod_fiberwise lam.youngDiagram (fun c => T.entry c)
    (fun c => (X (T.entry c) : MvPolynomial (Fin N) ℤ))
  rw [← h]
  congr 1
  ext k
  -- The goal is: ∏ i ∈ (filter (entry i = k)), X (entry i) = X k ^ card (filter ...)
  have step1 : ∏ i ∈ lam.youngDiagram.filter (fun c => T.entry c = k), (X (T.entry i) : MvPolynomial (Fin N) ℤ) =
               ∏ i ∈ lam.youngDiagram.filter (fun c => T.entry c = k), X k := by
    apply Finset.prod_congr rfl
    intro c hc
    simp only [Finset.mem_filter] at hc
    rw [hc.2]
  rw [step1]
  rw [Finset.prod_const]

/-- The occurrences of each value in a Young tableau sum to the diagram size.
    This is because each cell is counted exactly once. -/
theorem sum_occurrences_eq_card (T : YoungTableau lam) :
    ∑ k : Fin N, T.occurrences k = lam.youngDiagram.card := by
  unfold occurrences
  rw [← Finset.card_biUnion]
  · congr 1
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · intro ⟨k, hk, _⟩; exact hk
    · intro hc; exact ⟨T.entry c, hc, rfl⟩
  · intro k _ k' _ hkk'
    simp only [Finset.disjoint_left, Finset.mem_filter]
    intro c ⟨_, hck⟩ ⟨_, hck'⟩
    exact hkk' (hck.symm.trans hck')

set_option backward.isDefEq.respectTransparency false in
/-- The total degree of x_T equals the number of cells in the Young diagram.
    This is |Y(λ)| = λ₁ + λ₂ + ... + λ_N. -/
theorem monomial_totalDegree (T : YoungTableau lam) :
    T.monomial.totalDegree = lam.youngDiagram.card := by
  rw [monomial_eq_prod_pow]
  -- Define the exponent vector
  let d : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun k => T.occurrences k)
  -- The product equals monomial d 1
  have heq : (∏ k : Fin N, X k ^ T.occurrences k : MvPolynomial (Fin N) ℤ) =
             MvPolynomial.monomial d 1 := by
    simp only [MvPolynomial.monomial_eq, d]
    ext k
    simp [Finsupp.equivFunOnFinite]
  rw [heq, MvPolynomial.totalDegree_monomial _ (one_ne_zero)]
  -- Now show the sum equals the diagram size
  rw [← T.sum_occurrences_eq_card]
  simp only [Finsupp.sum, d]
  -- Use Finsupp.equivFunOnFinite_symm_sum to convert
  exact Finsupp.equivFunOnFinite_symm_sum (fun k => T.occurrences k)

set_option backward.isDefEq.respectTransparency false in
/-- The monomial x_T is indeed a monomial in the MvPolynomial sense
    (a single term with coefficient 1). -/
theorem monomial_isMonomial (T : YoungTableau lam) :
    ∃ (d : Fin N →₀ ℕ), T.monomial = MvPolynomial.monomial d 1 := by
  use Finsupp.equivFunOnFinite.symm (fun k => T.occurrences k)
  rw [monomial_eq_prod_pow]
  simp only [MvPolynomial.monomial_eq]
  ext k
  simp [Finsupp.equivFunOnFinite]

end YoungTableau

/-! ## Schur Polynomials -/

/-! ### Finiteness of SSYT

To define the Schur polynomial as a sum over all semistandard Young tableaux,
we need to show that the set of such tableaux is finite. The key insight is that:
1. The Young diagram Y(λ) is a finite set
2. Entries are bounded (they live in Fin N)
3. The SSYT conditions are decidable

We represent tableaux as functions from the diagram to Fin N, and filter for those
satisfying the SSYT conditions.
-/

/-- The type of all fillings of a Young diagram with entries in Fin N.
    This is finite since the diagram is finite and Fin N is finite. -/
def Filling {N : ℕ} [NeZero N] (lam : NPartition N) : Type :=
  { c // c ∈ lam.youngDiagram } → Fin N

/-- Fillings are finite. -/
noncomputable instance filling_fintype {N : ℕ} [NeZero N] (lam : NPartition N) :
    Fintype (Filling lam) :=
  @Fintype.ofFinite _ Pi.finite

/-- The set of fillings that correspond to valid semistandard tableaux.
    We check the conditions on pairs of cells in the diagram:
    - Row-weak: if c1 and c2 are in the same row with c1 to the left, then f(c1) ≤ f(c2)
    - Column-strict: if c1 and c2 are in the same column with c1 above, then f(c1) < f(c2) -/
def isSSYTFillingYoung {N : ℕ} [NeZero N] (lam : NPartition N) (f : Filling lam) : Prop :=
  -- Row-weak condition: check all pairs in the same row
  (∀ c1 c2 : { c // c ∈ lam.youngDiagram },
    c1.val.1 = c2.val.1 → c1.val.2 < c2.val.2 → f c1 ≤ f c2) ∧
  -- Column-strict condition: check all pairs in the same column
  (∀ c1 c2 : { c // c ∈ lam.youngDiagram },
    c1.val.2 = c2.val.2 → c1.val.1 < c2.val.1 → f c1 < f c2)

/-- The SSYT condition is decidable since we're quantifying over finite types. -/
instance isSSYTFillingYoung_decidable {N : ℕ} [NeZero N] (lam : NPartition N)
    (f : Filling lam) : Decidable (isSSYTFillingYoung lam f) := by
  unfold isSSYTFillingYoung
  infer_instance

/-- The finite set of all valid SSYT fillings of a Young diagram. -/
def ssytFillingsYoung {N : ℕ} [NeZero N] (lam : NPartition N) : Finset (Filling lam) :=
  Finset.univ.filter (isSSYTFillingYoung lam)

/-- The monomial associated to a filling of a Young diagram.
    x_f = ∏_{c ∈ Y(λ)} x_{f(c)} -/
def fillingMonomialYoung {N : ℕ} [NeZero N] {lam : NPartition N}
    (f : Filling lam) : MvPolynomial (Fin N) ℤ :=
  ∏ c : { c // c ∈ lam.youngDiagram }, X (f c)

/-- The Schur polynomial s_λ is the sum of monomials x_T over all SSYT of shape λ.
    Definition \ref{def.sf.schur} in the source.

    We define this as a sum over the finite set of valid SSYT fillings:
    s_λ = ∑_{T ∈ SSYT(λ)} x_T

    The definition proceeds by:
    1. Representing tableaux as functions from the Young diagram to Fin N
    2. Filtering for those satisfying the SSYT conditions (row-weak, column-strict)
    3. Summing the associated monomials

    This is equivalent to `skewSchurPoly lam 0` since `skewYoungDiagram lam 0 = lam.youngDiagram`.

    ## Relationship to Other Definitions

    This project has two Schur polynomial definitions with different design tradeoffs:

    | Definition | File | Input | Ring | Use case |
    |------------|------|-------|------|----------|
    | `schurPoly` (this) | SchurBasics.lean | `NPartition N` | `ℤ` | Proofs using Young diagrams, symmetry |
    | `AlgebraicCombinatorics.schurPoly` | LittlewoodRichardson.lean | `Fin N → ℕ` | generic `R` | Littlewood-Richardson rule, generic rings |

    **When to use which:**
    - Use **this definition** when working with Young diagrams, SSYT fillings, or proving
      symmetry properties. It requires `[NeZero N]` and uses integer coefficients.
    - Use **`AlgebraicCombinatorics.schurPoly`** when you need a generic coefficient ring
      or when working with the Littlewood-Richardson rule. It takes unbundled `Fin N → ℕ`.

    **Equivalence:** The two definitions agree when the partition is valid. See:
    - `SSYTEquiv.schurPoly_eq_schur`: relates this definition to `SymmetricFunctions.schur`
    - `schurPoly_eq_AC_schurPoly`: relates this definition to `AlgebraicCombinatorics.schurPoly` -/
def schurPoly {N : ℕ} [NeZero N] (lam : NPartition N) : MvPolynomial (Fin N) ℤ :=
  ∑ f ∈ ssytFillingsYoung lam, fillingMonomialYoung f

/-! ## Examples of Schur Polynomials -/

set_option backward.isDefEq.respectTransparency false in
/-- The Schur polynomial s_{(n,0,...,0)} equals the complete homogeneous symmetric
    polynomial h_n. Example \ref{exa.sf.schur-h-e}(a) in the source.

    The complete homogeneous symmetric polynomial h_n is the sum over all monomials
    of degree n: h_n = ∑_{i₁ ≤ i₂ ≤ ... ≤ iₙ} x_{i₁} x_{i₂} ⋯ x_{iₙ}.
    This equals the Schur polynomial for the single-row partition (n, 0, ..., 0). -/
theorem schurPoly_row_eq_h [DecidableEq (Fin N)] (n : ℕ) (lam : NPartition N)
    (hlam : lam.parts 0 = n ∧ ∀ i : Fin N, i ≠ 0 → lam.parts i = 0) :
    schurPoly lam = MvPolynomial.hsymm (Fin N) ℤ n := by
  -- For a single-row partition (n, 0, ..., 0), the Young diagram has n cells in row 0.
  -- An SSYT filling is a weakly increasing sequence of n elements from Fin N,
  -- which corresponds bijectively to an element of Sym (Fin N) n (multiset of size n).
  -- The monomials correspond under this bijection, so the sums are equal.

  -- Define the equivalence between cells and Fin n
  let e : { c // c ∈ lam.youngDiagram } ≃ Fin n := {
    toFun := fun ⟨c, hc⟩ => ⟨c.2, by
      rw [NPartition.mem_youngDiagram] at hc
      by_cases hc1 : c.1 = 0
      · rw [hc1] at hc; rw [hlam.1] at hc; exact hc
      · exfalso; rw [hlam.2 c.1 hc1] at hc; exact Nat.not_lt_zero _ hc⟩
    invFun := fun ⟨j, hj⟩ => ⟨(0, j), by rw [NPartition.mem_youngDiagram, hlam.1]; exact hj⟩
    left_inv := fun ⟨c, hc⟩ => by
      simp only [Subtype.mk.injEq]
      rw [NPartition.mem_youngDiagram] at hc
      by_cases hc1 : c.1 = 0
      · exact Prod.ext hc1.symm rfl
      · exfalso; rw [hlam.2 c.1 hc1] at hc; exact Nat.not_lt_zero _ hc
    right_inv := fun ⟨j, hj⟩ => rfl }

  unfold schurPoly MvPolynomial.hsymm

  -- Define the forward map: SSYT filling → Sym
  let toSym : Filling lam → Sym (Fin N) n :=
    fun f => ⟨Multiset.ofList (List.ofFn (f ∘ e.symm)), by simp⟩

  -- Define the backward map: Sym → Filling
  let fromSym : Sym (Fin N) n → Filling lam := fun s c =>
    (s.1.sort (· ≤ ·)).get ⟨(e c).val, by
      rw [Multiset.length_sort]
      have : s.1.card = n := s.2
      rw [this]
      exact (e c).isLt⟩

  -- Use sum_bij' to establish the bijection
  apply Finset.sum_bij'
    (i := fun f _ => toSym f)
    (j := fun s _ => fromSym s)
  · -- hi: toSym maps into Finset.univ
    intro f _
    exact Finset.mem_univ _
  · -- hj: fromSym maps into ssytFillingsYoung
    intro s _
    simp only [ssytFillingsYoung, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · -- row-weak: for cells in same row with c1.2 < c2.2, f c1 ≤ f c2
      intro c1 c2 _ hlt
      have h1 : (e c1).val = c1.val.2 := rfl
      have h2 : (e c2).val = c2.val.2 := rfl
      have hlt' : (e c1).val < (e c2).val := by simp [h1, h2]; exact hlt
      exact List.Pairwise.rel_get_of_le (Multiset.pairwise_sort (r := (· ≤ ·)) (s := s.1)) (le_of_lt hlt')
    · -- column-strict: impossible for single-row partition (all cells in row 0)
      intro c1 c2 _ hlt
      exfalso
      have hc1 : c1.val.1 = 0 := by
        by_contra h; have := NPartition.mem_youngDiagram.mp c1.property
        rw [hlam.2 c1.val.1 h] at this; exact Nat.not_lt_zero _ this
      have hc2 : c2.val.1 = 0 := by
        by_contra h; have := NPartition.mem_youngDiagram.mp c2.property
        rw [hlam.2 c2.val.1 h] at this; exact Nat.not_lt_zero _ this
      rw [hc1, hc2] at hlt
      exact Nat.lt_irrefl 0 hlt
  · -- left_inv: fromSym (toSym f) = f
    intro f hf
    funext c
    simp only [toSym, fromSym, ssytFillingsYoung, Finset.mem_filter, Finset.mem_univ, true_and] at *
    have hmono : Monotone (f ∘ e.symm) := by
      intro j1 j2 hj12
      rcases lt_or_eq_of_le hj12 with hlt | heq
      · exact hf.1 (e.symm j1) (e.symm j2) rfl hlt
      · rw [heq]
    have hpw : (List.ofFn (f ∘ e.symm)).Pairwise (· ≤ ·) := by
      rw [List.pairwise_iff_get]
      intro a b hab
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      exact hmono (le_of_lt hab)
    have hsorted : (Multiset.ofList (List.ofFn (f ∘ e.symm))).sort (· ≤ ·) = List.ofFn (f ∘ e.symm) := by
      have hperm : List.Perm ((Multiset.ofList (List.ofFn (f ∘ e.symm))).sort (· ≤ ·)) (List.ofFn (f ∘ e.symm)) := by
        have h := Multiset.sort_eq (Multiset.ofList (List.ofFn (f ∘ e.symm))) (· ≤ ·)
        simp only [Multiset.coe_eq_coe] at h
        exact h
      exact hperm.eq_of_pairwise' (Multiset.pairwise_sort (r := (· ≤ ·)) (s := Multiset.ofList (List.ofFn (f ∘ e.symm)))) hpw
    simp only [hsorted, List.get_eq_getElem, List.getElem_ofFn, Function.comp_apply]
    congr 1
    exact e.symm_apply_apply c
  · -- right_inv: toSym (fromSym s) = s
    intro s _
    apply Sym.coe_injective
    simp only [toSym, fromSym, Sym.coe_mk]
    have hlen : (s.1.sort (· ≤ ·)).length = n := by rw [Multiset.length_sort]; exact s.2
    have h1 : List.ofFn ((fun c => (s.1.sort (· ≤ ·)).get ⟨(e c).val, by
        rw [Multiset.length_sort]; have : s.1.card = n := s.2; rw [this]; exact (e c).isLt⟩) ∘ e.symm) =
        s.1.sort (· ≤ ·) := by
      apply List.ext_get
      · simp only [List.length_ofFn]; exact hlen.symm
      · intro i h1 h2
        simp only [List.getElem_ofFn, Function.comp_apply, Equiv.apply_symm_apply, List.get_eq_getElem]
    rw [h1]
    exact Multiset.sort_eq s.1 (· ≤ ·)
  · -- monomial equality: fillingMonomialYoung f = (toSym f).1.map X).prod
    intro f _
    simp only [fillingMonomialYoung, toSym]
    simp only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
    rw [Fintype.prod_equiv e (fun c => X (f c)) (fun i => X (f (e.symm i)))]
    · rfl
    · intro c; simp [Equiv.symm_apply_apply]

/-- Equivalence between cells in a column partition's Young diagram and Fin n.
    For a column partition (1,1,...,1,0,...,0) with n ones, the Young diagram
    consists of n cells in column 0, which can be identified with Fin n. -/
def col_partition_equiv {N : ℕ} [NeZero N] (n : ℕ) (hn : n ≤ N) (lam : NPartition N)
    (hlam : (∀ i : Fin N, i.val < n → lam.parts i = 1) ∧
            (∀ i : Fin N, i.val ≥ n → lam.parts i = 0)) :
    { c // c ∈ lam.youngDiagram } ≃ Fin n where
  toFun := fun ⟨c, hc⟩ => ⟨c.1.val, by
    rw [NPartition.mem_youngDiagram] at hc
    by_contra h; push Not at h
    have := hlam.2 c.1 h; rw [this] at hc
    exact Nat.not_lt_zero _ hc⟩
  invFun := fun ⟨k, hk⟩ => ⟨(⟨k, Nat.lt_of_lt_of_le hk hn⟩, 0), by
    rw [NPartition.mem_youngDiagram, hlam.1 ⟨k, Nat.lt_of_lt_of_le hk hn⟩ hk]
    exact Nat.zero_lt_one⟩
  left_inv := fun ⟨c, hc⟩ => by
    simp only [Subtype.mk.injEq]
    rw [NPartition.mem_youngDiagram] at hc
    by_cases hi : c.1.val < n
    · have hpart : lam.parts c.1 = 1 := hlam.1 c.1 hi
      rw [hpart] at hc; have hj : c.2 = 0 := by omega
      ext <;> simp [hj]
    · have hpart : lam.parts c.1 = 0 := hlam.2 c.1 (Nat.not_lt.mp hi)
      rw [hpart] at hc; exact absurd hc (Nat.not_lt_zero _)
  right_inv := fun ⟨k, hk⟩ => by simp

/-- In a column partition, all cells have j = 0 (they're all in column 0). -/
lemma col_partition_cell_snd_eq_zero {N : ℕ} [NeZero N] (n : ℕ) (_hn : n ≤ N) (lam : NPartition N)
    (hlam : (∀ i : Fin N, i.val < n → lam.parts i = 1) ∧
            (∀ i : Fin N, i.val ≥ n → lam.parts i = 0))
    (c : { c // c ∈ lam.youngDiagram }) : c.val.2 = 0 := by
  have hc := c.property
  rw [NPartition.mem_youngDiagram] at hc
  by_cases hi : c.val.1.val < n
  · have := hlam.1 c.val.1 hi; rw [this] at hc; omega
  · have := hlam.2 c.val.1 (Nat.not_lt.mp hi); rw [this] at hc
    exact absurd hc (Nat.not_lt_zero _)

lemma col_partition_equiv_symm_snd {N : ℕ} [NeZero N] (n : ℕ) (hn : n ≤ N) (lam : NPartition N)
    (hlam : (∀ i : Fin N, i.val < n → lam.parts i = 1) ∧
            (∀ i : Fin N, i.val ≥ n → lam.parts i = 0))
    (k : Fin n) : ((col_partition_equiv n hn lam hlam).symm k).val.2 = 0 := rfl

lemma col_partition_equiv_symm_fst {N : ℕ} [NeZero N] (n : ℕ) (hn : n ≤ N) (lam : NPartition N)
    (hlam : (∀ i : Fin N, i.val < n → lam.parts i = 1) ∧
            (∀ i : Fin N, i.val ≥ n → lam.parts i = 0))
    (k : Fin n) : ((col_partition_equiv n hn lam hlam).symm k).val.1.val = k.val := rfl

/-- For a column partition, the SSYT condition is equivalent to strict monotonicity.
    Since all cells are in column 0, the row-weak condition is vacuously true,
    and the column-strict condition becomes strict monotonicity. -/
lemma col_partition_ssyt_iff {N : ℕ} [NeZero N] (n : ℕ) (hn : n ≤ N) (lam : NPartition N)
    (hlam : (∀ i : Fin N, i.val < n → lam.parts i = 1) ∧
            (∀ i : Fin N, i.val ≥ n → lam.parts i = 0))
    (f : Filling lam) :
    isSSYTFillingYoung lam f ↔ StrictMono (f ∘ (col_partition_equiv n hn lam hlam).symm) := by
  let e := col_partition_equiv n hn lam hlam
  constructor
  · intro ⟨_, hcol⟩ i j hij
    simp only [Function.comp_apply, col_partition_equiv]
    apply hcol
    · rfl
    · simp only [Fin.lt_def] at hij ⊢; exact hij
  · intro hstrict
    constructor
    · intro c1 c2 _ hlt
      have h1 := col_partition_cell_snd_eq_zero n hn lam hlam c1
      have h2 := col_partition_cell_snd_eq_zero n hn lam hlam c2
      omega
    · intro c1 c2 _ hrow
      have hi1 : c1.val.1.val < n := by
        by_contra h; push Not at h
        have := hlam.2 c1.val.1 h
        have hc1 := c1.property
        rw [NPartition.mem_youngDiagram, this] at hc1
        exact Nat.not_lt_zero _ hc1
      have hi2 : c2.val.1.val < n := by
        by_contra h; push Not at h
        have := hlam.2 c2.val.1 h
        have hc2 := c2.property
        rw [NPartition.mem_youngDiagram, this] at hc2
        exact Nat.not_lt_zero _ hc2
      have h1 := col_partition_cell_snd_eq_zero n hn lam hlam c1
      have h2 := col_partition_cell_snd_eq_zero n hn lam hlam c2
      have hc1_eq : c1 = e.symm ⟨c1.val.1.val, hi1⟩ := by
        apply Subtype.ext; simp only [Prod.ext_iff]
        refine ⟨?_, ?_⟩
        · ext; exact (col_partition_equiv_symm_fst n hn lam hlam ⟨c1.val.1.val, hi1⟩).symm
        · rw [h1, col_partition_equiv_symm_snd]
      have hc2_eq : c2 = e.symm ⟨c2.val.1.val, hi2⟩ := by
        apply Subtype.ext; simp only [Prod.ext_iff]
        refine ⟨?_, ?_⟩
        · ext; exact (col_partition_equiv_symm_fst n hn lam hlam ⟨c2.val.1.val, hi2⟩).symm
        · rw [h2, col_partition_equiv_symm_snd]
      rw [hc1_eq, hc2_eq]
      exact hstrict (by simp only [Fin.lt_def]; exact hrow)

set_option backward.isDefEq.respectTransparency false in
/-- The Schur polynomial s_{(1,1,...,1,0,...,0)} (with n ones) equals the elementary
    symmetric polynomial e_n. Example \ref{exa.sf.schur-h-e}(b) in the source.

    The elementary symmetric polynomial e_n is the sum over all squarefree monomials
    of degree n: e_n = ∑_{i₁ < i₂ < ... < iₙ} x_{i₁} x_{i₂} ⋯ x_{iₙ}.
    This equals the Schur polynomial for the single-column partition (1, 1, ..., 1, 0, ..., 0)
    with n ones. -/
theorem schurPoly_col_eq_e (n : ℕ) (hn : n ≤ N) (lam : NPartition N)
    (hlam : (∀ i : Fin N, i.val < n → lam.parts i = 1) ∧
          (∀ i : Fin N, i.val ≥ n → lam.parts i = 0)) :
    schurPoly lam = MvPolynomial.esymm (Fin N) ℤ n := by
  let e := col_partition_equiv n hn lam hlam
  unfold schurPoly MvPolynomial.esymm

  -- Define the forward map: SSYT filling → subset of size n
  let toFinset : Filling lam → Finset (Fin N) := fun f => Finset.image (f ∘ e.symm) Finset.univ

  -- Define the backward map: subset of size n → Filling
  let fromFinset : (s : Finset (Fin N)) → s.card = n → Filling lam :=
    fun s hs c => (s.orderEmbOfFin hs) (e c)

  -- Show that SSYT fillings give finsets of size n
  have hcard : ∀ f ∈ ssytFillingsYoung lam, (toFinset f).card = n := fun f hf => by
    simp only [ssytFillingsYoung, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    rw [col_partition_ssyt_iff n hn lam hlam] at hf
    rw [Finset.card_image_of_injective _ hf.injective, Finset.card_univ, Fintype.card_fin]

  -- Use Finset.sum_bij' to establish the bijection
  refine Finset.sum_bij'
    (fun f _ => toFinset f)
    (fun s hs => fromFinset s (by simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs; exact hs))
    ?_ ?_ ?_ ?_ ?_
  · -- hi: toFinset maps into powersetCard n univ
    intro f hf
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact hcard f hf
  · -- hj: fromFinset maps into ssytFillingsYoung
    intro s hs
    simp only [ssytFillingsYoung, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [col_partition_ssyt_iff n hn lam hlam]
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs
    intro i j hij
    simp only [Function.comp_apply, fromFinset]
    exact (s.orderEmbOfFin hs).strictMono hij
  · -- left_inv: fromFinset (toFinset f) = f
    intro f hf
    simp only [ssytFillingsYoung, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    rw [col_partition_ssyt_iff n hn lam hlam] at hf
    funext c
    simp only [fromFinset, toFinset]
    have hcard' := hcard f (by simp [ssytFillingsYoung, col_partition_ssyt_iff n hn lam hlam, hf])
    have huniq := Finset.orderEmbOfFin_unique hcard'
      (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) hf
    calc ((Finset.image (f ∘ e.symm) Finset.univ).orderEmbOfFin hcard') (e c)
        = (f ∘ e.symm) (e c) := by rw [← huniq]
      _ = f c := by simp [Equiv.symm_apply_apply]
  · -- right_inv: toFinset (fromFinset s) = s
    intro s hs
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs
    simp only [toFinset, fromFinset]
    have heq : (fun c => (s.orderEmbOfFin hs) (e c)) ∘ e.symm = (s.orderEmbOfFin hs) := by
      funext i; simp [Equiv.apply_symm_apply]
    rw [heq]
    exact Finset.image_orderEmbOfFin_univ s hs
  · -- monomial equality
    intro f hf
    simp only [fillingMonomialYoung, toFinset]
    simp only [ssytFillingsYoung, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    rw [col_partition_ssyt_iff n hn lam hlam] at hf
    -- Need to show: ∏ c, X (f c) = ∏ i ∈ (Finset.image (f ∘ e.symm) univ), X i
    rw [Fintype.prod_equiv e (fun c => X (f c)) (fun i => X (f (e.symm i))) (fun c => by simp)]
    -- Now need: ∏ x, X (f (e.symm x)) = ∏ i ∈ image (f ∘ e.symm) univ, X i
    have hinj : Set.InjOn (f ∘ e.symm) (Finset.univ : Finset (Fin n)) :=
      fun _ _ _ _ h => hf.injective h
    conv_rhs => rw [Finset.prod_image hinj]
    simp only [Function.comp_apply]

/-! ### Helper lemmas for schurPoly_21_eq -/

omit [NeZero N] in
/-- The elementary symmetric polynomial e_3 equals the sum over strictly ordered triples.
    This is a key identity used in the proof of `schurPoly_21_eq`.

    The bijection between `powersetCard 3` and strictly ordered triples (i, j, k) with i < j < k
    is established by sorting the 3-element set. Each 3-element subset {a, b, c} corresponds
    uniquely to the ordered triple (min, mid, max). -/
theorem esymm_3_eq_sum_strictlyOrdered :
    esymm (Fin N) ℤ 3 =
    ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      if i < j ∧ j < k then X i * X j * X k else 0 := by
  classical
  rw [esymm]
  have h1 : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      if i < j ∧ j < k then X i * X j * X k else (0 : MvPolynomial (Fin N) ℤ)) =
      ∑ t ∈ univ.filter (fun (t : Fin N × Fin N × Fin N) => t.1 < t.2.1 ∧ t.2.1 < t.2.2),
        X t.1 * X t.2.1 * X t.2.2 := by
    rw [sum_filter]
    simp only [← Fintype.sum_prod_type']
  rw [h1]
  have card_triple : ∀ i j k : Fin N, i < j → j < k →
      ({i, j, k} : Finset (Fin N)).card = 3 := by
    intro i j k hij hjk
    rw [card_insert_eq_ite, ite_eq_right, card_insert_eq_ite, ite_eq_right, card_singleton]
    · simp [ne_of_lt hjk]
    · simp [ne_of_lt hij, ne_of_lt (lt_trans hij hjk)]
  have min_triple : ∀ i j k : Fin N, i < j → j < k →
      ({i, j, k} : Finset (Fin N)).min' (by simp) = i := by
    intro i j k hij hjk
    apply le_antisymm
    · apply min'_le; simp
    · apply le_min'; intro x hx; simp at hx
      rcases hx with rfl | rfl | rfl
      · rfl
      · exact le_of_lt hij
      · exact le_of_lt (lt_trans hij hjk)
  have max_triple : ∀ i j k : Fin N, i < j → j < k →
      ({i, j, k} : Finset (Fin N)).max' (by simp) = k := by
    intro i j k hij hjk
    apply le_antisymm
    · apply max'_le; intro x hx; simp at hx
      rcases hx with rfl | rfl | rfl
      · exact le_of_lt (lt_trans hij hjk)
      · exact le_of_lt hjk
      · rfl
    · apply le_max'; simp
  let tripleToSet : (t : Fin N × Fin N × Fin N) → Finset (Fin N) := fun t => {t.1, t.2.1, t.2.2}
  symm
  apply Finset.sum_bij (fun t _ => tripleToSet t)
  · intro ⟨i, j, k⟩ ht
    simp only [mem_filter, mem_univ, true_and] at ht
    rw [mem_powersetCard]
    exact ⟨subset_univ _, card_triple i j k ht.1 ht.2⟩
  · intro ⟨i₁, j₁, k₁⟩ ht₁ ⟨i₂, j₂, k₂⟩ ht₂ heq
    simp only [mem_filter, mem_univ, true_and] at ht₁ ht₂
    simp only [tripleToSet] at heq
    have hi : i₁ = i₂ := by
      have h1 := min_triple i₁ j₁ k₁ ht₁.1 ht₁.2
      have h2 := min_triple i₂ j₂ k₂ ht₂.1 ht₂.2
      rw [← h1, ← h2]; simp only [heq]
    have hk : k₁ = k₂ := by
      have h1 := max_triple i₁ j₁ k₁ ht₁.1 ht₁.2
      have h2 := max_triple i₂ j₂ k₂ ht₂.1 ht₂.2
      rw [← h1, ← h2]; simp only [heq]
    have hj : j₁ = j₂ := by
      have hj₁_mem : j₁ ∈ ({i₁, j₁, k₁} : Finset (Fin N)) := by simp
      rw [heq] at hj₁_mem; simp at hj₁_mem
      rcases hj₁_mem with rfl | rfl | rfl
      · omega
      · rfl
      · omega
    simp only [Prod.mk.injEq]; exact ⟨hi, hj, hk⟩
  · intro s hs
    have hcard := (mem_powersetCard.mp hs).2
    have hne : s.Nonempty := by rw [← card_pos]; omega
    let a := s.min' hne
    let c := s.max' hne
    have ha_mem : a ∈ s := min'_mem s hne
    have hc_mem : c ∈ s := max'_mem s hne
    have hne' : (s.erase a).Nonempty := by
      rw [← card_pos, card_erase_of_mem ha_mem]; omega
    let b := (s.erase a).min' hne'
    have hb_mem_erase : b ∈ s.erase a := min'_mem _ hne'
    have hb_mem : b ∈ s := mem_of_mem_erase hb_mem_erase
    have hab : a < b := by
      have hba : b ≠ a := (mem_erase.mp hb_mem_erase).1
      exact lt_of_le_of_ne (min'_le s b hb_mem) (Ne.symm hba)
    have hbc : b < c := by
      have hac : a < c := by
        have hne_ac : a ≠ c := by
          intro heq
          have : s.card ≤ 1 := by
            apply card_le_one.mpr
            intro x hx y hy
            have hxa : a ≤ x := min'_le s x hx
            have hxc : x ≤ c := le_max' s x hx
            have hya : a ≤ y := min'_le s y hy
            have hyc : y ≤ c := le_max' s y hy
            rw [heq] at hxa hya
            exact le_antisymm (le_trans hxc hya) (le_trans hyc hxa)
          omega
        exact lt_of_le_of_ne (le_max' s a ha_mem) hne_ac
      have hb_le_c : b ≤ c := le_max' s b hb_mem
      have hb_ne_c : b ≠ c := by
        intro heq
        have hc_in_erase : c ∈ s.erase a := mem_erase.mpr ⟨ne_of_gt hac, hc_mem⟩
        have hcard_erase : (s.erase a).card = 2 := by
          rw [card_erase_of_mem ha_mem]; omega
        have : (s.erase a).card ≤ 1 := by
          apply card_le_one.mpr
          intro x hx y hy
          have hbx : b ≤ x := min'_le _ x hx
          have hby : b ≤ y := min'_le _ y hy
          have hx_in_s : x ∈ s := mem_of_mem_erase hx
          have hy_in_s : y ∈ s := mem_of_mem_erase hy
          have hxc : x ≤ c := le_max' s x hx_in_s
          have hyc : y ≤ c := le_max' s y hy_in_s
          rw [← heq] at hxc hyc
          exact le_antisymm (le_trans hxc hby) (le_trans hyc hbx)
        omega
      exact lt_of_le_of_ne hb_le_c hb_ne_c
    use (a, b, c)
    refine ⟨?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]; exact ⟨hab, hbc⟩
    · simp only [tripleToSet]
      ext x
      simp only [mem_insert, mem_singleton]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ha_mem
        · exact hb_mem
        · exact hc_mem
      · intro hx
        by_cases hxa : x = a
        · left; exact hxa
        · by_cases hxc : x = c
          · right; right; exact hxc
          · right; left
            have hx_erase : x ∈ s.erase a := mem_erase.mpr ⟨hxa, hx⟩
            have hbx : b ≤ x := min'_le _ x hx_erase
            have hxc' : x < c := lt_of_le_of_ne (le_max' s x hx) hxc
            have hac : a < c := lt_trans hab hbc
            have hc_in_erase : c ∈ s.erase a := mem_erase.mpr ⟨ne_of_gt hac, hc_mem⟩
            have hcard_erase : (s.erase a).card = 2 := by
              rw [card_erase_of_mem ha_mem]; omega
            have herase_eq : s.erase a = {b, c} := by
              apply eq_of_subset_of_card_le
              · intro y hy
                simp only [mem_insert, mem_singleton]
                by_cases hyb : y = b
                · left; exact hyb
                · right
                  have hby : b < y := lt_of_le_of_ne (min'_le _ y hy) (Ne.symm hyb)
                  have hy_in_s : y ∈ s := mem_of_mem_erase hy
                  have hyc'' : y ≤ c := le_max' s y hy_in_s
                  by_contra hyne
                  have hyc''' : y < c := lt_of_le_of_ne hyc'' hyne
                  have hb_in : b ∈ s.erase a := hb_mem_erase
                  have hcard3 : 3 ≤ (s.erase a).card := by
                    have hsub : ({b, y, c} : Finset (Fin N)) ⊆ s.erase a := by
                      intro z hz
                      simp only [mem_insert, mem_singleton] at hz
                      rcases hz with rfl | rfl | rfl
                      · exact hb_in
                      · exact hy
                      · exact hc_in_erase
                    calc 3 = ({b, y, c} : Finset (Fin N)).card := by
                            rw [card_insert_eq_ite, ite_eq_right, card_insert_eq_ite, ite_eq_right, card_singleton]
                            · simp only [mem_singleton]; exact ne_of_lt hyc'''
                            · simp only [mem_insert, mem_singleton]; push Not
                              exact ⟨ne_of_lt hby, ne_of_lt (lt_trans hby hyc''')⟩
                      _ ≤ (s.erase a).card := card_le_card hsub
                  omega
              · rw [card_insert_eq_ite, ite_eq_right, card_singleton]
                · omega
                · simp only [mem_singleton]; exact ne_of_lt hbc
            have hx_in_bc : x ∈ ({b, c} : Finset (Fin N)) := by
              rw [← herase_eq]; exact hx_erase
            simp only [mem_insert, mem_singleton] at hx_in_bc
            rcases hx_in_bc with rfl | rfl
            · rfl
            · exact absurd rfl hxc
  · intro ⟨i, j, k⟩ ht
    simp only [mem_filter, mem_univ, true_and] at ht
    obtain ⟨hij, hjk⟩ := ht
    simp only [tripleToSet]
    rw [prod_insert, prod_insert, prod_singleton]
    · ring
    · simp only [mem_singleton]; exact ne_of_lt hjk
    · simp only [mem_insert, mem_singleton]; push Not
      exact ⟨ne_of_lt hij, ne_of_lt (lt_trans hij hjk)⟩

omit [NeZero N] in
/-- The product e_2 * e_1 expands as 3*e_3 plus squared terms.
    This is a key identity used in the proof of `schurPoly_21_eq`.

    The expansion proceeds by writing e_2 * e_1 = (∑_{a<b} X_a X_b) * (∑_c X_c)
    and partitioning the terms by the relationship of c to {a, b}:
    - c < a: contributes e_3 (strictly ordered triple (c, a, b))
    - c = a: contributes ∑_{a<b} X_a² X_b
    - a < c < b: contributes e_3 (strictly ordered triple (a, c, b))
    - c = b: contributes ∑_{a<b} X_a X_b²
    - c > b: contributes e_3 (strictly ordered triple (a, b, c))
    Total: 3*e_3 + ∑_{a<b} X_a² X_b + ∑_{a<b} X_a X_b² -/
theorem esymm_2_mul_esymm_1_expansion :
    esymm (Fin N) ℤ 2 * esymm (Fin N) ℤ 1 =
    3 * esymm (Fin N) ℤ 3 +
    (∑ a : Fin N, ∑ b : Fin N, if a < b then X a * X a * X b else 0) +
    (∑ a : Fin N, ∑ b : Fin N, if a < b then X a * X b * X b else 0) := by
  -- The proof follows from expanding e_2 * e_1 and partitioning by the relationship
  -- of the third variable c to the pair {a, b}.
  --
  -- e_2 = ∑_{a<b} X_a X_b
  -- e_1 = ∑_c X_c
  -- e_2 * e_1 = ∑_{a<b} ∑_c X_a X_b X_c
  --
  -- For each pair (a, b) with a < b, partition ∑_c X_c into:
  -- - c = a: contributes X_a² X_b
  -- - c = b: contributes X_a X_b²
  -- - c < a: contributes to e_3 (triple c < a < b)
  -- - a < c < b: contributes to e_3 (triple a < c < b)
  -- - c > b: contributes to e_3 (triple a < b < c)
  --
  -- The c ∉ {a, b} terms sum to 3*e_3 because each strictly ordered triple (i < j < k)
  -- appears exactly 3 times in the sum over (a, b, c) with a < b and c ∉ {a, b}:
  -- - as (a, b, c) = (j, k, i) when i < j < k (i.e., c < a)
  -- - as (a, b, c) = (i, k, j) when i < j < k (i.e., a < c < b)
  -- - as (a, b, c) = (i, j, k) when i < j < k (i.e., c > b)

  -- Step 1: Convert esymm 2 to sum over pairs
  have h_e2 : esymm (Fin N) ℤ 2 =
      ∑ a : Fin N, ∑ b : Fin N, if a < b then X a * X b else 0 := by
    rw [esymm]
    conv_rhs => rw [← Finset.sum_product', ← Finset.sum_filter, Finset.univ_product_univ]
    symm
    refine Finset.sum_bij'
      (i := fun (p : Fin N × Fin N) _ => ({p.1, p.2} : Finset (Fin N)))
      (j := fun s hs => (s.min' (by rw [Finset.mem_powersetCard_univ] at hs;
                                    exact Finset.card_pos.mp (by omega)),
        s.max' (by rw [Finset.mem_powersetCard_univ] at hs;
                   exact Finset.card_pos.mp (by omega))))
      ?_ ?_ ?_ ?_ ?_
    · intro ⟨a, b⟩ hab
      simp only [Finset.mem_filter] at hab
      rw [Finset.mem_powersetCard_univ]
      exact Finset.card_pair hab.2.ne
    · intro s hs
      rw [Finset.mem_powersetCard_univ] at hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
      rcases lt_trichotomy a b with h | h | h
      · rw [Finset.min'_pair, Finset.max'_pair, min_eq_left (le_of_lt h),
            max_eq_right (le_of_lt h)]; exact h
      · exact (hab h).elim
      · rw [Finset.min'_pair, Finset.max'_pair, min_eq_right (le_of_lt h),
            max_eq_left (le_of_lt h)]; exact h
    · intro ⟨a, b⟩ hab
      simp only [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq]
      exact ⟨by rw [Finset.min'_pair, min_eq_left (le_of_lt hab.2)],
             by rw [Finset.max'_pair, max_eq_right (le_of_lt hab.2)]⟩
    · intro s hs
      rw [Finset.mem_powersetCard_univ] at hs
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
      have hne : ({a, b} : Finset (Fin N)).Nonempty := Finset.insert_nonempty _ _
      rcases lt_trichotomy a b with h | h | h
      · simp only [Finset.min'_pair, Finset.max'_pair, min_eq_left (le_of_lt h),
                   max_eq_right (le_of_lt h)]
      · exact (hab h).elim
      · have h1 : ({a, b} : Finset (Fin N)).min' hne = b := by
          rw [Finset.min'_pair, min_eq_right (le_of_lt h)]
        have h2 : ({a, b} : Finset (Fin N)).max' hne = a := by
          rw [Finset.max'_pair, max_eq_left (le_of_lt h)]
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun hx => hx.elim (fun heq => Or.inr (heq ▸ h1))
                                 (fun heq => Or.inl (heq ▸ h2)),
               fun hx => hx.elim (fun heq => Or.inr (heq ▸ h2.symm))
                                 (fun heq => Or.inl (heq ▸ h1.symm))⟩
    · intro ⟨a, b⟩ hab
      simp only [Finset.mem_filter] at hab
      rw [Finset.prod_pair hab.2.ne]

  -- Step 2: Expand e_2 * e_1
  rw [h_e2, esymm_one]
  rw [Finset.sum_mul]
  conv_lhs => arg 2; ext a; rw [Finset.sum_mul]
  simp only [Finset.mul_sum]

  -- Step 3: Simplify the if-then-else in the product
  have h_prod : ∀ a b c : Fin N,
      (if a < b then (X a : MvPolynomial (Fin N) ℤ) * X b else 0) * X c =
      if a < b then X a * X b * X c else 0 := fun _ _ _ => by split_ifs <;> ring
  conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext c; rw [h_prod a b c]

  -- Step 4: Pull out the if from the innermost sum
  have h_sum_if : ∀ a b : Fin N,
      (∑ c : Fin N, if a < b then (X a : MvPolynomial (Fin N) ℤ) * X b * X c else 0) =
      if a < b then ∑ c : Fin N, X a * X b * X c else 0 := fun a b => by
    split_ifs <;> simp
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [h_sum_if a b]

  -- Step 5: Factor out X_a * X_b
  have h_factor : ∀ a b : Fin N,
      (if a < b then (∑ c : Fin N, (X a : MvPolynomial (Fin N) ℤ) * X b * X c) else 0) =
      if a < b then X a * X b * (∑ c : Fin N, X c) else 0 := fun a b => by
    split_ifs <;> [rw [Finset.mul_sum]; rfl]
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [h_factor a b]

  -- Step 6: Split ∑_c X_c = X_a + X_b + ∑_{c ≠ a, c ≠ b} X_c
  have h_sum_split : ∀ a b : Fin N, a < b →
      (∑ c : Fin N, (X c : MvPolynomial (Fin N) ℤ)) =
      X a + X b + ∑ c : Fin N, if c ≠ a ∧ c ≠ b then X c else 0 := by
    intros a b hab
    have h1 : (Finset.univ : Finset (Fin N)).filter (fun c => ¬(c ≠ a ∧ c ≠ b)) = {a, b} := by
      ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                        Finset.mem_insert, Finset.mem_singleton]; push Not
      exact ⟨fun h => by by_cases hca : c = a; exact Or.inl hca; exact Or.inr (h hca),
             fun h => h.elim (fun rfl => fun haa => (haa rfl).elim) (fun rfl _ => rfl)⟩
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => c ≠ a ∧ c ≠ b)]
    rw [h1, Finset.sum_pair hab.ne, Finset.sum_filter]
    ring

  -- Step 7: Apply the split and expand
  have h_expand : ∀ a b : Fin N,
      (if a < b then (X a : MvPolynomial (Fin N) ℤ) * X b * (∑ c : Fin N, X c) else 0) =
      (if a < b then X a * X a * X b else 0) +
      (if a < b then X a * X b * X b else 0) +
      (if a < b then X a * X b * (∑ c : Fin N, if c ≠ a ∧ c ≠ b then X c else 0) else 0) := by
    intros a b
    split_ifs with h
    · rw [h_sum_split a b h]; ring
    · ring
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [h_expand a b]

  simp only [Finset.sum_add_distrib]

  -- Step 8: Show that the remaining term equals 3 * e_3
  -- This requires showing that ∑_{a<b} X_a * X_b * (∑_{c ≠ a, c ≠ b} X_c) = 3 * e_3
  -- Each strictly ordered triple (i < j < k) appears 3 times in this sum.
  suffices h_rem : (∑ a : Fin N, ∑ b : Fin N, 
      if a < b then (X a : MvPolynomial (Fin N) ℤ) * X b * 
        (∑ c : Fin N, if c ≠ a ∧ c ≠ b then X c else 0) else 0) = 
      3 * esymm (Fin N) ℤ 3 by ring_nf; rw [h_rem]; ring
  
  rw [esymm_3_eq_sum_strictlyOrdered N]
  -- Expand the inner sum and reindex
  have h_inner : ∀ a b : Fin N,
      (if a < b then (X a : MvPolynomial (Fin N) ℤ) * X b *
        (∑ c : Fin N, if c ≠ a ∧ c ≠ b then X c else 0) else 0) =
      ∑ c : Fin N, if a < b ∧ c ≠ a ∧ c ≠ b then X a * X b * X c else 0 := by
    intros a b
    split_ifs with h
    · rw [Finset.mul_sum]
      congr 1; funext c
      simp only [h, true_and]
      split_ifs <;> ring
    · simp only [h, false_and, ite_false, Finset.sum_const_zero]
  conv_lhs => arg 2; ext a; arg 2; ext b; rw [h_inner a b]

  -- Partition by the position of c relative to a and b
  have h_partition : ∀ a b c : Fin N,
      (if a < b ∧ c ≠ a ∧ c ≠ b then (X a : MvPolynomial (Fin N) ℤ) * X b * X c else 0) =
      (if c < a ∧ a < b then X c * X a * X b else 0) +
      (if a < c ∧ c < b then X a * X c * X b else 0) +
      (if a < b ∧ b < c then X a * X b * X c else 0) := fun a b c => by
    rcases lt_trichotomy a b with hab | hab | hab
    · rcases lt_trichotomy c a with hca | hca | hca
      · have hcb : c < b := hca.trans hab
        have hne_a : c ≠ a := ne_of_lt hca
        have hne_b : c ≠ b := ne_of_lt hcb
        have h_lhs : a < b ∧ c ≠ a ∧ c ≠ b := ⟨hab, hne_a, hne_b⟩
        have h_rhs1 : c < a ∧ a < b := ⟨hca, hab⟩
        have h_rhs2 : ¬(a < c ∧ c < b) := fun ⟨h, _⟩ => (lt_asymm hca) h
        have h_rhs3 : ¬(a < b ∧ b < c) := fun ⟨_, h⟩ => (lt_asymm hcb) h
        simp only [ite_eq_left h_lhs, ite_eq_left h_rhs1, ite_eq_right h_rhs2, ite_eq_right h_rhs3, add_zero]; ring
      · simp only [hca, ne_eq, not_true_eq_false, and_false, false_and, ite_false, add_zero,
                   lt_irrefl, hab, and_true, asymm hab]
      · rcases lt_trichotomy c b with hcb | hcb | hcb
        · have hne_a : c ≠ a := ne_of_gt hca
          have hne_b : c ≠ b := ne_of_lt hcb
          have h_lhs : a < b ∧ c ≠ a ∧ c ≠ b := ⟨hab, hne_a, hne_b⟩
          have h_rhs1 : ¬(c < a ∧ a < b) := fun ⟨h, _⟩ => (lt_asymm h) hca
          have h_rhs2 : a < c ∧ c < b := ⟨hca, hcb⟩
          have h_rhs3 : ¬(a < b ∧ b < c) := fun ⟨_, h⟩ => (lt_asymm hcb) h
          simp only [ite_eq_left h_lhs, ite_eq_right h_rhs1, ite_eq_left h_rhs2, ite_eq_right h_rhs3, add_zero, zero_add]; ring
        · simp only [hcb, ne_eq, not_true_eq_false, ite_false, add_zero, lt_irrefl,
                     and_false, hab, asymm hab, and_true]
        · have hne_a : c ≠ a := ne_of_gt (hab.trans hcb)
          have hne_b : c ≠ b := ne_of_gt hcb
          have h_lhs : a < b ∧ c ≠ a ∧ c ≠ b := ⟨hab, hne_a, hne_b⟩
          have h_rhs1 : ¬(c < a ∧ a < b) := fun ⟨h, _⟩ => (lt_asymm h) (hab.trans hcb)
          have h_rhs2 : ¬(a < c ∧ c < b) := fun ⟨_, h⟩ => (lt_asymm h) hcb
          have h_rhs3 : a < b ∧ b < c := ⟨hab, hcb⟩
          simp only [ite_eq_left h_lhs, ite_eq_right h_rhs1, ite_eq_right h_rhs2, ite_eq_left h_rhs3, add_zero, zero_add]
    · have h_rhs2 : ¬(b < c ∧ c < b) := fun ⟨h1, h2⟩ => (lt_asymm h1) h2
      simp only [hab, lt_irrefl, false_and, ite_false, add_zero, and_false, ite_eq_right h_rhs2]
    · have h_lhs : ¬(a < b ∧ c ≠ a ∧ c ≠ b) := fun ⟨h, _, _⟩ => (lt_asymm h) hab
      have h_rhs1 : ¬(c < a ∧ a < b) := fun ⟨_, h⟩ => (lt_asymm h) hab
      have h_rhs2 : ¬(a < c ∧ c < b) := fun ⟨hac, hcb⟩ => (lt_asymm (hac.trans hcb)) hab
      have h_rhs3 : ¬(a < b ∧ b < c) := fun ⟨h, _⟩ => (lt_asymm h) hab
      simp only [ite_eq_right h_lhs, ite_eq_right h_rhs1, ite_eq_right h_rhs2, ite_eq_right h_rhs3, add_zero]
  conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext c; rw [h_partition a b c]
  simp only [Finset.sum_add_distrib]

  -- Each of the three sums equals e_3, so total is 3 * e_3
  have h1 : (∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N,
      if c < a ∧ a < b then (X c : MvPolynomial (Fin N) ℤ) * X a * X b else 0) =
      ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      if i < j ∧ j < k then X i * X j * X k else 0 := by
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]

  have h2 : (∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N,
      if a < c ∧ c < b then (X a : MvPolynomial (Fin N) ℤ) * X c * X b else 0) =
      ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      if i < j ∧ j < k then X i * X j * X k else 0 := by
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]

  have h3 : (∑ a : Fin N, ∑ b : Fin N, ∑ c : Fin N,
      if a < b ∧ b < c then (X a : MvPolynomial (Fin N) ℤ) * X b * X c else 0) =
      ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      if i < j ∧ j < k then X i * X j * X k else 0 := rfl

  rw [h1, h2, h3]
  ring

/-- The Schur polynomial s_{(2,1,0,...,0)} equals e_2 * e_1 - e_3.
    Example \ref{exa.sf.schur-h-e}(c) in the source.

    This is computed by summing over all SSYT of shape (2,1), which have the form
    ⌜i j⌝ with i ≤ j and i < k. The sum splits into cases based on the relative
    ⌞k⌟  order of i, j, k. -/
theorem schurPoly_21_eq [DecidableEq (Fin N)] (hN : 2 ≤ N) (lam : NPartition N)
    (hlam : lam.parts 0 = 2 ∧ lam.parts ⟨1, by omega⟩ = 1 ∧
            ∀ i : Fin N, 2 ≤ i.val → lam.parts i = 0) :
    schurPoly lam = MvPolynomial.esymm (Fin N) ℤ 2 * MvPolynomial.esymm (Fin N) ℤ 1 -
                    MvPolynomial.esymm (Fin N) ℤ 3 := by
  -- The proof proceeds by:
  -- 1. Characterizing the Young diagram as {(0,0), (0,1), (1,0)}
  -- 2. Showing SSYT fillings correspond to (i, j, k) with i ≤ j and i < k
  -- 3. Computing the sum and showing it equals e_2 * e_1 - e_3

  -- Step 1: The Young diagram has exactly 3 cells
  have hdiag : lam.youngDiagram = {(0, 0), (0, 1), (⟨1, by omega⟩, 0)} := by
    ext ⟨i, j⟩
    simp only [NPartition.mem_youngDiagram, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · intro hj
      by_cases hi0 : i = 0
      · subst hi0; rw [hlam.1] at hj
        interval_cases j <;> simp
      · by_cases hi1 : i.val = 1
        · have hi1' : i = ⟨1, by omega⟩ := by ext; exact hi1
          rw [hi1', hlam.2.1] at hj
          interval_cases j
          right; right; constructor; ext; exact hi1; rfl
        · have hi2 : 2 ≤ i.val := by
            have h0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
            omega
          rw [hlam.2.2 i hi2] at hj
          exact absurd hj (Nat.not_lt_zero _)
    · intro h
      rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hi, rfl⟩)
      · rw [hlam.1]; omega
      · rw [hlam.1]; omega
      · have : i = ⟨1, by omega⟩ := hi
        rw [this, hlam.2.1]; omega

  -- Step 2: An SSYT filling f assigns:
  -- - i = f(0,0) to cell (0,0)
  -- - j = f(0,1) to cell (0,1)
  -- - k = f(1,0) to cell (1,0)
  -- with constraints: i ≤ j (row-weak) and i < k (column-strict)
  -- The monomial is X_i * X_j * X_k

  -- The sum over SSYT fillings equals ∑_{i ≤ j, i < k} X_i * X_j * X_k

  -- This equals e_2 * e_1 - e_3 by the following computation:
  -- The SSYT sum splits into 4 cases based on the relative order of i, j, k:
  -- Case A (i = j, i < k): ∑_{i < k} X_i² * X_k
  -- Case B (i < j = k): ∑_{i < j} X_i * X_j²
  -- Case C (i < j < k): e_3
  -- Case D (i < k < j): e_3 (by relabeling)
  -- Total: ∑_{i < k} X_i² * X_k + ∑_{i < j} X_i * X_j² + 2 * e_3

  -- Meanwhile, e_2 * e_1 = ∑_{a < b, c} X_a * X_b * X_c, which partitions as:
  -- c < a: e_3, c = a: ∑ X_a² * X_b, a < c < b: e_3, c = b: ∑ X_a * X_b², c > b: e_3
  -- Total: 3 * e_3 + ∑ X_a² * X_b + ∑ X_a * X_b²

  -- Therefore e_2 * e_1 - e_3 = 2 * e_3 + ∑ X_a² * X_b + ∑ X_a * X_b² = SSYT sum

  -- The detailed verification requires establishing bijections between:
  -- 1. SSYT fillings and triples (i, j, k) with i ≤ j ∧ i < k
  -- 2. The partition of these triples into the 4 cases
  -- 3. The correspondence with e_2 * e_1 - e_3

  -- Convert to a sum over triples
  have h_sum : schurPoly lam =
      ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
        if i ≤ j ∧ i < k then X i * X j * X k else 0 := by
    -- The bijection maps f to (f(c00), f(c01), f(c10))
    unfold schurPoly
    simp only [ssytFillingsYoung]
    
    -- Define the three cells of the Young diagram
    have h1lt : 1 < N := Nat.lt_of_lt_of_le Nat.one_lt_two hN
    have h00 : (0, 0) ∈ lam.youngDiagram := by rw [hdiag]; simp
    have h01 : (0, 1) ∈ lam.youngDiagram := by rw [hdiag]; simp
    have h10 : ((⟨1, h1lt⟩ : Fin N), 0) ∈ lam.youngDiagram := by rw [hdiag]; simp
    let c00 : { c // c ∈ lam.youngDiagram } := ⟨(0, 0), h00⟩
    let c01 : { c // c ∈ lam.youngDiagram } := ⟨(0, 1), h01⟩
    let c10 : { c // c ∈ lam.youngDiagram } := ⟨(⟨1, h1lt⟩, 0), h10⟩
    
    -- Every cell is one of these three
    have hcells : ∀ c : { c // c ∈ lam.youngDiagram }, c = c00 ∨ c = c01 ∨ c = c10 := by
      intro ⟨c, hc⟩
      rw [hdiag] at hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with (rfl | rfl | hc10)
      · left; rfl
      · right; left; rfl
      · right; right
        simp only [c10, Subtype.mk.injEq]
        exact hc10
    
    -- The cells are distinct
    have hne01 : c00 ≠ c01 := by simp [c00, c01]
    have hne02 : c00 ≠ c10 := by simp [c00, c10]
    have hne12 : c01 ≠ c10 := by simp [c01, c10]

    -- The bijection is established via Finset.sum_nbij':
    -- Forward: f ↦ (f(c00), f(c01), f(c10))
    -- Backward: (i,j,k) ↦ filling with f(c00)=i, f(c01)=j, f(c10)=k
    -- SSYT condition ↔ i ≤ j ∧ i < k
    -- Monomial: X(f c00) * X(f c01) * X(f c10) = X i * X j * X k
    
    -- Step 1: SSYT condition ↔ f(c00) ≤ f(c01) ∧ f(c00) < f(c10)
    have h_ssyt_iff : ∀ f : Filling lam,
        isSSYTFillingYoung lam f ↔ (f c00 ≤ f c01 ∧ f c00 < f c10) := by
      intro f
      unfold isSSYTFillingYoung
      have h00_coord : (c00 : Fin N × ℕ) = (0, 0) := rfl
      have h01_coord : (c01 : Fin N × ℕ) = (0, 1) := rfl
      have h10_coord : (c10 : Fin N × ℕ) = (⟨1, h1lt⟩, 0) := rfl
      constructor
      · intro ⟨hrow, hcol⟩
        refine ⟨hrow c00 c01 rfl (by norm_num), ?_⟩
        have h0lt1 : (0 : Fin N) < ⟨1, h1lt⟩ := by simp [Fin.lt_def]
        exact hcol c00 c10 rfl h0lt1
      · intro ⟨h01', h10'⟩
        constructor
        · intro c1 c2 hrow_eq hcol_lt
          rcases hcells c1 with (rfl | rfl | rfl) <;> rcases hcells c2 with (rfl | rfl | rfl)
          · exact le_refl _
          · exact h01'
          · simp only [h00_coord, h10_coord] at hrow_eq; exact absurd hrow_eq (by simp [Fin.ext_iff])
          · simp only [h00_coord, h01_coord] at hcol_lt; omega
          · exact le_refl _
          · simp only [h01_coord, h10_coord] at hrow_eq; exact absurd hrow_eq (by simp [Fin.ext_iff])
          · simp only [h00_coord, h10_coord] at hrow_eq; exact absurd hrow_eq.symm (by simp [Fin.ext_iff])
          · simp only [h01_coord, h10_coord] at hrow_eq; exact absurd hrow_eq.symm (by simp [Fin.ext_iff])
          · exact le_refl _
        · intro c1 c2 hcol_eq hrow_lt
          rcases hcells c1 with (rfl | rfl | rfl) <;> rcases hcells c2 with (rfl | rfl | rfl)
          · simp only [h00_coord, Fin.lt_def, Fin.val_zero] at hrow_lt; exact absurd hrow_lt (lt_irrefl _)
          · simp only [h00_coord, h01_coord] at hcol_eq; omega
          · exact h10'
          · simp only [h00_coord, h01_coord] at hcol_eq; omega
          · simp only [h01_coord, Fin.lt_def, Fin.val_zero] at hrow_lt; exact absurd hrow_lt (lt_irrefl _)
          · simp only [h01_coord, h10_coord] at hcol_eq; omega
          · simp only [h00_coord, h10_coord, Fin.lt_def, Fin.val_zero] at hrow_lt; omega
          · simp only [h01_coord, h10_coord] at hcol_eq; omega
          · simp only [h10_coord, Fin.lt_def] at hrow_lt; exact absurd hrow_lt (lt_irrefl _)
    
    -- Step 2: Define equivalence between { c // c ∈ lam.youngDiagram } and Fin 3
    let e : { c // c ∈ lam.youngDiagram } ≃ Fin 3 := {
      toFun := fun c => if c = c00 then 0 else if c = c01 then 1 else 2
      invFun := fun i => if i = 0 then c00 else if i = 1 then c01 else c10
      left_inv := fun c => by
        rcases hcells c with (rfl | rfl | rfl) <;> simp [c00, c01, c10]
      right_inv := fun i => by
        fin_cases i <;> simp [c00, c01, c10]
    }
    
    -- Step 3: Monomial equality
    have h_mono : ∀ f : Filling lam,
        fillingMonomialYoung f = X (f c00) * X (f c01) * X (f c10) := by
      intro f
      unfold fillingMonomialYoung
      rw [Fintype.prod_equiv e (fun c => X (f c)) (fun i => X (f (e.symm i)))]
      · rw [Fin.prod_univ_three]
        simp only [e, Equiv.symm]
        rfl
      · intro c
        simp only [e.symm_apply_apply]
    
    -- Step 4: Rewrite filter using the equivalence
    have h_filter_eq : Finset.univ.filter (isSSYTFillingYoung lam) =
        Finset.univ.filter (fun f : Filling lam => f c00 ≤ f c01 ∧ f c00 < f c10) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_ssyt_iff f
    
    rw [h_filter_eq]
    simp_rw [h_mono]
    
    -- Convert RHS to sum over filtered triples
    have h_rhs : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
              if i ≤ j ∧ i < k then (X i : MvPolynomial (Fin N) ℤ) * X j * X k else 0) =
            ∑ ijk ∈ Finset.univ.filter (fun ijk : Fin N × Fin N × Fin N => ijk.1 ≤ ijk.2.1 ∧ ijk.1 < ijk.2.2),
              X ijk.1 * X ijk.2.1 * X ijk.2.2 := by
      simp only [Finset.sum_filter]
      simp only [← Finset.univ_product_univ, Finset.sum_product]
    rw [h_rhs]
    
    -- Use the bijection
    let toTriple : Filling lam → Fin N × Fin N × Fin N := 
      fun f => (f c00, f c01, f c10)
    let fromTriple : Fin N × Fin N × Fin N → Filling lam :=
      fun ⟨i, j, k⟩ c => if c = c00 then i else if c = c01 then j else k
    
    apply Finset.sum_nbij' toTriple fromTriple
    · -- hi: forward map lands in target
      intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, toTriple] at hf ⊢
      exact hf
    · -- hj: backward map lands in source
      intro ijk hijk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hijk ⊢
      -- fromTriple ijk c00 = ijk.1, fromTriple ijk c01 = ijk.2.1, fromTriple ijk c10 = ijk.2.2
      convert hijk using 2
      · simp only [fromTriple, ↓reduceIte]
      · simp only [fromTriple, hne01.symm, ↓reduceIte]
      · simp only [fromTriple, ↓reduceIte]
      · simp only [fromTriple, hne02.symm, hne12.symm, ↓reduceIte]
    · -- left_inv
      intro f _
      simp only [toTriple, fromTriple]
      funext c
      rcases hcells c with (rfl | rfl | rfl)
      · simp only [↓reduceIte]
      · simp only [hne01.symm, ↓reduceIte]
      · simp only [hne02.symm, hne12.symm, ↓reduceIte]
    · -- right_inv
      intro ⟨i, j, k⟩ _
      simp only [toTriple, fromTriple, ↓reduceIte, hne01.symm, hne02.symm, hne12.symm]
    · -- monomial equality
      intro f _
      rfl

  rw [h_sum]

  -- Now prove the polynomial identity
  -- ∑_{i ≤ j, i < k} X_i * X_j * X_k = e_2 * e_1 - e_3

  -- The proof proceeds by decomposing both sides:
  -- LHS = 2*e_3 + ∑_{a<b} X_a² X_b + ∑_{a<b} X_a X_b²
  -- RHS = 3*e_3 + ∑_{a<b} X_a² X_b + ∑_{a<b} X_a X_b² - e_3
  --     = 2*e_3 + ∑_{a<b} X_a² X_b + ∑_{a<b} X_a X_b²

  -- Define auxiliary sums
  let sumSqFirst : MvPolynomial (Fin N) ℤ :=
    ∑ a : Fin N, ∑ b : Fin N, if a < b then X a * X a * X b else 0
  let sumSqSecond : MvPolynomial (Fin N) ℤ :=
    ∑ a : Fin N, ∑ b : Fin N, if a < b then X a * X b * X b else 0

  -- Key lemma: e_3 equals sum over strictly ordered triples
  have h_e3 : esymm (Fin N) ℤ 3 =
      ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
        if i < j ∧ j < k then X i * X j * X k else 0 :=
    esymm_3_eq_sum_strictlyOrdered N

  -- Key lemma: sum over i < k < j equals e_3 (by relabeling j ↔ k)
  have h_ikj : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      if i < k ∧ k < j then X i * X j * X k else 0) = esymm (Fin N) ℤ 3 := by
    -- Relabeling: swap j and k in the sum
    rw [h_e3]
    congr 1
    funext i
    rw [Finset.sum_comm]
    congr 1
    funext j
    congr 1
    funext k
    split_ifs <;> ring

  -- LHS decomposition: SSYT sum = 2*e_3 + sumSqFirst + sumSqSecond
  have h_lhs : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
      if i ≤ j ∧ i < k then X i * X j * X k else 0) =
      2 * esymm (Fin N) ℤ 3 + sumSqFirst + sumSqSecond := by
    -- Split by i = j vs i < j
    have split_ij_ik : ∀ i j k : Fin N,
        (if i ≤ j ∧ i < k then (X i : MvPolynomial (Fin N) ℤ) * X j * X k else 0) =
        (if i = j ∧ i < k then X i * X j * X k else 0) +
        (if i < j ∧ i < k then X i * X j * X k else 0) := by
      intro i j k
      rcases le_or_gt i j with hle | hgt
      · rcases eq_or_lt_of_le hle with rfl | hlt
        · simp only [le_refl, true_and, lt_self_iff_false, false_and, ↓reduceIte]; ring
        · simp only [hle, true_and, ne_of_lt hlt, false_and, hlt, ↓reduceIte, zero_add]
      · simp only [not_le.mpr hgt, false_and, ne_of_gt hgt, not_lt.mpr (le_of_lt hgt), ↓reduceIte, add_zero]

    conv_lhs =>
      arg 2; ext i; arg 2; ext j; arg 2; ext k
      rw [split_ij_ik i j k]
    simp only [Finset.sum_add_distrib]

    -- Sum 1: ∑_{i = j, i < k} = sumSqFirst
    have h1 : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
        if i = j ∧ i < k then (X i : MvPolynomial (Fin N) ℤ) * X j * X k else 0) = sumSqFirst := by
      simp only [sumSqFirst]
      congr 1; funext i
      rw [Finset.sum_eq_single i]
      · simp only [true_and]
      · intro j _ hji; simp only [hji.symm, false_and, ↓reduceIte, Finset.sum_const_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi

    -- Sum 2: ∑_{i < j, i < k} = 2*e_3 + sumSqSecond
    have split_ij_jk : ∀ i j k : Fin N,
        (if i < j ∧ i < k then (X i : MvPolynomial (Fin N) ℤ) * X j * X k else 0) =
        (if i < j ∧ j < k then X i * X j * X k else 0) +
        (if i < j ∧ j = k then X i * X j * X k else 0) +
        (if i < k ∧ k < j then X i * X j * X k else 0) := by
      intro i j k
      rcases lt_trichotomy j k with hjk | rfl | hkj
      · by_cases hij : i < j
        · have hik : i < k := lt_trans hij hjk
          simp only [hij, hik, hjk, true_and, ne_of_lt hjk, not_lt.mpr (le_of_lt hjk), ↓reduceIte, add_zero]
        · have hnjk : ¬ k < j := not_lt.mpr (le_of_lt hjk)
          simp only [hij, false_and, ↓reduceIte, hnjk, and_false, add_zero]
      · by_cases hij : i < j
        · simp only [hij, true_and, lt_self_iff_false, ↓reduceIte]; ring
        · simp only [hij, false_and, ↓reduceIte, add_zero]
      · by_cases hij : i < j
        · by_cases hik : i < k
          · simp only [hij, hik, hkj, true_and, not_lt.mpr (le_of_lt hkj), ne_of_gt hkj, ↓reduceIte, add_zero, zero_add]
          · have hnjk : ¬ j < k := not_lt.mpr (le_of_lt hkj)
            have hnek : j ≠ k := ne_of_gt hkj
            simp only [hij, hik, false_and, hnjk, hnek, ↓reduceIte, and_false, add_zero]
        · by_cases hik : i < k
          · exact absurd (lt_trans hik hkj) hij
          · simp only [hij, hik, false_and, ↓reduceIte, add_zero]

    have h2 : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
        if i < j ∧ i < k then (X i : MvPolynomial (Fin N) ℤ) * X j * X k else 0) =
        2 * esymm (Fin N) ℤ 3 + sumSqSecond := by
      conv_lhs =>
        arg 2; ext i; arg 2; ext j; arg 2; ext k
        rw [split_ij_jk i j k]
      simp only [Finset.sum_add_distrib]

      have hA : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
          if i < j ∧ j < k then (X i : MvPolynomial (Fin N) ℤ) * X j * X k else 0) = esymm (Fin N) ℤ 3 := h_e3.symm

      have hB : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
          if i < j ∧ j = k then (X i : MvPolynomial (Fin N) ℤ) * X j * X k else 0) = sumSqSecond := by
        simp only [sumSqSecond]
        congr 1; funext i; congr 1; funext j
        rw [Finset.sum_eq_single j]
        · simp only [and_true]
        · intro k _ hkj; simp only [hkj.symm, and_false, ↓reduceIte]
        · intro hj; exact absurd (Finset.mem_univ j) hj

      rw [hA, hB, h_ikj]
      ring

    rw [h1, h2]
    ring

  -- RHS decomposition: e_2 * e_1 = 3*e_3 + sumSqFirst + sumSqSecond
  have h_rhs : esymm (Fin N) ℤ 2 * esymm (Fin N) ℤ 1 =
      3 * esymm (Fin N) ℤ 3 + sumSqFirst + sumSqSecond :=
    esymm_2_mul_esymm_1_expansion N

  -- Combine: LHS = RHS - e_3
  rw [h_lhs, h_rhs]
  ring

/-! ## Partition Containment

The partition containment infrastructure (LE, Preorder, PartialOrder, size, etc.)
is now provided by `NPartition.lean`. See `NPartition.instLE`, `NPartition.size`, etc.
-/


/-! ## Skew Young Diagrams

**Note**: The canonical `Finset` version of skew Young diagrams is `NPartition.skewYoungDiagram`
in `NPartition.lean`, which does not require `[NeZero N]`. The definition below is retained
for backwards compatibility but prefer `NPartition.skewYoungDiagram` for new code.

See also `AlgebraicCombinatorics.skewYoungDiagram` in LittlewoodRichardson.lean for the
`Set` version with 1-indexed columns (textbook convention).
-/

/-- The skew Young diagram Y(λ/μ) is the set difference Y(λ) \ Y(μ).
    Definition \ref{def.sf.skew-diag} in the source.

    **Note**: This is a duplicate of `NPartition.skewYoungDiagram` that requires `[NeZero N]`.
    Prefer `NPartition.skewYoungDiagram` for new code as it works for all `N`.

    For N-partitions λ and μ with μ ⊆ λ, the skew Young diagram Y(λ/μ) is defined as:
    ```
    Y(λ) \ Y(μ) = {(i,j) | i ∈ [N] and j ∈ [λ_i] \ [μ_i]}
                = {(i,j) | i ∈ [N] and j ∈ ℤ and μ_i < j ≤ λ_i}
    ```
    (The second form uses 1-indexed j as in the textbook.)

    In our 0-indexed formalization, this becomes:
    ```
    Y(λ/μ) = {(i,j) | i ∈ Fin N and μ_i ≤ j < λ_i}
    ```

    Example: Y((4,3,1)/(2,1,0)) consists of cells:
    - Row 0: (0, 2), (0, 3)  (since μ₀ = 2, λ₀ = 4)
    - Row 1: (1, 1), (1, 2)  (since μ₁ = 1, λ₁ = 3)
    - Row 2: (2, 0)          (since μ₂ = 0, λ₂ = 1) -/
def skewYoungDiagram {N : ℕ} [NeZero N] (lam mu : NPartition N) : Finset (Fin N × ℕ) :=
  lam.youngDiagram \ mu.youngDiagram

/-- Membership in a skew Young diagram: (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i.
    This is the 0-indexed version of the textbook condition μ_i < j ≤ λ_i. -/
theorem mem_skewYoungDiagram {N : ℕ} [NeZero N] {lam mu : NPartition N} {c : Fin N × ℕ} :
    c ∈ skewYoungDiagram lam mu ↔ mu.parts c.1 ≤ c.2 ∧ c.2 < lam.parts c.1 := by
  simp only [skewYoungDiagram, Finset.mem_sdiff, NPartition.mem_youngDiagram]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨Nat.not_lt.mp h2, h1⟩
  · intro ⟨h1, h2⟩
    exact ⟨h2, Nat.not_lt.mpr h1⟩

/-- Alternative characterization: membership in terms of the interval [μ_i, λ_i). -/
theorem mem_skewYoungDiagram' {N : ℕ} [NeZero N] {lam mu : NPartition N} {i : Fin N} {j : ℕ} :
    (i, j) ∈ skewYoungDiagram lam mu ↔ j ∈ Finset.Ico (mu.parts i) (lam.parts i) := by
  rw [mem_skewYoungDiagram, Finset.mem_Ico]

/-- The skew Young diagram is empty when μ = λ. -/
@[simp]
theorem skewYoungDiagram_self {N : ℕ} [NeZero N] (lam : NPartition N) :
    skewYoungDiagram lam lam = ∅ := by
  ext c
  rw [mem_skewYoungDiagram]
  constructor
  · intro ⟨h1, h2⟩
    omega
  · simp

/-- The skew Young diagram equals the full diagram when μ = 0. -/
@[simp]
theorem skewYoungDiagram_zero {N : ℕ} [NeZero N] (lam : NPartition N) :
    skewYoungDiagram lam 0 = lam.youngDiagram := by
  ext c
  simp only [mem_skewYoungDiagram, NPartition.mem_youngDiagram, NPartition.zero_parts]
  constructor
  · intro ⟨_, h2⟩
    exact h2
  · intro h
    exact ⟨Nat.zero_le _, h⟩

/-- Convexity of skew Young diagrams: if (a,b) and (e,f) are in Y(lam/mu), and
    a ≤ c ≤ e and b ≤ d ≤ f, then (c,d) ∈ Y(lam/mu).
    Lemma \ref{lem.sf.skew-diag.convexity} in the source. -/
theorem skewYoungDiagram_convex {N : ℕ} [NeZero N] {lam mu : NPartition N}
    {a e : Fin N} {b f : ℕ}
    (hab : (a, b) ∈ skewYoungDiagram lam mu)
    (hef : (e, f) ∈ skewYoungDiagram lam mu)
    {c : Fin N} {d : ℕ}
    (hac : a ≤ c) (hce : c ≤ e) (hbd : b ≤ d) (hdf : d ≤ f) :
    (c, d) ∈ skewYoungDiagram lam mu := by
  rw [mem_skewYoungDiagram] at hab hef ⊢
  constructor
  · -- mu_c ≤ d
    -- We have mu_a ≤ b ≤ d and mu_c ≤ mu_a (since mu is decreasing and a ≤ c)
    calc mu.parts c ≤ mu.parts a := mu.monotone a c hac
      _ ≤ b := hab.1
      _ ≤ d := hbd
  · -- d < lam_c
    -- We have d ≤ f < lam_e ≤ lam_c (since lam is decreasing and c ≤ e)
    calc d ≤ f := hdf
      _ < lam.parts e := hef.2
      _ ≤ lam.parts c := lam.monotone c e hce

/-! ## Skew Young Tableaux -/

/-- A skew Young tableau of shape λ/μ is a filling of Y(λ/μ) with elements of [N].
    Definition \ref{def.sf.skew-tab} in the source.

    Formally, a Young tableau of shape λ/μ is a map T : Y(λ/μ) → [N].
    We represent this as a total function `entry : Fin N × ℕ → Fin N` with a support
    condition that entries outside the skew diagram are 0.

    Young tableaux of shape λ/μ are often called "skew Young tableaux".

    Note: If μ ⊈ λ (i.e., not μ ≤ λ), then there are no Young tableaux of shape λ/μ
    because the skew diagram would be empty or malformed. -/
structure SkewYoungTableau {N : ℕ} [NeZero N] (lam mu : NPartition N) where
  /-- The filling function T : Y(λ/μ) → [N] -/
  entry : Fin N × ℕ → Fin N
  /-- The entry is only meaningful for cells in the skew diagram -/
  support : ∀ c, c ∉ skewYoungDiagram lam mu → entry c = 0

namespace SkewYoungTableau

variable {N : ℕ} [NeZero N] {lam mu : NPartition N}

/-- Two skew Young tableaux are equal if their entries agree on the skew diagram -/
@[ext]
theorem ext {T₁ T₂ : SkewYoungTableau lam mu}
    (h : ∀ c ∈ skewYoungDiagram lam mu, T₁.entry c = T₂.entry c) : T₁ = T₂ := by
  cases T₁ with | mk e₁ s₁ => ?_
  cases T₂ with | mk e₂ s₂ => ?_
  simp only [mk.injEq]
  funext c
  by_cases hc : c ∈ skewYoungDiagram lam mu
  · exact h c hc
  · rw [s₁ c hc, s₂ c hc]

/-- Coercion to function -/
instance : CoeFun (SkewYoungTableau lam mu) (fun _ => Fin N × ℕ → Fin N) := ⟨entry⟩

/-- The empty skew tableau when lam = mu -/
def empty (lam : NPartition N) : SkewYoungTableau lam lam where
  entry := fun _ => 0
  support := fun _ _ => rfl

/-- The number of cells in a skew Young tableau -/
def size (_T : SkewYoungTableau lam mu) : ℕ :=
  (skewYoungDiagram lam mu).card

/-- The size of a skew Young tableau equals the cardinality of its skew Young diagram. -/
@[simp]
theorem size_eq (T : SkewYoungTableau lam mu) : T.size = (skewYoungDiagram lam mu).card := rfl

/-- Entry at a specific row and column -/
def entryAt (T : SkewYoungTableau lam mu) (i : Fin N) (j : ℕ) : Fin N :=
  T.entry (i, j)

/-- A skew tableau is nonempty if the skew diagram is nonempty -/
def Nonempty (_T : SkewYoungTableau lam mu) : Prop :=
  (skewYoungDiagram lam mu).Nonempty

/-- Entry outside the skew diagram is zero -/
theorem entry_of_not_mem (T : SkewYoungTableau lam mu) {c : Fin N × ℕ}
    (hc : c ∉ skewYoungDiagram lam mu) : T.entry c = 0 :=
  T.support c hc

/-- Entry at a cell (i, j) where j < mu_i is zero -/
theorem entry_of_lt_mu (T : SkewYoungTableau lam mu) {i : Fin N} {j : ℕ}
    (hj : j < mu.parts i) : T.entry (i, j) = 0 := by
  apply T.support
  rw [mem_skewYoungDiagram]
  simp only [not_and, not_lt]
  intro _
  omega

/-- Entry at a cell (i, j) where j ≥ lam_i is zero -/
theorem entry_of_ge_lam (T : SkewYoungTableau lam mu) {i : Fin N} {j : ℕ}
    (hj : lam.parts i ≤ j) : T.entry (i, j) = 0 := by
  apply T.support
  rw [mem_skewYoungDiagram]
  simp only [not_and, not_lt]
  intro _
  omega

end SkewYoungTableau

/-- A semistandard skew Young tableau is a skew tableau where:
    - entries increase weakly along each row (left to right)
    - entries increase strictly down each column (top to bottom)
    Definition \ref{def.sf.skew-ssyt} in the source.

    **Note:** This is one of two SkewSSYT definitions in this project:
    - **This definition** (`SchurBasics.SkewSSYT`): Uses `entry : Fin N × ℕ → Fin N` with a
      support condition. Extends `SkewYoungTableau`. Takes `lam mu : NPartition N` as separate
      arguments. Requires `[NeZero N]`. Field names: `row_weak`, `col_strict`.
    - **Alternative definition** (`SymmetricFunctions.SkewSSYT` in `PieriJacobiTrudi.lean`):
      Uses dependent types. Takes `s : SkewPartition N` as a single bundled argument.
      No `[NeZero N]` requirement. Field names: `rowWeak`, `colStrict`.

    See `SSYTEquiv.lean` for conversions between representations. -/
structure SkewSSYT {N : ℕ} [NeZero N] (lam mu : NPartition N) extends SkewYoungTableau lam mu where
  /-- Entries increase weakly along rows -/
  row_weak : ∀ i : Fin N, ∀ j₁ j₂ : ℕ,
    (i, j₁) ∈ skewYoungDiagram lam mu → (i, j₂) ∈ skewYoungDiagram lam mu → j₁ < j₂ →
    entry (i, j₁) ≤ entry (i, j₂)
  /-- Entries increase strictly down columns -/
  col_strict : ∀ i₁ i₂ : Fin N, ∀ j : ℕ,
    (i₁, j) ∈ skewYoungDiagram lam mu → (i₂, j) ∈ skewYoungDiagram lam mu → i₁ < i₂ →
    entry (i₁, j) < entry (i₂, j)

/-! ## Properties of Semistandard Skew Tableaux -/

/-- In a semistandard skew tableau, entries increase weakly along rows (general version).
    Lemma \ref{lem.sf.skew-ssyt.increase}(a) in the source. -/
theorem SkewSSYT.row_weak_of_le {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (T : SkewSSYT lam mu) {i : Fin N} {j₁ j₂ : ℕ}
    (h1 : (i, j₁) ∈ skewYoungDiagram lam mu)
    (h2 : (i, j₂) ∈ skewYoungDiagram lam mu)
    (hle : j₁ ≤ j₂) :
    T.entry (i, j₁) ≤ T.entry (i, j₂) := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · rfl
  · exact T.row_weak i j₁ j₂ h1 h2 hlt

/-- In a semistandard skew tableau, entries increase weakly down columns.
    Lemma \ref{lem.sf.skew-ssyt.increase}(b) in the source. -/
theorem SkewSSYT.col_weak {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (T : SkewSSYT lam mu) {i₁ i₂ : Fin N} {j : ℕ}
    (h1 : (i₁, j) ∈ skewYoungDiagram lam mu)
    (h2 : (i₂, j) ∈ skewYoungDiagram lam mu)
    (hle : i₁ ≤ i₂) :
    T.entry (i₁, j) ≤ T.entry (i₂, j) := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · rfl
  · exact le_of_lt (T.col_strict i₁ i₂ j h1 h2 hlt)

/-- In a semistandard skew tableau, entries increase strictly down columns.
    Lemma \ref{lem.sf.skew-ssyt.increase}(c) in the source. -/
theorem SkewSSYT.col_strict_of_lt {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (T : SkewSSYT lam mu) {i₁ i₂ : Fin N} {j : ℕ}
    (h1 : (i₁, j) ∈ skewYoungDiagram lam mu)
    (h2 : (i₂, j) ∈ skewYoungDiagram lam mu)
    (hlt : i₁ < i₂) :
    T.entry (i₁, j) < T.entry (i₂, j) :=
  T.col_strict i₁ i₂ j h1 h2 hlt

/-- In a semistandard skew tableau, if (i₁, j₁) ≤ (i₂, j₂) componentwise,
    then T(i₁, j₁) ≤ T(i₂, j₂).
    Lemma \ref{lem.sf.skew-ssyt.increase}(d) in the source. -/
theorem SkewSSYT.monotone {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (T : SkewSSYT lam mu) {i₁ i₂ : Fin N} {j₁ j₂ : ℕ}
    (h1 : (i₁, j₁) ∈ skewYoungDiagram lam mu)
    (h2 : (i₂, j₂) ∈ skewYoungDiagram lam mu)
    (hi : i₁ ≤ i₂) (hj : j₁ ≤ j₂) :
    T.entry (i₁, j₁) ≤ T.entry (i₂, j₂) := by
  -- Use convexity to show (i₂, j₁) is in the diagram
  have hmid : (i₂, j₁) ∈ skewYoungDiagram lam mu :=
    skewYoungDiagram_convex h1 h2 hi (le_refl i₂) (le_refl j₁) hj
  calc T.entry (i₁, j₁) ≤ T.entry (i₂, j₁) := T.col_weak h1 hmid hi
    _ ≤ T.entry (i₂, j₂) := T.row_weak_of_le hmid h2 hj

/-- In a semistandard skew tableau, if i₁ < i₂ and j₁ ≤ j₂,
    then T(i₁, j₁) < T(i₂, j₂).
    Lemma \ref{lem.sf.skew-ssyt.increase}(e) in the source. -/
theorem SkewSSYT.strict_monotone {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (T : SkewSSYT lam mu) {i₁ i₂ : Fin N} {j₁ j₂ : ℕ}
    (h1 : (i₁, j₁) ∈ skewYoungDiagram lam mu)
    (h2 : (i₂, j₂) ∈ skewYoungDiagram lam mu)
    (hi : i₁ < i₂) (hj : j₁ ≤ j₂) :
    T.entry (i₁, j₁) < T.entry (i₂, j₂) := by
  -- Use convexity to show (i₂, j₁) is in the diagram
  have hmid : (i₂, j₁) ∈ skewYoungDiagram lam mu :=
    skewYoungDiagram_convex h1 h2 (le_of_lt hi) (le_refl i₂) (le_refl j₁) hj
  calc T.entry (i₁, j₁) < T.entry (i₂, j₁) := T.col_strict_of_lt h1 hmid hi
    _ ≤ T.entry (i₂, j₂) := T.row_weak_of_le hmid h2 hj

/-! ## Monomials from Skew Tableaux -/

/-- The monomial x_T associated to a skew Young tableau T.
    Definition \ref{def.sf.ytab.skew-xT} in the source.
    x_T = ∏_{c ∈ Y(lam/mu)} x_{T(c)} -/
def SkewYoungTableau.monomial {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (T : SkewYoungTableau lam mu) : MvPolynomial (Fin N) ℤ :=
  ∏ c ∈ skewYoungDiagram lam mu, X (T.entry c)

namespace SkewYoungTableau

variable {N : ℕ} [NeZero N] {lam mu : NPartition N}

/-- The number of times a value k appears in a skew tableau T.
    This is the exponent of x_k in the monomial x_T. -/
def countValue (T : SkewYoungTableau lam mu) (k : Fin N) : ℕ :=
  (skewYoungDiagram lam mu).filter (fun c => T.entry c = k) |>.card

/-- The monomial x_T equals ∏_{k=1}^N x_k^{(# of times k appears in T)}.
    This is the third equivalent form from Definition \ref{def.sf.ytab.skew-xT}. -/
theorem monomial_eq_prod_pow (T : SkewYoungTableau lam mu) :
    T.monomial = ∏ k : Fin N, (X k : MvPolynomial (Fin N) ℤ) ^ T.countValue k := by
  unfold monomial countValue
  -- Use prod_fiberwise to rewrite the product
  have h1 : ∏ c ∈ skewYoungDiagram lam mu, (X (T.entry c) : MvPolynomial (Fin N) ℤ) =
            ∏ k : Fin N, ∏ c ∈ (skewYoungDiagram lam mu).filter (fun c => T.entry c = k),
                         (X (T.entry c) : MvPolynomial (Fin N) ℤ) := by
    rw [← Finset.prod_fiberwise (skewYoungDiagram lam mu) T.entry
        (fun c => (X (T.entry c) : MvPolynomial (Fin N) ℤ))]
  rw [h1]
  congr 1
  ext k
  have h2 : ∀ c ∈ (skewYoungDiagram lam mu).filter (fun c => T.entry c = k),
            (X (T.entry c) : MvPolynomial (Fin N) ℤ) = X k := by
    intro c hc; simp only [Finset.mem_filter] at hc; rw [hc.2]
  rw [Finset.prod_congr rfl h2, Finset.prod_const]

/-- The sum of countValue over all k equals the cardinality of the skew diagram. -/
theorem sum_countValue_eq_card (T : SkewYoungTableau lam mu) :
    ∑ k : Fin N, T.countValue k = (skewYoungDiagram lam mu).card := by
  unfold countValue
  rw [← Finset.card_biUnion]
  · congr 1
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    constructor
    · intro ⟨k, hk, _⟩; exact hk
    · intro hc; exact ⟨T.entry c, hc, rfl⟩
  · intro k _ k' _ hkk'
    simp only [Finset.disjoint_filter]
    intro c _ hck hck'
    exact hkk' (hck.symm.trans hck')

/-- The monomial of the empty skew diagram is 1. -/
theorem monomial_empty (T : SkewYoungTableau lam mu)
    (h : skewYoungDiagram lam mu = ∅) : T.monomial = 1 := by
  unfold monomial
  rw [h]
  simp

/-- countValue is zero for values that don't appear in the tableau. -/
@[simp]
theorem countValue_zero_of_not_mem (T : SkewYoungTableau lam mu) (k : Fin N)
    (h : ∀ c ∈ skewYoungDiagram lam mu, T.entry c ≠ k) : T.countValue k = 0 := by
  unfold countValue
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc
  exact h c hc

/-- For a semistandard skew tableau, the monomial is the same. -/
def SkewSSYT.monomial' {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (T : SkewSSYT lam mu) : MvPolynomial (Fin N) ℤ :=
  T.toSkewYoungTableau.monomial

end SkewYoungTableau

/-! ## Skew Schur Polynomials -/

/-! ### Finiteness of SkewSSYT

To define the skew Schur polynomial as a sum over all semistandard skew tableaux,
we need to show that the set of such tableaux is finite. The key insight is that:
1. The skew diagram Y(λ/μ) is a finite set
2. Entries are bounded (they live in Fin N)
3. The SSYT conditions are decidable

We represent tableaux as functions from the diagram to Fin N, and filter for those
satisfying the SSYT conditions.
-/

/-- The type of all fillings of a skew diagram with entries in Fin N.
    This is finite since the diagram is finite and Fin N is finite. -/
def SkewFilling {N : ℕ} [NeZero N] (lam mu : NPartition N) : Type :=
  { c // c ∈ skewYoungDiagram lam mu } → Fin N

/-- Fillings are finite. -/
noncomputable instance skewFilling_fintype {N : ℕ} [NeZero N] (lam mu : NPartition N) :
    Fintype (SkewFilling lam mu) :=
  @Fintype.ofFinite _ Pi.finite

/-- The set of fillings that correspond to valid semistandard tableaux.
    We check the conditions on pairs of cells in the diagram:
    - Row-weak: if c1 and c2 are in the same row with c1 to the left, then f(c1) ≤ f(c2)
    - Column-strict: if c1 and c2 are in the same column with c1 above, then f(c1) < f(c2) -/
def isSSYTFilling {N : ℕ} [NeZero N] (lam mu : NPartition N) (f : SkewFilling lam mu) : Prop :=
  -- Row-weak condition: check all pairs in the same row
  (∀ c1 c2 : { c // c ∈ skewYoungDiagram lam mu },
    c1.val.1 = c2.val.1 → c1.val.2 < c2.val.2 → f c1 ≤ f c2) ∧
  -- Column-strict condition: check all pairs in the same column
  (∀ c1 c2 : { c // c ∈ skewYoungDiagram lam mu },
    c1.val.2 = c2.val.2 → c1.val.1 < c2.val.1 → f c1 < f c2)

/-- The SSYT condition is decidable since we're quantifying over finite types. -/
instance isSSYTFilling_decidable {N : ℕ} [NeZero N] (lam mu : NPartition N)
    (f : SkewFilling lam mu) : Decidable (isSSYTFilling lam mu f) := by
  unfold isSSYTFilling
  infer_instance

/-! ### Bridge between SchurBasics and LittlewoodRichardson representations

The two files use different indexing conventions for skew diagrams:
- `SchurBasics.lean`: 0-indexed columns, `mu.parts i ≤ j < lam.parts i`
- `LittlewoodRichardson.lean`: 1-indexed columns, `mu i < j ≤ lam i`

The bijection between cells is: (i, j) ↔ (i, j+1)

We define equivalences to bridge these representations. -/

/-- Cell bijection: SchurBasics cell (i, j) ↔ LittlewoodRichardson cell (i, j+1).
    
    SchurBasics: (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i
    LittlewoodRichardson: (i, j) ∈ Y(λ/μ) iff μ_i < j ≤ λ_i
    
    The map (i, j) ↦ (i, j+1) transforms the first to the second. -/
def skewCellEquiv {N : ℕ} [NeZero N] (lam mu : NPartition N) :
    { c // c ∈ skewYoungDiagram lam mu } ≃
    { c // c ∈ AlgebraicCombinatorics.skewYoungDiagram lam.parts mu.parts } where
  toFun := fun ⟨c, hc⟩ => ⟨(c.1, c.2 + 1), by
    rw [mem_skewYoungDiagram] at hc
    simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · show mu.parts c.1 < c.2 + 1; omega
    · show c.2 + 1 ≤ lam.parts c.1; omega⟩
  invFun := fun ⟨c, hc⟩ => ⟨(c.1, c.2 - 1), by
    simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq] at hc
    rw [mem_skewYoungDiagram]
    refine ⟨?_, ?_⟩
    · show mu.parts c.1 ≤ c.2 - 1; omega
    · show c.2 - 1 < lam.parts c.1; omega⟩
  left_inv := fun ⟨c, hc⟩ => by simp
  right_inv := fun ⟨c, hc⟩ => by
    simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq] at hc
    ext
    · rfl
    · simp; omega

/-- The two `skewYoungDiagram` definitions are isomorphic via the column shift bijection.
    
    This theorem makes explicit that `skewCellEquiv` provides an equivalence between:
    - `skewYoungDiagram lam mu` (SchurBasics): `Finset (Fin N × ℕ)` with 0-indexed columns
      where (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i
    - `AlgebraicCombinatorics.skewYoungDiagram lam.parts mu.parts` (LittlewoodRichardson): 
      `Set (Fin N × ℕ)` with 1-indexed columns where (i, j) ∈ Y(λ/μ) iff μ_i < j ≤ λ_i
    
    The bijection is: (i, j) in SchurBasics ↔ (i, j+1) in LittlewoodRichardson
    
    **Note**: This provides the explicit equivalence theorem
    that was missing from the bridge infrastructure. -/
theorem skewYoungDiagram_equiv_LR {N : ℕ} [NeZero N] (lam mu : NPartition N) :
    Nonempty ({ c // c ∈ skewYoungDiagram lam mu } ≃
              { c // c ∈ AlgebraicCombinatorics.skewYoungDiagram lam.parts mu.parts }) :=
  ⟨skewCellEquiv lam mu⟩

/-- The cardinalities of the two skew Young diagram representations are equal.
    
    This follows directly from `skewCellEquiv` being an equivalence. -/
theorem skewYoungDiagram_card_eq_LR {N : ℕ} [NeZero N] (lam mu : NPartition N) :
    (skewYoungDiagram lam mu).card = 
    Nat.card { c // c ∈ AlgebraicCombinatorics.skewYoungDiagram lam.parts mu.parts } := by
  rw [Nat.card_eq_fintype_card]
  conv_lhs => rw [← Fintype.card_coe (skewYoungDiagram lam mu)]
  exact Fintype.card_congr (skewCellEquiv lam mu)

/-- Membership characterization: (i, j) is in the SchurBasics skew diagram iff (i, j+1) is in
    the LittlewoodRichardson skew diagram.
    
    This is the fundamental relationship between the two indexing conventions. -/
theorem mem_skewYoungDiagram_iff_mem_LR_shifted {N : ℕ} [NeZero N] (lam mu : NPartition N) 
    (i : Fin N) (j : ℕ) :
    (i, j) ∈ skewYoungDiagram lam mu ↔ 
    (i, j + 1) ∈ AlgebraicCombinatorics.skewYoungDiagram lam.parts mu.parts := by
  rw [mem_skewYoungDiagram]
  simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq]
  constructor
  · intro ⟨hlo, hhi⟩
    exact ⟨by omega, by omega⟩
  · intro ⟨hlo, hhi⟩
    exact ⟨by omega, by omega⟩

/-- Filling bijection: convert between SkewFilling and Tableau.
    
    This bridges the two representations by composing with the cell bijection. -/
def skewFillingEquiv {N : ℕ} [NeZero N] (lam mu : NPartition N) :
    SkewFilling lam mu ≃ AlgebraicCombinatorics.Tableau lam.parts mu.parts :=
  Equiv.arrowCongr (skewCellEquiv lam mu) (Equiv.refl _)

/-- The filling bijection preserves the SSYT property. -/
theorem skewFillingEquiv_isSSYT {N : ℕ} [NeZero N] (lam mu : NPartition N)
    (f : SkewFilling lam mu) :
    isSSYTFilling lam mu f ↔ AlgebraicCombinatorics.IsSemistandard (skewFillingEquiv lam mu f) := by
  unfold isSSYTFilling AlgebraicCombinatorics.IsSemistandard skewFillingEquiv Equiv.arrowCongr
  constructor
  · intro ⟨h_row, h_col⟩
    constructor
    · -- Row-weak condition
      intro c1 c2 hrow hcol
      have hc1 := c1.prop
      have hc2 := c2.prop
      simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq] at hc1 hc2
      -- Map back to SchurBasics cells
      let c1' : { c // c ∈ skewYoungDiagram lam mu } := ⟨(c1.val.1, c1.val.2 - 1), by
        rw [mem_skewYoungDiagram]
        refine ⟨?_, ?_⟩ <;> [show mu.parts c1.val.1 ≤ c1.val.2 - 1; show c1.val.2 - 1 < lam.parts c1.val.1] <;> omega⟩
      let c2' : { c // c ∈ skewYoungDiagram lam mu } := ⟨(c2.val.1, c2.val.2 - 1), by
        rw [mem_skewYoungDiagram]
        refine ⟨?_, ?_⟩ <;> [show mu.parts c2.val.1 ≤ c2.val.2 - 1; show c2.val.2 - 1 < lam.parts c2.val.1] <;> omega⟩
      have heq1 : skewCellEquiv lam mu c1' = c1 := by ext <;> simp [skewCellEquiv, c1']; omega
      have heq2 : skewCellEquiv lam mu c2' = c2 := by ext <;> simp [skewCellEquiv, c2']; omega
      rw [← heq1, ← heq2]
      apply h_row c1' c2' hrow
      simp only [c1', c2']; omega
    · -- Column-strict condition
      intro c1 c2 hcol hrow
      have hc1 := c1.prop
      have hc2 := c2.prop
      simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq] at hc1 hc2
      let c1' : { c // c ∈ skewYoungDiagram lam mu } := ⟨(c1.val.1, c1.val.2 - 1), by
        rw [mem_skewYoungDiagram]
        refine ⟨?_, ?_⟩ <;> [show mu.parts c1.val.1 ≤ c1.val.2 - 1; show c1.val.2 - 1 < lam.parts c1.val.1] <;> omega⟩
      let c2' : { c // c ∈ skewYoungDiagram lam mu } := ⟨(c2.val.1, c2.val.2 - 1), by
        rw [mem_skewYoungDiagram]
        refine ⟨?_, ?_⟩ <;> [show mu.parts c2.val.1 ≤ c2.val.2 - 1; show c2.val.2 - 1 < lam.parts c2.val.1] <;> omega⟩
      have heq1 : skewCellEquiv lam mu c1' = c1 := by ext <;> simp [skewCellEquiv, c1']; omega
      have heq2 : skewCellEquiv lam mu c2' = c2 := by ext <;> simp [skewCellEquiv, c2']; omega
      rw [← heq1, ← heq2]
      apply h_col c1' c2'
      · simp only [c1', c2']; omega
      · exact hrow
  · intro ⟨h_row, h_col⟩
    constructor
    · intro c1 c2 hrow hcol
      have h := h_row (skewCellEquiv lam mu c1) (skewCellEquiv lam mu c2)
      simp at h
      apply h hrow
      simp only [skewCellEquiv]
      show c1.val.2 + 1 < c2.val.2 + 1
      omega
    · intro c1 c2 hcol hrow
      have h := h_col (skewCellEquiv lam mu c1) (skewCellEquiv lam mu c2)
      simp at h
      apply h
      · simp only [skewCellEquiv]
        show c1.val.2 + 1 = c2.val.2 + 1
        omega
      · exact hrow

/-- The finite set of all valid SSYT fillings. -/
def ssytFillings {N : ℕ} [NeZero N] (lam mu : NPartition N) : Finset (SkewFilling lam mu) :=
  Finset.univ.filter (isSSYTFilling lam mu)

/-- The monomial associated to a filling.
    x_f = ∏_{c ∈ Y(λ/μ)} x_{f(c)} -/
def fillingMonomial {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (f : SkewFilling lam mu) : MvPolynomial (Fin N) ℤ :=
  ∏ c : { c // c ∈ skewYoungDiagram lam mu }, X (f c)

set_option backward.isDefEq.respectTransparency false in
/-- The content of a filling: the number of cells with each entry value.
    content(f)(i) = |{c ∈ Y(λ/μ) : f(c) = i}|
    
    This is related to the monomial by: x_f = ∏_i x_i^{content(f)(i)}
    
    The Bender-Knuth involution BK_k swaps the content of k and k+1:
    content(BK_k(f))(k) = content(f)(k+1) and content(BK_k(f))(k+1) = content(f)(k) -/
def fillingContent {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (f : SkewFilling lam mu) : Fin N → ℕ :=
  fun i => Finset.univ.filter (fun c : { c // c ∈ skewYoungDiagram lam mu } => f c = i) |>.card

set_option backward.isDefEq.respectTransparency false in
/-- The fillingMonomial equals the product of X i raised to the content power. -/
lemma fillingMonomial_eq_prod_pow {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (f : SkewFilling lam mu) :
    fillingMonomial f = ∏ i : Fin N, (X i : MvPolynomial (Fin N) ℤ) ^ fillingContent f i := by
  unfold fillingMonomial fillingContent
  rw [← Finset.prod_fiberwise Finset.univ f (fun c => X (f c))]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_eq_pow_card]
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rw [hc]

set_option backward.isDefEq.respectTransparency false in
/-- Content bridge: the content of a filling equals the content of the corresponding tableau
    under the skewFillingEquiv bijection.
    
    This is a key lemma for bridging the Bender-Knuth involution from LittlewoodRichardson.lean
    to SchurBasics.lean. It allows us to transport content-related properties across the bijection.
    
    Both definitions count cells with entry i:
    - `fillingContent f i` counts cells c with f(c) = i using Finset.card
    - `contentTableau T i` counts cells c with T(c) = i using Nat.card
    
    The bijection (skewCellEquiv) maps (row, col) ↦ (row, col+1), which doesn't change the entry.
    
    **Proof sketch**: The key is to show that the bijection `skewCellEquiv` induces a bijection
    between `{c | f c = i}` and `{c | (skewFillingEquiv f) c = i}`. Since `skewFillingEquiv`
    is defined as `Equiv.arrowCongr (skewCellEquiv) (Equiv.refl)`, we have
    `(skewFillingEquiv f) c = f ((skewCellEquiv).symm c)`, so the sets are in bijection. -/
theorem skewFillingEquiv_content {N : ℕ} [NeZero N] (lam mu : NPartition N)
    (f : SkewFilling lam mu) (i : Fin N) :
    fillingContent f i = AlgebraicCombinatorics.contentTableau (skewFillingEquiv lam mu f) i := by
  unfold fillingContent AlgebraicCombinatorics.contentTableau
  simp only [skewFillingEquiv]
  -- Define the bijection between the two sets
  let e := skewCellEquiv lam mu
  -- The key is that the subtype {c | f (e.symm c) = i} is in bijection with 
  -- the subtype {c | f c = i} via e
  -- Build the equivalence
  let equiv : { c : { c // c ∈ skewYoungDiagram lam mu } // f c = i } ≃ 
      { c : { c // c ∈ AlgebraicCombinatorics.skewYoungDiagram lam.parts mu.parts } // 
        f (e.symm c) = i } := {
    toFun := fun ⟨c, hc⟩ => ⟨e c, by simp [e, hc]⟩
    invFun := fun ⟨c, hc⟩ => ⟨e.symm c, hc⟩
    left_inv := fun ⟨c, hc⟩ => by simp
    right_inv := fun ⟨c, hc⟩ => by simp
  }
  -- Now relate the cardinalities
  -- First, convert filter.card to Fintype.card of subtype
  have h1 : (Finset.univ.filter (fun c => f c = i)).card = Fintype.card { c : { c // c ∈ skewYoungDiagram lam mu } // f c = i } := by
    rw [Fintype.card_of_subtype (Finset.univ.filter (fun c => f c = i))]
    intro x
    simp
  rw [h1, Nat.card_eq_fintype_card]
  exact Fintype.card_eq.mpr ⟨equiv⟩

/-- The skew Schur polynomial s_{λ/μ} is the sum of monomials x_T over all
    semistandard skew tableaux of shape λ/μ.
    Definition \ref{def.sf.skew-schur} in the source.

    We define this as a sum over the finite set of valid SSYT fillings:
    s_{λ/μ} = ∑_{T ∈ SSYT(λ/μ)} x_T

    The definition proceeds by:
    1. Representing tableaux as functions from the skew diagram to Fin N
    2. Filtering for those satisfying the SSYT conditions (row-weak, column-strict)
    3. Summing the associated monomials

    ## Relationship to Other Definitions

    This project has two skew Schur polynomial definitions with different design tradeoffs:

    | Definition | File | Input | Ring | Use case |
    |------------|------|-------|------|----------|
    | `skewSchurPoly` (this) | SchurBasics.lean | `NPartition N` | `ℤ` | Proofs using skew diagrams, symmetry |
    | `AlgebraicCombinatorics.skewSchurPoly` | LittlewoodRichardson.lean | `Fin N → ℕ` | generic `R` | Littlewood-Richardson rule, generic rings |

    **When to use which:**
    - Use **this definition** when working with skew Young diagrams, SSYT fillings, or proving
      symmetry properties. It requires `[NeZero N]` and uses integer coefficients.
    - Use **`AlgebraicCombinatorics.skewSchurPoly`** when you need a generic coefficient ring
      or when working with the Littlewood-Richardson rule. It takes unbundled `Fin N → ℕ`.

    **Equivalence:** See `SSYTEquiv.lean` for the bridge between these definitions. -/
def skewSchurPoly {N : ℕ} [NeZero N] (lam mu : NPartition N) : MvPolynomial (Fin N) ℤ :=
  ∑ f ∈ ssytFillings lam mu, fillingMonomial f

/-- When mu = 0, the skew Schur polynomial equals the regular Schur polynomial.
    Remark \ref{rmk.sf.skew-0} in the source. -/
theorem skewSchurPoly_zero {N : ℕ} [NeZero N] (lam : NPartition N) :
    skewSchurPoly lam 0 = schurPoly lam := by
  -- Define the equivalence between the diagram subtypes
  have h_diag : skewYoungDiagram lam 0 = lam.youngDiagram := skewYoungDiagram_zero lam
  -- Define a helper equivalence between subtypes when finsets are equal
  let subtypeEquiv : { c // c ∈ skewYoungDiagram lam 0 } ≃ { c // c ∈ lam.youngDiagram } := {
    toFun := fun x => ⟨x.val, h_diag ▸ x.prop⟩
    invFun := fun x => ⟨x.val, h_diag.symm ▸ x.prop⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  -- Define the equivalence between filling types
  let e : SkewFilling lam 0 ≃ Filling lam := Equiv.arrowCongr subtypeEquiv (Equiv.refl _)
  -- Show the equivalence preserves the SSYT property
  have h_ssyt : ∀ f : SkewFilling lam 0, isSSYTFilling lam 0 f ↔ isSSYTFillingYoung lam (e f) := by
    intro f
    unfold isSSYTFilling isSSYTFillingYoung e Equiv.arrowCongr
    constructor
    · intro ⟨h1, h2⟩
      constructor
      · intro c1 c2 hrow hcol
        exact h1 ⟨c1.val, h_diag.symm ▸ c1.prop⟩ ⟨c2.val, h_diag.symm ▸ c2.prop⟩ hrow hcol
      · intro c1 c2 hcol hrow
        exact h2 ⟨c1.val, h_diag.symm ▸ c1.prop⟩ ⟨c2.val, h_diag.symm ▸ c2.prop⟩ hcol hrow
    · intro ⟨h1, h2⟩
      constructor
      · intro c1 c2 hrow hcol
        exact h1 ⟨c1.val, h_diag ▸ c1.prop⟩ ⟨c2.val, h_diag ▸ c2.prop⟩ hrow hcol
      · intro c1 c2 hcol hrow
        exact h2 ⟨c1.val, h_diag ▸ c1.prop⟩ ⟨c2.val, h_diag ▸ c2.prop⟩ hcol hrow
  -- Show the equivalence preserves monomials
  have h_mono : ∀ f : SkewFilling lam 0, fillingMonomial f = fillingMonomialYoung (e f) := by
    intro f
    unfold fillingMonomial fillingMonomialYoung e Equiv.arrowCongr
    apply Finset.prod_equiv subtypeEquiv
    · intro c
      simp only [Finset.mem_univ]
    · intro c _
      rfl
  -- Now use Finset.sum_bij' to prove the equality
  unfold skewSchurPoly schurPoly
  apply Finset.sum_bij' (fun f _ => e f) (fun g _ => e.symm g)
    (fun a ha => ?_)
    (fun a ha => ?_)
    (fun a _ => e.symm_apply_apply a)
    (fun a _ => e.apply_symm_apply a)
    (fun a _ => h_mono a)
  · simp only [ssytFillings, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [ssytFillingsYoung, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (h_ssyt a).mp ha
  · simp only [ssytFillingsYoung, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [ssytFillings, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h_ssyt]
    convert ha using 2; simp

/-- Applying a permutation σ to each entry of a filling. -/
def applyPermToFilling {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (σ : Equiv.Perm (Fin N)) (f : SkewFilling lam mu) : SkewFilling lam mu :=
  fun c => σ (f c)

/-- Renaming variables in a filling monomial equals applying the permutation to entries. -/
lemma rename_fillingMonomial_eq {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (f : SkewFilling lam mu) (σ : Equiv.Perm (Fin N)) :
    MvPolynomial.rename σ (fillingMonomial f) = fillingMonomial (applyPermToFilling σ f) := by
  simp only [fillingMonomial, applyPermToFilling, map_prod, MvPolynomial.rename_X]

/-! ## Bender-Knuth Involutions

The Bender-Knuth involution is a key tool for proving that Schur polynomials are symmetric.
For each k ∈ {0, 1, ..., N-2}, the Bender-Knuth involution BK_k is a bijection on the set
of semistandard Young tableaux that swaps certain entries k and k+1 while preserving
the semistandardness property.

### Key Properties

1. **Involution**: BK_k ∘ BK_k = id
2. **Preserves shape**: BK_k(T) has the same shape as T
3. **Monomial effect**: x_{BK_k(T)} = (swap x_k x_{k+1}) · x_T

### How BK_k Works

For each row i:
- Consider cells containing k or k+1
- Some cells are "forced" (must stay the same due to column constraints)
- The remaining "free" cells can be swapped
- BK_k swaps the free k's and (k+1)'s while maintaining semistandardness

A cell (i, j) with entry k is "forced" if there exists a cell (i', j) with i' > i
in the same column with entry k+1 (column-strict constraint would be violated).
Similarly for entry k+1 being forced by a k above it.

**Note:** The full implementation of the Bender-Knuth involution requires careful handling
of decidability instances. The proofs below are complete and sorry-free.
-/

/-- The simple transposition swapping k and k+1.
    
    This is an alternative signature for `AlgebraicCombinatorics.simpleTransposition`.
    Instead of taking `Fin (N - 1)` (which encodes the constraint), this takes
    `Fin N` with an explicit proof `hk : k.val + 1 < N`.
    
    See `simpleTransposition_eq_canonical` for the equivalence with the canonical definition. -/
def simpleTransposition {N : ℕ} (k : Fin N) (hk : k.val + 1 < N) : Equiv.Perm (Fin N) :=
  Equiv.swap k ⟨k.val + 1, hk⟩

/-- The alternative signature `simpleTransposition` equals the canonical definition.
    
    Given `k : Fin N` with proof `hk : k.val + 1 < N`, we can form `⟨k.val, _⟩ : Fin (N - 1)`
    and the resulting transpositions are equal. -/
theorem simpleTransposition_eq_canonical {N : ℕ} (k : Fin N) (hk : k.val + 1 < N) :
    simpleTransposition k hk = AlgebraicCombinatorics.simpleTransposition ⟨k.val, by omega⟩ := by
  simp only [simpleTransposition, AlgebraicCombinatorics.simpleTransposition]

/-- The Bender-Knuth involution BK_k on skew fillings.
    
    For a filling f and index k, BK_k swaps certain entries k and k+1 while preserving
    the semistandardness property. The construction works row by row:
    - In each row, identify which k's and (k+1)'s are "free" (not forced by column constraints)
    - Use parenthesis-matching: each free (k+1) "matches" with the nearest unmatched free k to its left
    - Only UNMATCHED free entries get swapped
    
    **Implementation**: This bridges to the full implementation in `LittlewoodRichardson.lean`
    via `skewFillingEquiv`. For SSYT fillings, it applies `AlgebraicCombinatorics.benderKnuth`;
    for non-SSYT fillings, it returns the input unchanged (the lemmas only apply to SSYT anyway). -/
def benderKnuthInvol {N : ℕ} [NeZero N] (lam mu : NPartition N) 
    (k : Fin N) (hk : k.val + 1 < N) (f : SkewFilling lam mu) : SkewFilling lam mu := by
  classical
  -- Convert to Tableau representation
  let T := skewFillingEquiv lam mu f
  -- Check if T is semistandard
  by_cases hT : AlgebraicCombinatorics.IsSemistandard T
  · -- Apply the real Bender-Knuth involution and convert back
    exact (skewFillingEquiv lam mu).symm (AlgebraicCombinatorics.benderKnuth k hk T hT)
  · -- For non-SSYT fillings, return unchanged
    exact f

/-- Helper lemma: benderKnuthInvol on SSYT fillings equals the bridged BK. -/
lemma benderKnuthInvol_eq_of_ssyt {N : ℕ} [NeZero N] (lam mu : NPartition N) 
    (k : Fin N) (hk : k.val + 1 < N) (f : SkewFilling lam mu) (hf : isSSYTFilling lam mu f) :
    benderKnuthInvol lam mu k hk f = 
      (skewFillingEquiv lam mu).symm 
        (AlgebraicCombinatorics.benderKnuth k hk (skewFillingEquiv lam mu f) 
          ((skewFillingEquiv_isSSYT lam mu f).mp hf)) := by
  have hT : AlgebraicCombinatorics.IsSemistandard (skewFillingEquiv lam mu f) := 
    (skewFillingEquiv_isSSYT lam mu f).mp hf
  simp only [benderKnuthInvol, hT, dite_true]

/-- The Bender-Knuth involution preserves SSYT membership.
    This is a key property: BK_k maps semistandard tableaux to semistandard tableaux. -/
lemma benderKnuthInvol_mem {N : ℕ} [NeZero N] (lam mu : NPartition N) 
    (k : Fin N) (hk : k.val + 1 < N) (f : SkewFilling lam mu) :
    f ∈ ssytFillings lam mu → benderKnuthInvol lam mu k hk f ∈ ssytFillings lam mu := by
  intro hf
  simp only [ssytFillings, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
  -- Rewrite using the helper lemma
  rw [benderKnuthInvol_eq_of_ssyt lam mu k hk f hf]
  -- Show that BK(T) is semistandard
  have hT : AlgebraicCombinatorics.IsSemistandard (skewFillingEquiv lam mu f) := 
    (skewFillingEquiv_isSSYT lam mu f).mp hf
  have hT' : AlgebraicCombinatorics.IsSemistandard (AlgebraicCombinatorics.benderKnuth k hk _ hT) :=
    AlgebraicCombinatorics.benderKnuth_semistandard (lam.isNPartition) (mu.isNPartition) k hk _ hT
  -- Transfer back through the equivalence
  rw [skewFillingEquiv_isSSYT]
  convert hT' using 1
  simp only [Equiv.apply_symm_apply]

/-- The Bender-Knuth map is an involution: applying it twice returns the original filling. -/
lemma benderKnuthInvol_invol {N : ℕ} [NeZero N] (lam mu : NPartition N) 
    (k : Fin N) (hk : k.val + 1 < N) (f : SkewFilling lam mu) :
    f ∈ ssytFillings lam mu → 
    benderKnuthInvol lam mu k hk (benderKnuthInvol lam mu k hk f) = f := by
  intro hf
  simp only [ssytFillings, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  -- Get the semistandard property for T
  have hT : AlgebraicCombinatorics.IsSemistandard (skewFillingEquiv lam mu f) := 
    (skewFillingEquiv_isSSYT lam mu f).mp hf
  -- Get the involution property from LittlewoodRichardson
  obtain ⟨hT', hInvol⟩ := AlgebraicCombinatorics.benderKnuth_involutive_partition 
    (lam.isNPartition) (mu.isNPartition) k hk _ hT
  -- Use the helper lemma twice
  rw [benderKnuthInvol_eq_of_ssyt lam mu k hk f hf]
  -- The intermediate filling is also SSYT
  have hf' : isSSYTFilling lam mu ((skewFillingEquiv lam mu).symm (AlgebraicCombinatorics.benderKnuth k hk _ hT)) := by
    rw [skewFillingEquiv_isSSYT]
    convert hT' using 2
    exact Equiv.apply_symm_apply _ _
  rw [benderKnuthInvol_eq_of_ssyt lam mu k hk _ hf']
  -- Now the goal involves two BK applications
  -- Key fact: skewFillingEquiv (symm x) = x
  have h1 : skewFillingEquiv lam mu ((skewFillingEquiv lam mu).symm (AlgebraicCombinatorics.benderKnuth k hk (skewFillingEquiv lam mu f) hT)) = 
      AlgebraicCombinatorics.benderKnuth k hk (skewFillingEquiv lam mu f) hT := Equiv.apply_symm_apply _ _
  -- The goal is: symm (BK T1 proof1) = f where T1 = skewFillingEquiv (symm (BK T))
  -- We know T1 = BK T by h1
  -- And BK (BK T) = T by hInvol
  -- So symm (BK (BK T)) = symm T = f
  -- The proof terms are different but the tableaux are equal, so we use congrArg
  suffices h : AlgebraicCombinatorics.benderKnuth k hk 
        (skewFillingEquiv lam mu ((skewFillingEquiv lam mu).symm (AlgebraicCombinatorics.benderKnuth k hk (skewFillingEquiv lam mu f) hT)))
        ((skewFillingEquiv_isSSYT lam mu _).mp hf') = 
      skewFillingEquiv lam mu f by
    rw [h]
    exact Equiv.symm_apply_apply _ _
  -- Now prove h using h1 and hInvol
  have h2 : AlgebraicCombinatorics.benderKnuth k hk 
        (skewFillingEquiv lam mu ((skewFillingEquiv lam mu).symm (AlgebraicCombinatorics.benderKnuth k hk (skewFillingEquiv lam mu f) hT)))
        ((skewFillingEquiv_isSSYT lam mu _).mp hf') 
      = AlgebraicCombinatorics.benderKnuth k hk (AlgebraicCombinatorics.benderKnuth k hk (skewFillingEquiv lam mu f) hT) hT' := by
    congr 1
  rw [h2, hInvol]

/-- The key property that the Bender-Knuth involution satisfies:
    BK_k swaps the content of k and k+1, leaving other entries unchanged.
    
    This is the content-level statement that implies `benderKnuthInvol_mono`:
    If content(BK_k(f))(k) = content(f)(k+1) and content(BK_k(f))(k+1) = content(f)(k),
    then fillingMonomial(BK_k(f)) = rename(swap k (k+1))(fillingMonomial(f)).
    
    The proof transfers `benderKnuth_content_swap` from LittlewoodRichardson.lean
    through the `skewFillingEquiv` bijection, using `skewFillingEquiv_content` to
    relate `fillingContent` and `contentTableau`. -/
lemma benderKnuthInvol_content_swap_spec {N : ℕ} [NeZero N] (lam mu : NPartition N) 
    (k : Fin N) (hk : k.val + 1 < N) (f : SkewFilling lam mu) :
    f ∈ ssytFillings lam mu →
    let f' := benderKnuthInvol lam mu k hk f
    fillingContent f' k = fillingContent f ⟨k.val + 1, hk⟩ ∧
    fillingContent f' ⟨k.val + 1, hk⟩ = fillingContent f k ∧
    (∀ i : Fin N, i ≠ k → i ≠ ⟨k.val + 1, hk⟩ → fillingContent f' i = fillingContent f i) := by
  intro hf
  simp only [ssytFillings, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  -- Rewrite using the helper lemma
  rw [benderKnuthInvol_eq_of_ssyt lam mu k hk f hf]
  -- Get the semistandard property for T
  have hT : AlgebraicCombinatorics.IsSemistandard (skewFillingEquiv lam mu f) := 
    (skewFillingEquiv_isSSYT lam mu f).mp hf
  -- Get the content swap property from LittlewoodRichardson
  obtain ⟨h1, h2, h3⟩ := AlgebraicCombinatorics.benderKnuth_content_swap k hk _ hT
  -- Transfer through the equivalence using skewFillingEquiv_content
  refine ⟨?_, ?_, ?_⟩
  · -- fillingContent f' k = fillingContent f ⟨k.val + 1, hk⟩
    rw [skewFillingEquiv_content, skewFillingEquiv_content]
    convert h1 using 1
    simp only [Equiv.apply_symm_apply]
  · -- fillingContent f' ⟨k.val + 1, hk⟩ = fillingContent f k
    rw [skewFillingEquiv_content, skewFillingEquiv_content]
    convert h2 using 1
    simp only [Equiv.apply_symm_apply]
  · -- For other i, fillingContent f' i = fillingContent f i
    intro i hi_ne_k hi_ne_ksucc
    rw [skewFillingEquiv_content, skewFillingEquiv_content]
    have h3' := h3 i hi_ne_k (by simp only [Fin.ext_iff, ne_eq] at hi_ne_ksucc ⊢; exact hi_ne_ksucc)
    convert h3' using 1
    simp only [Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The monomial effect of the Bender-Knuth involution:
    x_{BK_k(f)} = (swap x_k x_{k+1}) · x_f
    
    This says that BK_k effectively swaps the roles of variables x_k and x_{k+1}
    in the monomial, which is the key property for proving symmetry.
    
    The proof uses `benderKnuthInvol_content_swap_spec`: if the content swaps k and k+1,
    then the monomial (which is ∏ i, X i ^ content(f)(i)) is renamed by swap k (k+1). -/
lemma benderKnuthInvol_mono {N : ℕ} [NeZero N] (lam mu : NPartition N) 
    (k : Fin N) (hk : k.val + 1 < N) (f : SkewFilling lam mu) :
    f ∈ ssytFillings lam mu → 
    fillingMonomial (benderKnuthInvol lam mu k hk f) = 
      MvPolynomial.rename (simpleTransposition k hk) (fillingMonomial f) := by
  intro hssyt
  -- Get the content swap property from benderKnuthInvol_content_swap_spec
  obtain ⟨h_swap_k, h_swap_k1, h_other⟩ := benderKnuthInvol_content_swap_spec lam mu k hk f hssyt
  -- Express both sides in terms of content using fillingMonomial_eq_prod_pow
  rw [fillingMonomial_eq_prod_pow f, fillingMonomial_eq_prod_pow (benderKnuthInvol lam mu k hk f)]
  -- Apply the key transformation: if content swaps k↔k+1, then monomial is renamed
  simp only [simpleTransposition, map_prod, map_pow, MvPolynomial.rename_X]
  -- Reindex the RHS product using the swap permutation
  let σ := Equiv.swap k ⟨k.val + 1, hk⟩
  conv_rhs => 
    rw [← Equiv.prod_comp σ]
  -- Simplify σ(σ(i)) = i using swap_apply_self
  have hσσ : ∀ i, σ (σ i) = i := fun i => Equiv.swap_apply_self k ⟨k.val + 1, hk⟩ i
  conv_rhs =>
    arg 2
    ext i
    arg 1
    arg 1
    rw [hσσ]
  -- Now both sides are ∏ i, X i ^ (content i), show the contents match
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  -- Case split on whether i = k, i = k+1, or neither
  by_cases hik : i = k
  · -- i = k: content f' k = content f (k+1)
    rw [hik, h_swap_k, Equiv.swap_apply_left]
  · by_cases hik1 : i = ⟨k.val + 1, hk⟩
    · -- i = k+1: content f' (k+1) = content f k
      rw [hik1, h_swap_k1, Equiv.swap_apply_right]
    · -- i ≠ k and i ≠ k+1: content f' i = content f i
      rw [h_other i hik hik1, Equiv.swap_apply_of_ne_of_ne hik hik1]

/-- Helper lemma: swap i j = swap k j * swap i k * swap k j when i < k < j.
    This decomposition is used to reduce arbitrary swaps to adjacent swaps. -/
private lemma swap_decompose {N : ℕ} {i j k : Fin N} (hik : i < k) (hkj : k < j) :
    Equiv.swap i j = Equiv.swap k j * Equiv.swap i k * Equiv.swap k j := by
  ext x
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  have hine_k : i ≠ k := hik.ne
  have hkne_j : k ≠ j := hkj.ne
  have hine_j : i ≠ j := (hik.trans hkj).ne
  by_cases hxi : x = i
  · subst hxi
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hine_k hine_j,
        Equiv.swap_apply_left, Equiv.swap_apply_left]
  · by_cases hxj : x = j
    · subst hxj
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right, Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hine_k hine_j]
    · by_cases hxk : x = k
      · subst hxk
        rw [Equiv.swap_apply_of_ne_of_ne hine_k.symm hkne_j, Equiv.swap_apply_left,
            Equiv.swap_apply_of_ne_of_ne hine_j.symm hkne_j.symm, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hxi hxj, Equiv.swap_apply_of_ne_of_ne hxk hxj,
            Equiv.swap_apply_of_ne_of_ne hxi hxk, Equiv.swap_apply_of_ne_of_ne hxk hxj]

/-- Helper lemma: Any swap leaves a polynomial invariant if all adjacent swaps do.
    This reduces the symmetry proof to showing invariance under adjacent transpositions. -/
lemma swap_invariant_of_adj_invariant {N : ℕ} (P : MvPolynomial (Fin N) ℤ)
    (h_adj : ∀ (k : Fin N) (hk : k.val + 1 < N),
        MvPolynomial.rename (simpleTransposition k hk) P = P)
    (i j : Fin N) (hij : i ≠ j) :
    MvPolynomial.rename (Equiv.swap i j) P = P := by
  -- wlog: assume i < j
  wlog h : i < j generalizing i j with H
  · have hle : j ≤ i := Nat.le_of_not_lt h
    have : j < i := lt_of_le_of_ne hle hij.symm
    rw [Equiv.swap_comm]
    exact H j i hij.symm this
  -- Now i < j. Prove by strong induction on j.val - i.val
  have hdiff : j.val - i.val ≥ 1 := by
    have := Fin.lt_def.mp h
    omega
  generalize hd : j.val - i.val = d at hdiff
  induction d using Nat.strong_induction_on generalizing i j with
  | _ d ih =>
    rcases Nat.eq_or_lt_of_le hdiff with heq | hgt
    · -- d = 1, so j = i + 1, adjacent swap
      have hival : j.val = i.val + 1 := by omega
      have hk : i.val + 1 < N := by
        have hj := j.isLt
        omega
      have hj' : j = ⟨i.val + 1, hk⟩ := by
        apply Fin.ext
        omega
      rw [hj']
      have heq' : Equiv.swap i ⟨i.val + 1, hk⟩ = simpleTransposition i hk := rfl
      rw [heq']
      exact h_adj i hk
    · -- d > 1. Use decomposition: swap i j = swap k j * swap i k * swap k j where k = j - 1
      have hklt : j.val - 1 < N := by omega
      let k : Fin N := ⟨j.val - 1, hklt⟩
      have hik : i < k := by simp only [k, Fin.lt_def]; omega
      have hkj : k < j := by simp only [k, Fin.lt_def]; omega
      -- Apply the decomposition
      rw [swap_decompose hik hkj]
      simp only [Equiv.Perm.coe_mul]
      -- swap k j is adjacent (k = j - 1)
      have hklt' : k.val + 1 < N := by
        simp only [k]
        have := j.isLt
        omega
      have hswap_kj : MvPolynomial.rename (Equiv.swap k j) P = P := by
        have hj'' : j = ⟨k.val + 1, hklt'⟩ := by
          apply Fin.ext
          simp only [k]
          omega
        rw [hj'']
        have heq' : Equiv.swap k ⟨k.val + 1, hklt'⟩ = simpleTransposition k hklt' := rfl
        rw [heq']
        exact h_adj k hklt'
      -- swap i k has smaller difference, apply induction
      have hdiff' : k.val - i.val < d := by simp only [k]; omega
      have hswap_ik : MvPolynomial.rename (Equiv.swap i k) P = P := by
        apply ih (k.val - i.val) hdiff' i k hik.ne hik rfl
        simp only [k]
        omega
      rw [← MvPolynomial.rename_rename, ← MvPolynomial.rename_rename]
      rw [hswap_kj, hswap_ik, hswap_kj]

/-- The skew Schur polynomial is invariant under simple transpositions.
    This is the key lemma that uses Bender-Knuth involutions.
    
    The proof strategy is:
    1. Define the Bender-Knuth involution BK_k on ssytFillings
    2. Show BK_k is a bijection that preserves the SSYT property
    3. Show fillingMonomial (BK_k f) = rename (swap k (k+1)) (fillingMonomial f)
    4. Use the bijection to reindex the sum -/
theorem skewSchurPoly_swap_invariant {N : ℕ} [NeZero N] (lam mu : NPartition N)
    (k : Fin N) (hk : k.val + 1 < N) :
    MvPolynomial.rename (simpleTransposition k hk) (skewSchurPoly lam mu) = skewSchurPoly lam mu := by
  -- The Bender-Knuth involution BK_k provides a bijection on ssytFillings
  -- such that fillingMonomial (BK_k f) = rename (swap k (k+1)) (fillingMonomial f)
  -- Since BK_k is an involution (BK_k ∘ BK_k = id), the sums are equal.
  unfold skewSchurPoly
  rw [map_sum]
  -- Use benderKnuthInvol_mono to rewrite each term
  have h1 : ∀ f ∈ ssytFillings lam mu, 
      MvPolynomial.rename (simpleTransposition k hk) (fillingMonomial f) = 
        fillingMonomial (benderKnuthInvol lam mu k hk f) := 
    fun f hf => (benderKnuthInvol_mono lam mu k hk f hf).symm
  simp_rw [Finset.sum_congr rfl h1]
  -- Use involution to reindex the sum
  apply Finset.sum_nbij' (benderKnuthInvol lam mu k hk) (benderKnuthInvol lam mu k hk) 
    (benderKnuthInvol_mem lam mu k hk) (benderKnuthInvol_mem lam mu k hk)
    (benderKnuthInvol_invol lam mu k hk) (benderKnuthInvol_invol lam mu k hk)
  intro f hf
  rfl

/-- Skew Schur polynomials are symmetric.
    Theorem \ref{thm.sf.skew-schur-symm} in the source.

    **Proof Strategy (Bender-Knuth involutions):**
    The proof uses the Bender-Knuth involutions, which are combinatorial bijections
    on semistandard skew tableaux. For each k ∈ [N-1], the k-th Bender-Knuth involution
    BK_k swaps certain entries k and k+1 in a tableau T while preserving the
    semistandardness condition. The key properties are:
    1. BK_k is an involution: BK_k(BK_k(T)) = T
    2. BK_k preserves the shape of the tableau
    3. x_{BK_k(T)} = s_k · x_T (where s_k swaps x_k and x_{k+1})

    Since the simple transpositions s_1, ..., s_{N-1} generate S_N, and each BK_k
    establishes that s_k · s_{λ/μ} = s_{λ/μ}, we conclude that s_{λ/μ} is symmetric. -/
theorem skewSchurPoly_isSymmetric {N : ℕ} [NeZero N] (lam mu : NPartition N) :
    ∀ σ : Equiv.Perm (Fin N), MvPolynomial.rename σ (skewSchurPoly lam mu) = skewSchurPoly lam mu := by
  intro σ
  -- Use induction on the structure of σ as a product of swaps
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap f i j hij ih =>
    -- f * swap i j as a function is f ∘ swap i j
    simp only [Equiv.Perm.coe_mul]
    rw [← MvPolynomial.rename_rename]
    -- Apply swap_invariant_of_adj_invariant for swap i j
    have h_swap : MvPolynomial.rename (Equiv.swap i j) (skewSchurPoly lam mu) =
        skewSchurPoly lam mu :=
      swap_invariant_of_adj_invariant (skewSchurPoly lam mu)
        (fun k hk => skewSchurPoly_swap_invariant lam mu k hk) i j hij
    rw [h_swap, ih]

/-! ## Schur Polynomials are Symmetric -/

/-- Schur polynomials are symmetric.
    Theorem \ref{thm.sf.schur-symm}(a) in the source.

    This follows from `skewSchurPoly_isSymmetric` using the fact that
    `schurPoly lam = skewSchurPoly lam 0` (see `skewSchurPoly_zero`). -/
theorem schurPoly_isSymmetric {N : ℕ} [NeZero N] (lam : NPartition N) :
    ∀ σ : Equiv.Perm (Fin N), MvPolynomial.rename σ (schurPoly lam) = schurPoly lam := by
  intro σ
  rw [← skewSchurPoly_zero lam]
  exact skewSchurPoly_isSymmetric lam 0 σ

/-- The determinant-based alternant (from SchurBasics) equals the sum-based alternant
    (from LittlewoodRichardson).

    Since `alternant` is now an abbreviation for `AlgebraicCombinatorics.alternant`,
    this theorem is trivially true by reflexivity.

    Both compute the same polynomial; the determinant expands to the signed sum over permutations.
    See also `AlgebraicCombinatorics.alternant_eq_det` for the determinant form. -/
theorem alternant_eq_AC_alternant {N : ℕ} {R : Type*} [CommRing R] (α : Fin N → ℕ) :
    alternant (R := R) N α = AlgebraicCombinatorics.alternant (R := R) α := rfl

/-- The Schur polynomial defined in SchurBasics equals the one in LittlewoodRichardson.

    Both definitions compute the same polynomial:
    - SchurBasics: `∑ f ∈ ssytFillingsYoung lam, fillingMonomialYoung f`
    - LittlewoodRichardson: `∑ T : {T : Tableau lam.parts 0 // IsSemistandard T}, xPow (contentTableau T.val)`

    Both sum over semistandard Young tableaux of shape λ, but use different representations:
    - SchurBasics uses 0-indexed columns: cell (i,j) with 0 ≤ j < λ_i
    - LittlewoodRichardson uses 1-indexed columns: cell (i,j) with 0 < j ≤ λ_i

    The bijection between these representations preserves the monomial, so the sums are equal.

    **Note**: Currently proved only for `ℤ` coefficients.

    See also:
    - `SSYTEquiv.schur_eq_schurPoly_int`: equivalence with `SymmetricFunctions.schur`
    - `alternant_eq_AC_alternant`: corresponding equivalence for alternants -/
theorem schurPoly_eq_AC_schurPoly {N : ℕ} [NeZero N] (lam : NPartition N) :
    schurPoly lam = AlgebraicCombinatorics.schurPoly (R := ℤ) lam.parts := by
  -- Both definitions sum over SSYT of shape λ with the same monomials.
  -- SchurBasics uses 0-indexed columns: cell (i,j) with 0 ≤ j < λ_i
  -- LittlewoodRichardson uses 1-indexed columns: cell (i,j) with 0 < j ≤ λ_i
  -- The bijection (i, j) ↔ (i, j+1) preserves SSYT conditions and monomials.
  
  -- Step 1: Define the cell bijection (i, j) ↔ (i, j+1)
  let cellEquiv : { c // c ∈ lam.youngDiagram } ≃ 
      { c // c ∈ AlgebraicCombinatorics.skewYoungDiagram lam.parts 0 } := {
    toFun := fun ⟨c, hc⟩ => ⟨(c.1, c.2 + 1), by
      rw [NPartition.mem_youngDiagram] at hc
      simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq, Pi.zero_apply]
      exact ⟨Nat.zero_lt_succ c.2, hc⟩⟩
    invFun := fun ⟨c, hc⟩ => ⟨(c.1, c.2 - 1), by
      simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq, Pi.zero_apply] at hc
      rw [NPartition.mem_youngDiagram]
      simp
      omega⟩
    left_inv := fun ⟨c, hc⟩ => by simp
    right_inv := fun ⟨c, hc⟩ => by
      simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq, Pi.zero_apply] at hc
      ext
      · rfl
      · simp; omega
  }
  
  -- Step 2: Define the filling/tableau bijection
  let e : Filling lam ≃ AlgebraicCombinatorics.Tableau lam.parts 0 := 
    Equiv.arrowCongr cellEquiv (Equiv.refl _)
  
  -- Step 3: Show the bijection preserves SSYT conditions
  -- The SSYT conditions (row-weak, column-strict) depend only on relative ordering
  -- which is preserved by the column shift +1
  have h_ssyt : ∀ f : Filling lam, isSSYTFillingYoung lam f ↔ 
      AlgebraicCombinatorics.IsSemistandard (e f) := fun f => by
    unfold isSSYTFillingYoung AlgebraicCombinatorics.IsSemistandard e Equiv.arrowCongr
    -- Both conditions are preserved: row-weak and column-strict depend only on
    -- relative ordering of column indices within a row (or row indices within a column),
    -- and the +1 shift preserves this ordering.
    constructor
    · intro ⟨h_row, h_col⟩
      refine ⟨?_, ?_⟩
      · -- Row condition
        intro c1 c2 hrow hcol
        have hc1 := c1.prop
        have hc2 := c2.prop
        simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq, Pi.zero_apply] at hc1 hc2
        have h1 : c1.val.2 - 1 < lam.parts c1.val.1 := by omega
        have h2 : c2.val.2 - 1 < lam.parts c2.val.1 := by omega
        let c1' : { c // c ∈ lam.youngDiagram } := ⟨(c1.val.1, c1.val.2 - 1), by
          rw [NPartition.mem_youngDiagram]; exact h1⟩
        let c2' : { c // c ∈ lam.youngDiagram } := ⟨(c2.val.1, c2.val.2 - 1), by
          rw [NPartition.mem_youngDiagram]; exact h2⟩
        have heq1 : cellEquiv c1' = c1 := by ext <;> simp [cellEquiv, c1']; omega
        have heq2 : cellEquiv c2' = c2 := by ext <;> simp [cellEquiv, c2']; omega
        rw [← heq1, ← heq2]
        apply h_row c1' c2' hrow
        simp only [c1', c2']; omega
      · -- Column condition
        intro c1 c2 hcol hrow
        have hc1 := c1.prop
        have hc2 := c2.prop
        simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq, Pi.zero_apply] at hc1 hc2
        have h1 : c1.val.2 - 1 < lam.parts c1.val.1 := by omega
        have h2 : c2.val.2 - 1 < lam.parts c2.val.1 := by omega
        let c1' : { c // c ∈ lam.youngDiagram } := ⟨(c1.val.1, c1.val.2 - 1), by
          rw [NPartition.mem_youngDiagram]; exact h1⟩
        let c2' : { c // c ∈ lam.youngDiagram } := ⟨(c2.val.1, c2.val.2 - 1), by
          rw [NPartition.mem_youngDiagram]; exact h2⟩
        have heq1 : cellEquiv c1' = c1 := by ext <;> simp [cellEquiv, c1']; omega
        have heq2 : cellEquiv c2' = c2 := by ext <;> simp [cellEquiv, c2']; omega
        rw [← heq1, ← heq2]
        apply h_col c1' c2'
        · simp only [c1', c2']; omega
        · exact hrow
    · intro ⟨h_row, h_col⟩
      refine ⟨?_, ?_⟩
      · intro c1 c2 hrow hcol
        have h := h_row (cellEquiv c1) (cellEquiv c2)
        simp at h
        apply h hrow
        -- Need to show (cellEquiv c1).val.2 < (cellEquiv c2).val.2
        -- cellEquiv maps (i, j) to (i, j+1), so this follows from hcol
        show (c1.val.1, c1.val.2 + 1).2 < (c2.val.1, c2.val.2 + 1).2
        omega
      · intro c1 c2 hcol hrow
        have h := h_col (cellEquiv c1) (cellEquiv c2)
        simp at h
        apply h
        · show (c1.val.1, c1.val.2 + 1).2 = (c2.val.1, c2.val.2 + 1).2
          omega
        · exact hrow
  
  -- Step 4: Show monomials are equal
  have h_mono : ∀ f : Filling lam, 
      fillingMonomialYoung f = AlgebraicCombinatorics.xPow (AlgebraicCombinatorics.contentTableau (e f)) := by
    intro f
    unfold fillingMonomialYoung
    simp only [AlgebraicCombinatorics.xPow_eq_monomialExp, AlgebraicCombinatorics.SymmetricFunctions.monomialExp]
    conv_rhs => 
      arg 2
      ext i
      rw [AlgebraicCombinatorics.contentTableau_eq_card]
    have h_fiber := Finset.prod_fiberwise' (Finset.univ : Finset { c // c ∈ AlgebraicCombinatorics.skewYoungDiagram lam.parts 0 }) 
      (e f) (fun i => (X i : MvPolynomial (Fin N) ℤ))
    simp only [Finset.prod_const] at h_fiber
    rw [h_fiber]
    apply Finset.prod_equiv cellEquiv
    · intro c
      simp only [Finset.mem_univ]
    · intro c _
      rfl
  
  -- Step 5: Conclude using the sum equivalence
  unfold schurPoly ssytFillingsYoung AlgebraicCombinatorics.schurPoly AlgebraicCombinatorics.skewSchurPoly
  let ssytEquiv : { f : Filling lam // isSSYTFillingYoung lam f } ≃ 
      { T : AlgebraicCombinatorics.Tableau lam.parts 0 // AlgebraicCombinatorics.IsSemistandard T } :=
    Equiv.subtypeEquiv e (fun f => h_ssyt f)
  -- Convert the Finset sum to a sum over the subtype
  rw [Finset.sum_subtype]
  · apply Fintype.sum_equiv ssytEquiv
    intro ⟨f, hf⟩
    simp only [ssytEquiv, Equiv.subtypeEquiv_apply]
    exact h_mono f
  · intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The alternant identity: a_{lam+ρ} = a_ρ · s_lam.
    Theorem \ref{thm.sf.schur-symm}(b) in the source.

    **Proof Strategy (from the tex source, using Stembridge's Lemma):**

    1. Apply Stembridge's Lemma (lem.sf.stemb-lem) with μ = 0 and ν = 0:
       a_{0+ρ} · s_{λ/0} = ∑_{T 0-Yamanouchi of shape λ/0} a_{0 + cont(T) + ρ}

    2. Simplify using 0 + ρ = ρ and s_{λ/0} = s_λ:
       a_ρ · s_λ = ∑_{T 0-Yamanouchi of shape λ} a_{cont(T) + ρ}

    3. Show that the only 0-Yamanouchi semistandard tableau of shape λ is the
       "minimalistic" (highest weight) tableau T₀ where each row i contains only i's.
       This is `SSYT.highestWeight` in our formalization.

    4. The content of T₀ equals λ: cont(T₀) = λ
       (since row i has λᵢ cells, all filled with value i, so the count of i's is λᵢ)

    5. Therefore: a_ρ · s_λ = a_{λ + ρ}

    **Proof:** We use `schurPoly_eq_alternant_div` from LittlewoodRichardson.lean and
    bridge the type systems. -/
theorem alternant_eq_rho_mul_schur {N : ℕ} [NeZero N] (lam : NPartition N) :
    alternant (R := ℤ) N (fun i => lam.parts i + rhoVector N i) =
      alternant N (rhoVector N) * schurPoly lam := by
  -- First, show that lam.parts satisfies IsNPartition
  have hlam : AlgebraicCombinatorics.IsNPartition lam.parts := lam.monotone
  -- Apply the theorem from LittlewoodRichardson
  have h := AlgebraicCombinatorics.schurPoly_eq_alternant_div (R := ℤ) lam.parts hlam
  -- h : AC.alternant (lam.parts + rho N) = AC.alternant (rho N) * AC.schurPoly lam.parts
  -- Note: rhoVector N = rho N definitionally
  have hrho : rhoVector N = AlgebraicCombinatorics.rho N := rfl
  -- Note: (fun i => lam.parts i + rhoVector N i) = lam.parts + rho N
  have harg : (fun i => lam.parts i + rhoVector N i) = lam.parts + AlgebraicCombinatorics.rho N := rfl
  -- Rewrite using alternant equality
  simp only [alternant_eq_AC_alternant, harg, hrho]
  -- Goal: AC.alternant (lam.parts + rho N) = AC.alternant (rho N) * schurPoly lam
  -- Use schurPoly equality first
  rw [schurPoly_eq_AC_schurPoly]
  -- Goal: AC.alternant (lam.parts + rho N) = AC.alternant (rho N) * AC.schurPoly lam.parts
  exact h

/-! ## Properties of Alternants -/

omit [NeZero N] in
/-- An alternant is zero if two entries of α are equal.
    Lemma \ref{lem.sf.alternant-0}(a) in the source.

    This delegates to `AlgebraicCombinatorics.alternant_eq_zero_of_repeated`. -/
theorem alternant_zero_of_eq {R : Type*} [CommRing R] {α : Fin N → ℕ}
    (i j : Fin N) (hij : i ≠ j) (heq : α i = α j) :
    alternant (R := R) N α = 0 :=
  AlgebraicCombinatorics.alternant_eq_zero_of_repeated ⟨i, j, hij, heq⟩

omit [NeZero N] in
/-- Swapping columns of an alternant multiplies it by -1.
    Lemma \ref{lem.sf.alternant-0}(b) in the source.

    This delegates to `AlgebraicCombinatorics.alternant_swap`. -/
theorem alternant_swap {R : Type*} [CommRing R] {α : Fin N → ℕ}
    (i j : Fin N) (hij : i ≠ j) :
    alternant (R := R) N (α ∘ Equiv.swap i j) = -alternant N α :=
  AlgebraicCombinatorics.alternant_swap hij

end
