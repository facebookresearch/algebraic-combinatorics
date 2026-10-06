/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.Determinants.PermFinset

/-!
# Determinants: Cauchy-Binet and Related Formulas

This file formalizes the Cauchy-Binet formula and related determinant identities,
following Section "Cauchy--Binet ... Factoring the matrix" of the source
(CauchyBinet.tex).

## Main definitions

* `Matrix.submatrix` - The submatrix obtained by restricting to specific rows and columns.
  This corresponds to `sub_U^V A` in the source (Definition def.det.sub).
* `colsSubmatrix`, `rowsSubmatrix` - Submatrices selecting specific columns/rows.

## Main results

* `cauchyBinet` - The general Cauchy-Binet formula for det(AB) where A is n×m and B is m×n
  (Theorem thm.det.CB)
* `cauchyBinet_square` - Special case for square matrices: det(AB) = det(A)·det(B)
* `det_mul_eq_zero_of_rank_deficient` - When m < n, det(AB) = 0
* `det_add_sum` - Formula for det(A+B) as a double sum over subsets (Theorem thm.det.det(A+B))
* `det_diagonal_submatrix_eq`, `det_diagonal_submatrix_off_diag` - Minors of diagonal matrices
  (Lemma lem.det.minors-diag)
* `det_add_diagonal` - Simplified formula when adding a diagonal matrix (Theorem thm.det.det(A+D))
* `det_const_add_diagonal` - Determinant of x + D where D is diagonal (Proposition prop.det.x+ai)
* `det_charPoly_coeff` - Coefficients of the characteristic polynomial
  (Proposition prop.det.charpol-explicit)
* `det_pascal_matrix` - The Pascal matrix has determinant 1 (Proposition prop.det.pascal-LU)

## References

* Source: CauchyBinet.tex

## Implementation notes

Mathlib already provides `Matrix.det_mul` in `Mathlib.LinearAlgebra.Matrix.Determinant`.
We provide additional results and connect Mathlib's API to the textbook presentation.

The submatrix operation `Matrix.submatrix` uses functions for row/column selection,
which is more general than the textbook's subset-based notation.
-/

open scoped Matrix BigOperators
open Finset Matrix

namespace AlgebraicCombinatorics

namespace CauchyBinet

variable {R : Type*} [CommRing R]

/-!
## Submatrices (Definition def.det.sub)

For an n×m matrix A, subsets U ⊆ [n] and V ⊆ [m], we define
sub_U^V A to be the |U|×|V| submatrix obtained by keeping only
the rows indexed by U and columns indexed by V (in increasing order).

In Mathlib, this is `Matrix.submatrix A f g` where f and g are the
order-preserving embeddings of U and V into [n] and [m].
-/

/-- The submatrix of A obtained by restricting to rows in U and columns in V.
    This corresponds to `sub_U^V A` in the source (Definition def.det.sub).
    Label: def.det.sub
    
    ## Mathematical Description
    
    Let A be an n×m matrix. Let U ⊆ [n] and V ⊆ [m] be subsets.
    Writing U = {u₁, u₂, ..., uₚ} with u₁ < u₂ < ... < uₚ
    and V = {v₁, v₂, ..., vₚ} with v₁ < v₂ < ... < vₚ,
    we define sub_U^V A := (A_{uᵢ,vⱼ})_{1≤i≤p, 1≤j≤q}.
    
    This is the |U|×|V| matrix obtained from A by keeping only the rows
    indexed by U and columns indexed by V, in increasing order.
    
    ## Terminology
    
    - **Submatrix**: The matrix sub_U^V A
    - **Minor**: When |U| = |V|, the determinant det(sub_U^V A) is called a minor of A
    - **Principal minor**: When U = V, the minor det(sub_U^U A) is called a principal minor
    
    ## Implementation
    
    In Mathlib, `Matrix.submatrix` takes functions for row and column selection.
    For finite sets, we use the canonical order-preserving embedding `orderEmbOfFin`. -/
noncomputable def submatrixOfFinset {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) :
    Matrix (Fin U.card) (Fin V.card) R :=
  A.submatrix (U.orderEmbOfFin rfl) (V.orderEmbOfFin rfl)

/-- Notation for submatrices: `sub[U,V] A` denotes sub_U^V A. -/
scoped notation "sub[" U "," V "] " A => submatrixOfFinset A U V

/-- The (i, j) entry of sub_U^V A is A_{uᵢ, vⱼ} where uᵢ is the i-th smallest element of U
    and vⱼ is the j-th smallest element of V. -/
@[simp]
theorem submatrixOfFinset_apply {n m : ℕ} {R : Type*} (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) (i : Fin U.card) (j : Fin V.card) :
    submatrixOfFinset A U V i j = A (U.orderEmbOfFin rfl i) (V.orderEmbOfFin rfl j) := rfl

/-- The submatrix of the empty row set is a 0×|V| matrix. -/
theorem submatrixOfFinset_empty_rows {n m : ℕ} {R : Type*} (A : Matrix (Fin n) (Fin m) R)
    (V : Finset (Fin m)) :
    submatrixOfFinset A ∅ V = ![] := by
  ext i _
  exact i.elim0

/-- The submatrix of the empty column set is a |U|×0 matrix. -/
theorem submatrixOfFinset_empty_cols {n m : ℕ} {R : Type*} (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) :
    submatrixOfFinset A U ∅ = fun _ j => j.elim0 := by
  ext _ j
  exact j.elim0

/-- The submatrix respects matrix addition. -/
theorem submatrixOfFinset_add {n m : ℕ} (A B : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) :
    submatrixOfFinset (A + B) U V = submatrixOfFinset A U V + submatrixOfFinset B U V := by
  ext i j
  simp [submatrixOfFinset]

/-- The submatrix respects scalar multiplication. -/
theorem submatrixOfFinset_smul {n m : ℕ} (c : R) (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) :
    submatrixOfFinset (c • A) U V = c • submatrixOfFinset A U V := by
  ext i j
  simp [submatrixOfFinset]

/-- The transpose of a submatrix equals the submatrix of the transpose with swapped indices. -/
theorem submatrixOfFinset_transpose {n m : ℕ} {R : Type*} (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) :
    (submatrixOfFinset A U V)ᵀ = submatrixOfFinset Aᵀ V U := by
  ext i j
  simp [submatrixOfFinset, Matrix.transpose_apply]

/-- A **minor** of a matrix A is the determinant of a square submatrix.
    This is det(sub_U^V A) where |U| = |V|.
    
    If |U| ≠ |V|, we define the minor to be 0 (since the submatrix is not square). -/
noncomputable def minor {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) : R :=
  if h : U.card = V.card then
    (A.submatrix (U.orderEmbOfFin rfl) (V.orderEmbOfFin (h ▸ rfl))).det
  else 0

/-- When |U| = |V|, the minor equals the determinant of the submatrix. -/
theorem minor_eq_det {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) (h : U.card = V.card) :
    minor A U V = (A.submatrix (U.orderEmbOfFin rfl) (V.orderEmbOfFin (h ▸ rfl))).det := by
  simp [minor, h]

/-- When |U| ≠ |V|, the minor is 0. -/
theorem minor_eq_zero_of_card_ne {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) (h : U.card ≠ V.card) :
    minor A U V = 0 := by
  simp [minor, h]

/-- For square matrices, `CauchyBinet.minor` equals `PermFinset.submatrixDet`.
    
    Both are "total" definitions (return 0 when |U| ≠ |V|). They are definitionally equal
    for square matrices. -/
theorem minor_eq_permFinset_submatrixDet {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) :
    minor A P Q = PermFinset.submatrixDet A P Q := by
  simp only [minor, PermFinset.submatrixDet]

/-- A **principal minor** of a square matrix is a minor where U = V.
    These are the determinants of principal submatrices (same rows and columns). -/
noncomputable def principalMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P : Finset (Fin n)) : R :=
  (A.submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det

/-- Principal minor equals the general minor when U = V. -/
theorem principalMinor_eq_minor {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P : Finset (Fin n)) :
    principalMinor A P = minor A P P := by
  simp [principalMinor, minor]

/-- The minor of the empty set is 1 (determinant of 0×0 matrix). -/
theorem minor_empty {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    minor A ∅ ∅ = 1 := by
  simp only [minor, Finset.card_empty, ↓reduceDIte]
  exact det_isEmpty

/-- Example: For a 3×3 matrix, sub_{0,1}^{0,2} A extracts the 2×2 submatrix
    with rows 0,1 and columns 0,2.
    
    For the matrix:
      (a   b   c  )
      (a'  b'  c' )
      (a'' b'' c'')
    
    we get sub_{0,1}^{0,2} A = (a   c )
                               (a'  c')
    
    Note: The textbook uses 1-indexing, so sub_{1,2}^{1,3} in the textbook
    corresponds to sub_{0,1}^{0,2} in our 0-indexed formalization. -/
example {A : Matrix (Fin 3) (Fin 3) R} :
    let U : Finset (Fin 3) := {0, 1}
    let V : Finset (Fin 3) := {0, 2}
    submatrixOfFinset A U V = A.submatrix (U.orderEmbOfFin rfl) (V.orderEmbOfFin rfl) := rfl

/-!
## Cauchy-Binet Formula (Theorem thm.det.CB)

For an n×m matrix A and an m×n matrix B:
  det(AB) = ∑_{g : strictly increasing n-tuple from [m]} det(cols_g A) · det(rows_g B)

This generalizes det(AB) = det(A)·det(B) for square matrices.

Special cases:
- If m < n, the sum is empty, so det(AB) = 0
- If m = n, there's only one term: det(A)·det(B)
-/

/-- The Cauchy-Binet formula for square matrices: det(AB) = det(A)·det(B).
    (Theorem thm.det.CB, special case m = n)
    Label: thm.det.CB

    The general Cauchy-Binet formula for non-square matrices involves a sum
    over order-preserving embeddings. This special case is what Mathlib provides
    directly as `Matrix.det_mul`. -/
theorem cauchyBinet_square {n : Type*} [DecidableEq n] [Fintype n]
    (A B : Matrix n n R) :
    (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

/-- Submatrix obtained by selecting specific columns of A.
    `cols_g A` in the source notation selects columns indexed by g. -/
noncomputable def colsSubmatrix {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (S : Finset (Fin m)) (hcard : S.card = n) : Matrix (Fin n) (Fin n) R :=
  A.submatrix id (S.orderEmbOfFin hcard)

/-- Submatrix obtained by selecting specific rows of B.
    `rows_g B` in the source notation selects rows indexed by g. -/
noncomputable def rowsSubmatrix {n m : ℕ} (B : Matrix (Fin m) (Fin n) R)
    (S : Finset (Fin m)) (hcard : S.card = n) : Matrix (Fin n) (Fin n) R :=
  B.submatrix (S.orderEmbOfFin hcard) id

/-- Helper lemma: when f is not injective, the alternating sum over permutations is 0. -/
lemma det_mul_aux_nonsquare {n m : ℕ} {A : Matrix (Fin n) (Fin m) R} {B : Matrix (Fin m) (Fin n) R}
    {f : Fin n → Fin m} (hf : ¬Function.Injective f) :
    (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (f i) * B (f i) i) = 0 := by
  obtain ⟨i, j, hfij, hij⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    rw [Function.Injective] at hf; push Not at hf; exact hf
  exact Finset.sum_involution (fun σ _ => σ * Equiv.swap i j)
    (fun σ _ => by
      have h1 : (∏ k, A (σ k) (f k)) = ∏ k, A ((σ * Equiv.swap i j) k) (f k) := by
        refine Fintype.prod_equiv (Equiv.swap i j) _ _ (fun k => ?_)
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_self, 
          Equiv.apply_swap_eq_self hfij]
      have h2 : (Equiv.Perm.sign (σ * Equiv.swap i j) : R) = -(Equiv.Perm.sign σ : R) := by 
        simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
      simp only [h2, neg_mul, h1, Finset.prod_mul_distrib]; ring)
    (fun σ _ _ => (not_congr Equiv.mul_swap_eq_iff).mpr hij)
    (fun _ _ => Finset.mem_univ _) (fun σ _ => Equiv.mul_swap_involutive i j σ)

/-- Key identity: for a fixed subset S, the sum over permutations gives det(cols_S A) * det(rows_S B). -/
lemma sum_over_subset_eq_det_mul {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (S : Finset (Fin m)) (hcard : S.card = n) :
    ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n), 
      (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (S.orderEmbOfFin hcard (τ i)) * 
        B (S.orderEmbOfFin hcard (τ i)) i =
    (colsSubmatrix A S hcard).det * (rowsSubmatrix B S hcard).det := by
  let e := S.orderEmbOfFin hcard
  have split_prod : ∀ σ τ : Equiv.Perm (Fin n), 
      (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (e (τ i)) * B (e (τ i)) i = 
      (Equiv.Perm.sign σ : R) * (∏ i, A (σ i) (e (τ i))) * (∏ i, B (e (τ i)) i) := by
    intro σ τ
    calc (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (e (τ i)) * B (e (τ i)) i 
        = (Equiv.Perm.sign σ : R) * (∏ i, A (σ i) (e (τ i)) * B (e (τ i)) i) := by ring
      _ = (Equiv.Perm.sign σ : R) * ((∏ i, A (σ i) (e (τ i))) * (∏ i, B (e (τ i)) i)) := by 
          rw [← Finset.prod_mul_distrib]
      _ = (Equiv.Perm.sign σ : R) * (∏ i, A (σ i) (e (τ i))) * (∏ i, B (e (τ i)) i) := by ring
  conv_lhs => arg 2; ext τ; arg 2; ext σ; rw [split_prod σ τ]
  have factor_B : ∀ τ : Equiv.Perm (Fin n),
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * (∏ i, A (σ i) (e (τ i))) * 
        (∏ i, B (e (τ i)) i) =
      (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (e (τ i))) * 
        (∏ i, B (e (τ i)) i) := by
    intro τ
    have h : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * (∏ i, A (σ i) (e (τ i))) * 
        (∏ i, B (e (τ i)) i) =
        ((Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (e (τ i))) * (∏ i, B (e (τ i)) i) := fun σ => by ring
    conv_lhs => arg 2; ext σ; rw [h σ]
    rw [← Finset.sum_mul]
  conv_lhs => arg 2; ext τ; rw [factor_B τ]
  have A_sum : ∀ τ : Equiv.Perm (Fin n), 
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (e (τ i)) = 
      (Equiv.Perm.sign τ : R) * (A.submatrix id e).det := by
    intro τ
    have eq1 : ∀ σ : Equiv.Perm (Fin n), ∀ i : Fin n, 
        A (σ i) (e (τ i)) = (A.submatrix id e).submatrix id τ (σ i) i := by
      intro σ i; simp [Matrix.submatrix]
    conv_lhs => arg 2; ext σ; arg 2; arg 2; ext i; rw [eq1 σ i]
    rw [← Matrix.det_apply', Matrix.det_permute' τ]
  conv_lhs => arg 2; ext τ; arg 1; rw [A_sum τ]
  have h4 : ∀ τ : Equiv.Perm (Fin n), 
      (Equiv.Perm.sign τ : R) * (A.submatrix id e).det * ∏ i, B (e (τ i)) i =
      (A.submatrix id e).det * ((Equiv.Perm.sign τ : R) * ∏ i, B (e (τ i)) i) := fun τ => by ring
  conv_lhs => arg 2; ext τ; rw [h4 τ]
  rw [← Finset.mul_sum]
  have B_sum : ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : R) * ∏ i, B (e (τ i)) i = 
      (B.submatrix e id).det := by
    have eq1 : ∀ τ : Equiv.Perm (Fin n), ∀ i : Fin n, B (e (τ i)) i = (B.submatrix e id) (τ i) i := by
      intro τ i; simp [Matrix.submatrix]
    conv_lhs => arg 2; ext τ; arg 2; arg 2; ext i; rw [eq1 τ i]
    rw [← Matrix.det_apply']
  rw [B_sum]; rfl

/-- Helper: orderEmbOfFin applied to the inverse of orderIsoOfFin recovers the original element. -/
private lemma orderEmbOfFin_symm {n m : ℕ} (S : Finset (Fin m)) (hcard : S.card = n) 
    (x : Fin m) (hx : x ∈ S) :
    S.orderEmbOfFin hcard ((S.orderIsoOfFin hcard).symm ⟨x, hx⟩) = x := by
  have h := (S.orderIsoOfFin hcard).apply_symm_apply ⟨x, hx⟩
  have h' : ((S.orderIsoOfFin hcard) ((S.orderIsoOfFin hcard).symm ⟨x, hx⟩)).val = x := by rw [h]
  simp only [Finset.orderEmbOfFin]; convert h'; rfl

/-- Helper: orderIsoOfFin.symm applied to orderEmbOfFin gives back the original index. -/
private lemma orderIsoOfFin_symm_orderEmbOfFin {n m : ℕ} (S : Finset (Fin m)) (hcard : S.card = n) 
    (i : Fin n) :
    (S.orderIsoOfFin hcard).symm ⟨S.orderEmbOfFin hcard i, Finset.orderEmbOfFin_mem S hcard i⟩ = i := by
  apply (S.orderIsoOfFin hcard).injective
  simp only [OrderIso.apply_symm_apply]
  ext; rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a fixed S with |S| = n, injective functions with image S correspond bijectively 
    to permutations of Fin n. This allows us to transform the sum over such functions 
    into a sum over permutations. -/
private lemma sum_over_image_eq_sum_perm {n m : ℕ} (S : Finset (Fin m)) (hS : S.card = n) 
    (F : (Fin n → Fin m) → R) :
    ∑ f ∈ ((Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective).filter 
        (fun f => Finset.univ.image f = S), F f =
    ∑ τ : Equiv.Perm (Fin n), F (fun k => S.orderEmbOfFin hS (τ k)) := by
  -- Forward map: τ ↦ (fun k => S.orderEmbOfFin hS (τ k))
  let toFun : Equiv.Perm (Fin n) → (Fin n → Fin m) := fun τ k => S.orderEmbOfFin hS (τ k)
  have htoFun : ∀ τ, toFun τ ∈ ((Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective).filter 
      (fun f => Finset.univ.image f = S) := by
    intro τ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, toFun]
    constructor
    · intro a b h; exact τ.injective ((S.orderEmbOfFin hS).injective h)
    · ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro ⟨k, hk⟩; rw [← hk]; exact Finset.orderEmbOfFin_mem S hS (τ k)
      · intro hx; use τ.symm ((S.orderIsoOfFin hS).symm ⟨x, hx⟩)
        simp only [Equiv.apply_symm_apply]; exact orderEmbOfFin_symm S hS x hx
  -- Inverse map: for f in the filtered set, construct the permutation
  let invFun : (f : Fin n → Fin m) → (hf : Function.Injective f ∧ Finset.univ.image f = S) → 
      Equiv.Perm (Fin n) := fun f hf => Equiv.ofBijective 
    (fun k => (S.orderIsoOfFin hS).symm ⟨f k, by rw [← hf.2]; simp⟩)
    ⟨by intro a b h; have h' := congr_arg (S.orderIsoOfFin hS) h; simp at h'; exact hf.1 h', 
     Finite.injective_iff_surjective.mp (by 
       intro a b h; have h' := congr_arg (S.orderIsoOfFin hS) h; simp at h'; exact hf.1 h')⟩
  symm
  refine Finset.sum_bij' (fun τ _ => toFun τ) 
    (fun f hf => invFun f (by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf; exact hf)) 
    ?_ ?_ ?_ ?_ ?_
  · intro τ _; exact htoFun τ
  · intro f hf; exact Finset.mem_univ _
  · intro τ _; simp only [toFun, invFun]; ext k; simp only [Equiv.ofBijective_apply]; 
    have := orderIsoOfFin_symm_orderEmbOfFin S hS (τ k); simp only [this]
  · intro f hf; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf; funext k
    simp only [toFun, invFun, Equiv.ofBijective_apply]
    exact orderEmbOfFin_symm S hS (f k) (by rw [← hf.2]; simp)
  · intro τ _; rfl

/-- Partition the sum over injective functions by their image. Each fiber over a subset S
    corresponds to a sum over permutations. -/
private lemma sum_injective_eq_sum_over_subsets {n m : ℕ} (F : (Fin n → Fin m) → R) :
    ∑ f ∈ (Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective, F f =
    ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      if h : S.card = n then ∑ τ : Equiv.Perm (Fin n), F (fun i => S.orderEmbOfFin h (τ i)) else 0 := by
  let g : (Fin n → Fin m) → Finset (Fin m) := fun f => Finset.univ.image f
  have hg : ∀ f ∈ (Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective,
      g f ∈ (Finset.univ : Finset (Fin m)).powersetCard n := by
    intro f hf; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [g, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    rw [Finset.card_image_of_injective _ hf]; simp
  rw [← Finset.sum_fiberwise_of_maps_to hg F]; apply Finset.sum_congr rfl; intro S hS
  simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS; rw [dite_eq_left hS]
  have h_fiber : (Finset.filter Function.Injective Finset.univ).filter (fun f => g f = S) =
      ((Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective).filter 
        (fun f => Finset.univ.image f = S) := by ext f; simp [g]
  rw [h_fiber]; exact sum_over_image_eq_sum_perm S hS F

/-- The general Cauchy-Binet formula (Theorem thm.det.CB).
    For an n×m matrix A and an m×n matrix B:
      det(AB) = ∑_{S ⊆ [m], |S|=n} det(cols_S A) · det(rows_S B)

    The sum ranges over all n-element subsets S of [m], where cols_S A is the
    n×n matrix formed by selecting columns of A indexed by S (in increasing order),
    and rows_S B is the n×n matrix formed by selecting rows of B indexed by S.

    Special cases:
    - If m < n, the sum is empty (no n-element subsets), so det(AB) = 0
    - If m = n, there's only one term S = [m], giving det(A)·det(B) -/
theorem cauchyBinet {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) :
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      if h : S.card = n then
        (colsSubmatrix A S h).det * (rowsSubmatrix B S h).det
      else 0 := by
  -- Expand det(AB) using Leibniz formula
  calc (A * B).det 
      = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i, (A * B) (σ i) i := by 
          rw [Matrix.det_apply']
    _ = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * 
          ∏ i, ∑ k : Fin m, A (σ i) k * B k i := by rfl
    _ = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * 
          ∑ f : Fin n → Fin m, ∏ i, A (σ i) (f i) * B (f i) i := by
        congr 1; ext σ; congr 1
        rw [Finset.prod_univ_sum]; simp only [Fintype.piFinset_univ]
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ f : Fin n → Fin m, 
          (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (f i) * B (f i) i := by
        congr 1; ext σ; rw [mul_sum]
    _ = ∑ f : Fin n → Fin m, ∑ σ : Equiv.Perm (Fin n), 
          (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (f i) * B (f i) i := by
        rw [Finset.sum_comm]
    _ = ∑ f ∈ (Finset.univ : Finset (Fin n → Fin m)).filter Function.Injective, 
          ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : R) * ∏ i, A (σ i) (f i) * B (f i) i := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro f _ hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        exact det_mul_aux_nonsquare hf
    _ = _ := by
        -- Use the bijection between injective functions and (subset, permutation) pairs
        rw [sum_injective_eq_sum_over_subsets]
        apply Finset.sum_congr rfl; intro S hS
        split_ifs with h
        · exact sum_over_subset_eq_det_mul A B S h
        · rfl

/-- When m < n for an n×m matrix times an m×n matrix, det(AB) = 0.
    (Remark after Theorem thm.det.CB)

    This follows from the general Cauchy-Binet formula: when m < n, there are
    no n-element subsets of [m], so the sum is empty.

    When K is a field, this can also be seen from rank considerations:
    the product AB has rank at most m < n. -/
theorem det_mul_eq_zero_of_rank_deficient {n m : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) (h : m < n) :
    (A * B).det = 0 := by
  rw [cauchyBinet]
  have hempty : (Finset.univ : Finset (Fin m)).powersetCard n = ∅ := by
    rw [powersetCard_eq_empty]
    simp only [card_univ, Fintype.card_fin]
    exact h
  rw [hempty]
  simp

/-!
## Determinant of A + B (Theorem thm.det.det(A+B))

For n×n matrices A and B:
  det(A+B) = ∑_{P ⊆ [n]} ∑_{Q ⊆ [n], |P|=|Q|} (-1)^(sum P + sum Q) · det(sub_P^Q A) · det(sub_P̃^Q̃ B)

where P̃ denotes the complement [n] \ P.

This is a "binomial theorem" for determinants, containing det(A) (P=Q=[n])
and det(B) (P=Q=∅) as special terms.
-/

/-- Sum of elements in a finset of Fin n, viewed as natural numbers.
    Used in the sign factor of the det(A+B) formula.

    Note: This is named `finsetSumFin` to distinguish from `AlgebraicCombinatorics.QBinomialRec.finsetSumNat`,
    which computes the sum of elements in a `Finset ℕ` directly.
    Both compute "the sum of elements" but for different element types. -/
def finsetSumFin {n : ℕ} (P : Finset (Fin n)) : ℕ := ∑ i ∈ P, i.val

/-- The sum over the empty set is 0. -/
@[simp] lemma finsetSumFin_empty {n : ℕ} : finsetSumFin (∅ : Finset (Fin n)) = 0 := by
  simp [finsetSumFin]

/-- Helper: Given P, Q with same cardinality, compute the determinant of the
    submatrix of A restricted to rows P and columns Q. -/
noncomputable def submatrixDet {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (h : P.card = Q.card) : R :=
  (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det

/-- `CauchyBinet.submatrixDet` equals `PermFinset.submatrixDet` when cardinalities match.
    
    This lemma bridges the proof-requiring version in CauchyBinet with the total version
    in PermFinset. Use this when migrating code between the two styles. -/
theorem submatrixDet_eq_permFinset {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (h : P.card = Q.card) :
    submatrixDet A P Q h = PermFinset.submatrixDet A P Q := by
  simp only [submatrixDet, PermFinset.submatrixDet, h, ↓reduceDIte]

/-! ### Proof infrastructure for det(A+B) formula

The proof proceeds in several steps:
1. Expand det(A+B) using the Leibniz formula
2. Use the product rule ∏(a+b) = ∑_P (∏_{i∈P} a_i)(∏_{i∈Pᶜ} b_i)
3. Swap the order of summation
4. Partition the sum over σ based on σ(P) = Q
5. Factor out the sign and show it equals (-1)^(sum P + sum Q)
6. Recognize the remaining sums as determinants of submatrices
-/

/-!
### Permutation image definitions

These are local definitions that duplicate the bodies of the canonical definitions in 
`PermFinset` namespace (`Determinants/PermFinset.lean`). The definitions are 
**definitionally equal** to their `PermFinset` counterparts (witnessed by 
`imageFinset_eq_permFinset` and `permsMapping_eq_permFinset`), but are kept as 
separate `def`s rather than wrappers because many proofs in this file rely on 
specific unfolding behavior with `simp [imageFinset]`.

**For new code**: Use `PermFinset.imageFinset` and `PermFinset.permsMapping` directly.
-/

/-- The image of a finset under a permutation.
    
    This is definitionally equal to `PermFinset.imageFinset` (see `imageFinset_eq_permFinset`).
    New code should prefer `PermFinset.imageFinset`. -/
def imageFinset {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) : Finset (Fin n) :=
  P.map ⟨σ, σ.injective⟩

/-- The image has the same cardinality as the original set.
    See also `PermFinset.imageFinset_card`. -/
theorem imageFinset_card {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) :
    (imageFinset σ P).card = P.card := by
  simp [imageFinset]

/-- The image of a complement equals the complement of the image.
    See also `PermFinset.imageFinset_compl`. -/
lemma imageFinset_compl {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) :
    imageFinset σ Pᶜ = (imageFinset σ P)ᶜ := by
  ext x
  simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_compl]
  constructor
  · intro ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    rw [← hyx] at hzx
    have heq := σ.injective hzx
    exact hy (heq ▸ hz)
  · intro hx
    use σ.symm x
    constructor
    · intro h
      apply hx
      exact ⟨σ.symm x, h, by simp⟩
    · simp

/-- The set of permutations that map P to Q.
    
    This is definitionally equal to `PermFinset.permsMapping` (see `permsMapping_eq_permFinset`).
    New code should prefer `PermFinset.permsMapping`. -/
def permsMapping {n : ℕ} (P Q : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => imageFinset σ P = Q)

/-- If |P| ≠ |Q|, no permutation maps P to Q.
    See also `PermFinset.permsMapping_empty_of_card_ne`. -/
theorem permsMapping_empty_of_card_ne {n : ℕ} (P Q : Finset (Fin n))
    (h : P.card ≠ Q.card) : permsMapping P Q = ∅ := by
  simp only [permsMapping, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
  intro σ heq
  rw [← imageFinset_card σ P, heq] at h
  exact h rfl

/-- `imageFinset` is definitionally equal to `PermFinset.imageFinset`. -/
theorem imageFinset_eq_permFinset {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) :
    imageFinset σ P = PermFinset.imageFinset σ P := rfl

/-- `permsMapping` is definitionally equal to `PermFinset.permsMapping`. -/
theorem permsMapping_eq_permFinset {n : ℕ} (P Q : Finset (Fin n)) :
    permsMapping P Q = PermFinset.permsMapping P Q := rfl

/-- First step: expand det(A+B) using the Leibniz formula and product rule.

    This expands det(A+B) = ∑_σ sign(σ) ∏_i (A + B)_{σ(i),i}
    into ∑_σ sign(σ) ∑_P (∏_{i∈P} A_{σ(i),i}) · (∏_{i∈Pᶜ} B_{σ(i),i})
    using the product rule for (a + b). -/
theorem det_add_expand_step1 {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    (A + B).det = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
      ∑ P : Finset (Fin n), (∏ i ∈ P, A (σ i) i) * (∏ i ∈ Pᶜ, B (σ i) i) := by
  rw [det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  have h : ∏ i : Fin n, (A + B) (σ i) i = ∏ i : Fin n, (A (σ i) i + B (σ i) i) := by
    apply Finset.prod_congr rfl
    intro i _
    simp only [Matrix.add_apply]
  simp only [h, Fintype.prod_add, smul_sum]

/-- Second step: swap the order of summation over σ and P. -/
theorem det_add_expand_step2 {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    (A + B).det = ∑ P : Finset (Fin n), ∑ σ : Equiv.Perm (Fin n),
      Equiv.Perm.sign σ • ((∏ i ∈ P, A (σ i) i) * (∏ i ∈ Pᶜ, B (σ i) i)) := by
  rw [det_add_expand_step1]
  simp only [smul_sum]
  rw [Finset.sum_comm]

/-- Third step: partition the sum over σ based on σ(P) = Q. -/
theorem det_add_expand_step3 {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    (A + B).det = ∑ P : Finset (Fin n), ∑ Q : Finset (Fin n),
      ∑ σ ∈ permsMapping P Q,
        Equiv.Perm.sign σ • ((∏ i ∈ P, A (σ i) i) * (∏ i ∈ Pᶜ, B (σ i) i)) := by
  rw [det_add_expand_step2]
  congr 1
  ext P
  -- Partition univ by Q = σ(P)
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin n))) =
      Finset.univ.biUnion (fun Q => permsMapping P Q) := by
    ext σ
    constructor
    · intro _
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨imageFinset σ P, by simp [permsMapping]⟩
    · intro _
      exact Finset.mem_univ σ
  have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Finset (Fin n))) : Set _)
      (fun Q => permsMapping P Q) := by
    intro Q₁ _ Q₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left, permsMapping, Finset.mem_filter,
               Finset.mem_univ, true_and]
    intro σ h1 h2
    exact hne (h1.symm.trans h2)
  rw [huniv, Finset.sum_biUnion hdisj]

/-- The n=2 case of det(A+B) formula, expanded explicitly.
    This serves as a sanity check for the general formula. -/
theorem det_add_fin_two (A B : Matrix (Fin 2) (Fin 2) R) :
    (A + B).det = A.det + B.det +
      A 0 0 * B 1 1 + A 1 1 * B 0 0 - A 0 1 * B 1 0 - A 1 0 * B 0 1 := by
  simp only [det_fin_two, Matrix.add_apply]
  ring

/-! ### Helper lemmas for the key factorization

The proof of `sum_perms_mapping_eq_det_product` requires:
1. A bijection between {σ : σ(P) = Q} and Perm(Fin |P|) × Perm(Fin |Pᶜ|)
2. A sign identity: sign(σ) = (-1)^(sum P + sum Q) · sign(α) · sign(β)
3. Product factorization into determinants

We build these up step by step.
-/

/-- For σ with σ(P) = Q, the image of any element of P under σ lies in Q. -/
lemma sigma_orderEmb_mem_of_imageFinset {n : ℕ} (P Q : Finset (Fin n)) 
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) (i : Fin P.card) :
    σ (P.orderEmbOfFin rfl i) ∈ Q := by
  rw [← hσ]
  simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
  exact ⟨P.orderEmbOfFin rfl i, Finset.orderEmbOfFin_mem P rfl i, rfl⟩

/-- For σ with σ(P) = Q, the image of any element of Pᶜ under σ lies in Qᶜ. -/
lemma sigma_orderEmb_compl_mem_of_imageFinset {n : ℕ} (P Q : Finset (Fin n)) 
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) (i : Fin Pᶜ.card) :
    σ (Pᶜ.orderEmbOfFin rfl i) ∈ Qᶜ := by
  simp only [Finset.mem_compl]
  intro hcontra
  rw [← hσ] at hcontra
  simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at hcontra
  obtain ⟨p, hp, hσp⟩ := hcontra
  have : Pᶜ.orderEmbOfFin rfl i ∈ P := by
    have h := σ.injective hσp
    rw [← h]
    exact hp
  have hmem : Pᶜ.orderEmbOfFin rfl i ∈ Pᶜ := Finset.orderEmbOfFin_mem Pᶜ rfl i
  exact (Finset.mem_compl.mp hmem) this

/-- Extract α from σ: For σ with σ(P) = Q, extract the permutation α ∈ Perm(Fin |P|)
    that describes how σ permutes the elements of P.
    
    Specifically, if p₁ < p₂ < ... < pₖ are the elements of P and 
    q₁ < q₂ < ... < qₖ are the elements of Q, then α is defined by
    σ(pᵢ) = q_{α(i)}. -/
noncomputable def extractAlpha {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) : Equiv.Perm (Fin P.card) := by
  let pEmb := P.orderEmbOfFin rfl
  have h : ∀ i : Fin P.card, σ (pEmb i) ∈ Q := sigma_orderEmb_mem_of_imageFinset P Q σ hσ
  let qIso : Fin P.card ≃o Q := Q.orderIsoOfFin hcard.symm
  let f : Fin P.card → Fin P.card := fun i => qIso.symm ⟨σ (pEmb i), h i⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    have := qIso.symm.injective hab
    simp only [Subtype.mk.injEq] at this
    exact pEmb.injective (σ.injective this)
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-- Extract β from σ: For σ with σ(P) = Q, extract the permutation β ∈ Perm(Fin |Pᶜ|)
    that describes how σ permutes the elements of Pᶜ. -/
noncomputable def extractBeta {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) : Equiv.Perm (Fin Pᶜ.card) := by
  have hcard' : Pᶜ.card = Qᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin, hcard]
  let pEmb := Pᶜ.orderEmbOfFin rfl
  have h : ∀ i : Fin Pᶜ.card, σ (pEmb i) ∈ Qᶜ := sigma_orderEmb_compl_mem_of_imageFinset P Q σ hσ
  let qIso : Fin Pᶜ.card ≃o (Qᶜ : Finset (Fin n)) := Qᶜ.orderIsoOfFin hcard'.symm
  let f : Fin Pᶜ.card → Fin Pᶜ.card := fun i => qIso.symm ⟨σ (pEmb i), h i⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    have := qIso.symm.injective hab
    simp only [Subtype.mk.injEq] at this
    exact pEmb.injective (σ.injective this)
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

/-! ### Helper lemmas for empty set case in sign_decomposition -/

/-- Helper for idxOf computation -/
private lemma ofFn_id_nodup {n : ℕ} : (List.ofFn (fun i : Fin n => i)).Nodup := by
  rw [List.nodup_ofFn]
  exact Function.injective_id

/-- The idxOf of i in [0, 1, ..., n-1] is i -/
private lemma idxOf_ofFn_id {n : ℕ} (i : Fin n) : 
    (List.ofFn (fun j : Fin n => j)).idxOf i = i.val := by
  have h_nodup := ofFn_id_nodup (n := n)
  have h_len : i.val < (List.ofFn (fun j : Fin n => j)).length := by simp
  have h_getElem : (List.ofFn (fun j : Fin n => j))[i.val]'h_len = i := by simp
  have h_idx := h_nodup.idxOf_getElem i.val h_len
  simp only [h_getElem] at h_idx
  exact h_idx

/-- The orderEmbOfFin on ∅ᶜ = univ maps i to ⟨i.val, _⟩ (essentially identity) -/
private lemma orderEmbOfFin_empty_compl {n : ℕ} (i : Fin ((∅ : Finset (Fin n))ᶜ : Finset (Fin n)).card) :
    (((∅ : Finset (Fin n))ᶜ : Finset (Fin n)).orderEmbOfFin rfl i).val = i.val := by
  have h_univ : ((∅ : Finset (Fin n))ᶜ : Finset (Fin n)) = Finset.univ := by simp
  have h_sort : (((∅ : Finset (Fin n))ᶜ : Finset (Fin n))).sort (· ≤ ·) = List.finRange n := by
    rw [h_univ]
    apply List.Perm.eq_of_sortedLE
    · have h := Finset.sortedLT_sort (Finset.univ : Finset (Fin n))
      exact h.sortedLE
    · exact (List.sortedLT_finRange n).sortedLE
    · apply List.perm_of_nodup_nodup_toFinset_eq
      · exact Finset.sort_nodup _ _
      · exact List.nodup_finRange n
      · ext x; simp
  rw [Finset.orderEmbOfFin_apply]
  have h_card : ((∅ : Finset (Fin n))ᶜ : Finset (Fin n)).card = n := by simp
  have hi : i.val < (List.finRange n).length := by simp; exact Fin.cast h_card i |>.isLt
  have h_getElem : ((((∅ : Finset (Fin n))ᶜ : Finset (Fin n))).sort (· ≤ ·))[i] = 
                   (List.finRange n)[i.val]'hi := by
    simp only [h_sort]
    congr 1
  rw [h_getElem]
  simp [List.finRange]

/-- The orderIsoOfFin.symm on ∅ᶜ = univ returns the element's value as a Fin n -/
private lemma orderIsoOfFin_empty_compl_symm {n : ℕ} (x : (((∅ : Finset (Fin n))ᶜ : Finset (Fin n)))) :
    ((((∅ : Finset (Fin n))ᶜ : Finset (Fin n))).orderIsoOfFin rfl).symm x = 
    ⟨x.val.val, by simp⟩ := by
  ext
  rw [Finset.orderIsoOfFin_symm_apply]
  have h_univ : (((∅ : Finset (Fin n))ᶜ : Finset (Fin n))) = Finset.univ := by simp
  have h_sort : ((((∅ : Finset (Fin n))ᶜ : Finset (Fin n)))).sort (· ≤ ·) = List.finRange n := by
    rw [h_univ]
    apply List.Perm.eq_of_sortedLE
    · have h := Finset.sortedLT_sort (Finset.univ : Finset (Fin n))
      exact h.sortedLE
    · exact (List.sortedLT_finRange n).sortedLE
    · apply List.perm_of_nodup_nodup_toFinset_eq
      · exact Finset.sort_nodup _ _
      · exact List.nodup_finRange n
      · ext y; simp
  simp only [h_sort, List.finRange]
  exact idxOf_ofFn_id x.val

set_option backward.isDefEq.respectTransparency false in
/-- When P = Q = ∅, extractBeta is conjugate to σ by the natural bijection Fin n ≃ Fin (∅ᶜ.card).
    Therefore sign(extractBeta ∅ ∅ _ σ _) = sign(σ). -/
private lemma sign_extractBeta_empty {n : ℕ} (hcard : (∅ : Finset (Fin n)).card = (∅ : Finset (Fin n)).card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ ∅ = ∅) :
    Equiv.Perm.sign (extractBeta ∅ ∅ hcard σ hσ) = Equiv.Perm.sign σ := by
  -- Use sign_eq_sign_of_equiv with e : Fin n ≃ Fin (∅ᶜ.card)
  have h_card_eq : ((∅ : Finset (Fin n))ᶜ : Finset (Fin n)).card = n := by simp
  let e : Fin n ≃ Fin (((∅ : Finset (Fin n))ᶜ : Finset (Fin n))).card := Fin.castOrderIso h_card_eq.symm
  apply (Equiv.Perm.sign_eq_sign_of_equiv σ (extractBeta ∅ ∅ hcard σ hσ) e _).symm
  intro x
  -- Need: e (σ x) = extractBeta ∅ ∅ hcard σ hσ (e x)
  simp only [extractBeta, Equiv.ofBijective_apply]
  ext
  -- LHS: (e (σ x)).val = (σ x).val
  have h1 : (e (σ x)).val = (σ x).val := by simp [e, Fin.castOrderIso]
  -- RHS: need to show the orderIsoOfFin.symm ⟨σ(orderEmbOfFin (e x)), _⟩ has val = (σ x).val
  -- First, orderEmbOfFin (e x) has val = (e x).val = x.val
  have h2 : ((((∅ : Finset (Fin n))ᶜ : Finset (Fin n))).orderEmbOfFin rfl (e x)).val = x.val := by
    rw [orderEmbOfFin_empty_compl]
    simp [e, Fin.castOrderIso]
  -- So orderEmbOfFin (e x) = x as Fin n
  have h3 : (((∅ : Finset (Fin n))ᶜ : Finset (Fin n))).orderEmbOfFin rfl (e x) = x := by ext; exact h2
  rw [h1]
  rw [orderIsoOfFin_empty_compl_symm]
  simp only [h3]

set_option backward.isDefEq.respectTransparency false in
/-- When P = Q = univ, extractAlpha is conjugate to σ by the natural bijection Fin n ≃ Fin (univ.card).
    Therefore sign(extractAlpha univ univ _ σ _) = sign(σ). -/
private lemma sign_extractAlpha_univ {n : ℕ} 
    (hcard : (Finset.univ : Finset (Fin n)).card = (Finset.univ : Finset (Fin n)).card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ Finset.univ = Finset.univ) :
    Equiv.Perm.sign (extractAlpha Finset.univ Finset.univ hcard σ hσ) = Equiv.Perm.sign σ := by
  have h_card : (Finset.univ : Finset (Fin n)).card = n := by simp
  let e : Fin n ≃ Fin (Finset.univ : Finset (Fin n)).card := Fin.castOrderIso h_card.symm
  apply (Equiv.Perm.sign_eq_sign_of_equiv σ (extractAlpha Finset.univ Finset.univ hcard σ hσ) e _).symm
  intro x
  simp only [extractAlpha, Equiv.ofBijective_apply]
  ext
  -- Key helper: sort of univ is finRange
  have h_sort : (Finset.univ : Finset (Fin n)).sort (· ≤ ·) = List.finRange n := by
    apply List.Perm.eq_of_sortedLE
    · exact (Finset.sortedLT_sort _).sortedLE
    · exact (List.sortedLT_finRange n).sortedLE
    · apply List.perm_of_nodup_nodup_toFinset_eq
      · exact Finset.sort_nodup _ _
      · exact List.nodup_finRange n
      · ext y; simp
  -- orderEmbOfFin univ rfl (e x) has val = x.val
  have h_emb : ((Finset.univ : Finset (Fin n)).orderEmbOfFin rfl (e x)).val = x.val := by
    rw [Finset.orderEmbOfFin_apply]
    simp only [h_sort, List.finRange, List.getElem_ofFn, Fin.getElem_fin]
    simp [e, Fin.castOrderIso]
  -- So orderEmbOfFin univ rfl (e x) = x
  have h_emb_eq : (Finset.univ : Finset (Fin n)).orderEmbOfFin rfl (e x) = x := by
    ext; exact h_emb
  -- LHS: (e (σ x)).val = (σ x).val
  have h_lhs : (e (σ x)).val = (σ x).val := by simp [e, Fin.castOrderIso]
  rw [h_lhs]
  -- Now goal is: (σ x).val = (orderIsoOfFin.symm ⟨σ (orderEmbOfFin (e x)), _⟩).val
  rw [Finset.orderIsoOfFin_symm_apply]
  simp only [h_sort]
  -- Goal: (σ x).val = List.idxOf (σ (orderEmbOfFin (e x))) (finRange n)
  simp only [h_emb_eq]
  exact (List.idxOf_finRange (σ x)).symm

/-- Given α ∈ Perm(Fin |P|) and β ∈ Perm(Fin |Pᶜ|), construct σ ∈ Perm(Fin n) with σ(P) = Q.
    This is the inverse of the (extractAlpha, extractBeta) bijection. -/
noncomputable def constructSigma {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (α : Equiv.Perm (Fin P.card)) (β : Equiv.Perm (Fin Pᶜ.card)) : Equiv.Perm (Fin n) := by
  have hcardC : Pᶜ.card = Qᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin, hcard]
  let pEmb := P.orderEmbOfFin rfl
  let qEmb : Fin P.card ↪o Fin n := Q.orderEmbOfFin (by rw [hcard])
  let pCEmb := Pᶜ.orderEmbOfFin rfl
  let qCEmb : Fin Pᶜ.card ↪o Fin n := Qᶜ.orderEmbOfFin (by rw [hcardC])
  -- Construct the function
  let f : Fin n → Fin n := fun x =>
    if h : x ∈ P then
      qEmb (α ((P.orderIsoOfFin rfl).symm ⟨x, h⟩))
    else
      qCEmb (β ((Pᶜ.orderIsoOfFin rfl).symm ⟨x, Finset.mem_compl.mpr h⟩))
  -- Prove it's a bijection
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    by_cases ha : a ∈ P <;> by_cases hb : b ∈ P
    · simp only [ha, hb, dite_eq_left] at hab
      have := qEmb.injective hab
      have := α.injective this
      have := (P.orderIsoOfFin rfl).symm.injective this
      simp only [Subtype.mk.injEq] at this
      exact this
    · simp only [ha, hb, dite_eq_left, dite_eq_right, not_false_eq_true] at hab
      have h1 : qEmb (α ((P.orderIsoOfFin rfl).symm ⟨a, ha⟩)) ∈ Q := Finset.orderEmbOfFin_mem _ _ _
      have h2 : qCEmb (β ((Pᶜ.orderIsoOfFin rfl).symm ⟨b, Finset.mem_compl.mpr hb⟩)) ∈ Qᶜ := 
        Finset.orderEmbOfFin_mem _ _ _
      rw [hab] at h1
      exact absurd h1 (Finset.mem_compl.mp h2)
    · simp only [ha, hb, dite_eq_left, dite_eq_right, not_false_eq_true] at hab
      have h1 : qEmb (α ((P.orderIsoOfFin rfl).symm ⟨b, hb⟩)) ∈ Q := Finset.orderEmbOfFin_mem _ _ _
      have h2 : qCEmb (β ((Pᶜ.orderIsoOfFin rfl).symm ⟨a, Finset.mem_compl.mpr ha⟩)) ∈ Qᶜ := 
        Finset.orderEmbOfFin_mem _ _ _
      rw [← hab] at h1
      exact absurd h1 (Finset.mem_compl.mp h2)
    · simp only [ha, hb, dite_eq_right, not_false_eq_true] at hab
      have := qCEmb.injective hab
      have := β.injective this
      have := (Pᶜ.orderIsoOfFin rfl).symm.injective this
      simp only [Subtype.mk.injEq] at this
      exact this
  exact Equiv.ofBijective f ⟨hf_inj, Finite.injective_iff_surjective.mp hf_inj⟩

set_option backward.isDefEq.respectTransparency false in
/-- The constructed permutation maps P to Q. -/
lemma constructSigma_imageFinset {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (α : Equiv.Perm (Fin P.card)) (β : Equiv.Perm (Fin Pᶜ.card)) :
    imageFinset (constructSigma P Q hcard α β) P = Q := by
  ext x
  simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro ⟨y, hy, hyx⟩
    simp only [constructSigma, Equiv.ofBijective_apply] at hyx
    simp only [hy, dite_eq_left] at hyx
    rw [← hyx]
    exact Finset.orderEmbOfFin_mem Q (by rw [hcard]) _
  · intro hx
    -- Need to find y ∈ P such that constructSigma maps y to x
    -- Since x ∈ Q, we need y = P.orderEmb(α⁻¹(Q.orderIso⁻¹(x)))
    let qIso := Q.orderIsoOfFin (hcard.symm)
    let idx : Fin P.card := α.symm (qIso.symm ⟨x, hx⟩)
    let y := P.orderEmbOfFin rfl idx
    use y
    constructor
    · exact Finset.orderEmbOfFin_mem P rfl idx
    · simp only [constructSigma, Equiv.ofBijective_apply]
      have hy_mem : y ∈ P := Finset.orderEmbOfFin_mem P rfl idx
      simp only [hy_mem, dite_eq_left]
      -- Need to show: Q.orderEmbOfFin _ (α ((P.orderIsoOfFin rfl).symm ⟨y, hy_mem⟩)) = x
      -- (P.orderIsoOfFin rfl).symm ⟨y, hy_mem⟩ = idx since y = P.orderEmbOfFin rfl idx
      have h1 : (P.orderIsoOfFin rfl).symm ⟨y, hy_mem⟩ = idx :=
        orderIsoOfFin_symm_orderEmbOfFin P rfl idx
      rw [h1]
      -- α idx = qIso.symm ⟨x, hx⟩ since idx = α.symm (qIso.symm ⟨x, hx⟩)
      have h2 : α idx = qIso.symm ⟨x, hx⟩ := by simp only [idx, Equiv.apply_symm_apply]
      rw [h2]
      -- Q.orderEmbOfFin _ (qIso.symm ⟨x, hx⟩) = x
      exact orderEmbOfFin_symm Q hcard.symm x hx

/-- The constructed permutation is in permsMapping P Q. -/
lemma constructSigma_mem_permsMapping {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (α : Equiv.Perm (Fin P.card)) (β : Equiv.Perm (Fin Pᶜ.card)) :
    constructSigma P Q hcard α β ∈ permsMapping P Q := by
  simp only [permsMapping, Finset.mem_filter, Finset.mem_univ, true_and]
  exact constructSigma_imageFinset P Q hcard α β

/-! ### Base case lemmas for sign decomposition using subtypePerm

When P = Q = {0, 1, ..., k-1} (the first k elements), the sign identity simplifies
because inversions split cleanly into three categories:
1. Inversions within P (counted by α)
2. Inversions within Pᶜ (counted by β)  
3. Inversions between P and Pᶜ (which are zero because σ preserves both sets)

We formalize this using Mathlib's `sign_subtypeCongr` lemma and `Equiv.Perm.subtypePerm`.
-/

/-- Predicate for "i.val < k" used to partition Fin n. -/
def ltPred (n k : ℕ) : Fin n → Prop := fun i => i.val < k

instance instDecidablePredLtPred (n k : ℕ) : DecidablePred (ltPred n k) := 
  fun i => Nat.decLt i.val k

/-- A permutation "preserves [k]" if it maps elements with index < k to elements with index < k. -/
def preservesPrefix {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  ∀ i : Fin n, i.val < k ↔ (σ i).val < k

/-- Restriction of a permutation to {i | i.val < k} using Mathlib's `subtypePerm`. -/
noncomputable def restrictToLt {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (hσ : preservesPrefix σ k) : Equiv.Perm {i : Fin n // ltPred n k i} :=
  σ.subtypePerm fun i => by
    simp only [ltPred]
    exact (hσ i).symm

/-- Restriction of a permutation to {i | i.val ≥ k} using Mathlib's `subtypePerm`. -/
noncomputable def restrictToGe {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (hσ : preservesPrefix σ k) : Equiv.Perm {i : Fin n // ¬ltPred n k i} :=
  σ.subtypePerm fun i => by
    simp only [ltPred, not_lt]
    constructor
    · intro h
      exact Nat.le_of_not_lt fun hc => Nat.not_lt.mpr h ((hσ i).mp hc)
    · intro h
      exact Nat.le_of_not_lt fun hc => Nat.not_lt.mpr h ((hσ i).mpr hc)

/-- A permutation that preserves [k] equals the subtypeCongr of its restrictions. -/
lemma eq_subtypeCongr_of_preservesPrefix {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (hσ : preservesPrefix σ k) :
    σ = (restrictToLt σ k hσ).subtypeCongr (restrictToGe σ k hσ) := by
  ext i
  by_cases h : ltPred n k i
  · simp only [Equiv.Perm.subtypeCongr.left_apply _ _ h, restrictToLt, 
               Equiv.Perm.subtypePerm_apply]
  · simp only [Equiv.Perm.subtypeCongr.right_apply _ _ h, restrictToGe, 
               Equiv.Perm.subtypePerm_apply]

/-- Base case: When σ preserves [k], sign(σ) = sign(α) * sign(β) where α, β are restrictions.
    This follows from Mathlib's `sign_subtypeCongr`. -/
theorem sign_split_preservesPrefix {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (hσ : preservesPrefix σ k) :
    Equiv.Perm.sign σ = 
      Equiv.Perm.sign (restrictToLt σ k hσ) * Equiv.Perm.sign (restrictToGe σ k hσ) := by
  have h := eq_subtypeCongr_of_preservesPrefix σ k hσ
  calc Equiv.Perm.sign σ 
      = Equiv.Perm.sign ((restrictToLt σ k hσ).subtypeCongr (restrictToGe σ k hσ)) := by rw [← h]
    _ = Equiv.Perm.sign (restrictToLt σ k hσ) * Equiv.Perm.sign (restrictToGe σ k hσ) := 
        Equiv.Perm.sign_subtypeCongr _ _

/-- The finset {0, 1, ..., k-1} ⊆ Fin n. -/
def prefixFinset (n k : ℕ) (_hk : k ≤ n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < k)

lemma mem_prefixFinset_iff {n k : ℕ} (hk : k ≤ n) (i : Fin n) :
    i ∈ prefixFinset n k hk ↔ i.val < k := by
  simp [prefixFinset]

lemma prefixFinset_card (n k : ℕ) (hk : k ≤ n) :
    (prefixFinset n k hk).card = k := by
  simp only [prefixFinset]
  rw [Finset.card_filter]
  conv_lhs => 
    arg 2
    ext i
    rw [show (if i.val < k then 1 else 0) = (if (i : Fin n).val < k then 1 else 0) from rfl]
  rw [← Finset.card_filter]
  have hbij : (Finset.univ.filter (fun i : Fin n => i.val < k)).card = 
              (Finset.range k).card := by
    refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact Finset.mem_range.mpr ha
    · intro a₁ a₂ ha₁ ha₂ h
      ext; exact h
    · intro b hb
      simp only [Finset.mem_range] at hb
      exact ⟨⟨b, by omega⟩, by simp [hb], rfl⟩
  rw [hbij, Finset.card_range]

/-- Sum of 0 + 1 + ... + (k-1) = k(k-1)/2 -/
lemma finsetSumFin_prefixFinset (n k : ℕ) (hk : k ≤ n) :
    finsetSumFin (prefixFinset n k hk) = k * (k - 1) / 2 := by
  simp only [finsetSumFin, prefixFinset]
  have h : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), i.val = 
           ∑ i ∈ Finset.range k, i := by
    refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact Finset.mem_range.mpr ha
    · intro a _ a' _ h
      ext; exact h
    · intro b hb
      simp only [Finset.mem_range] at hb
      exact ⟨⟨b, by omega⟩, by simp [hb], rfl⟩
    · intro a ha; rfl
  rw [h, Finset.sum_range_id]

/-- The j-th element of prefixFinset (in sorted order) is just j.
    This is because prefixFinset = {0, 1, ..., k-1} is already sorted. -/
lemma prefixFinset_orderEmbOfFin_eq {n k : ℕ} (hk : k ≤ n) (j : Fin k) :
    (prefixFinset n k hk).orderEmbOfFin (prefixFinset_card n k hk) j = ⟨j.val, by omega⟩ := by
  have h_range : ∀ j : Fin k, (⟨j.val, by omega⟩ : Fin n) ∈ prefixFinset n k hk := by
    intro j; simp [prefixFinset, j.isLt]
  have h_mono : StrictMono (fun j : Fin k => (⟨j.val, by omega⟩ : Fin n)) := by
    intro a b hab; simp only [Fin.lt_def]; exact hab
  have huniq := Finset.orderEmbOfFin_unique (prefixFinset_card n k hk) h_range h_mono
  exact (congrFun huniq j).symm

/-- The inverse of orderIsoOfFin for prefixFinset extracts the value.
    Since prefixFinset = {0, 1, ..., k-1}, the index of element x is just x.val. -/
lemma prefixFinset_orderIsoOfFin_symm {n k : ℕ} (hk : k ≤ n) 
    (x : prefixFinset n k hk) :
    ((prefixFinset n k hk).orderIsoOfFin (by rw [prefixFinset_card])).symm x = 
    ⟨x.val.val, by 
      have := x.prop
      simp only [prefixFinset, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this⟩ := by
  have h_range : ∀ j : Fin k, (⟨j.val, by omega⟩ : Fin n) ∈ prefixFinset n k hk := by
    intro j; simp [prefixFinset, j.isLt]
  have h_mono : StrictMono (fun j : Fin k => (⟨j.val, by omega⟩ : Fin n)) := by
    intro a b hab; simp only [Fin.lt_def]; exact hab
  have huniq := Finset.orderEmbOfFin_unique (prefixFinset_card n k hk) h_range h_mono
  apply ((prefixFinset n k hk).orderIsoOfFin (by rw [prefixFinset_card])).injective
  simp only [OrderIso.apply_symm_apply]
  ext
  have hx := x.prop
  simp only [prefixFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  have heq := congrFun huniq ⟨x.val.val, hx⟩
  simp only [Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin] at heq ⊢
  simp only [Fin.ext_iff] at heq
  exact heq

/-- The j-th element of prefixFinset^c (in sorted order) is k + j.
    Since prefixFinset^c = {k, k+1, ..., n-1}, the elements in sorted order are k, k+1, etc. -/
lemma prefixFinset_compl_orderEmbOfFin_eq {n k : ℕ} (hk : k ≤ n) (j : Fin (n - k)) :
    let P := prefixFinset n k hk
    let hcard : Pᶜ.card = n - k := by 
      rw [Finset.card_compl, Fintype.card_fin, prefixFinset_card]
    Pᶜ.orderEmbOfFin hcard j = ⟨k + j.val, by omega⟩ := by
  intro P hcard
  have h_range : ∀ j : Fin (n - k), (⟨k + j.val, by omega⟩ : Fin n) ∈ Pᶜ := by
    intro j
    simp only [P, prefixFinset, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    omega
  have h_mono : StrictMono (fun j : Fin (n - k) => (⟨k + j.val, by omega⟩ : Fin n)) := by
    intro a b hab
    simp only [Fin.lt_def]
    omega
  have huniq := Finset.orderEmbOfFin_unique hcard h_range h_mono
  rw [← huniq]

/-- The inverse of orderIsoOfFin for prefixFinset^c extracts the value minus k.
    Since prefixFinset^c = {k, k+1, ..., n-1}, the index of element x is x.val - k. -/
lemma prefixFinset_compl_orderIsoOfFin_symm {n k : ℕ} (hk : k ≤ n) 
    (x : ↑((prefixFinset n k hk)ᶜ)) :
    let P := prefixFinset n k hk
    let hcard : Pᶜ.card = n - k := by 
      rw [Finset.card_compl, Fintype.card_fin, prefixFinset_card]
    ((Pᶜ.orderIsoOfFin hcard).symm x).val = x.val.val - k := by
  intro P hcard
  have hx : x.val ∈ Pᶜ := x.prop
  simp only [P, prefixFinset, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
  -- Use that orderIsoOfFin is the inverse of orderEmbOfFin
  have h_emb := prefixFinset_compl_orderEmbOfFin_eq hk ⟨x.val.val - k, by omega⟩
  -- h_emb says: orderEmbOfFin ⟨x.val.val - k, _⟩ = ⟨k + (x.val.val - k), _⟩ = ⟨x.val.val, _⟩ = x.val
  have h_eq : Pᶜ.orderEmbOfFin hcard ⟨x.val.val - k, by omega⟩ = x.val := by
    simp only [Fin.ext_iff] at h_emb ⊢
    rw [h_emb]
    omega
  -- So orderIsoOfFin.symm x = ⟨x.val.val - k, _⟩
  have h_symm : (Pᶜ.orderIsoOfFin hcard).symm x = ⟨x.val.val - k, by omega⟩ := by
    apply (Pᶜ.orderIsoOfFin hcard).injective
    simp only [OrderIso.apply_symm_apply]
    -- Need: x = orderIsoOfFin ⟨x.val.val - k, _⟩
    -- orderIsoOfFin j has underlying value orderEmbOfFin j
    have h_coe : ((Pᶜ.orderIsoOfFin hcard) ⟨x.val.val - k, by omega⟩ : Fin n) = 
                 Pᶜ.orderEmbOfFin hcard ⟨x.val.val - k, by omega⟩ := by
      rw [Finset.coe_orderIsoOfFin_apply]
    ext
    rw [h_coe, h_eq]
  simp only [h_symm]

/-- When P = Q = prefixFinset n k hk, and σ(P) = Q, then σ preserves the prefix. -/
lemma preservesPrefix_of_imageFinset_prefix {n k : ℕ} (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ (prefixFinset n k hk) = prefixFinset n k hk) :
    preservesPrefix σ k := by
  intro i
  constructor
  · intro hi
    have hi_mem : i ∈ prefixFinset n k hk := by simp [prefixFinset, hi]
    have hσi_mem : σ i ∈ prefixFinset n k hk := by
      rw [← hσ]
      simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨i, hi_mem, rfl⟩
    simp only [prefixFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hσi_mem
    exact hσi_mem
  · intro hi
    have hσi_mem : σ i ∈ prefixFinset n k hk := by simp [prefixFinset, hi]
    rw [← hσ] at hσi_mem
    simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at hσi_mem
    obtain ⟨j, hj, hjσi⟩ := hσi_mem
    have : i = j := σ.injective hjσi.symm
    rw [this]
    simp only [prefixFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj

/-- A "left shift" replaces P with s_i(P) where i ∉ P and i+1 ∈ P.
    This decrements finsetSumFin P by 1. -/
lemma finsetSumFin_swap_of_left_shift {n : ℕ} (P : Finset (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
    (hi_notP : i ∉ P) (hiplus_P : (⟨i.val + 1, hi⟩ : Fin n) ∈ P) :
    finsetSumFin (imageFinset (Equiv.swap i ⟨i.val + 1, hi⟩) P) = finsetSumFin P - 1 := by
  simp only [finsetSumFin, imageFinset]
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have h_split : ∑ x ∈ P, (Equiv.swap i ⟨i.val + 1, hi⟩ x).val = 
                 ∑ x ∈ P \ {⟨i.val + 1, hi⟩}, x.val + i.val := by
    rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr hiplus_P)]
    simp only [Finset.sum_singleton]
    have h1 : Equiv.swap i ⟨i.val + 1, hi⟩ ⟨i.val + 1, hi⟩ = i := Equiv.swap_apply_right i _
    rw [h1]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
    have hx_ne_i : x ≠ i := fun h => hi_notP (h ▸ hx.1)
    have hx_ne_ip1 : x ≠ ⟨i.val + 1, hi⟩ := hx.2
    rw [Equiv.swap_apply_of_ne_of_ne hx_ne_i hx_ne_ip1]
  rw [h_split]
  have h_orig : ∑ x ∈ P, x.val = ∑ x ∈ P \ {⟨i.val + 1, hi⟩}, x.val + (i.val + 1) := by
    rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr hiplus_P)]
    simp only [Finset.sum_singleton]
  rw [h_orig]
  omega

/-- Key lemma: When σ(P) = Q and we multiply σ by a transposition, the sign flips. -/
lemma sign_mul_swap {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    Equiv.Perm.sign (σ * Equiv.swap i j) = -Equiv.Perm.sign σ := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  simp

/-- The sign of s_i · σ also flips -/
lemma sign_swap_mul {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    Equiv.Perm.sign (Equiv.swap i j * σ) = -Equiv.Perm.sign σ := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  simp

/-- Left shift preserves the combined sign factor.
    
    When we replace σ by σ * swap i (i+1) and P by (swap i (i+1))(P),
    the product (-1)^(finsetSumFin P + finsetSumFin Q) * sign(σ) is preserved,
    provided i ∉ P and i+1 ∈ P (so finsetSumFin decreases by 1).
    
    This is the key invariant for the shift reduction in the proof of sign_decomposition. -/
lemma leftShift_preserves_combined_sign {n : ℕ} 
    (P Q : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : imageFinset σ P = Q)
    (i : Fin n) (hi : i.val + 1 < n)
    (hi_notP : i ∉ P) (hiplus_P : (⟨i.val + 1, hi⟩ : Fin n) ∈ P) :
    let P' := imageFinset (Equiv.swap i ⟨i.val + 1, hi⟩) P
    let σ' := σ * Equiv.swap i ⟨i.val + 1, hi⟩
    let Q' := imageFinset σ' P'
    (-1 : ℤ) ^ (finsetSumFin P' + finsetSumFin Q') * (Equiv.Perm.sign σ' : ℤ) = 
    (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := by
  -- First show Q' = Q
  have hQ' : imageFinset (σ * Equiv.swap i ⟨i.val + 1, hi⟩) 
      (imageFinset (Equiv.swap i ⟨i.val + 1, hi⟩) P) = Q := by
    ext x
    simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk, Equiv.Perm.coe_mul, 
               Function.comp_apply]
    constructor
    · intro ⟨y, hy, hyx⟩
      obtain ⟨z, hz, hzy⟩ := hy
      rw [← hσ]
      simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
      use z
      constructor
      · exact hz
      · simp only [← hzy, ← hyx, Equiv.swap_apply_self]
    · intro hx
      rw [← hσ] at hx
      simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      use Equiv.swap i ⟨i.val + 1, hi⟩ z
      constructor
      · exact ⟨z, hz, rfl⟩
      · simp only [← hzx, Equiv.swap_apply_self]
  simp only [hQ']
  -- Now show finsetSumFin P' = finsetSumFin P - 1
  have hsum := finsetSumFin_swap_of_left_shift P i hi hi_notP hiplus_P
  -- Sign of σ' = -sign(σ)
  have hi_ne : i ≠ ⟨i.val + 1, hi⟩ := by simp [Fin.ext_iff]
  have hsign : (Equiv.Perm.sign (σ * Equiv.swap i ⟨i.val + 1, hi⟩) : ℤ) = 
               -(Equiv.Perm.sign σ : ℤ) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hi_ne]
    simp
  rw [hsum, hsign]
  -- Now: (-1)^((finsetSumFin P - 1) + finsetSumFin Q) * (-sign σ) = (-1)^(finsetSumFin P + finsetSumFin Q) * sign σ
  have hpos : finsetSumFin P ≥ 1 := by
    simp only [finsetSumFin]
    have h1 : ∑ x ∈ ({⟨i.val + 1, hi⟩} : Finset (Fin n)), (x : Fin n).val = i.val + 1 := by
      simp
    have h2 : ({⟨i.val + 1, hi⟩} : Finset (Fin n)) ⊆ P := by
      simp [hiplus_P]
    calc ∑ x ∈ P, x.val ≥ ∑ x ∈ ({⟨i.val + 1, hi⟩} : Finset (Fin n)), (x : Fin n).val := 
        Finset.sum_le_sum_of_subset h2
      _ = i.val + 1 := h1
      _ ≥ 1 := by omega
  -- (-1)^(k-1) * (-x) = (-1)^k * x when k ≥ 1
  have h_neg_one : (-1 : ℤ) ^ (finsetSumFin P - 1 + finsetSumFin Q) * (-(Equiv.Perm.sign σ : ℤ)) = 
                   (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := by
    have hge1 : finsetSumFin P + finsetSumFin Q ≥ 1 := by omega
    cases' Nat.exists_eq_succ_of_ne_zero (by omega : finsetSumFin P + finsetSumFin Q ≠ 0) with k hk
    have hk' : finsetSumFin P - 1 + finsetSumFin Q = k := by omega
    rw [hk, hk']
    simp only [pow_succ]
    ring
  exact h_neg_one

/-- Left co-shift preserves the combined sign factor.
    
    When we replace σ by (swap i (i+1)) * σ and Q by (swap i (i+1))(Q),
    the product (-1)^(finsetSumFin P + finsetSumFin Q) * sign(σ) is preserved,
    provided i ∉ Q and i+1 ∈ Q (so finsetSumFin Q decreases by 1).
    
    This is the key invariant for the co-shift reduction in the proof of sign_decomposition. -/
lemma leftCoShift_preserves_combined_sign {n : ℕ} 
    (P Q : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (_hσ : imageFinset σ P = Q)
    (i : Fin n) (hi : i.val + 1 < n)
    (hi_notQ : i ∉ Q) (hiplus_Q : (⟨i.val + 1, hi⟩ : Fin n) ∈ Q) :
    let Q' := imageFinset (Equiv.swap i ⟨i.val + 1, hi⟩) Q
    let σ' := Equiv.swap i ⟨i.val + 1, hi⟩ * σ
    (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q') * (Equiv.Perm.sign σ' : ℤ) = 
    (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := by
  intro Q' σ'
  -- Show finsetSumFin Q' = finsetSumFin Q - 1
  have hsum : finsetSumFin (imageFinset (Equiv.swap i ⟨i.val + 1, hi⟩) Q) = finsetSumFin Q - 1 := by
    simp only [finsetSumFin, imageFinset]
    rw [Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    have h_split : ∑ x ∈ Q, (Equiv.swap i ⟨i.val + 1, hi⟩ x).val = 
                   ∑ x ∈ Q \ {⟨i.val + 1, hi⟩}, x.val + i.val := by
      rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr hiplus_Q)]
      simp only [Finset.sum_singleton]
      have h1 : Equiv.swap i ⟨i.val + 1, hi⟩ ⟨i.val + 1, hi⟩ = i := Equiv.swap_apply_right i _
      rw [h1]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
      have hx_ne_i : x ≠ i := fun h => hi_notQ (h ▸ hx.1)
      have hx_ne_ip1 : x ≠ ⟨i.val + 1, hi⟩ := hx.2
      rw [Equiv.swap_apply_of_ne_of_ne hx_ne_i hx_ne_ip1]
    rw [h_split]
    have h_orig : ∑ x ∈ Q, x.val = ∑ x ∈ Q \ {⟨i.val + 1, hi⟩}, x.val + (i.val + 1) := by
      rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr hiplus_Q)]
      simp only [Finset.sum_singleton]
    rw [h_orig]
    omega
  -- Sign of σ' = -sign(σ)
  have hi_ne : i ≠ ⟨i.val + 1, hi⟩ := by simp [Fin.ext_iff]
  have hsign : (Equiv.Perm.sign (Equiv.swap i ⟨i.val + 1, hi⟩ * σ) : ℤ) = 
               -(Equiv.Perm.sign σ : ℤ) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hi_ne]
    simp
  rw [hsum, hsign]
  -- Now: (-1)^(finsetSumFin P + (finsetSumFin Q - 1)) * (-sign σ) = (-1)^(finsetSumFin P + finsetSumFin Q) * sign σ
  have hpos : finsetSumFin Q ≥ 1 := by
    simp only [finsetSumFin]
    have h1 : ∑ x ∈ ({⟨i.val + 1, hi⟩} : Finset (Fin n)), (x : Fin n).val = i.val + 1 := by
      simp
    have h2 : ({⟨i.val + 1, hi⟩} : Finset (Fin n)) ⊆ Q := by
      simp [hiplus_Q]
    calc ∑ x ∈ Q, x.val ≥ ∑ x ∈ ({⟨i.val + 1, hi⟩} : Finset (Fin n)), (x : Fin n).val := 
        Finset.sum_le_sum_of_subset h2
      _ = i.val + 1 := h1
      _ ≥ 1 := by omega
  -- (-1)^(k-1) * (-x) = (-1)^k * x when k ≥ 1
  have h_neg_one : (-1 : ℤ) ^ (finsetSumFin P + (finsetSumFin Q - 1)) * (-(Equiv.Perm.sign σ : ℤ)) = 
                   (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := by
    have hge1 : finsetSumFin P + finsetSumFin Q ≥ 1 := by omega
    cases' Nat.exists_eq_succ_of_ne_zero (by omega : finsetSumFin P + finsetSumFin Q ≠ 0) with k hk
    have hk' : finsetSumFin P + (finsetSumFin Q - 1) = k := by omega
    rw [hk, hk']
    simp only [pow_succ]
    ring
  exact h_neg_one

/-- k * (k - 1) is always even (consecutive integers). -/
lemma even_mul_pred (k : ℕ) : Even (k * (k - 1)) :=
  Nat.even_mul_pred_self k

/-- 2 divides k * (k - 1). -/
lemma two_dvd_mul_pred (k : ℕ) : 2 ∣ k * (k - 1) := Nat.two_dvd_mul_sub_one k

/-- Helper lemma: the index of orderEmbOfFin i in the sorted list is i.val. -/
lemma orderEmbOfFin_idxOf_eq {α : Type*} [LinearOrder α] (s : Finset α) {k : ℕ} (h : s.card = k) 
    (i : Fin k) : (s.sort (· ≤ ·)).idxOf (s.orderEmbOfFin h i) = i.val := by
  rw [Finset.orderEmbOfFin_apply]
  have h_nodup := s.sort_nodup (· ≤ ·)
  have h_len : i.val < (s.sort (· ≤ ·)).length := by rw [Finset.length_sort]; omega
  exact h_nodup.idxOf_getElem i.val h_len

/-- Key lemma for co-shifts: when we swap i and i+1 in Q (where i ∉ Q, i+1 ∈ Q),
    the swap preserves the sorted order within Q.
    
    More precisely: s(Q.orderEmbOfFin j) = Q'.orderEmbOfFin j where Q' = s(Q).
    This is because s swaps i and i+1, and i replaces i+1 at the same position in the sorted order. -/
lemma swap_preserves_position {n k : ℕ} (Q : Finset (Fin n)) (hQ_card : Q.card = k)
    (i : Fin n) (hi : i.val + 1 < n)
    (hi_notQ : i ∉ Q) (_hiplus_Q : (⟨i.val + 1, hi⟩ : Fin n) ∈ Q)
    (j : Fin k) :
    let s := Equiv.swap i ⟨i.val + 1, hi⟩
    let Q' := Q.map ⟨s, s.injective⟩
    let hQ'_card : Q'.card = k := by simp [Q', Finset.card_map, hQ_card]
    s (Q.orderEmbOfFin hQ_card j) = Q'.orderEmbOfFin hQ'_card j := by
  intro s Q' hQ'_card
  have h_mono : StrictMono (fun j : Fin k => s (Q.orderEmbOfFin hQ_card j)) := by
    intro a b hab
    have hlt : (Q.orderEmbOfFin hQ_card a) < (Q.orderEmbOfFin hQ_card b) := 
      (Q.orderEmbOfFin hQ_card).strictMono hab
    by_cases ha_eq : Q.orderEmbOfFin hQ_card a = ⟨i.val + 1, hi⟩
    · have hb_ne : Q.orderEmbOfFin hQ_card b ≠ ⟨i.val + 1, hi⟩ := by
        intro h; rw [ha_eq, h] at hlt; exact lt_irrefl _ hlt
      have hb_ne_i : Q.orderEmbOfFin hQ_card b ≠ i := by
        intro h
        have hqb_mem := Finset.orderEmbOfFin_mem Q hQ_card b
        rw [h] at hqb_mem
        exact hi_notQ hqb_mem
      simp only [s]
      rw [Equiv.swap_apply_of_ne_of_ne hb_ne_i hb_ne]
      rw [ha_eq, Equiv.swap_apply_right]
      calc i.val < i.val + 1 := by omega
        _ = (Q.orderEmbOfFin hQ_card a).val := by rw [ha_eq]
        _ < (Q.orderEmbOfFin hQ_card b).val := hlt
    · by_cases hb_eq : Q.orderEmbOfFin hQ_card b = ⟨i.val + 1, hi⟩
      · have ha_ne_i : Q.orderEmbOfFin hQ_card a ≠ i := by
          intro h
          have hqa_mem := Finset.orderEmbOfFin_mem Q hQ_card a
          rw [h] at hqa_mem
          exact hi_notQ hqa_mem
        simp only [s]
        rw [Equiv.swap_apply_of_ne_of_ne ha_ne_i ha_eq]
        rw [hb_eq, Equiv.swap_apply_right]
        have h1 : (Q.orderEmbOfFin hQ_card a).val < i.val + 1 := by 
          have := hlt; rw [hb_eq] at this; exact this
        have h2 : (Q.orderEmbOfFin hQ_card a).val ≠ i.val := by
          intro h; apply ha_ne_i; exact Fin.ext h
        have h3 : (Q.orderEmbOfFin hQ_card a).val < i.val := by omega
        exact h3
      · have ha_ne_i : Q.orderEmbOfFin hQ_card a ≠ i := by
          intro h
          have hqa_mem := Finset.orderEmbOfFin_mem Q hQ_card a
          rw [h] at hqa_mem
          exact hi_notQ hqa_mem
        have hb_ne_i : Q.orderEmbOfFin hQ_card b ≠ i := by
          intro h
          have hqb_mem := Finset.orderEmbOfFin_mem Q hQ_card b
          rw [h] at hqb_mem
          exact hi_notQ hqb_mem
        simp only [s]
        rw [Equiv.swap_apply_of_ne_of_ne ha_ne_i ha_eq]
        rw [Equiv.swap_apply_of_ne_of_ne hb_ne_i hb_eq]
        exact hlt
  have h_mem : ∀ j : Fin k, s (Q.orderEmbOfFin hQ_card j) ∈ Q' := by
    intro j
    simp only [Q', Finset.mem_map, Function.Embedding.coeFn_mk]
    exact ⟨Q.orderEmbOfFin hQ_card j, Finset.orderEmbOfFin_mem Q hQ_card j, rfl⟩
  have h_unique := Finset.orderEmbOfFin_unique hQ'_card h_mem h_mono
  exact congrFun h_unique j

/-- Positions are preserved under a permutation that preserves sorted order.
    If s(Q.orderEmbOfFin j) = Q'.orderEmbOfFin j for all j, then the position of s(x) in Q'
    equals the position of x in Q for all x ∈ Q. -/
lemma position_preserved_under_swap {n k : ℕ} (Q : Finset (Fin n)) (hQ_card : Q.card = k)
    (s : Equiv.Perm (Fin n))
    (Q' : Finset (Fin n)) (hQ'_card : Q'.card = k)
    (h_swap : ∀ j : Fin k, s (Q.orderEmbOfFin hQ_card j) = Q'.orderEmbOfFin hQ'_card j)
    (x : Fin n) (hx : x ∈ Q) (hsx : s x ∈ Q') :
    (Q'.orderIsoOfFin hQ'_card).symm ⟨s x, hsx⟩ = (Q.orderIsoOfFin hQ_card).symm ⟨x, hx⟩ := by
  -- Let j = position of x in Q
  let j := (Q.orderIsoOfFin hQ_card).symm ⟨x, hx⟩
  -- Then Q.orderEmbOfFin j = x (by definition of orderIsoOfFin)
  have hj : Q.orderEmbOfFin hQ_card j = x := by
    have h' := (Q.orderIsoOfFin hQ_card).apply_symm_apply ⟨x, hx⟩
    change ((Q.orderIsoOfFin hQ_card) j).val = x
    rw [h']
  -- By h_swap: s(Q.orderEmbOfFin j) = Q'.orderEmbOfFin j
  have h' := h_swap j
  -- So s(x) = Q'.orderEmbOfFin j
  rw [hj] at h'
  -- Therefore position of s(x) in Q' is j
  have h_pos : (Q'.orderIsoOfFin hQ'_card).symm ⟨s x, hsx⟩ = j := by
    have hmem : Q'.orderEmbOfFin hQ'_card j ∈ Q' := Finset.orderEmbOfFin_mem Q' hQ'_card j
    have h_eq : (⟨s x, hsx⟩ : Q') = ⟨Q'.orderEmbOfFin hQ'_card j, hmem⟩ := by
      simp only [Subtype.mk.injEq]
      exact h'
    rw [h_eq]
    exact orderIsoOfFin_symm_orderEmbOfFin Q' hQ'_card j
  exact h_pos

/-- Key lemma: extractAlpha values are equal under co-shift.
    If σ' = s * σ and Q' = s(Q), then extractAlpha P Q' σ' j = extractAlpha P Q σ j (as values). -/
lemma extractAlpha_val_eq_of_coshift {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q)
    (s : Equiv.Perm (Fin n))
    (Q' : Finset (Fin n)) (hQ'_card : Q'.card = Q.card)
    (hcard' : P.card = Q'.card)
    (σ' : Equiv.Perm (Fin n))
    (hσ' : imageFinset σ' P = Q')
    (h_σ'_eq : ∀ j : Fin P.card, σ' (P.orderEmbOfFin rfl j) = s (σ (P.orderEmbOfFin rfl j)))
    (h_swap : ∀ j : Fin Q.card, s (Q.orderEmbOfFin rfl j) = Q'.orderEmbOfFin hQ'_card j)
    (j : Fin P.card) :
    (extractAlpha P Q' hcard' σ' hσ' j).val = (extractAlpha P Q hcard σ hσ j).val := by
  simp only [extractAlpha, Equiv.ofBijective_apply]
  let pEmb := P.orderEmbOfFin rfl
  have hσPj_mem : σ (pEmb j) ∈ Q := sigma_orderEmb_mem_of_imageFinset P Q σ hσ j
  have hsσPj_mem : s (σ (pEmb j)) ∈ Q' := by
    have h := h_σ'_eq j
    rw [← h]
    exact sigma_orderEmb_mem_of_imageFinset P Q' σ' hσ' j
  have h_pos := position_preserved_under_swap Q rfl s Q' hQ'_card h_swap (σ (pEmb j)) hσPj_mem hsσPj_mem
  have h1 : σ' (pEmb j) = s (σ (pEmb j)) := h_σ'_eq j
  have hσ'Pj_mem : σ' (pEmb j) ∈ Q' := sigma_orderEmb_mem_of_imageFinset P Q' σ' hσ' j
  calc ((Q'.orderIsoOfFin hcard'.symm).symm ⟨σ' (pEmb j), _⟩).val
      = ((Q'.orderIsoOfFin hQ'_card).symm ⟨σ' (pEmb j), hσ'Pj_mem⟩).val := by rfl
    _ = ((Q'.orderIsoOfFin hQ'_card).symm ⟨s (σ (pEmb j)), hsσPj_mem⟩).val := by simp only [h1]
    _ = ((Q.orderIsoOfFin rfl).symm ⟨σ (pEmb j), hσPj_mem⟩).val := by rw [h_pos]
    _ = ((Q.orderIsoOfFin hcard.symm).symm ⟨σ (pEmb j), _⟩).val := by rfl

/-- When P = Q = prefixFinset n k hk, the sign factor (-1)^(sum P + sum Q) = 1.
    This is because sum P = sum Q = k(k-1)/2, so the exponent is k(k-1), which is even. -/
lemma neg_one_pow_double_sum_prefix (n k : ℕ) (hk : k ≤ n) :
    (-1 : ℤ) ^ (finsetSumFin (prefixFinset n k hk) + finsetSumFin (prefixFinset n k hk)) = 1 := by
  simp only [finsetSumFin_prefixFinset]
  have h : k * (k - 1) / 2 + k * (k - 1) / 2 = k * (k - 1) := by
    have hdiv := two_dvd_mul_pred k
    omega
  rw [h]
  exact Even.neg_one_pow (even_mul_pred k)

/-- Helper for orderEmbOfFin_val_ge: strong induction on m. -/
private lemma orderEmbOfFin_val_ge_aux {n k : ℕ} (P : Finset (Fin n)) (hcard : P.card = k) :
    ∀ m : ℕ, ∀ j : Fin k, j.val = m → m ≤ (P.orderEmbOfFin hcard j).val := by
  have hemb_mono : StrictMono (P.orderEmbOfFin hcard) := (P.orderEmbOfFin hcard).strictMono
  intro m
  induction m with
  | zero => 
    intro j hj
    exact Nat.zero_le _
  | succ m ih =>
    intro j hj
    have hm_lt : m < k := by omega
    let j' : Fin k := ⟨m, hm_lt⟩
    have hj'_lt_j : j' < j := by simp [Fin.lt_def, j', hj]
    have ih' : m ≤ (P.orderEmbOfFin hcard j').val := ih j' rfl
    have hlt : (P.orderEmbOfFin hcard j') < (P.orderEmbOfFin hcard j) := hemb_mono hj'_lt_j
    calc m + 1 
        ≤ (P.orderEmbOfFin hcard j').val + 1 := by omega
      _ ≤ (P.orderEmbOfFin hcard j).val := by omega

/-- The j-th element of a k-element subset (in sorted order) has value ≥ j.
    This is because if we list the elements as p₀ < p₁ < ... < p_{k-1},
    then pᵢ ≥ i for all i (since there are at least i elements below pᵢ). -/
lemma orderEmbOfFin_val_ge {n k : ℕ} (P : Finset (Fin n)) (hcard : P.card = k) (j : Fin k) :
    j.val ≤ (P.orderEmbOfFin hcard j).val := 
  orderEmbOfFin_val_ge_aux P hcard j.val j rfl

/-- Key lemma for the left shift induction: if P ≠ prefixFinset, 
    there exists i ∉ P with i+1 ∈ P. This allows us to apply a transposition
    to reduce finsetSumFin P while preserving the cardinality. -/
lemma exists_left_shift_witness {n k : ℕ} (hk : k ≤ n) (P : Finset (Fin n)) 
    (hcard : P.card = k) (hne : P ≠ prefixFinset n k hk) :
    ∃ i : Fin n, ∃ hi : i.val + 1 < n, i ∉ P ∧ (⟨i.val + 1, hi⟩ : Fin n) ∈ P := by
  -- P is a k-subset that's not {0, 1, ..., k-1}
  -- Since P ≠ prefixFinset and both have k elements, there's some element in P \ prefixFinset
  have hne' : ¬(P ⊆ prefixFinset n k hk) := by
    intro hsub
    have hcard' := Finset.card_le_card hsub
    rw [hcard, prefixFinset_card] at hcard'
    have hcard'' : (prefixFinset n k hk).card ≤ P.card := by rw [prefixFinset_card, hcard]
    exact hne (Finset.eq_of_subset_of_card_le hsub hcard'')
  -- So there's j ∈ P with j ≥ k
  rw [Finset.not_subset] at hne'
  obtain ⟨j, hjP, hjnotpre⟩ := hne'
  simp only [prefixFinset, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hjnotpre
  -- j ∈ P and j.val ≥ k
  -- Since P has exactly k elements and j.val ≥ k, 
  -- there must be some i < k with i ∉ P
  have hexists_not_in_P : ∃ i : Fin n, i.val < k ∧ i ∉ P := by
    by_contra h
    push Not at h
    -- h says: all i with i.val < k are in P
    have hsub : prefixFinset n k hk ⊆ P := by
      intro x hx
      simp only [prefixFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact h ⟨x.val, by omega⟩ hx
    have hcard' : P.card ≤ (prefixFinset n k hk).card := by rw [prefixFinset_card, hcard]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard'
    exact hne heq.symm
  obtain ⟨i₀, hi₀lt, hi₀notP⟩ := hexists_not_in_P
  -- Now we have: i₀ < k, i₀ ∉ P, j ≥ k, j ∈ P
  -- We need to find consecutive i, i+1 with i ∉ P and i+1 ∈ P
  -- Consider the set of indices m < j.val where ⟨m, _⟩ ∉ P
  -- This set is nonempty (contains i₀.val) and bounded above by j.val
  -- Take the maximum such m. Then m ∉ P and m+1 ∈ P.
  
  -- Define the set of "gaps" - indices before j that are not in P
  let gaps := (Finset.range j.val).filter (fun m => ∀ hm : m < n, (⟨m, hm⟩ : Fin n) ∉ P)
  have hgaps_nonempty : gaps.Nonempty := by
    use i₀.val
    simp only [gaps, Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · intro hm
      have : (⟨i₀.val, hm⟩ : Fin n) = i₀ := by ext; rfl
      rw [this]
      exact hi₀notP
  -- Let m be the maximum of gaps
  obtain ⟨m, hm_mem, hm_max⟩ := gaps.exists_max_image id hgaps_nonempty
  simp only [gaps, Finset.mem_filter, Finset.mem_range, id_eq] at hm_mem hm_max
  obtain ⟨hm_lt_j, hm_notP⟩ := hm_mem
  -- m < j.val < n, so m + 1 ≤ j.val < n
  have hm1_lt_n : m + 1 < n := by omega
  use ⟨m, by omega⟩, hm1_lt_n
  constructor
  · exact hm_notP (by omega)
  · -- Need to show ⟨m+1, hm1_lt_n⟩ ∈ P
    -- If m+1 ∉ P and m+1 < j.val, then m+1 ∈ gaps, contradicting maximality of m
    -- If m+1 = j.val, then ⟨m+1, _⟩ = j ∈ P
    by_cases hm1_eq_j : m + 1 = j.val
    · have : (⟨m + 1, hm1_lt_n⟩ : Fin n) = j := by ext; exact hm1_eq_j
      rw [this]
      exact hjP
    · -- m + 1 < j.val
      have hm1_lt_j : m + 1 < j.val := by omega
      by_contra hm1_notP
      have hm1_in_gaps : m + 1 < j.val ∧ ∀ (hm : m + 1 < n), (⟨m + 1, hm⟩ : Fin n) ∉ P := by
        constructor
        · exact hm1_lt_j
        · intro hm1
          have : (⟨m + 1, hm1⟩ : Fin n) = ⟨m + 1, hm1_lt_n⟩ := by ext; rfl
          rw [this]
          exact hm1_notP
      have := hm_max (m + 1) hm1_in_gaps
      omega

/-- The minimum sum for a k-element subset of Fin n is achieved by prefixFinset.
    This is because prefixFinset = {0, 1, ..., k-1} has sum 0+1+...+(k-1) = k(k-1)/2,
    and any other k-element subset must have at least one element ≥ k, giving a larger sum. -/
lemma finsetSumFin_ge_prefixFinset {n k : ℕ} (hk : k ≤ n) (P : Finset (Fin n)) (hcard : P.card = k) :
    finsetSumFin P ≥ finsetSumFin (prefixFinset n k hk) := by
  rw [finsetSumFin_prefixFinset]
  simp only [finsetSumFin]
  rw [← Finset.sum_range_id k]
  let emb := P.orderEmbOfFin hcard
  have h : ∑ i ∈ P, i.val = ∑ j : Fin k, (emb j).val := by
    rw [← Finset.sum_coe_sort P (fun i => i.val)]
    apply Fintype.sum_equiv (P.orderIsoOfFin hcard).symm.toEquiv
    intro j
    simp [emb, Finset.orderEmbOfFin]
  rw [h]
  -- Convert range sum to Fin k sum
  have hrange : ∑ i ∈ Finset.range k, i = ∑ j : Fin k, j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j => j) k]
  rw [hrange]
  -- Now show ∑ j : Fin k, (emb j).val ≥ ∑ j : Fin k, j.val
  apply Finset.sum_le_sum
  intro j _
  exact orderEmbOfFin_val_ge P hcard j

/-- Helper: downward closure of a finset with no shift opportunities.
    If there's no i with i ∉ P and i+1 ∈ P, then P is "downward closed":
    for any j ∈ P and i < j, we have i ∈ P. -/
private lemma downward_closure_aux {n : ℕ} (P : Finset (Fin n))
    (h_no_shift : ∀ (i : Fin n) (hi : i.val + 1 < n), i ∉ P → (⟨i.val + 1, hi⟩ : Fin n) ∉ P)
    (j : Fin n) (hj : j ∈ P) (i : Fin n) (hij : i.val < j.val) : i ∈ P := by
  have hdist : j.val - i.val > 0 := by omega
  obtain ⟨d, hd⟩ : ∃ d, j.val - i.val = d + 1 := ⟨j.val - i.val - 1, by omega⟩
  clear hdist
  induction d using Nat.strongRecOn generalizing j with
  | ind d ih =>
    by_cases hadj : d = 0
    · have hj_eq : j.val = i.val + 1 := by omega
      have hi_lt : i.val + 1 < n := by omega
      have := h_no_shift i hi_lt
      by_contra hi_not
      have hj_not : (⟨i.val + 1, hi_lt⟩ : Fin n) ∉ P := this hi_not
      have heq : j = ⟨i.val + 1, hi_lt⟩ := Fin.ext hj_eq
      rw [heq] at hj
      exact hj_not hj
    · have hgap : j.val > i.val + 1 := by omega
      have hj'_lt : j.val - 1 < n := by omega
      let j' : Fin n := ⟨j.val - 1, hj'_lt⟩
      have hj'_in : j' ∈ P := by
        have hj'_plus_lt : j'.val + 1 < n := by simp [j']; omega
        have := h_no_shift j' hj'_plus_lt
        by_contra hj'_not
        have h_not : (⟨j'.val + 1, hj'_plus_lt⟩ : Fin n) ∉ P := this hj'_not
        have heq : (⟨j'.val + 1, hj'_plus_lt⟩ : Fin n) = j := by
          simp only [Fin.ext_iff, j']
          omega
        rw [heq] at h_not
        exact h_not hj
      have hi_lt_j' : i.val < j'.val := by simp [j']; omega
      have hd' : j'.val - i.val = d - 1 + 1 := by simp [j']; omega
      exact ih (d - 1) (by omega) j' hj'_in hi_lt_j' hd'

/-- If P has card k and P ≠ prefixFinset, then there's a shift opportunity:
    some i with i ∉ P and i+1 ∈ P. This is because P has a "gap" that can be shifted. -/
lemma exists_shift_opportunity {n k : ℕ} (hk : k ≤ n) (hk_pos : 0 < k) (_hn : k < n) 
    (P : Finset (Fin n)) 
    (hcard : P.card = k) (hne : P ≠ prefixFinset n k hk) :
    ∃ (i : Fin n) (hi : i.val + 1 < n), i ∉ P ∧ (⟨i.val + 1, hi⟩ : Fin n) ∈ P := by
  by_contra h_no_shift
  push Not at h_no_shift
  
  have h_downward := downward_closure_aux P h_no_shift
  
  apply hne
  ext x
  rw [mem_prefixFinset_iff]
  constructor
  · intro hx
    by_contra hxge
    push Not at hxge
    have hx1_le : x.val + 1 ≤ n := x.isLt
    have h_subset : prefixFinset n (x.val + 1) hx1_le ⊆ P := by
      intro y hy
      rw [mem_prefixFinset_iff] at hy
      by_cases hyx : y = x
      · rw [hyx]; exact hx
      · have hyx' : y.val < x.val := by
          cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hy) with
          | inl h => exact h
          | inr h => exfalso; apply hyx; exact Fin.ext h
        exact h_downward x hx y hyx'
    have hcard' := Finset.card_le_card h_subset
    rw [prefixFinset_card n (x.val + 1) hx1_le, hcard] at hcard'
    omega
  · intro hxlt
    have hP_nonempty : P.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty] at hcard
      simp at hcard
      omega
    obtain ⟨m, hm, hm_max⟩ := P.exists_max_image (fun i => i.val) hP_nonempty
    have hm1_le : m.val + 1 ≤ n := m.isLt
    have h_prefix_sub : prefixFinset n (m.val + 1) hm1_le ⊆ P := by
      intro y hy
      rw [mem_prefixFinset_iff] at hy
      by_cases hym : y = m
      · rw [hym]; exact hm
      · have hym' : y.val < m.val := by
          cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hy) with
          | inl h => exact h
          | inr h => exfalso; apply hym; exact Fin.ext h
        exact h_downward m hm y hym'
    have hcard_ge : P.card ≥ m.val + 1 := by
      calc P.card ≥ (prefixFinset n (m.val + 1) _).card := Finset.card_le_card h_prefix_sub
        _ = m.val + 1 := prefixFinset_card n (m.val + 1) hm1_le
    have hP_sub_prefix : P ⊆ prefixFinset n (m.val + 1) hm1_le := by
      intro y hy
      rw [mem_prefixFinset_iff]
      have := hm_max y hy
      omega
    have hP_eq : P = prefixFinset n (m.val + 1) hm1_le := 
      Finset.Subset.antisymm hP_sub_prefix h_prefix_sub
    have hm_eq : m.val + 1 = k := by
      rw [hP_eq, prefixFinset_card n (m.val + 1) hm1_le] at hcard
      exact hcard
    have hxm : x.val ≤ m.val := by omega
    by_cases hxm' : x = m
    · rw [hxm']; exact hm
    · have hxm'' : x.val < m.val := by
        cases Nat.lt_or_eq_of_le hxm with
        | inl h => exact h
        | inr h => exfalso; apply hxm'; exact Fin.ext h
      exact h_downward m hm x hxm''

/-- When P = Q = prefixFinset, extractAlpha(j).val = (σ(orderEmbOfFin j)).val.
    This shows that extractAlpha just extracts the value of σ on the prefix. -/
lemma extractAlpha_prefixFinset_val {n k : ℕ} (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ (prefixFinset n k hk) = prefixFinset n k hk)
    (j : Fin (prefixFinset n k hk).card) :
    (extractAlpha (prefixFinset n k hk) (prefixFinset n k hk) rfl σ hσ j).val = 
    (σ ((prefixFinset n k hk).orderEmbOfFin rfl j)).val := by
  let P := prefixFinset n k hk
  simp only [extractAlpha, Equiv.ofBijective_apply]
  have hσj_mem : σ (P.orderEmbOfFin rfl j) ∈ P := by
    have hmem : P.orderEmbOfFin rfl j ∈ P := Finset.orderEmbOfFin_mem P rfl j
    have h1 : σ (P.orderEmbOfFin rfl j) ∈ imageFinset σ P := by
      simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨P.orderEmbOfFin rfl j, hmem, rfl⟩
    rw [hσ] at h1
    exact h1
  have h := prefixFinset_orderIsoOfFin_symm hk ⟨σ (P.orderEmbOfFin rfl j), hσj_mem⟩
  simp only [Fin.ext_iff] at h
  convert h using 1; rfl

/-- For prefixFinset^c, extractBeta j gives the position of σ(Pᶜ.orderEmbOfFin j) in Pᶜ.
    Since Pᶜ = {k, ..., n-1}, this equals (σ(k+j)).val - k. -/
lemma extractBeta_prefixFinset_val {n k : ℕ} (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ (prefixFinset n k hk) = prefixFinset n k hk)
    (j : Fin (prefixFinset n k hk)ᶜ.card) :
    (extractBeta (prefixFinset n k hk) (prefixFinset n k hk) rfl σ hσ j).val = 
    (σ ((prefixFinset n k hk)ᶜ.orderEmbOfFin rfl j)).val - k := by
  let P := prefixFinset n k hk
  simp only [extractBeta, Equiv.ofBijective_apply]
  -- σ maps Pᶜ to Pᶜ (since σ(P) = P)
  have hσj_mem : σ (Pᶜ.orderEmbOfFin rfl j) ∈ Pᶜ := sigma_orderEmb_compl_mem_of_imageFinset P P σ hσ j
  have h := prefixFinset_compl_orderIsoOfFin_symm hk ⟨σ (Pᶜ.orderEmbOfFin rfl j), hσj_mem⟩
  simp only [P] at h
  convert h using 1; rfl

/-- Equivalence between Fin k and the subtype {i : Fin n // i.val < k}. -/
noncomputable def finEquivSubtypeLt (n k : ℕ) (hk : k ≤ n) : 
    Fin k ≃ {i : Fin n // ltPred n k i} := by
  refine ⟨fun j => ⟨⟨j.val, by omega⟩, j.isLt⟩, 
         fun x => ⟨x.val.val, x.prop⟩, ?_, ?_⟩
  · intro j; rfl
  · intro x; rfl

/-- Equivalence between Fin (n-k) and the subtype {i : Fin n // ¬(i.val < k)}. -/
noncomputable def finEquivSubtypeGe (n k : ℕ) (hk : k ≤ n) : 
    Fin (n - k) ≃ {i : Fin n // ¬ltPred n k i} := by
  refine ⟨fun j => ⟨⟨j.val + k, ?_⟩, ?_⟩, 
         fun x => ⟨x.val.val - k, ?_⟩, ?_, ?_⟩
  · have hj := j.isLt; omega
  · have hj := j.isLt; simp only [ltPred, not_lt]; omega
  · have hx := x.prop
    have hxlt := x.val.isLt
    simp only [ltPred] at hx
    push Not at hx
    omega
  · intro j
    simp only [Fin.ext_iff]
    have hj := j.isLt
    have : j.val + k - k = j.val := Nat.add_sub_cancel j.val k
    exact this
  · intro x
    simp only [Subtype.ext_iff, Fin.ext_iff]
    have hx := x.prop
    simp only [ltPred] at hx
    push Not at hx
    have : x.val.val - k + k = x.val.val := Nat.sub_add_cancel hx
    exact this

/-- Convert restrictToLt to a permutation on Fin k using finEquivSubtypeLt. -/
noncomputable def restrictToLtAsFink {n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin n)) 
    (hσ : preservesPrefix σ k) : Equiv.Perm (Fin k) :=
  (finEquivSubtypeLt n k hk).symm.permCongr (restrictToLt σ k hσ)

/-- Convert restrictToGe to a permutation on Fin (n-k) using finEquivSubtypeGe. -/
noncomputable def restrictToGeAsFinNK {n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin n)) 
    (hσ : preservesPrefix σ k) : Equiv.Perm (Fin (n - k)) :=
  (finEquivSubtypeGe n k hk).symm.permCongr (restrictToGe σ k hσ)

/-- Sign of restrictToLt equals sign of restrictToLtAsFink by sign_permCongr. -/
lemma sign_restrictToLt_eq_sign_restrictToLtAsFink {n k : ℕ} (hk : k ≤ n) 
    (σ : Equiv.Perm (Fin n)) (hσ : preservesPrefix σ k) :
    Equiv.Perm.sign (restrictToLt σ k hσ) = Equiv.Perm.sign (restrictToLtAsFink hk σ hσ) := by
  simp only [restrictToLtAsFink]
  exact (Equiv.Perm.sign_permCongr _ _).symm

/-- Sign of restrictToGe equals sign of restrictToGeAsFinNK by sign_permCongr. -/
lemma sign_restrictToGe_eq_sign_restrictToGeAsFinNK {n k : ℕ} (hk : k ≤ n) 
    (σ : Equiv.Perm (Fin n)) (hσ : preservesPrefix σ k) :
    Equiv.Perm.sign (restrictToGe σ k hσ) = Equiv.Perm.sign (restrictToGeAsFinNK hk σ hσ) := by
  simp only [restrictToGeAsFinNK]
  exact (Equiv.Perm.sign_permCongr _ _).symm

/-- Auxiliary lemma: casting extractAlpha and applying to j gives the same value as
    applying extractAlpha to the corresponding element. -/
lemma extractAlpha_cast_apply_val {n : ℕ} (P : Finset (Fin n)) (k : ℕ) (hcard : P.card = k)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = P) (j : Fin k) :
    ((hcard ▸ extractAlpha P P rfl σ hσ) j).val = 
    (extractAlpha P P rfl σ hσ ⟨j.val, by omega⟩).val := by
  rcases hcard with rfl
  rfl

lemma extractBeta_cast_apply_val {n : ℕ} (P : Finset (Fin n)) (m : ℕ) (hcard : Pᶜ.card = m)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = P) (j : Fin m) :
    ((hcard ▸ extractBeta P P rfl σ hσ) j).val = 
    (extractBeta P P rfl σ hσ ⟨j.val, by omega⟩).val := by
  rcases hcard with rfl
  rfl

/-- At the base case (P = Q = prefixFinset), extractAlpha equals restrictToLtAsFink.
    This is because both permutations act the same way: for j : Fin k,
    - extractAlpha j = position of σ(j) in prefixFinset = (σ ⟨j, _⟩).val
    - restrictToLtAsFink j = (σ ⟨j, _⟩).val -/
lemma extractAlpha_eq_restrictToLtAsFink_at_prefix {n k : ℕ} (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) 
    (hσ : imageFinset σ (prefixFinset n k hk) = prefixFinset n k hk)
    (hpres : preservesPrefix σ k) :
    let P := prefixFinset n k hk
    let hcard_eq : P.card = k := prefixFinset_card n k hk
    (hcard_eq ▸ extractAlpha P P rfl σ hσ : Equiv.Perm (Fin k)) = restrictToLtAsFink hk σ hpres := by
  intro P hcard_eq
  apply Equiv.ext
  intro j
  apply Fin.ext
  -- LHS value using the auxiliary lemma
  rw [extractAlpha_cast_apply_val P k hcard_eq σ hσ j]
  -- Now use extractAlpha_prefixFinset_val
  have hj_lt_P : j.val < P.card := by rw [hcard_eq]; exact j.isLt
  have h_extract := extractAlpha_prefixFinset_val hk σ hσ ⟨j.val, hj_lt_P⟩
  -- Show the arguments are the same
  have h_arg : (⟨j.val, by omega⟩ : Fin P.card) = ⟨j.val, hj_lt_P⟩ := rfl
  rw [h_arg, h_extract]
  -- RHS value
  have h_rhs : (restrictToLtAsFink hk σ hpres j).val = (σ ⟨j.val, by omega⟩).val := by
    simp only [restrictToLtAsFink, Equiv.permCongr_apply, finEquivSubtypeLt,
               restrictToLt, Equiv.Perm.subtypePerm_apply]
    rfl
  rw [h_rhs]
  -- Now need: (σ (P.orderEmbOfFin rfl ⟨j.val, hj_lt_P⟩)).val = (σ ⟨j.val, _⟩).val
  -- This follows from P.orderEmbOfFin rfl ⟨j.val, _⟩ = ⟨j.val, _⟩
  have h_emb := prefixFinset_orderEmbOfFin_eq hk ⟨j.val, j.isLt⟩
  -- Need to connect orderEmbOfFin rfl to orderEmbOfFin (prefixFinset_card n k hk)
  have h_eq : (prefixFinset n k hk).orderEmbOfFin rfl ⟨j.val, hj_lt_P⟩ = 
              (prefixFinset n k hk).orderEmbOfFin (prefixFinset_card n k hk) ⟨j.val, j.isLt⟩ := by
    simp only [Finset.orderEmbOfFin]
    rfl
  rw [h_eq, h_emb]

/-- At the base case (P = Q = prefixFinset), extractBeta equals restrictToGeAsFinNK.
    Similar to extractAlpha_eq_restrictToLtAsFink_at_prefix but for the complement. -/
lemma extractBeta_eq_restrictToGeAsFinNK_at_prefix {n k : ℕ} (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) 
    (hσ : imageFinset σ (prefixFinset n k hk) = prefixFinset n k hk)
    (hpres : preservesPrefix σ k) :
    let P := prefixFinset n k hk
    let hcard_compl : Pᶜ.card = n - k := by 
      rw [Finset.card_compl, Fintype.card_fin, prefixFinset_card]
    (hcard_compl ▸ extractBeta P P rfl σ hσ : Equiv.Perm (Fin (n - k))) = 
      restrictToGeAsFinNK hk σ hpres := by
  intro P hcard_compl
  apply Equiv.ext
  intro j
  apply Fin.ext
  -- LHS value using the auxiliary lemma
  rw [extractBeta_cast_apply_val P (n - k) hcard_compl σ hσ j]
  -- Now use extractBeta_prefixFinset_val
  have hj_lt_Pc : j.val < Pᶜ.card := by rw [hcard_compl]; exact j.isLt
  have h_extract := extractBeta_prefixFinset_val hk σ hσ ⟨j.val, hj_lt_Pc⟩
  -- Show the arguments are the same
  have h_arg : (⟨j.val, by omega⟩ : Fin Pᶜ.card) = ⟨j.val, hj_lt_Pc⟩ := rfl
  rw [h_arg, h_extract]
  -- RHS value: restrictToGeAsFinNK j = (σ ⟨j + k, _⟩).val - k
  have h_rhs : (restrictToGeAsFinNK hk σ hpres j).val = (σ ⟨j.val + k, by omega⟩).val - k := by
    simp only [restrictToGeAsFinNK, Equiv.permCongr_apply, finEquivSubtypeGe,
               restrictToGe, Equiv.Perm.subtypePerm_apply]
    rfl
  rw [h_rhs]
  -- Now need: (σ (Pᶜ.orderEmbOfFin rfl ⟨j.val, hj_lt_Pc⟩)).val - k = (σ ⟨j.val + k, _⟩).val - k
  -- This follows from Pᶜ.orderEmbOfFin rfl ⟨j.val, _⟩ = ⟨k + j.val, _⟩
  have h_emb := prefixFinset_compl_orderEmbOfFin_eq hk ⟨j.val, j.isLt⟩
  -- Need to connect orderEmbOfFin rfl to orderEmbOfFin hcard_compl
  have h_eq : (prefixFinset n k hk)ᶜ.orderEmbOfFin rfl ⟨j.val, hj_lt_Pc⟩ = 
              (prefixFinset n k hk)ᶜ.orderEmbOfFin hcard_compl ⟨j.val, j.isLt⟩ := by
    simp only [Finset.orderEmbOfFin]
    rfl
  rw [h_eq]
  -- h_emb says: orderEmbOfFin ⟨j.val, _⟩ = ⟨k + j.val, _⟩
  simp only [Fin.ext_iff] at h_emb
  -- Need to show: (σ (orderEmbOfFin hcard_compl ⟨j.val, j.isLt⟩)).val = (σ ⟨j.val + k, _⟩).val
  -- First connect orderEmbOfFin hcard_compl to h_emb
  have h_emb' : ((prefixFinset n k hk)ᶜ.orderEmbOfFin hcard_compl ⟨j.val, j.isLt⟩).val = k + j.val := by
    have h2 := prefixFinset_compl_orderEmbOfFin_eq hk ⟨j.val, j.isLt⟩
    simp only [Fin.ext_iff] at h2
    convert h2 using 2
  have h_fin_eq : (prefixFinset n k hk)ᶜ.orderEmbOfFin hcard_compl ⟨j.val, j.isLt⟩ = 
                  ⟨j.val + k, by omega⟩ := by
    ext
    rw [h_emb']
    ring
  rw [h_fin_eq]

/-- Helper lemma: sign is preserved under casting between Fin types. -/
lemma sign_eq_of_cast_eq {m n : ℕ} (h : m = n) (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin n))
    (heq : (h ▸ α) = β) : Equiv.Perm.sign α = Equiv.Perm.sign β := by
  subst heq
  cases h
  rfl

/-- Base case of sign_decomposition: when P = Q = prefixFinset n k hk. -/
lemma sign_decomposition_prefix {n k : ℕ} (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) 
    (hσ : imageFinset σ (prefixFinset n k hk) = prefixFinset n k hk) :
    let P := prefixFinset n k hk
    (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin P) * 
      (Equiv.Perm.sign (extractAlpha P P rfl σ hσ) : ℤ) * 
      (Equiv.Perm.sign (extractBeta P P rfl σ hσ) : ℤ) := by
  intro P
  -- First, (-1)^(sum P + sum P) = 1 by neg_one_pow_double_sum_prefix
  have h_neg_one : (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin P) = 1 := 
    neg_one_pow_double_sum_prefix n k hk
  rw [h_neg_one, one_mul]
  -- Now we need: sign(σ) = sign(extractAlpha) * sign(extractBeta)
  -- By sign_split_preservesPrefix, sign(σ) = sign(restrictToLt) * sign(restrictToGe)
  have hpres := preservesPrefix_of_imageFinset_prefix hk σ hσ
  have hsplit := sign_split_preservesPrefix σ k hpres
  -- Convert to ℤ
  have hsplit' : (Equiv.Perm.sign σ : ℤ) = 
      (Equiv.Perm.sign (restrictToLt σ k hpres) : ℤ) * 
      (Equiv.Perm.sign (restrictToGe σ k hpres) : ℤ) := by
    norm_cast
  rw [hsplit']
  -- Now use the equivalences: sign(restrictToLt) = sign(restrictToLtAsFink) = sign(extractAlpha)
  -- and sign(restrictToGe) = sign(restrictToGeAsFinNK) = sign(extractBeta)
  have h_alpha := extractAlpha_eq_restrictToLtAsFink_at_prefix hk σ hσ hpres
  have h_beta := extractBeta_eq_restrictToGeAsFinNK_at_prefix hk σ hσ hpres
  -- Get the cardinality facts
  have hcard_eq : P.card = k := prefixFinset_card n k hk
  have hcard_compl : Pᶜ.card = n - k := by 
    rw [Finset.card_compl, Fintype.card_fin, prefixFinset_card]
  -- sign(restrictToLt) = sign(restrictToLtAsFink) by sign_restrictToLt_eq_sign_restrictToLtAsFink
  have h_sign_lt := sign_restrictToLt_eq_sign_restrictToLtAsFink hk σ hpres
  -- sign(restrictToGe) = sign(restrictToGeAsFinNK) by sign_restrictToGe_eq_sign_restrictToGeAsFinNK
  have h_sign_ge := sign_restrictToGe_eq_sign_restrictToGeAsFinNK hk σ hpres
  -- sign(extractAlpha) = sign(restrictToLtAsFink) by h_alpha and sign_eq_of_cast_eq
  have h1 : Equiv.Perm.sign (extractAlpha P P rfl σ hσ) = 
            Equiv.Perm.sign (restrictToLtAsFink hk σ hpres) := 
    sign_eq_of_cast_eq hcard_eq (extractAlpha P P rfl σ hσ) (restrictToLtAsFink hk σ hpres) h_alpha
  -- sign(extractBeta) = sign(restrictToGeAsFinNK) by h_beta and sign_eq_of_cast_eq
  have h2 : Equiv.Perm.sign (extractBeta P P rfl σ hσ) = 
            Equiv.Perm.sign (restrictToGeAsFinNK hk σ hpres) := 
    sign_eq_of_cast_eq hcard_compl (extractBeta P P rfl σ hσ) (restrictToGeAsFinNK hk σ hpres) h_beta
  -- Combine: sign(restrictToLt) * sign(restrictToGe) = sign(extractAlpha) * sign(extractBeta)
  simp only [h_sign_lt, h_sign_ge, h1, h2]

/-- Key lemma: After a left shift, Q' = Q (the image is preserved).
    
    When we apply swap(i, i+1) to P (where i ∉ P, i+1 ∈ P) and compose σ with swap,
    the image σ'(P') equals the original image Q.
    
    This is because:
    - For p ∈ P with p ≠ i+1: swap(p) = p, so σ'(swap(p)) = σ(swap(swap(p))) = σ(p)
    - For p = i+1: swap(i+1) = i, so σ'(i) = σ(swap(i)) = σ(i+1)
    
    Thus the multiset of images is unchanged. -/
lemma imageFinset_leftShift_eq {n : ℕ} (P Q : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : imageFinset σ P = Q)
    (i : Fin n) (hi : i.val + 1 < n)
    (_hi_notP : i ∉ P) (_hiplus_P : (⟨i.val + 1, hi⟩ : Fin n) ∈ P) :
    let s := Equiv.swap i ⟨i.val + 1, hi⟩
    let P' := imageFinset s P
    let σ' := σ * s
    imageFinset σ' P' = Q := by
  intro s P' σ'
  ext x
  constructor
  · intro hx
    simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [P', imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [← hσ]
    simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
    use z
    constructor
    · exact hz
    · -- Need: σ z = x
      -- We have: hyx : σ' y = x, i.e., σ (s y) = x
      -- We have: hzy : s z = y
      -- So σ (s (s z)) = σ (s y) = x
      -- But s (s z) = z since s is an involution
      simp only [σ', Equiv.Perm.coe_mul, Function.comp_apply] at hyx
      rw [← hzy] at hyx
      have h_inv : s (s z) = z := Equiv.swap_apply_self i ⟨i.val + 1, hi⟩ z
      rw [h_inv] at hyx
      exact hyx
  · intro hx
    rw [← hσ] at hx
    simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
    use s z
    constructor
    · simp only [P', imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨z, hz, rfl⟩
    · -- Need: σ' (s z) = x
      -- We have: hzx : σ z = x
      -- σ' (s z) = σ (s (s z)) = σ z = x
      simp only [σ', Equiv.Perm.coe_mul, Function.comp_apply]
      have h_inv : s (s z) = z := Equiv.swap_apply_self i ⟨i.val + 1, hi⟩ z
      rw [h_inv, hzx]

/-- Helper lemma for casting permutations: the value of a cast permutation applied to j
    equals the original permutation applied to the corresponding element. -/
lemma perm_cast_apply_val {m n : ℕ} (h : m = n) (α : Equiv.Perm (Fin m)) (j : Fin n) :
    ((h ▸ α) j).val = (α ⟨j.val, h ▸ j.isLt⟩).val := by
  cases h
  rfl

/-- Key lemma: when P' = s(P) for a swap s = swap(i, i+1) with i ∉ P and i+1 ∈ P,
    the sorted order of P' is s applied to the sorted order of P.
    
    This is because s swaps adjacent elements i < i+1, and since i ∉ P but i+1 ∈ P,
    replacing i+1 with i preserves the relative order of all elements. -/
lemma swap_orderEmbOfFin_eq {n : ℕ} (P : Finset (Fin n)) (i : Fin n) (hi : i.val + 1 < n)
    (hi_notP : i ∉ P) (_hiplus_P : (⟨i.val + 1, hi⟩ : Fin n) ∈ P) :
    let s := Equiv.swap i ⟨i.val + 1, hi⟩
    let P' := P.map ⟨s, s.injective⟩
    ∀ j : Fin P.card, P'.orderEmbOfFin (Finset.card_map _) j = s (P.orderEmbOfFin rfl j) := by
  intro s P' j
  have h_strict : StrictMono (fun j => s (P.orderEmbOfFin rfl j)) := by
    intro a b hab
    have ha := P.orderEmbOfFin_mem rfl a
    have hb := P.orderEmbOfFin_mem rfl b
    have h_lt := (P.orderEmbOfFin rfl).strictMono hab
    by_cases ha_eq : P.orderEmbOfFin rfl a = ⟨i.val + 1, hi⟩
    · simp only [s, ha_eq, Equiv.swap_apply_right]
      by_cases hb_eq : P.orderEmbOfFin rfl b = ⟨i.val + 1, hi⟩
      · rw [ha_eq, hb_eq] at h_lt
        exact absurd h_lt (lt_irrefl _)
      · have hb_ne_i : P.orderEmbOfFin rfl b ≠ i := by
          intro heq; rw [heq] at hb; exact hi_notP hb
        simp only [Equiv.swap_apply_of_ne_of_ne hb_ne_i hb_eq]
        have : (⟨i.val + 1, hi⟩ : Fin n) < P.orderEmbOfFin rfl b := by rw [← ha_eq]; exact h_lt
        calc i < ⟨i.val + 1, hi⟩ := by simp [Fin.lt_def]
             _ < P.orderEmbOfFin rfl b := this
    · have ha_ne_i : P.orderEmbOfFin rfl a ≠ i := by
        intro heq; rw [heq] at ha; exact hi_notP ha
      simp only [s, Equiv.swap_apply_of_ne_of_ne ha_ne_i ha_eq]
      by_cases hb_eq : P.orderEmbOfFin rfl b = ⟨i.val + 1, hi⟩
      · simp only [hb_eq, Equiv.swap_apply_right]
        have h_lt' : P.orderEmbOfFin rfl a < ⟨i.val + 1, hi⟩ := by rw [← hb_eq]; exact h_lt
        have hval_lt : (P.orderEmbOfFin rfl a).val < i.val + 1 := Fin.lt_def.mp h_lt'
        have h_lt_or_eq : (P.orderEmbOfFin rfl a).val < i.val ∨ (P.orderEmbOfFin rfl a).val = i.val := by omega
        rcases h_lt_or_eq with hlt | heq
        · exact Fin.mk_lt_mk.mpr hlt
        · exfalso; exact ha_ne_i (Fin.ext heq)
      · have hb_ne_i : P.orderEmbOfFin rfl b ≠ i := by
          intro heq; rw [heq] at hb; exact hi_notP hb
        simp only [Equiv.swap_apply_of_ne_of_ne hb_ne_i hb_eq]
        exact h_lt
  have h_mem : ∀ j, s (P.orderEmbOfFin rfl j) ∈ P' := by
    intro j
    simp only [P', Finset.mem_map, Function.Embedding.coeFn_mk]
    exact ⟨P.orderEmbOfFin rfl j, P.orderEmbOfFin_mem rfl j, rfl⟩
  have huniq := Finset.orderEmbOfFin_unique (Finset.card_map _ : P'.card = P.card) h_mem h_strict
  exact (congrFun huniq j).symm

set_option backward.isDefEq.respectTransparency false in
/-- Key insight: extractAlpha is preserved under left shifts.
    
    When we apply a left shift:
    - P' = swap(P) where i ∉ P and i+1 ∈ P (so P' has i instead of i+1)
    - σ' = σ * swap
    - Q' = Q (unchanged, by imageFinset_leftShift_eq)
    
    The extractAlpha permutation describes the bijection from sorted P to sorted Q
    via σ. After the shift, the same bijection exists from sorted P' to sorted Q via σ'.
    
    The key observation is that for each position j in the sorted order:
    - If P_j ≠ i+1: P'_j' = P_j for some j', and σ'(P'_j') = σ(P_j)
    - If P_j = i+1: P'_j' = i, and σ'(i) = σ(swap(i)) = σ(i+1) = σ(P_j)
    
    Since the images are the same, extractAlpha' = extractAlpha. -/
lemma extractAlpha_leftShift_eq {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q)
    (i : Fin n) (hi : i.val + 1 < n)
    (hi_notP : i ∉ P) (hiplus_P : (⟨i.val + 1, hi⟩ : Fin n) ∈ P) :
    let s := Equiv.swap i ⟨i.val + 1, hi⟩
    let P' := imageFinset s P
    let σ' := σ * s
    let hcard' : P'.card = Q.card := by 
      simp only [P', imageFinset, Finset.card_map]
      exact hcard
    let hσ' : imageFinset σ' P' = Q := imageFinset_leftShift_eq P Q σ hσ i hi hi_notP hiplus_P
    (Equiv.Perm.sign (extractAlpha P' Q hcard' σ' hσ') : ℤ) = 
    (Equiv.Perm.sign (extractAlpha P Q hcard σ hσ) : ℤ) := by
  intro s P' σ' hcard' hσ'
  -- P'.card = P.card since P' is just P with elements permuted
  have hP'_card : P'.card = P.card := by simp [P', imageFinset, Finset.card_map]
  
  -- Show the underlying functions are pointwise equal (after accounting for type)
  have h_val_eq : ∀ (j : ℕ) (hj : j < P'.card) (hj' : j < P.card),
      (extractAlpha P' Q hcard' σ' hσ' ⟨j, hj⟩).val = 
      (extractAlpha P Q hcard σ hσ ⟨j, hj'⟩).val := by
    intro j hj hj'
    simp only [extractAlpha, Equiv.ofBijective_apply]
    -- Use swap_orderEmbOfFin_eq to relate P'.orderEmbOfFin to P.orderEmbOfFin
    have h_swap := swap_orderEmbOfFin_eq P i hi hi_notP hiplus_P ⟨j, hj'⟩
    -- P'.orderEmbOfFin rfl ⟨j, hj⟩ = s (P.orderEmbOfFin rfl ⟨j, hj'⟩)
    have h_orderEmb : P'.orderEmbOfFin rfl ⟨j, hj⟩ = s (P.orderEmbOfFin rfl ⟨j, hj'⟩) := by
      have h1 : P'.orderEmbOfFin rfl ⟨j, hj⟩ = 
          (P.map ⟨s, s.injective⟩).orderEmbOfFin (Finset.card_map _) ⟨j, hj'⟩ := by
        simp only [P', imageFinset]; rfl
      rw [h1, h_swap]
    -- σ' (P'.orderEmbOfFin j) = σ (s (s (P.orderEmbOfFin j))) = σ (P.orderEmbOfFin j)
    have h_sigma : σ' (P'.orderEmbOfFin rfl ⟨j, hj⟩) = σ (P.orderEmbOfFin rfl ⟨j, hj'⟩) := by
      rw [h_orderEmb]
      simp only [σ', Equiv.Perm.coe_mul, Function.comp_apply]
      have h_inv : s (s (P.orderEmbOfFin rfl ⟨j, hj'⟩)) = P.orderEmbOfFin rfl ⟨j, hj'⟩ := 
        Equiv.swap_apply_self i ⟨i.val + 1, hi⟩ _
      rw [h_inv]
    -- The values are equal because the arguments to orderIsoOfFin.symm are equal
    simp only [h_sigma]
    rfl
  
  -- Show the cast permutation equals the original
  have h_perm_eq : (hP'_card ▸ extractAlpha P' Q hcard' σ' hσ') = extractAlpha P Q hcard σ hσ := by
    ext ⟨j, hj⟩
    have hj' : j < P'.card := hP'_card ▸ hj
    have := h_val_eq j hj' hj
    rw [perm_cast_apply_val hP'_card (extractAlpha P' Q hcard' σ' hσ') ⟨j, hj⟩]
    convert this using 2
  
  -- Use sign_eq_of_cast_eq to conclude
  have hsign := sign_eq_of_cast_eq hP'_card (extractAlpha P' Q hcard' σ' hσ') 
    (extractAlpha P Q hcard σ hσ) h_perm_eq
  rw [hsign]

set_option backward.isDefEq.respectTransparency false in
/-- Key insight: extractBeta is also preserved under left shifts.
    
    Similar reasoning to extractAlpha: the complement P'ᶜ has the same structure
    as Pᶜ (with i and i+1 swapped), and the bijection from sorted P'ᶜ to sorted Qᶜ
    via σ' is the same as from sorted Pᶜ to sorted Qᶜ via σ. -/
lemma extractBeta_leftShift_eq {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q)
    (i : Fin n) (hi : i.val + 1 < n)
    (hi_notP : i ∉ P) (hiplus_P : (⟨i.val + 1, hi⟩ : Fin n) ∈ P) :
    let s := Equiv.swap i ⟨i.val + 1, hi⟩
    let P' := imageFinset s P
    let σ' := σ * s
    let hcard' : P'.card = Q.card := by 
      simp only [P', imageFinset, Finset.card_map]
      exact hcard
    let hσ' : imageFinset σ' P' = Q := imageFinset_leftShift_eq P Q σ hσ i hi hi_notP hiplus_P
    (Equiv.Perm.sign (extractBeta P' Q hcard' σ' hσ') : ℤ) = 
    (Equiv.Perm.sign (extractBeta P Q hcard σ hσ) : ℤ) := by
  intro s P' σ' hcard' hσ'
  -- Similar reasoning to extractAlpha_leftShift_eq:
  -- The key insight is that extractBeta P' Q ... σ' ... and extractBeta P Q ... σ ...
  -- compute the same permutation (up to a trivial type cast).
  --
  -- Key facts:
  -- 1. P'ᶜ.card = Pᶜ.card (since P'.card = P.card)
  -- 2. P'ᶜ = imageFinset s Pᶜ (complement of image = image of complement for bijections)
  -- 3. For any j : Fin Pᶜ.card, P'ᶜ.orderEmbOfFin (cast j) = s (Pᶜ.orderEmbOfFin j)
  --    (the sorted order is preserved because s swaps adjacent elements i < i+1)
  -- 4. σ' (P'ᶜ.orderEmbOfFin (cast j)) = σ (s (s (Pᶜ.orderEmbOfFin j))) = σ (Pᶜ.orderEmbOfFin j)
  --    (since s is an involution and σ' = σ * s)
  --
  -- Therefore the permutations give the same positions in Qᶜ, and thus have equal signs.
  
  have hcardC : P'ᶜ.card = Pᶜ.card := by
    simp only [Finset.card_compl, Fintype.card_fin, P', imageFinset, Finset.card_map]
  
  -- The equivalence between the index types
  let e : Fin Pᶜ.card ≃ Fin P'ᶜ.card := (Fin.castOrderIso hcardC.symm).toEquiv
  
  -- Step 1: P'ᶜ = imageFinset s Pᶜ
  have hP'compl : P'ᶜ = imageFinset s Pᶜ := by
    rw [show P' = imageFinset s P from rfl]
    exact (imageFinset_compl s P).symm
  
  -- Step 2: s is strictly monotone on Pᶜ (since i ∈ Pᶜ but i+1 ∉ Pᶜ)
  have hs_mono : StrictMono (fun y : (Pᶜ : Finset (Fin n)) => (s y : Fin n)) := by
    intro a b hab
    show s (a : Fin n) < s (b : Fin n)
    have hab_val : (a : Fin n).val < (b : Fin n).val := hab
    have ha_notP : (a : Fin n) ∉ P := Finset.mem_compl.mp a.prop
    have hb_notP : (b : Fin n) ∉ P := Finset.mem_compl.mp b.prop
    have ha_ne_iplus : (a : Fin n) ≠ ⟨i.val + 1, hi⟩ := fun h => ha_notP (h ▸ hiplus_P)
    have hb_ne_iplus : (b : Fin n) ≠ ⟨i.val + 1, hi⟩ := fun h => hb_notP (h ▸ hiplus_P)
    by_cases ha_eq_i : (a : Fin n) = i
    · rw [ha_eq_i, Equiv.swap_apply_left]
      have hb_ne_i : (b : Fin n) ≠ i := by intro h; rw [ha_eq_i, h] at hab_val; omega
      rw [Equiv.swap_apply_of_ne_of_ne hb_ne_i hb_ne_iplus]
      have h1 : (b : Fin n).val > i.val := by rw [ha_eq_i] at hab_val; exact hab_val
      have h2 : (b : Fin n).val ≠ i.val + 1 := fun h => hb_ne_iplus (Fin.ext h)
      exact Fin.lt_def.mpr (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt h1) (Ne.symm h2))
    · rw [Equiv.swap_apply_of_ne_of_ne ha_eq_i ha_ne_iplus]
      by_cases hb_eq_i : (b : Fin n) = i
      · rw [hb_eq_i, Equiv.swap_apply_left]
        have h : (a : Fin n).val < i.val := by rw [hb_eq_i] at hab_val; exact hab_val
        exact Fin.lt_def.mpr (Nat.lt_trans h (Nat.lt_succ_self i.val))
      · rw [Equiv.swap_apply_of_ne_of_ne hb_eq_i hb_ne_iplus]
        exact hab_val
  
  -- Step 3: orderEmbOfFin of imageFinset s Pᶜ at x equals s applied to orderEmbOfFin of Pᶜ at x
  have h_orderEmb : ∀ x : Fin Pᶜ.card, 
      (imageFinset s Pᶜ).orderEmbOfFin (by simp only [imageFinset, Finset.card_map]) x = 
      s (Pᶜ.orderEmbOfFin rfl x) := by
    intro x
    have h1 : ∀ y, s (Pᶜ.orderEmbOfFin rfl y) ∈ imageFinset s Pᶜ := by
      intro y
      simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨Pᶜ.orderEmbOfFin rfl y, Finset.orderEmbOfFin_mem Pᶜ rfl y, rfl⟩
    have h2 : StrictMono (fun y => s (Pᶜ.orderEmbOfFin rfl y)) := by
      intro a b hab
      have h := (Pᶜ.orderEmbOfFin rfl).strictMono hab
      exact hs_mono (Subtype.mk_lt_mk.mpr h)
    have h3 := Finset.orderEmbOfFin_unique (by simp [imageFinset]) h1 h2
    exact (congrFun h3 x).symm
  
  -- Step 4: σ' (s y) = σ y (since σ' = σ * s and s is involution)
  have h_sigma : ∀ y : Fin n, σ' (s y) = σ y := by
    intro y
    simp only [σ', Equiv.Perm.mul_apply]
    congr 1
    exact Equiv.swap_apply_self i ⟨i.val + 1, hi⟩ y
  
  -- The permutations are related by e (they compute the same thing up to type cast)
  have h_comm : ∀ x : Fin Pᶜ.card, 
      e (extractBeta P Q hcard σ hσ x) = extractBeta P' Q hcard' σ' hσ' (e x) := by
    intro x
    -- Both sides are qIso.symm ⟨σ' (P'ᶜ.orderEmbOfFin (e x)), _⟩ and qIso.symm ⟨σ (Pᶜ.orderEmbOfFin x), _⟩
    -- We'll show they have equal .val by showing σ' (P'ᶜ.orderEmbOfFin (e x)) = σ (Pᶜ.orderEmbOfFin x)
    
    -- P'ᶜ.orderEmbOfFin (e x) = s (Pᶜ.orderEmbOfFin x)
    have h_emb_P'C : P'ᶜ.orderEmbOfFin (by rw [hcardC]) ((Fin.castOrderIso hcardC.symm).toEquiv x) = 
                     s (Pᶜ.orderEmbOfFin rfl x) := by
      -- Use orderEmbOfFin_unique: both sides are strictly monotone maps into P'ᶜ
      have h_mem : ∀ y : Fin Pᶜ.card, s (Pᶜ.orderEmbOfFin rfl y) ∈ P'ᶜ := by
        intro y
        rw [hP'compl]
        simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
        exact ⟨Pᶜ.orderEmbOfFin rfl y, Finset.orderEmbOfFin_mem Pᶜ rfl y, rfl⟩
      have h_mono : StrictMono (fun y : Fin Pᶜ.card => s (Pᶜ.orderEmbOfFin rfl y)) := by
        intro a b hab
        have h := (Pᶜ.orderEmbOfFin rfl).strictMono hab
        exact hs_mono (Subtype.mk_lt_mk.mpr h)
      -- Use orderEmbOfFin_unique
      have h_unique := Finset.orderEmbOfFin_unique (by rw [hcardC]) h_mem h_mono
      -- h_unique : (fun y => s (Pᶜ.orderEmbOfFin y)) = P'ᶜ.orderEmbOfFin _
      have h_at_x := congrFun h_unique x
      -- h_at_x : s (Pᶜ.orderEmbOfFin x) = P'ᶜ.orderEmbOfFin x
      -- We need P'ᶜ.orderEmbOfFin (e x) = s (Pᶜ.orderEmbOfFin x)
      -- where (e x).val = x.val
      -- Use that orderEmbOfFin values at indices with same .val are equal
      have h_eq : P'ᶜ.orderEmbOfFin (by rw [hcardC]) ((Fin.castOrderIso hcardC.symm).toEquiv x) = 
                  P'ᶜ.orderEmbOfFin (by rw [hcardC]) x := by
        rw [Finset.orderEmbOfFin_eq_orderEmbOfFin_iff]
        rfl
      rw [h_eq, ← h_at_x]
    
    -- σ' (s y) = σ y
    have h_sigma_eq : σ' (P'ᶜ.orderEmbOfFin (by rw [hcardC]) ((Fin.castOrderIso hcardC.symm).toEquiv x)) = 
                      σ (Pᶜ.orderEmbOfFin rfl x) := by
      rw [h_emb_P'C, h_sigma]
    
    -- Now show the equality of extractBeta values
    simp only [extractBeta, Equiv.ofBijective_apply, e]
    apply Fin.ext
    -- The goal is: (Fin.cast ... (qIso.symm ⟨σ ..., ...⟩)).val = (qIso'.symm ⟨σ' ..., ...⟩).val
    -- We prove this by showing both sides equal idxOf (σ (Pᶜ.orderEmbOfFin x)) (Qᶜ.sort)
    
    -- Cardinality facts
    have hcardQ : Qᶜ.card = Pᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin]; omega
    have hcardQ' : Qᶜ.card = P'ᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin, P', imageFinset, Finset.card_map]; omega
    
    -- LHS: Fin.cast preserves .val, and orderIsoOfFin_symm_apply gives idxOf
    have h_lhs : ((Fin.castOrderIso hcardC.symm).toEquiv 
                   ((Qᶜ.orderIsoOfFin hcardQ).symm 
                     ⟨σ (Pᶜ.orderEmbOfFin rfl x), sigma_orderEmb_compl_mem_of_imageFinset P Q σ hσ x⟩)).val = 
                 (Qᶜ.sort (· ≤ ·)).idxOf (σ (Pᶜ.orderEmbOfFin rfl x)) := by
      -- Fin.cast preserves val
      have h1 : ((Fin.castOrderIso hcardC.symm).toEquiv 
                   ((Qᶜ.orderIsoOfFin hcardQ).symm 
                     ⟨σ (Pᶜ.orderEmbOfFin rfl x), sigma_orderEmb_compl_mem_of_imageFinset P Q σ hσ x⟩)).val = 
                ((Qᶜ.orderIsoOfFin hcardQ).symm 
                  ⟨σ (Pᶜ.orderEmbOfFin rfl x), sigma_orderEmb_compl_mem_of_imageFinset P Q σ hσ x⟩).val := rfl
      rw [h1, Finset.orderIsoOfFin_symm_apply]
    
    -- RHS: orderIsoOfFin_symm_apply gives idxOf
    have h_rhs : ((Qᶜ.orderIsoOfFin hcardQ').symm 
                   ⟨σ' (P'ᶜ.orderEmbOfFin (by rw [hcardC]) ((Fin.castOrderIso hcardC.symm).toEquiv x)), 
                    sigma_orderEmb_compl_mem_of_imageFinset P' Q σ' hσ' ((Fin.castOrderIso hcardC.symm).toEquiv x)⟩).val = 
                 (Qᶜ.sort (· ≤ ·)).idxOf (σ' (P'ᶜ.orderEmbOfFin (by rw [hcardC]) ((Fin.castOrderIso hcardC.symm).toEquiv x))) := by
      rw [Finset.orderIsoOfFin_symm_apply]
    
    -- Combine using h_sigma_eq
    rw [h_lhs, h_rhs, h_sigma_eq]
  
  -- Apply sign_eq_sign_of_equiv to conclude
  have h_sign := Equiv.Perm.sign_eq_sign_of_equiv (extractBeta P Q hcard σ hσ) 
                   (extractBeta P' Q hcard' σ' hσ') e h_comm
  simp only [h_sign]

/-- The sign decomposition formula is preserved under left shifts.
    
    This combines:
    1. leftShift_preserves_combined_sign: (-1)^(sum P + sum Q) * sign(σ) is preserved
    2. extractAlpha_leftShift_eq: sign(extractAlpha) is preserved
    3. extractBeta_leftShift_eq: sign(extractBeta) is preserved
    
    Together, these show that if the formula holds for (P', Q, σ'), it holds for (P, Q, σ). -/
lemma sign_decomposition_leftShift_invariant {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q)
    (i : Fin n) (hi : i.val + 1 < n)
    (hi_notP : i ∉ P) (hiplus_P : (⟨i.val + 1, hi⟩ : Fin n) ∈ P) :
    let s := Equiv.swap i ⟨i.val + 1, hi⟩
    let P' := imageFinset s P
    let σ' := σ * s
    let hcard' : P'.card = Q.card := by 
      simp only [P', imageFinset, Finset.card_map]
      exact hcard
    let hσ' : imageFinset σ' P' = Q := imageFinset_leftShift_eq P Q σ hσ i hi hi_notP hiplus_P
    -- If the formula holds for (P', Q, σ'), then it holds for (P, Q, σ)
    ((Equiv.Perm.sign σ' : ℤ) = (-1 : ℤ) ^ (finsetSumFin P' + finsetSumFin Q) * 
      (Equiv.Perm.sign (extractAlpha P' Q hcard' σ' hσ') : ℤ) * 
      (Equiv.Perm.sign (extractBeta P' Q hcard' σ' hσ') : ℤ)) →
    ((Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * 
      (Equiv.Perm.sign (extractAlpha P Q hcard σ hσ) : ℤ) * 
      (Equiv.Perm.sign (extractBeta P Q hcard σ hσ) : ℤ)) := by
  intro s P' σ' hcard' hσ' h_shifted
  -- Get the preservation lemmas
  have h_preserve_raw := leftShift_preserves_combined_sign P Q σ hσ i hi hi_notP hiplus_P
  have h_alpha := extractAlpha_leftShift_eq P Q hcard σ hσ i hi hi_notP hiplus_P
  have h_beta := extractBeta_leftShift_eq P Q hcard σ hσ i hi hi_notP hiplus_P
  -- Expand let bindings in the helper lemmas
  simp only at h_preserve_raw h_alpha h_beta
  -- h_preserve_raw has Q' = imageFinset σ' P', but we know Q' = Q by hσ'
  -- So we need to rewrite finsetSumFin Q' to finsetSumFin Q
  have h_preserve : (-1 : ℤ) ^ (finsetSumFin P' + finsetSumFin Q) * (Equiv.Perm.sign σ' : ℤ) = 
                    (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := by
    have hQ'_eq : imageFinset σ' P' = Q := hσ'
    rw [hQ'_eq] at h_preserve_raw
    exact h_preserve_raw
  -- From h_shifted and h_preserve:
  -- h_shifted: sign(σ') = (-1)^(sum P' + sum Q) * sign(α') * sign(β')
  -- h_preserve: (-1)^(sum P' + sum Q) * sign(σ') = (-1)^(sum P + sum Q) * sign(σ)
  have h1 : (-1 : ℤ) ^ (finsetSumFin P' + finsetSumFin Q) * 
            ((-1 : ℤ) ^ (finsetSumFin P' + finsetSumFin Q) * 
             (Equiv.Perm.sign (extractAlpha P' Q hcard' σ' hσ') : ℤ) * 
             (Equiv.Perm.sign (extractBeta P' Q hcard' σ' hσ') : ℤ)) = 
            (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := by
    rw [← h_shifted]; exact h_preserve
  -- Simplify LHS using (-1)^k * (-1)^k = 1
  have h2 : (-1 : ℤ) ^ (finsetSumFin P' + finsetSumFin Q) * (-1 : ℤ) ^ (finsetSumFin P' + finsetSumFin Q) = 1 := by
    rw [← pow_add]; simp
  have h3 : (Equiv.Perm.sign (extractAlpha P' Q hcard' σ' hσ') : ℤ) * 
            (Equiv.Perm.sign (extractBeta P' Q hcard' σ' hσ') : ℤ) = 
            (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := by
    calc (Equiv.Perm.sign (extractAlpha P' Q hcard' σ' hσ') : ℤ) * 
         (Equiv.Perm.sign (extractBeta P' Q hcard' σ' hσ') : ℤ) 
        = 1 * ((Equiv.Perm.sign (extractAlpha P' Q hcard' σ' hσ') : ℤ) * 
               (Equiv.Perm.sign (extractBeta P' Q hcard' σ' hσ') : ℤ)) := by ring
      _ = ((-1 : ℤ) ^ (finsetSumFin P' + finsetSumFin Q) * (-1 : ℤ) ^ (finsetSumFin P' + finsetSumFin Q)) * 
          ((Equiv.Perm.sign (extractAlpha P' Q hcard' σ' hσ') : ℤ) * 
           (Equiv.Perm.sign (extractBeta P' Q hcard' σ' hσ') : ℤ)) := by rw [h2]
      _ = (-1 : ℤ) ^ (finsetSumFin P' + finsetSumFin Q) * 
          ((-1 : ℤ) ^ (finsetSumFin P' + finsetSumFin Q) * 
           (Equiv.Perm.sign (extractAlpha P' Q hcard' σ' hσ') : ℤ) * 
           (Equiv.Perm.sign (extractBeta P' Q hcard' σ' hσ') : ℤ)) := by ring
      _ = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := h1
  -- Use h_alpha and h_beta: sign(α') = sign(α), sign(β') = sign(β)
  have h4 : (Equiv.Perm.sign (extractAlpha P Q hcard σ hσ) : ℤ) * 
            (Equiv.Perm.sign (extractBeta P Q hcard σ hσ) : ℤ) = 
            (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := by
    rw [← h_alpha, ← h_beta]; exact h3
  -- Solve for sign(σ) using (-1)^k * (-1)^k = 1
  have h5 : (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) = 1 := by
    rw [← pow_add]; simp
  calc (Equiv.Perm.sign σ : ℤ) 
      = 1 * (Equiv.Perm.sign σ : ℤ) := by ring
    _ = ((-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q)) * 
        (Equiv.Perm.sign σ : ℤ) := by rw [h5]
    _ = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * 
        ((-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ)) := by ring
    _ = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * 
        ((Equiv.Perm.sign (extractAlpha P Q hcard σ hσ) : ℤ) * 
         (Equiv.Perm.sign (extractBeta P Q hcard σ hσ) : ℤ)) := by rw [h4]
    _ = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * 
        (Equiv.Perm.sign (extractAlpha P Q hcard σ hσ) : ℤ) * 
        (Equiv.Perm.sign (extractBeta P Q hcard σ hσ) : ℤ) := by ring

/-- Left co-shift: when σ' = s * σ and Q' = s(Q), we have σ'(P) = Q'. -/
lemma imageFinset_leftCoShift_eq {n : ℕ} (P Q : Finset (Fin n)) (σ : Equiv.Perm (Fin n))
    (hσ : imageFinset σ P = Q)
    (i : Fin n) (hi : i.val + 1 < n)
    (_hi_notQ : i ∉ Q) (_hiplus_Q : (⟨i.val + 1, hi⟩ : Fin n) ∈ Q) :
    let s := Equiv.swap i ⟨i.val + 1, hi⟩
    let Q' := imageFinset s Q
    let σ' := s * σ
    imageFinset σ' P = Q' := by
  intro s Q' σ'
  simp only [Q', σ', imageFinset]
  ext x
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro ⟨p, hp, hpx⟩
    have hσp_mem : σ p ∈ Q := by 
      rw [← hσ]
      simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨p, hp, rfl⟩
    refine ⟨σ p, hσp_mem, ?_⟩
    simp only [Equiv.Perm.coe_mul, Function.comp_apply] at hpx ⊢
    exact hpx
  · intro ⟨q, hq_mem, hqx⟩
    rw [← hσ] at hq_mem
    simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at hq_mem
    obtain ⟨p, hp, hpq⟩ := hq_mem
    refine ⟨p, hp, ?_⟩
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, hpq, hqx]

set_option backward.isDefEq.respectTransparency false in
/-- Key insight: extractAlpha is preserved under left co-shifts.
    
    When we apply a left co-shift:
    - P stays the same
    - Q' = swap(Q) where i ∉ Q and i+1 ∈ Q (so Q' has i instead of i+1)
    - σ' = swap * σ
    
    The key observation is that swap_preserves_position shows:
    s(Q.orderEmbOfFin j) = Q'.orderEmbOfFin j
    
    Since σ'(P.orderEmbOfFin j) = s(σ(P.orderEmbOfFin j)), and the position of
    s(x) in Q' equals the position of x in Q (for x ∈ Q), we have
    extractAlpha P Q' σ' = extractAlpha P Q σ. -/
lemma extractAlpha_leftCoShift_eq {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q)
    (i : Fin n) (hi : i.val + 1 < n)
    (hi_notQ : i ∉ Q) (hiplus_Q : (⟨i.val + 1, hi⟩ : Fin n) ∈ Q) :
    let s := Equiv.swap i ⟨i.val + 1, hi⟩
    let Q' := imageFinset s Q
    let σ' := s * σ
    let hcard' : P.card = Q'.card := by 
      simp only [Q', imageFinset, Finset.card_map]
      exact hcard
    let hσ' : imageFinset σ' P = Q' := imageFinset_leftCoShift_eq P Q σ hσ i hi hi_notQ hiplus_Q
    (Equiv.Perm.sign (extractAlpha P Q' hcard' σ' hσ') : ℤ) = 
    (Equiv.Perm.sign (extractAlpha P Q hcard σ hσ) : ℤ) := by
  intro s Q' σ' hcard' hσ'
  -- The key is to show extractAlpha P Q' hcard' σ' hσ' = extractAlpha P Q hcard σ hσ
  -- Then the signs are equal
  suffices h : extractAlpha P Q' hcard' σ' hσ' = extractAlpha P Q hcard σ hσ by rw [h]
  -- Show the permutations are equal by showing they agree on all inputs
  ext j : 1
  -- Unfold the definitions
  simp only [extractAlpha, Equiv.ofBijective_apply]
  -- Get the swap preservation lemma
  have h_swap := swap_preserves_position Q hcard.symm i hi hi_notQ hiplus_Q
  -- The key fact: σ(p) ∈ Q and s(σ(p)) ∈ Q'
  have hσp_mem : σ (P.orderEmbOfFin rfl j) ∈ Q := sigma_orderEmb_mem_of_imageFinset P Q σ hσ j
  have hsσp_mem : s (σ (P.orderEmbOfFin rfl j)) ∈ Q' := by
    simp only [Q', imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
    exact ⟨σ (P.orderEmbOfFin rfl j), hσp_mem, rfl⟩
  -- Use swap_preserves_position to show positions are equal
  -- Let pos = (Q.orderIso).symm ⟨σ p, hσp_mem⟩
  set pos := (Q.orderIsoOfFin hcard.symm).symm ⟨σ (P.orderEmbOfFin rfl j), hσp_mem⟩ with hpos_def
  -- Q.orderEmb pos = σ p
  have hpos_eq : Q.orderEmbOfFin hcard.symm pos = σ (P.orderEmbOfFin rfl j) := by
    have h := (Q.orderIsoOfFin hcard.symm).apply_symm_apply ⟨σ (P.orderEmbOfFin rfl j), hσp_mem⟩
    exact congr_arg Subtype.val h
  -- s(σ p) = Q'.orderEmb pos by h_swap
  have hQ'_card : Q'.card = P.card := by simp only [Q', imageFinset, Finset.card_map, hcard]
  have hsσp_eq : s (σ (P.orderEmbOfFin rfl j)) = Q'.orderEmbOfFin hQ'_card pos := by
    rw [← hpos_eq]
    simp only [Q', imageFinset]
    exact h_swap pos
  -- Therefore (Q'.orderIso).symm ⟨s(σ p), _⟩ = pos
  have h_goal : (Q'.orderIsoOfFin hQ'_card).symm ⟨s (σ (P.orderEmbOfFin rfl j)), hsσp_mem⟩ = pos := by
    apply (Q'.orderIsoOfFin hQ'_card).injective
    simp only [OrderIso.apply_symm_apply]
    ext
    simp only [Finset.coe_orderIsoOfFin_apply, hsσp_eq]
  -- Now connect to the goal
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, σ']
  convert h_goal using 1

set_option backward.isDefEq.respectTransparency false in
/-- Key insight: extractBeta is also preserved under left co-shifts.
    
    Similar reasoning to extractAlpha: the complement Q'ᶜ has the same structure
    as Qᶜ (with i and i+1 swapped), and the bijection from sorted Pᶜ to sorted Q'ᶜ
    via σ' is the same as from sorted Pᶜ to sorted Qᶜ via σ. -/
lemma extractBeta_leftCoShift_eq {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q)
    (i : Fin n) (hi : i.val + 1 < n)
    (hi_notQ : i ∉ Q) (hiplus_Q : (⟨i.val + 1, hi⟩ : Fin n) ∈ Q) :
    let s := Equiv.swap i ⟨i.val + 1, hi⟩
    let Q' := imageFinset s Q
    let σ' := s * σ
    let hcard' : P.card = Q'.card := by 
      simp only [Q', imageFinset, Finset.card_map]
      exact hcard
    let hσ' : imageFinset σ' P = Q' := imageFinset_leftCoShift_eq P Q σ hσ i hi hi_notQ hiplus_Q
    (Equiv.Perm.sign (extractBeta P Q' hcard' σ' hσ') : ℤ) = 
    (Equiv.Perm.sign (extractBeta P Q hcard σ hσ) : ℤ) := by
  intro s Q' σ' hcard' hσ'
  -- Key insight: For Qᶜ, we have i ∈ Qᶜ (since i ∉ Q) and i+1 ∉ Qᶜ (since i+1 ∈ Q)
  -- This is the case where s preserves the sorted order on Qᶜ
  
  -- Cardinality facts
  have hcardC : Pᶜ.card = Qᶜ.card := by simp [Finset.card_compl, hcard]
  have hcardC' : Pᶜ.card = Q'ᶜ.card := by simp [Finset.card_compl, Q', imageFinset, hcard]
  
  -- Q'ᶜ = imageFinset s Qᶜ
  have hQ'compl : Q'ᶜ = imageFinset s Qᶜ := (imageFinset_compl s Q).symm
  
  -- Key facts about i and Qᶜ
  have hi_inQC : i ∈ Qᶜ := Finset.mem_compl.mpr hi_notQ
  have hiplus_notQC : (⟨i.val + 1, hi⟩ : Fin n) ∉ Qᶜ := by
    simp only [Finset.mem_compl, not_not]
    exact hiplus_Q
  
  -- s is strictly monotone on Qᶜ (since i ∈ Qᶜ but i+1 ∉ Qᶜ)
  have hs_mono : StrictMono (fun y : (Qᶜ : Finset (Fin n)) => (s y : Fin n)) := by
    intro a b hab
    show s (a : Fin n) < s (b : Fin n)
    have hab_val : (a : Fin n).val < (b : Fin n).val := hab
    have ha_inQC : (a : Fin n) ∈ Qᶜ := a.prop
    have hb_inQC : (b : Fin n) ∈ Qᶜ := b.prop
    have ha_ne_iplus : (a : Fin n) ≠ ⟨i.val + 1, hi⟩ := fun h => hiplus_notQC (h ▸ ha_inQC)
    have hb_ne_iplus : (b : Fin n) ≠ ⟨i.val + 1, hi⟩ := fun h => hiplus_notQC (h ▸ hb_inQC)
    by_cases ha_eq_i : (a : Fin n) = i
    · rw [ha_eq_i, Equiv.swap_apply_left]
      have hb_ne_i : (b : Fin n) ≠ i := by intro h; rw [ha_eq_i, h] at hab_val; omega
      rw [Equiv.swap_apply_of_ne_of_ne hb_ne_i hb_ne_iplus]
      have h1 : (b : Fin n).val > i.val := by rw [ha_eq_i] at hab_val; exact hab_val
      have h2 : (b : Fin n).val ≠ i.val + 1 := fun h => hb_ne_iplus (Fin.ext h)
      exact Fin.lt_def.mpr (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt h1) (Ne.symm h2))
    · rw [Equiv.swap_apply_of_ne_of_ne ha_eq_i ha_ne_iplus]
      by_cases hb_eq_i : (b : Fin n) = i
      · rw [hb_eq_i, Equiv.swap_apply_left]
        have h : (a : Fin n).val < i.val := by rw [hb_eq_i] at hab_val; exact hab_val
        exact Fin.lt_def.mpr (Nat.lt_trans h (Nat.lt_succ_self i.val))
      · rw [Equiv.swap_apply_of_ne_of_ne hb_eq_i hb_ne_iplus]
        exact hab_val
  
  -- orderEmbOfFin of imageFinset s Qᶜ at x equals s applied to orderEmbOfFin of Qᶜ at x
  have h_orderEmb : ∀ x : Fin Qᶜ.card, 
      (imageFinset s Qᶜ).orderEmbOfFin (by simp only [imageFinset, Finset.card_map]) x = 
      s (Qᶜ.orderEmbOfFin rfl x) := by
    intro x
    have h1 : ∀ y, s (Qᶜ.orderEmbOfFin rfl y) ∈ imageFinset s Qᶜ := by
      intro y
      simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨Qᶜ.orderEmbOfFin rfl y, Finset.orderEmbOfFin_mem Qᶜ rfl y, rfl⟩
    have h2 : StrictMono (fun y => s (Qᶜ.orderEmbOfFin rfl y)) := by
      intro a b hab
      have h := (Qᶜ.orderEmbOfFin rfl).strictMono hab
      exact hs_mono (Subtype.mk_lt_mk.mpr h)
    have h3 := Finset.orderEmbOfFin_unique (by simp [imageFinset]) h1 h2
    exact (congrFun h3 x).symm
  
  -- σ' y = s (σ y) (since σ' = s * σ)
  have h_sigma : ∀ y : Fin n, σ' y = s (σ y) := fun y => rfl
  
  -- The key: show extractBeta P Q' σ' = extractBeta P Q σ
  suffices h_eq : extractBeta P Q' hcard' σ' hσ' = extractBeta P Q hcard σ hσ by
    rw [h_eq]
  
  -- Prove equality by showing they agree on all inputs
  ext x
  
  -- Unfold the definitions to see the goal
  unfold extractBeta
  simp only [Equiv.ofBijective_apply]
  
  -- Get the value σ(Pᶜ.orderEmbOfFin x)
  set y := σ (Pᶜ.orderEmbOfFin rfl x) with hy_def
  have hy_mem : y ∈ Qᶜ := sigma_orderEmb_compl_mem_of_imageFinset P Q σ hσ x
  
  -- s(y) ∈ Q'ᶜ
  have hsy_mem : s y ∈ Q'ᶜ := by
    rw [hQ'compl]
    simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
    exact ⟨y, hy_mem, rfl⟩
  
  -- Find k such that Qᶜ.orderEmbOfFin k = y
  have h_y_in_range : y ∈ Set.range (Qᶜ.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hy_mem
  obtain ⟨k, hk⟩ := h_y_in_range
  
  have h_sy_eq : s y = (imageFinset s Qᶜ).orderEmbOfFin (by simp [imageFinset]) k := by
    rw [← hk, h_orderEmb]
  
  -- idxOf (Qᶜ.orderEmbOfFin k) in Qᶜ.sort = k.val
  have h_idx_y : (Qᶜ.sort (· ≤ ·)).idxOf y = k.val := by
    rw [← hk]
    exact orderEmbOfFin_idxOf_eq Qᶜ rfl k
  
  -- idxOf (Q'ᶜ.orderEmbOfFin k) in Q'ᶜ.sort = k.val
  have h_idx_sy : (Q'ᶜ.sort (· ≤ ·)).idxOf (s y) = k.val := by
    rw [hQ'compl, h_sy_eq]
    exact orderEmbOfFin_idxOf_eq (imageFinset s Qᶜ) (by simp [imageFinset]) k
  
  -- σ' (Pᶜ.orderEmbOfFin x) = s y
  have h_sigma_x : σ' (Pᶜ.orderEmbOfFin rfl x) = s y := by
    simp only [h_sigma, hy_def]
  
  -- The goal is about .val of orderIsoOfFin_symm, which equals idxOf
  rw [Finset.orderIsoOfFin_symm_apply, Finset.orderIsoOfFin_symm_apply]
  
  -- σ' (Pᶜ.orderEmbOfFin x) = s y and σ (Pᶜ.orderEmbOfFin x) = y
  calc (Q'ᶜ.sort (· ≤ ·)).idxOf (σ' (Pᶜ.orderEmbOfFin rfl x))
      = (Q'ᶜ.sort (· ≤ ·)).idxOf (s y) := by rw [h_sigma_x]
    _ = k.val := h_idx_sy
    _ = (Qᶜ.sort (· ≤ ·)).idxOf y := h_idx_y.symm
    _ = (Qᶜ.sort (· ≤ ·)).idxOf (σ (Pᶜ.orderEmbOfFin rfl x)) := by rw [hy_def]

/-- The sign decomposition formula is preserved under left co-shifts.
    
    This combines:
    1. leftCoShift_preserves_combined_sign: (-1)^(sum P + sum Q) * sign(σ) is preserved
    2. extractAlpha_leftCoShift_eq: sign(extractAlpha) is preserved
    3. extractBeta_leftCoShift_eq: sign(extractBeta) is preserved
    
    Together, these show that if the formula holds for (P, Q', σ'), it holds for (P, Q, σ). -/
lemma sign_decomposition_leftCoShift_invariant {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q)
    (i : Fin n) (hi : i.val + 1 < n)
    (hi_notQ : i ∉ Q) (hiplus_Q : (⟨i.val + 1, hi⟩ : Fin n) ∈ Q) :
    let s := Equiv.swap i ⟨i.val + 1, hi⟩
    let Q' := imageFinset s Q
    let σ' := s * σ
    let hcard' : P.card = Q'.card := by 
      simp only [Q', imageFinset, Finset.card_map]
      exact hcard
    let hσ' : imageFinset σ' P = Q' := imageFinset_leftCoShift_eq P Q σ hσ i hi hi_notQ hiplus_Q
    -- If the formula holds for (P, Q', σ'), then it holds for (P, Q, σ)
    ((Equiv.Perm.sign σ' : ℤ) = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q') * 
      (Equiv.Perm.sign (extractAlpha P Q' hcard' σ' hσ') : ℤ) * 
      (Equiv.Perm.sign (extractBeta P Q' hcard' σ' hσ') : ℤ)) →
    ((Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * 
      (Equiv.Perm.sign (extractAlpha P Q hcard σ hσ) : ℤ) * 
      (Equiv.Perm.sign (extractBeta P Q hcard σ hσ) : ℤ)) := by
  intro s Q' σ' hcard' hσ' h_shifted
  -- Get the preservation lemmas
  have h_preserve := leftCoShift_preserves_combined_sign P Q σ hσ i hi hi_notQ hiplus_Q
  have h_alpha := extractAlpha_leftCoShift_eq P Q hcard σ hσ i hi hi_notQ hiplus_Q
  have h_beta := extractBeta_leftCoShift_eq P Q hcard σ hσ i hi hi_notQ hiplus_Q
  -- Expand let bindings in the helper lemmas
  simp only at h_preserve h_alpha h_beta
  -- From h_shifted and h_preserve:
  -- h_shifted: sign(σ') = (-1)^(sum P + sum Q') * sign(α') * sign(β')
  -- h_preserve: (-1)^(sum P + sum Q') * sign(σ') = (-1)^(sum P + sum Q) * sign(σ)
  have h1 : (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q') * 
            ((-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q') * 
             (Equiv.Perm.sign (extractAlpha P Q' hcard' σ' hσ') : ℤ) * 
             (Equiv.Perm.sign (extractBeta P Q' hcard' σ' hσ') : ℤ)) = 
            (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := by
    rw [← h_shifted]; exact h_preserve
  -- Simplify LHS using (-1)^k * (-1)^k = 1
  have h2 : (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q') * (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q') = 1 := by
    rw [← pow_add]; simp
  have h3 : (Equiv.Perm.sign (extractAlpha P Q' hcard' σ' hσ') : ℤ) * 
            (Equiv.Perm.sign (extractBeta P Q' hcard' σ' hσ') : ℤ) = 
            (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := by
    calc (Equiv.Perm.sign (extractAlpha P Q' hcard' σ' hσ') : ℤ) * 
         (Equiv.Perm.sign (extractBeta P Q' hcard' σ' hσ') : ℤ) 
        = 1 * ((Equiv.Perm.sign (extractAlpha P Q' hcard' σ' hσ') : ℤ) * 
               (Equiv.Perm.sign (extractBeta P Q' hcard' σ' hσ') : ℤ)) := by ring
      _ = ((-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q') * (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q')) * 
          ((Equiv.Perm.sign (extractAlpha P Q' hcard' σ' hσ') : ℤ) * 
           (Equiv.Perm.sign (extractBeta P Q' hcard' σ' hσ') : ℤ)) := by rw [h2]
      _ = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q') * 
          ((-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q') * 
           (Equiv.Perm.sign (extractAlpha P Q' hcard' σ' hσ') : ℤ) * 
           (Equiv.Perm.sign (extractBeta P Q' hcard' σ' hσ') : ℤ)) := by ring
      _ = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := h1
  -- Use h_alpha and h_beta: sign(α') = sign(α), sign(β') = sign(β)
  have h4 : (Equiv.Perm.sign (extractAlpha P Q hcard σ hσ) : ℤ) * 
            (Equiv.Perm.sign (extractBeta P Q hcard σ hσ) : ℤ) = 
            (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ) := by
    rw [← h_alpha, ← h_beta]; exact h3
  -- Solve for sign(σ) using (-1)^k * (-1)^k = 1
  have h5 : (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) = 1 := by
    rw [← pow_add]; simp
  calc (Equiv.Perm.sign σ : ℤ) 
      = 1 * (Equiv.Perm.sign σ : ℤ) := by ring
    _ = ((-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q)) * 
        (Equiv.Perm.sign σ : ℤ) := by rw [h5]
    _ = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * 
        ((-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign σ : ℤ)) := by ring
    _ = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * 
        ((Equiv.Perm.sign (extractAlpha P Q hcard σ hσ) : ℤ) * 
         (Equiv.Perm.sign (extractBeta P Q hcard σ hσ) : ℤ)) := by rw [h4]
    _ = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * 
        (Equiv.Perm.sign (extractAlpha P Q hcard σ hσ) : ℤ) * 
        (Equiv.Perm.sign (extractBeta P Q hcard σ hσ) : ℤ) := by ring


/-- The sign decomposition theorem: for any σ with σ(P) = Q,
    sign(σ) = (-1)^(sum P + sum Q) * sign(extractAlpha) * sign(extractBeta).
    
    This is proved by strong induction on finsetSumFin P + finsetSumFin Q.
    - Base case: P = Q = prefixFinset (handled by sign_decomposition_prefix)
    - Inductive case: Either P or Q can be shifted towards prefixFinset
      - If P ≠ prefixFinset: apply left shift (sign_decomposition_leftShift_invariant)
      - If P = prefixFinset but Q ≠ prefixFinset: apply co-shift (sign_decomposition_leftCoShift_invariant)
-/
theorem sign_decomposition {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) :
    (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * 
      (Equiv.Perm.sign (extractAlpha P Q hcard σ hσ) : ℤ) * 
      (Equiv.Perm.sign (extractBeta P Q hcard σ hσ) : ℤ) := by
  -- Handle edge cases: empty or full sets
  by_cases hk_pos : 0 < P.card
  · by_cases hk_lt : P.card < n
    · -- Main case: 0 < P.card < n
      have hk : P.card ≤ n := Nat.le_of_lt hk_lt
      -- Use strong induction on finsetSumFin P + finsetSumFin Q
      have hQ_card_pos : 0 < Q.card := hcard ▸ hk_pos
      have hQ_card_lt : Q.card < n := hcard ▸ hk_lt
      have hQ_card : Q.card ≤ n := Nat.le_of_lt hQ_card_lt
      -- Strong induction
      generalize hm : finsetSumFin P + finsetSumFin Q = m
      induction m using Nat.strong_induction_on generalizing P Q σ with
        | _ m ih =>
          -- Check if P = prefixFinset
          by_cases hP_prefix : P = prefixFinset n P.card hk
          · -- P is already the prefix
            by_cases hQ_prefix : Q = prefixFinset n Q.card hQ_card
            · -- Both are prefixes, apply base case
              -- Since P.card = Q.card and both are prefixFinset, P = Q
              -- The formula holds by sign_decomposition_prefix
              have hPQ : P = Q := by
                have h1 : P = prefixFinset n P.card hk := hP_prefix
                have h2 : Q = prefixFinset n Q.card hQ_card := hQ_prefix
                rw [h1, h2]
                simp only [prefixFinset, hcard]
              subst hPQ
              -- The base case is handled by sign_decomposition_prefix
              -- After subst hPQ, P = Q so hm : finsetSumFin P + finsetSumFin P = m
              -- We use sign_decomposition_prefix with k = P.card
              have hσ' : imageFinset σ (prefixFinset n P.card hk) = prefixFinset n P.card hk := by
                rw [← hP_prefix]; exact hσ
              have h_base := sign_decomposition_prefix hk σ hσ'
              -- h_base provides the result for P' := prefixFinset n P.card hk
              -- The goal is the same formula but with P instead of P'
              -- Since P = P' (by hP_prefix), these are equal
              -- Use subst on hP_prefix to convert P to prefixFinset n P.card hk
              -- Then the goal matches h_base exactly (up to proof irrelevance)
              have key : ∀ (R : Finset (Fin n)) (hR : R = prefixFinset n P.card hk) 
                  (hσR : imageFinset σ R = R),
                  (Equiv.Perm.sign σ : ℤ) = (-1 : ℤ) ^ (finsetSumFin R + finsetSumFin R) * 
                    (Equiv.Perm.sign (extractAlpha R R rfl σ hσR) : ℤ) * 
                    (Equiv.Perm.sign (extractBeta R R rfl σ hσR) : ℤ) := by
                intro R hR hσR
                subst hR
                exact h_base
              -- Now use key and rewrite m back to finsetSumFin P + finsetSumFin P
              rw [← hm]
              exact key P hP_prefix hσ

            · -- P is prefix but Q is not, use co-shift
              obtain ⟨i, hi, hi_notQ, hiplus_Q⟩ := exists_shift_opportunity hQ_card hQ_card_pos 
                  hQ_card_lt Q rfl hQ_prefix
              -- Define the shifted objects
              let s := Equiv.swap i ⟨i.val + 1, hi⟩
              let Q' := imageFinset s Q
              let σ' := s * σ
              have hcard' : P.card = Q'.card := by 
                simp only [Q', imageFinset, Finset.card_map]
                exact hcard
              have hσ' : imageFinset σ' P = Q' := 
                imageFinset_leftCoShift_eq P Q σ hσ i hi hi_notQ hiplus_Q
              -- finsetSumFin Q' < finsetSumFin Q
              have hQ'_sum : finsetSumFin Q' = finsetSumFin Q - 1 := 
                finsetSumFin_swap_of_left_shift Q i hi hi_notQ hiplus_Q
              have hQ_sum_pos : 0 < finsetSumFin Q := by
                have h : (⟨i.val + 1, hi⟩ : Fin n) ∈ Q := hiplus_Q
                have hpos : 0 < (⟨i.val + 1, hi⟩ : Fin n).val := Nat.zero_lt_succ i.val
                calc finsetSumFin Q = ∑ x ∈ Q, x.val := rfl
                  _ ≥ (⟨i.val + 1, hi⟩ : Fin n).val := Finset.single_le_sum (by simp) h
                  _ > 0 := hpos
              have hsum_lt : finsetSumFin P + finsetSumFin Q' < m := by
                rw [hQ'_sum, ← hm]
                omega
              -- Apply IH
              have hQ'_card : Q'.card ≤ n := by
                simp only [Q', imageFinset, Finset.card_map]
                exact hQ_card
              have hQ'_card_lt : Q'.card < n := by
                simp only [Q', imageFinset, Finset.card_map]
                exact hQ_card_lt
              have hQ'_card_pos : 0 < Q'.card := by
                simp only [Q', imageFinset, Finset.card_map]
                exact hQ_card_pos
              have h_ih := ih (finsetSumFin P + finsetSumFin Q') hsum_lt P Q' hcard' σ' hσ' 
                  hk_pos hk_lt hk hQ'_card_pos hQ'_card_lt hQ'_card rfl
              -- Apply the co-shift invariant
              have h_result := sign_decomposition_leftCoShift_invariant P Q hcard σ hσ i hi hi_notQ hiplus_Q h_ih
              rw [← hm]
              exact h_result
          · -- P is not prefix, use left shift
            obtain ⟨i, hi, hi_notP, hiplus_P⟩ := exists_shift_opportunity hk hk_pos hk_lt P rfl hP_prefix
            -- Define the shifted objects
            let s := Equiv.swap i ⟨i.val + 1, hi⟩
            let P' := imageFinset s P
            let σ' := σ * s
            have hcard' : P'.card = Q.card := by 
              simp only [P', imageFinset, Finset.card_map]
              exact hcard
            have hσ' : imageFinset σ' P' = Q := 
              imageFinset_leftShift_eq P Q σ hσ i hi hi_notP hiplus_P
            -- finsetSumFin P' < finsetSumFin P
            have hP'_sum : finsetSumFin P' = finsetSumFin P - 1 := 
              finsetSumFin_swap_of_left_shift P i hi hi_notP hiplus_P
            have hP_sum_pos : 0 < finsetSumFin P := by
              have h : (⟨i.val + 1, hi⟩ : Fin n) ∈ P := hiplus_P
              have hpos : 0 < (⟨i.val + 1, hi⟩ : Fin n).val := Nat.zero_lt_succ i.val
              calc finsetSumFin P = ∑ x ∈ P, x.val := rfl
                _ ≥ (⟨i.val + 1, hi⟩ : Fin n).val := Finset.single_le_sum (by simp) h
                _ > 0 := hpos
            have hsum_lt : finsetSumFin P' + finsetSumFin Q < m := by
              rw [hP'_sum, ← hm]
              omega
            -- Apply IH
            have hP'_card : P'.card ≤ n := by
              simp only [P', imageFinset, Finset.card_map]
              exact hk
            have hP'_card_lt : P'.card < n := by
              simp only [P', imageFinset, Finset.card_map]
              exact hk_lt
            have hP'_card_pos : 0 < P'.card := by
              simp only [P', imageFinset, Finset.card_map]
              exact hk_pos
            have h_ih := ih (finsetSumFin P' + finsetSumFin Q) hsum_lt P' Q hcard' σ' hσ' hP'_card_pos 
                hP'_card_lt hP'_card hQ_card_pos hQ_card_lt hQ_card rfl
            -- Apply the left shift invariant
            have h_result := sign_decomposition_leftShift_invariant P Q hcard σ hσ i hi hi_notP hiplus_P h_ih
            rw [← hm]
            exact h_result
    · -- P.card = n (full set case)
      -- When P = Q = univ, extractAlpha = σ (up to reindexing) and extractBeta = 1
      -- P.card = n implies P = univ
      have hP_univ : P = Finset.univ := by
        apply Finset.eq_univ_of_card
        have h1 : P.card ≤ n := by
          have h : P.card ≤ Fintype.card (Fin n) := Finset.card_le_univ P
          rw [Fintype.card_fin] at h
          exact h
        have h2 : n ≤ P.card := Nat.not_lt.mp hk_lt
        simp only [Fintype.card_fin]
        exact Nat.le_antisymm h1 h2
      -- Since imageFinset σ P = Q and P = univ, we have Q = univ
      have hQ_univ : Q = Finset.univ := by
        rw [hP_univ] at hσ
        simp [imageFinset] at hσ
        exact hσ.symm
      subst hP_univ hQ_univ
      -- Now P = Q = univ
      -- extractBeta univ univ _ σ _ : Perm (Fin 0) (since univᶜ = ∅), which has sign 1
      have h_beta_sign : (Equiv.Perm.sign (extractBeta Finset.univ Finset.univ hcard σ hσ) : ℤ) = 1 := by
        have h_eq : extractBeta Finset.univ Finset.univ hcard σ hσ = 1 := by
          ext x
          -- x : Fin (univ : Finset (Fin n))ᶜ.card = Fin 0
          have h : (Finset.univ : Finset (Fin n))ᶜ.card = 0 := by simp
          exact (Fin.cast h x).elim0
        rw [h_eq, Equiv.Perm.sign_one]
        norm_cast
      -- extractAlpha univ univ _ σ _ has the same sign as σ
      have h_alpha_sign : (Equiv.Perm.sign (extractAlpha Finset.univ Finset.univ hcard σ hσ) : ℤ) = 
          (Equiv.Perm.sign σ : ℤ) := by
        simp only [sign_extractAlpha_univ hcard σ hσ]
      -- finsetSumFin univ + finsetSumFin univ is even, so (-1)^(...) = 1
      have h_pow : (-1 : ℤ) ^ (finsetSumFin (Finset.univ : Finset (Fin n)) + finsetSumFin (Finset.univ : Finset (Fin n))) = 1 := by
        have : Even (finsetSumFin (Finset.univ : Finset (Fin n)) + finsetSumFin (Finset.univ : Finset (Fin n))) := by
          exact Even.add_self (finsetSumFin (Finset.univ : Finset (Fin n)))
        exact Even.neg_one_pow this
      rw [h_pow, h_alpha_sign, h_beta_sign]
      ring
  · -- P.card = 0 (empty set case)
    -- When P = Q = ∅, extractAlpha = 1 (on Fin 0) and extractBeta = σ (on Fin n)
    have hP_empty : P = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hk_pos)
    have hQ_empty : Q = ∅ := by
      rw [← Finset.card_eq_zero]
      rw [← hcard]
      exact Nat.eq_zero_of_not_pos hk_pos
    subst hP_empty hQ_empty
    -- Now P = Q = ∅
    -- finsetSumFin ∅ = 0
    simp only [finsetSumFin, Finset.sum_empty]
    -- (-1)^0 = 1
    simp only [add_zero, pow_zero, one_mul]
    -- extractAlpha ∅ ∅ _ σ _ : Perm (Fin 0), which has sign 1
    have h_alpha_sign : (Equiv.Perm.sign (extractAlpha ∅ ∅ hcard σ hσ) : ℤ) = 1 := by
      have h_eq : extractAlpha ∅ ∅ hcard σ hσ = 1 := by
        ext x
        exact x.elim0
      rw [h_eq, Equiv.Perm.sign_one]
      norm_cast
    rw [h_alpha_sign, one_mul]
    -- Now we need: sign(σ) = sign(extractBeta ∅ ∅ hcard σ hσ)
    -- Use sign_extractBeta_empty
    congr 1
    exact (sign_extractBeta_empty hcard σ hσ).symm


/-- Helper lemma: product over a finset equals product over Fin card. -/
private lemma prod_over_finset_eq_prod_fin {n : ℕ} {R : Type*} [CommMonoid R]
    (P : Finset (Fin n)) (f : Fin n → R) :
    ∏ i ∈ P, f i = ∏ j : Fin P.card, f (P.orderEmbOfFin rfl j) := by
  rw [← Finset.prod_coe_sort P f]
  apply Fintype.prod_equiv (P.orderIsoOfFin rfl).symm.toEquiv
  intro j
  simp [Finset.orderEmbOfFin]

/-- The key property of extractAlpha: σ(pⱼ) = q_{α(j)} where pⱼ and qⱼ are the j-th elements
    of P and Q in sorted order. -/
lemma extractAlpha_spec {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) (j : Fin P.card) :
    σ (P.orderEmbOfFin rfl j) = Q.orderEmbOfFin (hcard.symm ▸ rfl) (extractAlpha P Q hcard σ hσ j) := by
  simp only [extractAlpha, Equiv.ofBijective_apply]
  have h : σ (P.orderEmbOfFin rfl j) ∈ Q := sigma_orderEmb_mem_of_imageFinset P Q σ hσ j
  have hiso := (Q.orderIsoOfFin hcard.symm).apply_symm_apply ⟨σ (P.orderEmbOfFin rfl j), h⟩
  simp only [Finset.orderEmbOfFin]
  simp only [RelEmbedding.coe_trans, OrderIso.coe_toOrderEmbedding, Function.comp_apply,
             OrderEmbedding.subtype_apply, Finset.coe_orderIsoOfFin_apply]
  exact (congrArg Subtype.val hiso).symm

/-- The key property of extractBeta: σ(pᶜⱼ) = qᶜ_{β(j)} where pᶜⱼ and qᶜⱼ are the j-th elements
    of Pᶜ and Qᶜ in sorted order. -/
lemma extractBeta_spec {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) (j : Fin Pᶜ.card) :
    σ (Pᶜ.orderEmbOfFin rfl j) = 
    Qᶜ.orderEmbOfFin (by simp [Finset.card_compl, hcard] : Qᶜ.card = Pᶜ.card) 
      (extractBeta P Q hcard σ hσ j) := by
  simp only [extractBeta, Equiv.ofBijective_apply]
  have hcard' : Pᶜ.card = Qᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin, hcard]
  have h : σ (Pᶜ.orderEmbOfFin rfl j) ∈ Qᶜ := sigma_orderEmb_compl_mem_of_imageFinset P Q σ hσ j
  have hiso := (Qᶜ.orderIsoOfFin hcard'.symm).apply_symm_apply ⟨σ (Pᶜ.orderEmbOfFin rfl j), h⟩
  simp only [Finset.orderEmbOfFin]
  simp only [RelEmbedding.coe_trans, OrderIso.coe_toOrderEmbedding, Function.comp_apply,
             OrderEmbedding.subtype_apply, Finset.coe_orderIsoOfFin_apply]
  exact (congrArg Subtype.val hiso).symm

set_option backward.isDefEq.respectTransparency false in
/-- Round-trip lemma: extractAlpha of constructSigma equals the original α. -/
lemma extractAlpha_constructSigma {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (α : Equiv.Perm (Fin P.card)) (β : Equiv.Perm (Fin Pᶜ.card)) 
    (hσ : imageFinset (constructSigma P Q hcard α β) P = Q) :
    extractAlpha P Q hcard (constructSigma P Q hcard α β) hσ = α := by
  ext i
  simp only [extractAlpha, Equiv.ofBijective_apply]
  have hi_mem : P.orderEmbOfFin rfl i ∈ P := Finset.orderEmbOfFin_mem P rfl i
  -- constructSigma applied to an element of P uses α
  have h_eval : (constructSigma P Q hcard α β) (P.orderEmbOfFin rfl i) = 
      Q.orderEmbOfFin hcard.symm (α ((P.orderIsoOfFin rfl).symm ⟨P.orderEmbOfFin rfl i, hi_mem⟩)) := by
    simp only [constructSigma, Equiv.ofBijective_apply]
    simp only [hi_mem, dite_eq_left]
  -- Use orderIsoOfFin_symm_orderEmbOfFin to simplify
  have h1 : (P.orderIsoOfFin rfl).symm ⟨P.orderEmbOfFin rfl i, hi_mem⟩ = i :=
    orderIsoOfFin_symm_orderEmbOfFin P rfl i
  -- Now the result follows
  have h2 : (Q.orderIsoOfFin hcard.symm).symm 
      ⟨Q.orderEmbOfFin hcard.symm (α i), Finset.orderEmbOfFin_mem Q hcard.symm (α i)⟩ = α i :=
    orderIsoOfFin_symm_orderEmbOfFin Q hcard.symm (α i)
  -- Connect the pieces
  have h_goal : (Q.orderIsoOfFin hcard.symm).symm 
      ⟨(constructSigma P Q hcard α β) (P.orderEmbOfFin rfl i), 
       sigma_orderEmb_mem_of_imageFinset P Q (constructSigma P Q hcard α β) hσ i⟩ = α i := by
    simp only [h_eval, h1]
    convert h2
  simp only [Fin.val_inj]
  exact h_goal

set_option backward.isDefEq.respectTransparency false in
/-- Round-trip lemma: extractBeta of constructSigma equals the original β. -/
lemma extractBeta_constructSigma {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (α : Equiv.Perm (Fin P.card)) (β : Equiv.Perm (Fin Pᶜ.card)) 
    (hσ : imageFinset (constructSigma P Q hcard α β) P = Q) :
    extractBeta P Q hcard (constructSigma P Q hcard α β) hσ = β := by
  ext i
  simp only [extractBeta, Equiv.ofBijective_apply]
  have hcard' : Pᶜ.card = Qᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin, hcard]
  have hcard'' : Qᶜ.card = Pᶜ.card := hcard'.symm
  have hi_mem : Pᶜ.orderEmbOfFin rfl i ∈ Pᶜ := Finset.orderEmbOfFin_mem Pᶜ rfl i
  have hi_notP : Pᶜ.orderEmbOfFin rfl i ∉ P := Finset.mem_compl.mp hi_mem
  -- constructSigma applied to an element of Pᶜ uses β
  have h_eval : (constructSigma P Q hcard α β) (Pᶜ.orderEmbOfFin rfl i) = 
      Qᶜ.orderEmbOfFin hcard'' (β ((Pᶜ.orderIsoOfFin rfl).symm ⟨Pᶜ.orderEmbOfFin rfl i, hi_mem⟩)) := by
    simp only [constructSigma, Equiv.ofBijective_apply]
    simp only [hi_notP, dite_eq_right, not_false_eq_true]
  -- Use orderIsoOfFin_symm_orderEmbOfFin to simplify
  have h1 : (Pᶜ.orderIsoOfFin rfl).symm ⟨Pᶜ.orderEmbOfFin rfl i, hi_mem⟩ = i :=
    orderIsoOfFin_symm_orderEmbOfFin Pᶜ rfl i
  -- Now the result follows
  have h2 : (Qᶜ.orderIsoOfFin hcard'').symm 
      ⟨Qᶜ.orderEmbOfFin hcard'' (β i), Finset.orderEmbOfFin_mem Qᶜ hcard'' (β i)⟩ = β i :=
    orderIsoOfFin_symm_orderEmbOfFin Qᶜ hcard'' (β i)
  -- Connect the pieces
  have h_goal : (Qᶜ.orderIsoOfFin hcard'').symm 
      ⟨(constructSigma P Q hcard α β) (Pᶜ.orderEmbOfFin rfl i), 
       sigma_orderEmb_compl_mem_of_imageFinset P Q (constructSigma P Q hcard α β) hσ i⟩ = β i := by
    simp only [h_eval, h1]
    convert h2
  simp only [Fin.val_inj]
  exact h_goal

set_option backward.isDefEq.respectTransparency false in
/-- Round-trip lemma: constructSigma of (extractAlpha, extractBeta) equals the original σ.
    This is the other direction of the bijection, showing that extract ∘ construct = id. -/
lemma constructSigma_extract {n : ℕ} (P Q : Finset (Fin n)) (hcard : P.card = Q.card)
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) :
    constructSigma P Q hcard (extractAlpha P Q hcard σ hσ) (extractBeta P Q hcard σ hσ) = σ := by
  ext x
  simp only [constructSigma, Equiv.ofBijective_apply]
  by_cases hx : x ∈ P
  · -- Case x ∈ P: constructSigma uses extractAlpha
    simp only [hx, dite_eq_left]
    simp only [extractAlpha, Equiv.ofBijective_apply]
    -- First simplify P.orderEmbOfFin rfl ((P.orderIsoOfFin rfl).symm ⟨x, hx⟩) = x
    have hPiso : P.orderEmbOfFin rfl ((P.orderIsoOfFin rfl).symm ⟨x, hx⟩) = x := by
      have h := (P.orderIsoOfFin rfl).apply_symm_apply ⟨x, hx⟩
      exact congrArg Subtype.val h
    -- Now we need Q.orderEmbOfFin _ ((Q.orderIsoOfFin _).symm ⟨σ x, _⟩) = σ x
    have hσx_mem : σ x ∈ Q := by
      rw [← hσ]
      simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨x, hx, rfl⟩
    have hQiso : Q.orderEmbOfFin (hcard.symm ▸ rfl) ((Q.orderIsoOfFin hcard.symm).symm ⟨σ x, hσx_mem⟩) = σ x := by
      have h := (Q.orderIsoOfFin hcard.symm).apply_symm_apply ⟨σ x, hσx_mem⟩
      exact congrArg Subtype.val h
    -- Now connect the pieces
    simp only [hPiso]
    simp only [Fin.val_inj]
    exact hQiso
  · -- Case x ∉ P: constructSigma uses extractBeta
    simp only [hx, dite_eq_right, not_false_eq_true]
    have hxC : x ∈ Pᶜ := Finset.mem_compl.mpr hx
    simp only [extractBeta, Equiv.ofBijective_apply]
    have hPCiso : Pᶜ.orderEmbOfFin rfl ((Pᶜ.orderIsoOfFin rfl).symm ⟨x, hxC⟩) = x := by
      have h := (Pᶜ.orderIsoOfFin rfl).apply_symm_apply ⟨x, hxC⟩
      exact congrArg Subtype.val h
    have hcardC : Pᶜ.card = Qᶜ.card := by simp only [Finset.card_compl, Fintype.card_fin, hcard]
    have hσx_mem : σ x ∈ Qᶜ := by
      simp only [Finset.mem_compl]
      intro hcontra
      rw [← hσ] at hcontra
      simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at hcontra
      obtain ⟨y, hy, hσy⟩ := hcontra
      have : x = y := σ.injective hσy.symm
      rw [this] at hx
      exact hx hy
    have hQCiso : Qᶜ.orderEmbOfFin hcardC.symm ((Qᶜ.orderIsoOfFin hcardC.symm).symm ⟨σ x, hσx_mem⟩) = σ x := by
      have h := (Qᶜ.orderIsoOfFin hcardC.symm).apply_symm_apply ⟨σ x, hσx_mem⟩
      exact congrArg Subtype.val h
    simp only [hPCiso]
    simp only [Fin.val_inj]
    exact hQCiso

/-- The product over P factors through the submatrix determinant.
    ∑_{σ : σ(P)=Q} sign(σ) · ∏_{i∈P} A_{σ(i),i} relates to det(sub_Q^P A). -/
theorem prod_P_eq_submatrix_det {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (hcard : P.card = Q.card) 
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) :
    ∏ i ∈ P, A (σ i) i = 
    ∏ j : Fin P.card, A (Q.orderEmbOfFin (hcard.symm ▸ rfl) (extractAlpha P Q hcard σ hσ j)) 
                        (P.orderEmbOfFin rfl j) := by
  rw [prod_over_finset_eq_prod_fin P (fun i => A (σ i) i)]
  congr 1
  ext j
  rw [extractAlpha_spec P Q hcard σ hσ j]

/-- The product over Pᶜ factors through the submatrix determinant. -/
theorem prod_Pc_eq_submatrix_det {n : ℕ} (B : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (hcard : P.card = Q.card) 
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) :
    ∏ i ∈ Pᶜ, B (σ i) i = 
    ∏ j : Fin Pᶜ.card, B (Qᶜ.orderEmbOfFin (by simp [Finset.card_compl, hcard]) (extractBeta P Q hcard σ hσ j)) 
                          (Pᶜ.orderEmbOfFin rfl j) := by
  rw [prod_over_finset_eq_prod_fin Pᶜ (fun i => B (σ i) i)]
  congr 1
  ext j
  rw [extractBeta_spec P Q hcard σ hσ j]

/-- The key factorization lemma: For fixed P and Q with |P| = |Q|,
    the sum over permutations σ with σ(P) = Q factors into a product of determinants.
    
    This is equation (pf.thm.det.det(A+B).sumPQ) from the tex source.
    
    The proof involves:
    1. A bijection σ ↦ (α_σ, β_σ) from {σ : σ(P) = Q} to S_{|P|} × S_{|Pᶜ|}
       where α_σ describes σ's action on P and β_σ describes σ's action on Pᶜ
    2. The sign identity: (-1)^σ = (-1)^(sum P + sum Q) · (-1)^α · (-1)^β
    3. Factoring the products and recognizing them as determinants
    
    See the tex source (CauchyBinet.tex, proof of Theorem thm.det.det(A+B)) for details.
    
    The sign identity proof (step 2) uses the following key insight from the tex source:
    - Define "left shifts" that replace σ by σ·s_i and P by s_i(P)
    - Each left shift decrements sum(P) by 1 and flips both (-1)^(sum P + sum Q) and (-1)^σ
    - After sum(P) - (1+2+...+k) left shifts, P becomes [k]
    - Similarly for Q via "left co-shifts"
    - When P = Q = [k], the sign identity reduces to ℓ(σ) = ℓ(α) + ℓ(β) (inversion counting) -/
theorem sum_perms_mapping_eq_det_product {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (hcard : P.card = Q.card) :
    ∑ σ ∈ permsMapping P Q,
      Equiv.Perm.sign σ • ((∏ i ∈ P, A (σ i) i) * (∏ i ∈ Pᶜ, B (σ i) i)) =
    (-1 : R) ^ (finsetSumFin P + finsetSumFin Q) *
    submatrixDet A Q P hcard.symm * 
    submatrixDet B Qᶜ Pᶜ (by simp [Finset.card_compl, hcard]) := by
  /-
  The proof proceeds by:
  1. Use the bijection σ ↦ (extractAlpha σ, extractBeta σ) to reindex the sum
  2. Apply sign_decomposition to factor out (-1)^(sum P + sum Q)
  3. Use prod_P_eq_submatrix_det to recognize the determinant structure
  4. Factor the double sum into a product of two determinants
  
  See CauchyBinet.tex, proof of Theorem thm.det.det(A+B) for full details.
  
  Proof outline:
  1. For σ ∈ permsMapping P Q, we have σ(P) = Q and σ(Pᶜ) = Qᶜ (by imageFinset_compl)
  2. Define α : Perm (Fin P.card) by: σ(P.orderEmb i) = Q.orderEmb (α i)
  3. Define β : Perm (Fin Pᶜ.card) by: σ(Pᶜ.orderEmb i) = Qᶜ.orderEmb (β i)
  4. The map σ ↦ (α, β) is a bijection permsMapping P Q ≃ Perm (Fin P.card) × Perm (Fin Pᶜ.card)
  5. The sign identity sign(σ) = (-1)^(sum P + sum Q) * sign(α) * sign(β) follows from:
     - The "shift" argument: left-shifting by s_i flips both (-1)^(sum P + sum Q) and sign(σ)
     - After reducing to P = Q = [k], the identity becomes ℓ(σ) = ℓ(α) + ℓ(β)
  6. Reindex the sum over permsMapping P Q as a double sum over α and β
  7. Factor the products and recognize them as det(A_QP) and det(B_QᶜPᶜ)
  -/
  -- Step 1: Key property - σ(Pᶜ) = Qᶜ for σ ∈ permsMapping P Q
  have hcompl : ∀ σ ∈ permsMapping P Q, imageFinset σ Pᶜ = Qᶜ := by
    intro σ hσ
    simp only [permsMapping, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    ext x
    simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_compl]
    constructor
    · intro ⟨y, hy, hyx⟩ hxQ
      have : y ∈ P := by
        rw [← hσ] at hxQ
        simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at hxQ
        obtain ⟨z, hz, hzx⟩ := hxQ
        rw [← hyx] at hzx
        have hyz := σ.injective hzx
        subst hyz
        exact hz
      exact hy this
    · intro hx
      use σ.symm x
      constructor
      · intro h
        apply hx
        rw [← hσ]
        simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
        exact ⟨σ.symm x, h, by simp⟩
      · simp
  -- Step 2: Key cardinality facts
  have hcardC : Pᶜ.card = Qᶜ.card := by simp [Finset.card_compl, hcard]
  have hcardQ : Q.card = P.card := hcard.symm
  
  -- Step 3: Expand the determinants on the RHS
  simp only [submatrixDet]
  
  -- Step 4: For each σ ∈ permsMapping P Q, we use sign_decomposition and prod factorization
  -- The LHS is ∑_{σ : σ(P)=Q} sign(σ) • (∏_{i∈P} A_{σ(i),i}) * (∏_{i∈Pᶜ} B_{σ(i),i})
  -- The RHS is (-1)^(sum P + sum Q) * det(A_QP) * det(B_QᶜPᶜ)
  
  -- Key insight: The bijection σ ↦ (extractAlpha σ, extractBeta σ) transforms the LHS into
  -- a double sum over Perm(Fin P.card) × Perm(Fin Pᶜ.card), which factors as the RHS
  
  -- For each σ ∈ permsMapping P Q:
  -- 1. sign(σ) = (-1)^(sum P + sum Q) * sign(α) * sign(β)  [by sign_decomposition]
  -- 2. ∏_{i∈P} A_{σ(i),i} = ∏_j A_{Q_α(j), P_j}  [by prod_P_eq_submatrix_det]
  -- 3. ∏_{i∈Pᶜ} B_{σ(i),i} = ∏_j B_{Qᶜ_β(j), Pᶜ_j}  [analogous for complement]
  
  -- The bijection and factorization then give the result
  -- This requires establishing that σ ↦ (α, β) is a bijection, which involves:
  -- - Injectivity: different σ give different (α, β)
  -- - Surjectivity: every (α, β) comes from some σ (via constructSigma)
  
  -- Rewrite using the sign decomposition and product factorizations
  have h_mem : ∀ σ ∈ permsMapping P Q, imageFinset σ P = Q := by
    intro σ hσ
    simp only [permsMapping, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact hσ
  
  -- Step 5: Reindex the sum using the bijection σ ↦ (extractAlpha σ, extractBeta σ)
  -- with inverse (α, β) ↦ constructSigma α β
  have h_eq : ∑ σ ∈ permsMapping P Q,
      Equiv.Perm.sign σ • ((∏ i ∈ P, A (σ i) i) * (∏ i ∈ Pᶜ, B (σ i) i)) =
    ∑ p : Equiv.Perm (Fin P.card) × Equiv.Perm (Fin Pᶜ.card),
      Equiv.Perm.sign (constructSigma P Q hcard p.1 p.2) • 
      ((∏ i ∈ P, A (constructSigma P Q hcard p.1 p.2 i) i) * 
       (∏ i ∈ Pᶜ, B (constructSigma P Q hcard p.1 p.2 i) i)) := by
    refine Finset.sum_bij' 
      (fun (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ permsMapping P Q) => 
        (extractAlpha P Q hcard σ (h_mem σ hσ), extractBeta P Q hcard σ (h_mem σ hσ)))
      (fun (p : Equiv.Perm (Fin P.card) × Equiv.Perm (Fin Pᶜ.card)) (_ : p ∈ Finset.univ) => 
        constructSigma P Q hcard p.1 p.2)
      ?_ ?_ ?_ ?_ ?_
    · intro σ hσ; exact Finset.mem_univ _
    · intro p _; exact constructSigma_mem_permsMapping P Q hcard p.1 p.2
    · intro σ hσ; exact constructSigma_extract P Q hcard σ (h_mem σ hσ)
    · intro p _
      exact Prod.ext
        (extractAlpha_constructSigma P Q hcard p.1 p.2 (constructSigma_imageFinset P Q hcard p.1 p.2))
        (extractBeta_constructSigma P Q hcard p.1 p.2 (constructSigma_imageFinset P Q hcard p.1 p.2))
    · intro σ hσ
      simp only
      rw [constructSigma_extract P Q hcard σ (h_mem σ hσ)]
  
  rw [h_eq]
  
  -- Step 6: Convert to double sum over α and β
  rw [← Finset.univ_product_univ, Finset.sum_product]
  
  -- Step 7: For each (α, β), use sign_decomposition and product factorizations
  -- sign(constructSigma α β) = (-1)^(sum P + sum Q) * sign(α) * sign(β)
  -- ∏_{i∈P} A_{σi,i} = ∏_j A_{Q_α(j), P_j}
  -- ∏_{i∈Pᶜ} B_{σi,i} = ∏_j B_{Qᶜ_β(j), Pᶜ_j}
  
  -- Apply sign_decomposition to each term
  -- sign_decomposition gives: sign(σ) = (-1)^(sum P + sum Q) * sign(extractAlpha σ) * sign(extractBeta σ)
  -- We use the round-trip lemmas to convert extractAlpha (constructSigma α β) = α
  have h_sign : ∀ α β, (Equiv.Perm.sign (constructSigma P Q hcard α β) : ℤ) = 
      (-1 : ℤ) ^ (finsetSumFin P + finsetSumFin Q) * 
      (Equiv.Perm.sign α : ℤ) * (Equiv.Perm.sign β : ℤ) := by
    intro α β
    have h := sign_decomposition P Q hcard (constructSigma P Q hcard α β) 
      (constructSigma_imageFinset P Q hcard α β)
    rw [extractAlpha_constructSigma P Q hcard α β (constructSigma_imageFinset P Q hcard α β),
        extractBeta_constructSigma P Q hcard α β (constructSigma_imageFinset P Q hcard α β)] at h
    exact h
  
  -- Apply product factorizations
  -- prod_P_eq_submatrix_det gives the product in terms of extractAlpha
  -- We use the round-trip lemma to convert to α
  have h_prodP : ∀ α β, ∏ i ∈ P, A (constructSigma P Q hcard α β i) i = 
      ∏ j : Fin P.card, A (Q.orderEmbOfFin (hcard.symm ▸ rfl) (α j)) (P.orderEmbOfFin rfl j) := by
    intro α β
    rw [prod_P_eq_submatrix_det A P Q hcard (constructSigma P Q hcard α β) 
        (constructSigma_imageFinset P Q hcard α β)]
    congr 1
    ext j
    rw [extractAlpha_constructSigma P Q hcard α β (constructSigma_imageFinset P Q hcard α β)]
  
  have h_prodPc : ∀ α β, ∏ i ∈ Pᶜ, B (constructSigma P Q hcard α β i) i = 
      ∏ j : Fin Pᶜ.card, B (Qᶜ.orderEmbOfFin hcardC.symm (β j)) (Pᶜ.orderEmbOfFin rfl j) := by
    intro α β
    rw [prod_Pc_eq_submatrix_det B P Q hcard (constructSigma P Q hcard α β) 
        (constructSigma_imageFinset P Q hcard α β)]
    congr 1
    ext j
    rw [extractBeta_constructSigma P Q hcard α β (constructSigma_imageFinset P Q hcard α β)]
  
  -- Simplify the sum using these identities
  -- First apply h_prodP and h_prodPc
  simp only [h_prodP, h_prodPc]
  
  -- Convert smul to multiplication first
  simp only [Units.smul_def, zsmul_eq_mul]
  
  -- Now apply h_sign to each term
  simp only [h_sign]
  
  -- Expand the coercion of the product
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  
  -- Now we need to show:
  -- ∑_α ∑_β (-1)^... * sign(α) * sign(β) * (∏ A) * (∏ B) = 
  -- (-1)^... * det(A_QP) * det(B_QᶜPᶜ)
  
  -- Factor out (-1)^(sum P + sum Q) from the double sum
  -- Key: ∑_α ∑_β c * f(α) * g(β) * h(α) * k(β) = c * (∑_α f(α) * h(α)) * (∑_β g(β) * k(β))
  have h_factor : ∑ α : Equiv.Perm (Fin P.card), ∑ β : Equiv.Perm (Fin Pᶜ.card),
      ((-1 : R) ^ (finsetSumFin P + finsetSumFin Q) * (Equiv.Perm.sign α : R) * (Equiv.Perm.sign β : R)) *
      ((∏ j, A (Q.orderEmbOfFin (hcard.symm ▸ rfl) (α j)) (P.orderEmbOfFin rfl j)) *
       (∏ j, B (Qᶜ.orderEmbOfFin hcardC.symm (β j)) (Pᶜ.orderEmbOfFin rfl j))) =
      (-1 : R) ^ (finsetSumFin P + finsetSumFin Q) *
      (∑ α : Equiv.Perm (Fin P.card), (Equiv.Perm.sign α : R) * 
        ∏ j, A (Q.orderEmbOfFin (hcard.symm ▸ rfl) (α j)) (P.orderEmbOfFin rfl j)) *
      (∑ β : Equiv.Perm (Fin Pᶜ.card), (Equiv.Perm.sign β : R) * 
        ∏ j, B (Qᶜ.orderEmbOfFin hcardC.symm (β j)) (Pᶜ.orderEmbOfFin rfl j)) := by
    -- First rewrite each summand into the form c * f(α) * g(β)
    have h_rearrange : ∀ α β, 
        ((-1 : R) ^ (finsetSumFin P + finsetSumFin Q) * ↑↑(Equiv.Perm.sign α) * ↑↑(Equiv.Perm.sign β)) *
        ((∏ j, A (Q.orderEmbOfFin (hcard.symm ▸ rfl) (α j)) (P.orderEmbOfFin rfl j)) *
         ∏ j, B (Qᶜ.orderEmbOfFin hcardC.symm (β j)) (Pᶜ.orderEmbOfFin rfl j)) = 
        (-1 : R) ^ (finsetSumFin P + finsetSumFin Q) * 
        (↑↑(Equiv.Perm.sign α) * ∏ j, A (Q.orderEmbOfFin (hcard.symm ▸ rfl) (α j)) (P.orderEmbOfFin rfl j)) *
        (↑↑(Equiv.Perm.sign β) * ∏ j, B (Qᶜ.orderEmbOfFin hcardC.symm (β j)) (Pᶜ.orderEmbOfFin rfl j)) := by
      intros; ring
    simp_rw [h_rearrange]
    -- Now factor: ∑_α ∑_β c * f(α) * g(β) = c * (∑_α f(α)) * (∑_β g(β))
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
  
  rw [h_factor]
  
  -- Now we need to match with the determinants on the RHS
  -- The issue is that h_factor sums over Perm (Fin P.card) but submatrixDet A Q P sums over Perm (Fin Q.card)
  -- We use hcard : P.card = Q.card to reindex
  
  -- Expand the determinants
  simp only [Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
  
  -- Reindex the first sum using hcard
  have h_reindex_A : ∑ α : Equiv.Perm (Fin P.card), 
      (Equiv.Perm.sign α : R) * ∏ j, A (Q.orderEmbOfFin (hcard.symm ▸ rfl) (α j)) (P.orderEmbOfFin rfl j) =
      ∑ σ : Equiv.Perm (Fin Q.card),
      (Equiv.Perm.sign σ : R) * ∏ i, A (Q.orderEmbOfFin rfl (σ i)) (P.orderEmbOfFin (hcard.symm ▸ rfl) i) := by
    apply Fintype.sum_bijective (Equiv.permCongr (finCongr hcard))
    · exact (Equiv.permCongr (finCongr hcard)).bijective
    · intro α
      congr 1
      · simp only [Equiv.Perm.sign_permCongr]
      · apply Finset.prod_equiv (finCongr hcard)
        · simp
        · intro i _
          simp only [Equiv.permCongr_apply, finCongr_apply, Finset.orderEmbOfFin_apply, finCongr_symm]
          congr 1
  
  -- Reindex the second sum using hcardC
  have h_reindex_B : ∑ β : Equiv.Perm (Fin Pᶜ.card), 
      (Equiv.Perm.sign β : R) * ∏ j, B (Qᶜ.orderEmbOfFin hcardC.symm (β j)) (Pᶜ.orderEmbOfFin rfl j) =
      ∑ σ : Equiv.Perm (Fin Qᶜ.card),
      (Equiv.Perm.sign σ : R) * ∏ i, B (Qᶜ.orderEmbOfFin rfl (σ i)) (Pᶜ.orderEmbOfFin (hcardC.symm ▸ rfl) i) := by
    apply Fintype.sum_bijective (Equiv.permCongr (finCongr hcardC))
    · exact (Equiv.permCongr (finCongr hcardC)).bijective
    · intro β
      congr 1
      · simp only [Equiv.Perm.sign_permCongr]
      · apply Finset.prod_equiv (finCongr hcardC)
        · simp
        · intro i _
          simp only [Equiv.permCongr_apply, finCongr_apply, Finset.orderEmbOfFin_apply, finCongr_symm]
          congr 1
  
  rw [h_reindex_A, h_reindex_B]

/-- The formula for det(A+B) as a double sum over subsets.
    (Theorem thm.det.det(A+B))
    Label: thm.det.det(A+B)

    This expands det(A+B) into terms involving submatrices of A and B.
    The formula contains det(A) and det(B) as special cases (when P=Q=[n] or P=Q=∅).

    Note: The statement uses `submatrixDet` helper to handle the cardinality constraints.

    The proof uses the following key steps (see det_add_expand_step1/2/3):
    1. Expand using Leibniz formula: det(A+B) = ∑_σ sign(σ) ∏_i (A+B)_{σ(i),i}
    2. Apply product rule: ∏(a+b) = ∑_P (∏_{i∈P} a_i)(∏_{i∈Pᶜ} b_i)
    3. Swap summation order and partition by Q = σ(P)
    4. Apply sum_perms_mapping_eq_det_product for each (P, Q) pair -/
theorem det_add_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) :
    (A + B).det = ∑ P : Finset (Fin n), ∑ Q : Finset (Fin n),
      if h : Q.card = P.card then
        (-1 : R) ^ (finsetSumFin P + finsetSumFin Q) *
        submatrixDet A Q P h *
        submatrixDet B Qᶜ Pᶜ (by simp [Finset.card_compl, h])
      else 0 := by
  rw [det_add_expand_step3]
  congr 1
  ext P
  congr 1
  ext Q
  by_cases hcard : Q.card = P.card
  · rw [dite_eq_left hcard]
    -- Use sum_perms_mapping_eq_det_product
    have h := sum_perms_mapping_eq_det_product A B P Q hcard.symm
    convert h using 2
  · rw [dite_eq_right hcard]
    rw [permsMapping_empty_of_card_ne P Q (fun h => hcard h.symm)]
    simp

/-!
## Minors of Diagonal Matrices (Lemma lem.det.minors-diag)

For a diagonal matrix D with entries d₁, d₂, ..., dₙ:

(a) det(sub_P^P D) = ∏_{i ∈ P} dᵢ  (principal minors are products of diagonal entries)
(b) If P ≠ Q with |P| = |Q|, then det(sub_P^Q D) = 0  (off-diagonal submatrices have zero det)
-/

/-- Part (a): Principal minors of a diagonal matrix are products of diagonal entries.
    (Lemma lem.det.minors-diag (a))
    Label: lem.det.minors-diag.a -/
theorem det_diagonal_submatrix_eq {n : ℕ} (d : Fin n → R) (P : Finset (Fin n)) :
    ((Matrix.diagonal d).submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det =
    ∏ i ∈ P, d i := by
  have h : (Matrix.diagonal d).submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl) =
           Matrix.diagonal (d ∘ P.orderEmbOfFin rfl) :=
    Matrix.submatrix_diagonal_embedding d (P.orderEmbOfFin rfl).toEmbedding
  rw [h, Matrix.det_diagonal]
  simp only [Function.comp]
  rw [Fintype.prod_equiv (P.orderIsoOfFin rfl).toEquiv
      (fun i => d (P.orderEmbOfFin rfl i)) (fun i => d i)]
  · exact Finset.prod_coe_sort P d
  · intro i
    simp [Finset.coe_orderIsoOfFin_apply]

/-- Part (b): Off-diagonal submatrices of a diagonal matrix have zero determinant.
    (Lemma lem.det.minors-diag (b))
    Label: lem.det.minors-diag.b -/
theorem det_diagonal_submatrix_off_diag {n : ℕ} (d : Fin n → R)
    (P Q : Finset (Fin n)) (hcard : P.card = Q.card) (hne : P ≠ Q) :
    ((Matrix.diagonal d).submatrix (P.orderEmbOfFin rfl)
      (Q.orderEmbOfFin (hcard ▸ rfl))).det = 0 := by
  -- Since P ≠ Q but |P| = |Q|, there exists some element in P but not in Q
  have hne' : ∃ x, x ∈ P ∧ x ∉ Q := by
    by_contra h
    push Not at h
    have hsub : P ⊆ Q := fun x hx => h x hx
    exact hne (Finset.eq_of_subset_of_card_le hsub (hcard ▸ le_refl _))
  obtain ⟨x, hxP, hxQ⟩ := hne'
  -- Get the row index i corresponding to x
  let i : Fin P.card := (P.orderIsoOfFin rfl).symm ⟨x, hxP⟩
  -- Apply det_eq_zero_of_row_eq_zero at row i
  apply det_eq_zero_of_row_eq_zero i
  intro j
  -- The submatrix at (i, j) is (diagonal d) (P.orderEmbOfFin rfl i) (Q.orderEmbOfFin ... j)
  simp only [submatrix_apply]
  -- P.orderEmbOfFin rfl i = x
  have hi : P.orderEmbOfFin rfl i = x := by
    simp [i, orderEmbOfFin, OrderIso.toOrderEmbedding]
  rw [hi]
  -- (diagonal d) x (Q.orderEmbOfFin ... j) = 0 because x ≠ Q.orderEmbOfFin ... j
  -- since x ∉ Q but Q.orderEmbOfFin ... j ∈ Q
  have hj_in_Q : Q.orderEmbOfFin (hcard ▸ rfl) j ∈ Q := Finset.orderEmbOfFin_mem _ _ _
  have hne_xj : x ≠ Q.orderEmbOfFin (hcard ▸ rfl) j := fun h => hxQ (h ▸ hj_in_Q)
  exact diagonal_apply_ne d hne_xj

/-!
## Determinant of A + D (Theorem thm.det.det(A+D))

When B = D is diagonal with entries d₁, ..., dₙ, the formula for det(A+B) simplifies:
  det(A+D) = ∑_{P ⊆ [n]} det(sub_P^P A) · ∏_{i ∈ [n]\P} dᵢ

The cross terms vanish because det(sub_P̃^Q̃ D) = 0 when P ≠ Q.
-/

/-- Simplified formula for det(A+D) when D is diagonal.
    (Theorem thm.det.det(A+D))
    Label: thm.det.det(A+D)

    This follows from det_add_sum by observing that off-diagonal submatrices
    of D have zero determinant. -/
theorem det_add_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (d : Fin n → R) :
    (A + Matrix.diagonal d).det =
    ∑ P : Finset (Fin n),
      ((A.submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det) *
      ∏ i ∈ Pᶜ, d i := by
  rw [det_add_sum]
  -- Simplify the double sum: only P = Q terms survive
  apply Finset.sum_congr rfl
  intro P _
  -- For each P, the inner sum over Q only has the P = P term
  have h1 : ∑ Q : Finset (Fin n),
      (if h : Q.card = P.card then
        (-1 : R) ^ (finsetSumFin P + finsetSumFin Q) *
        submatrixDet A Q P h *
        submatrixDet (diagonal d) Qᶜ Pᶜ (by simp [Finset.card_compl, h])
      else 0) =
      (A.submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det * ∏ i ∈ Pᶜ, d i := by
    -- The sum is over all Q, but only Q = P gives nonzero
    -- Use Finset.sum_eq_single
    rw [Finset.sum_eq_single P]
    · -- The P = P term
      rw [dite_eq_left (rfl : P.card = P.card)]
      -- (-1)^(finsetSumFin P + finsetSumFin P) = 1
      have hone : (-1 : R) ^ (finsetSumFin P + finsetSumFin P) = 1 := by
        rw [← two_mul, pow_mul]
        norm_num
      rw [hone, one_mul]
      -- submatrixDet A P P ... = (A.submatrix ...).det
      unfold submatrixDet
      -- The goal is to show the two submatrix expressions are equal
      -- They differ only in the proof terms, which don't affect values
      have h2 : ((diagonal d).submatrix (Pᶜ.orderEmbOfFin rfl) (Pᶜ.orderEmbOfFin rfl)).det =
          ∏ i ∈ Pᶜ, d i := det_diagonal_submatrix_eq d Pᶜ
      rw [h2]
    · -- For Q ≠ P, the term is zero
      intro Q _ hQP
      by_cases hcard : Q.card = P.card
      · rw [dite_eq_left hcard]
        -- submatrixDet (diagonal d) Qᶜ Pᶜ ... = 0 because Qᶜ ≠ Pᶜ
        have hne : Qᶜ ≠ Pᶜ := by
          intro h
          apply hQP
          exact compl_injective h
        -- Need to unfold submatrixDet and apply det_diagonal_submatrix_off_diag
        unfold submatrixDet
        have hcard' : Qᶜ.card = Pᶜ.card := by simp [Finset.card_compl, hcard]
        rw [det_diagonal_submatrix_off_diag d Qᶜ Pᶜ hcard' hne]
        ring
      · rw [dite_eq_right hcard]
    · intro hP
      exact (hP (mem_univ P)).elim
  exact h1

/-!
## Determinant of x + D (Proposition prop.det.x+ai)

For the matrix F with entries F_{i,j} = x + d_i [i=j], i.e.,
  F = (x x ... x)
      (x x+d₂ ... x)
      (⋮  ⋮  ⋱  ⋮)
      (x x ... x+dₙ)

we have:
  det F = d₁d₂...dₙ + x ∑_{i=1}^n d₁d₂...d̂ᵢ...dₙ

where d̂ᵢ means "omit dᵢ".

This is useful in graph theory (e.g., Laplacian matrices).
-/

/-- The matrix with x on all entries except diagonal which has x + dᵢ.
    (Used in Proposition prop.det.x+ai) -/
def constPlusDiagMatrix {n : ℕ} (x : R) (d : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => x + if i = j then d i else 0

/-- The set of fixed points of a permutation. -/
def fixedPoints' {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => σ i = i)

/-- The identity permutation has all points fixed. -/
lemma fixedPoints'_one {n : ℕ} : fixedPoints' (1 : Equiv.Perm (Fin n)) = Finset.univ := by
  simp [fixedPoints']

/-- Key lemma: the product for a permutation σ in the determinant expansion.
    For constPlusDiagMatrix, entry (σ(i), i) equals x + d_i if σ(i) = i, else x.
    So the product splits into x^{non-fixed} · ∏_{fixed} (x + d_i). -/
lemma prod_constPlusDiagMatrix_perm {n : ℕ} (x : R) (d : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    ∏ i, constPlusDiagMatrix x d (σ i) i =
    x ^ (n - (fixedPoints' σ).card) * ∏ i ∈ fixedPoints' σ, (x + d i) := by
  -- Rewrite each factor based on whether i is a fixed point
  have h1 : ∏ i : Fin n, constPlusDiagMatrix x d (σ i) i =
            ∏ i, (x + if σ i = i then d i else 0) := by
    congr 1; ext i
    simp only [constPlusDiagMatrix]
    split_ifs with h <;> simp [h]
  rw [h1]
  -- Split the product over fixed and non-fixed points
  have h2 : ∏ i : Fin n, (x + if σ i = i then d i else 0) =
            (∏ i ∈ fixedPoints' σ, (x + if σ i = i then d i else 0)) *
            (∏ i ∈ (Finset.univ \ fixedPoints' σ), (x + if σ i = i then d i else 0)) := by
    rw [← Finset.prod_union (Finset.disjoint_sdiff)]
    apply Finset.prod_congr; simp; intro _ _; rfl
  rw [h2]
  -- On fixed points: x + d_i
  have h_fixed : ∏ i ∈ fixedPoints' σ, (x + if σ i = i then d i else 0) =
                 ∏ i ∈ fixedPoints' σ, (x + d i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [fixedPoints', Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [hi]
  -- On non-fixed points: just x
  have h_nonfixed : ∏ i ∈ Finset.univ \ fixedPoints' σ, (x + if σ i = i then d i else 0) =
                    x ^ (n - (fixedPoints' σ).card) := by
    have h_eq : ∀ i ∈ Finset.univ \ fixedPoints' σ, (x + if σ i = i then d i else 0) = x := by
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, fixedPoints', Finset.mem_filter] at hi
      simp [hi]
    rw [Finset.prod_congr rfl h_eq, Finset.prod_const]
    congr 1
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [fixedPoints']
  rw [h_fixed, h_nonfixed]
  ring

/-- A permutation cannot have exactly 1 non-fixed point.
    If σ(i) ≠ i, then σ(σ(i)) = i ≠ σ(i), so σ(i) is also non-fixed. -/
lemma card_nonfixed_ne_one {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Finset.univ \ fixedPoints' σ).card ≠ 1 := by
  intro h
  rw [Finset.card_eq_one] at h
  obtain ⟨i, hi⟩ := h
  have hi' : i ∈ Finset.univ \ fixedPoints' σ := by rw [hi]; exact Finset.mem_singleton_self i
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, fixedPoints', Finset.mem_filter] at hi'
  -- σ(i) is also non-fixed since σ(σ(i)) = i ≠ σ(i)
  have hσi : σ i ∈ Finset.univ \ fixedPoints' σ := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, fixedPoints', Finset.mem_filter]
    intro h_eq
    have : σ i = i := by
      have := congr_arg σ.symm h_eq
      simp at this
      exact this
    exact hi' this
  -- But non-fixed = {i}, so σ(i) = i, contradiction
  rw [hi] at hσi
  simp at hσi
  exact hi' hσi

/-- The constant x matrix (all entries equal to x). -/
def constMatrix {n : ℕ} (x : R) : Matrix (Fin n) (Fin n) R :=
  fun _ _ => x

/-- constPlusDiagMatrix = constMatrix + diagonal d -/
lemma constPlusDiagMatrix_eq_add {n : ℕ} (x : R) (d : Fin n → R) :
    constPlusDiagMatrix x d = constMatrix x + Matrix.diagonal d := by
  ext i j
  simp only [constPlusDiagMatrix, constMatrix, Matrix.add_apply, Matrix.diagonal_apply]

/-- For a submatrix of a constant matrix, if the submatrix has size ≥ 2, its determinant is 0.
    This is because all rows are identical. -/
lemma det_submatrix_constMatrix_eq_zero {n : ℕ} (x : R) (P : Finset (Fin n)) (hP : 2 ≤ P.card) :
    ((constMatrix x).submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det = 0 := by
  have hrows : ∀ i j : Fin P.card,
      (constMatrix x).submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl) i =
      (constMatrix x).submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl) j := by
    intro i j
    ext k
    simp [constMatrix, Matrix.submatrix]
  have h0 : (⟨0, by omega⟩ : Fin P.card) ≠ ⟨1, by omega⟩ := by simp
  exact Matrix.det_zero_of_row_eq h0 (hrows _ _)

/-- For a 1×1 constant matrix, the determinant is x. -/
lemma det_submatrix_constMatrix_singleton {n : ℕ} (x : R) (P : Finset (Fin n))
    (hP : P.card = 1) :
    ((constMatrix x).submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det = x := by
  haveI : Unique (Fin P.card) := by rw [hP]; infer_instance
  rw [det_unique]
  simp [constMatrix, Matrix.submatrix]

/-- For a 0×0 matrix, the determinant is 1. -/
lemma det_submatrix_constMatrix_empty {n : ℕ} (x : R) (P : Finset (Fin n))
    (hP : P.card = 0) :
    ((constMatrix x).submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det = 1 := by
  haveI : IsEmpty (Fin P.card) := by rw [hP]; exact Fin.isEmpty
  rw [det_isEmpty]

/-- Determinant of the matrix with constant x plus diagonal d.
    (Proposition prop.det.x+ai)
    Label: prop.det.x+ai

    det F = d₁d₂...dₙ + x ∑_{i=1}^n d₁...d̂ᵢ...dₙ

    **Proof:**
    Write F = A + D where A is the constant x matrix and D = diagonal(d).
    By det_add_diagonal: det(A+D) = ∑_P det(sub_P^P A) · ∏_{i∈Pᶜ} d_i

    For |P| ≥ 2: det(sub_P^P A) = 0 (constant matrix with identical rows)
    For |P| = 1, P = {i}: det(sub_P^P A) = x (1×1 matrix)
    For |P| = 0, P = ∅: det(sub_P^P A) = 1 (0×0 matrix)

    So only the P = ∅ term and the P = {i} terms survive:
    det F = 1 · ∏_i d_i + ∑_i x · ∏_{j≠i} d_j = ∏_i d_i + x · ∑_i ∏_{j≠i} d_j -/
theorem det_const_add_diagonal {n : ℕ} (x : R) (d : Fin n → R) :
    (constPlusDiagMatrix x d).det =
    (∏ i : Fin n, d i) + x * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, d j := by
  rw [constPlusDiagMatrix_eq_add, det_add_diagonal]
  -- |P| ≥ 2 terms are all 0
  have h_ge2 : ∀ P : Finset (Fin n), 2 ≤ P.card →
      ((constMatrix x).submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det *
      ∏ i ∈ Pᶜ, d i = 0 := fun P hP => by
    rw [det_submatrix_constMatrix_eq_zero x P hP, zero_mul]
  -- The only |P| = 0 term is P = ∅
  have h_empty : ((constMatrix x).submatrix ((∅ : Finset (Fin n)).orderEmbOfFin rfl)
      ((∅ : Finset (Fin n)).orderEmbOfFin rfl)).det *
      ∏ i ∈ (∅ : Finset (Fin n))ᶜ, d i = ∏ i : Fin n, d i := by
    rw [det_submatrix_constMatrix_empty x ∅ card_empty, one_mul, compl_empty]
  -- For |P| = 1, i.e., P = {i} for some i
  have h_singleton : ∀ i : Fin n,
      ((constMatrix x).submatrix (({i} : Finset (Fin n)).orderEmbOfFin rfl)
        (({i} : Finset (Fin n)).orderEmbOfFin rfl)).det *
      ∏ j ∈ ({i} : Finset (Fin n))ᶜ, d j = x * ∏ j ∈ Finset.univ.erase i, d j := fun i => by
    rw [det_submatrix_constMatrix_singleton x {i} (card_singleton i)]
    congr 1
    apply Finset.prod_congr
    · ext j
      simp [mem_compl, mem_singleton, mem_erase, mem_univ]
    · intro _ _; rfl
  -- Now rewrite the sum
  have h_sum : ∑ P : Finset (Fin n),
      ((constMatrix x).submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det *
      ∏ i ∈ Pᶜ, d i =
    (∏ i : Fin n, d i) + (∑ i : Fin n, x * ∏ j ∈ Finset.univ.erase i, d j) := by
    rw [← Finset.insert_erase (mem_univ (∅ : Finset (Fin n)))]
    rw [Finset.sum_insert (by simp)]
    rw [h_empty]
    congr 1
    have h_partition : (Finset.univ : Finset (Finset (Fin n))).erase ∅ =
        ((Finset.univ : Finset (Finset (Fin n))).filter (fun P => P.card = 1)) ∪
        ((Finset.univ : Finset (Finset (Fin n))).filter (fun P => 2 ≤ P.card)) := by
      ext P
      simp only [mem_erase, mem_univ, ne_eq, mem_union, mem_filter, true_and]
      constructor
      · intro hP
        by_cases hc : P.card = 0
        · simp [card_eq_zero.mp hc] at hP
        · by_cases hc' : P.card = 1
          · left; exact hc'
          · right; omega
      · intro h
        rcases h with h | h
        · simp only [and_true]
          intro hne; rw [hne, card_empty] at h; omega
        · simp only [and_true]
          intro hne; rw [hne, card_empty] at h; omega
    rw [h_partition]
    rw [Finset.sum_union]
    · have h_sum_ge2 : ∑ P ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun P => 2 ≤ P.card),
          ((constMatrix x).submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det *
          ∏ i ∈ Pᶜ, d i = 0 := Finset.sum_eq_zero fun P hP => by
        simp only [mem_filter, mem_univ, true_and] at hP
        exact h_ge2 P hP
      rw [h_sum_ge2, add_zero]
      have h_singletons : (Finset.univ : Finset (Finset (Fin n))).filter (fun P => P.card = 1) =
          Finset.univ.image (fun i : Fin n => {i}) := by
        ext P
        simp only [mem_filter, mem_univ, true_and, mem_image, card_eq_one]
        constructor
        · intro ⟨a, ha⟩; exact ⟨a, ha.symm⟩
        · intro ⟨a, ha⟩; exact ⟨a, ha.symm⟩
      rw [h_singletons]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i _
        exact h_singleton i
      · intro i _ j _ hij
        simp only [Finset.singleton_inj] at hij
        exact hij
    · simp only [disjoint_left, mem_filter, mem_univ, true_and]
      intro P h1 h2
      omega
  rw [h_sum, mul_sum]

/-!
## Characteristic Polynomial Coefficients (Proposition prop.det.charpol-explicit)

The characteristic polynomial of A is det(xI - A) (or det(A + xI) up to sign).
Its coefficients are sums of principal minors:

  det(A + xI) = ∑_{k=0}^n (∑_{P ⊆ [n], |P|=n-k} det(sub_P^P A)) · x^k

The coefficient of x^{n-k} is the sum of all k×k principal minors of A.
-/

/-- The coefficient of x^k in det(A + xI) is a sum of principal minors (first form).
    (Proposition prop.det.charpol-explicit)
    Label: prop.det.charpol-explicit

    This gives an explicit formula for the coefficients of the characteristic polynomial:
      det(A + xI) = ∑_{P ⊆ [n]} det(sub_P^P A) · x^{n-|P|}
    
    See also `det_charPoly_coeff'` for the equivalent form grouped by powers of x. -/
theorem det_charPoly_coeff {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (x : R) :
    (A + x • (1 : Matrix (Fin n) (Fin n) R)).det =
    ∑ P : Finset (Fin n),
      ((A.submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det) * x ^ (n - P.card) := by
  rw [smul_one_eq_diagonal, det_add_diagonal]
  congr 1
  ext P
  congr 1
  rw [Finset.prod_const, Finset.card_compl, Fintype.card_fin]

/-- The coefficient of x^k in det(A + xI) is the sum of principal minors of size (n-k).
    (Proposition prop.det.charpol-explicit, second form)
    Label: prop.det.charpol-explicit

    This regroups the sum by powers of x:
      det(A + xI) = ∑_{k=0}^n (∑_{P ⊆ [n], |P|=n-k} det(sub_P^P A)) · x^k

    This form makes explicit that the coefficient of x^k is the sum of all 
    (n-k) × (n-k) principal minors of A. In particular:
    - The coefficient of x^n is 1 (the only principal minor of size 0 is det(∅) = 1)
    - The coefficient of x^{n-1} is Tr(A) (the sum of 1×1 principal minors)
    - The constant term is det(A) (the only principal minor of size n) -/
theorem det_charPoly_coeff' {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (x : R) :
    (A + x • (1 : Matrix (Fin n) (Fin n) R)).det =
    ∑ k ∈ Finset.range (n + 1),
      (∑ P ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun P => P.card = n - k),
        (A.submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det) * x ^ k := by
  rw [det_charPoly_coeff]
  -- Define the fiber function that groups subsets by n - card
  let fiber (k : ℕ) : Finset (Finset (Fin n)) := 
    (Finset.univ : Finset (Finset (Fin n))).filter (fun P => P.card = n - k)
  -- Show that univ is the disjoint union of fibers over range (n+1)
  have huniv : (Finset.univ : Finset (Finset (Fin n))) = 
      (Finset.range (n + 1)).biUnion fiber := by
    ext P
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, 
               true_and, fiber]
    constructor
    · intro _
      use n - P.card
      constructor
      · have hP := Finset.card_le_card (Finset.subset_univ P)
        simp at hP
        omega
      · have hP := Finset.card_le_card (Finset.subset_univ P)
        simp at hP
        omega
    · intro ⟨k, _, heq⟩
      exact True.intro
  have hdisj : Set.PairwiseDisjoint (Finset.range (n + 1) : Set ℕ) fiber := by
    intro k1 hk1 k2 hk2 hne
    simp only [Function.onFun, Finset.disjoint_left, fiber, Finset.mem_filter, 
               Finset.mem_univ, true_and]
    intro P h1 h2
    have hk1' : k1 < n + 1 := Finset.mem_range.mp hk1
    have hk2' : k2 < n + 1 := Finset.mem_range.mp hk2
    omega
  rw [huniv, Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n + 1 := Finset.mem_range.mp hk
  -- Show that the filter on biUnion equals fiber k
  have hfilter_eq : ((Finset.range (n + 1)).biUnion fiber).filter (fun P => P.card = n - k) =
      fiber k := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, fiber, Finset.mem_univ, true_and]
    constructor
    · intro ⟨⟨j, hj, hPj⟩, hPk⟩
      exact hPk
    · intro hP
      exact ⟨⟨k, hk', hP⟩, hP⟩
  -- The inner sum is over fiber k, and the RHS filter is over biUnion
  -- Rewrite the RHS filter to fiber k
  have hsum_rhs : (∑ P ∈ ((Finset.range (n + 1)).biUnion fiber).filter (fun P => P.card = n - k),
      (A.submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det) =
      ∑ P ∈ fiber k, (A.submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det := by
    exact Finset.sum_congr hfilter_eq (fun _ _ => rfl)
  rw [hsum_rhs]
  -- Now: ∑ P ∈ fiber k, det * x^(n-P.card) = (∑ P ∈ fiber k, det) * x^k
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hP
  have hPcard : P.card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ P)
    simp at this
    exact this
  have heq2 : n - P.card = k := by omega
  rw [heq2]

/-!
## Pascal Matrix Determinant (Proposition prop.det.pascal-LU)

The Pascal matrix P_n has entries P_{i,j} = C(i+j-2, i-1), i.e.,
  P = (C(0,0) C(1,0) ... C(n-1,0))
      (C(1,1) C(2,1) ... C(n,1))
      (⋮      ⋮      ⋱   ⋮)
      (C(n-1,n-1) C(n,n-1) ... C(2n-2,n-1))

For n=4, this is:
  (1 1 1 1)
  (1 2 3 4)
  (1 3 6 10)
  (1 4 10 20)

The determinant is 1, which can be proven via LU decomposition.
-/

/-- Key identity for the LU decomposition: ∑_k C(m,k) * C(n,k) = C(m+n, n).
    This is a consequence of Vandermonde's identity. -/
private lemma sum_choose_mul_choose (m n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), m.choose k * n.choose k = (m + n).choose n := by
  rw [Nat.add_choose_eq m n n]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have hk' : k ≤ n := Nat.lt_succ_iff.mp hk
  rw [Nat.choose_symm hk']

/-- The Pascal matrix with entries C(i+j, i).
    (Proposition prop.det.pascal-LU)

    Note: We use 0-indexing, so entry (i,j) is C(i+j, i). -/
def pascalMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => (i.val + j.val).choose i.val

@[simp]
theorem pascalMatrix_apply (n : ℕ) (i j : Fin n) :
    pascalMatrix n i j = (i.val + j.val).choose i.val := rfl

/-- The lower triangular factor L in the LU decomposition of the Pascal matrix.
    L_{i,k} = C(i, k) -/
def pascalLowerTriangular (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i k => i.val.choose k.val

@[simp]
theorem pascalLowerTriangular_apply (n : ℕ) (i k : Fin n) :
    pascalLowerTriangular n i k = i.val.choose k.val := rfl

/-- The upper triangular factor U in the LU decomposition of the Pascal matrix.
    U_{k,j} = C(j, k) -/
def pascalUpperTriangular (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun k j => j.val.choose k.val

@[simp]
theorem pascalUpperTriangular_apply (n : ℕ) (k j : Fin n) :
    pascalUpperTriangular n k j = j.val.choose k.val := rfl

/-- The Pascal matrix factors as L * U where L and U are lower and upper triangular.
    This is the LU decomposition of the Pascal matrix.

    The proof uses Vandermonde's identity: C(i+j, i) = ∑_k C(i,k) * C(j,k). -/
theorem pascal_eq_LU (n : ℕ) :
    (pascalMatrix n).map (↑· : ℕ → ℤ) =
    (pascalLowerTriangular n).map (↑· : ℕ → ℤ) *
    (pascalUpperTriangular n).map (↑· : ℕ → ℤ) := by
  ext i j
  simp only [pascalMatrix, pascalLowerTriangular, pascalUpperTriangular, map_apply, mul_apply]
  symm
  -- First convert to natural number sum
  have h1 : ∑ k : Fin n, (↑(i.val.choose k.val) : ℤ) * ↑(j.val.choose k.val)
          = ↑(∑ k : Fin n, i.val.choose k.val * j.val.choose k.val) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro k _
    norm_cast
  rw [h1]
  -- Now convert Fin n sum to range n sum
  have h2 : ∑ k : Fin n, i.val.choose k.val * j.val.choose k.val
          = ∑ k ∈ Finset.range n, i.val.choose k * j.val.choose k := by
    rw [Fin.sum_univ_eq_sum_range (fun k => i.val.choose k * j.val.choose k)]
  rw [h2]
  -- Extend to range (j.val + 1)
  have h3 : ∑ k ∈ Finset.range n, i.val.choose k * j.val.choose k
          = ∑ k ∈ Finset.range (j.val + 1), i.val.choose k * j.val.choose k := by
    symm
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      have := j.isLt
      omega
    · intro k hkn hkj
      simp only [Finset.mem_range, not_lt] at *
      have : j.val.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega : j.val < k)
      simp [this]
  rw [h3]
  -- Apply the key identity
  rw [sum_choose_mul_choose]
  -- Finally use symmetry
  rw [Nat.choose_symm_add]

/-- The lower triangular factor L has all diagonal entries equal to 1. -/
theorem pascalLowerTriangular_diag (n : ℕ) (i : Fin n) :
    pascalLowerTriangular n i i = 1 := by
  simp [pascalLowerTriangular, Nat.choose_self]

/-- The upper triangular factor U has all diagonal entries equal to 1. -/
theorem pascalUpperTriangular_diag (n : ℕ) (i : Fin n) :
    pascalUpperTriangular n i i = 1 := by
  simp [pascalUpperTriangular, Nat.choose_self]

/-- The lower triangular factor L is indeed lower triangular. -/
theorem pascalLowerTriangular_is_lower (n : ℕ) (i k : Fin n) (h : i < k) :
    pascalLowerTriangular n i k = 0 := by
  simp only [pascalLowerTriangular]
  exact Nat.choose_eq_zero_of_lt (Fin.val_fin_lt.mpr h)

/-- The upper triangular factor U is indeed upper triangular. -/
theorem pascalUpperTriangular_is_upper (n : ℕ) (k j : Fin n) (h : k > j) :
    pascalUpperTriangular n k j = 0 := by
  simp only [pascalUpperTriangular]
  exact Nat.choose_eq_zero_of_lt (Fin.val_fin_lt.mpr h)

/-- The determinant of the lower triangular factor is 1.

    The proof uses that L is lower triangular with 1s on the diagonal,
    so its determinant is the product of diagonal entries, which is 1. -/
theorem det_pascalLowerTriangular (n : ℕ) :
    ((pascalLowerTriangular n).map (↑· : ℕ → ℤ)).det = 1 := by
  have hLower : ∀ i j : Fin n, i < j → ((pascalLowerTriangular n).map (↑· : ℕ → ℤ)) i j = 0 := by
    intro i j hij
    simp only [map_apply, pascalLowerTriangular]
    have : i.val.choose j.val = 0 := Nat.choose_eq_zero_of_lt (Fin.val_fin_lt.mpr hij)
    simp [this]
  have hT : ((pascalLowerTriangular n).map (↑· : ℕ → ℤ))ᵀ.BlockTriangular id := by
    intro i j hij
    simp only [transpose_apply]
    exact hLower j i hij
  rw [← det_transpose]
  rw [det_of_isUpperTriangular hT]
  simp only [transpose_apply, map_apply]
  apply Finset.prod_eq_one
  intro i _
  simp only [pascalLowerTriangular_diag, Nat.cast_one]

/-- The determinant of the upper triangular factor is 1.

    The proof uses that U is upper triangular with 1s on the diagonal,
    so its determinant is the product of diagonal entries, which is 1. -/
theorem det_pascalUpperTriangular (n : ℕ) :
    ((pascalUpperTriangular n).map (↑· : ℕ → ℤ)).det = 1 := by
  have hUpper : ((pascalUpperTriangular n).map (↑· : ℕ → ℤ)).BlockTriangular id := by
    intro i j hij
    simp only [map_apply, pascalUpperTriangular]
    have : j.val.choose i.val = 0 := Nat.choose_eq_zero_of_lt (Fin.val_fin_lt.mpr hij)
    simp [this]
  rw [det_of_isUpperTriangular hUpper]
  simp only [map_apply]
  apply Finset.prod_eq_one
  intro i _
  simp [pascalUpperTriangular]

/-- The Pascal matrix has determinant 1.
    (Proposition prop.det.pascal-LU)
    Label: prop.det.pascal-LU

    This follows from the LU decomposition: det(P) = det(L) · det(U) = 1 · 1 = 1.

    The proof strategy:
    1. Factor P = L * U where L is lower triangular and U is upper triangular
    2. Both L and U have 1s on the diagonal (since C(n,n) = 1)
    3. Determinant of a triangular matrix is the product of diagonal entries
    4. Therefore det(P) = det(L) * det(U) = 1 * 1 = 1 -/
theorem det_pascal_matrix (n : ℕ) :
    ((pascalMatrix n).map (↑· : ℕ → ℤ)).det = 1 := by
  rw [pascal_eq_LU, Matrix.det_mul, det_pascalLowerTriangular, det_pascalUpperTriangular]
  ring

/-!
## Additional Lemmas

Some auxiliary results used in the main theorems.
-/

/-- The complement of a finset has the expected cardinality. -/
theorem finset_compl_card {n : ℕ} (P : Finset (Fin n)) :
    Pᶜ.card = n - P.card := by
  simp [Finset.card_compl]

/-- The sum of elements in a finset and its complement equals the sum of all elements. -/
theorem finsetSumFin_add_compl {n : ℕ} (P : Finset (Fin n)) :
    finsetSumFin P + finsetSumFin Pᶜ = finsetSumFin (Finset.univ : Finset (Fin n)) := by
  unfold finsetSumFin
  rw [← Finset.sum_union (disjoint_compl_right)]
  congr 1
  ext x
  simp

end CauchyBinet

end AlgebraicCombinatorics
