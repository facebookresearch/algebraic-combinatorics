/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.SymmetricFunctions.SchurBasics
import AlgebraicCombinatorics.SymmetricFunctions.PieriJacobiTrudi

/-!
# Equivalence Between SSYT Definitions

This file establishes the equivalence between the two definitions of semistandard
Young tableaux (SSYT) in this project:

1. **SchurBasics.SSYT**: Uses `entry : Fin N × ℕ → Fin N` with a support condition
   that entries outside the Young diagram are 0. This representation is more
   flexible for proofs involving cell coordinates.

2. **SymmetricFunctions.SSYT**: Uses dependent types `entries : (i : Fin N) →
   (j : Fin (lam.parts i)) → Fin N`. This representation is more type-safe but
   harder to work with for some proofs.

## Main Results

* `npartitionEquiv`: An equivalence between the two NPartition types
* `ssytEquiv`: An equivalence between the two SSYT types
* `toSchurBasicsSSYT`: Convert from SymmetricFunctions.SSYT to SchurBasics.SSYT
* `toSFSSYT`: Convert from SchurBasics.SSYT to SymmetricFunctions.SSYT
* `schur_eq_schurPoly_int`: Equivalence of Schur polynomial definitions
* `schurPoly_eq_schur`: Corollary for composing theorems from different files

## Implementation Notes

The two definitions also use different `NPartition` types (with fields `monotone`
vs `weaklyDecreasing`), so we also provide conversions between these.

The SkewSSYT definitions have a similar relationship and are also addressed here.

## Schur Polynomial Equivalence

The project has three Schur polynomial definitions:
- `SchurBasics.schurPoly`: Takes `NPartition N` with `[NeZero N]`, coefficient ring `ℤ`
- `SymmetricFunctions.schur`: Takes `SymmetricFunctions.NPartition N`, generic ring `R`
- `AlgebraicCombinatorics.schurPoly`: Takes `Fin N → ℕ` with `IsNPartition`, generic ring `R`

This file provides equivalence theorems between the first two definitions.
The third definition (in LittlewoodRichardson.lean) is related via the `IsNPartition`
predicate, which is equivalent to the bundled `NPartition` types.

## Design Rationale

Both SSYT definitions are retained in their original files. This file provides the
equivalence infrastructure for code that needs both representations.

The two representations serve different purposes:
- `SchurBasics.SSYT`: Better for proofs using cell coordinates, extends `YoungTableau`
- `SymmetricFunctions.SSYT`: Better for type-safe code, no `[NeZero N]` requirement

## NPartition Types

This file bridges between the two `NPartition` types in this project:
- `NPartition N` (shared, from NPartition.lean) - uses `antitone` field
- `SymmetricFunctions.NPartition N` (local, from PieriJacobiTrudi.lean) - uses
  `weaklyDecreasing` field

Both equivalences are provided for API convenience:
- `SSYTEquiv.npartitionEquiv`: shared → local
- `SymmetricFunctions.NPartition.equivShared`: local → shared

## Tags

semistandard Young tableau, SSYT, equivalence, Young diagram, Schur polynomial
-/

noncomputable section

open Finset BigOperators MvPolynomial

namespace SSYTEquiv

variable {N : ℕ} [NeZero N]

/-! ## NPartition Conversions

The two files use different NPartition types with different field names:
- `NPartition N` (shared, from NPartition.lean) - uses `antitone` field
  (with `monotone` alias theorem for compatibility)
- `SymmetricFunctions.NPartition N` (local, from PieriJacobiTrudi.lean) - uses
  `weaklyDecreasing` field

We provide conversions between them. These conversions are trivial (just renaming fields).

**Note**: PieriJacobiTrudi.lean also provides `NPartition.equivShared` which
is the inverse of `npartitionEquiv` defined here. Both are retained for API convenience:
- `npartitionEquiv`: shared → local
- `NPartition.equivShared`: local → shared
-/

/-- Convert from SchurBasics.NPartition to SymmetricFunctions.NPartition.
    Note: SchurBasics.lean now uses the shared NPartition from NPartition.lean,
    which has `antitone` as its field name (with `monotone` as an alias theorem). -/
def schurBasicsNPartition_to_SF (lam : NPartition N) : SymmetricFunctions.NPartition N where
  parts := lam.parts
  weaklyDecreasing := lam.monotone

/-- Convert from SymmetricFunctions.NPartition to SchurBasics.NPartition.
    Note: SchurBasics.lean now uses the shared NPartition from NPartition.lean,
    which has `antitone` as its field name. -/
def sfNPartition_to_SchurBasics (lam : SymmetricFunctions.NPartition N) : NPartition N where
  parts := lam.parts
  antitone := lam.weaklyDecreasing

omit [NeZero N] in
/-- The conversions are inverses (direction 1). -/
@[simp]
theorem sfNPartition_schurBasics_id (lam : NPartition N) :
    sfNPartition_to_SchurBasics (schurBasicsNPartition_to_SF lam) = lam := by
  cases lam; rfl

omit [NeZero N] in
/-- The conversions are inverses (direction 2). -/
@[simp]
theorem schurBasics_sfNPartition_id (lam : SymmetricFunctions.NPartition N) :
    schurBasicsNPartition_to_SF (sfNPartition_to_SchurBasics lam) = lam := by
  cases lam; rfl

omit [NeZero N] in
/-- The parts are preserved by conversion. -/
@[simp]
theorem schurBasicsNPartition_to_SF_parts (lam : NPartition N) :
    (schurBasicsNPartition_to_SF lam).parts = lam.parts := rfl

omit [NeZero N] in
@[simp]
theorem sfNPartition_to_SchurBasics_parts (lam : SymmetricFunctions.NPartition N) :
    (sfNPartition_to_SchurBasics lam).parts = lam.parts := rfl

omit [NeZero N] in
/-- The NPartition types are equivalent. This is the symmetric of
    `SymmetricFunctions.NPartition.equivShared` from PieriJacobiTrudi.lean.
    See `npartitionEquiv_eq_equivShared_symm` for the relationship. -/
def npartitionEquiv : NPartition N ≃ SymmetricFunctions.NPartition N where
  toFun := schurBasicsNPartition_to_SF
  invFun := sfNPartition_to_SchurBasics
  left_inv := sfNPartition_schurBasics_id
  right_inv := schurBasics_sfNPartition_id

omit [NeZero N] in
@[simp]
theorem npartitionEquiv_apply (lam : NPartition N) :
    npartitionEquiv lam = schurBasicsNPartition_to_SF lam := rfl

omit [NeZero N] in
@[simp]
theorem npartitionEquiv_symm_apply (lam : SymmetricFunctions.NPartition N) :
    npartitionEquiv.symm lam = sfNPartition_to_SchurBasics lam := rfl

omit [NeZero N] in
/-- The equivalence `npartitionEquiv` is the symmetric of `NPartition.equivShared`
    from PieriJacobiTrudi.lean. This means code can use either:
    - `npartitionEquiv lam` to go from shared → local
    - `lam.toShared` to go from local → shared -/
theorem npartitionEquiv_eq_equivShared_symm :
    (npartitionEquiv (N := N)) = SymmetricFunctions.NPartition.equivShared.symm := by
  ext lam
  rfl

/-! ## SSYT Conversions

The main equivalence between the two SSYT definitions.
-/

omit [NeZero N] in
/-- Helper lemma: column-strict property extends to non-adjacent rows for SF SSYT.
    If j is in rows i₁ and i₂ with i₁ < i₂, then T.entries i₁ j < T.entries i₂ j. -/
theorem sf_ssyt_col_strict_nonadjacent {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) {i₁ i₂ : Fin N} {j : ℕ}
    (hj₁ : j < lam.parts i₁) (hj₂ : j < lam.parts i₂) (hi : i₁ < i₂) :
    T.entries i₁ ⟨j, hj₁⟩ < T.entries i₂ ⟨j, hj₂⟩ := by
  -- Use strong induction on the distance between rows
  obtain ⟨d, hd_eq⟩ : ∃ d, i₂.val - i₁.val = d + 1 := ⟨i₂.val - i₁.val - 1, by omega⟩
  induction d using Nat.strong_induction_on generalizing i₁ i₂ with
  | _ d ih =>
    by_cases hd : d = 0
    · -- Base case: adjacent rows (i₂ = i₁ + 1)
      have hi₂_eq : i₂.val = i₁.val + 1 := by omega
      have hi_lt : i₁.val + 1 < N := by omega
      have hi₂_fin : i₂ = ⟨i₁.val + 1, hi_lt⟩ := Fin.ext hi₂_eq
      subst hi₂_fin
      exact T.colStrict i₁ hi_lt ⟨j, hj₁⟩ hj₂
    · -- Inductive case: i₂.val - i₁.val > 1
      have hi₂_gt : i₂.val > i₁.val + 1 := by omega
      -- Find intermediate row i' = i₁.val + 1
      let i' : Fin N := ⟨i₁.val + 1, by omega⟩
      have hi₁_i' : i₁ < i' := by simp only [i', Fin.lt_def]; omega
      have hi'_i₂ : i' < i₂ := by simp only [i', Fin.lt_def]; omega
      -- j is in row i' too (by partition monotonicity)
      have hj' : j < lam.parts i' :=
        Nat.lt_of_lt_of_le hj₂ (lam.weaklyDecreasing i' i₂ (Nat.le_of_lt hi'_i₂))
      -- Apply T.colStrict for i₁ → i'
      have h1 : T.entries i₁ ⟨j, hj₁⟩ < T.entries i' ⟨j, hj'⟩ := by
        have hi_lt : i₁.val + 1 < N := by omega
        have hj'_alt : j < lam.parts ⟨i₁.val + 1, hi_lt⟩ := hj'
        have hcol := T.colStrict i₁ hi_lt ⟨j, hj₁⟩ hj'_alt
        convert hcol using 2
      -- Apply IH for i' → i₂
      have hdiff' : i₂.val - i'.val - 1 < d := by simp only [i']; omega
      have hdiff'_eq : i₂.val - i'.val = (i₂.val - i'.val - 1) + 1 := by omega
      have h2 : T.entries i' ⟨j, hj'⟩ < T.entries i₂ ⟨j, hj₂⟩ :=
        ih (i₂.val - i'.val - 1) hdiff' hj' hj₂ hi'_i₂ hdiff'_eq
      exact lt_trans h1 h2

/-- Convert from SymmetricFunctions.SSYT to SchurBasics.SSYT.

The key insight is that the dependent type `(j : Fin (lam.parts i))` in the SF
definition corresponds to cells `(i, j)` where `j < lam.parts i`, which is exactly
the membership condition for the Young diagram in SchurBasics. -/
def toSchurBasicsSSYT {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) : SSYT (sfNPartition_to_SchurBasics lam) where
  entry := fun c =>
    if h : c.2 < lam.parts c.1 then
      T.entries c.1 ⟨c.2, h⟩
    else
      0
  support := fun c hc => by
    rw [NPartition.mem_youngDiagram] at hc
    simp only [sfNPartition_to_SchurBasics_parts] at hc
    simp [hc]
  row_weak := fun i j₁ j₂ hj₂ hlt => by
    rw [NPartition.mem_youngDiagram] at hj₂
    simp only [sfNPartition_to_SchurBasics_parts] at hj₂
    have hj₁ : j₁ < lam.parts i := Nat.lt_of_lt_of_le hlt (Nat.le_of_lt hj₂)
    simp only [hj₁, hj₂, ↓reduceDIte]
    exact T.rowWeak i ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ (Nat.le_of_lt hlt)
  col_strict := fun i₁ i₂ j hj₂ hi => by
    rw [NPartition.mem_youngDiagram] at hj₂
    simp only [sfNPartition_to_SchurBasics_parts] at hj₂
    have hj₁ : j < lam.parts i₁ := by
      calc j < lam.parts i₂ := hj₂
        _ ≤ lam.parts i₁ := lam.weaklyDecreasing i₁ i₂ (Nat.le_of_lt hi)
    simp only [hj₁, hj₂, ↓reduceDIte]
    exact sf_ssyt_col_strict_nonadjacent T hj₁ hj₂ hi

/-- Convert from SchurBasics.SSYT to SymmetricFunctions.SSYT.

This requires extracting the entries at valid positions from the total function. -/
def toSFSSYT {lam : NPartition N}
    (T : SSYT lam) : SymmetricFunctions.SSYT (schurBasicsNPartition_to_SF lam) where
  entries := fun i j => T.entry (i, j.val)
  rowWeak := fun i j k hjk => by
    have hk : (i, k.val) ∈ lam.youngDiagram := by
      rw [NPartition.mem_youngDiagram]
      exact k.isLt
    have hj_lt : j.val < k.val ∨ j.val = k.val := Nat.lt_or_eq_of_le hjk
    rcases hj_lt with hlt | heq
    · exact T.row_weak i j.val k.val hk hlt
    · rw [heq]
  colStrict := fun i hi j hj => by
    simp only [schurBasicsNPartition_to_SF_parts] at hj
    have hmem : (⟨i.val + 1, hi⟩, j.val) ∈ lam.youngDiagram := by
      rw [NPartition.mem_youngDiagram]
      exact hj
    have hlt : i < ⟨i.val + 1, hi⟩ := by simp only [Fin.lt_def]; omega
    exact T.col_strict i ⟨i.val + 1, hi⟩ j.val hmem hlt

omit [NeZero N] in
/-- Two SSYTs in the SymmetricFunctions namespace are equal if their entries are equal. -/
theorem SSYT_eq_of_entries_eq {lam : SymmetricFunctions.NPartition N}
    {T1 T2 : SymmetricFunctions.SSYT lam}
    (h : T1.entries = T2.entries) : T1 = T2 := by
  cases T1; cases T2
  simp only at h
  subst h
  rfl

/-- The conversions are inverses (direction 1). -/
theorem toSFSSYT_toSchurBasicsSSYT {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) :
    toSFSSYT (toSchurBasicsSSYT T) = T := by
  apply SSYT_eq_of_entries_eq
  funext i j
  simp only [toSFSSYT, toSchurBasicsSSYT]
  have hj_lt : j.val < lam.parts i := j.isLt
  simp only [hj_lt, ↓reduceDIte]
  rfl

/-- The conversions are inverses (direction 2). -/
theorem toSchurBasicsSSYT_toSFSSYT {lam : NPartition N}
    (T : SSYT lam) :
    toSchurBasicsSSYT (toSFSSYT T) = T := by
  apply SSYT.ext
  intro c
  simp only [toSchurBasicsSSYT, toSFSSYT]
  by_cases h : c.2 < lam.parts c.1
  · simp only [schurBasicsNPartition_to_SF_parts, h, ↓reduceDIte]
  · simp only [schurBasicsNPartition_to_SF_parts, h, ↓reduceDIte]
    have hc : c ∉ lam.youngDiagram := by
      rw [NPartition.mem_youngDiagram]
      exact h
    exact (T.toYoungTableau.support c hc).symm

/-- The equivalence between the two SSYT types. -/
def ssytEquiv (lam : SymmetricFunctions.NPartition N) :
    SymmetricFunctions.SSYT lam ≃ SSYT (sfNPartition_to_SchurBasics lam) where
  toFun := toSchurBasicsSSYT
  invFun := toSFSSYT
  left_inv := toSFSSYT_toSchurBasicsSSYT
  right_inv := toSchurBasicsSSYT_toSFSSYT

/-! ## Skew SSYT Conversions

Similar conversions for skew semistandard Young tableaux.
-/

/-- Convert a SymmetricFunctions.SkewPartition to a SchurBasics-style skew partition
    (as a pair of NPartitions). -/
def sfSkewPartition_to_SchurBasics (s : SymmetricFunctions.SkewPartition N) :
    NPartition N × NPartition N :=
  (sfNPartition_to_SchurBasics s.outer, sfNPartition_to_SchurBasics s.inner)

omit [NeZero N] in
/-- The outer partition contains the inner partition after conversion. -/
theorem sfSkewPartition_contained (s : SymmetricFunctions.SkewPartition N) :
    (sfSkewPartition_to_SchurBasics s).2 ≤ (sfSkewPartition_to_SchurBasics s).1 := by
  intro i
  simp only [sfSkewPartition_to_SchurBasics, sfNPartition_to_SchurBasics_parts]
  exact s.contained i

/-- Convert from SymmetricFunctions.SkewSSYT to SchurBasics.SkewSSYT. -/
def toSchurBasicsSkewSSYT {s : SymmetricFunctions.SkewPartition N}
    (T : SymmetricFunctions.SkewSSYT s) :
    SkewSSYT (sfSkewPartition_to_SchurBasics s).1 (sfSkewPartition_to_SchurBasics s).2 where
  entry := fun c =>
    if h : s.inner.parts c.1 ≤ c.2 ∧ c.2 < s.outer.parts c.1 then
      T.entries c.1 ⟨c.2 - s.inner.parts c.1, by omega⟩
    else
      0
  support := fun c hc => by
    rw [mem_skewYoungDiagram] at hc
    simp only [sfSkewPartition_to_SchurBasics, sfNPartition_to_SchurBasics_parts] at hc
    push Not at hc
    by_cases h1 : s.inner.parts c.1 ≤ c.2
    · have h2 := hc h1
      simp only [h1, Nat.not_lt.mpr h2, and_false, ↓reduceDIte]
    · simp only [h1, false_and, ↓reduceDIte]
  row_weak := fun i j₁ j₂ hj₁ hj₂ hlt => by
    rw [mem_skewYoungDiagram] at hj₁ hj₂
    simp only [sfSkewPartition_to_SchurBasics, sfNPartition_to_SchurBasics_parts] at hj₁ hj₂
    have hcond₁ : s.inner.parts i ≤ j₁ ∧ j₁ < s.outer.parts i := hj₁
    have hcond₂ : s.inner.parts i ≤ j₂ ∧ j₂ < s.outer.parts i := hj₂
    simp only [hcond₁, hcond₂, and_self, ↓reduceDIte]
    have hk₁_lt : j₁ - s.inner.parts i < s.outer.parts i - s.inner.parts i := by omega
    have hk₂_lt : j₂ - s.inner.parts i < s.outer.parts i - s.inner.parts i := by omega
    have hjk : (⟨j₁ - s.inner.parts i, hk₁_lt⟩ : Fin _) ≤ ⟨j₂ - s.inner.parts i, hk₂_lt⟩ := by
      simp only [Fin.le_def]; omega
    exact T.rowWeak i ⟨j₁ - s.inner.parts i, hk₁_lt⟩ ⟨j₂ - s.inner.parts i, hk₂_lt⟩ hjk
  col_strict := fun i₁ i₂ j hj₁ hj₂ hi => by
    rw [mem_skewYoungDiagram] at hj₁ hj₂
    simp only [sfSkewPartition_to_SchurBasics, sfNPartition_to_SchurBasics_parts] at hj₁ hj₂
    have hcond₁ : s.inner.parts i₁ ≤ j ∧ j < s.outer.parts i₁ := hj₁
    have hcond₂ : s.inner.parts i₂ ≤ j ∧ j < s.outer.parts i₂ := hj₂
    simp only [hcond₁, hcond₂, and_self, ↓reduceDIte]
    have hk₁_lt : j - s.inner.parts i₁ < s.outer.parts i₁ - s.inner.parts i₁ := by omega
    have hk₂_lt : j - s.inner.parts i₂ < s.outer.parts i₂ - s.inner.parts i₂ := by omega
    -- Need to show T.entries i₁ k₁ < T.entries i₂ k₂
    -- where k₁ = j - s.inner.parts i₁ and k₂ = j - s.inner.parts i₂
    -- The column condition: s.inner.parts i₁ + k₁ = s.inner.parts i₂ + k₂ = j
    have hcol_eq : s.inner.parts i₁ + (j - s.inner.parts i₁) =
                   s.inner.parts i₂ + (j - s.inner.parts i₂) := by omega
    exact T.colStrict_nonadjacent i₁ i₂ hi ⟨j - s.inner.parts i₁, hk₁_lt⟩
      ⟨j - s.inner.parts i₂, hk₂_lt⟩ hcol_eq

/-! ## Schur Polynomial Equivalences

The following theorems establish that the different Schur polynomial definitions
are equivalent.

**Summary of definitions**:
- `SchurBasics.schurPoly`: Takes `NPartition N` with `[NeZero N]`, coefficient ring `ℤ`
- `SymmetricFunctions.schur`: Takes `SymmetricFunctions.NPartition N`, generic coefficient ring `R`

The key insight is that both definitions sum over the same mathematical objects (SSYT),
just represented differently. The `ssytEquiv` equivalence provides the bijection on tableaux,
and we show that monomials are preserved under this bijection.
-/

/-- The monomial associated to a SymmetricFunctions.SSYT equals the monomial of the
    corresponding SchurBasics.SSYT (as a product over cells).

    This is the key lemma for proving Schur polynomial equivalence.
    The proof shows that the product over cells is preserved by the bijection. -/
theorem toSchurBasicsSSYT_monomial_eq {R : Type*} [CommRing R]
    {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) :
    (T.toMonomial : MvPolynomial (Fin N) R) =
    ∏ c : { c // c ∈ (sfNPartition_to_SchurBasics lam).youngDiagram },
      X ((toSchurBasicsSSYT T).entry c.val) := by
  -- T.toMonomial = ∏ i, ∏ j : Fin (lam.parts i), X (T.entries i j)
  -- RHS = ∏ c ∈ youngDiagram, X ((toSchurBasicsSSYT T).entry c)
  -- Both are products over the same cells, with the same values
  -- The proof requires showing the bijection between (i, j : Fin (lam.parts i))
  -- and cells c ∈ youngDiagram preserves the monomial factors
  unfold SymmetricFunctions.SSYT.toMonomial
  -- First, show that the entry values match under the bijection
  have h_entry : ∀ (i : Fin N) (j : Fin (lam.parts i)),
      (X (T.entries i j) : MvPolynomial (Fin N) R) =
      X ((toSchurBasicsSSYT T).entry (i, j.val)) := by
    intro i j
    simp only [toSchurBasicsSSYT]
    have hj_lt : j.val < lam.parts i := j.isLt
    simp only [hj_lt, ↓reduceDIte]
  -- Rewrite the LHS using Fintype.prod_sigma'
  rw [← Fintype.prod_sigma']
  -- Define the equivalence
  let e : (Σ i : Fin N, Fin (lam.parts i)) ≃
      { c // c ∈ (sfNPartition_to_SchurBasics lam).youngDiagram } := {
    toFun := fun ⟨i, j⟩ => ⟨(i, j.val), by
      rw [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact j.isLt⟩
    invFun := fun ⟨c, hc⟩ => ⟨c.1, ⟨c.2, by
      rw [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts] at hc
      exact hc⟩⟩
    left_inv := fun ⟨i, j⟩ => rfl
    right_inv := fun ⟨c, hc⟩ => rfl
  }
  -- Now use the equivalence
  rw [Fintype.prod_equiv e]
  intro ⟨i, j⟩
  simp only [e, Equiv.coe_fn_mk]
  rw [h_entry i j]

/-- Convert a SymmetricFunctions.SSYT to a Filling for SchurBasics.schurPoly. -/
def sfSSYT_to_Filling {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) : Filling (sfNPartition_to_SchurBasics lam) :=
  fun c => T.entries c.val.1 ⟨c.val.2, by
    have hc := c.prop
    rw [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts] at hc
    exact hc⟩

/-- Convert a Filling (satisfying SSYT conditions) to a SymmetricFunctions.SSYT. -/
def filling_to_sfSSYT {lam : SymmetricFunctions.NPartition N}
    (f : Filling (sfNPartition_to_SchurBasics lam))
    (hf : isSSYTFillingYoung (sfNPartition_to_SchurBasics lam) f) :
    SymmetricFunctions.SSYT lam where
  entries := fun i j => f ⟨(i, j.val), by
    simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
    exact j.isLt⟩
  rowWeak := fun i j k hjk => by
    have hj_mem : (i, j.val) ∈ (sfNPartition_to_SchurBasics lam).youngDiagram := by
      simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact Nat.lt_of_le_of_lt hjk k.isLt
    have hk_mem : (i, k.val) ∈ (sfNPartition_to_SchurBasics lam).youngDiagram := by
      simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact k.isLt
    rcases Nat.lt_or_eq_of_le hjk with hlt | heq
    · exact hf.1 ⟨(i, j.val), hj_mem⟩ ⟨(i, k.val), hk_mem⟩ rfl hlt
    · have hj_eq_k : j = k := Fin.ext heq
      rw [hj_eq_k]
  colStrict := fun i hi j hj => by
    have hj_lt : j.val < lam.parts ⟨i.val + 1, hi⟩ := hj
    have hj_i : j.val < lam.parts i := Nat.lt_of_lt_of_le hj_lt (lam.weaklyDecreasing i ⟨i.val + 1, hi⟩ (by simp [Fin.le_def]))
    have hc1 : ((i, j.val) : Fin N × ℕ) ∈ (sfNPartition_to_SchurBasics lam).youngDiagram := by
      simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact hj_i
    have hc2 : ((⟨i.val + 1, hi⟩, j.val) : Fin N × ℕ) ∈ (sfNPartition_to_SchurBasics lam).youngDiagram := by
      simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact hj_lt
    exact hf.2 ⟨(i, j.val), hc1⟩ ⟨(⟨i.val + 1, hi⟩, j.val), hc2⟩ rfl (by simp [Fin.lt_def])

/-- The conversion from SF SSYT to Filling satisfies the SSYT condition. -/
theorem sfSSYT_to_Filling_isSSYT {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) :
    isSSYTFillingYoung (sfNPartition_to_SchurBasics lam) (sfSSYT_to_Filling T) := by
  constructor
  · -- Row-weak condition: same row (c1.1 = c2.1), c1.2 < c2.2
    intro c1 c2 hrow hcol
    simp only [sfSSYT_to_Filling]
    have hc1_mem := c1.prop
    have hc2_mem := c2.prop
    simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts] at hc1_mem hc2_mem
    -- hrow says c1.val.1 = c2.val.1 (same row)
    -- hcol says c1.val.2 < c2.val.2 (c1 is to the left of c2)
    have hc1_lt : c1.val.2 < lam.parts c1.val.1 := hc1_mem
    have hc2_lt : c2.val.2 < lam.parts c2.val.1 := hc2_mem
    -- Since c1.1 = c2.1, we can rewrite
    have hc1_lt' : c1.val.2 < lam.parts c2.val.1 := by rw [← hrow]; exact hc1_lt
    -- Apply rowWeak: entries at (c2.1, c1.2) ≤ entries at (c2.1, c2.2)
    have h := T.rowWeak c2.val.1 ⟨c1.val.2, hc1_lt'⟩ ⟨c2.val.2, hc2_lt⟩ (Nat.le_of_lt hcol)
    -- Need to show: T.entries c1.1 ⟨c1.2, _⟩ ≤ T.entries c2.1 ⟨c2.2, _⟩
    -- Since c1.1 = c2.1, rewrite using hrow
    cases c1 with | mk c1val c1prop =>
    cases c2 with | mk c2val c2prop =>
    simp only [Subtype.coe_mk] at hrow hcol hc1_lt hc2_lt hc1_lt' h ⊢
    cases c1val with | mk c1fst c1snd =>
    cases c2val with | mk c2fst c2snd =>
    simp only at hrow
    simp only at hrow hcol hc1_lt hc2_lt hc1_lt' h ⊢
    subst hrow
    exact h
  · -- Column-strict condition: same column (c1.2 = c2.2), c1.1 < c2.1
    intro c1 c2 hcol hrow
    simp only [sfSSYT_to_Filling]
    have hc1_mem := c1.prop
    have hc2_mem := c2.prop
    simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts] at hc1_mem hc2_mem
    -- hcol says c1.val.2 = c2.val.2 (same column)
    -- hrow says c1.val.1 < c2.val.1 (c1 is above c2)
    have hc1_lt : c1.val.2 < lam.parts c1.val.1 := hc1_mem
    have hc2_lt : c2.val.2 < lam.parts c2.val.1 := hc2_mem
    -- Since c1.2 = c2.2 and c2.2 < lam.parts c2.1, we have c1.2 < lam.parts c2.1
    have hc1_lt' : c1.val.2 < lam.parts c2.val.1 := by rw [hcol]; exact hc2_lt
    -- Apply sf_ssyt_col_strict_nonadjacent
    have h := sf_ssyt_col_strict_nonadjacent T hc1_lt hc1_lt' hrow
    -- Need to show: T.entries c1.1 ⟨c1.2, _⟩ < T.entries c2.1 ⟨c2.2, _⟩
    convert h using 3
    · exact hcol.symm

/-- The conversions are inverses (SF SSYT → Filling → SF SSYT). -/
theorem filling_sfSSYT_id {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) :
    filling_to_sfSSYT (sfSSYT_to_Filling T) (sfSSYT_to_Filling_isSSYT T) = T := by
  apply SSYT_eq_of_entries_eq
  funext i j
  simp only [filling_to_sfSSYT, sfSSYT_to_Filling]

/-- The conversions are inverses (Filling → SF SSYT → Filling). -/
theorem sfSSYT_filling_id {lam : SymmetricFunctions.NPartition N}
    (f : Filling (sfNPartition_to_SchurBasics lam))
    (hf : isSSYTFillingYoung (sfNPartition_to_SchurBasics lam) f) :
    sfSSYT_to_Filling (filling_to_sfSSYT f hf) = f := by
  funext c
  simp only [sfSSYT_to_Filling, filling_to_sfSSYT]

/-- The monomial of an SF SSYT equals the monomial of the corresponding Filling. -/
theorem sfSSYT_monomial_eq_filling {lam : SymmetricFunctions.NPartition N}
    (T : SymmetricFunctions.SSYT lam) :
    (T.toMonomial : MvPolynomial (Fin N) ℤ) =
    fillingMonomialYoung (sfSSYT_to_Filling T) := by
  unfold SymmetricFunctions.SSYT.toMonomial fillingMonomialYoung sfSSYT_to_Filling
  -- Both are products over the cells of the Young diagram
  -- LHS: ∏ i, ∏ j : Fin (lam.parts i), X (T.entries i j)
  -- RHS: ∏ c : { c // c ∈ youngDiagram }, X (T.entries c.1 ⟨c.2, _⟩)
  rw [← Fintype.prod_sigma']
  -- Define the equivalence between (Σ i, Fin (lam.parts i)) and { c // c ∈ youngDiagram }
  let e : (Σ i : Fin N, Fin (lam.parts i)) ≃
      { c // c ∈ (sfNPartition_to_SchurBasics lam).youngDiagram } := {
    toFun := fun ⟨i, j⟩ => ⟨(i, j.val), by
      rw [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact j.isLt⟩
    invFun := fun ⟨c, hc⟩ => ⟨c.1, ⟨c.2, by
      rw [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts] at hc
      exact hc⟩⟩
    left_inv := fun ⟨i, j⟩ => rfl
    right_inv := fun ⟨c, hc⟩ => rfl
  }
  rw [Fintype.prod_equiv e]
  intro ⟨i, j⟩
  rfl

/-- The Schur polynomial from PieriJacobiTrudi equals the Schur polynomial from SchurBasics
    when specialized to coefficient ring ℤ.

    This theorem establishes that `SymmetricFunctions.schur lam` (over ℤ) equals
    `schurPoly (sfNPartition_to_SchurBasics lam)`.

    **Note**: This theorem requires `[NeZero N]` because `schurPoly` requires it.
    For the generic ring version, see `schur_eq_schurPoly_map`. -/
theorem schur_eq_schurPoly_int (lam : SymmetricFunctions.NPartition N) :
    (SymmetricFunctions.schur (R := ℤ) lam : MvPolynomial (Fin N) ℤ) =
    schurPoly (sfNPartition_to_SchurBasics lam) := by
  -- Both are sums over SSYT, we need to show the sums are equal
  -- schur lam = ∑ T ∈ ssytFinset lam, T.toMonomial
  -- schurPoly lam' = ∑ f ∈ ssytFillingsYoung lam', fillingMonomialYoung f
  unfold SymmetricFunctions.schur schurPoly ssytFillingsYoung
  -- Use Finset.sum_bij to establish the bijection
  apply Finset.sum_bij (fun T _ => sfSSYT_to_Filling T)
  · -- hi: sfSSYT_to_Filling maps ssytFinset to ssytFillingsYoung
    intro T _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact sfSSYT_to_Filling_isSSYT T
  · -- i_inj: sfSSYT_to_Filling is injective
    intro T1 _ T2 _ heq
    apply SSYT_eq_of_entries_eq
    funext i j
    have h1 := congrFun heq ⟨(i, j.val), by
      simp only [NPartition.mem_youngDiagram, sfNPartition_to_SchurBasics_parts]
      exact j.isLt⟩
    simp only [sfSSYT_to_Filling] at h1
    exact h1
  · -- i_surj: sfSSYT_to_Filling is surjective onto ssytFillingsYoung
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    refine ⟨filling_to_sfSSYT f hf, SymmetricFunctions.ssytFinset_mem lam _, ?_⟩
    exact sfSSYT_filling_id f hf
  · -- h: monomials are preserved
    intro T _
    exact sfSSYT_monomial_eq_filling T

/-- Corollary: The two Schur polynomial definitions are equal up to NPartition conversion.

    This is the main user-facing theorem for composing results from different files. -/
theorem schurPoly_eq_schur (lam : NPartition N) :
    (schurPoly lam : MvPolynomial (Fin N) ℤ) =
    SymmetricFunctions.schur (schurBasicsNPartition_to_SF lam) := by
  rw [schur_eq_schurPoly_int]
  simp only [sfNPartition_schurBasics_id]

end SSYTEquiv

end
