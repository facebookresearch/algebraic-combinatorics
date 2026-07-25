/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import AlgebraicCombinatorics.SymmetricFunctions.PieriJacobiTrudi

/-!
# Jacobi--Trudi with independent row and alphabet sizes

The original API in `PieriJacobiTrudi` uses one natural number both for the number
of rows of a skew partition and for the tableau alphabet.  This file starts the
compatibility-preserving generalization in which:

* `M` indexes rows and the Jacobi--Trudi matrix;
* `N` indexes tableau entries and polynomial variables.

The old definitions remain unchanged.  The `M = N` equivalences below make the
new API interoperable with them.
-/

open Finset BigOperators Matrix MvPolynomial

namespace SymmetricFunctions

variable {M N : ℕ} {R : Type*} [CommRing R]

/-- A semistandard tableau of an `M`-row skew shape with entries in `Fin N`. -/
structure SkewSSYTMN (N : ℕ) (s : SkewPartition M) where
  /-- The entries in each row, indexed by their offset from the inner shape. -/
  entries :
    (i : Fin M) → Fin (s.outer.parts i - s.inner.parts i) → Fin N
  /-- Entries weakly increase along rows. -/
  rowWeak :
    ∀ i : Fin M, ∀ j k : Fin (s.outer.parts i - s.inner.parts i),
      j ≤ k → entries i j ≤ entries i k
  /-- Entries strictly increase down adjacent rows whenever both cells exist. -/
  colStrict :
    ∀ i : Fin M, ∀ hi : i.val + 1 < M,
      ∀ k : Fin (s.outer.parts i - s.inner.parts i),
      ∀ _hcol :
        s.inner.parts i + k.val + 1 > s.inner.parts ⟨i.val + 1, hi⟩ ∧
          s.inner.parts i + k.val + 1 ≤ s.outer.parts ⟨i.val + 1, hi⟩,
      let k' := s.inner.parts i + k.val - s.inner.parts ⟨i.val + 1, hi⟩
      ∀ hk' :
        k' <
          s.outer.parts ⟨i.val + 1, hi⟩ -
            s.inner.parts ⟨i.val + 1, hi⟩,
        entries i k < entries ⟨i.val + 1, hi⟩ ⟨k', hk'⟩

namespace SkewSSYTMN

/-- Two generalized skew tableaux are equal when their entries are equal. -/
@[ext]
theorem ext {s : SkewPartition M} {T U : SkewSSYTMN N s}
    (h : T.entries = U.entries) : T = U := by
  cases T
  cases U
  simp only at h
  subst h
  rfl

/-- The monomial obtained by multiplying one variable for every tableau cell. -/
noncomputable def toMonomial {s : SkewPartition M} (T : SkewSSYTMN N s) :
    MvPolynomial (Fin N) R :=
  ∏ i : Fin M, ∏ k : Fin (s.outer.parts i - s.inner.parts i),
    X (T.entries i k)

end SkewSSYTMN

/-- An unrestricted filling of an `M`-row skew shape by letters in `Fin N`. -/
abbrev SkewFillingMN (N : ℕ) (s : SkewPartition M) :=
  (i : Fin M) → Fin (s.outer.parts i - s.inner.parts i) → Fin N

instance skewFillingMN_fintype (N : ℕ) (s : SkewPartition M) :
    Fintype (SkewFillingMN N s) :=
  inferInstance

/-- Row semistandardness for a generalized skew filling. -/
def isRowWeakMN (s : SkewPartition M) (f : SkewFillingMN N s) : Prop :=
  ∀ i : Fin M, ∀ j k : Fin (s.outer.parts i - s.inner.parts i),
    j ≤ k → f i j ≤ f i k

/-- Adjacent-row column strictness for a generalized skew filling. -/
def isColStrictMN (s : SkewPartition M) (f : SkewFillingMN N s) : Prop :=
  ∀ i : Fin M, ∀ hi : i.val + 1 < M,
    ∀ k : Fin (s.outer.parts i - s.inner.parts i),
    ∀ _hcol :
      s.inner.parts i + k.val + 1 > s.inner.parts ⟨i.val + 1, hi⟩ ∧
        s.inner.parts i + k.val + 1 ≤ s.outer.parts ⟨i.val + 1, hi⟩,
    let k' := s.inner.parts i + k.val - s.inner.parts ⟨i.val + 1, hi⟩
    ∀ hk' :
      k' <
        s.outer.parts ⟨i.val + 1, hi⟩ -
          s.inner.parts ⟨i.val + 1, hi⟩,
      f i k < f ⟨i.val + 1, hi⟩ ⟨k', hk'⟩

/-- Semistandardness for a generalized skew filling. -/
def isSSYTFillingMN (s : SkewPartition M) (f : SkewFillingMN N s) : Prop :=
  isRowWeakMN s f ∧ isColStrictMN s f

instance isRowWeakMN_decidable (s : SkewPartition M) (f : SkewFillingMN N s) :
    Decidable (isRowWeakMN s f) :=
  Fintype.decidableForallFintype

instance isColStrictMN_decidable (s : SkewPartition M) (f : SkewFillingMN N s) :
    Decidable (isColStrictMN s f) :=
  Fintype.decidableForallFintype

instance isSSYTFillingMN_decidable (s : SkewPartition M) (f : SkewFillingMN N s) :
    Decidable (isSSYTFillingMN s f) :=
  instDecidableAnd

/-- Turn a semistandard filling into a bundled generalized tableau. -/
def fillingToSkewSSYTMN {s : SkewPartition M} (f : SkewFillingMN N s)
    (hf : isSSYTFillingMN s f) : SkewSSYTMN N s where
  entries := f
  rowWeak := hf.1
  colStrict := hf.2

/-- The finite collection of all generalized skew tableaux of a fixed shape. -/
noncomputable def skewSSYTMNFinset (N : ℕ) (s : SkewPartition M) :
    Finset (SkewSSYTMN N s) :=
  (Finset.univ.filter (isSSYTFillingMN s)).attach.map
    ⟨fun f => fillingToSkewSSYTMN f.1 (Finset.mem_filter.mp f.2).2,
      fun f g h => by
        apply Subtype.ext
        apply _root_.funext
        intro i
        apply _root_.funext
        intro k
        exact congrFun (congrFun (congrArg SkewSSYTMN.entries h) i) k⟩

/-- Every generalized skew tableau occurs in `skewSSYTMNFinset`. -/
theorem skewSSYTMNFinset_mem (s : SkewPartition M) (T : SkewSSYTMN N s) :
    T ∈ skewSSYTMNFinset N s := by
  simp only [skewSSYTMNFinset, Finset.mem_map, Finset.mem_attach, true_and,
    Subtype.exists]
  refine ⟨T.entries, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨T.rowWeak, T.colStrict⟩
  · cases T
    rfl

/-- Adjacent column strictness implies column strictness between arbitrary rows. -/
theorem SkewSSYTMN.colStrict_nonadjacent {s : SkewPartition M}
    (T : SkewSSYTMN N s) (i j : Fin M) (hij : i < j)
    (k : Fin (s.outer.parts i - s.inner.parts i))
    (k' : Fin (s.outer.parts j - s.inner.parts j))
    (hcol_eq : s.inner.parts i + k.val = s.inner.parts j + k'.val) :
    T.entries i k < T.entries j k' := by
  obtain ⟨d, hd_eq⟩ : ∃ d, j.val - i.val = d + 1 :=
    ⟨j.val - i.val - 1, by omega⟩
  induction d using Nat.strong_induction_on generalizing i j k k' with
  | _ d ih =>
    by_cases hd : d = 0
    · have hj_eq : j.val = i.val + 1 := by omega
      have hi_lt : i.val + 1 < M := by omega
      have hj_fin : j = ⟨i.val + 1, hi_lt⟩ := by
        apply Fin.ext
        exact hj_eq
      subst hj_fin
      have hcol :
          s.inner.parts i + k.val + 1 >
              s.inner.parts ⟨i.val + 1, hi_lt⟩ ∧
            s.inner.parts i + k.val + 1 ≤
              s.outer.parts ⟨i.val + 1, hi_lt⟩ := by
        constructor <;> omega
      let k''_val :=
        s.inner.parts i + k.val - s.inner.parts ⟨i.val + 1, hi_lt⟩
      have hk''_eq : k''_val = k'.val := by omega
      have hk''_lt :
          k''_val <
            s.outer.parts ⟨i.val + 1, hi_lt⟩ -
              s.inner.parts ⟨i.val + 1, hi_lt⟩ := by
        rw [hk''_eq]
        exact k'.isLt
      have hres := T.colStrict i hi_lt k hcol hk''_lt
      convert hres using 2
      apply Fin.ext
      exact hk''_eq.symm
    · have hj_gt : j.val > i.val + 1 := by omega
      let j' : Fin M := ⟨j.val - 1, by omega⟩
      have hij' : i < j' := by simp only [j', Fin.lt_def]; omega
      have hj'j : j' < j := by simp only [j', Fin.lt_def]; omega
      let k''_val := s.inner.parts i + k.val - s.inner.parts j'
      have hk''_lt :
          k''_val < s.outer.parts j' - s.inner.parts j' := by
        simp only [k''_val]
        have hinner : s.inner.parts j' ≤ s.inner.parts i :=
          s.inner.weaklyDecreasing i j' (le_of_lt hij')
        have houter : s.outer.parts j ≤ s.outer.parts j' :=
          s.outer.weaklyDecreasing j' j (le_of_lt hj'j)
        omega
      let k'' : Fin (s.outer.parts j' - s.inner.parts j') :=
        ⟨k''_val, hk''_lt⟩
      have hcol_eq' :
          s.inner.parts i + k.val = s.inner.parts j' + k''.val := by
        simp only [k'', k''_val]
        have hinner : s.inner.parts j' ≤ s.inner.parts i :=
          s.inner.weaklyDecreasing i j' (le_of_lt hij')
        omega
      have hdiff' : j'.val - i.val - 1 < d := by
        simp only [j']
        omega
      have hdiff'_eq : j'.val - i.val = (j'.val - i.val - 1) + 1 := by
        omega
      have h₁ : T.entries i k < T.entries j' k'' :=
        ih (j'.val - i.val - 1) hdiff' i j' hij' k k'' hcol_eq'
          hdiff'_eq
      have hcol_eq'' :
          s.inner.parts j' + k''.val = s.inner.parts j + k'.val := by
        rw [← hcol_eq', hcol_eq]
      have hdiff'' : j.val - j'.val - 1 < d := by
        simp only [j']
        omega
      have hdiff''_eq : j.val - j'.val = (j.val - j'.val - 1) + 1 := by
        simp only [j']
        omega
      have h₂ : T.entries j' k'' < T.entries j k' :=
        ih (j.val - j'.val - 1) hdiff'' j' j hj'j k'' k' hcol_eq''
          hdiff''_eq
      exact lt_trans h₁ h₂

/-- The skew Schur polynomial of an `M`-row shape in `N` variables. -/
noncomputable def skewSchurMN (N : ℕ) (s : SkewPartition M) :
    MvPolynomial (Fin N) R :=
  ∑ T ∈ skewSSYTMNFinset N s, T.toMonomial

/-- Complete homogeneous functions with the negative-index convention. -/
noncomputable def jacobiTrudiMatrixHMN (N : ℕ) (lam mu : Fin M → ℕ) :
    Matrix (Fin M) (Fin M) (MvPolynomial (Fin N) R) :=
  fun i j => hsymmExt (N := N) (R := R)
    ((lam i : ℤ) - (mu j : ℤ) - (i.val : ℤ) + (j.val : ℤ))

/-! ## The independent-size path/tableau correspondence -/

/-- The rectangular path tuple from the foundational Jacobi--Trudi module. -/
abbrev NipatMN (N : ℕ) (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :=
  RectNipat N lam mu hlam hmu hcontained

namespace NipatMN

/-- The product of the weights of the component paths. -/
noncomputable def weight {lam mu : Fin M → ℕ}
    {hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : NipatMN N lam mu hlam hmu hcontained) :
    MvPolynomial (Fin N) R :=
  RectNipat.weight np

@[ext]
theorem ext {lam mu : Fin M → ℕ}
    {hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    {p q : NipatMN N lam mu hlam hmu hcontained}
    (h : p.paths = q.paths) : p = q := by
  cases p
  cases q
  simp only at h
  subst h
  rfl

end NipatMN

private theorem list_isChain_getElem_le_getElem_of_le_MN
    {α : Type*} [Preorder α] {l : List α} (h : l.IsChain (· ≤ ·))
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    l[i] ≤ l[j] := by
  induction j with
  | zero => simp_all
  | succ j ih =>
    by_cases heq : i = j + 1
    · simp [heq]
    · by_cases hij' : i ≤ j
      · have hj' : j < l.length := by omega
        have h₁ := ih hj' hij'
        rw [List.isChain_iff_getElem] at h
        exact h₁.trans (h j hj)
      · omega

/-- Build one tableau path from the entries in a row. -/
def mkLatticePathFromEntriesMN (lam mu i : ℕ)
    (entries : Fin (lam - mu) → Fin N)
    (hrowWeak :
      ∀ j k : Fin (lam - mu), j ≤ k → entries j ≤ entries k) :
    LatticePath (N := N) ((mu : ℤ) - i) ((lam : ℤ) - i) where
  eastStepHeights := List.ofFn entries
  weaklyIncreasing := by
    rw [List.isChain_iff_pairwise, List.pairwise_ofFn]
    intro j k hjk
    exact hrowWeak j k (le_of_lt hjk)
  length_eq := by simp

/-- Turn an independent-size path tuple into its skew tableau. -/
noncomputable def nipatMNToSSYT {lam mu : Fin M → ℕ}
    {hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : NipatMN N lam mu hlam hmu hcontained) :
    SkewSSYTMN N
      ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ where
  entries := fun i k => (np.paths i).eastStepHeights.get ⟨k.val, by
    rw [(np.paths i).length_eq]
    simp only [sub_sub_sub_cancel_right]
    omega⟩
  rowWeak := fun i j k hjk => by
    simp only [List.get_eq_getElem]
    exact list_isChain_getElem_le_getElem_of_le_MN
      (np.paths i).weaklyIncreasing
      (by
        rw [(np.paths i).length_eq]
        simp only [sub_sub_sub_cancel_right]
        simp)
      (by
        rw [(np.paths i).length_eq]
        simp only [sub_sub_sub_cancel_right]
        simp)
      hjk
  colStrict := fun i hi k hcol hk' => by
    simp only [List.get_eq_getElem]
    change mu i + k.val + 1 > mu ⟨i.val + 1, hi⟩ ∧
      mu i + k.val + 1 ≤ lam ⟨i.val + 1, hi⟩ at hcol
    change mu i + k.val - mu ⟨i.val + 1, hi⟩ <
      lam ⟨i.val + 1, hi⟩ - mu ⟨i.val + 1, hi⟩ at hk'
    have hij : i < (⟨i.val + 1, hi⟩ : Fin M) := by
      simp only [Fin.lt_def]
      omega
    have hk :
        k.val < (np.paths i).eastStepHeights.length := by
      have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
        rw [(np.paths i).length_eq]
        simp only [sub_sub_sub_cancel_right]
        omega
      rw [hlen]
      exact k.isLt
    have hkNext :
        mu i + k.val - mu ⟨i.val + 1, hi⟩ <
          (np.paths ⟨i.val + 1, hi⟩).eastStepHeights.length := by
      have hlen :
          (np.paths ⟨i.val + 1, hi⟩).eastStepHeights.length =
            lam ⟨i.val + 1, hi⟩ - mu ⟨i.val + 1, hi⟩ := by
        rw [(np.paths ⟨i.val + 1, hi⟩).length_eq]
        simp only [sub_sub_sub_cancel_right]
        omega
      rw [hlen]
      exact hk'
    exact np.colStrictPaths i ⟨i.val + 1, hi⟩ hij k.val hk
      (mu i + k.val - mu ⟨i.val + 1, hi⟩) hkNext (by omega)

/-- Turn an independent-size skew tableau into its tuple of tableau paths. -/
noncomputable def ssytToNipatMN {lam mu : Fin M → ℕ}
    {hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (T : SkewSSYTMN N
      ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩) :
    NipatMN N lam mu hlam hmu hcontained where
  paths := fun i =>
    mkLatticePathFromEntriesMN (lam i) (mu i) i.val (T.entries i)
      (T.rowWeak i)
  colStrictPaths := fun i j hij k hk k' hk' hcol_eq => by
    simp only [mkLatticePathFromEntriesMN, List.getElem_ofFn]
    have hk_fin : k < lam i - mu i := by
      simpa [mkLatticePathFromEntriesMN] using hk
    have hk'_fin : k' < lam j - mu j := by
      simpa [mkLatticePathFromEntriesMN] using hk'
    exact T.colStrict_nonadjacent i j hij ⟨k, hk_fin⟩ ⟨k', hk'_fin⟩
      hcol_eq

@[simp]
theorem ssytToNipatMN_nipatMNToSSYT {lam mu : Fin M → ℕ}
    {hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : NipatMN N lam mu hlam hmu hcontained) :
    ssytToNipatMN (nipatMNToSSYT np) = np := by
  apply NipatMN.ext
  funext i
  apply LatticePath.ext
  simp only [ssytToNipatMN, nipatMNToSSYT, mkLatticePathFromEntriesMN]
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    rw [(np.paths i).length_eq]
    simp only [sub_sub_sub_cancel_right]
    omega
  · intro k hk₁ hk₂
    simp only [List.getElem_ofFn, List.get_eq_getElem]

@[simp]
theorem nipatMNToSSYT_ssytToNipatMN {lam mu : Fin M → ℕ}
    {hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (T : SkewSSYTMN N
      ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩) :
    nipatMNToSSYT (ssytToNipatMN T) = T := by
  apply SkewSSYTMN.ext
  funext i k
  simp only [nipatMNToSSYT, ssytToNipatMN, mkLatticePathFromEntriesMN,
    List.get_ofFn]
  congr 1

/-- The weight-preserving path/tableau equivalence with independent dimensions. -/
noncomputable def nipatMNSSYTEquiv (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    NipatMN N lam mu hlam hmu hcontained ≃
      SkewSSYTMN N
        ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ where
  toFun := nipatMNToSSYT
  invFun := ssytToNipatMN
  left_inv := ssytToNipatMN_nipatMNToSSYT
  right_inv := nipatMNToSSYT_ssytToNipatMN

private theorem list_prod_map_X_eq_finset_prod_MN
    (l : List (Fin N)) (n : ℕ) (h : l.length = n) :
    (l.map (fun j => X (R := R) j)).prod =
      ∏ k : Fin n, X (l.get ⟨k.val, by rw [h]; exact k.isLt⟩) := by
  subst h
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, List.get_cons_succ, List.get]
    rw [mul_comm, ih, mul_comm]

/-- The path/tableau equivalence preserves monomial weights. -/
theorem nipatMNToSSYT_weight {lam mu : Fin M → ℕ}
    {hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : NipatMN N lam mu hlam hmu hcontained) :
    np.weight (R := R) = (nipatMNToSSYT np).toMonomial := by
  unfold NipatMN.weight RectNipat.weight SkewSSYTMN.toMonomial
  congr 1
  funext i
  unfold LatticePath.weight
  have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
    rw [(np.paths i).length_eq]
    simp only [sub_sub_sub_cancel_right]
    omega
  rw [list_prod_map_X_eq_finset_prod_MN _ _ hlen]
  congr 1

noncomputable instance SkewSSYTMN.fintype (N : ℕ) (s : SkewPartition M) :
    Fintype (SkewSSYTMN N s) := by
  let S := {f : SkewFillingMN N s // isSSYTFillingMN s f}
  let e : S ≃ SkewSSYTMN N s :=
    { toFun := fun f => fillingToSkewSSYTMN f.1 f.2
      invFun := fun T => ⟨T.entries, T.rowWeak, T.colStrict⟩
      left_inv := fun f => by cases f; rfl
      right_inv := fun T => by cases T; rfl }
  exact Fintype.ofEquiv S e

/-- Summing the independent-size path weights gives the tableau definition of
the skew Schur polynomial. -/
theorem nipatMNWeightSum_eq_skewSchurMN (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    ∑ np : NipatMN N lam mu hlam hmu hcontained, np.weight (R := R) =
      skewSchurMN (R := R) N
        ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ := by
  let e := nipatMNSSYTEquiv (N := N) lam mu hlam hmu hcontained
  rw [show (∑ np : NipatMN N lam mu hlam hmu hcontained,
      np.weight (R := R)) =
      ∑ T : SkewSSYTMN N
        ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩,
          T.toMonomial by
    calc
      _ = ∑ np : NipatMN N lam mu hlam hmu hcontained,
          (e np).toMonomial := by
            apply Finset.sum_congr rfl
            intro np _
            exact nipatMNToSSYT_weight np
      _ = _ := Equiv.sum_comp e (fun T => T.toMonomial)]
  unfold skewSchurMN
  symm
  apply Finset.sum_bij (fun T _ => T)
  · intro T _
    exact Finset.mem_univ T
  · intro T₁ _ T₂ _ h
    exact h
  · intro T _
    exact ⟨T, skewSSYTMNFinset_mem _ T, rfl⟩
  · intro T _
    rfl

/-! ## Independent-size LGV determinant layer -/

/-- The `M` source vertices for Jacobi--Trudi. -/
def jacobiTrudiSourceVertexMN (mu : Fin M → ℕ) :
    LGV.kVertex (ℤ × ℤ) M :=
  fun i => ((mu i : ℤ) - i.val, 1)

/-- The `M` target vertices, at alphabet height `N`. -/
def jacobiTrudiTargetVertexMN (N : ℕ) (lam : Fin M → ℕ) :
    LGV.kVertex (ℤ × ℤ) M :=
  fun i => ((lam i : ℤ) - i.val, N)

theorem jacobiTrudiSourceVertexMN_xDecreasing (mu : Fin M → ℕ)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i) :
    LGV.xDecreasing (jacobiTrudiSourceVertexMN mu) := by
  intro i j hij
  simp only [LGV.xCoord, jacobiTrudiSourceVertexMN]
  have := hmu i j hij
  omega

theorem jacobiTrudiTargetVertexMN_xDecreasing (N : ℕ) (lam : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i) :
    LGV.xDecreasing (jacobiTrudiTargetVertexMN N lam) := by
  intro i j hij
  simp only [LGV.xCoord, jacobiTrudiTargetVertexMN]
  have := hlam i j hij
  omega

theorem jacobiTrudiSourceVertexMN_yIncreasing (mu : Fin M → ℕ) :
    LGV.yIncreasing (jacobiTrudiSourceVertexMN mu) := by
  intro i j _
  simp [LGV.yCoord, jacobiTrudiSourceVertexMN]

theorem jacobiTrudiTargetVertexMN_yIncreasing (N : ℕ) (lam : Fin M → ℕ) :
    LGV.yIncreasing (jacobiTrudiTargetVertexMN N lam) := by
  intro i j _
  simp [LGV.yCoord, jacobiTrudiTargetVertexMN]

/-- The generalized Jacobi--Trudi matrix is the transpose of its LGV path
weight matrix.  Positivity of `N` is exactly what the lattice-path encoding,
whose vertical interval is from height `1` to height `N`, requires. -/
theorem jacobiTrudiMatrixHMN_eq_pathWeightMatrix_transpose
    (hN : 0 < N) (lam mu : Fin M → ℕ) :
    jacobiTrudiMatrixHMN (R := R) N lam mu =
      (LGV.pathWeightMatrix LGV.integerLattice_pathFinite
        (jacobiTrudiArcWeight (N := N) (R := R))
        (jacobiTrudiSourceVertexMN mu)
        (jacobiTrudiTargetVertexMN N lam))ᵀ := by
  apply Matrix.ext
  intro i j
  simp only [jacobiTrudiMatrixHMN, Matrix.transpose_apply,
    LGV.pathWeightMatrix, Matrix.of_apply, jacobiTrudiSourceVertexMN,
    jacobiTrudiTargetVertexMN]
  rw [lgv_pathWeightSum_eq_hsymmExt _ _ hN]
  congr 1
  ring

/-- Determinant form of `jacobiTrudiMatrixHMN_eq_pathWeightMatrix_transpose`. -/
theorem det_jacobiTrudiMatrixHMN_eq_det_pathWeightMatrix
    (hN : 0 < N) (lam mu : Fin M → ℕ) :
    (jacobiTrudiMatrixHMN (R := R) N lam mu).det =
      (LGV.pathWeightMatrix LGV.integerLattice_pathFinite
        (jacobiTrudiArcWeight (N := N) (R := R))
        (jacobiTrudiSourceVertexMN mu)
        (jacobiTrudiTargetVertexMN N lam)).det := by
  rw [jacobiTrudiMatrixHMN_eq_pathWeightMatrix_transpose hN,
    Matrix.det_transpose]

/-- LGV expresses the generalized determinant as the sum over
nonintersecting `M`-tuples of paths. -/
theorem det_jacobiTrudiMatrixHMN_eq_lgvNipatWeightSum
    (hN : 0 < N) (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i) :
    (jacobiTrudiMatrixHMN (R := R) N lam mu).det =
      LGV.nipatWeightSum LGV.integerLattice_pathFinite
        (jacobiTrudiArcWeight (N := N) (R := R))
        (jacobiTrudiSourceVertexMN mu)
        (jacobiTrudiTargetVertexMN N lam) (Equiv.refl (Fin M)) := by
  rw [det_jacobiTrudiMatrixHMN_eq_det_pathWeightMatrix hN]
  exact LGV.lgv_nonpermutable
    (jacobiTrudiArcWeight (N := N) (R := R))
    (jacobiTrudiSourceVertexMN mu)
    (jacobiTrudiTargetVertexMN N lam)
    (jacobiTrudiSourceVertexMN_xDecreasing mu hmu)
    (jacobiTrudiSourceVertexMN_yIncreasing mu)
    (jacobiTrudiTargetVertexMN_xDecreasing N lam hlam)
    (jacobiTrudiTargetVertexMN_yIncreasing N lam)

/-- The sole remaining geometric bridge needed by the independent-size proof.

It says that LGV's vertex-disjoint path tuples and the east-step-height tuples
used in the tableau equivalence have the same total weight.  Keeping this as an
explicit proposition makes the remaining refactor obligation auditable. -/
def JacobiTrudiMNBridge (N : ℕ) (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) : Prop :=
  LGV.nipatWeightSum LGV.integerLattice_pathFinite
      (jacobiTrudiArcWeight (N := N) (R := R))
      (jacobiTrudiSourceVertexMN mu)
      (jacobiTrudiTargetVertexMN N lam) (Equiv.refl (Fin M)) =
    ∑ np : NipatMN N lam mu hlam hmu hcontained, np.weight (R := R)

/-- The generalized geometric bridge, obtained from the rectangular version of
the repository's full nonintersection/east-step-height proof. -/
theorem jacobiTrudiMNBridge
    (hN : 0 < N) (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    JacobiTrudiMNBridge (R := R) N lam mu hlam hmu hcontained := by
  unfold JacobiTrudiMNBridge NipatMN.weight
  change
    LGV.nipatWeightSum LGV.integerLattice_pathFinite
        (jacobiTrudiArcWeight (N := N) (R := R))
        (jacobiTrudiSourceVertexRect mu)
        (jacobiTrudiTargetVertexRect N lam) (Equiv.refl (Fin M)) =
      ∑ np : RectNipat N lam mu hlam hmu hcontained,
        np.weight (R := R)
  exact lgv_nipatWeightSum_eq_rectNipatSum (R := R) N lam mu
    (fun _ => hN) hlam hmu hcontained

/-- Once the geometric path-representation bridge is supplied, the full
independent-`M`/`N` Jacobi--Trudi identity follows by the two compiled layers. -/
theorem jacobiTrudi_h_mn_of_bridge
    (hN : 0 < N) (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i)
    (hbridge :
      JacobiTrudiMNBridge (R := R) N lam mu hlam hmu hcontained) :
    skewSchurMN (R := R) N
        ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ =
      (jacobiTrudiMatrixHMN (R := R) N lam mu).det := by
  rw [det_jacobiTrudiMatrixHMN_eq_lgvNipatWeightSum hN lam mu hlam hmu,
    hbridge, nipatMNWeightSum_eq_skewSchurMN]

/-- First Jacobi--Trudi with independent determinant size `M` and alphabet
size `N`. -/
theorem jacobiTrudi_h_mn
    (hN : 0 < N) (lam mu : Fin M → ℕ)
    (hlam : ∀ i j : Fin M, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin M, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    skewSchurMN (R := R) N
        ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ =
      (jacobiTrudiMatrixHMN (R := R) N lam mu).det :=
  jacobiTrudi_h_mn_of_bridge hN lam mu hlam hmu hcontained
    (jacobiTrudiMNBridge hN lam mu hlam hmu hcontained)

/-- At equal row and alphabet sizes, a generalized tableau is the original tableau. -/
def skewSSYTMNSelfEquiv (s : SkewPartition N) : SkewSSYTMN N s ≃ SkewSSYT s where
  toFun T :=
    { entries := T.entries
      rowWeak := T.rowWeak
      colStrict := T.colStrict }
  invFun T :=
    { entries := T.entries
      rowWeak := T.rowWeak
      colStrict := T.colStrict }
  left_inv T := by cases T; rfl
  right_inv T := by cases T; rfl

@[simp]
theorem skewSSYTMNSelfEquiv_entries (s : SkewPartition N) (T : SkewSSYTMN N s) :
    (skewSSYTMNSelfEquiv s T).entries = T.entries :=
  rfl

@[simp]
theorem skewSSYTMNSelfEquiv_toMonomial (s : SkewPartition N) (T : SkewSSYTMN N s) :
    SkewSSYT.toMonomial (R := R) (skewSSYTMNSelfEquiv s T) =
      T.toMonomial :=
  rfl

/-- The generalized skew Schur polynomial recovers the original API when `M = N`. -/
@[simp]
theorem skewSchurMN_self (s : SkewPartition N) :
    skewSchurMN (R := R) N s = skewSchur (R := R) s := by
  unfold skewSchurMN skewSchur
  apply Finset.sum_bij (fun T _ => skewSSYTMNSelfEquiv s T)
  · intro T _
    exact skewSSYTFinset_mem s (skewSSYTMNSelfEquiv s T)
  · intro T₁ _ T₂ _ h
    exact (skewSSYTMNSelfEquiv s).injective h
  · intro T hT
    refine ⟨(skewSSYTMNSelfEquiv s).symm T,
      skewSSYTMNFinset_mem s ((skewSSYTMNSelfEquiv s).symm T), ?_⟩
    exact (skewSSYTMNSelfEquiv s).apply_symm_apply T
  · intro T _
    exact (skewSSYTMNSelfEquiv_toMonomial (R := R) s T).symm

@[simp]
theorem jacobiTrudiMatrixHMN_self (lam mu : Fin N → ℕ) :
    jacobiTrudiMatrixHMN (R := R) N lam mu = jacobiTrudiMatrixH (R := R) lam mu :=
  rfl

/-- The new statement specializes to the already-proved theorem when the two
dimensions agree.  This is also a regression theorem for the compatibility
layer; it does not use `JacobiTrudiMNBridge`. -/
theorem jacobiTrudi_h_mn_self (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i) :
    skewSchurMN (R := R) N
        ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩ =
      (jacobiTrudiMatrixHMN (R := R) N lam mu).det := by
  rw [skewSchurMN_self, jacobiTrudiMatrixHMN_self]
  exact jacobiTrudi_h (R := R) lam mu hlam hmu hcontained

end SymmetricFunctions
