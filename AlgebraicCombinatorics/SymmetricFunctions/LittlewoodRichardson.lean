/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.SymmetricFunctions.NPartition
import AlgebraicCombinatorics.SymmetricFunctions.MonomialSymmetric

/-!
# The Littlewood-Richardson Rule

This file formalizes the Littlewood-Richardson rule for Schur polynomials, following
the presentation in the Algebraic Combinatorics textbook.

The Littlewood-Richardson rule is one of the most famous results in the theory of symmetric
polynomials. It provides a combinatorial formula for expanding the product of Schur polynomials
as a sum of Schur polynomials:
$$s_\nu \cdot s_{\lambda/\mu} = \sum_{T} s_{\nu + \operatorname{cont}(T)}$$
where the sum is over all ν-Yamanouchi semistandard tableaux T of shape λ/μ.

## Main definitions

* `NPartition`: An N-partition is a weakly decreasing N-tuple of natural numbers
* `contentTableau`: The content of a tableau (counting occurrences of each entry)
* `colGeq`: Restriction of a tableau to columns ≥ j
* `IsYamanouchi`: A semistandard tableau is ν-Yamanouchi if certain conditions hold
* `alternant`: The alternant polynomial a_α
* `schurPoly`: The Schur polynomial s_λ (via the Jacobi-Trudi formula)
* `skewSchurPoly`: The skew Schur polynomial s_{λ/μ}

## Main results

* `littlewoodRichardson`: Zelevinsky's generalized Littlewood-Richardson rule (thm.sf.lr-zy)
* `stembridgeLemma`: Stembridge's lemma (lem.sf.stemb-lem)
* `schurPoly_eq_alternant_div`: Theorem relating Schur polynomials to alternants (thm.sf.schur-symm (b))

## Indexing Convention

**This file uses 1-indexed columns** for skew Young diagrams, matching the textbook convention:
- A cell (i, j) is in Y(λ/μ) iff μ_i < j ≤ λ_i
- Column indices start at 1 (the first column is j = 1)

This differs from `SchurBasics.lean` which uses **0-indexed columns** (Mathlib convention):
- A cell (i, j) is in Y(λ/μ) iff μ_i ≤ j < λ_i
- Column indices start at 0 (the first column is j = 0)

The bijection (i, j) ↔ (i, j+1) converts between the conventions.
See `SchurBasics.skewCellEquiv` and `SchurBasics.mem_skewYoungDiagram_iff_mem_LR_shifted`
for explicit equivalences.

## References

* [Stembridge, *A concise proof of the Littlewood-Richardson rule*][Stembr02]
* [Grinberg-Reiner, *Hopf algebras in Combinatorics*][GriRei]

## Tags

Littlewood-Richardson rule, Schur polynomial, Yamanouchi tableau, symmetric polynomial
-/

open Finset Function BigOperators Polynomial MvPolynomial

namespace AlgebraicCombinatorics

variable {R : Type*} [CommRing R]
variable {N : ℕ}

/-! ## N-partitions and N-tuples

An N-partition is a weakly decreasing N-tuple of natural numbers.
We use `Fin N → ℕ` to represent N-tuples.

The `IsNPartition` predicate is defined in `NPartition.lean` and re-exported here
for backwards compatibility. -/

/-- An N-partition is a weakly decreasing N-tuple of natural numbers.
    (Used throughout the source)

    This is an alias for the canonical definition in `NPartition.lean`. -/
abbrev IsNPartition (lam : Fin N → ℕ) : Prop := _root_.IsNPartition lam

/-- The zero N-tuple (0, 0, ..., 0). (def.sf.tuple-addition (a))
    Note: This is definitionally equal to `(0 : Fin N → ℕ)` via Mathlib's Pi.instZero. -/
abbrev zeroTuple : Fin N → ℕ := 0

/-- Addition of N-tuples, defined entrywise. (def.sf.tuple-addition (b))
    Note: This is definitionally equal to `(· + ·)` on `Fin N → ℕ` via Mathlib's Pi.instAdd. -/
abbrev addTuple (α β : Fin N → ℕ) : Fin N → ℕ := α + β

/-- Subtraction of N-tuples, defined entrywise. Note: result is in ℤ.
    (def.sf.tuple-addition (b)) -/
def subTuple (α β : Fin N → ℕ) : Fin N → ℤ := fun i => (α i : ℤ) - (β i : ℤ)

-- Note: We use Mathlib's existing instances for Add and Zero on (Fin N → ℕ)
-- via Pi.instAdd and Pi.instZero, rather than defining redundant instances.

theorem addTuple_apply (α β : Fin N → ℕ) (i : Fin N) : (α + β) i = α i + β i := rfl

/-! ### API for def.sf.tuple-addition

The following lemmas establish the basic properties of N-tuple arithmetic
as stated in Definition def.sf.tuple-addition:
- (a) The zero N-tuple 0 = (0, 0, ..., 0)
- (b) Addition α + β and subtraction α - β are entrywise operations

Key properties (from the source text):
- "The addition operation + is associative and commutative"
- "The N-tuple 0 is its neutral element"
- "The subtraction operation − undoes +"
-/

section TupleAdditionAPI

variable (α β γ : Fin N → ℕ)

/-! #### Part (a): The zero N-tuple -/

/-- The zero tuple has all entries equal to 0. (def.sf.tuple-addition (a)) -/
@[simp]
theorem zeroTuple_apply (i : Fin N) : (zeroTuple : Fin N → ℕ) i = 0 := rfl

/-- The zero tuple is an N-partition (trivially weakly decreasing).
    This is an alias for `isNPartition_zero` from `NPartition.lean`. -/
theorem isNPartition_zeroTuple : IsNPartition (zeroTuple : Fin N → ℕ) :=
  _root_.isNPartition_zero

/-! #### Part (b): Entrywise operations -/

/-- Subtraction is computed entrywise. (def.sf.tuple-addition (b)) -/
@[simp]
theorem subTuple_apply' (i : Fin N) : subTuple α β i = (α i : ℤ) - (β i : ℤ) := rfl

/-! #### Algebraic properties of addition -/

/-- Addition of N-tuples is associative. -/
theorem addTuple_assoc : (α + β) + γ = α + (β + γ) := by
  ext i
  simp only [Pi.add_apply]
  ring

/-- Addition of N-tuples is commutative. -/
theorem addTuple_comm : α + β = β + α := by
  ext i
  simp only [Pi.add_apply]
  ring

/-- The zero tuple is the right identity for addition. -/
@[simp]
theorem addTuple_zeroTuple : α + zeroTuple = α := by
  ext i
  simp only [Pi.add_apply, zeroTuple_apply, add_zero]

/-- The zero tuple is the left identity for addition. -/
@[simp]
theorem zeroTuple_addTuple : zeroTuple + α = α := by
  ext i
  simp only [Pi.add_apply, zeroTuple_apply, zero_add]

/-! #### Subtraction undoes addition -/

/-- Subtraction recovers the first argument from the sum.
    This formalizes "The subtraction operation − undoes +". -/
theorem subTuple_add_left : subTuple (α + β) β = fun i => (α i : ℤ) := by
  ext i
  simp only [subTuple_apply', Pi.add_apply, Nat.cast_add, add_sub_cancel_right]

/-- Subtraction recovers the second argument from the sum. -/
theorem subTuple_add_right : subTuple (α + β) α = fun i => (β i : ℤ) := by
  ext i
  simp only [subTuple_apply', Pi.add_apply, Nat.cast_add, add_sub_cancel_left]

/-- Subtracting a tuple from itself gives zero. -/
@[simp]
theorem subTuple_self : subTuple α α = fun _ => (0 : ℤ) := by
  ext i
  simp only [subTuple_apply', sub_self]

/-- Subtracting zero gives the original tuple (as integers). -/
@[simp]
theorem subTuple_zeroTuple : subTuple α zeroTuple = fun i => (α i : ℤ) := by
  ext i
  simp only [subTuple_apply', zeroTuple_apply, Nat.cast_zero, sub_zero]

/-- Subtracting from zero gives negation. -/
@[simp]
theorem zeroTuple_subTuple : subTuple zeroTuple α = fun i => -(α i : ℤ) := by
  ext i
  simp only [subTuple_apply', zeroTuple_apply, Nat.cast_zero, zero_sub]

/-! #### Interaction with N-partitions -/

/-- The sum of two N-partitions is an N-partition.
    This is an alias for `IsNPartition.add` from `NPartition.lean`. -/
theorem isNPartition_add (hα : IsNPartition α) (hβ : IsNPartition β) :
    IsNPartition (α + β) :=
  hα.add hβ

end TupleAdditionAPI

/-- The staircase partition ρ = (N-1, N-2, ..., 1, 0). -/
def rho (N : ℕ) : Fin N → ℕ := fun i => N - 1 - i.val

theorem rho_apply (i : Fin N) : rho N i = N - 1 - i.val := rfl

/-- ρ is an N-partition when N > 0. -/
theorem isNPartition_rho : IsNPartition (rho N) := by
  intro i j hij
  simp only [rho]
  omega

/-- The ρ vector is strictly decreasing -/
theorem rho_strictAnti : StrictAnti (rho N) := by
  intro i j hij
  simp only [rho]
  omega

/-- The ρ vector is weakly decreasing -/
theorem rho_antitone : Antitone (rho N) :=
  rho_strictAnti.antitone

/-- The first component ρ_0 = N - 1 (when N > 0) -/
theorem rho_zero (hN : 0 < N) : rho N ⟨0, hN⟩ = N - 1 := by
  simp [rho]

/-- The last component ρ_{N-1} = 0 (when N > 0) -/
theorem rho_last (hN : 0 < N) : rho N ⟨N - 1, Nat.sub_lt hN one_pos⟩ = 0 := by
  simp [rho]

/-- The sum of the ρ vector equals N(N-1)/2, which is the triangular number T_{N-1}.
    This follows from ∑_{i=0}^{N-1} (N-1-i) = ∑_{k=0}^{N-1} k = N(N-1)/2. -/
theorem rho_sum : ∑ i : Fin N, rho N i = N * (N - 1) / 2 := by
  simp only [rho]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i)]
  have h : ∑ i ∈ Finset.range N, (N - 1 - i) = ∑ k ∈ Finset.range N, k := by
    cases N with
    | zero => simp
    | succ n =>
      refine Finset.sum_nbij' (s := Finset.range (n + 1)) (t := Finset.range (n + 1))
        (fun i => n - i) (fun k => n - k) ?_ ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_range] at hi ⊢
        omega
      · intro k hk
        simp only [Finset.mem_range] at hk ⊢
        omega
      · intro i hi
        simp only [Finset.mem_range] at hi
        have : n - (n - i) = i := by omega
        exact this
      · intro k hk
        simp only [Finset.mem_range] at hk
        have : n - (n - k) = k := by omega
        exact this
      · intro i hi
        simp only [Finset.mem_range] at hi
        have : n - i = n + 1 - 1 - i := by omega
        exact this
  rw [h, Finset.sum_range_id]

/-! ## Tableaux and their content

We work with semistandard Young tableaux. The content of a tableau counts
how many times each value appears.

### Indexing Convention

**This file uses 1-indexed columns** for skew Young diagrams:
- A cell (i, j) is in Y(λ/μ) iff μ_i < j ≤ λ_i
- Column indices start at 1 (the first column is j = 1)
- This matches the textbook convention

**SchurBasics.lean uses 0-indexed columns**:
- A cell (i, j) is in Y(λ/μ) iff μ_i ≤ j < λ_i
- Column indices start at 0 (the first column is j = 0)
- This follows Mathlib/programming convention

**Conversion**: The bijection (i, j) ↔ (i, j+1) transforms between conventions.
See `SchurBasics.skewCellEquiv` and `SchurBasics.mem_skewYoungDiagram_iff_mem_LR_shifted`
for the explicit equivalences and conversion lemmas.
-/

/-- The skew Young diagram Y(lam/mu) as a set of cells.
    A cell (i,j) is in Y(lam/mu) if mu_i < j ≤ lam_i.
    
    **This is the `Set` version with 1-indexed columns (textbook convention).**
    The first column is j = 1, not j = 0.
    
    For the canonical `Finset` version with 0-indexed columns, see:
    - `NPartition.skewYoungDiagram` in NPartition.lean (canonical, no `[NeZero N]` required)
    - `skewYoungDiagram` in SchurBasics.lean (duplicate, requires `[NeZero N]`)
    
    Comparison:
    - Here: (i, j) ∈ Y(λ/μ) iff μ_i < j ≤ λ_i (1-indexed)
    - NPartition/SchurBasics: (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i (0-indexed)
    
    The bijection between them is: (i, j) here ↔ (i, j-1) in NPartition/SchurBasics.
    See `SchurBasics.mem_skewYoungDiagram_iff_mem_LR_shifted` for the conversion lemma. -/
def skewYoungDiagram (lam mu : Fin N → ℕ) : Set (Fin N × ℕ) :=
  {c | mu c.1 < c.2 ∧ c.2 ≤ lam c.1}

/-- Decidability of membership in the skew Young diagram. -/
instance skewYoungDiagram_decidable (lam mu : Fin N → ℕ) (c : Fin N × ℕ) :
    Decidable (c ∈ skewYoungDiagram lam mu) :=
  inferInstanceAs (Decidable (mu c.1 < c.2 ∧ c.2 ≤ lam c.1))

/-- A tableau of shape lam/mu is a function from cells to [N]. -/
def Tableau (lam mu : Fin N → ℕ) := {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} → Fin N

/-- A tableau is semistandard if entries weakly increase along rows
    and strictly increase down columns. -/
def IsSemistandard {lam mu : Fin N → ℕ} (T : Tableau lam mu) : Prop :=
  -- Weakly increasing along rows
  (∀ c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu},
    c₁.val.1 = c₂.val.1 → c₁.val.2 < c₂.val.2 → T c₁ ≤ T c₂) ∧
  -- Strictly increasing down columns
  (∀ c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu},
    c₁.val.2 = c₂.val.2 → c₁.val.1 < c₂.val.1 → T c₁ < T c₂)

/-- The skew Young diagram is finite. -/
theorem skewYoungDiagram_finite (lam mu : Fin N → ℕ) :
    Set.Finite (skewYoungDiagram lam mu) := by
  let maxCol := Finset.sup Finset.univ lam
  have h : skewYoungDiagram lam mu ⊆
      Set.range (fun (p : Fin N × Fin (maxCol + 1)) => (p.1, p.2.val)) := by
    intro ⟨i, j⟩ ⟨_, hj⟩
    simp only [Set.mem_range]
    have hj_le : j ≤ maxCol := by
      calc j ≤ lam i := hj
        _ ≤ maxCol := Finset.le_sup (Finset.mem_univ i)
    use (i, ⟨j, Nat.lt_add_one_of_le hj_le⟩)
  exact Set.Finite.subset (Set.finite_range _) h

/-- The set of cells in the skew Young diagram as a Fintype. -/
noncomputable instance skewYoungDiagram_fintype (lam mu : Fin N → ℕ) :
    Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
  Set.Finite.fintype (skewYoungDiagram_finite lam mu)

/-- **Definition (def.sf.content)**: The content of a tableau T is the N-tuple counting
    occurrences of each value.

    For a tableau T of shape λ/μ, we define the content of T to be the N-tuple
    (a₁, a₂, ..., a_N), where aᵢ = (# of i's in T) = (# of boxes c of T such that T(c) = i).

    We denote this N-tuple by cont(T).

    **Example**: If N=5, then cont([[1,1,2],[4]]) = (2,1,0,1,0).

    **Key property** (eq.def.sf.content.xT=): x_T = x^(cont(T)) for any tableau T.
    (Both sides equal ∏ᵢ xᵢ^(# of i's in T).) -/
noncomputable def contentTableau {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) : Fin N → ℕ := fun i =>
  -- Count how many cells have entry i
  -- The diagram is finite since it's bounded by lam
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // T c = i}

-- Scoped notation for content, matching the textbook notation "cont T"
scoped notation "cont" => contentTableau

/-! ### Content API lemmas (def.sf.content) -/

set_option backward.isDefEq.respectTransparency false in
/-- Alternative characterization: content counts cells using Finset.card. -/
theorem contentTableau_eq_card {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N) :
    contentTableau T i = Finset.card (Finset.univ.filter (fun c => T c = i)) := by
  unfold contentTableau
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_subtype]

/-- The sum of content entries equals the number of cells in the tableau.
    (∑ᵢ cont(T)ᵢ = |Y(λ/μ)|)

    This follows from the fact that content partitions the cells by their entries. -/
theorem contentTableau_sum {lam mu : Fin N → ℕ} (T : Tableau lam mu) :
    ∑ i : Fin N, contentTableau T i =
    Fintype.card {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := by
  -- Rewrite using contentTableau_eq_card
  simp_rw [contentTableau_eq_card]
  -- The sum over fibers equals the card of the whole set
  rw [← Finset.card_univ (α := {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})]
  have h : ((Finset.univ : Finset {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Set _).MapsTo T (Finset.univ : Finset (Fin N)) :=
    fun c _ => Finset.mem_univ (T c)
  exact (Finset.card_eq_sum_card_fiberwise h).symm

/-- Content is nonnegative (trivially true for ℕ, but stated for documentation). -/
theorem contentTableau_nonneg {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N) :
    0 ≤ contentTableau T i := Nat.zero_le _

/-- If two tableaux have the same cells with value i (i.e., T' c = i ↔ T c = i for all c),
    then they have the same content at i. This is useful for proving that transformations
    that don't affect certain values preserve the content at those values. -/
theorem contentTableau_eq_of_iff {lam mu : Fin N → ℕ} (T T' : Tableau lam mu) (i : Fin N)
    (h : ∀ c, T' c = i ↔ T c = i) :
    contentTableau T' i = contentTableau T i := by
  unfold contentTableau
  apply Nat.card_congr
  refine ⟨fun ⟨c, hc⟩ => ⟨c, (h c).mp hc⟩, fun ⟨c, hc⟩ => ⟨c, (h c).mpr hc⟩, ?_, ?_⟩
  · intro ⟨c, hc⟩; simp
  · intro ⟨c, hc⟩; simp

/-- x^α = ∏ᵢ xᵢ^(αᵢ) for an N-tuple α.

    This is an alias for `AlgebraicCombinatorics.SymmetricFunctions.monomialExp` from MonomialSymmetric.lean.
    The two definitions are identical: both equal `∏ i, X i ^ α i`.

    See also: `xPow_eq_monomialExp` for the equivalence lemma. -/
noncomputable abbrev xPow (α : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  AlgebraicCombinatorics.SymmetricFunctions.monomialExp α

/-- `xPow` equals `monomialExp` (definitional equality).

    This lemma witnesses that the two definitions are the same:
    - `xPow α = ∏ i, X i ^ α i` (from LittlewoodRichardson.lean)
    - `monomialExp α = ∏ i, X i ^ α i` (from MonomialSymmetric.lean) -/
theorem xPow_eq_monomialExp (α : Fin N → ℕ) :
    (xPow α : MvPolynomial (Fin N) R) = AlgebraicCombinatorics.SymmetricFunctions.monomialExp α := rfl

/-- x^α · x^β = x^(α+β). (eq.def.sf.tuple-addition.xab)

    This is equivalent to `monomialExp_add` from MonomialSymmetric.lean. -/
theorem xPow_mul (α β : Fin N → ℕ) :
    (xPow α : MvPolynomial (Fin N) R) * xPow β = xPow (α + β) := by
  simp only [xPow_eq_monomialExp]
  rw [← AlgebraicCombinatorics.SymmetricFunctions.monomialExp_add]

/-! ## Column restriction of tableaux (def.sf.col-tab)

**Definition (def.sf.col-tab)**: Let λ and μ be two N-partitions. Let T be a tableau of shape λ/μ.
Let j be a positive integer. Then, col_{≥j}(T) means the restriction of T to columns j, j+1, j+2, ...
(that is, the result of removing the first j-1 columns from T).

Formally speaking, this means the restriction of the map T to the set {(u,v) ∈ Y(λ/μ) | v ≥ j}.

**Note**: col_{≥1}(T) = T for any tableau T. -/

/-- The restriction of a tableau to columns ≥ j. (def.sf.col-tab)

    For a tableau T of shape λ/μ, `colGeq T j` is the restriction of T to the cells
    in columns j, j+1, j+2, ... This is the formal definition of col_{≥j}(T).

    The domain is {(u,v) ∈ Y(λ/μ) | v ≥ j}, and the function returns T(u,v)
    for each such cell. -/
def colGeq {lam mu : Fin N → ℕ} (T : Tableau lam mu) (j : ℕ) :
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} → Fin N :=
  fun ⟨c, hc⟩ => T ⟨c, hc.1⟩

/-- col_{≥j}(T) at cell c equals T at cell c. (def.sf.col-tab)

    This is the defining property: the restriction to columns ≥ j simply
    returns the same value as T at each cell. -/
@[simp]
theorem colGeq_apply {lam mu : Fin N → ℕ} (T : Tableau lam mu) (j : ℕ)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j}) :
    colGeq T j c = T ⟨c.val, c.prop.1⟩ := rfl

/-- For any cell in the domain of col_{≥j}(T), its column index is at least j. -/
theorem colGeq_col_ge {lam mu : Fin N → ℕ} (j : ℕ)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j}) :
    c.val.2 ≥ j := c.prop.2

/-- col_{≥1}(T) = T for any tableau T.

    This is a key property from the source text: "Note that col_{≥1}(T) = T for any tableau T." -/
theorem colGeq_one {lam mu : Fin N → ℕ} (T : Tableau lam mu) :
    ∀ c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ 1},
      colGeq T 1 c = T ⟨c.val, c.prop.1⟩ := by
  intro c
  rfl

/-- Every cell in a skew Young diagram has column ≥ 1.

    This is because cells (i,j) in Y(λ/μ) satisfy μ_i < j, and μ_i ≥ 0, so j ≥ 1.
    This is why col_{≥1}(T) has the same domain as T. -/
theorem skewYoungDiagram_col_pos {lam mu : Fin N → ℕ}
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) :
    c.val.2 ≥ 1 := by
  have h := c.prop
  simp only [skewYoungDiagram, Set.mem_ofPred_eq] at h
  omega

/-- The embedding from the domain of T to the domain of col_{≥1}(T).

    Since every cell in Y(λ/μ) has column ≥ 1, this is a natural inclusion. -/
def embedColGeqOne {lam mu : Fin N → ℕ} :
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} →
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ 1} :=
  fun c => ⟨c.val, ⟨c.prop, skewYoungDiagram_col_pos c⟩⟩

/-- The projection from the domain of col_{≥1}(T) to the domain of T. -/
def embedFromColGeqOne {lam mu : Fin N → ℕ} :
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ 1} →
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
  fun c => ⟨c.val, c.prop.1⟩

/-- embedColGeqOne is a left inverse of embedFromColGeqOne. -/
theorem embedColGeqOne_embedFromColGeqOne {lam mu : Fin N → ℕ}
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ 1}) :
    embedColGeqOne (embedFromColGeqOne c) = c := by
  simp only [embedColGeqOne, embedFromColGeqOne]

/-- embedFromColGeqOne is a left inverse of embedColGeqOne. -/
theorem embedFromColGeqOne_embedColGeqOne {lam mu : Fin N → ℕ}
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) :
    embedFromColGeqOne (embedColGeqOne c) = c := by
  simp only [embedColGeqOne, embedFromColGeqOne]

/-- The domain of col_{≥1}(T) is equivalent to the domain of T.

    This formalizes the note "col_{≥1}(T) = T for any tableau T" from the source:
    the two functions have equivalent domains and agree on corresponding elements. -/
def equivColGeqOne {lam mu : Fin N → ℕ} :
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} ≃
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ 1} where
  toFun := embedColGeqOne
  invFun := embedFromColGeqOne
  left_inv := embedFromColGeqOne_embedColGeqOne
  right_inv := embedColGeqOne_embedFromColGeqOne

/-- col_{≥1}(T) = T (as functions, up to domain equivalence).

    This is the formal statement of "Note that col_{≥1}(T) = T for any tableau T"
    from the source text. -/
theorem colGeq_one_eq_tableau {lam mu : Fin N → ℕ} (T : Tableau lam mu) :
    colGeq T 1 ∘ embedColGeqOne = T := by
  ext c
  simp only [comp_apply, colGeq_apply, embedColGeqOne]

/-- The embedding from the domain of col_{≥k}(T) to the domain of col_{≥j}(T) when j ≤ k. -/
def embedColGeq {lam mu : Fin N → ℕ} {j k : ℕ} (hjk : j ≤ k) :
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ k} →
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} :=
  fun c => ⟨c.val, ⟨c.prop.1, le_trans hjk c.prop.2⟩⟩

/-- Composing column restrictions: col_{≥k}(T) factors through col_{≥j}(T) when j ≤ k. -/
theorem colGeq_compose {lam mu : Fin N → ℕ} (T : Tableau lam mu) {j k : ℕ} (hjk : j ≤ k)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ k}) :
    colGeq T j (embedColGeq hjk c) = colGeq T k c := rfl

/-- The domain of col_{≥j}(T) is empty when j exceeds all column indices in the diagram.

    This corresponds to the example in the source text where col_{≥5}(T) = (empty tableau)
    when the tableau has no columns ≥ 5. -/
theorem colGeq_empty_of_large {lam mu : Fin N → ℕ} (j : ℕ) (hj : ∀ i : Fin N, lam i < j) :
    IsEmpty {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} := by
  constructor
  intro ⟨c, hc, hcj⟩
  simp only [skewYoungDiagram, Set.mem_ofPred_eq] at hc
  have : c.2 ≤ lam c.1 := hc.2
  have : lam c.1 < j := hj c.1
  omega

/-- Monotonicity: if j ≤ k, then the domain of col_{≥k}(T) is a subset of the domain of col_{≥j}(T). -/
theorem colGeq_domain_subset {lam mu : Fin N → ℕ} {j k : ℕ} (hjk : j ≤ k) :
    {c : Fin N × ℕ | c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ k} ⊆
    {c : Fin N × ℕ | c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} := by
  intro c ⟨hc, hck⟩
  exact ⟨hc, le_trans hjk hck⟩

/-- The domain of col_{≥0}(T) equals the entire domain of T (since all columns are ≥ 0). -/
theorem colGeq_zero_domain {lam mu : Fin N → ℕ} :
    {c : Fin N × ℕ | c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ 0} =
    {c : Fin N × ℕ | c ∈ skewYoungDiagram lam mu} := by
  ext c
  simp only [Set.mem_ofPred_eq, ge_iff_le, Nat.zero_le, and_true]

/-- The content of a restricted tableau col_{≥j}(T).
    Counts occurrences of each value in columns j and beyond. -/
noncomputable def contentColGeq {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (j : ℕ) : Fin N → ℕ := fun i =>
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} // T ⟨c.val, c.prop.1⟩ = i}

/-! ## Yamanouchi tableaux

A semistandard tableau T is ν-Yamanouchi if ν + cont(col_{≥j}(T)) is an N-partition
for every positive integer j. -/

/-- A semistandard tableau T of shape λ/μ is ν-Yamanouchi if for each positive integer j,
    the N-tuple ν + cont(col_{≥j}(T)) is an N-partition (i.e., weakly decreasing).

    **Definition (def.sf.yamanouchi)**:
    Let λ, μ, ν be three N-partitions. A semistandard tableau T of shape λ/μ is said to be
    ν-Yamanouchi if for each positive integer j, the N-tuple ν + cont(col_{≥j}T) ∈ ℕ^N is
    an N-partition (i.e., weakly decreasing).

    **Key properties:**
    - The condition ensures that as we process the tableau column by column from right to left,
      starting with tally ν, the running tally always remains weakly decreasing.
    - For j = 1, we get that ν + cont(T) is an N-partition (see `IsYamanouchi.isNPartition_add_content`).
    - A 0-Yamanouchi tableau (also called a "ballot tableau") has content that is itself an N-partition.

    **Voting interpretation (rmk.sf.yamanouchi.votes):**
    Think of each entry i in T as a vote for candidate i. Starting with tally ν and counting votes
    column by column from right to left, the tally must remain weakly decreasing at every step.
    Since columns have distinct entries (strictly increasing), no candidate gains more than one
    vote at a time. -/
def IsYamanouchi {lam mu : Fin N → ℕ}
    (nu : Fin N → ℕ) (T : Tableau lam mu) : Prop :=
  IsSemistandard T ∧
  ∀ j : ℕ, j > 0 → IsNPartition (nu + contentColGeq T j)

/-! ### API lemmas for IsYamanouchi -/

/-- A ν-Yamanouchi tableau is semistandard. -/
theorem IsYamanouchi.isSemistandard {lam mu : Fin N → ℕ} {nu : Fin N → ℕ}
    {T : Tableau lam mu} (h : IsYamanouchi nu T) : IsSemistandard T :=
  h.1

/-- For a ν-Yamanouchi tableau T and any j > 0, ν + cont(col_{≥j}(T)) is an N-partition. -/
theorem IsYamanouchi.isNPartition_add_contentColGeq {lam mu : Fin N → ℕ} {nu : Fin N → ℕ}
    {T : Tableau lam mu} (h : IsYamanouchi nu T) {j : ℕ} (hj : j > 0) :
    IsNPartition (nu + contentColGeq T j) :=
  h.2 j hj

/-- Constructing a Yamanouchi tableau from its components. -/
theorem isYamanouchi_iff {lam mu : Fin N → ℕ} {nu : Fin N → ℕ} {T : Tableau lam mu} :
    IsYamanouchi nu T ↔
    IsSemistandard T ∧ ∀ j : ℕ, j > 0 → IsNPartition (nu + contentColGeq T j) :=
  Iff.rfl

/-- A cell in the skew diagram has column index ≥ 1 (since column indices start from 1
    in the standard convention where column j contains cells with c.2 = j). -/
theorem skewYoungDiagram_col_ge_one {lam mu : Fin N → ℕ}
    (c : Fin N × ℕ) (hc : c ∈ skewYoungDiagram lam mu) : c.2 ≥ 1 := by
  simp only [skewYoungDiagram, Set.mem_ofPred_eq] at hc
  omega

/-- The type of cells in the skew diagram with column ≥ 1 is equivalent to the full diagram. -/
noncomputable def skewDiagramColGeqOneEquiv (lam mu : Fin N → ℕ) :
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ 1} ≃
    {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} where
  toFun c := ⟨c.val, c.prop.1⟩
  invFun c := ⟨c.val, c.prop, skewYoungDiagram_col_ge_one c.val c.prop⟩
  left_inv c := by simp
  right_inv c := by simp

/-- Equivalence between cells with entry i in col_{≥1} and all cells with entry i. -/
noncomputable def contentColGeqOneEquiv {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (i : Fin N) :
    {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ 1} // T ⟨c.val, c.prop.1⟩ = i} ≃
    {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // T c = i} where
  toFun c := ⟨⟨c.val.val, c.val.prop.1⟩, c.prop⟩
  invFun c := ⟨⟨c.val.val, c.val.prop, skewYoungDiagram_col_ge_one c.val.val c.val.prop⟩, c.prop⟩
  left_inv c := by simp
  right_inv c := by simp

/-- col_{≥1}(T) = T, i.e., the content of col_{≥1}(T) equals the content of T.
    This is because all cells in the skew diagram have column index ≥ 1. -/
theorem contentColGeq_one_eq_contentTableau {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) : contentColGeq T 1 = contentTableau T := by
  ext i
  simp only [contentColGeq, contentTableau]
  exact Nat.card_congr (contentColGeqOneEquiv T i)

/-- contentColGeq is monotonic: cells in columns >= j+1 are a subset of cells in columns >= j. -/
theorem contentColGeq_mono {lam mu : Fin N → ℕ} (T : Tableau lam mu) (j : ℕ) (i : Fin N) :
    contentColGeq T (j + 1) i ≤ contentColGeq T j i := by
  -- The key insight is that cells with col >= j+1 are a subset of cells with col >= j
  -- This follows from the definition of contentColGeq as a cardinality
  unfold contentColGeq
  -- Get finiteness of the base set
  have hfin_j : Set.Finite {c : Fin N × ℕ | c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} := by
    apply Set.Finite.subset (skewYoungDiagram_finite lam mu)
    intro c ⟨hc, _⟩
    exact hc
  haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} :=
    Set.Finite.to_subtype hfin_j
  haveI : Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} // T ⟨c.val, c.prop.1⟩ = i} :=
    Subtype.finite
  have hfin_j1 : Set.Finite {c : Fin N × ℕ | c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j + 1} := by
    apply Set.Finite.subset (skewYoungDiagram_finite lam mu)
    intro c ⟨hc, _⟩
    exact hc
  haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j + 1} :=
    Set.Finite.to_subtype hfin_j1
  -- Define the injection from cells with col >= j+1 to cells with col >= j
  let f : {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j + 1} // T ⟨c.val, c.prop.1⟩ = i} →
          {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} // T ⟨c.val, c.prop.1⟩ = i} :=
    fun ⟨⟨c, hc1, hc2⟩, hTc⟩ => ⟨⟨c, hc1, Nat.le_of_succ_le hc2⟩, hTc⟩
  apply Nat.card_le_card_of_injective f
  -- Prove f is injective
  intro ⟨⟨c1, hc1_1, hc1_2⟩, hTc1⟩ ⟨⟨c2, hc2_1, hc2_2⟩, hTc2⟩ h
  simp only [f, Subtype.mk.injEq] at h ⊢
  exact h

/-- For semistandard tableaux, contentColGeq T j i ≤ contentColGeq T (j+1) i + 1.
    This is because adding column j can add at most 1 cell with entry i
    (since columns are strictly increasing in semistandard tableaux). -/
theorem contentColGeq_succ_le {lam mu : Fin N → ℕ} (T : Tableau lam mu) (_hT : IsSemistandard T)
    (j : ℕ) (i : Fin N) :
    contentColGeq T j i ≤ contentColGeq T (j + 1) i + 1 := by
  unfold contentColGeq
  -- Define the sets
  let Sj := {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} // T ⟨c.val, c.prop.1⟩ = i}
  let Sj1 := {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j + 1} // T ⟨c.val, c.prop.1⟩ = i}

  -- Finiteness instances
  haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} := by
    apply Set.Finite.to_subtype
    apply Set.Finite.subset (skewYoungDiagram_finite lam mu)
    intro c ⟨hc, _⟩
    exact hc
  haveI : Finite Sj := Subtype.finite
  haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j + 1} := by
    apply Set.Finite.to_subtype
    apply Set.Finite.subset (skewYoungDiagram_finite lam mu)
    intro c ⟨hc, _⟩
    exact hc
  haveI : Finite Sj1 := Subtype.finite

  -- Partition Sj into {col = j} and {col > j}
  let Sj_eq := {c : Sj // c.val.val.2 = j}
  let Sj_gt := {c : Sj // c.val.val.2 > j}

  haveI : Finite Sj_eq := Subtype.finite
  haveI : Finite Sj_gt := Subtype.finite

  -- We have |Sj| = |Sj_eq| + |Sj_gt| via the partition
  have hpartition : ∀ c : Sj, c.val.val.2 = j ∨ c.val.val.2 > j := fun c => by
    have hge := c.val.prop.2
    omega

  -- Create an equivalence Sj ≃ Sj_eq ⊕ Sj_gt
  let e : Sj ≃ Sj_eq ⊕ Sj_gt := {
    toFun := fun c => if h : c.val.val.2 = j then Sum.inl ⟨c, h⟩ else Sum.inr ⟨c, by
      cases hpartition c with
      | inl heq => exact absurd heq h
      | inr hgt => exact hgt⟩
    invFun := fun x => match x with
      | Sum.inl c => c.val
      | Sum.inr c => c.val
    left_inv := fun c => by simp only; split_ifs <;> rfl
    right_inv := fun x => by
      cases x with
      | inl c =>
        simp only [dite_eq_left c.prop]
        rfl
      | inr c =>
        simp only [dite_eq_right (Nat.ne_of_gt c.prop)]
        rfl
  }

  have hcard_partition : Nat.card Sj = Nat.card Sj_eq + Nat.card Sj_gt := by
    rw [Nat.card_congr e, Nat.card_sum]

  -- |Sj_eq| ≤ 1 (at most one cell per column with entry i, by semistandardness)
  have hcard_eq_le_one : Nat.card Sj_eq ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    constructor
    intro c1 c2
    -- c1 and c2 are cells in column j with entry i
    have hcol1 : c1.val.val.val.2 = j := c1.prop
    have hcol2 : c2.val.val.val.2 = j := c2.prop
    have hcol_eq : c1.val.val.val.2 = c2.val.val.val.2 := by omega
    have hentry1 : T ⟨c1.val.val.val, c1.val.val.prop.1⟩ = i := c1.val.prop
    have hentry2 : T ⟨c2.val.val.val, c2.val.val.prop.1⟩ = i := c2.val.prop
    -- If they're in the same column with same entry, they must be in the same row (by col-strict)
    by_cases hrow : c1.val.val.val.1 = c2.val.val.val.1
    · -- Same row and column means same cell
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hrow hcol_eq
    · -- Different rows but same column with same entry contradicts column-strictness
      have hcol_strict := _hT.2
      exfalso
      cases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne (by
        intro heq
        apply hrow
        exact heq : c1.val.val.val.1 ≠ c2.val.val.val.1)) with
      | inl hlt =>
        have := hcol_strict ⟨c1.val.val.val, c1.val.val.prop.1⟩ ⟨c2.val.val.val, c2.val.val.prop.1⟩ hcol_eq (Fin.lt_def.mpr hlt)
        rw [hentry1, hentry2] at this
        exact Nat.lt_irrefl i.val this
      | inr hgt =>
        have := hcol_strict ⟨c2.val.val.val, c2.val.val.prop.1⟩ ⟨c1.val.val.val, c1.val.val.prop.1⟩ hcol_eq.symm (Fin.lt_def.mpr hgt)
        rw [hentry1, hentry2] at this
        exact Nat.lt_irrefl i.val this

  -- |Sj_gt| ≤ |Sj1| via injection (col > j means col ≥ j+1)
  have hcard_gt_le : Nat.card Sj_gt ≤ Nat.card Sj1 := by
    let f : Sj_gt → Sj1 := fun ⟨⟨⟨c, hskew, hge⟩, hT_eq⟩, hgt⟩ =>
      ⟨⟨c, hskew, hgt⟩, hT_eq⟩
    apply Nat.card_le_card_of_injective f
    intro ⟨⟨⟨c1, hskew1, hge1⟩, hT1_eq⟩, hgt1⟩ ⟨⟨⟨c2, hskew2, hge2⟩, hT2_eq⟩, hgt2⟩ h
    -- Extract c1 = c2 from the equality
    simp only [f] at h
    -- h : ⟨⟨c1, hskew1, hgt1⟩, hT1_eq⟩ = ⟨⟨c2, hskew2, hgt2⟩, hT2_eq⟩
    have hval := congrArg Subtype.val h
    -- hval : ⟨c1, hskew1, hgt1⟩ = ⟨c2, hskew2, hgt2⟩
    have hc_eq := congrArg Subtype.val hval
    -- hc_eq : c1 = c2
    -- Now we need to prove the full equality
    congr 1
    · apply Subtype.ext
      apply Subtype.ext
      exact hc_eq

  -- Combine: |Sj| = |Sj_eq| + |Sj_gt| ≤ 1 + |Sj1|
  calc Nat.card Sj = Nat.card Sj_eq + Nat.card Sj_gt := hcard_partition
    _ ≤ 1 + Nat.card Sj1 := Nat.add_le_add hcard_eq_le_one hcard_gt_le
    _ = Nat.card Sj1 + 1 := Nat.add_comm 1 _

/-- contentTableau is at least contentColGeq for any j.
    This is because contentColGeq counts cells in columns >= j, which is a subset of all cells. -/
theorem contentTableau_ge_contentColGeq {lam mu : Fin N → ℕ} (T : Tableau lam mu) (j : ℕ) (i : Fin N) :
    contentTableau T i ≥ contentColGeq T j i := by
  unfold contentTableau contentColGeq
  haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
    Set.Finite.to_subtype (skewYoungDiagram_finite lam mu)
  haveI : Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // T c = i} :=
    Subtype.finite
  -- Define the injection from cells with col >= j to all cells
  let f : {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} // T ⟨c.val, c.prop.1⟩ = i} →
          {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // T c = i} :=
    fun ⟨⟨c, hc1, _⟩, hTc⟩ => ⟨⟨c, hc1⟩, hTc⟩
  apply Nat.card_le_card_of_injective f
  -- Prove f is injective
  intro ⟨⟨c1, hc1_1, hc1_2⟩, hTc1⟩ ⟨⟨c2, hc2_1, hc2_2⟩, hTc2⟩ h
  simp only [f, Subtype.mk.injEq] at h ⊢
  exact h

/-- **Key property**: For a ν-Yamanouchi tableau T, ν + cont(T) is an N-partition.
    This is the j=1 case of the Yamanouchi condition, and is essential for the
    Littlewood-Richardson rule since it ensures the output partitions are valid. -/
theorem IsYamanouchi.isNPartition_add_content {lam mu : Fin N → ℕ} {nu : Fin N → ℕ}
    {T : Tableau lam mu} (h : IsYamanouchi nu T) :
    IsNPartition (nu + contentTableau T) := by
  rw [← contentColGeq_one_eq_contentTableau]
  exact h.isNPartition_add_contentColGeq Nat.one_pos

/-- The zero N-tuple is an N-partition.
    This is an alias for `isNPartition_zero` from `NPartition.lean`. -/
theorem isNPartition_zero : IsNPartition (0 : Fin N → ℕ) :=
  _root_.isNPartition_zero

/-- Adding two N-partitions gives an N-partition.
    This is an alias for `IsNPartition.add` from `NPartition.lean`. -/
theorem IsNPartition.add {α β : Fin N → ℕ} (hα : IsNPartition α) (hβ : IsNPartition β) :
    IsNPartition (α + β) :=
  _root_.IsNPartition.add hα hβ

/-- A 0-Yamanouchi tableau (ballot tableau) has content that is itself an N-partition. -/
theorem IsYamanouchi.isNPartition_content_of_zero {lam mu : Fin N → ℕ}
    {T : Tableau lam mu} (h : IsYamanouchi zeroTuple T) :
    IsNPartition (contentTableau T) := by
  have := h.isNPartition_add_content
  simp only [zeroTuple, zero_add] at this
  exact this

/-! ## Voting metaphor for Yamanouchi condition

The Yamanouchi condition can be understood through a voting metaphor (rmk.sf.yamanouchi.votes):
- Each entry i in T is a vote for candidate i
- We count votes column by column, from right to left
- Starting with tally ν, after processing each column, the tally must remain weakly decreasing
- Key observation: no candidate gains more than one vote at a time (since columns have distinct entries)
-/

/-! ## Alternants and Schur polynomials -/

/-- The alternant a_α = ∑_{σ ∈ S_N} sign(σ) · x^(σ·α).
    Here σ·α means (α_{σ(1)}, α_{σ(2)}, ..., α_{σ(N)}).

    **Equivalence with SchurBasics.alternant:**
    This sum-based definition equals the determinant-based definition in
    `alternant` (from SchurBasics.lean). See `alternant_eq_det` for the proof
    that this equals `det(alternantMatrix α)`. -/
noncomputable def alternant (α : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  ∑ σ : Equiv.Perm (Fin N), Equiv.Perm.sign σ • xPow (α ∘ σ)

/-- The Vandermonde determinant: a_ρ = ∏_{i<j} (xᵢ - xⱼ).
    (eq.def.sf.alternants.arho=vdm) -/
noncomputable def vandermonde : MvPolynomial (Fin N) R :=
  ∏ i : Fin N, ∏ j : Fin N, if i < j then X i - X j else 1

/-! ### Helper lemmas for alternant_rho_eq_vandermonde -/

private lemma prod_if_lt_eq_prod_Ioi' {α : Type*} [CommMonoid α] (f : Fin N → Fin N → α) :
    ∏ i : Fin N, ∏ j : Fin N, (if i < j then f i j else 1) =
    ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j := by
  congr 1
  ext i
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp [Finset.mem_Ioi]

private lemma prod_neg_sub' {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → MvPolynomial (Fin N) R) :
    ∏ i ∈ s, (f i - g i) = (-1) ^ s.card * ∏ i ∈ s, (g i - f i) := by
  induction s using Finset.induction_on
  case empty => simp
  case insert a s hna ih =>
    rw [Finset.prod_insert hna, ih]
    rw [Finset.prod_insert hna, Finset.card_insert_of_notMem hna]
    rw [pow_succ]
    have h : f a - g a = -(g a - f a) := by ring
    rw [h]
    ring

private lemma vandermonde_eq_prod_Ioi :
    (vandermonde : MvPolynomial (Fin N) R) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (X i - X j) := by
  unfold vandermonde
  exact prod_if_lt_eq_prod_Ioi' _

private lemma prod_prod_neg_sub' :
    ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (X i - X j : MvPolynomial (Fin N) R) =
    (-1) ^ (∑ i : Fin N, (Finset.Ioi i).card) * ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (X j - X i) := by
  have h : ∀ i : Fin N, ∏ j ∈ Finset.Ioi i, (X i - X j : MvPolynomial (Fin N) R) =
           (-1) ^ (Finset.Ioi i).card * ∏ j ∈ Finset.Ioi i, (X j - X i) := fun i => by
    rw [prod_neg_sub' (Finset.Ioi i) (fun _ => X i) (fun j => X j)]
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_pow_eq_pow_sum]

private lemma vandermonde_eq_signed_det_vandermonde :
    (vandermonde : MvPolynomial (Fin N) R) =
    (-1) ^ (∑ i : Fin N, (Finset.Ioi i).card) *
      (Matrix.vandermonde (X : Fin N → MvPolynomial (Fin N) R)).det := by
  rw [vandermonde_eq_prod_Ioi, Matrix.det_vandermonde]
  exact prod_prod_neg_sub'

/-- Matrix whose determinant equals the alternant.
    Entry (i, j) is x_j^{α_i}. -/
noncomputable def alternantMatrix (α : Fin N → ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R) :=
  Matrix.of fun i j => X j ^ (α i)

/-- The sum-based alternant definition equals the determinant of the alternant matrix.

    This establishes the equivalence:
    `∑ σ : Perm (Fin N), sign(σ) • x^(α ∘ σ) = det(x_j^{α_i})`

    The determinant-based definition is used in SchurBasics.lean (see `alternant` there),
    while this file uses the sum-based definition. This theorem proves they are equal. -/
theorem alternant_eq_det (α : Fin N → ℕ) :
    (alternant α : MvPolynomial (Fin N) R) = (alternantMatrix α).det := by
  unfold alternant alternantMatrix
  simp only [xPow_eq_monomialExp, AlgebraicCombinatorics.SymmetricFunctions.monomialExp]
  rw [Matrix.det_apply]
  simp only [Matrix.of_apply, Function.comp_apply]

private lemma alternantMatrix_rho_eq :
    (alternantMatrix (rho N) : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R)) =
    (Matrix.vandermonde (X : Fin N → MvPolynomial (Fin N) R)).transpose.submatrix Fin.rev id := by
  ext i j
  simp only [alternantMatrix, Matrix.of_apply, rho, Matrix.transpose_apply,
             Matrix.vandermonde_apply, Matrix.submatrix_apply, id]
  have h : (Fin.rev i).val = N - (i.val + 1) := Fin.val_rev i
  have hi : i.val < N := i.isLt
  have heq : N - 1 - i.val = N - (i.val + 1) := by omega
  rw [heq, ← h]

private lemma det_alternantMatrix_rho :
    (alternantMatrix (rho N) : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N) R)).det =
    Equiv.Perm.sign (Fin.revPerm (n := N)) *
      (Matrix.vandermonde (X : Fin N → MvPolynomial (Fin N) R)).det := by
  rw [alternantMatrix_rho_eq]
  have h : (Matrix.vandermonde (X : Fin N → MvPolynomial (Fin N) R)).transpose.submatrix Fin.rev id =
           (Matrix.vandermonde (X : Fin N → MvPolynomial (Fin N) R)).transpose.submatrix
             (↑(Fin.revPerm (n := N))) id := rfl
  rw [h]
  rw [Matrix.det_permute (Fin.revPerm (n := N))]
  rw [Matrix.det_transpose]

private lemma sum_sub_val_eq' (n : ℕ) : ∑ x : Fin n, (n - 1 - x.val) = n * (n - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i)]
  rw [Finset.sum_range_reflect (fun i => i)]
  exact Finset.sum_range_id n

private lemma sign_revPerm_eq' (n : ℕ) :
    Equiv.Perm.sign (Fin.revPerm (n := n)) = (-1) ^ (n * (n - 1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  have h : ∀ i : Fin n, ∀ j ∈ Finset.Ioi i,
      (if Fin.revPerm i < Fin.revPerm j then (1 : ℤˣ) else -1) = -1 := by
    intro i j hj
    rw [Finset.mem_Ioi] at hj
    have hnotlt : ¬ Fin.revPerm i < Fin.revPerm j := by
      rw [Fin.revPerm_apply, Fin.revPerm_apply]
      have hrev : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.mpr hj
      exact not_lt.mpr hrev.le
    rw [ite_eq_right hnotlt]
  have h2 : ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      (if Fin.revPerm i < Fin.revPerm j then (1 : ℤˣ) else -1) =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (-1 : ℤˣ) := by
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j hj
    exact h i j hj
  rw [h2]
  simp only [Finset.prod_const]
  simp only [Fin.card_Ioi]
  have h3 : ∏ x : Fin n, (-1 : ℤˣ) ^ (n - 1 - x.val) =
      (-1 : ℤˣ) ^ (∑ x : Fin n, (n - 1 - x.val)) := by
    rw [← Finset.prod_pow_eq_pow_sum]
  rw [h3, sum_sub_val_eq']

private lemma sum_card_Ioi_eq' (n : ℕ) : ∑ i : Fin n, (Finset.Ioi i).card = n * (n - 1) / 2 := by
  simp only [Fin.card_Ioi]
  exact sum_sub_val_eq' n

private lemma units_neg_one_pow_coe' (k : ℕ) :
    (↑((-1 : ℤˣ) ^ k) : MvPolynomial (Fin N) R) = (-1 : MvPolynomial (Fin N) R) ^ k := by
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
             Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- a_ρ equals the Vandermonde determinant. -/
theorem alternant_rho_eq_vandermonde :
    (alternant (rho N) : MvPolynomial (Fin N) R) = vandermonde := by
  rw [alternant_eq_det, det_alternantMatrix_rho]
  rw [vandermonde_eq_signed_det_vandermonde]
  rw [sum_card_Ioi_eq']
  rw [sign_revPerm_eq']
  rw [units_neg_one_pow_coe']

/-- If α has two equal entries, then a_α = 0. (lem.sf.alternant-0 (a)) -/
theorem alternant_eq_zero_of_repeated {α : Fin N → ℕ}
    (h : ∃ i j : Fin N, i ≠ j ∧ α i = α j) :
    (alternant α : MvPolynomial (Fin N) R) = 0 := by
  obtain ⟨i, j, hij, hαij⟩ := h
  unfold alternant
  apply Finset.sum_involution (fun σ _ => Equiv.swap i j * σ)
  · -- f(σ) + f(swap * σ) = 0
    intro σ _
    simp only [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
    rw [show α ∘ (Equiv.swap i j * σ) = α ∘ σ from ?_]
    · simp [add_neg_cancel]
    · ext k
      simp only [comp_apply, Equiv.Perm.coe_mul, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, hαij]
      · rw [h2, ← hαij]
      · rfl
  · -- swap * σ ≠ σ when f(σ) ≠ 0
    intro σ _ _ heq
    have : Equiv.swap i j = 1 := mul_right_cancel heq
    exact hij (Equiv.swap_eq_one_iff.mp this)
  · -- swap * σ ∈ univ
    intro σ _
    exact Finset.mem_univ _
  · -- swap * (swap * σ) = σ
    intro σ _
    exact Equiv.swap_mul_involutive i j σ

/-- Swapping two entries of α negates the alternant. (lem.sf.alternant-0 (b)) -/
theorem alternant_swap {α : Fin N → ℕ} {i j : Fin N} (hij : i ≠ j) :
    (alternant (α ∘ Equiv.swap i j) : MvPolynomial (Fin N) R) = -alternant α := by
  simp only [alternant]
  -- Reindex the sum using the bijection σ ↦ swap i j * σ
  -- Key: (α ∘ swap i j) ∘ σ = α ∘ (swap i j * σ)
  -- After substituting τ = swap i j * σ (equivalently σ = swap i j * τ since swap is self-inverse):
  -- ∑_τ sign(swap * τ) • xPow(α ∘ swap ∘ (swap * τ)) = ∑_τ sign(swap * τ) • xPow(α ∘ τ)
  -- Since sign(swap * τ) = sign(swap) * sign(τ) = -sign(τ), this equals -∑_τ sign(τ) • xPow(α ∘ τ)
  rw [Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap i j))
    (fun σ => Equiv.Perm.sign σ • xPow ((α ∘ Equiv.swap i j) ∘ σ))
    (fun τ => Equiv.Perm.sign (Equiv.swap i j * τ) • xPow (α ∘ τ))
    (fun τ => ?_)]
  · -- After reindexing: ∑_τ (-1 * sign(τ)) • xPow(α ∘ τ) = -∑_σ sign(σ) • xPow(α ∘ σ)
    simp only [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
    rw [← sum_neg_distrib]
    congr 1
    ext σ
    simp only [neg_mul, one_mul, Units.neg_smul]
  · -- Show the reindexing is valid: f(τ) = g(e(τ)) where e = mulLeft(swap)
    -- i.e., sign(τ) • xPow((α ∘ swap) ∘ τ) = sign(swap * (swap * τ)) • xPow(α ∘ (swap * τ))
    -- Using swap * swap = 1, both sides simplify to sign(τ) • xPow(α ∘ (swap * τ))
    simp only [Equiv.coe_mulLeft, Equiv.swap_mul_self_mul]
    -- xPow ((α ∘ swap) ∘ τ) = xPow (α ∘ (swap * τ)) definitionally
    rfl

/-! ## Regular elements and cancellation

This section formalizes Definition def.cring.reg from the source material.

### Definition (def.cring.reg)

Let L be a commutative ring. Let a ∈ L. The element a of L is said to be **regular**
if and only if every x ∈ L satisfying ax = 0 satisfies x = 0.

Regular elements are also called "non-zero-divisors" or "cancellable" elements.

### Connection to Mathlib

In Mathlib, the relevant concepts are:
- `IsLeftRegular a`: left multiplication by `a` is injective (i.e., `a * x = a * y → x = y`)
- `IsRightRegular a`: right multiplication by `a` is injective
- `IsRegular a`: both left and right regular

The textbook definition (ax = 0 → x = 0) is equivalent to `IsLeftRegular` in any ring.
In a commutative ring, `IsLeftRegular` and `IsRightRegular` are equivalent, so
`IsRegular` is equivalent to either one.

The key equivalence is `isLeftRegular_iff_right_eq_zero_of_mul` from Mathlib:
  `IsLeftRegular r ↔ ∀ x, r * x = 0 → x = 0`
-/

section RegularElements

variable {L : Type*} [CommRing L]

/-- **Definition (def.cring.reg)**: An element `a` of a commutative ring `L` is **regular**
    if and only if every `x ∈ L` satisfying `a * x = 0` satisfies `x = 0`.

    This is the textbook definition. We show it's equivalent to Mathlib's `IsLeftRegular`.
    In commutative rings, this is also equivalent to `IsRegular` and `IsRightRegular`. -/
def IsRegularElement (a : L) : Prop := ∀ x : L, a * x = 0 → x = 0

/-- The textbook definition of regular is equivalent to Mathlib's `IsLeftRegular`. -/
theorem isRegularElement_iff_isLeftRegular {a : L} :
    IsRegularElement a ↔ IsLeftRegular a := by
  rw [IsRegularElement, isLeftRegular_iff_right_eq_zero_of_mul]

/-- In a commutative ring, `IsRegularElement` is equivalent to `IsRightRegular`. -/
theorem isRegularElement_iff_isRightRegular {a : L} :
    IsRegularElement a ↔ IsRightRegular a := by
  rw [isRegularElement_iff_isLeftRegular]
  constructor
  · intro h x y hxy
    have : x * a = y * a := hxy
    rw [mul_comm x a, mul_comm y a] at this
    exact h this
  · intro h x y hxy
    have : a * x = a * y := hxy
    rw [mul_comm a x, mul_comm a y] at this
    exact h this

/-- In a commutative ring, `IsRegularElement` is equivalent to Mathlib's `IsRegular`. -/
theorem isRegularElement_iff_isRegular {a : L} :
    IsRegularElement a ↔ _root_.IsRegular a := by
  constructor
  · intro h
    rw [isRegularElement_iff_isLeftRegular] at h
    rw [isRegular_iff]
    exact ⟨h, isRegularElement_iff_isRightRegular.mp (isRegularElement_iff_isLeftRegular.mpr h)⟩
  · intro ⟨h, _⟩
    rw [isRegularElement_iff_isLeftRegular]
    exact h

/-- `IsRegularElement` is equivalent to membership in `nonZeroDivisorsLeft`. -/
theorem isRegularElement_iff_mem_nonZeroDivisorsLeft {a : L} :
    IsRegularElement a ↔ a ∈ nonZeroDivisorsLeft L := by
  rw [isRegularElement_iff_isLeftRegular, isLeftRegular_iff_mem_nonZeroDivisorsLeft]

/-- In a commutative ring, `IsRegularElement` is equivalent to membership in `nonZeroDivisors`. -/
theorem isRegularElement_iff_mem_nonZeroDivisors {a : L} :
    IsRegularElement a ↔ a ∈ nonZeroDivisors L := by
  rw [isRegularElement_iff_isRegular]
  constructor
  · intro h
    exact ⟨h.1.mem_nonZeroDivisorsLeft, h.2.mem_nonZeroDivisorsRight⟩
  · intro h
    constructor
    · exact isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr h.1
    · exact isRightRegular_iff_mem_nonZeroDivisorsRight.mpr h.2

/-- Regular elements are non-zero in a nontrivial ring. -/
theorem IsRegularElement.ne_zero [Nontrivial L] {a : L} (ha : IsRegularElement a) : a ≠ 0 := by
  rw [isRegularElement_iff_isLeftRegular] at ha
  exact ha.ne_zero

/-- Zero is not regular in a nontrivial ring. -/
theorem not_isRegularElement_zero [Nontrivial L] : ¬IsRegularElement (0 : L) := by
  rw [isRegularElement_iff_isLeftRegular]
  exact not_isLeftRegular_zero

/-- Units are regular. -/
theorem IsUnit.isRegularElement' {a : L} (ha : IsUnit a) : IsRegularElement a := by
  rw [isRegularElement_iff_isRegular]
  exact ha.isRegular

/-- One is regular. -/
theorem isRegularElement_one : IsRegularElement (1 : L) :=
  IsUnit.isRegularElement' isUnit_one

/-- The product of regular elements is regular. -/
theorem IsRegularElement.mul {a b : L} (ha : IsRegularElement a) (hb : IsRegularElement b) :
    IsRegularElement (a * b) := by
  rw [isRegularElement_iff_isRegular] at ha hb ⊢
  exact ha.mul hb

/-- **Lemma (lem.cring.reg.cancel)**: Regular elements can be cancelled.
    Let L be a commutative ring. Let a, u, v ∈ L be such that a is regular.
    Assume that au = av. Then u = v. -/
theorem IsRegularElement.cancel {a u v : L} (ha : IsRegularElement a) (h : a * u = a * v) :
    u = v := by
  rw [isRegularElement_iff_isLeftRegular] at ha
  exact ha h

/-- Variant of the cancellation lemma using subtraction. -/
theorem IsRegularElement.cancel_of_mul_eq_zero {a x : L} (ha : IsRegularElement a)
    (h : a * x = 0) : x = 0 :=
  ha x h

end RegularElements

/-- Regular elements can be cancelled (using Mathlib's `IsRegular`). (lem.cring.reg.cancel)
    This is a direct consequence of `IsLeftRegular` (injectivity of left multiplication). -/
theorem isRegular_cancel {L : Type*} [CommRing L] {a u v : L}
    (ha : _root_.IsRegular a) (h : a * u = a * v) : u = v :=
  ha.left h

/-- X i - X j is non-zero when i ≠ j (in a polynomial ring over an integral domain). -/
lemma X_sub_X_ne_zero [IsDomain R] (i j : Fin N) (hij : i ≠ j) :
    (X i - X j : MvPolynomial (Fin N) R) ≠ 0 := by
  intro h
  have h1 : (X i : MvPolynomial (Fin N) R) = X j := sub_eq_zero.mp h
  have h2 := MvPolynomial.X_injective (σ := Fin N) (R := R) h1
  exact hij h2

/-- The Vandermonde polynomial is non-zero (in a polynomial ring over an integral domain). -/
lemma vandermonde_ne_zero [IsDomain R] : (vandermonde : MvPolynomial (Fin N) R) ≠ 0 := by
  unfold vandermonde
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j _
  split_ifs with hij
  · exact X_sub_X_ne_zero i j (ne_of_lt hij)
  · exact one_ne_zero

/-- The alternant a_ρ is a regular element of the polynomial ring.
    (lem.sf.arho-reg)

    Note: This requires R to be an integral domain. In a non-integral domain,
    the polynomial ring has zero divisors and regularity may fail. -/
theorem alternant_rho_isRegular [IsDomain R] :
    _root_.IsRegular (alternant (rho N) : MvPolynomial (Fin N) R) := by
  rw [alternant_rho_eq_vandermonde]
  exact IsRegular.of_ne_zero vandermonde_ne_zero

/-! ## Schur polynomials -/

/-- The monomial x_T = ∏_i x_i^(# of i's in T) for a tableau T.
    By definition, this equals x^(cont(T)). -/
noncomputable def monomialTableau {lam mu : Fin N → ℕ} (T : Tableau lam mu) :
    MvPolynomial (Fin N) R :=
  xPow (contentTableau T)

/-- **Equation (eq.def.sf.content.xT=)**: The monomial x_T equals x^(cont(T)).

    This is the key property of the content: both sides equal ∏ᵢ xᵢ^(# of i's in T).

    This is definitional since `monomialTableau` is defined as `xPow (contentTableau T)`. -/
theorem monomialTableau_eq_xPow_content {lam mu : Fin N → ℕ} (T : Tableau lam mu) :
    (monomialTableau T : MvPolynomial (Fin N) R) = xPow (contentTableau T) := rfl

/-! ## Finiteness of tableaux

The set of semistandard tableaux of any fixed shape is finite, since entries are bounded
by N and the shape is finite. Similarly, the set of Yamanouchi tableaux is finite. -/

/-- IsSemistandard is decidable since it's a conjunction of foralls over finite types. -/
noncomputable instance isSemistandard_decidable {lam mu : Fin N → ℕ} (T : Tableau lam mu) :
    Decidable (IsSemistandard T) := by
  unfold IsSemistandard
  infer_instance

/-- The type of all tableaux of a given shape is finite.
    This follows from the fact that entries are in Fin N and the shape is finite. -/
noncomputable instance tableau_fintype (lam mu : Fin N → ℕ) :
    Fintype (Tableau lam mu) := by
  unfold Tableau
  infer_instance

/-- The type of semistandard tableaux of a given shape is finite.
    This follows from the fact that entries are bounded by N and the shape is finite. -/
noncomputable instance semistandardTableau_fintype (lam mu : Fin N → ℕ) :
    Fintype {T : Tableau lam mu // IsSemistandard T} :=
  Fintype.subtype (Finset.univ.filter IsSemistandard) (by simp)

/-- The skew Schur polynomial s_{lam/mu}.
    Defined as a sum over semistandard tableaux of shape lam/mu:
    s_{lam/mu} = ∑_{T semistandard of shape lam/mu} x^(cont(T))

    Note: This is a finite sum since there are finitely many semistandard tableaux
    of any given shape (entries are bounded by N).

    ## Relationship to Other Definitions

    This project has two skew Schur polynomial definitions with different design tradeoffs:

    | Definition | File | Input | Ring | Use case |
    |------------|------|-------|------|----------|
    | `AlgebraicCombinatorics.skewSchurPoly` (this) | LittlewoodRichardson.lean | `Fin N → ℕ` | generic `R` | Littlewood-Richardson rule, generic rings |
    | `skewSchurPoly` | SchurBasics.lean | `NPartition N` | `ℤ` | Proofs using skew diagrams, symmetry |

    **When to use which:**
    - Use **this definition** when you need a generic coefficient ring `R`, when working
      with the Littlewood-Richardson rule, or when you have an unbundled `Fin N → ℕ`.
    - Use **`SchurBasics.skewSchurPoly`** when working with skew Young diagrams, SSYT
      fillings as explicit structures, or proving symmetry properties. It requires
      `[NeZero N]` and uses integer coefficients.

    **Equivalence:** See `SSYTEquiv.lean` for the bridge between these definitions. -/
noncomputable def skewSchurPoly (lam mu : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  -- Sum over all semistandard tableaux T of shape lam/mu
  -- Each term is x^(cont(T))
  ∑ T : {T : Tableau lam mu // IsSemistandard T}, xPow (contentTableau T.val)

/-- The Schur polynomial s_lam for an N-partition lam.
    Defined as s_{lam/0}, i.e., the skew Schur polynomial with empty inner shape.

    ## Relationship to Other Definitions

    This project has two Schur polynomial definitions with different design tradeoffs:

    | Definition | File | Input | Ring | Use case |
    |------------|------|-------|------|----------|
    | `AlgebraicCombinatorics.schurPoly` (this) | LittlewoodRichardson.lean | `Fin N → ℕ` | generic `R` | Littlewood-Richardson rule, generic rings |
    | `schurPoly` | SchurBasics.lean | `NPartition N` | `ℤ` | Proofs using Young diagrams, symmetry |

    **When to use which:**
    - Use **this definition** when you need a generic coefficient ring `R`, when working
      with the Littlewood-Richardson rule, or when you have an unbundled `Fin N → ℕ`.
    - Use **`SchurBasics.schurPoly`** when working with Young diagrams, SSYT fillings
      as explicit structures, or proving symmetry properties. It requires `[NeZero N]`
      and uses integer coefficients.

    **Equivalence:** The two definitions agree when the partition is valid. See:
    - `SSYTEquiv.schurPoly_eq_schur`: relates `SchurBasics.schurPoly` to `SymmetricFunctions.schur`
    - `schurPoly_eq_AC_schurPoly`: relates `SchurBasics.schurPoly` to this definition -/
noncomputable def schurPoly (lam : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  skewSchurPoly lam 0

/-- s_{lam/0} = s_lam for any partition lam (definitional). -/
theorem skewSchurPoly_zero (lam : Fin N → ℕ) :
    (skewSchurPoly lam 0 : MvPolynomial (Fin N) R) = schurPoly lam := rfl

/-- The type of Yamanouchi tableaux of a given shape is finite.
    This follows from the finiteness of tableaux (Yamanouchi tableaux are a subset). -/
noncomputable instance yamanouchiTableau_fintype (lam mu nu : Fin N → ℕ) :
    Fintype {T : Tableau lam mu // IsYamanouchi nu T} := by
  -- IsYamanouchi T implies IsSemistandard T
  -- So Yamanouchi tableaux are a subset of tableaux, which are finite
  have h : Set.Finite {T : Tableau lam mu | IsYamanouchi nu T} := by
    apply Set.Finite.subset (Set.toFinite (Set.univ : Set (Tableau lam mu)))
    intro T _
    exact Set.mem_univ T
  exact Set.Finite.fintype h

/-! ## Bender-Knuth Involutions

The Bender-Knuth involutions are key tools for proving properties of Schur polynomials.
For each k ∈ [N-1], the k-th Bender-Knuth involution BK_k is a bijection on semistandard
tableaux that swaps certain k's and (k+1)'s while preserving the SSYT property.

### Definition

For a semistandard tableau T and k ∈ [N-1], the Bender-Knuth involution BK_k works as follows:
1. For each row i, consider the cells containing k or k+1
2. Partition these cells into "free" and "forced" based on column constraints:
   - A cell with value k is "forced" if the cell above it has value k
   - A cell with value k+1 is "forced" if the cell below it has value k+1
   - All other k's and (k+1)'s are "free"
3. In each row, swap the free k's with the free (k+1)'s

### Key Properties

1. **Involution**: BK_k ∘ BK_k = id
2. **Preserves SSYT**: If T is semistandard, so is BK_k(T)
3. **Content change**: cont(BK_k(T)) differs from cont(T) by swapping entries k and k+1
4. **Monomial change**: x_{BK_k(T)} = s_k · x_T where s_k swaps x_k and x_{k+1}

### References

- [Stanley, EC2, Section 7.10]
- [Fulton, Young Tableaux, Section 4.3]
- [Bender-Knuth, "Enumeration of plane partitions", 1972]
-/

/-! ### Helper function for swapping adjacent values -/

/-- Swap adjacent values k and k+1 in a Fin N. -/
def swapAdjacentFin (k : Fin N) (hk : k.val + 1 < N) (v : Fin N) : Fin N :=
  if v = k then ⟨k.val + 1, hk⟩
  else if v = ⟨k.val + 1, hk⟩ then k
  else v

@[simp]
lemma swapAdjacentFin_k (k : Fin N) (hk : k.val + 1 < N) :
    swapAdjacentFin k hk k = ⟨k.val + 1, hk⟩ := by
  simp only [swapAdjacentFin, ↓reduceIte]

@[simp]
lemma swapAdjacentFin_kSucc (k : Fin N) (hk : k.val + 1 < N) :
    swapAdjacentFin k hk ⟨k.val + 1, hk⟩ = k := by
  simp only [swapAdjacentFin, ↓reduceIte]
  split_ifs with h
  · simp only [Fin.ext_iff] at h; omega
  · rfl

lemma swapAdjacentFin_other (k : Fin N) (hk : k.val + 1 < N) (v : Fin N)
    (hv1 : v ≠ k) (hv2 : v ≠ ⟨k.val + 1, hk⟩) :
    swapAdjacentFin k hk v = v := by
  simp only [swapAdjacentFin, hv1, hv2, ↓reduceIte]

@[simp]
lemma swapAdjacentFin_involutive (k : Fin N) (hk : k.val + 1 < N) (v : Fin N) :
    swapAdjacentFin k hk (swapAdjacentFin k hk v) = v := by
  by_cases h1 : v = k
  · rw [h1, swapAdjacentFin_k, swapAdjacentFin_kSucc]
  · by_cases h2 : v = ⟨k.val + 1, hk⟩
    · rw [h2, swapAdjacentFin_kSucc, swapAdjacentFin_k]
    · rw [swapAdjacentFin_other k hk v h1 h2, swapAdjacentFin_other k hk v h1 h2]

/-- The swap preserves the "not equal to k" property for values other than k+1. -/
lemma swapAdjacentFin_ne_k_iff (k : Fin N) (hk : k.val + 1 < N) (v : Fin N) :
    swapAdjacentFin k hk v ≠ k ↔ v ≠ ⟨k.val + 1, hk⟩ := by
  constructor
  · intro h hv
    subst hv
    simp at h
  · intro h
    by_cases hv : v = k
    · subst hv
      simp only [swapAdjacentFin_k]
      intro heq
      simp only [Fin.ext_iff] at heq
      omega
    · rw [swapAdjacentFin_other k hk v hv h]
      exact hv

/-- The swap preserves the "not equal to k+1" property for values other than k. -/
lemma swapAdjacentFin_ne_kSucc_iff (k : Fin N) (hk : k.val + 1 < N) (v : Fin N) :
    swapAdjacentFin k hk v ≠ ⟨k.val + 1, hk⟩ ↔ v ≠ k := by
  constructor
  · intro h hv
    subst hv
    simp at h
  · intro h
    by_cases hv : v = ⟨k.val + 1, hk⟩
    · subst hv
      simp only [swapAdjacentFin_kSucc]
      intro heq
      simp only [Fin.ext_iff] at heq
      omega
    · rw [swapAdjacentFin_other k hk v h hv]
      exact hv

/-- The swap is order-preserving on values not equal to k or k+1. -/
lemma swapAdjacentFin_lt_iff_of_ne (k : Fin N) (hk : k.val + 1 < N) (v w : Fin N)
    (hv1 : v ≠ k) (hv2 : v ≠ ⟨k.val + 1, hk⟩)
    (hw1 : w ≠ k) (hw2 : w ≠ ⟨k.val + 1, hk⟩) :
    swapAdjacentFin k hk v < swapAdjacentFin k hk w ↔ v < w := by
  rw [swapAdjacentFin_other k hk v hv1 hv2, swapAdjacentFin_other k hk w hw1 hw2]

/-- Swapping k and k+1 reverses their order. -/
lemma swapAdjacentFin_k_lt_kSucc (k : Fin N) (hk : k.val + 1 < N) :
    swapAdjacentFin k hk ⟨k.val + 1, hk⟩ < swapAdjacentFin k hk k := by
  simp only [swapAdjacentFin_k, swapAdjacentFin_kSucc, Fin.lt_def]
  omega

/-- In row i of tableau T, count the number of cells with value k.
    This is used to define the Bender-Knuth involution. -/
noncomputable def rowCount {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N) (k : Fin N) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // c.val.1 = i ∧ T c = k}

/-- A cell containing k is "k-forced" if there's a k+1 directly BELOW it in the same column.
    This means the k and the k+1 below it form a "pair" that won't be swapped by BK_k.

    **Note**: The original (incorrect) definition said "k above k", but in a semistandard tableau,
    entries strictly increase down columns, so you can't have the same value in vertically
    adjacent cells. The correct definition is: k is paired with k+1 below it. -/
def isForcedK {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = k ∧
  ∃ (c_below : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}),
    c_below.val.2 = c.val.2 ∧ -- same column
    c.val.1.val + 1 = c_below.val.1.val ∧ -- row below (c.row + 1 = c_below.row)
    T c_below = ⟨k.val + 1, hk⟩

/-- A cell containing k+1 is "(k+1)-forced" if there's a k directly ABOVE it in the same column.
    This means the k above and this k+1 form a "pair" that won't be swapped by BK_k.

    **Note**: The original (incorrect) definition said "k+1 below k+1", but in a semistandard
    tableau, entries strictly increase down columns. The correct definition is: k+1 is paired
    with k above it. -/
def isForcedKSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = ⟨k.val + 1, hk⟩ ∧
  ∃ (c_above : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}),
    c_above.val.2 = c.val.2 ∧ -- same column
    c_above.val.1.val + 1 = c.val.1.val ∧ -- row above (c_above.row + 1 = c.row)
    T c_above = k

/-- A cell containing k or k+1 is "free" if it is not forced.
    Free cells can be swapped by the Bender-Knuth involution. -/
def isFreeCell {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  (T c = k ∧ ¬isForcedK T k hk c) ∨
  (T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c)

/-- Count of free k's in row i. -/
noncomputable def freeKCount {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ T c = k ∧ ¬isForcedK T k hk c}

/-- Count of free (k+1)'s in row i. -/
noncomputable def freeKSuccCount {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c}

/-- Count of free k's in row i with column strictly less than j.
    Used for the parenthesis-matching algorithm in Bender-Knuth. -/
noncomputable def freeKCountBefore {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c}

/-- Count of free k's in row i with column at most j.
    Used for the parenthesis-matching algorithm in Bender-Knuth. -/
noncomputable def freeKCountUpTo {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 ≤ j ∧ T c = k ∧ ¬isForcedK T k hk c}

/-- Count of free (k+1)'s in row i with column at most j.
    Used for the parenthesis-matching algorithm in Bender-Knuth. -/
noncomputable def freeKSuccCountUpTo {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 ≤ j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c}

/-- A free k at position c is "unmatched" in the parenthesis-matching sense.

    The Bender-Knuth involution uses a parenthesis-matching algorithm:
    - Read free entries left-to-right in each row
    - Each free (k+1) matches with the nearest unmatched free k to its left
    - Unmatched entries get swapped

    A free k is unmatched iff at its position, the cumulative count of free k's exceeds
    the TOTAL count of free (k+1)'s in the row. In other words, there aren't enough (k+1)'s
    in the entire row to match all the k's up to this position.

    This definition correctly implements the standard parenthesis-matching algorithm:
    - Unmatched k's are exactly those at positions where there's an "excess" of k's
    - These are the rightmost free k's that don't have a (k+1) to match with
    
    Note: We compare freeKCountUpTo(c) with freeKSuccCount (total), not freeKSuccCountUpTo(c),
    because a k can match with any (k+1) to its right, not just (k+1)'s up to its position. -/
def isUnmatchedFreeK {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = k ∧ ¬isForcedK T k hk c ∧
  freeKCountUpTo T c.val.1 k hk c.val.2 > freeKSuccCount T c.val.1 k hk

/-- A free (k+1) at position c is "unmatched" in the parenthesis-matching sense.

    In the BK involution on a semistandard row with `a` free k's followed by `b` free (k+1)'s:
    - If b > a: the LEFTMOST (b-a) free (k+1)'s are unmatched → become k
    - If a ≥ b: all free (k+1)'s are matched (paired with the rightmost b free k's)

    A free (k+1) at position c is unmatched iff it's among the leftmost (b-a) free (k+1)'s,
    i.e., the cumulative count of free (k+1)'s up to c is at most (b-a).

    Equivalently: `freeKSuccCountUpTo(c) + freeKCount ≤ freeKSuccCount`

    This marks the LEFTMOST excess (k+1)'s as unmatched, which is correct for the BK involution.
    The matched pairs are: leftmost min(a,b) k's paired with rightmost min(a,b) (k+1)'s.

    Note: The previous (incorrect) definition used `freeKSuccCountUpTo > freeKCountUpTo`,
    which marked RIGHTMOST (k+1)'s as unmatched — the wrong polarity. -/
def isUnmatchedFreeKSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c ∧
  freeKCount T c.val.1 k hk + freeKSuccCountUpTo T c.val.1 k hk c.val.2 ≤ freeKSuccCount T c.val.1 k hk

/-- A matched free k is a free k that is not unmatched.
    In the parenthesis-matching algorithm, these are the k's that get paired with (k+1)'s. -/
def isMatchedFreeK {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = k ∧ ¬isForcedK T k hk c ∧ ¬isUnmatchedFreeK T k hk c

/-- A matched free (k+1) is a free (k+1) that is not unmatched.
    In the parenthesis-matching algorithm, these are the (k+1)'s that get paired with k's. -/
def isMatchedFreeKSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c ∧ ¬isUnmatchedFreeKSucc T k hk c

/-- The Bender-Knuth involution BK_k on semistandard tableaux.

    This involution swaps UNMATCHED free k's with UNMATCHED free (k+1)'s in each row,
    using a parenthesis-matching algorithm that preserves semistandardness.

    **Algorithm** (for each row independently):
    1. Identify all "free" entries (k's not paired with k+1 below, (k+1)'s not paired with k above)
    2. Read free entries left-to-right, matching each (k+1) with nearest unmatched k to its left
    3. Swap only the UNMATCHED entries: unmatched k → k+1, unmatched (k+1) → k

    **Why this preserves row-weak ordering**:
    - Matched pairs don't change
    - Unmatched k's (which become k+1) are always to the RIGHT of all matched (k+1)'s
    - Unmatched (k+1)'s (which become k) are always to the LEFT of all matched k's

    **Key theorem**: This is an involution that preserves semistandardness
    and swaps the counts of k and k+1 in the content.

    **Note**: The naive cell-by-cell swap (swapping ALL free entries) is INCORRECT
    because adjacent free k and free (k+1) would become (k+1, k), violating row-weak ordering.
    The parenthesis-matching ensures only non-adjacent free entries get swapped. -/
noncomputable def benderKnuth {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (_hT : IsSemistandard T) : Tableau lam mu := by
  classical
  exact fun c =>
    if isUnmatchedFreeK T k hk c then
      ⟨k.val + 1, hk⟩
    else if isUnmatchedFreeKSucc T k hk c then
      k
    else
      T c

-- The Bender-Knuth involution is an involution.
--
-- **Proof strategy** (now possible with corrected definitions):
-- 1. First prove T' = benderKnuth k hk T hT is semistandard
--    - Row-weak: swapping k↔k+1 in free cells preserves weak increase along rows
--    - Column-strict: forced pairs (k above, k+1 below) ensure strict increase down columns
-- 2. Then prove benderKnuth k hk T' hT' = T by showing:
--    - Free k's in T become free (k+1)'s in T' (no k above because of semistandardness)
--    - Free (k+1)'s in T become free k's in T' (no k+1 below because of semistandardness)
--    - Forced cells are unchanged in both directions
-- Helper lemmas for benderKnuth_involutive are defined below.

/-- freeKCountUpTo is monotone in the column index. -/
private lemma freeKCountUpTo_mono {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j₁ j₂ : ℕ) (h : j₁ ≤ j₂) :
    freeKCountUpTo T i k hk j₁ ≤ freeKCountUpTo T i k hk j₂ := by
  unfold freeKCountUpTo
  apply Nat.card_mono
  · haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
      Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
    exact Set.toFinite _
  · intro c hc
    exact ⟨hc.1, le_trans hc.2.1 h, hc.2.2⟩

/-- freeKSuccCountUpTo is monotone in the column index. -/
private lemma freeKSuccCountUpTo_mono {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j₁ j₂ : ℕ) (h : j₁ ≤ j₂) :
    freeKSuccCountUpTo T i k hk j₁ ≤ freeKSuccCountUpTo T i k hk j₂ := by
  unfold freeKSuccCountUpTo
  apply Nat.card_mono
  · haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
      Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
    exact Set.toFinite _
  · intro c hc
    exact ⟨hc.1, le_trans hc.2.1 h, hc.2.2⟩

/-- freeKCountUpTo is strictly monotone on free k cells.
    If c₁ and c₂ are free k cells in the same row with c₁.col < c₂.col,
    then freeKCountUpTo(c₁.col) < freeKCountUpTo(c₂.col).
    
    This is because c₂ is counted in freeKCountUpTo(c₂.col) but not in freeKCountUpTo(c₁.col). -/
private lemma freeKCountUpTo_strictMono_on_freeK {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (_hc₁_row : c₁.val.1 = i) (_hc₁_val : T c₁ = k) (_hc₁_free : ¬isForcedK T k hk c₁)
    (hc₂_row : c₂.val.1 = i) (hc₂_val : T c₂ = k) (hc₂_free : ¬isForcedK T k hk c₂)
    (hcol : c₁.val.2 < c₂.val.2) :
    freeKCountUpTo T i k hk c₁.val.2 < freeKCountUpTo T i k hk c₂.val.2 := by
  unfold freeKCountUpTo
  -- The set for c₂.col strictly contains the set for c₁.col
  -- because c₂ is in the former but not the latter
  haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
  -- Define the two sets as Sets
  let S₁ : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ c.val.2 ≤ c₁.val.2 ∧ T c = k ∧ ¬isForcedK T k hk c}
  let S₂ : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ c.val.2 ≤ c₂.val.2 ∧ T c = k ∧ ¬isForcedK T k hk c}
  -- Show S₁ ⊂ S₂ (strict subset)
  have h_ssubset : S₁ ⊂ S₂ := by
    constructor
    · intro c hc
      exact ⟨hc.1, le_trans hc.2.1 (le_of_lt hcol), hc.2.2⟩
    · intro h_eq
      have h_c₂_in : c₂ ∈ S₂ := ⟨hc₂_row, le_refl _, hc₂_val, hc₂_free⟩
      have h_c₂_in' := h_eq h_c₂_in
      have : c₂.val.2 ≤ c₁.val.2 := h_c₂_in'.2.1
      omega
  have h_S₂_finite : S₂.Finite := Set.toFinite _
  exact h_S₂_finite.card_lt_card h_ssubset

/-- freeKCountUpTo(j₁) ≤ freeKCountBefore(j₂) when j₁ < j₂.
    This is because {col ≤ j₁} ⊆ {col < j₂} when j₁ < j₂.
    Key lemma for proving row-weak preservation of BK. -/
private lemma freeKCountUpTo_le_freeKCountBefore {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j₁ j₂ : ℕ) (h : j₁ < j₂) :
    freeKCountUpTo T i k hk j₁ ≤ freeKCountBefore T i k hk j₂ := by
  unfold freeKCountUpTo freeKCountBefore
  apply Nat.card_mono
  · haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
      Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
    exact Set.toFinite _
  · intro c hc
    exact ⟨hc.1, Nat.lt_of_le_of_lt hc.2.1 h, hc.2.2⟩

/-- freeKCountUpTo(j) ≤ freeKCount (the total in the row).
    This is because {col ≤ j} ⊆ {all cols}.
    Key lemma for proving row-weak preservation of BK. -/
private lemma freeKCountUpTo_le_freeKCount {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) :
    freeKCountUpTo T i k hk j ≤ freeKCount T i k hk := by
  unfold freeKCountUpTo freeKCount
  apply Nat.card_mono
  · haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
      Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
    exact Set.toFinite _
  · intro c hc
    exact ⟨hc.1, hc.2.2⟩

/-- freeKSuccCountUpTo(j) ≤ freeKSuccCount (the total in the row).
    This is because {col ≤ j} ⊆ {all cols}.
    Key lemma for proving row-weak preservation of BK. -/
private lemma freeKSuccCountUpTo_le_freeKSuccCount {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) :
    freeKSuccCountUpTo T i k hk j ≤ freeKSuccCount T i k hk := by
  unfold freeKSuccCountUpTo freeKSuccCount
  apply Nat.card_mono
  · haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
      Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
    exact Set.toFinite _
  · intro c hc
    exact ⟨hc.1, hc.2.2⟩

/-- Key impossibility lemma: If c₁.col < c₂.col in the same row, then c₁ cannot be an
    unmatched free k while c₂ is an unmatched free (k+1).
    
    This is the crucial lemma for proving row-weak preservation of BK.
    With the corrected definitions:
    - isUnmatchedFreeK c₁: freeKCountUpTo(c₁.col) > freeKSuccCount (total)
    - isUnmatchedFreeKSucc c₂: freeKCount + freeKSuccCountUpTo(c₂.col) ≤ freeKSuccCount
    
    Proof: 
    From (1): freeKCountUpTo(c₁.col) > freeKSuccCount
    Since freeKCount ≥ freeKCountUpTo(c₁.col), we have freeKCount > freeKSuccCount.
    From (2): freeKCount + freeKSuccCountUpTo(c₂.col) ≤ freeKSuccCount
    This implies freeKCount ≤ freeKSuccCount (since freeKSuccCountUpTo ≥ 0).
    But freeKCount > freeKSuccCount contradicts freeKCount ≤ freeKSuccCount! -/
private lemma not_unmatched_k_and_unmatched_kSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (_h_col : c₁.val.2 < c₂.val.2)
    (h_c₁_unmatched_k : isUnmatchedFreeK T k hk c₁)
    (h_c₂_unmatched_kSucc : isUnmatchedFreeKSucc T k hk c₂) : False := by
  -- Extract the key inequalities from the unmatched conditions
  -- From isUnmatchedFreeK: freeKCountUpTo(c₁.col) > freeKSuccCount
  have h1 : freeKCountUpTo T c₁.val.1 k hk c₁.val.2 > freeKSuccCount T c₁.val.1 k hk := 
    h_c₁_unmatched_k.2.2
  -- From isUnmatchedFreeKSucc: freeKCount + freeKSuccCountUpTo(c₂.col) ≤ freeKSuccCount
  have h2 : freeKCount T c₂.val.1 k hk + freeKSuccCountUpTo T c₂.val.1 k hk c₂.val.2 ≤ 
            freeKSuccCount T c₂.val.1 k hk := h_c₂_unmatched_kSucc.2.2
  -- freeKCountUpTo(c₁.col) ≤ freeKCount (cumulative ≤ total)
  have h_upto_le_total : freeKCountUpTo T c₁.val.1 k hk c₁.val.2 ≤ freeKCount T c₁.val.1 k hk := 
    freeKCountUpTo_le_freeKCount T c₁.val.1 k hk c₁.val.2
  -- Rewrite using h_row to use same row index
  rw [h_row] at h1 h_upto_le_total
  -- From h1 and h_upto_le_total: freeKCount > freeKSuccCount
  have h_k_gt_kSucc : freeKCount T c₂.val.1 k hk > freeKSuccCount T c₂.val.1 k hk := by
    calc freeKCount T c₂.val.1 k hk 
        ≥ freeKCountUpTo T c₂.val.1 k hk c₁.val.2 := h_upto_le_total
      _ > freeKSuccCount T c₂.val.1 k hk := h1
  -- From h2: freeKCount ≤ freeKSuccCount - freeKSuccCountUpTo ≤ freeKSuccCount
  have h_k_le_kSucc : freeKCount T c₂.val.1 k hk ≤ freeKSuccCount T c₂.val.1 k hk := by
    omega
  -- Contradiction: freeKCount > freeKSuccCount AND freeKCount ≤ freeKSuccCount
  omega

/-- Key lemma: in a semistandard tableau, if c₁ and c₂ are both k's in the same row
    with c₁.col < c₂.col, then freeKSuccCountUpTo is the same for both.
    This is because any cell between them must have value ≤ k by row-weak ordering,
    so there are no (k+1)'s between c₁ and c₂. -/
private lemma freeKSuccCountUpTo_eq_between_k {lam mu : Fin N → ℕ} (T : Tableau lam mu) (hT : IsSemistandard T)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (h_col : c₁.val.2 < c₂.val.2)
    (_h_c₁_k : T c₁ = k)
    (h_c₂_k : T c₂ = k) :
    freeKSuccCountUpTo T c₂.val.1 k hk c₂.val.2 = freeKSuccCountUpTo T c₁.val.1 k hk c₁.val.2 := by
  unfold freeKSuccCountUpTo
  -- The predicates define the same set of cells
  have h_pred_eq : ∀ c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu},
      (c.val.1 = c₂.val.1 ∧ c.val.2 ≤ c₂.val.2 ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c) ↔
      (c.val.1 = c₁.val.1 ∧ c.val.2 ≤ c₁.val.2 ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c) := by
    intro c
    constructor
    · intro ⟨hc_row, hc_col_le, hc_val, hc_free⟩
      by_cases hc_col : c.val.2 ≤ c₁.val.2
      · exact ⟨hc_row.trans h_row.symm, hc_col, hc_val, hc_free⟩
      · -- c.val.2 > c₁.val.2, contradiction via semistandardness
        push Not at hc_col
        exfalso
        -- c is between c₁ and c₂ (or at c₂), and T c = k+1
        -- But T c ≤ T c₂ = k (by row-weak), so k+1 ≤ k, contradiction
        cases' Nat.lt_or_eq_of_le hc_col_le with hlt heq
        · -- c.val.2 < c₂.val.2: T c ≤ T c₂, but T c = k+1 and T c₂ = k
          have h1 : T c ≤ T c₂ := hT.1 c c₂ hc_row hlt
          rw [hc_val, h_c₂_k] at h1
          simp only [Fin.le_def] at h1
          omega
        · -- c.val.2 = c₂.val.2: same cell, but T c = k+1 and T c₂ = k
          have hc_eq_c₂ : c = c₂ := by
            apply Subtype.ext
            apply Prod.ext
            · exact hc_row
            · exact heq
          rw [hc_eq_c₂, h_c₂_k] at hc_val
          simp only [Fin.ext_iff] at hc_val
          omega
    · intro ⟨hc_row, hc_col_le, hc_val, hc_free⟩
      exact ⟨hc_row.trans h_row, Nat.le_trans hc_col_le (Nat.le_of_lt h_col), hc_val, hc_free⟩
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl _) h_pred_eq

private lemma matched_k_propagates_left {lam mu : Fin N → ℕ} (T : Tableau lam mu) (_hT : IsSemistandard T)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (h_col : c₁.val.2 < c₂.val.2)
    (_h_c₁_free_k : T c₁ = k ∧ ¬isForcedK T k hk c₁)
    (h_c₂_free_k : T c₂ = k ∧ ¬isForcedK T k hk c₂)
    (h_c₂_matched : ¬isUnmatchedFreeK T k hk c₂) :
    ¬isUnmatchedFreeK T k hk c₁ := by
  -- With the corrected definition of isUnmatchedFreeK (using freeKSuccCount instead of 
  -- freeKSuccCountUpTo), matched k's propagate left because:
  -- - If c₂ is matched, then freeKCountUpTo(c₂) ≤ freeKSuccCount (total)
  -- - Since c₁.col < c₂.col, freeKCountUpTo(c₁) < freeKCountUpTo(c₂) 
  --   (c₁ contributes to the count at c₂ but not at c₁)
  -- - Therefore freeKCountUpTo(c₁) < freeKCountUpTo(c₂) ≤ freeKSuccCount
  -- - So c₁ is also matched
  intro h_c₁_unmatched
  apply h_c₂_matched
  unfold isUnmatchedFreeK at h_c₁_unmatched ⊢
  refine ⟨h_c₂_free_k.1, h_c₂_free_k.2, ?_⟩
  -- Need: freeKCountUpTo c₂ > freeKSuccCount
  -- From h_c₁_unmatched: freeKCountUpTo c₁ > freeKSuccCount
  -- freeKSuccCount is the same for both (it's the total count in the row)
  have h_succ_eq : freeKSuccCount T c₂.val.1 k hk = freeKSuccCount T c₁.val.1 k hk := by
    rw [h_row]
  -- freeKCountUpTo is monotone
  have h_mono : freeKCountUpTo T c₁.val.1 k hk c₁.val.2 ≤ 
                freeKCountUpTo T c₂.val.1 k hk c₂.val.2 := by
    rw [h_row]
    exact freeKCountUpTo_mono T c₂.val.1 k hk c₁.val.2 c₂.val.2 (Nat.le_of_lt h_col)
  -- Combine: freeKCountUpTo c₂ ≥ freeKCountUpTo c₁ > freeKSuccCount c₁ = freeKSuccCount c₂
  rw [h_succ_eq]
  omega

/-- Key lemma: in a semistandard tableau, if c₁ and c₂ are both (k+1)'s in the same row
    with c₁.col < c₂.col, then freeKCountBefore is the same for both.
    This is because any cell between them must have value ≥ k+1 by row-weak ordering,
    so there are no k's between c₁ and c₂. -/
private lemma freeKCountBefore_eq_between_kSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu) (hT : IsSemistandard T)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (h_col : c₁.val.2 < c₂.val.2)
    (h_c₁_kSucc : T c₁ = ⟨k.val + 1, hk⟩)
    (_h_c₂_kSucc : T c₂ = ⟨k.val + 1, hk⟩) :
    freeKCountBefore T c₂.val.1 k hk c₂.val.2 = freeKCountBefore T c₁.val.1 k hk c₁.val.2 := by
  unfold freeKCountBefore
  -- The predicates define the same set of cells
  have h_pred_eq : ∀ c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu},
      (c.val.1 = c₂.val.1 ∧ c.val.2 < c₂.val.2 ∧ T c = k ∧ ¬isForcedK T k hk c) ↔
      (c.val.1 = c₁.val.1 ∧ c.val.2 < c₁.val.2 ∧ T c = k ∧ ¬isForcedK T k hk c) := by
    intro c
    constructor
    · intro ⟨hc_row, hc_col_lt, hc_val, hc_free⟩
      by_cases hc_col : c.val.2 < c₁.val.2
      · exact ⟨hc_row.trans h_row.symm, hc_col, hc_val, hc_free⟩
      · -- c.val.2 ≥ c₁.val.2, contradiction via semistandardness
        push Not at hc_col
        exfalso
        cases' Nat.lt_or_eq_of_le hc_col with hlt heq
        · -- c₁.val.2 < c.val.2: T c₁ ≤ T c, but T c₁ = k+1 and T c = k
          have h1 : T c₁ ≤ T c := hT.1 c₁ c (hc_row.trans h_row.symm).symm hlt
          rw [h_c₁_kSucc, hc_val] at h1
          simp only [Fin.le_def] at h1
          omega
        · -- c.val.2 = c₁.val.2: same cell, but T c = k and T c₁ = k+1
          have hc_eq_c₁ : c = c₁ := by
            apply Subtype.ext
            apply Prod.ext
            · exact hc_row.trans h_row.symm
            · exact heq.symm
          rw [hc_eq_c₁, h_c₁_kSucc] at hc_val
          simp only [Fin.ext_iff] at hc_val
          omega
    · intro ⟨hc_row, hc_col_lt, hc_val, hc_free⟩
      exact ⟨hc_row.trans h_row, Nat.lt_trans hc_col_lt h_col, hc_val, hc_free⟩
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl _) h_pred_eq

/-- freeKCountUpTo is constant between two (k+1)'s in a semistandard tableau.
    This is because in a semistandard tableau, k's come before (k+1)'s in each row,
    so there are no k's between two (k+1)'s. -/
private lemma freeKCountUpTo_eq_between_kSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu) (hT : IsSemistandard T)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (h_col : c₁.val.2 < c₂.val.2)
    (h_c₁_kSucc : T c₁ = ⟨k.val + 1, hk⟩)
    (_h_c₂_kSucc : T c₂ = ⟨k.val + 1, hk⟩) :
    freeKCountUpTo T c₂.val.1 k hk c₂.val.2 = freeKCountUpTo T c₁.val.1 k hk c₁.val.2 := by
  unfold freeKCountUpTo
  have h_pred_eq : ∀ c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu},
      (c.val.1 = c₂.val.1 ∧ c.val.2 ≤ c₂.val.2 ∧ T c = k ∧ ¬isForcedK T k hk c) ↔
      (c.val.1 = c₁.val.1 ∧ c.val.2 ≤ c₁.val.2 ∧ T c = k ∧ ¬isForcedK T k hk c) := by
    intro c
    constructor
    · intro ⟨hc_row, hc_col_le, hc_val, hc_free⟩
      by_cases hc_col : c.val.2 ≤ c₁.val.2
      · exact ⟨hc_row.trans h_row.symm, hc_col, hc_val, hc_free⟩
      · push Not at hc_col
        exfalso
        have h1 : T c₁ ≤ T c := hT.1 c₁ c (hc_row.trans h_row.symm).symm hc_col
        rw [h_c₁_kSucc, hc_val] at h1
        simp only [Fin.le_def] at h1
        omega
    · intro ⟨hc_row, hc_col_le, hc_val, hc_free⟩
      refine ⟨hc_row.trans h_row, ?_, hc_val, hc_free⟩
      exact Nat.le_trans hc_col_le (Nat.le_of_lt h_col)
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl _) h_pred_eq

/-- At a (k+1) position in a semistandard tableau, freeKCountUpTo equals freeKCount.
    This is because all free k's are to the left of all (k+1)'s by row-weak ordering. -/
private lemma freeKCountUpTo_eq_freeKCount_at_kSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu) (hT : IsSemistandard T)
    (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_kSucc : T c = ⟨k.val + 1, hk⟩) :
    freeKCountUpTo T c.val.1 k hk c.val.2 = freeKCount T c.val.1 k hk := by
  unfold freeKCountUpTo freeKCount
  -- Show the sets are equal by showing any free k has column ≤ c.col
  have h_pred_eq : ∀ d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu},
      (d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ T d = k ∧ ¬isForcedK T k hk d) ↔
      (d.val.1 = c.val.1 ∧ T d = k ∧ ¬isForcedK T k hk d) := by
    intro d
    constructor
    · intro ⟨hd_row, _, hd_val, hd_free⟩
      exact ⟨hd_row, hd_val, hd_free⟩
    · intro ⟨hd_row, hd_val, hd_free⟩
      refine ⟨hd_row, ?_, hd_val, hd_free⟩
      -- Need to show d.col ≤ c.col
      -- If d.col > c.col, then by row-weak T(c) ≤ T(d), i.e., k+1 ≤ k, contradiction
      by_contra h_gt
      push Not at h_gt
      have h1 : T c ≤ T d := hT.1 c d hd_row.symm h_gt
      rw [h_kSucc, hd_val] at h1
      simp only [Fin.le_def] at h1
      omega
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl _) h_pred_eq

/-- At a k position in a semistandard tableau, freeKSuccCountUpTo equals 0.
    This is because all (k+1)'s are to the right of all k's by row-weak ordering.
    
    More precisely: if T c = k, then any cell d in the same row with T d = k+1 must have d.col > c.col.
    Therefore there are no free (k+1)'s at columns ≤ c.col. -/
private lemma freeKSuccCountUpTo_eq_zero_at_k {lam mu : Fin N → ℕ} (T : Tableau lam mu) (hT : IsSemistandard T)
    (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_k : T c = k) :
    freeKSuccCountUpTo T c.val.1 k hk c.val.2 = 0 := by
  unfold freeKSuccCountUpTo
  -- Show the set is empty: any cell d with T d = k+1 in the same row must have d.col > c.col
  have h_empty : ∀ d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu},
      ¬(d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d) := by
    intro d ⟨hd_row, hd_col_le, hd_val, _⟩
    -- If d.col ≤ c.col and d.row = c.row, then by row-weak T d ≤ T c
    -- But T d = k+1 > k = T c, contradiction
    by_cases h_col_eq : d.val.2 = c.val.2
    · -- d.col = c.col, so d = c (same row, same col)
      have h_eq : d = c := Subtype.ext (Prod.ext hd_row h_col_eq)
      rw [h_eq, h_k] at hd_val
      simp only [Fin.ext_iff] at hd_val
      omega
    · -- d.col < c.col
      have h_col_lt : d.val.2 < c.val.2 := Nat.lt_of_le_of_ne hd_col_le h_col_eq
      have h1 : T d ≤ T c := hT.1 d c hd_row h_col_lt
      rw [hd_val, h_k] at h1
      simp only [Fin.le_def] at h1
      omega
  -- The cardinality of an empty set is 0
  have h_card_zero : Nat.card {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} //
      d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} = 0 := by
    rw [Nat.card_eq_zero]
    left
    rw [isEmpty_subtype]
    exact h_empty
  exact h_card_zero

/-- If c₁.col < c₂.col are both free (k+1)'s in the same row, and c₁ is matched, then c₂ is matched.
    This is a key lemma for proving row-weak preservation of BK. 
    
    With corrected definitions, a free (k+1) at c is unmatched iff:
    `freeKCount + freeKSuccCountUpTo(c) ≤ freeKSuccCount`
    
    This marks the LEFTMOST free (k+1)'s as unmatched. So:
    - If c₁ is matched (not among the leftmost unmatched), then c₂ (to the right) is also matched.
    - Contrapositive: If c₂ is unmatched, then c₁ is also unmatched.
    
    Proof: Since freeKSuccCountUpTo is monotonic in column, and c₁.col < c₂.col:
    freeKSuccCountUpTo(c₁) ≤ freeKSuccCountUpTo(c₂)
    
    If c₁ is matched: freeKCount + freeKSuccCountUpTo(c₁) > freeKSuccCount
    Then: freeKCount + freeKSuccCountUpTo(c₂) ≥ freeKCount + freeKSuccCountUpTo(c₁) > freeKSuccCount
    So c₂ is also matched. -/
private lemma matched_kSucc_propagates_right {lam mu : Fin N → ℕ} (T : Tableau lam mu) (_hT : IsSemistandard T)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (h_col : c₁.val.2 < c₂.val.2)
    (h_c₁_free_kSucc : T c₁ = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c₁)
    (_h_c₂_free_kSucc : T c₂ = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c₂)
    (h_c₁_matched : ¬isUnmatchedFreeKSucc T k hk c₁) :
    ¬isUnmatchedFreeKSucc T k hk c₂ := by
  -- Extract the counting inequality from h_c₁_matched
  unfold isUnmatchedFreeKSucc at h_c₁_matched ⊢
  push Not at h_c₁_matched
  -- h_c₁_matched: T c₁ = k+1 → ¬isForcedKSucc c₁ → freeKCount + freeKSuccCountUpTo(c₁) > freeKSuccCount
  have h_gt : freeKSuccCount T c₁.val.1 k hk < freeKCount T c₁.val.1 k hk + freeKSuccCountUpTo T c₁.val.1 k hk c₁.val.2 := 
    h_c₁_matched h_c₁_free_kSucc.1 h_c₁_free_kSucc.2
  -- Monotonicity: freeKSuccCountUpTo(c₁) ≤ freeKSuccCountUpTo(c₂)
  have h_mono : freeKSuccCountUpTo T c₁.val.1 k hk c₁.val.2 ≤ freeKSuccCountUpTo T c₂.val.1 k hk c₂.val.2 := by
    rw [h_row]
    exact freeKSuccCountUpTo_mono T c₂.val.1 k hk c₁.val.2 c₂.val.2 (le_of_lt h_col)
  -- Show c₂ is matched
  intro ⟨_, _, h_le⟩
  -- h_le: freeKCount(c₂.row) + freeKSuccCountUpTo(c₂) ≤ freeKSuccCount(c₂.row)
  -- Rewrite h_gt to use c₂.val.1
  rw [h_row] at h_gt
  -- Now h_gt: freeKSuccCount(c₂.row) < freeKCount(c₂.row) + freeKSuccCountUpTo(c₁.row, c₁.col)
  -- But freeKSuccCountUpTo(c₁.row, c₁.col) = freeKSuccCountUpTo(c₂.row, c₁.col) (by h_row)
  -- And freeKSuccCountUpTo(c₂.row, c₁.col) ≤ freeKSuccCountUpTo(c₂.row, c₂.col) (by h_mono)
  rw [h_row] at h_mono
  -- h_mono: freeKSuccCountUpTo(c₂.row, c₁.col) ≤ freeKSuccCountUpTo(c₂.row, c₂.col)
  -- Combining: freeKSuccCount < freeKCount + freeKSuccCountUpTo(c₂.row, c₁.col) 
  --                           ≤ freeKCount + freeKSuccCountUpTo(c₂.row, c₂.col)
  --                           ≤ freeKSuccCount (by h_le)
  -- Contradiction!
  omega

/-- In a skew diagram with mu weakly decreasing, if (i, j₁) and (i+1, j₂) are both in the diagram 
    with j₁ < j₂, then (i+1, j₁) is also in the diagram.
    This is a key geometric fact for proving row-weak preservation of BK. -/
private lemma skewYoungDiagram_cell_below_exists' {lam mu : Fin N → ℕ}
    (hmu : IsNPartition mu)
    (i : Fin N) (hi : i.val + 1 < N) (j₁ j₂ : ℕ) (hj : j₁ < j₂)
    (h1 : ((i, j₁) : Fin N × ℕ) ∈ skewYoungDiagram lam mu)
    (h2 : ((⟨i.val + 1, hi⟩ : Fin N), j₂) ∈ skewYoungDiagram lam mu) :
    ((⟨i.val + 1, hi⟩ : Fin N), j₁) ∈ skewYoungDiagram lam mu := by
  simp only [skewYoungDiagram, Set.mem_ofPred_eq] at h1 h2 ⊢
  constructor
  · have hmu_le : mu ⟨i.val + 1, hi⟩ ≤ mu i := hmu i ⟨i.val + 1, hi⟩ (by simp only [Fin.le_def]; omega)
    omega
  · omega

/-- Columns are contiguous when lam and mu are N-partitions.
    If (i₁, j) and (i₂, j) are in the diagram with i₁ < i₂, then (i, j) is in the diagram for all i₁ ≤ i ≤ i₂. -/
private lemma skewYoungDiagram_column_contiguous {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (i₁ i₂ : Fin N) (j : ℕ) (_hi : i₁ < i₂)
    (h1 : (i₁, j) ∈ skewYoungDiagram lam mu)
    (h2 : (i₂, j) ∈ skewYoungDiagram lam mu)
    (i : Fin N) (hi1 : i₁ ≤ i) (hi2 : i ≤ i₂) :
    (i, j) ∈ skewYoungDiagram lam mu := by
  simp only [skewYoungDiagram, Set.mem_ofPred_eq] at h1 h2 ⊢
  constructor
  · have hmu_le : mu i ≤ mu i₁ := hmu i₁ i hi1
    omega
  · have hlam_le : lam i₂ ≤ lam i := hlam i i₂ hi2
    omega

/-- If c₁ and c₂ are in the same column with c₁.row < c₂.row,
    then either they're adjacent or there's an intermediate cell.
    This requires lam and mu to be N-partitions (columns are contiguous). -/
private lemma skewYoungDiagram_adjacent_or_intermediate {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_col : c₁.val.2 = c₂.val.2) (h_row : c₁.val.1 < c₂.val.1) :
    c₁.val.1.val + 1 = c₂.val.1.val ∨
    ∃ (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}),
      c.val.2 = c₁.val.2 ∧ c₁.val.1 < c.val.1 ∧ c.val.1 < c₂.val.1 := by
  by_cases h_adjacent : c₁.val.1.val + 1 = c₂.val.1.val
  · left; exact h_adjacent
  · right
    have h_gap : c₁.val.1.val + 1 < c₂.val.1.val := by
      simp only [Fin.lt_def] at h_row
      omega
    have hi : c₁.val.1.val + 1 < N := by
      have := c₂.val.1.isLt
      omega
    let i_mid : Fin N := ⟨c₁.val.1.val + 1, hi⟩
    have h_mid_in : (i_mid, c₁.val.2) ∈ skewYoungDiagram lam mu := by
      apply skewYoungDiagram_column_contiguous hlam hmu c₁.val.1 c₂.val.1 c₁.val.2
      · exact h_row
      · exact c₁.prop
      · rw [h_col]; exact c₂.prop
      · simp only [Fin.le_def, i_mid]; omega
      · simp only [Fin.le_def, i_mid]; omega
    refine ⟨⟨(i_mid, c₁.val.2), h_mid_in⟩, ?_, ?_, ?_⟩
    · rfl
    · simp only [Fin.lt_def, i_mid]; omega
    · simp only [Fin.lt_def, i_mid]; exact h_gap

/-- If T c₁ = k and T c₂ = k+1 in the same column with c₁.row < c₂.row,
    then c₁ and c₂ are adjacent (c₁.row + 1 = c₂.row).
    This requires lam and mu to be N-partitions.
    
    Proof: If they're not adjacent, there's an intermediate cell c_mid.
    By column-strict: k < T c_mid < k+1, which is impossible. -/
private lemma adjacent_k_kSucc_in_column {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_col : c₁.val.2 = c₂.val.2) (h_row : c₁.val.1 < c₂.val.1)
    (h_c₁_val : T c₁ = k) (h_c₂_val : T c₂ = ⟨k.val + 1, hk⟩) :
    c₁.val.1.val + 1 = c₂.val.1.val := by
  rcases skewYoungDiagram_adjacent_or_intermediate hlam hmu c₁ c₂ h_col h_row with h_adj | ⟨c_mid, h_mid_col, h_mid_row1, h_mid_row2⟩
  · exact h_adj
  · exfalso
    have h1 : T c₁ < T c_mid := hT.2 c₁ c_mid h_mid_col.symm h_mid_row1
    have h2 : T c_mid < T c₂ := hT.2 c_mid c₂ (h_mid_col.trans h_col) h_mid_row2
    rw [h_c₁_val] at h1
    rw [h_c₂_val] at h2
    simp only [Fin.lt_def] at h1 h2
    omega

/-- If c₁ and c₂ are adjacent in the same column (c₁ directly above c₂) with T c₁ = k and T c₂ = k+1,
    then c₁ is forced k. This is because c₂ (with value k+1) is directly below c₁. -/
private lemma adjacent_k_kSucc_implies_forced_k {lam mu : Fin N → ℕ} (T : Tableau lam mu)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_col : c₁.val.2 = c₂.val.2)
    (h_adj : c₁.val.1.val + 1 = c₂.val.1.val)
    (h_c₁_val : T c₁ = k) (h_c₂_val : T c₂ = ⟨k.val + 1, hk⟩) :
    isForcedK T k hk c₁ :=
  ⟨h_c₁_val, c₂, h_col.symm, h_adj, h_c₂_val⟩

/-- If c₁ and c₂ are adjacent in the same column (c₁ directly above c₂) with T c₁ = k and T c₂ = k+1,
    then c₂ is forced k+1. This is because c₁ (with value k) is directly above c₂. -/
private lemma adjacent_k_kSucc_implies_forced_kSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_col : c₁.val.2 = c₂.val.2)
    (h_adj : c₁.val.1.val + 1 = c₂.val.1.val)
    (h_c₁_val : T c₁ = k) (h_c₂_val : T c₂ = ⟨k.val + 1, hk⟩) :
    isForcedKSucc T k hk c₂ :=
  ⟨h_c₂_val, c₁, h_col, h_adj, h_c₁_val⟩

/-- If c₁ and c₂ are adjacent in the same column (c₁ directly above c₂) with T c₁ = k and T c₂ = k+1,
    then neither can be unmatched free (both are forced). -/
private lemma adjacent_k_kSucc_not_unmatched {lam mu : Fin N → ℕ} (T : Tableau lam mu)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_col : c₁.val.2 = c₂.val.2)
    (h_adj : c₁.val.1.val + 1 = c₂.val.1.val)
    (h_c₁_val : T c₁ = k) (h_c₂_val : T c₂ = ⟨k.val + 1, hk⟩) :
    ¬isUnmatchedFreeK T k hk c₁ ∧ ¬isUnmatchedFreeKSucc T k hk c₂ := by
  constructor
  · intro h
    have hforced : isForcedK T k hk c₁ := adjacent_k_kSucc_implies_forced_k T k hk c₁ c₂ h_col h_adj h_c₁_val h_c₂_val
    exact h.2.1 hforced
  · intro h
    have hforced : isForcedKSucc T k hk c₂ := adjacent_k_kSucc_implies_forced_kSucc T k hk c₁ c₂ h_col h_adj h_c₁_val h_c₂_val
    exact h.2.1 hforced

/-- Key lemma: In a semistandard tableau, if c₁.col < c₂.col in the same row,
    T c₁ = k (free), T c₂ = k (forced), and there exists a cell below c₁,
    then we get a contradiction.
    
    Proof: If c₂ is forced k, there's a k+1 below c₂. 
    If c₁ is free k, the cell below c₁ has value > k+1 (by column-strict + c₁ free).
    By row-weak in the row below, we'd need (value below c₁) ≤ k+1, contradiction. -/
private lemma no_free_k_left_of_forced_k {lam mu : Fin N → ℕ} (T : Tableau lam mu) (hT : IsSemistandard T)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (c₁_below : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_c₁_below_col : c₁_below.val.2 = c₁.val.2)
    (h_c₁_below_row : c₁.val.1.val + 1 = c₁_below.val.1.val)
    (h_row : c₁.val.1 = c₂.val.1) (h_col : c₁.val.2 < c₂.val.2)
    (h_c₁_val : T c₁ = k) (h_c₁_free : ¬isForcedK T k hk c₁)
    (h_c₂_forced : isForcedK T k hk c₂) : False := by
  obtain ⟨_, c₂_below, h_c₂_below_col, h_c₂_below_row, h_c₂_below_val⟩ := h_c₂_forced
  have h_strict : T c₁ < T c₁_below := hT.2 c₁ c₁_below h_c₁_below_col.symm (by 
    simp only [Fin.lt_def]; omega)
  rw [h_c₁_val] at h_strict
  have h_ge_k1 : (T c₁_below).val ≥ k.val + 1 := by simp only [Fin.lt_def] at h_strict; omega
  have h_ne_k1 : T c₁_below ≠ ⟨k.val + 1, hk⟩ := by
    intro h_eq
    apply h_c₁_free
    exact ⟨h_c₁_val, c₁_below, h_c₁_below_col, h_c₁_below_row, h_eq⟩
  have h_gt_k1 : (T c₁_below).val > k.val + 1 := by
    cases' Nat.lt_or_eq_of_le h_ge_k1 with hlt heq
    · exact hlt
    · exfalso; apply h_ne_k1; ext; exact heq.symm
  have h_row_below : c₁_below.val.1 = c₂_below.val.1 := by
    ext
    have h1 : c₁.val.1.val + 1 = c₁_below.val.1.val := h_c₁_below_row
    have h2 : c₂.val.1.val + 1 = c₂_below.val.1.val := h_c₂_below_row
    have h3 : c₁.val.1.val = c₂.val.1.val := by
      have := congrArg Fin.val h_row
      exact this
    omega
  have h_col_below : c₁_below.val.2 < c₂_below.val.2 := by
    rw [h_c₁_below_col, h_c₂_below_col]; exact h_col
  have h_weak_below : T c₁_below ≤ T c₂_below := hT.1 c₁_below c₂_below h_row_below h_col_below
  rw [h_c₂_below_val] at h_weak_below
  simp only [Fin.le_def] at h_weak_below
  omega

/-- Cells with values other than k or k+1 are unchanged by Bender-Knuth. -/
private lemma benderKnuth_unchanged' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h1 : T c ≠ k) (h2 : T c ≠ ⟨k.val + 1, hk⟩) :
    benderKnuth k hk T hT c = T c := by
  unfold benderKnuth isUnmatchedFreeK isUnmatchedFreeKSucc
  simp only [h1, h2, false_and, ↓reduceIte]

/-- An unmatched free k becomes k+1 under Bender-Knuth. -/
private lemma benderKnuth_unmatched_k' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hunmatched : isUnmatchedFreeK T k hk c) :
    benderKnuth k hk T hT c = ⟨k.val + 1, hk⟩ := by
  unfold benderKnuth
  simp only [hunmatched, ↓reduceIte]

/-- An unmatched free (k+1) becomes k under Bender-Knuth. -/
private lemma benderKnuth_unmatched_kSucc' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hunmatched : isUnmatchedFreeKSucc T k hk c) :
    benderKnuth k hk T hT c = k := by
  unfold benderKnuth isUnmatchedFreeK
  have hne : ¬(T c = k) := by
    intro h
    have := hunmatched.1
    rw [h] at this
    simp only [Fin.ext_iff] at this
    omega
  simp only [hne, false_and, ↓reduceIte, hunmatched]

/-- A forced k stays as k under Bender-Knuth (forced cells are never unmatched). -/
private lemma benderKnuth_forced_k' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hforced : isForcedK T k hk c) :
    benderKnuth k hk T hT c = k := by
  unfold benderKnuth
  have hval := hforced.1
  have hne : ¬(T c = ⟨k.val + 1, hk⟩) := by
    intro h; rw [hval] at h; simp only [Fin.ext_iff] at h; omega
  -- A forced k is not unmatched (it's not even free)
  have h_not_unmatched_k : ¬isUnmatchedFreeK T k hk c := by
    intro h; exact h.2.1 hforced
  have h_not_unmatched_ksucc : ¬isUnmatchedFreeKSucc T k hk c := by
    unfold isUnmatchedFreeKSucc
    intro ⟨hTc, _, _⟩
    rw [hval] at hTc
    simp only [Fin.ext_iff] at hTc
    omega
  simp only [h_not_unmatched_k, h_not_unmatched_ksucc, ↓reduceIte, hval]

/-- A forced (k+1) stays as (k+1) under Bender-Knuth (forced cells are never unmatched). -/
private lemma benderKnuth_forced_kSucc' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hforced : isForcedKSucc T k hk c) :
    benderKnuth k hk T hT c = ⟨k.val + 1, hk⟩ := by
  unfold benderKnuth
  have hval := hforced.1
  have hne : ¬(T c = k) := by
    intro h; rw [hval] at h; simp only [Fin.ext_iff] at h; omega
  have h_not_unmatched_k : ¬isUnmatchedFreeK T k hk c := by
    intro h; exact hne h.1
  have h_not_unmatched_ksucc : ¬isUnmatchedFreeKSucc T k hk c := by
    intro h; exact h.2.1 hforced
  simp only [h_not_unmatched_k, h_not_unmatched_ksucc, ↓reduceIte, hval]

/-- Forced k cells remain forced after Bender-Knuth. -/
lemma forced_k_preserved' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hforced : isForcedK T k hk c) :
    let T' := benderKnuth k hk T hT
    isForcedK T' k hk c := by
  intro T'
  obtain ⟨hval, c_below, h_col, h_row, hbelow⟩ := hforced
  have hT'c : T' c = k := benderKnuth_forced_k' k hk T hT c ⟨hval, c_below, h_col, h_row, hbelow⟩
  have hbelow_forced : isForcedKSucc T k hk c_below := ⟨hbelow, c, h_col.symm, h_row, hval⟩
  have hT'_below : T' c_below = ⟨k.val + 1, hk⟩ := benderKnuth_forced_kSucc' k hk T hT c_below hbelow_forced
  exact ⟨hT'c, c_below, h_col, h_row, hT'_below⟩

/-- Forced (k+1) cells remain forced after Bender-Knuth. -/
lemma forced_kSucc_preserved' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hforced : isForcedKSucc T k hk c) :
    let T' := benderKnuth k hk T hT
    isForcedKSucc T' k hk c := by
  intro T'
  obtain ⟨hval, c_above, h_col, h_row, habove⟩ := hforced
  have hT'c : T' c = ⟨k.val + 1, hk⟩ := benderKnuth_forced_kSucc' k hk T hT c ⟨hval, c_above, h_col, h_row, habove⟩
  have habove_forced : isForcedK T k hk c_above := ⟨habove, c, h_col.symm, h_row, hval⟩
  have hT'_above : T' c_above = k := benderKnuth_forced_k' k hk T hT c_above habove_forced
  exact ⟨hT'c, c_above, h_col, h_row, hT'_above⟩

/-- An unmatched free k that becomes k+1 is not forced as a (k+1) in T'. -/
private lemma unmatched_k_becomes_free_kSucc' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hunmatched : isUnmatchedFreeK T k hk c) :
    let T' := benderKnuth k hk T hT
    ¬isForcedKSucc T' k hk c := by
  intro T' hforced'
  obtain ⟨_, c_above, h_col, h_row, hT'_above⟩ := hforced'
  have hval := hunmatched.1
  have h_lt : T c_above < T c := hT.2 c_above c h_col (by simp only [Fin.lt_def]; omega)
  rw [hval] at h_lt
  have h_ne_k : T c_above ≠ k := Fin.ne_of_lt h_lt
  have h_ne_k1 : T c_above ≠ ⟨k.val + 1, hk⟩ := by
    intro h; rw [h] at h_lt; simp only [Fin.lt_def] at h_lt; omega
  have hT'_eq : T' c_above = T c_above := benderKnuth_unchanged' k hk T hT c_above h_ne_k h_ne_k1
  rw [hT'_eq] at hT'_above
  exact h_ne_k hT'_above

/-- An unmatched free (k+1) that becomes k is not forced as a k in T'. -/
private lemma unmatched_kSucc_becomes_free_k' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hunmatched : isUnmatchedFreeKSucc T k hk c) :
    let T' := benderKnuth k hk T hT
    ¬isForcedK T' k hk c := by
  intro T' hforced'
  obtain ⟨_, c_below, h_col, h_row, hT'_below⟩ := hforced'
  have hval := hunmatched.1
  have h_lt : T c < T c_below := hT.2 c c_below h_col.symm (by simp only [Fin.lt_def]; omega)
  rw [hval] at h_lt
  have h_ne_k : T c_below ≠ k := by intro h; rw [h] at h_lt; simp only [Fin.lt_def] at h_lt; omega
  have h_ne_k1 : T c_below ≠ ⟨k.val + 1, hk⟩ := Fin.ne_of_gt h_lt
  have hT'_eq : T' c_below = T c_below := benderKnuth_unchanged' k hk T hT c_below h_ne_k h_ne_k1
  rw [hT'_eq] at hT'_below
  simp only [Fin.ext_iff] at hT'_below; simp only [Fin.lt_def] at h_lt; omega

/-- A matched free k (i.e., free but not unmatched) stays as k under BK. -/
private lemma benderKnuth_matched_k' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hval : T c = k) (_hfree : ¬isForcedK T k hk c) (hmatched : ¬isUnmatchedFreeK T k hk c) :
    benderKnuth k hk T hT c = k := by
  unfold benderKnuth
  simp only [hmatched, ↓reduceIte]
  -- Not unmatched as (k+1) either since T c = k
  have h_not_ksucc : ¬isUnmatchedFreeKSucc T k hk c := by
    intro h
    have := h.1
    rw [hval] at this
    simp only [Fin.ext_iff] at this
    omega
  simp only [h_not_ksucc, ↓reduceIte, hval]

/-- A matched free (k+1) (i.e., free but not unmatched) stays as (k+1) under BK. -/
private lemma benderKnuth_matched_kSucc' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hval : T c = ⟨k.val + 1, hk⟩) (_hfree : ¬isForcedKSucc T k hk c)
    (hmatched : ¬isUnmatchedFreeKSucc T k hk c) :
    benderKnuth k hk T hT c = ⟨k.val + 1, hk⟩ := by
  unfold benderKnuth
  -- Not unmatched as k since T c = k+1
  have h_not_k : ¬isUnmatchedFreeK T k hk c := by
    intro h
    have := h.1
    rw [hval] at this
    simp only [Fin.ext_iff] at this
    omega
  simp only [h_not_k, hmatched, ↓reduceIte, hval]

/-! ### Key lemmas for benderKnuth_involutive

The proof of involutivity requires showing that the matching structure is preserved
under BK. The key insights are:

1. **Matching symmetry**: If a free k at position c is matched with a free (k+1) at
   position c', then after BK, both stay as their original values (k and k+1).

2. **Unmatched symmetry**: An unmatched free k becomes an unmatched free (k+1) in T',
   and an unmatched free (k+1) becomes an unmatched free k in T'.

3. **Row-weak preservation**: In each row, the ordering of entries is preserved because:
   - Unmatched (k+1)'s (→ k) are to the LEFT of matched entries
   - Unmatched k's (→ k+1) are to the RIGHT of matched entries

4. **Column-strict preservation**: Forced pairs stay together, and free cells in the
   same column have the same matching status (since they're in the same row).
-/
/-! ### Partner functions for forced cells

Forced k cells and forced (k+1) cells come in pairs: each forced k has exactly one
forced (k+1) directly below it, and vice versa. These helper functions extract the
partner cell, which is useful for proving the content swap property. -/

/-- The cell below a forced k cell. This is well-defined because the existence is witnessed. -/
private noncomputable def forcedK_partner {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedK T k hk c) : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
  Classical.choose hc.2

private lemma forcedK_partner_spec {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedK T k hk c) :
    let p := forcedK_partner T k hk c hc
    p.val.2 = c.val.2 ∧ c.val.1.val + 1 = p.val.1.val ∧ T p = ⟨k.val + 1, hk⟩ :=
  Classical.choose_spec hc.2

/-- The cell above a forced (k+1) cell. -/
private noncomputable def forcedKSucc_partner {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedKSucc T k hk c) : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
  Classical.choose hc.2

private lemma forcedKSucc_partner_spec {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedKSucc T k hk c) :
    let p := forcedKSucc_partner T k hk c hc
    p.val.2 = c.val.2 ∧ p.val.1.val + 1 = c.val.1.val ∧ T p = k :=
  Classical.choose_spec hc.2

/-- The partner of a forced k is a forced (k+1). -/
private lemma forcedK_partner_isForcedKSucc {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedK T k hk c) :
    isForcedKSucc T k hk (forcedK_partner T k hk c hc) := by
  obtain ⟨h_col, h_row, hval⟩ := forcedK_partner_spec T k hk c hc
  exact ⟨hval, c, h_col.symm, h_row, hc.1⟩

/-- The partner of a forced (k+1) is a forced k. -/
private lemma forcedKSucc_partner_isForcedK {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedKSucc T k hk c) :
    isForcedK T k hk (forcedKSucc_partner T k hk c hc) := by
  obtain ⟨h_col, h_row, hval⟩ := forcedKSucc_partner_spec T k hk c hc
  exact ⟨hval, c, h_col.symm, h_row, hc.1⟩

/-- The partner functions are inverses (for k → k+1 → k direction). -/
private lemma forcedKSucc_partner_forcedK_partner {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedK T k hk c) :
    forcedKSucc_partner T k hk (forcedK_partner T k hk c hc)
      (forcedK_partner_isForcedKSucc T k hk c hc) = c := by
  obtain ⟨h_col1, h_row1, _⟩ := forcedK_partner_spec T k hk c hc
  let p := forcedK_partner T k hk c hc
  let hp := forcedK_partner_isForcedKSucc T k hk c hc
  obtain ⟨h_col2, h_row2, _⟩ := forcedKSucc_partner_spec T k hk p hp
  let q := forcedKSucc_partner T k hk p hp
  have hq_row : q.val.1.val = c.val.1.val := by
    have h1 : c.val.1.val + 1 = p.val.1.val := h_row1
    have h2 : q.val.1.val + 1 = p.val.1.val := h_row2
    linarith
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext hq_row
  · exact h_col2.trans h_col1

/-- The partner functions are inverses (for k+1 → k → k+1 direction). -/
private lemma forcedK_partner_forcedKSucc_partner {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedKSucc T k hk c) :
    forcedK_partner T k hk (forcedKSucc_partner T k hk c hc)
      (forcedKSucc_partner_isForcedK T k hk c hc) = c := by
  obtain ⟨h_col1, h_row1, _⟩ := forcedKSucc_partner_spec T k hk c hc
  let p := forcedKSucc_partner T k hk c hc
  let hp := forcedKSucc_partner_isForcedK T k hk c hc
  obtain ⟨h_col2, h_row2, _⟩ := forcedK_partner_spec T k hk p hp
  let q := forcedK_partner T k hk p hp
  have hq_row : q.val.1.val = c.val.1.val := by
    have h1 : p.val.1.val + 1 = c.val.1.val := h_row1
    have h2 : p.val.1.val + 1 = q.val.1.val := h_row2
    linarith
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext hq_row
  · exact h_col2.trans h_col1

/-- The set of cells where T c = k and c is not an unmatched free k.
    This includes forced k cells and matched free k cells. -/
private def notUnmatchedK {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) :
    Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
  {c | T c = k ∧ ¬isUnmatchedFreeK T k hk c}

/-- The set of cells where T c = k+1 and c is not an unmatched free (k+1).
    This includes forced (k+1) cells and matched free (k+1) cells. -/
private def notUnmatchedKSucc {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) :
    Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
  {c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c}

/-- Key characterization: T' c = k iff (T c = k ∧ ¬isUnmatchedFreeK) ∨ isUnmatchedFreeKSucc. -/
private lemma benderKnuth_eq_k_iff {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) :
    benderKnuth k hk T hT c = k ↔ (T c = k ∧ ¬isUnmatchedFreeK T k hk c) ∨ isUnmatchedFreeKSucc T k hk c := by
  constructor
  · intro hT'c
    by_cases h_unmatched_k : isUnmatchedFreeK T k hk c
    · -- If c is an unmatched free k, then T' c = k+1, not k
      have := benderKnuth_unmatched_k' k hk T hT c h_unmatched_k
      rw [this] at hT'c
      simp only [Fin.ext_iff] at hT'c
      omega
    · by_cases h_unmatched_ksucc : isUnmatchedFreeKSucc T k hk c
      · right; exact h_unmatched_ksucc
      · left
        constructor
        · -- T c = k because T' c = k and c is not unmatched
          unfold benderKnuth at hT'c
          simp only [h_unmatched_k, h_unmatched_ksucc, ↓reduceIte] at hT'c
          exact hT'c
        · exact h_unmatched_k
  · intro h
    rcases h with ⟨hTc, h_not_unmatched⟩ | h_unmatched_ksucc
    · -- Case: T c = k and c is not unmatched free k
      unfold benderKnuth
      simp only [h_not_unmatched, ↓reduceIte]
      -- c is also not unmatched free (k+1) since T c = k
      have h_not_ksucc : ¬isUnmatchedFreeKSucc T k hk c := by
        intro h
        have := h.1
        rw [hTc] at this
        simp only [Fin.ext_iff] at this
        omega
      simp only [h_not_ksucc, ↓reduceIte, hTc]
    · -- Case: c is unmatched free (k+1), so T' c = k
      exact benderKnuth_unmatched_kSucc' k hk T hT c h_unmatched_ksucc

/-- Key characterization: T' c = k+1 iff (T c = k+1 ∧ ¬isUnmatchedFreeKSucc) ∨ isUnmatchedFreeK. -/
private lemma benderKnuth_eq_kSucc_iff {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) :
    benderKnuth k hk T hT c = ⟨k.val + 1, hk⟩ ↔
      (T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c) ∨ isUnmatchedFreeK T k hk c := by
  constructor
  · intro hT'c
    by_cases h_unmatched_ksucc : isUnmatchedFreeKSucc T k hk c
    · -- If c is an unmatched free (k+1), then T' c = k, not k+1
      have := benderKnuth_unmatched_kSucc' k hk T hT c h_unmatched_ksucc
      rw [this] at hT'c
      simp only [Fin.ext_iff] at hT'c
      omega
    · by_cases h_unmatched_k : isUnmatchedFreeK T k hk c
      · right; exact h_unmatched_k
      · left
        constructor
        · -- T c = k+1 because T' c = k+1 and c is not unmatched
          unfold benderKnuth at hT'c
          simp only [h_unmatched_k, h_unmatched_ksucc, ↓reduceIte] at hT'c
          exact hT'c
        · exact h_unmatched_ksucc
  · intro h
    rcases h with ⟨hTc, h_not_unmatched⟩ | h_unmatched_k
    · -- Case: T c = k+1 and c is not unmatched free (k+1)
      unfold benderKnuth
      -- c is not unmatched free k since T c = k+1
      have h_not_k : ¬isUnmatchedFreeK T k hk c := by
        intro h
        have := h.1
        rw [hTc] at this
        simp only [Fin.ext_iff] at this
        omega
      simp only [h_not_k, h_not_unmatched, ↓reduceIte, hTc]
    · -- Case: c is unmatched free k, so T' c = k+1
      exact benderKnuth_unmatched_k' k hk T hT c h_unmatched_k

/-- Forced k's and forced (k+1)'s are in bijection via the pairing.
    This is a key lemma for proving the content swap property of Bender-Knuth involutions. -/
private lemma forced_k_kSucc_bijection {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) :
    Nat.card {c // isForcedK T k hk c} = Nat.card {c // isForcedKSucc T k hk c} := by
  apply Nat.card_congr
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  · exact fun ⟨c, hc⟩ =>
      ⟨forcedK_partner T k hk c hc, forcedK_partner_isForcedKSucc T k hk c hc⟩
  · exact fun ⟨c, hc⟩ =>
      ⟨forcedKSucc_partner T k hk c hc, forcedKSucc_partner_isForcedK T k hk c hc⟩
  · intro ⟨c, hc⟩
    simp only [Subtype.mk.injEq]
    exact forcedKSucc_partner_forcedK_partner T k hk c hc
  · intro ⟨c, hc⟩
    simp only [Subtype.mk.injEq]
    exact forcedK_partner_forcedKSucc_partner T k hk c hc

/-- The set of cells where T c = k and c is not unmatched free k.
    This equals {forced k} ∪ {matched free k}. -/
private lemma notUnmatchedK_eq_union {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) :
    {c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} =
      {c | isForcedK T k hk c} ∪ {c | isMatchedFreeK T k hk c} := by
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro ⟨hTc, h_not_unmatched⟩
    by_cases hforced : isForcedK T k hk c
    · left; exact hforced
    · right; exact ⟨hTc, hforced, h_not_unmatched⟩
  · intro h
    rcases h with hforced | ⟨hTc, _, h_not_unmatched⟩
    · exact ⟨hforced.1, fun h => h.2.1 hforced⟩
    · exact ⟨hTc, h_not_unmatched⟩

/-- The set of cells where T c = k+1 and c is not unmatched free (k+1).
    This equals {forced (k+1)} ∪ {matched free (k+1)}. -/
private lemma notUnmatchedKSucc_eq_union {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) :
    {c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} =
      {c | isForcedKSucc T k hk c} ∪ {c | isMatchedFreeKSucc T k hk c} := by
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro ⟨hTc, h_not_unmatched⟩
    by_cases hforced : isForcedKSucc T k hk c
    · left; exact hforced
    · right; exact ⟨hTc, hforced, h_not_unmatched⟩
  · intro h
    rcases h with hforced | ⟨hTc, _, h_not_unmatched⟩
    · exact ⟨hforced.1, fun h => h.2.1 hforced⟩
    · exact ⟨hTc, h_not_unmatched⟩

/-- Forced k and matched free k are disjoint. -/
private lemma forcedK_matchedFreeK_disjoint {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) :
    Disjoint {c | isForcedK T k hk c} {c | isMatchedFreeK T k hk c} := by
  rw [Set.disjoint_iff]
  intro c ⟨hforced, ⟨_, h_not_forced, _⟩⟩
  exact h_not_forced hforced

/-- Forced (k+1) and matched free (k+1) are disjoint. -/
private lemma forcedKSucc_matchedFreeKSucc_disjoint {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) :
    Disjoint {c | isForcedKSucc T k hk c} {c | isMatchedFreeKSucc T k hk c} := by
  rw [Set.disjoint_iff]
  intro c ⟨hforced, ⟨_, h_not_forced, _⟩⟩
  exact h_not_forced hforced

/-- Free k's in a given row have distinct columns.
    This is because each cell has a unique (row, column) position. -/
private lemma freeK_distinct_cols {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc₁_row : c₁.val.1 = i) (_hc₁_val : T c₁ = k) (_hc₁_free : ¬isForcedK T k hk c₁)
    (hc₂_row : c₂.val.1 = i) (_hc₂_val : T c₂ = k) (_hc₂_free : ¬isForcedK T k hk c₂)
    (hcol : c₁.val.2 = c₂.val.2) : c₁ = c₂ := by
  have hrow : c₁.val.1 = c₂.val.1 := hc₁_row.trans hc₂_row.symm
  exact Subtype.ext (Prod.ext hrow hcol)

/-- The column function is injective on free k's in a given row.
    This allows us to order free k's by column and establish a bijection with Fin(freeKCount). -/
private lemma freeK_col_injective {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) :
    Set.InjOn (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} => c.val.2) 
              {c | c.val.1 = i ∧ T c = k ∧ ¬isForcedK T k hk c} := by
  intro c₁ hc₁ c₂ hc₂ hcol
  exact freeK_distinct_cols T i k hk c₁ c₂ hc₁.1 hc₁.2.1 hc₁.2.2 hc₂.1 hc₂.2.1 hc₂.2.2 hcol

/-- Helper: Count of items with index > threshold equals total - min(total, threshold).
    This is the key counting lemma for unmatched free cells. -/
private lemma count_gt_threshold (m n : ℕ) : 
    Fintype.card {i : Fin m // i.val + 1 > n} = m - min m n := by
  classical
  by_cases hm : m = 0
  · subst hm
    haveI : IsEmpty (Fin 0) := Fin.isEmpty
    haveI : IsEmpty {i : Fin 0 // i.val + 1 > n} := Subtype.isEmpty_of_false (fun i => i.elim0)
    simp only [Fintype.card_eq_zero, Nat.zero_sub]
  · by_cases hn : n ≥ m
    · have h : ∀ i : Fin m, ¬(i.val + 1 > n) := by intro i; have := i.isLt; omega
      have : IsEmpty {i : Fin m // i.val + 1 > n} := ⟨fun ⟨i, hi⟩ => h i hi⟩
      simp only [Fintype.card_eq_zero]; omega
    · push Not at hn
      have hmn : m - n > 0 := by omega
      have h_eq : {i : Fin m // i.val + 1 > n} ≃ Fin (m - n) := {
        toFun := fun ⟨i, hi⟩ => ⟨i.val - n, by have := i.isLt; omega⟩
        invFun := fun j => ⟨⟨j.val + n, by have := j.isLt; omega⟩, by simp only [gt_iff_lt]; have := j.isLt; omega⟩
        left_inv := fun ⟨i, hi⟩ => by 
          simp only [Subtype.mk.injEq]
          have hi' : i.val ≥ n := by simp only [gt_iff_lt] at hi; omega
          apply Fin.ext
          simp; omega
        right_inv := fun j => by 
          apply Fin.ext
          simp
      }
      rw [Fintype.card_congr h_eq, Fintype.card_fin]; omega

/-- Helper: Count of items with index ≤ threshold equals min(total, threshold).
    This is the key counting lemma for matched free cells. -/
private lemma count_le_threshold (m n : ℕ) : 
    Fintype.card {i : Fin m // i.val + 1 ≤ n} = min m n := by
  classical
  have h1 : Fintype.card {i : Fin m // i.val + 1 > n} + Fintype.card {i : Fin m // i.val + 1 ≤ n} = m := by
    have h2 : Fintype.card (Fin m) = m := Fintype.card_fin m
    have h3 : Fintype.card {i : Fin m // ¬(i.val + 1 > n)} = Fintype.card (Fin m) - Fintype.card {i : Fin m // i.val + 1 > n} := by
      exact Fintype.card_subtype_compl (fun i : Fin m => i.val + 1 > n)
    simp only [not_lt] at h3
    have h4 := count_gt_threshold m n
    have h5 : Fintype.card {i : Fin m // i.val + 1 > n} ≤ m := by
      calc Fintype.card {i : Fin m // i.val + 1 > n} = m - min m n := h4
        _ ≤ m := Nat.sub_le m (min m n)
    omega
  have h4 := count_gt_threshold m n
  omega

/-- For a finset of natural numbers ordered as n₁ < n₂ < ... < nₘ,
    the count of elements ≤ nⱼ equals j+1.
    
    This is the key lemma connecting freeKCountUpTo to position in the ordering:
    if free k cells have columns forming a finset S, and c is the j-th cell (0-indexed)
    by column order, then freeKCountUpTo(c.col) = j + 1. -/
private lemma count_le_nth_smallest (S : Finset ℕ) (j : Fin S.card) :
    (S.filter (· ≤ (S.orderEmbOfFin rfl j : ℕ))).card = j.val + 1 := by
  classical
  let f := S.orderEmbOfFin rfl
  have hf_strict_mono : StrictMono f := f.strictMono
  have h_eq : S.filter (· ≤ f j) = ((Finset.univ : Finset (Fin S.card)).filter (· ≤ j)).image f := by
    ext x
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · intro ⟨hx, hle⟩
      have hx_range : x ∈ Set.range f := by rw [range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := hx_range
      refine ⟨i, ?_, rfl⟩
      by_contra h; push Not at h
      have : f j < f i := hf_strict_mono h
      omega
    · intro ⟨i, hi, hxi⟩
      constructor
      · rw [← hxi]; exact orderEmbOfFin_mem S rfl i
      · rw [← hxi]; exact hf_strict_mono.monotone hi
  rw [h_eq, card_image_of_injective _ f.injective]
  have h2 : (Finset.univ : Finset (Fin S.card)).filter (· ≤ j) = Finset.Iic j := by
    ext i; simp [mem_filter, mem_Iic]
  rw [h2, Fin.card_Iic]

/-- Helper: The number of elements in `{j : Fin m | j.val + 1 ≤ n}` equals `min m n`.
    This is the key counting lemma for matched free cells after establishing the bijection. -/
private lemma matched_position_count (m n : ℕ) : 
    Fintype.card {j : Fin m // j.val + 1 ≤ n} = min m n := by
  classical
  by_cases hm : m = 0
  · subst hm
    simp [Fintype.card_eq_zero]
  · by_cases hn : n = 0
    · have h : ∀ j : Fin m, ¬(j.val + 1 ≤ 0) := by intro j; omega
      have : IsEmpty {j : Fin m // j.val + 1 ≤ n} := ⟨fun ⟨j, hj⟩ => by subst hn; exact h j hj⟩
      simp [Fintype.card_eq_zero, hn]
    · push Not at hm hn
      by_cases hmn : m ≤ n
      · have h_eq : {j : Fin m // j.val + 1 ≤ n} ≃ Fin m := by
          refine ⟨fun ⟨j, _⟩ => j, fun j => ⟨j, ?_⟩, ?_, ?_⟩
          · have := j.isLt; omega
          · intro ⟨j, _⟩; rfl
          · intro j; rfl
        rw [Fintype.card_congr h_eq, Fintype.card_fin, Nat.min_eq_left hmn]
      · push Not at hmn
        have h_eq : {j : Fin m // j.val + 1 ≤ n} ≃ Fin n := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact fun ⟨j, hj⟩ => ⟨j.val, by omega⟩
          · intro i
            refine ⟨⟨i.val, ?_⟩, ?_⟩
            · have := i.isLt; omega
            · simp only; have := i.isLt; omega
          · intro ⟨j, hj⟩; simp
          · intro i; simp
        rw [Fintype.card_congr h_eq, Fintype.card_fin, Nat.min_eq_right (le_of_lt hmn)]

/-- For an element s of a finset S, the filter cardinality equals its position + 1. -/
private lemma filter_card_eq_symm_val (S : Finset ℕ) (s : S) :
    (S.filter (· ≤ s.val)).card = ((S.orderIsoOfFin rfl).symm s).val + 1 := by
  classical
  let g := S.orderIsoOfFin rfl
  let j := g.symm s
  have hs_eq : s = g j := (g.apply_symm_apply s).symm
  have s_val_eq : s.val = S.orderEmbOfFin rfl j := by rw [hs_eq]; rfl
  rw [s_val_eq]
  let f := S.orderEmbOfFin rfl
  have hf_strict_mono : StrictMono f := f.strictMono
  have h_eq2 : S.filter (· ≤ f j) = ((Finset.univ : Finset (Fin S.card)).filter (· ≤ j)).image f := by
    ext x
    simp only [mem_filter, mem_image, mem_univ, true_and]
    constructor
    · intro ⟨hx, hle⟩
      have hx_range : x ∈ Set.range f := by rw [range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := hx_range
      refine ⟨i, ?_, rfl⟩
      by_contra h; push Not at h
      have : f j < f i := hf_strict_mono h
      omega
    · intro ⟨i, hi, hxi⟩
      constructor
      · rw [← hxi]; exact orderEmbOfFin_mem S rfl i
      · rw [← hxi]; exact hf_strict_mono.monotone hi
  rw [h_eq2, card_image_of_injective _ f.injective]
  have h3 : (Finset.univ : Finset (Fin S.card)).filter (· ≤ j) = Finset.Iic j := by
    ext i; simp [mem_filter, mem_Iic]
  rw [h3, Fin.card_Iic]

/-- Equivalence between elements with bounded filter count and positions with bounded index.
    This is the key bijection for counting matched cells. -/
private noncomputable def count_filter_equiv (S : Finset ℕ) (n : ℕ) : 
    {s : S // (S.filter (· ≤ s.val)).card ≤ n} ≃ {j : Fin S.card // j.val + 1 ≤ n} := by
  classical
  let g := S.orderIsoOfFin rfl
  refine {
    toFun := fun ⟨s, hcount⟩ => ⟨g.symm s, ?_⟩
    invFun := fun ⟨j, hj⟩ => ⟨g j, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · rw [← filter_card_eq_symm_val S s]; exact hcount
  · have h := filter_card_eq_symm_val S (g j)
    have hj_eq : (g.symm (g j)) = j := g.symm_apply_apply j
    rw [hj_eq] at h; omega
  · intro ⟨s, hs⟩; simp only [Subtype.mk.injEq]; exact g.apply_symm_apply s
  · intro ⟨j, hj⟩; simp only [Subtype.mk.injEq]; exact g.symm_apply_apply j

/-- The count of elements with bounded filter cardinality equals min(|S|, n). -/
private lemma count_filter_card (S : Finset ℕ) (n : ℕ) :
    Fintype.card {s : S // (S.filter (· ≤ s.val)).card ≤ n} = min S.card n := by
  rw [Fintype.card_congr (count_filter_equiv S n), matched_position_count]

/-! ### Free k cells and column ordering

The following section documents the structure needed to prove `matchedFreeK_card_eq_matchedFreeKSucc_card`.

**Key insight:** Free k cells in a given row can be ordered by column. If we denote the
columns of free k cells in row i as c₁ < c₂ < ... < cₘ, then:
- `freeKCountUpTo(cⱼ) = j` for each j (by definition of freeKCountUpTo)
- A free k cell at column cⱼ is matched iff `freeKCountUpTo(cⱼ) ≤ freeKSuccCount`, i.e., `j ≤ n`
- There are `min(m, n)` such cells

The formal proof requires:
1. Showing that free k columns in row i form a finset S
2. Using `S.orderEmbOfFin` to establish the bijection with `Fin m`
3. Showing that `freeKCountUpTo` at the j-th column equals j+1 (via `count_le_nth_smallest`)
4. Applying `matched_position_count` to count matched cells

The helper lemmas `count_le_nth_smallest` and `matched_position_count` provide the counting
infrastructure. The remaining work is to formalize the bijection between free k cells and
their position in the column ordering.
-/

/-- Helper lemma: Count of matched columns in a finset equals min(|S|, n).
    A column s is "matched" if the count of elements ≤ s is at most n. -/
private lemma matched_cols_count (S : Finset ℕ) (n : ℕ) :
    (S.filter (fun s => (S.filter (· ≤ s)).card ≤ n)).card = min S.card n := by
  classical
  by_cases hS : S.card = 0
  · simp [Finset.card_eq_zero.mp hS]
  · let f := S.orderEmbOfFin rfl
    have h_prefix_count : ∀ j : Fin S.card, (S.filter (· ≤ f j)).card = j.val + 1 := by
      intro j
      have hf_strict_mono : StrictMono f := f.strictMono
      have h_eq : S.filter (· ≤ f j) = ((Finset.univ : Finset (Fin S.card)).filter (· ≤ j)).image f := by
        ext x
        simp only [mem_filter, mem_image, mem_univ, true_and]
        constructor
        · intro ⟨hx, hle⟩
          have hx_range : x ∈ Set.range f := by rw [range_orderEmbOfFin]; exact hx
          obtain ⟨i, rfl⟩ := hx_range
          refine ⟨i, ?_, rfl⟩
          by_contra h; push Not at h
          have : f j < f i := hf_strict_mono h
          omega
        · intro ⟨i, hi, hxi⟩
          constructor
          · rw [← hxi]; exact orderEmbOfFin_mem S rfl i
          · rw [← hxi]; exact hf_strict_mono.monotone hi
      rw [h_eq, card_image_of_injective _ f.injective]
      have h2 : (Finset.univ : Finset (Fin S.card)).filter (· ≤ j) = Finset.Iic j := by
        ext i; simp [mem_filter, mem_Iic]
      rw [h2, Fin.card_Iic]
    have h_filter_eq : S.filter (fun s => (S.filter (· ≤ s)).card ≤ n) = 
        ((Finset.univ : Finset (Fin S.card)).filter (fun j => j.val + 1 ≤ n)).image f := by
      ext s
      simp only [mem_filter, mem_image, mem_univ, true_and]
      constructor
      · intro ⟨hs, hcond⟩
        have hs_range : s ∈ Set.range f := by rw [range_orderEmbOfFin]; exact hs
        obtain ⟨j, rfl⟩ := hs_range
        refine ⟨j, ?_, rfl⟩
        rw [h_prefix_count j] at hcond
        exact hcond
      · intro ⟨j, hj, hjs⟩
        constructor
        · rw [← hjs]; exact orderEmbOfFin_mem S rfl j
        · rw [← hjs, h_prefix_count j]; exact hj
    rw [h_filter_eq, card_image_of_injective _ f.injective]
    by_cases hmn : S.card ≤ n
    · have h_all : (Finset.univ : Finset (Fin S.card)).filter (fun j => j.val + 1 ≤ n) = Finset.univ := by
        ext j; simp only [mem_filter, mem_univ, true_and, iff_true]; have := j.isLt; omega
      rw [h_all, card_univ, Fintype.card_fin, Nat.min_eq_left hmn]
    · push Not at hmn
      have h_eq : (Finset.univ : Finset (Fin S.card)).filter (fun j => j.val + 1 ≤ n) = 
          (Finset.univ : Finset (Fin S.card)).filter (fun j => j.val < n) := by
        ext j; simp only [mem_filter, mem_univ, true_and]; omega
      rw [h_eq]
      have h_eq2 : (Finset.univ : Finset (Fin S.card)).filter (fun j : Fin S.card => j.val < n) = 
          Finset.Iio (⟨n, hmn⟩ : Fin S.card) := by
        ext j; simp only [mem_filter, mem_univ, true_and, mem_Iio]; rfl
      rw [h_eq2, Fin.card_Iio, Nat.min_eq_right (le_of_lt hmn)]

/-- Complementary counting lemma for (k+1)'s in the Bender-Knuth matching.
    
    A (k+1) at position j (1-indexed among free (k+1)'s) is matched iff m + j > n,
    where m = freeKCount (number of free k's) and n = freeKSuccCount (number of free (k+1)'s).
    
    This counts min(m, n) elements, matching the count of matched free k's.
    
    **Key insight:** The condition `m + (S.filter (· ≤ s)).card > S.card` captures exactly
    the matched (k+1) condition from `¬isUnmatchedFreeKSucc`:
    - `freeKCount + freeKSuccCountUpTo c.col > freeKSuccCount`
    
    This is the dual of `matched_cols_count` which handles free k's. -/
private lemma matched_kSucc_cols_count (S : Finset ℕ) (m : ℕ) :
    (S.filter (fun s => m + (S.filter (· ≤ s)).card > S.card)).card = min m S.card := by
  classical
  by_cases hS : S.card = 0
  · simp [Finset.card_eq_zero.mp hS]
  · by_cases hm : m = 0
    · -- When m = 0, no (k+1)'s are matched (condition 0 + j > n is never true for j ≤ n)
      simp only [hm, zero_add]
      have h_empty : S.filter (fun s => (S.filter (· ≤ s)).card > S.card) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro s _
        exact Nat.not_lt.mpr (Finset.card_filter_le S (· ≤ s))
      rw [h_empty, Finset.card_empty]
      simp
    · -- When m > 0, use the orderEmbOfFin approach
      let f := S.orderEmbOfFin rfl
      have h_prefix_count : ∀ j : Fin S.card, (S.filter (· ≤ f j)).card = j.val + 1 := by
        intro j
        have hf_strict_mono : StrictMono f := f.strictMono
        have h_eq : S.filter (· ≤ f j) = ((Finset.univ : Finset (Fin S.card)).filter (· ≤ j)).image f := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · intro ⟨hx, hle⟩
            have hx_range : x ∈ Set.range f := by rw [Finset.range_orderEmbOfFin]; exact hx
            obtain ⟨i, rfl⟩ := hx_range
            refine ⟨i, ?_, rfl⟩
            by_contra h; push Not at h
            have : f j < f i := hf_strict_mono h
            omega
          · intro ⟨i, hi, hxi⟩
            constructor
            · rw [← hxi]; exact Finset.orderEmbOfFin_mem S rfl i
            · rw [← hxi]; exact hf_strict_mono.monotone hi
        rw [h_eq, Finset.card_image_of_injective _ f.injective]
        have h2 : (Finset.univ : Finset (Fin S.card)).filter (· ≤ j) = Finset.Iic j := by
          ext i; simp [Finset.mem_filter, Finset.mem_Iic]
        rw [h2, Fin.card_Iic]
      have h_filter_eq : S.filter (fun s => m + (S.filter (· ≤ s)).card > S.card) = 
          ((Finset.univ : Finset (Fin S.card)).filter (fun j => m + j.val + 1 > S.card)).image f := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hs, hcond⟩
          have hs_range : s ∈ Set.range f := by rw [Finset.range_orderEmbOfFin]; exact hs
          obtain ⟨j, rfl⟩ := hs_range
          refine ⟨j, ?_, rfl⟩
          rw [h_prefix_count j] at hcond
          exact hcond
        · intro ⟨j, hj, hjs⟩
          constructor
          · rw [← hjs]; exact Finset.orderEmbOfFin_mem S rfl j
          · rw [← hjs, h_prefix_count j]; exact hj
      rw [h_filter_eq, Finset.card_image_of_injective _ f.injective]
      by_cases hmn : m ≥ S.card
      · have h_all : (Finset.univ : Finset (Fin S.card)).filter (fun j => m + j.val + 1 > S.card) = Finset.univ := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
        rw [h_all, Finset.card_univ, Fintype.card_fin, Nat.min_eq_right hmn]
      · push Not at hmn
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h_filter_eq2 : (Finset.univ : Finset (Fin S.card)).filter (fun j => m + j.val + 1 > S.card) = 
            Finset.Ici (⟨S.card - m, by 
              have : S.card - m < S.card := Nat.sub_lt (Nat.pos_of_ne_zero hS) hm_pos
              exact this⟩ : Fin S.card) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
          have := j.isLt
          omega
        rw [h_filter_eq2, Fin.card_Ici, Nat.min_eq_left (le_of_lt hmn)]
        exact Nat.sub_sub_self (le_of_lt hmn)

/-- Count cells with a column-based predicate using matched_cols_count.
    This is the key lemma connecting cell counts to column counts. -/
private lemma count_with_column_bijection {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset ℕ) (cells : Finset α) (col : α → ℕ) (n : ℕ)
    (h_col_mem : ∀ c ∈ cells, col c ∈ S)
    (h_col_inj : ∀ c₁ ∈ cells, ∀ c₂ ∈ cells, col c₁ = col c₂ → c₁ = c₂)
    (h_col_surj : ∀ s ∈ S, ∃ c ∈ cells, col c = s)
    (P : α → Prop) [DecidablePred P]
    (h_P_iff : ∀ c ∈ cells, P c ↔ (S.filter (· ≤ col c)).card ≤ n) :
    (cells.filter P).card = min S.card n := by
  -- Use matched_cols_count via bijection
  have h_filter_eq : (cells.filter P).card = (S.filter (fun s => (S.filter (· ≤ s)).card ≤ n)).card := by
    apply Finset.card_bij (fun c _ => col c)
    · intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      exact ⟨h_col_mem c hc.1, (h_P_iff c hc.1).mp hc.2⟩
    · intro c₁ hc₁ c₂ hc₂ heq
      simp only [Finset.mem_filter] at hc₁ hc₂
      exact h_col_inj c₁ hc₁.1 c₂ hc₂.1 heq
    · intro s hs
      simp only [Finset.mem_filter] at hs
      obtain ⟨c, hc, hcol⟩ := h_col_surj s hs.1
      refine ⟨c, ?_, hcol⟩
      simp only [Finset.mem_filter]
      exact ⟨hc, (h_P_iff c hc).mpr (hcol ▸ hs.2)⟩
  rw [h_filter_eq, matched_cols_count]

/-- The finset of columns of free k cells in row i.
    This is the key connection between the subtype-based definition of freeKCountUpTo
    and the finset-based counting lemmas. -/
private noncomputable def freeKCols {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) : Finset ℕ := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  exact (Finset.univ.filter (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} =>
    c.val.1 = i ∧ T c = k ∧ ¬isForcedK T k hk c)).image (fun c => c.val.2)

/-- Given a column in freeKCols, return the corresponding free k cell.
    This is the inverse of the column map used in the bijection. -/
private noncomputable def cellOfFreeKCol {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) 
    (s : ↑(freeKCols T i k hk)) : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  have hs : s.val ∈ freeKCols T i k hk := s.property
  simp only [freeKCols, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  exact Classical.choose hs

/-- The cell returned by cellOfFreeKCol satisfies the expected properties. -/
private lemma cellOfFreeKCol_spec {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) (s : ↑(freeKCols T i k hk)) :
    let c := cellOfFreeKCol T i k hk s
    c.val.1 = i ∧ T c = k ∧ ¬isForcedK T k hk c ∧ c.val.2 = s.val := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  simp only [cellOfFreeKCol]
  have hs : s.val ∈ freeKCols T i k hk := s.property
  simp only [freeKCols, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  have h := Classical.choose_spec hs
  exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩

/-- The cardinality of freeKCols equals freeKCount. -/
private lemma freeKCols_card {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) :
    (freeKCols T i k hk).card = freeKCount T i k hk := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  unfold freeKCols freeKCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_image_of_injOn]
  · -- The filter sets are equal (up to instance differences)
      -- Fintype is a Subsingleton, so the two instances are equal
      convert rfl
  · -- Injectivity: cells in the same row with the same column are equal
    intro c₁ hc₁ c₂ hc₂ hcol
    have hc₁' := Finset.mem_filter.mp hc₁
    have hc₂' := Finset.mem_filter.mp hc₂
    ext
    · rw [hc₁'.2.1, hc₂'.2.1]
    · exact hcol

/-- freeKCountUpTo equals the filter cardinality of freeKCols.
    This is the key lemma connecting the Nat.card-based definition to finset operations. -/
private lemma freeKCountUpTo_eq_filter_card {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) (col : ℕ) :
    freeKCountUpTo T i k hk col = ((freeKCols T i k hk).filter (· ≤ col)).card := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  unfold freeKCountUpTo freeKCols
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Both sides count elements with column ≤ col
  -- LHS: {c | c.row = i ∧ c.col ≤ col ∧ T c = k ∧ ¬isForcedK}
  -- RHS: {col' ∈ image | col' ≤ col}
  -- These are equal because the column map is injective on free k cells
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injOn]
  · -- The filter sets are equal (up to instance differences)
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨h1, h2, h3, h4⟩
        exact ⟨⟨h1, h3, h4⟩, h2⟩
      · intro ⟨⟨h1, h3, h4⟩, h2⟩
        exact ⟨h1, h2, h3, h4⟩
  · -- Injectivity on the filtered set
    intro c₁ hc₁ c₂ hc₂ hcol
    have hc₁' := Finset.mem_filter.mp hc₁
    have hc₂' := Finset.mem_filter.mp hc₂
    have hc₁'' := Finset.mem_filter.mp hc₁'.1
    have hc₂'' := Finset.mem_filter.mp hc₂'.1
    ext
    · rw [hc₁''.2.1, hc₂''.2.1]
    · exact hcol

/-! ### Free (k+1) cells and column ordering

Similar to the free k cell infrastructure, we define helpers for free (k+1) cells.
The key difference is that for free (k+1) cells, the matched condition involves
`freeKCountBefore` rather than `freeKSuccCount`. -/

/-- The finset of columns of free (k+1) cells in row i. -/
private noncomputable def freeKSuccCols {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) : Finset ℕ := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  exact (Finset.univ.filter (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} =>
    c.val.1 = i ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c)).image (fun c => c.val.2)

/-- Given a column in freeKSuccCols, return the corresponding free (k+1) cell. -/
private noncomputable def cellOfFreeKSuccCol {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) 
    (s : ↑(freeKSuccCols T i k hk)) : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  have hs : s.val ∈ freeKSuccCols T i k hk := s.property
  simp only [freeKSuccCols, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  exact Classical.choose hs

/-- The cell returned by cellOfFreeKSuccCol satisfies the expected properties. -/
private lemma cellOfFreeKSuccCol_spec {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) (s : ↑(freeKSuccCols T i k hk)) :
    let c := cellOfFreeKSuccCol T i k hk s
    c.val.1 = i ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c ∧ c.val.2 = s.val := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  simp only [cellOfFreeKSuccCol]
  have hs : s.val ∈ freeKSuccCols T i k hk := s.property
  simp only [freeKSuccCols, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  have h := Classical.choose_spec hs
  exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩

/-- The cardinality of freeKSuccCols equals freeKSuccCount. -/
private lemma freeKSuccCols_card {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) :
    (freeKSuccCols T i k hk).card = freeKSuccCount T i k hk := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  unfold freeKSuccCols freeKSuccCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_image_of_injOn]
  · convert rfl
  · intro c₁ hc₁ c₂ hc₂ hcol
    have hc₁' := Finset.mem_filter.mp hc₁
    have hc₂' := Finset.mem_filter.mp hc₂
    ext
    · rw [hc₁'.2.1, hc₂'.2.1]
    · exact hcol

/-- freeKSuccCountUpTo equals the filter cardinality of freeKSuccCols. -/
private lemma freeKSuccCountUpTo_eq_filter_card {lam mu : Fin N → ℕ} (T : Tableau lam mu) 
    (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) (col : ℕ) :
    freeKSuccCountUpTo T i k hk col = ((freeKSuccCols T i k hk).filter (· ≤ col)).card := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  unfold freeKSuccCountUpTo freeKSuccCols
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.filter_image]
  rw [Finset.card_image_of_injOn]
  · congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h3, h4⟩, h2⟩
    · intro ⟨⟨h1, h3, h4⟩, h2⟩
      exact ⟨h1, h2, h3, h4⟩
  · intro c₁ hc₁ c₂ hc₂ hcol
    have hc₁' := Finset.mem_filter.mp hc₁
    have hc₂' := Finset.mem_filter.mp hc₂
    have hc₁'' := Finset.mem_filter.mp hc₁'.1
    have hc₂'' := Finset.mem_filter.mp hc₂'.1
    ext
    · rw [hc₁''.2.1, hc₂''.2.1]
    · exact hcol

/-- In a semistandard tableau, for any free (k+1) cell c, all free k cells are at columns < c.col.
    Therefore freeKCountBefore(c.col) = freeKCount (all free k's are before). -/
private lemma freeKCountBefore_eq_freeKCount_at_kSucc {lam mu : Fin N → ℕ} 
    (T : Tableau lam mu) (hT : IsSemistandard T) (i : Fin N) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) 
    (hc_row : c.val.1 = i) (hc_kSucc : T c = ⟨k.val + 1, hk⟩) :
    freeKCountBefore T i k hk c.val.2 = freeKCount T i k hk := by
  unfold freeKCountBefore freeKCount
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (Equiv.refl _) ?_
  intro d
  simp only [Equiv.refl_apply]
  constructor
  · intro ⟨hd_row, hd_col, hd_val, hd_free⟩
    exact ⟨hd_row, hd_val, hd_free⟩
  · intro ⟨hd_row, hd_val, hd_free⟩
    refine ⟨hd_row, ?_, hd_val, hd_free⟩
    -- Need to show d.col < c.col (strictly less)
    by_contra h_not_lt
    push Not at h_not_lt
    -- d and c are in the same row
    have h_same_row : c.val.1 = d.val.1 := hc_row.trans hd_row.symm
    cases' Nat.lt_or_eq_of_le h_not_lt with hgt heq
    · -- c.col < d.col: By semistandardness, T c ≤ T d, so k+1 ≤ k, contradiction
      have h_weak : T c ≤ T d := hT.1 c d h_same_row hgt
      rw [hc_kSucc, hd_val] at h_weak
      simp only [Fin.le_def] at h_weak
      omega
    · -- c.col = d.col: c = d (same row, same col), but T c = k+1 ≠ k = T d
      have h_same : c = d := by
        apply Subtype.ext
        apply Prod.ext
        · exact h_same_row
        · exact heq
      rw [← h_same] at hd_val
      rw [hc_kSucc] at hd_val
      simp only [Fin.ext_iff] at hd_val
      omega

/-- Per-row count of matched free k's equals min(m, n) where m = freeKCount, n = freeKSuccCount.
    
    A free k at column c is matched iff freeKCountUpTo(c) ≤ freeKSuccCount.
    Since free k's are enumerated by column order, the j-th free k has freeKCountUpTo = j.
    So matched free k's are those with j ≤ n, giving min(m, n) matched.
    
    The proof uses `matched_cols_count` via a bijection between cells and columns. -/
private lemma matchedFreeK_row_card {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) :
    Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeK T k hk c} = 
    min (freeKCount T i k hk) (freeKSuccCount T i k hk) := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Step 1: Define the finset of free k cells in row i
  let cells := Finset.univ.filter (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} =>
    c.val.1 = i ∧ T c = k ∧ ¬isForcedK T k hk c)
  -- Use S and n as abbreviations for cleaner proofs
  set S := freeKCols T i k hk with hS_def
  set n := freeKSuccCount T i k hk with hn_def
  -- Step 2: The matched condition for free k cells
  -- isMatchedFreeK c ↔ T c = k ∧ ¬isForcedK ∧ ¬isUnmatchedFreeK
  -- where ¬isUnmatchedFreeK means: freeKCountUpTo c.col ≤ freeKSuccCount
  -- And freeKCountUpTo c.col = (S.filter (· ≤ c.col)).card by freeKCountUpTo_eq_filter_card
  -- So the matched condition is: (S.filter (· ≤ c.col)).card ≤ n
  
  -- Step 3: Show the filter of matched cells equals the filter with the column condition
  have h_filter_eq : (Finset.univ.filter (fun c => c.val.1 = i ∧ isMatchedFreeK T k hk c)).card = 
      (cells.filter (fun c => (S.filter (· ≤ c.val.2)).card ≤ n)).card := by
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cells]
    constructor
    · intro ⟨hrow, hmatched⟩
      unfold isMatchedFreeK at hmatched
      obtain ⟨hval, hfree, hunmatched⟩ := hmatched
      refine ⟨⟨hrow, hval, hfree⟩, ?_⟩
      -- ¬isUnmatchedFreeK means freeKCountUpTo c.col ≤ freeKSuccCount
      unfold isUnmatchedFreeK at hunmatched
      push Not at hunmatched
      have h := hunmatched hval hfree
      -- Use hrow to rewrite c.val.1 to i in h
      rw [hrow] at h
      -- freeKCountUpTo c.col = (S.filter (· ≤ c.col)).card
      rw [freeKCountUpTo_eq_filter_card T i k hk c.val.2, ← hS_def] at h
      -- freeKSuccCount = n
      rw [← hn_def] at h
      exact h
    · intro ⟨⟨hrow, hval, hfree⟩, hcond⟩
      refine ⟨hrow, ?_⟩
      unfold isMatchedFreeK
      refine ⟨hval, hfree, ?_⟩
      -- Need to show ¬isUnmatchedFreeK
      unfold isUnmatchedFreeK
      push Not
      intro _ _
      -- hcond: (S.filter (· ≤ c.col)).card ≤ n
      -- Need: freeKCountUpTo c.col ≤ freeKSuccCount
      rw [hrow, freeKCountUpTo_eq_filter_card T i k hk c.val.2, ← hS_def, ← hn_def]
      exact hcond
  -- The goal after Fintype.card_subtype is: #{x | x ∈ {c | ...}} = ...
  convert h_filter_eq using 1
  on_goal 1 => rfl
  
  -- Step 4: Show the bijection between cells and columns in S
  have h_col_mem : ∀ c ∈ cells, c.val.2 ∈ S := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cells] at hc
    rw [hS_def]
    unfold freeKCols
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c, ⟨hc.1, hc.2.1, hc.2.2⟩, rfl⟩
  
  have h_col_inj : ∀ c₁ ∈ cells, ∀ c₂ ∈ cells, c₁.val.2 = c₂.val.2 → c₁ = c₂ := by
    intro c₁ hc₁ c₂ hc₂ hcol
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cells] at hc₁ hc₂
    ext
    · rw [hc₁.1, hc₂.1]
    · exact hcol
  
  have h_col_surj : ∀ s ∈ S, ∃ c ∈ cells, c.val.2 = s := by
    intro s hs
    rw [hS_def] at hs
    unfold freeKCols at hs
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨c, ⟨hrow, hval, hfree⟩, hcol⟩ := hs
    refine ⟨c, ?_, hcol⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cells]
    exact ⟨hrow, hval, hfree⟩
  
  -- Step 5: Apply the bijection to get the equality with column filter
  have h_bij : (cells.filter (fun c => (S.filter (· ≤ c.val.2)).card ≤ n)).card = 
      (S.filter (fun s => (S.filter (· ≤ s)).card ≤ n)).card := by
    apply Finset.card_bij (fun c _ => c.val.2)
    · intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      exact ⟨h_col_mem c hc.1, hc.2⟩
    · intro c₁ hc₁ c₂ hc₂ heq
      simp only [Finset.mem_filter] at hc₁ hc₂
      exact h_col_inj c₁ hc₁.1 c₂ hc₂.1 heq
    · intro s hs
      simp only [Finset.mem_filter] at hs
      obtain ⟨c, hc, hcol⟩ := h_col_surj s hs.1
      refine ⟨c, ?_, hcol⟩
      simp only [Finset.mem_filter]
      exact ⟨hc, hcol ▸ hs.2⟩
  rw [h_bij]
  
  -- Step 6: Apply matched_cols_count
  rw [matched_cols_count S n]
  -- Now need to show min S.card n = min m n where m = freeKCount
  rw [hS_def, freeKCols_card T i k hk, hn_def]

/-- Per-row count of matched free (k+1)'s equals min(m, n) where m = freeKCount, n = freeKSuccCount.
    
    A free (k+1) at column c is matched iff freeKCount + freeKSuccCountUpTo(c) > freeKSuccCount.
    Since free (k+1)'s are enumerated by column order, the j-th free (k+1) has freeKSuccCountUpTo = j.
    So matched free (k+1)'s are those with m + j > n, giving min(m, n) matched.
    
    The proof uses `matched_kSucc_cols_count` via a bijection between cells and columns. -/
private lemma matchedFreeKSucc_row_card {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) :
    Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} = 
    min (freeKCount T i k hk) (freeKSuccCount T i k hk) := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Step 1: Define the finset of free (k+1) cells in row i
  let cells := Finset.univ.filter (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} =>
    c.val.1 = i ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c)
  -- Use S and m as abbreviations (not let bindings) for cleaner proofs
  set S := freeKSuccCols T i k hk with hS_def
  set m := freeKCount T i k hk with hm_def
  -- Step 2: The matched condition for free (k+1) cells
  -- isMatchedFreeKSucc c ↔ T c = k+1 ∧ ¬isForcedKSucc ∧ ¬isUnmatchedFreeKSucc
  -- where ¬isUnmatchedFreeKSucc means: freeKCount + freeKSuccCountUpTo c.col > freeKSuccCount
  -- And freeKSuccCountUpTo c.col = (S.filter (· ≤ c.col)).card by freeKSuccCountUpTo_eq_filter_card
  -- So the matched condition is: m + (S.filter (· ≤ c.col)).card > S.card
  
  -- Step 3: Show the filter of matched cells equals the filter with the column condition
  have h_filter_eq : (Finset.univ.filter (fun c => c.val.1 = i ∧ isMatchedFreeKSucc T k hk c)).card = 
      (cells.filter (fun c => m + (S.filter (· ≤ c.val.2)).card > S.card)).card := by
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cells]
    constructor
    · intro ⟨hrow, hmatched⟩
      unfold isMatchedFreeKSucc at hmatched
      obtain ⟨hval, hfree, hunmatched⟩ := hmatched
      refine ⟨⟨hrow, hval, hfree⟩, ?_⟩
      -- ¬isUnmatchedFreeKSucc means freeKCount + freeKSuccCountUpTo c.col > freeKSuccCount
      unfold isUnmatchedFreeKSucc at hunmatched
      push Not at hunmatched
      have h := hunmatched hval hfree
      -- Use hrow to rewrite c.val.1 to i in h
      rw [hrow] at h
      -- freeKSuccCountUpTo c.col = (S.filter (· ≤ c.col)).card
      rw [freeKSuccCountUpTo_eq_filter_card T i k hk c.val.2, ← hS_def] at h
      -- freeKSuccCount = S.card
      rw [← freeKSuccCols_card T i k hk, ← hS_def, ← hm_def] at h
      exact h
    · intro ⟨⟨hrow, hval, hfree⟩, hcond⟩
      refine ⟨hrow, ?_⟩
      unfold isMatchedFreeKSucc
      refine ⟨hval, hfree, ?_⟩
      -- Need to show ¬isUnmatchedFreeKSucc
      unfold isUnmatchedFreeKSucc
      push Not
      intro _ _
      -- hcond: m + (S.filter (· ≤ c.col)).card > S.card
      -- Need: freeKCount + freeKSuccCountUpTo c.col > freeKSuccCount
      rw [hrow, freeKSuccCountUpTo_eq_filter_card T i k hk c.val.2, ← hS_def]
      rw [← freeKSuccCols_card T i k hk, ← hS_def, ← hm_def]
      exact hcond
  -- The goal after Fintype.card_subtype is: #{x | x ∈ {c | ...}} = ...
  -- This is definitionally equal to (Finset.univ.filter (fun c => c.val.1 = i ∧ isMatchedFreeKSucc T k hk c)).card
  convert h_filter_eq using 1
  on_goal 1 => rfl
  
  -- Step 4: Show the bijection between cells and columns in S
  have h_col_mem : ∀ c ∈ cells, c.val.2 ∈ S := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cells] at hc
    rw [hS_def]
    unfold freeKSuccCols
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c, ⟨hc.1, hc.2.1, hc.2.2⟩, rfl⟩
  
  have h_col_inj : ∀ c₁ ∈ cells, ∀ c₂ ∈ cells, c₁.val.2 = c₂.val.2 → c₁ = c₂ := by
    intro c₁ hc₁ c₂ hc₂ hcol
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cells] at hc₁ hc₂
    ext
    · rw [hc₁.1, hc₂.1]
    · exact hcol
  
  have h_col_surj : ∀ s ∈ S, ∃ c ∈ cells, c.val.2 = s := by
    intro s hs
    rw [hS_def] at hs
    unfold freeKSuccCols at hs
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨c, ⟨hrow, hval, hfree⟩, hcol⟩ := hs
    refine ⟨c, ?_, hcol⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cells]
    exact ⟨hrow, hval, hfree⟩
  
  -- Step 5: Apply the bijection to get the equality with column filter
  have h_bij : (cells.filter (fun c => m + (S.filter (· ≤ c.val.2)).card > S.card)).card = 
      (S.filter (fun s => m + (S.filter (· ≤ s)).card > S.card)).card := by
    apply Finset.card_bij (fun c _ => c.val.2)
    · intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      exact ⟨h_col_mem c hc.1, hc.2⟩
    · intro c₁ hc₁ c₂ hc₂ heq
      simp only [Finset.mem_filter] at hc₁ hc₂
      exact h_col_inj c₁ hc₁.1 c₂ hc₂.1 heq
    · intro s hs
      simp only [Finset.mem_filter] at hs
      obtain ⟨c, hc, hcol⟩ := h_col_surj s hs.1
      refine ⟨c, ?_, hcol⟩
      simp only [Finset.mem_filter]
      exact ⟨hc, hcol ▸ hs.2⟩
  rw [h_bij]
  
  -- Step 6: Apply matched_kSucc_cols_count
  rw [matched_kSucc_cols_count S m]
  -- Now need to show min m S.card = min m n where n = freeKSuccCount
  rw [hS_def, freeKSuccCols_card T i k hk, hm_def]

/-- Per-row count of unmatched free k's equals m - min(m, n) where m = freeKCount, n = freeKSuccCount.
    
    Since free k's partition into matched and unmatched:
    |unmatched free k's| = |free k's| - |matched free k's| = m - min(m, n)
    
    This is the complement of `matchedFreeK_row_card`. -/
private lemma unmatchedFreeK_row_card {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) :
    Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isUnmatchedFreeK T k hk c} = 
    freeKCount T i k hk - min (freeKCount T i k hk) (freeKSuccCount T i k hk) := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  -- Free k's in row i = matched + unmatched (disjoint union)
  set m := freeKCount T i k hk with hm_def
  set n := freeKSuccCount T i k hk with hn_def
  -- Matched free k's
  have h_matched : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeK T k hk c} = min m n := matchedFreeK_row_card T i k hk
  -- Free k's = matched ∪ unmatched (disjoint)
  have h_partition : {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ T c = k ∧ ¬isForcedK T k hk c} =
    {c | c.val.1 = i ∧ isMatchedFreeK T k hk c} ∪ {c | c.val.1 = i ∧ isUnmatchedFreeK T k hk c} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro ⟨hrow, hval, hfree⟩
      by_cases h : isUnmatchedFreeK T k hk c
      · right; exact ⟨hrow, h⟩
      · left
        unfold isMatchedFreeK
        exact ⟨hrow, hval, hfree, h⟩
    · intro h
      rcases h with ⟨hrow, hmatched⟩ | ⟨hrow, hunmatched⟩
      · unfold isMatchedFreeK at hmatched
        exact ⟨hrow, hmatched.1, hmatched.2.1⟩
      · unfold isUnmatchedFreeK at hunmatched
        exact ⟨hrow, hunmatched.1, hunmatched.2.1⟩
  -- Disjointness
  have h_disj : Disjoint {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeK T k hk c} 
    {c | c.val.1 = i ∧ isUnmatchedFreeK T k hk c} := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨_, hmatched⟩, ⟨_, hunmatched⟩⟩
    unfold isMatchedFreeK at hmatched
    exact hmatched.2.2 hunmatched
  -- Finiteness
  have hfin1 : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeK T k hk c} := Set.toFinite _
  have hfin2 : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isUnmatchedFreeK T k hk c} := Set.toFinite _
  -- Compute total from partition
  have h_total_eq : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ T c = k ∧ ¬isForcedK T k hk c} = 
    Nat.card {c | c.val.1 = i ∧ isMatchedFreeK T k hk c} + 
    Nat.card {c | c.val.1 = i ∧ isUnmatchedFreeK T k hk c} := by
    rw [h_partition]
    rw [Nat.card_eq_card_toFinset, Set.toFinset_union, 
        Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr h_disj)]
    simp only [Nat.card_eq_card_toFinset]
  -- Total = m
  have h_total_m : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ T c = k ∧ ¬isForcedK T k hk c} = m := rfl
  -- Combine
  rw [h_total_m, h_matched] at h_total_eq
  omega

/-- Per-row count of unmatched free (k+1)'s equals n - min(m, n) where m = freeKCount, n = freeKSuccCount.
    
    Since free (k+1)'s partition into matched and unmatched:
    |unmatched free (k+1)'s| = |free (k+1)'s| - |matched free (k+1)'s| = n - min(m, n)
    
    This is the complement of `matchedFreeKSucc_row_card`. -/
private lemma unmatchedFreeKSucc_row_card {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) :
    Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} = 
    freeKSuccCount T i k hk - min (freeKCount T i k hk) (freeKSuccCount T i k hk) := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  -- Free (k+1)'s in row i = matched + unmatched (disjoint union)
  set m := freeKCount T i k hk with hm_def
  set n := freeKSuccCount T i k hk with hn_def
  -- Matched free (k+1)'s
  have h_matched : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} = min m n := matchedFreeKSucc_row_card T i k hk
  -- Free (k+1)'s = matched ∪ unmatched (disjoint)
  have h_partition : {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c} =
    {c | c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} ∪ {c | c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro ⟨hrow, hval, hfree⟩
      by_cases h : isUnmatchedFreeKSucc T k hk c
      · right; exact ⟨hrow, h⟩
      · left
        unfold isMatchedFreeKSucc
        exact ⟨hrow, hval, hfree, h⟩
    · intro h
      rcases h with ⟨hrow, hmatched⟩ | ⟨hrow, hunmatched⟩
      · unfold isMatchedFreeKSucc at hmatched
        exact ⟨hrow, hmatched.1, hmatched.2.1⟩
      · unfold isUnmatchedFreeKSucc at hunmatched
        exact ⟨hrow, hunmatched.1, hunmatched.2.1⟩
  -- Disjointness
  have h_disj : Disjoint {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} 
    {c | c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨_, hmatched⟩, ⟨_, hunmatched⟩⟩
    unfold isMatchedFreeKSucc at hmatched
    exact hmatched.2.2 hunmatched
  -- Finiteness
  have hfin1 : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} := Set.toFinite _
  have hfin2 : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} := Set.toFinite _
  -- Compute total from partition
  have h_total_eq : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c} = 
    Nat.card {c | c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} + 
    Nat.card {c | c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} := by
    rw [h_partition]
    rw [Nat.card_eq_card_toFinset, Set.toFinset_union, 
        Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr h_disj)]
    simp only [Nat.card_eq_card_toFinset]
  -- Total = n
  have h_total_n : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c} = n := rfl
  -- Combine
  rw [h_total_n, h_matched] at h_total_eq
  omega

/-- The number of matched free k's equals the number of matched free (k+1)'s.
    
    **Proof Strategy:**
    In each row i with m = freeKCount i free k's and n = freeKSuccCount i free (k+1)'s:
    
    1. **Counting unmatched free k's:**
       - A free k at column j is unmatched iff freeKCountUpTo(j) > n
       - The free k's can be indexed 1, 2, ..., m by their column order
       - The j-th free k has freeKCountUpTo = j (by definition of freeKCountUpTo)
       - So unmatched free k's are those with index > n
       - By count_gt_threshold: |unmatched free k's| = m - min(m, n)
       - Therefore: |matched free k's| = m - (m - min(m, n)) = min(m, n)
    
    2. **Counting unmatched free (k+1)'s:**
       - A free (k+1) at column j is unmatched iff freeKSuccCountUpTo(j) > freeKCountBefore(j)
       - In a semistandard tableau, all k's are to the left of all (k+1)'s in each row
       - So freeKCountBefore(j) for the j-th free (k+1) equals m (all free k's are before)
       - The condition becomes: j > m, i.e., the (k+1) has index > m
       - By count_gt_threshold: |unmatched free (k+1)'s| = n - min(m, n)
       - Therefore: |matched free (k+1)'s| = n - (n - min(m, n)) = min(m, n)
    
    3. **Conclusion:**
       In each row, |matched free k's| = |matched free (k+1)'s| = min(m, n).
       Summing over all rows gives the equality.
    
    **Note:** The formal proof requires showing that freeKCountUpTo at the j-th free k
    equals j, which follows from the definition but requires careful bookkeeping.
    
    **Formalization approach (row decomposition):**
    The proof decomposes by rows. For each row i:
    - Let m = freeKCount T i k hk (number of free k's in row i)
    - Let n = freeKSuccCount T i k hk (number of free (k+1)'s in row i)
    - Matched free k's in row i = {c | c.row = i ∧ isMatchedFreeK T k hk c}
    - Matched free (k+1)'s in row i = {c | c.row = i ∧ isMatchedFreeKSucc T k hk c}
    
    The key per-row equality: |matched free k's in row i| = |matched free (k+1)'s in row i| = min(m, n)
    
    Proof of per-row equality:
    1. Free k's in row i are at columns c₁ < c₂ < ... < cₘ (by row-weak ordering)
    2. freeKCountUpTo(i, cⱼ) = j for each j (by definition of freeKCountUpTo)
    3. Matched free k's are those with freeKCountUpTo ≤ n, i.e., j ≤ n
    4. There are min(m, n) such j's
    5. Similarly for (k+1)'s using freeKSuccCountUpTo and freeKCountBefore
    
    Summing over all rows gives the global equality. -/
private lemma matchedFreeK_card_eq_matchedFreeKSucc_card {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (_hT : IsSemistandard T) (k : Fin N) (hk : k.val + 1 < N) :
    Nat.card {c | isMatchedFreeK T k hk c} = Nat.card {c | isMatchedFreeKSucc T k hk c} := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  -- Decompose by rows: both sides equal ∑ᵢ min(freeKCount i, freeKSuccCount i)
  -- Use matchedFreeK_row_card and matchedFreeKSucc_row_card
  -- 
  -- Key insight: Both counts decompose by row, and in each row i:
  --   matchedFreeK_row_card shows: #{matched free k's in row i} = min(m_i, n_i)
  --   matchedFreeKSucc_row_card shows: #{matched free (k+1)'s in row i} = min(m_i, n_i)
  -- where m_i = freeKCount T i k hk and n_i = freeKSuccCount T i k hk.
  -- Therefore summing over rows gives the equality.
  
  -- Step 1: Convert to Fintype.card
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype, Fintype.card_subtype]
  simp only [Set.mem_ofPred_eq]
  
  -- Step 2: Decompose by rows
  -- LHS = ∑ᵢ #{c | c.row = i ∧ isMatchedFreeK T k hk c}
  -- RHS = ∑ᵢ #{c | c.row = i ∧ isMatchedFreeKSucc T k hk c}
  
  have h_decomp_K : (Finset.univ.filter (fun c => isMatchedFreeK T k hk c)).card = 
      ∑ i : Fin N, (Finset.univ.filter (fun c => c.val.1 = i ∧ isMatchedFreeK T k hk c)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := fun c => c.val.1)
        (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
      
  have h_decomp_KSucc : (Finset.univ.filter (fun c => isMatchedFreeKSucc T k hk c)).card = 
      ∑ i : Fin N, (Finset.univ.filter (fun c => c.val.1 = i ∧ isMatchedFreeKSucc T k hk c)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := fun c => c.val.1)
        (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
      
  rw [h_decomp_K, h_decomp_KSucc]
  
  -- Step 3: Show each row contributes the same amount
  apply Finset.sum_congr rfl
  intro i _
  -- Use matchedFreeK_row_card and matchedFreeKSucc_row_card
  have hK := matchedFreeK_row_card T i k hk
  have hKSucc := matchedFreeKSucc_row_card T i k hk
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hK hKSucc
  simp only [Set.mem_ofPred_eq] at hK hKSucc
  rw [hK, hKSucc]

private lemma notUnmatched_k_kSucc_card_eq {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (hT : IsSemistandard T) (k : Fin N) (hk : k.val + 1 < N) :
    Nat.card {c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} =
      Nat.card {c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} := by
  classical
  -- Step 1: Rewrite using the decomposition lemmas
  rw [notUnmatchedK_eq_union T k hk, notUnmatchedKSucc_eq_union T k hk]
  -- Step 2: The sets are finite (subsets of the finite skew Young diagram subtype)
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  have hfin_forcedK : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | isForcedK T k hk c} :=
    Set.toFinite _
  have hfin_matchedK : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | isMatchedFreeK T k hk c} :=
    Set.toFinite _
  have hfin_forcedKSucc : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | isForcedKSucc T k hk c} :=
    Set.toFinite _
  have hfin_matchedKSucc : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | isMatchedFreeKSucc T k hk c} :=
    Set.toFinite _
  -- Step 3: Get Fintype instances
  haveI : Fintype {c | isForcedK T k hk c} := hfin_forcedK.fintype
  haveI : Fintype {c | isMatchedFreeK T k hk c} := hfin_matchedK.fintype
  haveI : Fintype {c | isForcedKSucc T k hk c} := hfin_forcedKSucc.fintype
  haveI : Fintype {c | isMatchedFreeKSucc T k hk c} := hfin_matchedKSucc.fintype
  haveI : Fintype ({c | isForcedK T k hk c} ∪ {c | isMatchedFreeK T k hk c} : Set _) :=
    (hfin_forcedK.union hfin_matchedK).fintype
  haveI : Fintype ({c | isForcedKSucc T k hk c} ∪ {c | isMatchedFreeKSucc T k hk c} : Set _) :=
    (hfin_forcedKSucc.union hfin_matchedKSucc).fintype
  -- Step 4: Use disjoint union cardinality
  rw [Nat.card_eq_card_toFinset, Set.toFinset_union,
      Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr (forcedK_matchedFreeK_disjoint T k hk))]
  rw [Nat.card_eq_card_toFinset, Set.toFinset_union,
      Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr (forcedKSucc_matchedFreeKSucc_disjoint T k hk))]
  -- Step 5: Use the bijection lemmas
  have h_forced : Nat.card {c | isForcedK T k hk c} = Nat.card {c | isForcedKSucc T k hk c} :=
    forced_k_kSucc_bijection T k hk
  have h_matched : Nat.card {c | isMatchedFreeK T k hk c} = Nat.card {c | isMatchedFreeKSucc T k hk c} :=
    matchedFreeK_card_eq_matchedFreeKSucc_card T hT k hk
  simp only [Nat.card_eq_card_toFinset] at h_forced h_matched
  omega

/-! ### Per-row count swap lemmas for Bender-Knuth

These lemmas establish that applying Bender-Knuth swaps the counts of free k's and free (k+1)'s
in each row. This is the key fact needed to prove that matched cells stay matched after BK. -/

/-- A cell is a free (k+1) in T' iff it was either a matched free (k+1) in T or an unmatched free k in T.
    This is the key characterization for the count swap lemma. -/
private lemma freeKSucc_in_benderKnuth_iff {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) :
    let T' := benderKnuth k hk T hT
    (T' c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk c) ↔
    isMatchedFreeKSucc T k hk c ∨ isUnmatchedFreeK T k hk c := by
  intro T'
  constructor
  · -- (→) If c is a free (k+1) in T', show it was matched free (k+1) or unmatched free k in T
    intro ⟨hT'c, hfree'⟩
    -- By benderKnuth_eq_kSucc_iff, T' c = k+1 means:
    -- (T c = k+1 ∧ ¬isUnmatchedFreeKSucc) ∨ isUnmatchedFreeK
    rw [benderKnuth_eq_kSucc_iff k hk T hT c] at hT'c
    rcases hT'c with ⟨hTc, h_not_unmatched⟩ | h_unmatched_k
    · -- Case: T c = k+1 and c was not unmatched free (k+1)
      -- Need to show c was a matched free (k+1)
      left
      unfold isMatchedFreeKSucc
      refine ⟨hTc, ?_, h_not_unmatched⟩
      -- Show c was not forced in T
      -- If c were forced in T, then c would be forced in T' (by forced_kSucc_preserved')
      -- But we have hfree' : ¬isForcedKSucc T' c, contradiction
      intro hforced
      have hforced' := forced_kSucc_preserved' k hk T hT c ⟨hTc, hforced.2⟩
      exact hfree' hforced'
    · -- Case: c was an unmatched free k in T
      right
      exact h_unmatched_k
  · -- (←) If c was matched free (k+1) or unmatched free k, show it's free (k+1) in T'
    intro h
    rcases h with hmatched | hunmatched
    · -- Case: c was a matched free (k+1) in T
      obtain ⟨hval, hfree, h_not_unmatched⟩ := hmatched
      constructor
      · -- T' c = k+1 by benderKnuth_matched_kSucc'
        exact benderKnuth_matched_kSucc' k hk T hT c hval hfree h_not_unmatched
      · -- c is not forced in T' (part 2 of matched_kSucc_stays_matched')
        -- We need to show ¬isForcedKSucc T' k hk c
        intro hforced'
        -- This follows from matched_kSucc_stays_matched' part 2
        obtain ⟨_, c_above, h_col, h_row, hT'_above⟩ := hforced'
        -- By column-strictness in T, T c_above < T c = k+1
        have h_lt : T c_above < T c := hT.2 c_above c h_col (by simp only [Fin.lt_def]; omega)
        rw [hval] at h_lt
        -- So T c_above < k+1, meaning T c_above ≤ k
        have h_ne_kSucc : T c_above ≠ ⟨k.val + 1, hk⟩ := by
          intro h; rw [h] at h_lt; simp only [Fin.lt_def] at h_lt; omega
        by_cases h_eq_k : T c_above = k
        · -- If T c_above = k, then c was forced in T (contradiction with hfree)
          have hforced : isForcedKSucc T k hk c := ⟨hval, c_above, h_col, h_row, h_eq_k⟩
          exact hfree hforced
        · -- If T c_above ≠ k and T c_above ≠ k+1, then BK doesn't change it
          have hT'_eq : T' c_above = T c_above := benderKnuth_unchanged' k hk T hT c_above h_eq_k h_ne_kSucc
          rw [hT'_eq] at hT'_above
          exact h_eq_k hT'_above
    · -- Case: c was an unmatched free k in T
      constructor
      · -- T' c = k+1 by benderKnuth_unmatched_k'
        exact benderKnuth_unmatched_k' k hk T hT c hunmatched
      · -- c is not forced in T' by unmatched_k_becomes_free_kSucc'
        exact unmatched_k_becomes_free_kSucc' k hk T hT c hunmatched

/-- The set of free (k+1)'s in T' in row i is the disjoint union of matched free (k+1)'s and
    unmatched free k's from T in row i. -/
private lemma freeKSucc_benderKnuth_eq_union {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T) (i : Fin N) :
    let T' := benderKnuth k hk T hT
    {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ T' c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk c} =
    {c | c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} ∪ {c | c.val.1 = i ∧ isUnmatchedFreeK T k hk c} := by
  intro T'
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro ⟨hrow, hT'c, hfree'⟩
    have h := (freeKSucc_in_benderKnuth_iff k hk T hT c).mp ⟨hT'c, hfree'⟩
    rcases h with hmatched | hunmatched
    · left; exact ⟨hrow, hmatched⟩
    · right; exact ⟨hrow, hunmatched⟩
  · intro h
    rcases h with ⟨hrow, hmatched⟩ | ⟨hrow, hunmatched⟩
    · have h := (freeKSucc_in_benderKnuth_iff k hk T hT c).mpr (Or.inl hmatched)
      exact ⟨hrow, h.1, h.2⟩
    · have h := (freeKSucc_in_benderKnuth_iff k hk T hT c).mpr (Or.inr hunmatched)
      exact ⟨hrow, h.1, h.2⟩

/-- Matched free (k+1)'s and unmatched free k's are disjoint (they have different values). -/
private lemma matchedFreeKSucc_unmatchedFreeK_disjoint {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) (i : Fin N) :
    Disjoint {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | c.val.1 = i ∧ isMatchedFreeKSucc T k hk c}
             {c | c.val.1 = i ∧ isUnmatchedFreeK T k hk c} := by
  rw [Set.disjoint_iff]
  intro c ⟨⟨_, hmatched⟩, ⟨_, hunmatched⟩⟩
  -- isMatchedFreeKSucc means T c = k+1
  -- isUnmatchedFreeK means T c = k
  have h1 : T c = ⟨k.val + 1, hk⟩ := hmatched.1
  have h2 : T c = k := hunmatched.1
  rw [h1] at h2
  simp only [Fin.ext_iff] at h2
  omega

/-- Characterization of free k cells in T' (dual to freeKSucc_in_benderKnuth_iff). -/
private lemma freeK_in_benderKnuth_iff {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) :
    let T' := benderKnuth k hk T hT
    (T' c = k ∧ ¬isForcedK T' k hk c) ↔
    isMatchedFreeK T k hk c ∨ isUnmatchedFreeKSucc T k hk c := by
  intro T'
  constructor
  · -- (→) If c is a free k in T', show it was matched free k or unmatched free (k+1) in T
    intro ⟨hT'c, hfree'⟩
    -- By benderKnuth_eq_k_iff, T' c = k means:
    -- (T c = k ∧ ¬isUnmatchedFreeK) ∨ isUnmatchedFreeKSucc
    rw [benderKnuth_eq_k_iff k hk T hT c] at hT'c
    rcases hT'c with ⟨hTc, h_not_unmatched⟩ | h_unmatched_ksucc
    · -- Case: T c = k and c was not unmatched free k
      -- Need to show c was a matched free k
      left
      unfold isMatchedFreeK
      refine ⟨hTc, ?_, h_not_unmatched⟩
      -- Show c was not forced in T
      -- If c were forced in T, then c would be forced in T' (by forced_k_preserved')
      -- But we have hfree' : ¬isForcedK T' c, contradiction
      intro hforced
      have hforced' := forced_k_preserved' k hk T hT c ⟨hTc, hforced.2⟩
      exact hfree' hforced'
    · -- Case: c was an unmatched free (k+1) in T
      right
      exact h_unmatched_ksucc
  · -- (←) If c was matched free k or unmatched free (k+1), show it's free k in T'
    intro h
    rcases h with hmatched | hunmatched
    · -- Case: c was a matched free k in T
      obtain ⟨hval, hfree, h_not_unmatched⟩ := hmatched
      constructor
      · -- T' c = k by benderKnuth_matched_k'
        exact benderKnuth_matched_k' k hk T hT c hval hfree h_not_unmatched
      · -- c is not forced in T' (part 2 of matched_k_stays_matched')
        intro hforced'
        obtain ⟨_, c_below, h_col, h_row, hT'_below⟩ := hforced'
        -- By column-strictness in T, T c < T c_below
        have h_lt : T c < T c_below := hT.2 c c_below h_col.symm (by simp only [Fin.lt_def]; omega)
        rw [hval] at h_lt
        -- So k < T c_below
        have h_ne_k : T c_below ≠ k := by
          intro h; rw [h] at h_lt; simp only [Fin.lt_def] at h_lt; omega
        by_cases h_eq_kSucc : T c_below = ⟨k.val + 1, hk⟩
        · -- If T c_below = k+1, then c was forced in T (contradiction with hfree)
          have hforced : isForcedK T k hk c := ⟨hval, c_below, h_col, h_row, h_eq_kSucc⟩
          exact hfree hforced
        · -- If T c_below ≠ k and T c_below ≠ k+1, then BK doesn't change it
          have hT'_eq : T' c_below = T c_below := benderKnuth_unchanged' k hk T hT c_below h_ne_k h_eq_kSucc
          rw [hT'_eq] at hT'_below
          exact h_eq_kSucc hT'_below
    · -- Case: c was an unmatched free (k+1) in T
      constructor
      · -- T' c = k by benderKnuth_unmatched_kSucc'
        exact benderKnuth_unmatched_kSucc' k hk T hT c hunmatched
      · -- c is not forced in T' by unmatched_kSucc_becomes_free_k'
        exact unmatched_kSucc_becomes_free_k' k hk T hT c hunmatched

/-- The set of free k's in T' in row i is the disjoint union of matched free k's and
    unmatched free (k+1)'s from T in row i. -/
private lemma freeK_benderKnuth_eq_union {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T) (i : Fin N) :
    let T' := benderKnuth k hk T hT
    {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ T' c = k ∧ ¬isForcedK T' k hk c} =
    {c | c.val.1 = i ∧ isMatchedFreeK T k hk c} ∪ {c | c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} := by
  intro T'
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro ⟨hrow, hT'c, hfree'⟩
    have h := (freeK_in_benderKnuth_iff k hk T hT c).mp ⟨hT'c, hfree'⟩
    rcases h with hmatched | hunmatched
    · left; exact ⟨hrow, hmatched⟩
    · right; exact ⟨hrow, hunmatched⟩
  · intro h
    rcases h with ⟨hrow, hmatched⟩ | ⟨hrow, hunmatched⟩
    · have h := (freeK_in_benderKnuth_iff k hk T hT c).mpr (Or.inl hmatched)
      exact ⟨hrow, h.1, h.2⟩
    · have h := (freeK_in_benderKnuth_iff k hk T hT c).mpr (Or.inr hunmatched)
      exact ⟨hrow, h.1, h.2⟩

/-- Matched free k's and unmatched free (k+1)'s are disjoint (they have different values). -/
private lemma matchedFreeK_unmatchedFreeKSucc_disjoint {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) (i : Fin N) :
    Disjoint {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | c.val.1 = i ∧ isMatchedFreeK T k hk c}
             {c | c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} := by
  rw [Set.disjoint_iff]
  intro c ⟨⟨_, hmatched⟩, ⟨_, hunmatched⟩⟩
  -- isMatchedFreeK means T c = k
  -- isUnmatchedFreeKSucc means T c = k+1
  have h1 : T c = k := hmatched.1
  have h2 : T c = ⟨k.val + 1, hk⟩ := hunmatched.1
  rw [h1] at h2
  simp only [Fin.ext_iff] at h2
  omega

/-- After Bender-Knuth, the count of free (k+1)'s equals the original count of free k's.

    **Proof idea:** Free (k+1)'s in T' = {matched free (k+1)'s from T} ∪ {unmatched free k's from T}
    By `benderKnuth_eq_kSucc_iff`: T' c = k+1 iff (T c = k+1 ∧ ¬isUnmatchedFreeKSucc) ∨ isUnmatchedFreeK
    
    - #{matched free (k+1)'s in row i} = min(m_i, n_i) (by `matchedFreeKSucc_row_card`)
    - #{unmatched free k's in row i} = m_i - min(m_i, n_i)
    - Total = min(m_i, n_i) + (m_i - min(m_i, n_i)) = m_i = freeKCount T i
    
    The key characterization lemma `freeKSucc_in_benderKnuth_iff` shows that:
    (T' c = k+1 ∧ ¬isForcedKSucc T' c) ↔ isMatchedFreeKSucc T c ∨ isUnmatchedFreeK T c
    
    The set equality `freeKSucc_benderKnuth_eq_union` and disjointness lemma
    `matchedFreeKSucc_unmatchedFreeK_disjoint` provide the infrastructure for the
    cardinality argument.
-/
private lemma freeKSuccCount_benderKnuth {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T) (i : Fin N) :
    freeKSuccCount (benderKnuth k hk T hT) i k hk = freeKCount T i k hk := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  let T' := benderKnuth k hk T hT
  set m := freeKCount T i k hk with hm_def
  set n := freeKSuccCount T i k hk with hn_def
  
  -- The LHS is Nat.card of the set of free (k+1)'s in T' in row i
  -- By freeKSucc_benderKnuth_eq_union, this equals the union of:
  -- - matched free (k+1)'s from T in row i
  -- - unmatched free k's from T in row i
  
  -- Get the set equality
  have h_union := freeKSucc_benderKnuth_eq_union k hk T hT i
  
  -- Get disjointness
  have h_disj := matchedFreeKSucc_unmatchedFreeK_disjoint T k hk i
  
  -- Get cardinalities
  have h_matchedKSucc : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} = min m n := matchedFreeKSucc_row_card T i k hk
  have h_unmatchedK : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isUnmatchedFreeK T k hk c} = m - min m n := unmatchedFreeK_row_card T i k hk
  
  -- The LHS is definitionally equal to Nat.card of the set
  show Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
      c.val.1 = i ∧ T' c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk c} = m
  
  -- Define the two sets
  let A : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ isMatchedFreeKSucc T k hk c}
  let B : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ isUnmatchedFreeK T k hk c}
  let LHS : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
    {c | c.val.1 = i ∧ T' c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk c}
  
  -- The set equality gives LHS = A ∪ B
  have h_LHS_eq : LHS = A ∪ B := h_union
  
  -- So Nat.card LHS = Nat.card (A ∪ B)
  have h_card_eq : Nat.card LHS = Nat.card ↑(A ∪ B) := by
    rw [h_LHS_eq]
  
  -- Use disjoint union cardinality (via ncard)
  have h_ncard : (A ∪ B).ncard = A.ncard + B.ncard := Set.ncard_union_eq h_disj
  
  -- Convert to ncard
  change LHS.ncard = m
  rw [h_LHS_eq, h_ncard]
  
  -- Now use the cardinality facts
  have hA : A.ncard = min m n := h_matchedKSucc
  have hB : B.ncard = m - min m n := h_unmatchedK
  rw [hA, hB]
  
  -- Now we have: min m n + (m - min m n) = m
  omega


/-- After Bender-Knuth, the count of free k's equals the original count of free (k+1)'s.

    **Proof idea:** Free k's in T' = {matched free k's from T} ∪ {unmatched free (k+1)'s from T}
    By `benderKnuth_eq_k_iff`: T' c = k iff (T c = k ∧ ¬isUnmatchedFreeK) ∨ isUnmatchedFreeKSucc
    
    - #{matched free k's in row i} = min(m_i, n_i) (by `matchedFreeK_row_card`)
    - #{unmatched free (k+1)'s in row i} = n_i - min(m_i, n_i)
    - Total = min(m_i, n_i) + (n_i - min(m_i, n_i)) = n_i = freeKSuccCount T i
-/
private lemma freeKCount_benderKnuth {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T) (i : Fin N) :
    freeKCount (benderKnuth k hk T hT) i k hk = freeKSuccCount T i k hk := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  let T' := benderKnuth k hk T hT
  set m := freeKCount T i k hk with hm_def
  set n := freeKSuccCount T i k hk with hn_def
  
  -- The LHS is Nat.card of the set of free k's in T' in row i
  -- By freeK_benderKnuth_eq_union, this equals the union of:
  -- - matched free k's from T in row i
  -- - unmatched free (k+1)'s from T in row i
  
  -- Get the set equality
  have h_union := freeK_benderKnuth_eq_union k hk T hT i
  
  -- Get disjointness
  have h_disj := matchedFreeK_unmatchedFreeKSucc_disjoint T k hk i
  
  -- Get cardinalities
  have h_matchedK : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeK T k hk c} = min m n := matchedFreeK_row_card T i k hk
  have h_unmatchedKSucc : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} = n - min m n := unmatchedFreeKSucc_row_card T i k hk
  
  -- The LHS is definitionally equal to Nat.card of the set
  show Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
      c.val.1 = i ∧ T' c = k ∧ ¬isForcedK T' k hk c} = n
  
  -- Define the two sets
  let A : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ isMatchedFreeK T k hk c}
  let B : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c}
  let LHS : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
    {c | c.val.1 = i ∧ T' c = k ∧ ¬isForcedK T' k hk c}
  
  -- The set equality gives LHS = A ∪ B
  have h_LHS_eq : LHS = A ∪ B := h_union
  
  -- Use disjoint union cardinality (via ncard)
  have h_ncard : (A ∪ B).ncard = A.ncard + B.ncard := Set.ncard_union_eq h_disj
  
  -- Convert to ncard
  change LHS.ncard = n
  rw [h_LHS_eq, h_ncard]
  
  -- Now use the cardinality facts
  have hA : A.ncard = min m n := h_matchedK
  have hB : B.ncard = n - min m n := h_unmatchedKSucc
  rw [hA, hB]
  
  -- Now we have: min m n + (n - min m n) = n
  omega

/-- A matched free k stays as k after BK, and remains matched in T'.
    This is the key lemma for proving that BK(BK(T)) = T for matched cells.
    
    **Definition reminder**: A free k at position c is unmatched iff 
    `freeKCountUpTo(c.col) > freeKSuccCount` (total in row). This compares the
    cumulative count of k's up to c with the TOTAL count of (k+1)'s in the row.
    
    In a semistandard row with `a` free k's followed by `b` free (k+1)'s:
    - The j-th free k has `freeKCountUpTo = j`
    - It's unmatched iff `j > b`, i.e., the rightmost `(a - b)` free k's are unmatched
    - The leftmost `min(a, b)` free k's are matched
    
    So matched free k's DO exist when `b > 0` (there are free (k+1)'s in the row).
    
    **Proof strategy:**
    1. freeKCountUpTo T' c.col = freeKCountUpTo T c.col (by `matched_k_propagates_left`, all free k's
       at columns ≤ c.col are matched, so they stay as k in T')
    2. freeKCountUpTo T c.col ≤ freeKCount T (cumulative ≤ total)
    3. freeKSuccCount T' = freeKCount T (count swap under BK)
    4. Combining: freeKCountUpTo T' c.col ≤ freeKCount T = freeKSuccCount T' -/
lemma matched_k_stays_matched' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hval : T c = k) (hfree : ¬isForcedK T k hk c) (hmatched : ¬isUnmatchedFreeK T k hk c) :
    let T' := benderKnuth k hk T hT
    T' c = k ∧ ¬isForcedK T' k hk c ∧ ¬isUnmatchedFreeK T' k hk c := by
  intro T'
  refine ⟨?_, ?_, ?_⟩
  -- Part 1: T' c = k (from benderKnuth_matched_k')
  · exact benderKnuth_matched_k' k hk T hT c hval hfree hmatched
  -- Part 2: c is not forced in T' (no k+1 directly below c in T')
  · intro hforced'
    obtain ⟨_, c_below, h_col, h_row, hT'_below⟩ := hforced'
    -- By column-strictness in T, T c < T c_below
    have h_lt : T c < T c_below := hT.2 c c_below h_col.symm (by simp only [Fin.lt_def]; omega)
    rw [hval] at h_lt
    -- So T c_below > k
    have h_ne_k : T c_below ≠ k := Fin.ne_of_gt h_lt
    by_cases h_ksucc : T c_below = ⟨k.val + 1, hk⟩
    · -- If T c_below = k+1, then c was forced in T (contradiction with hfree)
      exact hfree ⟨hval, c_below, h_col, h_row, h_ksucc⟩
    · -- If T c_below ≠ k+1, then BK doesn't change it
      have hT'_eq : T' c_below = T c_below := benderKnuth_unchanged' k hk T hT c_below h_ne_k h_ksucc
      rw [hT'_eq] at hT'_below
      exact h_ksucc hT'_below
  -- Part 3: c is not unmatched in T' (count condition)
  -- 
  -- **Proof strategy:**
  -- We need to show ¬(freeKCountUpTo T' c.col > freeKSuccCount T').
  -- 
  -- Key facts:
  -- 1. freeKCountUpTo T' c.col ≤ freeKCountUpTo T c.col
  --    (In a semistandard tableau, all (k+1)'s are at columns > all k's,
  --     so no (k+1)→k conversions happen at columns ≤ c.col)
  -- 2. freeKCountUpTo T c.col ≤ freeKCount T (cumulative ≤ total)
  -- 3. freeKSuccCount T' = freeKCount T (count swap under BK)
  --
  -- Combining: freeKCountUpTo T' c.col ≤ freeKCount T = freeKSuccCount T'
  -- So freeKCountUpTo T' c.col ≤ freeKSuccCount T', meaning c is matched in T'.
  --
  -- However, proving fact 3 (the count swap) requires matchedFreeK_card_eq_matchedFreeKSucc_card.
  -- That lemma is NOW PROVED, so this proof can be completed.
  · intro hunmatched'
    -- We need to show: ¬(freeKCountUpTo T' c.col > freeKSuccCount T')
    -- 
    -- Key insight: Since c is a matched free k in T, all free k's to the left of c are also matched
    -- (by matched_k_propagates_left). And there are no free (k+1)'s at columns ≤ c.col
    -- (by freeKSuccCountUpTo_eq_zero_at_k).
    --
    -- Therefore:
    -- 1. freeKCountUpTo T' c.col ≤ freeKCountUpTo T c.col (no new k's from (k+1)→k conversions)
    -- 2. freeKCountUpTo T c.col ≤ freeKSuccCount T (from hmatched: c is not unmatched)
    -- 3. freeKSuccCount T ≤ freeKSuccCount T' (need to prove this separately)
    --
    -- Actually, we use a simpler approach: show freeKCountUpTo T' c.col ≤ freeKCount T
    -- and freeKSuccCount T' = freeKCount T (count swap).
    
    -- Key fact: there are no free (k+1)'s at columns ≤ c.col (since T c = k)
    have h_no_kSucc : freeKSuccCountUpTo T c.val.1 k hk c.val.2 = 0 := 
      freeKSuccCountUpTo_eq_zero_at_k T hT k hk c hval
    
    -- Step 1: Show freeKCountUpTo T' c.col ≤ freeKCountUpTo T c.col
    -- The free k's in T' at columns ≤ c.col are a subset of free k's in T at columns ≤ c.col
    have h_le_upto : freeKCountUpTo T' c.val.1 k hk c.val.2 ≤ freeKCountUpTo T c.val.1 k hk c.val.2 := by
      unfold freeKCountUpTo
      apply Nat.card_mono
      · haveI : Finite {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
          Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
        exact Set.toFinite _
      · intro d ⟨hd_row, hd_col, hT'd, hd_free'⟩
        -- Need: T d = k ∧ ¬isForcedK T k hk d
        -- From T' d = k, analyze using the definition of benderKnuth
        -- T' = benderKnuth k hk T hT, so T' d = benderKnuth k hk T hT d
        have hT'd' : benderKnuth k hk T hT d = k := hT'd
        simp only [benderKnuth] at hT'd'
        split_ifs at hT'd' with h_unmatched_k h_unmatched_kSucc
        · -- Case: d was unmatched free k in T, so T' d = k+1, not k
          simp only [Fin.ext_iff] at hT'd'
          omega
        · -- Case: d was unmatched free (k+1) in T, so T' d = k
          -- But there are no free (k+1)'s at columns ≤ c.col
          exfalso
          have h_kSucc_val := h_unmatched_kSucc.1
          have h_kSucc_free := h_unmatched_kSucc.2.1
          -- d is a free (k+1) at column ≤ c.col, contradicting h_no_kSucc
          have h_pos : freeKSuccCountUpTo T c.val.1 k hk c.val.2 ≥ 1 := by
            unfold freeKSuccCountUpTo
            have h_d_in : d ∈ {d' : {d' : Fin N × ℕ // d' ∈ skewYoungDiagram lam mu} | 
                d'.val.1 = c.val.1 ∧ d'.val.2 ≤ c.val.2 ∧ T d' = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d'} := 
              ⟨hd_row, hd_col, h_kSucc_val, h_kSucc_free⟩
            haveI : Finite {d' : Fin N × ℕ // d' ∈ skewYoungDiagram lam mu} := 
              Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
            have h_nonempty : Nonempty {d' : {d' : Fin N × ℕ // d' ∈ skewYoungDiagram lam mu} // 
                d'.val.1 = c.val.1 ∧ d'.val.2 ≤ c.val.2 ∧ T d' = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d'} :=
              ⟨⟨d, h_d_in⟩⟩
            haveI h_finite : Finite {d' : {d' : Fin N × ℕ // d' ∈ skewYoungDiagram lam mu} // 
                d'.val.1 = c.val.1 ∧ d'.val.2 ≤ c.val.2 ∧ T d' = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d'} :=
              (Set.toFinite _).to_subtype
            exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨h_nonempty, h_finite⟩)
          omega
        · -- Case: T d unchanged, so T' d = T d = k
          -- Need to show d is free in T (¬isForcedK T k hk d)
          refine ⟨hd_row, hd_col, hT'd', ?_⟩
          -- If d were forced in T, it would stay forced in T' (by forced_k_preserved')
          -- But hd_free' says d is free in T'
          intro hd_forced
          have hd_forced' := forced_k_preserved' k hk T hT d hd_forced
          exact hd_free' hd_forced'
    
    -- Step 2: freeKCountUpTo T c.col ≤ freeKCount T
    have h_le_total : freeKCountUpTo T c.val.1 k hk c.val.2 ≤ freeKCount T c.val.1 k hk := 
      freeKCountUpTo_le_freeKCount T c.val.1 k hk c.val.2
    
    -- Step 3: From hmatched, we know ¬(freeKCountUpTo T c.col > freeKSuccCount T)
    -- i.e., freeKCountUpTo T c.col ≤ freeKSuccCount T
    have h_matched_bound : freeKCountUpTo T c.val.1 k hk c.val.2 ≤ freeKSuccCount T c.val.1 k hk := by
      unfold isUnmatchedFreeK at hmatched
      push Not at hmatched
      exact hmatched hval hfree
    
    -- Step 4: Show freeKSuccCount T' ≥ freeKCountUpTo T' c.col
    -- The key is that freeKSuccCount T' = freeKCount T (count swap under BK).
    -- And freeKCountUpTo T' c.col ≤ freeKCountUpTo T c.col ≤ freeKCount T.
    -- So freeKCountUpTo T' c.col ≤ freeKCount T = freeKSuccCount T'.
    have h_swap := freeKSuccCount_benderKnuth k hk T hT c.val.1
    -- We have:
    -- h_le_upto : freeKCountUpTo T' c.col ≤ freeKCountUpTo T c.col
    -- h_le_total : freeKCountUpTo T c.col ≤ freeKCount T
    -- h_swap : freeKSuccCount T' = freeKCount T
    -- hunmatched' : freeKCountUpTo T' c.col > freeKSuccCount T'
    -- Need to derive a contradiction
    have h_bound : freeKCountUpTo T' c.val.1 k hk c.val.2 ≤ freeKSuccCount T' c.val.1 k hk := by
      calc freeKCountUpTo T' c.val.1 k hk c.val.2 
        ≤ freeKCountUpTo T c.val.1 k hk c.val.2 := h_le_upto
        _ ≤ freeKCount T c.val.1 k hk := h_le_total
        _ = freeKSuccCount T' c.val.1 k hk := h_swap.symm
    -- But hunmatched' says freeKCountUpTo T' c.col > freeKSuccCount T'
    unfold isUnmatchedFreeK at hunmatched'
    have h_gt := hunmatched'.2.2
    omega

/-- Helper: freeKCountUpTo = freeKCountBefore(j+1) because {col ≤ j} = {col < j+1}. -/
private lemma freeKCountUpTo_eq_freeKCountBefore_succ {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) :
    freeKCountUpTo T i k hk j = freeKCountBefore T i k hk (j + 1) := by
  unfold freeKCountUpTo freeKCountBefore
  have h_eq : (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} =>
      c.val.1 = i ∧ c.val.2 ≤ j ∧ T c = k ∧ ¬isForcedK T k hk c) =
    (fun c => c.val.1 = i ∧ c.val.2 < j + 1 ∧ T c = k ∧ ¬isForcedK T k hk c) := by
    ext c
    simp only [Nat.lt_add_one_iff]
  simp only [h_eq]

lemma matched_kSucc_stays_matched' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hval : T c = ⟨k.val + 1, hk⟩) (hfree : ¬isForcedKSucc T k hk c)
    (hmatched : ¬isUnmatchedFreeKSucc T k hk c) :
    let T' := benderKnuth k hk T hT
    T' c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk c ∧ ¬isUnmatchedFreeKSucc T' k hk c := by
  intro T'
  refine ⟨?_, ?_, ?_⟩
  -- Part 1: T' c = k+1 (from benderKnuth_matched_kSucc')
  · exact benderKnuth_matched_kSucc' k hk T hT c hval hfree hmatched
  -- Part 2: c is not forced in T' (no k directly above c in T')
  · intro hforced'
    -- Suppose c is forced in T', meaning there's a cell c_above with T' c_above = k
    obtain ⟨_, c_above, h_col, h_row, hT'_above⟩ := hforced'
    -- By column-strictness in T, T c_above < T c = k+1
    have h_lt : T c_above < T c := hT.2 c_above c h_col (by simp only [Fin.lt_def]; omega)
    rw [hval] at h_lt
    -- So T c_above < k+1, meaning T c_above ≤ k
    have h_ne_kSucc : T c_above ≠ ⟨k.val + 1, hk⟩ := by
      intro h; rw [h] at h_lt; simp only [Fin.lt_def] at h_lt; omega
    by_cases h_eq_k : T c_above = k
    · -- If T c_above = k, then c was forced in T (contradiction with hfree)
      have hforced : isForcedKSucc T k hk c := ⟨hval, c_above, h_col, h_row, h_eq_k⟩
      exact hfree hforced
    · -- If T c_above ≠ k and T c_above ≠ k+1, then BK doesn't change it
      have hT'_eq : T' c_above = T c_above := benderKnuth_unchanged' k hk T hT c_above h_eq_k h_ne_kSucc
      rw [hT'_eq] at hT'_above
      exact h_eq_k hT'_above
  -- Part 3: c is not unmatched in T' (count condition preserved)
  · -- We need to show: ¬isUnmatchedFreeKSucc T' k hk c
    -- i.e., ¬(freeKCount T' + freeKSuccCountUpTo T' c.col ≤ freeKSuccCount T')
    -- i.e., freeKCount T' + freeKSuccCountUpTo T' c.col > freeKSuccCount T'
    --
    -- From the count swaps:
    --   freeKCount T' = freeKSuccCount T = n
    --   freeKSuccCount T' = freeKCount T = m
    -- So we need: n + freeKSuccCountUpTo T' c.col > m
    --
    -- From hmatched (c is matched): ¬(m + freeKSuccCountUpTo T c.col ≤ n)
    -- i.e., m + freeKSuccCountUpTo T c.col > n
    -- i.e., m + cnt_kSucc > n where cnt_kSucc = freeKSuccCountUpTo T c.col
    --
    -- Key insight: freeKSuccCountUpTo T' c.col ≥ #{matched (k+1)'s at cols ≤ c.col in T}
    --                                        + #{unmatched k's at cols ≤ c.col in T}
    -- Since c is a matched (k+1), c contributes to the matched count, so this is ≥ 1.
    -- Also, when m > n, all unmatched k's are at cols < c.col (by semistandardness).
    
    classical
    haveI : Fintype {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
    let m := freeKCount T c.val.1 k hk
    let n := freeKSuccCount T c.val.1 k hk
    let cnt_kSucc := freeKSuccCountUpTo T c.val.1 k hk c.val.2
    
    -- From hmatched: m + cnt_kSucc > n
    have h_matched_bound : m + cnt_kSucc > n := by
      unfold isUnmatchedFreeKSucc at hmatched
      push Not at hmatched
      exact hmatched hval hfree
    
    -- The count swaps after BK
    have h_freeK_swap : freeKCount T' c.val.1 k hk = n := freeKCount_benderKnuth k hk T hT c.val.1
    have h_freeKSucc_swap : freeKSuccCount T' c.val.1 k hk = m := freeKSuccCount_benderKnuth k hk T hT c.val.1
    
    -- freeKSuccCountUpTo T' c.col counts:
    --   (a) matched (k+1)'s from T at cols ≤ c.col (stay as k+1)
    --   (b) unmatched k's from T at cols ≤ c.col (become k+1)
    -- Since c is a matched (k+1), c ∈ (a), so freeKSuccCountUpTo T' c.col ≥ 1.
    -- When m > n, all m - n unmatched k's are at cols < c.col (by semistandardness).
    
    -- Key bound: freeKSuccCountUpTo T' c.col ≥ 1 + max(0, m - n)
    -- Since c is matched (k+1), it stays as (k+1) in T', contributing 1.
    -- The m - n unmatched k's (when m > n) become (k+1)'s at cols < c.col.
    
    have h_c_contributes : freeKSuccCountUpTo T' c.val.1 k hk c.val.2 ≥ 1 := by
      -- c is a free (k+1) in T' at cols ≤ c.col
      have hT'c := benderKnuth_matched_kSucc' k hk T hT c hval hfree hmatched
      have hfree' : ¬isForcedKSucc T' k hk c := by
        intro hforced'
        obtain ⟨_, c_above, h_col, h_row, hT'_above⟩ := hforced'
        have h_lt : T c_above < T c := hT.2 c_above c h_col (by simp only [Fin.lt_def]; omega)
        rw [hval] at h_lt
        have h_ne_kSucc : T c_above ≠ ⟨k.val + 1, hk⟩ := by
          intro h; rw [h] at h_lt; simp only [Fin.lt_def] at h_lt; omega
        by_cases h_eq_k : T c_above = k
        · exact hfree ⟨hval, c_above, h_col, h_row, h_eq_k⟩
        · have hT'_eq : T' c_above = T c_above := benderKnuth_unchanged' k hk T hT c_above h_eq_k h_ne_kSucc
          rw [hT'_eq] at hT'_above
          exact h_eq_k hT'_above
      -- Inline proof of freeKSuccCountUpTo_pos
      unfold freeKSuccCountUpTo
      have h_c_in : c ∈ {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
          d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ T' d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk d} := 
        ⟨rfl, le_refl _, hT'c, hfree'⟩
      haveI : Finite {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
        Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
      have h_nonempty' : Nonempty {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} // 
          d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ T' d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk d} :=
        ⟨⟨c, h_c_in⟩⟩
      haveI h_finite' : Finite {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} // 
          d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ T' d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk d} :=
        (Set.toFinite _).to_subtype
      exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨h_nonempty', h_finite'⟩)
    
    -- When m > n, unmatched k's contribute m - n more
    have h_unmatched_k_contrib : m > n → freeKSuccCountUpTo T' c.val.1 k hk c.val.2 ≥ m - n + 1 := by
      intro h_m_gt_n
      -- All unmatched k's are at cols < c.col (by semistandardness, k's come before (k+1)'s)
      -- They all become (k+1)'s in T', contributing m - n to freeKSuccCountUpTo T' c.col.
      -- Plus c itself contributes 1.
      
      -- Define sets
      let unmatchedK_set : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
        {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ isUnmatchedFreeK T k hk d}
      let c_set : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := {c}
      let LHS_set : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
        {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ T' d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk d}
      
      -- unmatchedK_set ∪ c_set ⊆ LHS_set
      have h_subset : unmatchedK_set ∪ c_set ⊆ LHS_set := by
        intro d hd
        rcases hd with ⟨hd_row, hd_col, hunmatched_d⟩ | hd_eq_c
        · -- d is unmatched k in T at cols ≤ c.col
          have hT'd := benderKnuth_unmatched_k' k hk T hT d hunmatched_d
          have hfree_d := unmatched_k_becomes_free_kSucc' k hk T hT d hunmatched_d
          exact ⟨hd_row, hd_col, hT'd, hfree_d⟩
        · -- d = c
          rw [Set.mem_singleton_iff] at hd_eq_c
          rw [hd_eq_c]
          have hT'c := benderKnuth_matched_kSucc' k hk T hT c hval hfree hmatched
          have hfree' : ¬isForcedKSucc T' k hk c := by
            intro hforced'
            obtain ⟨_, c_above, h_col, h_row, hT'_above⟩ := hforced'
            have h_lt : T c_above < T c := hT.2 c_above c h_col (by simp only [Fin.lt_def]; omega)
            rw [hval] at h_lt
            have h_ne_kSucc : T c_above ≠ ⟨k.val + 1, hk⟩ := by
              intro h; rw [h] at h_lt; simp only [Fin.lt_def] at h_lt; omega
            by_cases h_eq_k : T c_above = k
            · exact hfree ⟨hval, c_above, h_col, h_row, h_eq_k⟩
            · have hT'_eq : T' c_above = T c_above := benderKnuth_unchanged' k hk T hT c_above h_eq_k h_ne_kSucc
              rw [hT'_eq] at hT'_above
              exact h_eq_k hT'_above
          exact ⟨rfl, le_refl _, hT'c, hfree'⟩
      
      -- unmatchedK_set and c_set are disjoint (c is a (k+1), not a k)
      have h_disj : Disjoint unmatchedK_set c_set := by
        rw [Set.disjoint_iff]
        intro d ⟨⟨_, _, hunmatched_d⟩, hd_eq_c⟩
        rw [Set.mem_singleton_iff] at hd_eq_c
        rw [hd_eq_c] at hunmatched_d
        have h_k := hunmatched_d.1
        rw [hval] at h_k
        simp only [Fin.ext_iff] at h_k; omega
      
      -- |unmatchedK_set| = m - n (all unmatched k's are at cols ≤ c.col by semistandardness)
      have h_unmatchedK_card : unmatchedK_set.ncard = m - n := by
        -- All unmatched k's are at cols < c.col (since c is a (k+1) and k's come before (k+1)'s)
        have h_all_unmatchedK : ∀ d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu},
            d.val.1 = c.val.1 → isUnmatchedFreeK T k hk d → d.val.2 ≤ c.val.2 := by
          intro d hd_row hunmatched_d
          -- d is a k, c is a (k+1), by semistandardness d.col < c.col
          by_contra h_gt; push Not at h_gt
          have h_weak : T c ≤ T d := hT.1 c d hd_row.symm h_gt
          rw [hval, hunmatched_d.1] at h_weak
          simp only [Fin.le_def] at h_weak; omega
        
        have h_eq : unmatchedK_set = {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
            d.val.1 = c.val.1 ∧ isUnmatchedFreeK T k hk d} := by
          ext d
          simp only [Set.mem_ofPred_eq, unmatchedK_set]
          constructor
          · intro ⟨hrow, _, hu⟩; exact ⟨hrow, hu⟩
          · intro ⟨hrow, hu⟩; exact ⟨hrow, h_all_unmatchedK d hrow hu, hu⟩
        
        have h := unmatchedFreeK_row_card T c.val.1 k hk
        have h_min : min m n = n := Nat.min_eq_right (le_of_lt h_m_gt_n)
        rw [h_min] at h
        rw [h_eq]
        exact h
      
      -- |c_set| = 1
      have h_c_card : c_set.ncard = 1 := Set.ncard_singleton c
      
      -- |unmatchedK_set ∪ c_set| = m - n + 1
      have h_union_card : (unmatchedK_set ∪ c_set).ncard = m - n + 1 := by
        rw [Set.ncard_union_eq h_disj, h_unmatchedK_card, h_c_card]
      
      calc freeKSuccCountUpTo T' c.val.1 k hk c.val.2 
          = LHS_set.ncard := rfl
        _ ≥ (unmatchedK_set ∪ c_set).ncard := Set.ncard_le_ncard h_subset (Set.toFinite _)
        _ = m - n + 1 := h_union_card
    
    -- Complete the proof
    intro hunmatched'
    unfold isUnmatchedFreeKSucc at hunmatched'
    have h_le := hunmatched'.2.2
    rw [h_freeK_swap, h_freeKSucc_swap] at h_le
    -- h_le : n + freeKSuccCountUpTo T' c.col ≤ m
    by_cases h_case : m > n
    · -- Case: m > n
      have h_ge := h_unmatched_k_contrib h_case
      omega
    · -- Case: m ≤ n
      push Not at h_case
      -- n + freeKSuccCountUpTo T' c.col ≥ n + 1 > n ≥ m
      have h_ge := h_c_contributes
      omega

lemma unmatched_k_becomes_unmatched_kSucc' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hunmatched : isUnmatchedFreeK T k hk c) :
    let T' := benderKnuth k hk T hT
    T' c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk c ∧ isUnmatchedFreeKSucc T' k hk c := by
  -- First two parts from existing lemmas
  have hT'c : benderKnuth k hk T hT c = ⟨k.val + 1, hk⟩ := benderKnuth_unmatched_k' k hk T hT c hunmatched
  have hfree' : ¬isForcedKSucc (benderKnuth k hk T hT) k hk c := unmatched_k_becomes_free_kSucc' k hk T hT c hunmatched
  refine ⟨hT'c, hfree', hT'c, hfree', ?_⟩
  
  -- Third part: c is unmatched free (k+1) in T'
  -- Need: freeKCount T' + freeKSuccCountUpTo T' c.col ≤ freeKSuccCount T'
  -- 
  -- Key insight: Since c is an unmatched k, we have m > n (more k's than (k+1)'s).
  -- After BK: freeKCount T' = n, freeKSuccCount T' = m
  -- freeKSuccCountUpTo T' c.col ≤ m - n (at most all unmatched k's become (k+1)'s)
  -- So: n + freeKSuccCountUpTo T' c.col ≤ n + (m - n) = m = freeKSuccCount T' ✓
  
  classical
  haveI : Fintype {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  let T' := benderKnuth k hk T hT
  let m := freeKCount T c.val.1 k hk
  let n := freeKSuccCount T c.val.1 k hk
  
  -- From hunmatched: freeKCountUpTo T c.col > n, which implies m > n
  have h_m_gt_n : m > n := by
    have h_excess := hunmatched.2.2
    have h_le := freeKCountUpTo_le_freeKCount T c.val.1 k hk c.val.2
    omega
  
  -- The count swaps after BK
  have h_freeK_swap : freeKCount T' c.val.1 k hk = n := freeKCount_benderKnuth k hk T hT c.val.1
  have h_freeKSucc_swap : freeKSuccCount T' c.val.1 k hk = m := freeKSuccCount_benderKnuth k hk T hT c.val.1
  
  -- Key: freeKSuccCountUpTo T' c.col ≤ m - n
  -- The free (k+1)'s in T' are: matched (k+1)'s from T + unmatched k's from T
  -- Total free (k+1)'s in T' = min(m,n) + (m - min(m,n)) = m (by freeKSuccCount_benderKnuth)
  -- The unmatched k's that become (k+1)'s number exactly m - n (since m > n).
  -- Since all (k+1)'s in T are at cols > c.col (c is a k), matched (k+1)'s don't contribute.
  -- So freeKSuccCountUpTo T' c.col ≤ #{unmatched k's in T} = m - n
  
  have h_kSuccUpTo_bound : freeKSuccCountUpTo T' c.val.1 k hk c.val.2 ≤ m - n := by
    -- The set of free (k+1)'s in T' at cols ≤ c.col ⊆ {unmatched k's in T at cols ≤ c.col}
    -- ⊆ {all unmatched k's in T} which has cardinality m - n
    unfold freeKSuccCountUpTo
    
    let LHS_set : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
      {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ T' d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk d}
    let unmatchedK_all : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
      {d | d.val.1 = c.val.1 ∧ isUnmatchedFreeK T k hk d}
    
    -- Show LHS_set ⊆ unmatchedK_all
    have h_subset : LHS_set ⊆ unmatchedK_all := by
      intro d ⟨hd_row, hd_col, hT'd_val, hd_free'⟩
      -- d is a free (k+1) in T' at cols ≤ c.col
      -- By freeKSucc_in_benderKnuth_iff, d was either matched (k+1) or unmatched k in T
      have h_char := (freeKSucc_in_benderKnuth_iff k hk T hT d).mp ⟨hT'd_val, hd_free'⟩
      rcases h_char with ⟨hd_val_kSucc, hd_free_orig, _⟩ | hunmatched_d
      · -- d was matched (k+1) in T, but all (k+1)'s are at cols > c.col
        exfalso
        -- d.col ≤ c.col and T d = k+1, but T c = k
        -- By semistandardness, T d ≤ T c, contradiction
        by_cases h_eq : d.val.2 = c.val.2
        · have h_d_eq_c : d = c := Subtype.ext (Prod.ext hd_row h_eq)
          rw [h_d_eq_c, hunmatched.1] at hd_val_kSucc
          simp only [Fin.ext_iff] at hd_val_kSucc; omega
        · have h_lt : d.val.2 < c.val.2 := Nat.lt_of_le_of_ne hd_col h_eq
          have h_weak : T d ≤ T c := hT.1 d c hd_row h_lt
          rw [hd_val_kSucc, hunmatched.1] at h_weak
          simp only [Fin.le_def] at h_weak; omega
      · -- d was unmatched k in T
        exact ⟨hd_row, hunmatched_d⟩
    
    -- |unmatchedK_all| = m - n (by unmatchedFreeK_row_card)
    have h_unmatchedK_card : unmatchedK_all.ncard = m - n := by
      have h := unmatchedFreeK_row_card T c.val.1 k hk
      -- h : Nat.card {c | c.val.1 = i ∧ isUnmatchedFreeK T k hk c} = m - min m n
      -- Since m > n, min m n = n, so this equals m - n
      have h_min : min m n = n := Nat.min_eq_right (le_of_lt h_m_gt_n)
      rw [h_min] at h
      exact h
    
    calc Nat.card ↑LHS_set ≤ Nat.card ↑unmatchedK_all := Nat.card_mono (Set.toFinite _) h_subset
      _ = m - n := h_unmatchedK_card
  
  -- Now complete the proof
  calc freeKCount T' c.val.1 k hk + freeKSuccCountUpTo T' c.val.1 k hk c.val.2 
      = n + freeKSuccCountUpTo T' c.val.1 k hk c.val.2 := by rw [h_freeK_swap]
    _ ≤ n + (m - n) := by omega
    _ = m := by omega
    _ = freeKSuccCount T' c.val.1 k hk := h_freeKSucc_swap.symm

/-- A free (k+1) at position c contributes to freeKSuccCountUpTo, so the count is at least 1. -/
private lemma freeKSuccCountUpTo_pos {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hval : T c = ⟨k.val + 1, hk⟩) (hfree : ¬isForcedKSucc T k hk c) :
    freeKSuccCountUpTo T c.val.1 k hk c.val.2 ≥ 1 := by
  unfold freeKSuccCountUpTo
  -- c itself is in the counted set
  have h_c_in : c ∈ {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
      d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} := 
    ⟨rfl, le_refl _, hval, hfree⟩
  haveI : Finite {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
    Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
  have h_nonempty' : Nonempty {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} // 
      d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} :=
    ⟨⟨c, h_c_in⟩⟩
  haveI h_finite' : Finite {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} // 
      d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} :=
    (Set.toFinite _).to_subtype
  exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨h_nonempty', h_finite'⟩)

/-- Helper lemma: After BK, freeKCountUpTo in T' is at least freeKCount T + freeKSuccCountUpTo T.
    
    This holds because:
    - All matched free k's in T stay as free k's in T' (by matched_k_stays_matched')
    - All unmatched free (k+1)'s in T at columns ≤ c.col become free k's in T'
    - In a semistandard tableau, all k's are at columns < all (k+1)'s
    - So all m free k's are at columns < c.col (since c is a (k+1))
    - The j unmatched free (k+1)'s at columns ≤ c.col become k's
    - Therefore freeKCountUpTo T' c.col ≥ m + j
    
    Note: The hypothesis `h_cnt_pos` (cnt > 0) ensures there's a free (k+1) at column ≤ j,
    which by semistandardness forces all free k's to be at columns ≤ j. This is essential
    for the proof. In the actual usage (unmatched_kSucc_becomes_unmatched_k'), j is the
    column of an unmatched free (k+1), so cnt ≥ 1 is always satisfied. -/
private lemma freeKCountUpTo_after_BK_ge {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T) (i : Fin N) (j : ℕ)
    (h_unmatched_bound : freeKCount T i k hk + freeKSuccCountUpTo T i k hk j ≤ freeKSuccCount T i k hk)
    (h_cnt_pos : freeKSuccCountUpTo T i k hk j > 0) :
    freeKCountUpTo (benderKnuth k hk T hT) i k hk j ≥ freeKCount T i k hk + freeKSuccCountUpTo T i k hk j := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  let T' := benderKnuth k hk T hT
  
  -- Abbreviations
  let m := freeKCount T i k hk
  let cnt := freeKSuccCountUpTo T i k hk j
  let n := freeKSuccCount T i k hk
  
  -- Step 1: All free (k+1)'s at cols ≤ j are unmatched
  have h_all_kSucc_unmatched : ∀ c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu},
      c.val.1 = i → c.val.2 ≤ j → T c = ⟨k.val + 1, hk⟩ → ¬isForcedKSucc T k hk c → 
      isUnmatchedFreeKSucc T k hk c := by
    intro c hrow hcol hval hfree
    unfold isUnmatchedFreeKSucc
    refine ⟨hval, hfree, ?_⟩
    have h_mono : freeKSuccCountUpTo T i k hk c.val.2 ≤ freeKSuccCountUpTo T i k hk j := 
      freeKSuccCountUpTo_mono T i k hk c.val.2 j hcol
    calc freeKCount T c.val.1 k hk + freeKSuccCountUpTo T c.val.1 k hk c.val.2 
        = freeKCount T i k hk + freeKSuccCountUpTo T i k hk c.val.2 := by rw [hrow]
      _ ≤ freeKCount T i k hk + freeKSuccCountUpTo T i k hk j := by omega
      _ ≤ freeKSuccCount T i k hk := h_unmatched_bound
      _ = freeKSuccCount T c.val.1 k hk := by rw [hrow]
  
  -- Step 2: When cnt > 0, all free k's are at cols ≤ j (by semistandardness)
  have h_all_freeK_at_cols_le_j : cnt > 0 → 
      ∀ c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu},
      c.val.1 = i → T c = k → ¬isForcedK T k hk c → c.val.2 ≤ j := by
    intro hcnt_pos c hrow hval hfree
    -- There exists a free (k+1) at some col ≤ j
    have h_exists : ∃ d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu},
        d.val.1 = i ∧ d.val.2 ≤ j ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d := by
      by_contra h_not_exists
      push Not at h_not_exists
      have h_cnt_zero : cnt = 0 := by
        show freeKSuccCountUpTo T i k hk j = 0
        unfold freeKSuccCountUpTo
        rw [Nat.card_eq_zero]
        left; rw [isEmpty_subtype]
        intro d; push Not
        intro hd_row hd_col hd_val
        exact h_not_exists d hd_row hd_col hd_val
      omega
    obtain ⟨d, hd_row, hd_col, hd_val, _⟩ := h_exists
    by_contra h_gt; push Not at h_gt
    have h_col_lt : d.val.2 < c.val.2 := Nat.lt_of_le_of_lt hd_col h_gt
    have h_weak : T d ≤ T c := hT.1 d c (hd_row.trans hrow.symm) h_col_lt
    rw [hd_val, hval] at h_weak
    simp only [Fin.le_def] at h_weak; omega
  
  -- Step 3: m ≤ n, so all free k's are matched
  have h_m_le_n : m ≤ n := by omega
  have h_all_freeK_matched : ∀ c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu},
      c.val.1 = i → T c = k → ¬isForcedK T k hk c → ¬isUnmatchedFreeK T k hk c := by
    intro c hrow hval hfree hunmatched
    unfold isUnmatchedFreeK at hunmatched
    have h_gt := hunmatched.2.2
    have h_le := freeKCountUpTo_le_freeKCount T c.val.1 k hk c.val.2
    simp only [hrow] at h_le h_gt; omega
  
  -- Step 4: Define the sets
  let A : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ c.val.2 ≤ j ∧ isMatchedFreeK T k hk c}
  let B : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ c.val.2 ≤ j ∧ isUnmatchedFreeKSucc T k hk c}
  let LHS : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
    {c | c.val.1 = i ∧ c.val.2 ≤ j ∧ T' c = k ∧ ¬isForcedK T' k hk c}
  
  -- Step 5: A ∪ B ⊆ LHS
  have h_subset : A ∪ B ⊆ LHS := by
    intro c hc
    rcases hc with ⟨hrow, hcol, hmatched⟩ | ⟨hrow, hcol, hunmatched⟩
    · obtain ⟨hval, hfree, h_not_unmatched⟩ := hmatched
      have h := (freeK_in_benderKnuth_iff k hk T hT c).mpr (Or.inl ⟨hval, hfree, h_not_unmatched⟩)
      exact ⟨hrow, hcol, h.1, h.2⟩
    · have h := (freeK_in_benderKnuth_iff k hk T hT c).mpr (Or.inr hunmatched)
      exact ⟨hrow, hcol, h.1, h.2⟩
  
  -- Step 6: A and B are disjoint
  have h_disj : Disjoint A B := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨_, _, hmatched⟩, ⟨_, _, hunmatched⟩⟩
    have h1 : T c = k := hmatched.1
    have h2 : T c = ⟨k.val + 1, hk⟩ := hunmatched.1
    rw [h1] at h2; simp only [Fin.ext_iff] at h2; omega
  
  -- Step 7: |B| = cnt
  have h_B_card : B.ncard = cnt := by
    have h_B_eq : B = {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
        c.val.1 = i ∧ c.val.2 ≤ j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c} := by
      ext c; simp only [Set.mem_ofPred_eq, B]
      constructor
      · intro ⟨hrow, hcol, hunmatched⟩; exact ⟨hrow, hcol, hunmatched.1, hunmatched.2.1⟩
      · intro ⟨hrow, hcol, hval, hfree⟩; exact ⟨hrow, hcol, h_all_kSucc_unmatched c hrow hcol hval hfree⟩
    rw [h_B_eq]; rfl
  
  -- Step 8: Since cnt > 0 (from h_cnt_pos), all free k's are at cols ≤ j, so |A| = m
  have hcnt_pos : cnt > 0 := h_cnt_pos
  have h_A_card : A.ncard = m := by
    have h_A_eq : A = {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
        c.val.1 = i ∧ T c = k ∧ ¬isForcedK T k hk c} := by
      ext c; simp only [Set.mem_ofPred_eq, A]
      constructor
      · intro ⟨hrow, _, hmatched⟩; exact ⟨hrow, hmatched.1, hmatched.2.1⟩
      · intro ⟨hrow, hval, hfree⟩
        have hcol := h_all_freeK_at_cols_le_j hcnt_pos c hrow hval hfree
        have hmatched := h_all_freeK_matched c hrow hval hfree
        exact ⟨hrow, hcol, hval, hfree, hmatched⟩
    rw [h_A_eq]; rfl
  have h_union_card : (A ∪ B).ncard = m + cnt := by
    rw [Set.ncard_union_eq h_disj, h_A_card, h_B_card]
  calc freeKCountUpTo T' i k hk j 
      = LHS.ncard := rfl
    _ ≥ (A ∪ B).ncard := Set.ncard_le_ncard h_subset (Set.toFinite _)
    _ = m + cnt := h_union_card

/-- Helper lemma: After BK, freeKSuccCount T' = freeKCount T (per-row count swap).
    
    This holds because:
    - Free (k+1)'s in T' come from matched free (k+1)'s in T + unmatched free k's in T
    - When m ≤ n (all k's matched), unmatched free k's = 0
    - So free (k+1)'s in T' = matched free (k+1)'s in T = min(m, n) = m = freeKCount T -/
private lemma freeKSuccCount_after_BK_eq {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T) (i : Fin N)
    (h_all_k_matched : freeKCount T i k hk ≤ freeKSuccCount T i k hk) :
    freeKSuccCount (benderKnuth k hk T hT) i k hk = freeKCount T i k hk := by
  -- Let T' = benderKnuth k hk T hT
  set T' := benderKnuth k hk T hT with hT'_def
  -- Abbreviations for counts
  set m := freeKCount T i k hk with hm_def
  set n := freeKSuccCount T i k hk with hn_def
  
  -- Key observation: when m ≤ n, no free k in row i is unmatched
  -- This is because isUnmatchedFreeK requires freeKCountUpTo > freeKSuccCount
  -- But freeKCountUpTo ≤ freeKCount = m ≤ n = freeKSuccCount
  have h_no_unmatched_k : ∀ c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu},
      c.val.1 = i → ¬isUnmatchedFreeK T k hk c := by
    intro c hrow hunmatched
    have h_gt := hunmatched.2.2
    have h_le := freeKCountUpTo_le_freeKCount T c.val.1 k hk c.val.2
    rw [hrow] at h_le
    rw [hrow] at h_gt
    omega
  
  -- Step 1: Show the set equality
  -- Free (k+1)'s in T' = {c | c.row = i ∧ T' c = k+1 ∧ ¬isForcedKSucc T' k hk c}
  -- We show this equals {c | c.row = i ∧ isMatchedFreeKSucc T k hk c}
  
  have h_set_eq : {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ T' c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk c} =
    {c | c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} := by
    ext c
    simp only [Set.mem_ofPred_eq]
    constructor
    · -- Forward direction: free (k+1) in T' → matched free (k+1) in T
      intro ⟨hrow, hT'c, hfree'⟩
      -- Analyze T' c = k+1 using the definition of benderKnuth
      rw [hT'_def] at hT'c
      unfold benderKnuth at hT'c
      split_ifs at hT'c with h_unmatched_k h_unmatched_kSucc
      · -- Case: c was unmatched free k in T, became k+1
        -- But h_no_unmatched_k says this is impossible in row i
        exact absurd h_unmatched_k (h_no_unmatched_k c hrow)
      · -- Case: c was unmatched free (k+1) in T, became k
        -- But T' c = k+1, not k, contradiction
        simp only [Fin.ext_iff] at hT'c
        omega
      · -- Case: T c = T' c = k+1 (unchanged)
        refine ⟨hrow, hT'c, ?_, ?_⟩
        · -- ¬isForcedKSucc T k hk c
          intro hforced
          have hforced' : isForcedKSucc T' k hk c := forced_kSucc_preserved' k hk T hT c hforced
          exact hfree' hforced'
        · -- ¬isUnmatchedFreeKSucc T k hk c
          exact h_unmatched_kSucc
    · -- Backward direction: matched free (k+1) in T → free (k+1) in T'
      intro ⟨hrow, hmatched⟩
      unfold isMatchedFreeKSucc at hmatched
      obtain ⟨hTc, hfree, h_not_unmatched⟩ := hmatched
      refine ⟨hrow, ?_, ?_⟩
      · -- T' c = k+1
        rw [hT'_def]
        exact benderKnuth_matched_kSucc' k hk T hT c hTc hfree h_not_unmatched
      · -- ¬isForcedKSucc T' k hk c
        intro hforced'
        obtain ⟨_, c_above, h_col, h_row_above, hT'_above⟩ := hforced'
        -- T' c_above = k, analyze using benderKnuth definition
        rw [hT'_def] at hT'_above
        unfold benderKnuth at hT'_above
        split_ifs at hT'_above with h_unmatched_k_above h_unmatched_kSucc_above
        · -- c_above was unmatched free k, became k+1, not k
          simp only [Fin.ext_iff] at hT'_above
          omega
        · -- c_above was unmatched free (k+1), became k
          -- But T c_above = k+1, and by column-strictness T c_above < T c = k+1
          -- This is a contradiction
          have h_above_kSucc := h_unmatched_kSucc_above.1
          have h_lt : T c_above < T c := hT.2 c_above c h_col (by simp only [Fin.lt_def]; omega)
          rw [hTc, h_above_kSucc] at h_lt
          simp only [Fin.lt_def] at h_lt
          omega
        · -- T c_above = k (unchanged), so c was forced in T
          have hforced : isForcedKSucc T k hk c := ⟨hTc, c_above, h_col, h_row_above, hT'_above⟩
          exact hfree hforced
  
  -- Step 2: Count matched free (k+1)'s = m
  -- This uses the partition: free (k+1)'s = matched ∪ unmatched
  -- And the fact that #{unmatched free (k+1)'s} = n - min(m, n) = n - m when m ≤ n
  -- So #{matched free (k+1)'s} = n - (n - m) = m
  
  have h_matched_kSucc_eq_m : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} = m := by
    classical
    haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
    
    -- Partition: free (k+1)'s = matched ∪ unmatched
    have h_partition : {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
        c.val.1 = i ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c} =
      {c | c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} ∪ 
      {c | c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · intro ⟨hrow, hTc, hfree⟩
        by_cases h : isUnmatchedFreeKSucc T k hk c
        · right; exact ⟨hrow, h⟩
        · left; exact ⟨hrow, hTc, hfree, h⟩
      · intro h
        rcases h with ⟨hrow, hmatched⟩ | ⟨hrow, hunmatched⟩
        · exact ⟨hrow, hmatched.1, hmatched.2.1⟩
        · exact ⟨hrow, hunmatched.1, hunmatched.2.1⟩
    
    have h_disjoint : Disjoint 
      {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | c.val.1 = i ∧ isMatchedFreeKSucc T k hk c}
      {c | c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} := by
      rw [Set.disjoint_iff]
      intro c ⟨⟨_, hmatched⟩, ⟨_, hunmatched⟩⟩
      exact hmatched.2.2 hunmatched
    
    -- Finiteness
    have hfin_matched : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
        c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} := Set.toFinite _
    have hfin_unmatched : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
        c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} := Set.toFinite _
    
    haveI : Fintype {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
        c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} := hfin_matched.fintype
    haveI : Fintype {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
        c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} := hfin_unmatched.fintype
    haveI : Fintype ({c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
        c.val.1 = i ∧ isMatchedFreeKSucc T k hk c} ∪ 
      {c | c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} : Set _) := 
      (hfin_matched.union hfin_unmatched).fintype
    
    -- #{free (k+1)'s} = n
    have h_free_card : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
        c.val.1 = i ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c} = n := rfl
    
    -- #{unmatched free (k+1)'s} = n - m (when m ≤ n)
    -- A free (k+1) at c is unmatched iff m + freeKSuccCountUpTo(c) ≤ n
    -- The j-th free (k+1) has freeKSuccCountUpTo = j
    -- So unmatched iff j ≤ n - m, giving exactly n - m unmatched
    have h_unmatched_card : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
        c.val.1 = i ∧ isUnmatchedFreeKSucc T k hk c} = n - m := by
      -- Use unmatchedFreeKSucc_row_card which gives:
      -- #{unmatched free (k+1)'s} = n - min(m, n)
      -- Since m ≤ n (h_all_k_matched), min(m, n) = m, so this equals n - m
      rw [unmatchedFreeKSucc_row_card T i k hk]
      -- Now need: n - min m n = n - m
      rw [← hm_def, ← hn_def, Nat.min_eq_left h_all_k_matched]
    
    -- Compute: #{matched} = #{free} - #{unmatched} = n - (n - m) = m
    rw [h_partition] at h_free_card
    rw [Nat.card_eq_card_toFinset, Set.toFinset_union,
        Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr h_disjoint)] at h_free_card
    simp only [Nat.card_eq_card_toFinset] at h_free_card h_unmatched_card
    -- h_free_card : #{matched} + #{unmatched} = n
    -- h_unmatched_card : #{unmatched} = n - m
    -- Therefore #{matched} = n - (n - m) = m (since m ≤ n)
    -- Use Fintype.card instead of Nat.card for omega
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_eq_nat_card, Nat.card_eq_card_toFinset]
    omega
  
  -- Step 3: Use the set equality and count
  unfold freeKSuccCount
  have h_card_eq : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // 
      c.val.1 = i ∧ T' c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk c} =
    Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ T' c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk c} := by
    congr 1
  rw [h_card_eq, h_set_eq, h_matched_kSucc_eq_m]

lemma unmatched_kSucc_becomes_unmatched_k' {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hunmatched : isUnmatchedFreeKSucc T k hk c) :
    let T' := benderKnuth k hk T hT
    T' c = k ∧ ¬isForcedK T' k hk c ∧ isUnmatchedFreeK T' k hk c := by
  -- First two parts from existing lemmas
  have hT'c : benderKnuth k hk T hT c = k := benderKnuth_unmatched_kSucc' k hk T hT c hunmatched
  have hfree' : ¬isForcedK (benderKnuth k hk T hT) k hk c := unmatched_kSucc_becomes_free_k' k hk T hT c hunmatched
  -- Third part: c is unmatched free k in T'
  -- This requires: T' c = k ∧ ¬isForcedK T' k hk c ∧ freeKCountUpTo T' > freeKSuccCount T'
  refine ⟨hT'c, hfree', hT'c, hfree', ?_⟩
  -- Need: freeKCountUpTo T' c.val.1 k hk c.val.2 > freeKSuccCount T' c.val.1 k hk
  --
  -- Let m = freeKCount T c.row, n = freeKSuccCount T c.row, cnt = freeKSuccCountUpTo T c.row c.col
  -- From hunmatched.2.2: m + cnt ≤ n, which implies m ≤ n (all k's are matched)
  -- From freeKSuccCountUpTo_pos: cnt ≥ 1
  --
  -- By freeKCountUpTo_after_BK_ge: freeKCountUpTo T' c.col ≥ m + cnt
  -- By freeKSuccCount_after_BK_eq: freeKSuccCount T' = m
  -- Therefore: freeKCountUpTo T' c.col ≥ m + cnt > m = freeKSuccCount T' (since cnt ≥ 1)
  have hj_pos : freeKSuccCountUpTo T c.val.1 k hk c.val.2 ≥ 1 := 
    freeKSuccCountUpTo_pos T k hk c hunmatched.1 hunmatched.2.1
  have h_unmatched_bound : freeKCount T c.val.1 k hk + freeKSuccCountUpTo T c.val.1 k hk c.val.2 ≤ 
      freeKSuccCount T c.val.1 k hk := hunmatched.2.2
  have h_m_le_n : freeKCount T c.val.1 k hk ≤ freeKSuccCount T c.val.1 k hk := by omega
  have h_ge := freeKCountUpTo_after_BK_ge k hk T hT c.val.1 c.val.2 h_unmatched_bound (by omega : freeKSuccCountUpTo T c.val.1 k hk c.val.2 > 0)
  have h_eq := freeKSuccCount_after_BK_eq k hk T hT c.val.1 h_m_le_n
  omega



/-- Row-weak preservation for Bender-Knuth: T' c₁ ≤ T' c₂ when c₁.col < c₂.col in the same row.

    The key insight is:
    
    - Unmatched free k's are the RIGHTMOST free k's (when a > b)
    - Unmatched free (k+1)'s are the LEFTMOST free (k+1)'s (when b > a)
    
    After BK:
    - Rightmost k's become k+1 (moving to the right of remaining k's)
    - Leftmost (k+1)'s become k (moving to the left of remaining (k+1)'s)
    
    This preserves row-weak ordering because the new k's are to the LEFT of remaining (k+1)'s.
    
    **Proof strategy:**
    Case analysis on what T c₁ and T c₂ are, using:
    1. `not_unmatched_k_and_unmatched_kSucc`: Can't have unmatched k left of unmatched k+1
    2. `matched_k_propagates_left`: If c₂ is matched k, then c₁ (to the left) is also matched
    3. `matched_kSucc_propagates_right`: If c₁ is matched k+1, then c₂ (to the right) is also matched -/
lemma benderKnuth_row_weak {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (h_col : c₁.val.2 < c₂.val.2) :
    benderKnuth k hk T hT c₁ ≤ benderKnuth k hk T hT c₂ := by
  have hT_weak : T c₁ ≤ T c₂ := hT.1 c₁ c₂ h_row h_col
  unfold benderKnuth
  -- Case analysis on whether c₁ is unmatched k
  by_cases h1 : isUnmatchedFreeK T k hk c₁
  · -- c₁ is unmatched k → T' c₁ = k+1
    simp only [h1, ↓reduceIte]
    by_cases h2 : isUnmatchedFreeK T k hk c₂
    · -- c₂ is also unmatched k → T' c₂ = k+1
      simp only [h2, ↓reduceIte]
      exact le_refl _
    · simp only [h2, ↓reduceIte]
      by_cases h3 : isUnmatchedFreeKSucc T k hk c₂
      · -- c₂ is unmatched k+1 → contradiction by not_unmatched_k_and_unmatched_kSucc
        exfalso
        exact not_unmatched_k_and_unmatched_kSucc T k hk c₁ c₂ h_row h_col h1 h3
      · -- c₂ is neither unmatched k nor unmatched k+1 → T' c₂ = T c₂
        simp only [h3, ↓reduceIte]
        -- Need: k+1 ≤ T c₂
        -- Since c₁ is unmatched k, T c₁ = k, so k ≤ T c₂
        have hT1 : T c₁ = k := h1.1
        rw [hT1] at hT_weak
        -- If T c₂ = k, then c₂ is free k (not unmatched), so by matched_k_propagates_left,
        -- c₁ would also be not unmatched, contradiction.
        by_cases hT2k : T c₂ = k
        · -- T c₂ = k, c₂ is not unmatched k
          -- c₂ is either forced k or matched free k
          by_cases hf2 : isForcedK T k hk c₂
          · -- c₂ is forced k → c₁ is also forced k → contradiction
            exfalso
            -- c₁ is unmatched free k, so T c₁ = k and c₁ is not forced
            have h_not_forced : ¬isForcedK T k hk c₁ := h1.2.1
            -- By row_forced_propagates_left logic (inlined):
            -- c₂ is forced k means there's a cell below c₂ with value k+1
            obtain ⟨_, c₂_below, hc₂b_col, hc₂b_row, hc₂b_ksucc⟩ := hf2
            have hi : c₁.val.1.val + 1 < N := by
              have := c₂_below.val.1.isLt
              have heq : c₁.val.1.val = c₂.val.1.val := by simp only [Fin.ext_iff] at h_row; exact h_row
              rw [heq]; omega
            have h_c₁b_mem : (⟨c₁.val.1.val + 1, hi⟩, c₁.val.2) ∈ skewYoungDiagram lam mu := by
              apply skewYoungDiagram_cell_below_exists' hmu c₁.val.1 hi c₁.val.2 c₂.val.2 h_col c₁.prop
              convert c₂_below.prop using 1
              ext
              · simp only [Fin.ext_iff] at h_row ⊢; omega
              · simp only [hc₂b_col]
            let c₁_below : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
              ⟨(⟨c₁.val.1.val + 1, hi⟩, c₁.val.2), h_c₁b_mem⟩
            have h_row_weak : T c₁_below ≤ T c₂_below := by
              apply hT.1 c₁_below c₂_below
              · simp only [c₁_below, Fin.ext_iff] at h_row ⊢; omega
              · simp only [c₁_below, hc₂b_col]; exact h_col
            rw [hc₂b_ksucc] at h_row_weak
            have h_col_strict : T c₁ < T c₁_below := by
              apply hT.2 c₁ c₁_below
              · simp only [c₁_below]
              · simp only [c₁_below, Fin.lt_def]; omega
            rw [hT1] at h_col_strict
            have h_c₁b_ksucc : T c₁_below = ⟨k.val + 1, hk⟩ := by
              apply Fin.ext
              have h1' : k.val < (T c₁_below).val := h_col_strict
              have h2' : (T c₁_below).val ≤ k.val + 1 := h_row_weak
              simp only; omega
            have h_c₁_forced : isForcedK T k hk c₁ := ⟨hT1, c₁_below, rfl, rfl, h_c₁b_ksucc⟩
            exact h_not_forced h_c₁_forced
          · -- c₂ is matched free k
            exfalso
            have hT1_free : ¬isForcedK T k hk c₁ := h1.2.1
            have h_c₁_not_unmatched := matched_k_propagates_left T hT k hk c₁ c₂ h_row h_col 
                      ⟨hT1, hT1_free⟩ ⟨hT2k, hf2⟩ (fun h => h2 h)
            exact h_c₁_not_unmatched h1
        · -- T c₂ ≠ k, so T c₂ > k (since k ≤ T c₂), so T c₂ ≥ k+1
          simp only [Fin.le_def] at hT_weak ⊢
          have hne : (T c₂).val ≠ k.val := by
            intro heq; apply hT2k; exact Fin.ext heq
          omega
  · -- c₁ is not unmatched k
    simp only [h1, ↓reduceIte]
    by_cases h2 : isUnmatchedFreeKSucc T k hk c₁
    · -- c₁ is unmatched k+1 → T' c₁ = k
      simp only [h2, ↓reduceIte]
      by_cases h3 : isUnmatchedFreeK T k hk c₂
      · -- c₂ is unmatched k → T' c₂ = k+1
        simp only [h3, ↓reduceIte]
        simp only [Fin.le_def]; omega
      · simp only [h3, ↓reduceIte]
        by_cases h4 : isUnmatchedFreeKSucc T k hk c₂
        · -- c₂ is also unmatched k+1 → T' c₂ = k
          simp only [h4, ↓reduceIte]
          exact le_refl _
        · -- c₂ is neither → T' c₂ = T c₂
          simp only [h4, ↓reduceIte]
          -- Need: k ≤ T c₂
          have hT1 : T c₁ = ⟨k.val + 1, hk⟩ := h2.1
          rw [hT1] at hT_weak
          simp only [Fin.le_def] at hT_weak ⊢
          omega
    · -- c₁ is neither unmatched k nor unmatched k+1 → T' c₁ = T c₁
      simp only [h2, ↓reduceIte]
      by_cases h3 : isUnmatchedFreeK T k hk c₂
      · -- c₂ is unmatched k → T' c₂ = k+1
        simp only [h3, ↓reduceIte]
        have hT2 : T c₂ = k := h3.1
        rw [hT2] at hT_weak
        simp only [Fin.le_def] at hT_weak ⊢
        omega
      · simp only [h3, ↓reduceIte]
        by_cases h4 : isUnmatchedFreeKSucc T k hk c₂
        · -- c₂ is unmatched k+1 → T' c₂ = k
          simp only [h4, ↓reduceIte]
          -- Need: T c₁ ≤ k
          have hT2 : T c₂ = ⟨k.val + 1, hk⟩ := h4.1
          rw [hT2] at hT_weak
          -- If T c₁ = k+1, then c₁ is free k+1 (not unmatched)
          -- By contrapositive of matched_kSucc_propagates_left, if c₁ is not unmatched k+1
          -- and c₂ IS unmatched k+1, then c₁ must be forced k+1.
          by_cases hT1k1 : T c₁ = ⟨k.val + 1, hk⟩
          · -- T c₁ = k+1, c₁ is not unmatched k+1
            by_cases hf1 : isForcedKSucc T k hk c₁
            · -- c₁ is forced k+1 → c₂ is also forced k+1 → contradiction
              exfalso
              -- c₂ is unmatched free k+1, so T c₂ = k+1 and c₂ is not forced
              have h_not_forced : ¬isForcedKSucc T k hk c₂ := h4.2.1
              -- By row_forcedKSucc_propagates_right logic (inlined):
              -- c₁ is forced k+1 means there's a cell above c₁ with value k
              obtain ⟨_, c₁_above, hc₁a_col, hc₁a_row, hc₁a_k⟩ := hf1
              have hi : 0 < c₂.val.1.val := by
                have heq : c₂.val.1.val = c₁.val.1.val := by simp only [Fin.ext_iff] at h_row; exact h_row.symm
                rw [heq]; omega
              have h_c₂a_mem : ((⟨c₂.val.1.val - 1, by omega⟩ : Fin N), c₂.val.2) ∈ skewYoungDiagram lam mu := by
                -- Use partition property: if (row, col₂) and (row-1, col₁) are in diagram with col₁ < col₂,
                -- then (row-1, col₂) is also in diagram
                have hc₂_prop := c₂.prop
                have hc₁a_prop := c₁_above.prop
                simp only [skewYoungDiagram, Set.mem_ofPred_eq] at hc₂_prop hc₁a_prop ⊢
                constructor
                · -- mu (row-1) ≤ c₂.col
                  -- We have c₁_above at (row-1, c₁.col) is in diagram, so mu(row-1) ≤ c₁.col
                  -- And c₁.col < c₂.col (from h_col)
                  have h_c₁a_row : c₁_above.val.1.val + 1 = c₁.val.1.val := hc₁a_row
                  have h_c₁a_col : c₁_above.val.2 = c₁.val.2 := hc₁a_col
                  have h_eq : c₁.val.1.val = c₂.val.1.val := by simp only [Fin.ext_iff] at h_row; exact h_row
                  -- c₁_above.row = c₁.row - 1 = c₂.row - 1
                  have h_row_eq : c₁_above.val.1.val = c₂.val.1.val - 1 := by omega
                  -- mu (c₂.row - 1) ≤ c₁_above.col = c₁.col < c₂.col
                  have hmu_le : mu ⟨c₂.val.1.val - 1, by omega⟩ ≤ c₁_above.val.2 := by
                    have h_fin_eq : (⟨c₂.val.1.val - 1, by omega⟩ : Fin N) = c₁_above.val.1 := by
                      ext
                      simp only
                      omega
                    rw [h_fin_eq]
                    exact le_of_lt hc₁a_prop.1
                  omega
                · -- c₂.col < lam (row-1)
                  -- We have c₂.col < lam(row) and lam is weakly decreasing
                  have hlam_le : lam c₂.val.1 ≤ lam ⟨c₂.val.1.val - 1, by omega⟩ := by
                    apply hlam ⟨c₂.val.1.val - 1, by omega⟩ c₂.val.1
                    simp only [Fin.le_def]; omega
                  omega
              let c₂_above : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
                ⟨(⟨c₂.val.1.val - 1, by omega⟩, c₂.val.2), h_c₂a_mem⟩
              have h_row_weak : T c₁_above ≤ T c₂_above := by
                apply hT.1 c₁_above c₂_above
                · have heq : c₁.val.1.val = c₂.val.1.val := by
                    simp only [Fin.ext_iff] at h_row
                    exact h_row
                  simp only [c₂_above, Fin.ext_iff]
                  omega
                · simp only [c₂_above]; rw [hc₁a_col]; exact h_col
              rw [hc₁a_k] at h_row_weak
              have h_col_strict : T c₂_above < T c₂ := by
                apply hT.2 c₂_above c₂
                · simp only [c₂_above]
                · simp only [c₂_above, Fin.lt_def]; omega
              rw [h4.1] at h_col_strict
              have h_c₂a_k : T c₂_above = k := by
                apply Fin.ext
                have h1' : k.val ≤ (T c₂_above).val := h_row_weak
                have h2' : (T c₂_above).val < k.val + 1 := h_col_strict
                omega
              have h_c₂_forced : isForcedKSucc T k hk c₂ := ⟨h4.1, c₂_above, rfl, by simp only [c₂_above]; omega, h_c₂a_k⟩
              exact h_not_forced h_c₂_forced
            · -- c₁ is matched free k+1
              -- By the structure of unmatched k+1's (leftmost free k+1's are unmatched),
              -- if c₁ is matched free k+1 and c₂ is to the right, c₂ should also be matched.
              -- This uses matched_kSucc_propagates_right.
              exfalso
              have h_c₁_free_kSucc : T c₁ = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c₁ := ⟨hT1k1, hf1⟩
              have h_c₂_free_kSucc : T c₂ = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c₂ := ⟨h4.1, h4.2.1⟩
              have h_c₂_matched := matched_kSucc_propagates_right T hT k hk c₁ c₂ h_row h_col 
                        h_c₁_free_kSucc h_c₂_free_kSucc h2
              exact h_c₂_matched h4
          · -- T c₁ ≠ k+1, so T c₁ < k+1 (since T c₁ ≤ k+1), so T c₁ ≤ k
            simp only [Fin.le_def] at hT_weak ⊢
            have hne : (T c₁).val ≠ k.val + 1 := by
              intro heq; apply hT1k1; exact Fin.ext heq
            omega
        · -- c₂ is neither → T' c₂ = T c₂
          simp only [h4, ↓reduceIte]
          exact hT_weak

/-- Column-strict preservation for Bender-Knuth involution.
    
    This lemma proves that BK preserves column-strict ordering when lam and mu are N-partitions.
    The key insight is that if T c₁ = k and T c₂ = k+1 in the same column with c₁.row < c₂.row,
    then by the partition property (columns are contiguous), c₁ and c₂ must be adjacent.
    Adjacent cells with k above and k+1 below form a forced pair, which is unchanged by BK.
    
    This lemma resolves the column-strict sorry in benderKnuth_involutive when partition
    hypotheses are available. -/
lemma benderKnuth_column_strict {lam mu : Fin N → ℕ} 
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_col : c₁.val.2 = c₂.val.2) (h_row : c₁.val.1 < c₂.val.1) :
    benderKnuth k hk T hT c₁ < benderKnuth k hk T hT c₂ := by
  have hT_strict : T c₁ < T c₂ := hT.2 c₁ c₂ h_col h_row
  -- The dangerous case is when T c₁ = k (unmatched) → k+1 and T c₂ = k+1 (unmatched) → k.
  -- This would give T' c₁ = k+1 > k = T' c₂, violating strict ordering.
  -- But this can't happen because if T c₁ = k and T c₂ = k+1 in the same column,
  -- they must be adjacent (by partition property via adjacent_k_kSucc_in_column),
  -- making them a forced pair (k above k+1), which is unchanged by BK.
  unfold benderKnuth
  by_cases h1 : isUnmatchedFreeK T k hk c₁
  · -- c₁ is unmatched k → T' c₁ = k+1
    simp only [h1, ↓reduceIte]
    by_cases h2 : isUnmatchedFreeK T k hk c₂
    · -- c₂ is also unmatched k → T' c₂ = k+1, same value, contradiction
      simp only [h2, ↓reduceIte]
      -- Goal: ⟨k.val + 1, hk⟩ < ⟨k.val + 1, hk⟩, which is impossible
      -- But we can also derive contradiction from hT_strict: T c₁ < T c₂ with T c₁ = T c₂ = k
      have hT1 : T c₁ = k := h1.1
      have hT2 : T c₂ = k := h2.1
      rw [hT1, hT2] at hT_strict
      exact absurd hT_strict (lt_irrefl k)
    · simp only [h2, ↓reduceIte]
      by_cases h3 : isUnmatchedFreeKSucc T k hk c₂
      · -- c₂ is unmatched k+1 → T' c₂ = k
        -- T' c₁ = k+1 > k = T' c₂, this would be bad!
        -- But this case is impossible: T c₁ = k and T c₂ = k+1 in same column
        -- means they're adjacent (by partition property), so both are forced.
        simp only [h3, ↓reduceIte]
        exfalso
        have hT1 : T c₁ = k := h1.1
        have hT2 : T c₂ = ⟨k.val + 1, hk⟩ := h3.1
        have h_adj := adjacent_k_kSucc_in_column hlam hmu T hT k hk c₁ c₂ h_col h_row hT1 hT2
        -- c₁ being adjacent to c₂ with T c₂ = k+1 means c₁ is forced (k+1 directly below)
        -- This contradicts h1.2.1 (c₁ is not forced)
        have hi : c₁.val.1.val + 1 < N := by have := c₂.val.1.isLt; omega
        have h_c₂_row : c₂.val.1 = ⟨c₁.val.1.val + 1, hi⟩ := by ext; exact h_adj.symm
        have h_c₁_forced : isForcedK T k hk c₁ := by
          refine ⟨hT1, c₂, ?_, ?_, hT2⟩
          · exact h_col.symm
          · simp only [h_c₂_row]
        exact h1.2.1 h_c₁_forced
      · -- c₂ is neither unmatched k nor unmatched k+1 → T' c₂ = T c₂
        simp only [h3, ↓reduceIte]
        have hT1 : T c₁ = k := h1.1
        rw [hT1] at hT_strict
        -- We need to show k+1 < T c₂. We know k < T c₂.
        -- If T c₂ = k+1, then c₂ would be unmatched k+1 (since c₂ is not unmatched k by h2,
        -- and if c₂ were forced k+1, then c₁ would be forced k, contradicting h1).
        -- But h3 says c₂ is not unmatched k+1, so T c₂ ≠ k+1.
        -- Therefore T c₂ > k+1.
        simp only [Fin.lt_def] at hT_strict ⊢
        by_cases hT2 : T c₂ = ⟨k.val + 1, hk⟩
        · -- T c₂ = k+1, c₂ is not unmatched k+1 (by h3)
          -- c₂ must be forced k+1, so there's a k above c₂
          -- But c₁ is directly above c₂ (by column-strict adjacency) with T c₁ = k
          -- So c₁ is forced k, contradicting h1.2.1
          exfalso
          have h_adj := adjacent_k_kSucc_in_column hlam hmu T hT k hk c₁ c₂ h_col h_row hT1 hT2
          have hi : c₁.val.1.val + 1 < N := by have := c₂.val.1.isLt; omega
          have h_c₂_row : c₂.val.1 = ⟨c₁.val.1.val + 1, hi⟩ := by ext; exact h_adj.symm
          have h_c₁_forced : isForcedK T k hk c₁ := by
            refine ⟨hT1, c₂, ?_, ?_, hT2⟩
            · exact h_col.symm
            · simp only [h_c₂_row]
          exact h1.2.1 h_c₁_forced
        · have hne : (T c₂).val ≠ k.val + 1 := fun heq => hT2 (Fin.ext heq)
          omega
  · -- c₁ is not unmatched k
    simp only [h1, ↓reduceIte]
    by_cases h2 : isUnmatchedFreeKSucc T k hk c₁
    · -- c₁ is unmatched k+1 → T' c₁ = k
      simp only [h2, ↓reduceIte]
      by_cases h3 : isUnmatchedFreeK T k hk c₂
      · -- c₂ is unmatched k → T' c₂ = k+1
        simp only [h3, ↓reduceIte]
        simp only [Fin.lt_def]; omega
      · simp only [h3, ↓reduceIte]
        by_cases h4 : isUnmatchedFreeKSucc T k hk c₂
        · -- c₂ is also unmatched k+1 → T' c₂ = k, same value
          simp only [h4, ↓reduceIte]
          have hT1 : T c₁ = ⟨k.val + 1, hk⟩ := h2.1
          have hT2 : T c₂ = ⟨k.val + 1, hk⟩ := h4.1
          rw [hT1, hT2] at hT_strict
          exact absurd hT_strict (lt_irrefl _)
        · -- c₂ is neither → T' c₂ = T c₂
          simp only [h4, ↓reduceIte]
          have hT1 : T c₁ = ⟨k.val + 1, hk⟩ := h2.1
          rw [hT1] at hT_strict
          simp only [Fin.lt_def] at hT_strict ⊢
          omega
    · -- c₁ is neither unmatched k nor unmatched k+1 → T' c₁ = T c₁
      simp only [h2, ↓reduceIte]
      by_cases h3 : isUnmatchedFreeK T k hk c₂
      · -- c₂ is unmatched k → T' c₂ = k+1
        simp only [h3, ↓reduceIte]
        have hT2 : T c₂ = k := h3.1
        rw [hT2] at hT_strict
        simp only [Fin.lt_def] at hT_strict ⊢
        omega
      · simp only [h3, ↓reduceIte]
        by_cases h4 : isUnmatchedFreeKSucc T k hk c₂
        · -- c₂ is unmatched k+1 → T' c₂ = k
          simp only [h4, ↓reduceIte]
          have hT2 : T c₂ = ⟨k.val + 1, hk⟩ := h4.1
          rw [hT2] at hT_strict
          by_cases hT1k : T c₁ = k
          · -- T c₁ = k, c₁ is not unmatched k (by h1)
            -- T c₂ = k+1, c₂ is unmatched free k+1
            -- In same column, if T c₁ = k and T c₂ = k+1, they're adjacent
            -- So c₂ is forced (k above), contradicting h4.2.1
            exfalso
            have h_adj := adjacent_k_kSucc_in_column hlam hmu T hT k hk c₁ c₂ h_col h_row hT1k hT2
            have h_c₂_forced : isForcedKSucc T k hk c₂ := by
              refine ⟨hT2, c₁, h_col, ?_, hT1k⟩
              omega
            exact h4.2.1 h_c₂_forced
          · simp only [Fin.lt_def] at hT_strict ⊢
            have hne : (T c₁).val ≠ k.val := fun heq => hT1k (Fin.ext heq)
            omega
        · -- c₂ is neither → T' c₂ = T c₂
          simp only [h4, ↓reduceIte]
          exact hT_strict

theorem benderKnuth_involutive {lam mu : Fin N → ℕ} 
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T) :
    let T' := benderKnuth k hk T hT
    ∃ (hT' : IsSemistandard T'), benderKnuth k hk T' hT' = T := by
  classical
  set T' := benderKnuth k hk T hT with hT'_def
  -- Part 1: T' is semistandard
  -- The key insight: BK only swaps UNMATCHED free k ↔ UNMATCHED free k+1
  -- The parenthesis-matching ensures that swapped entries don't violate ordering
  --
  -- **Row-weak preservation**:
  -- Consider cells c₁ < c₂ in the same row. We need T'(c₁) ≤ T'(c₂).
  --
  -- The key observation is that in each row:
  -- - Unmatched free k's are the RIGHTMOST free k's (those where freeKCountUpTo > freeKSuccCount)
  -- - Unmatched free (k+1)'s are the LEFTMOST free (k+1)'s (those where freeKSuccCountUpTo > freeKCountBefore)
  --
  -- After BK, in each row:
  -- - The leftmost free (k+1)'s become k's (stay on the left)
  -- - The rightmost free k's become (k+1)'s (stay on the right)
  -- - Matched cells stay unchanged
  --
  -- So the ordering k ≤ k+1 is preserved because:
  -- - New k's (from unmatched (k+1)'s) are to the LEFT of new (k+1)'s (from unmatched k's)
  -- - This follows from the parenthesis-matching structure
  --
  -- **Column-strict preservation**:
  -- Forced pairs (k above, k+1 below) stay together and unchanged.
  -- Free cells in the same column have the same row, so the column-strict property
  -- is inherited from the original tableau.
  have hT'_ss : IsSemistandard T' := by
    constructor
    · intro c₁ c₂ h_row h_col
      exact benderKnuth_row_weak hlam hmu k hk T hT c₁ c₂ h_row h_col
    · intro c₁ c₂ h_col h_row
      exact benderKnuth_column_strict hlam hmu k hk T hT c₁ c₂ h_col h_row
  use hT'_ss
  -- Part 2: BK(BK(T)) = T
  -- The key insight: BK is an involution because the matching is symmetric
  -- An unmatched free k in T becomes an unmatched free (k+1) in T'
  -- An unmatched free (k+1) in T becomes an unmatched free k in T'
  -- Matched and forced cells are unchanged
  funext c
  -- Case analysis on the value of T c
  by_cases h1 : T c = k
  · by_cases hf1 : isForcedK T k hk c
    · -- T c = k (forced) → T' c = k (forced in T') → T'' c = k
      have hT'c : T' c = k := benderKnuth_forced_k' k hk T hT c hf1
      have hf1' : isForcedK T' k hk c := forced_k_preserved' k hk T hT c hf1
      rw [benderKnuth_forced_k' k hk T' hT'_ss c hf1', h1]
    · -- T c = k (free) - need to distinguish matched vs unmatched
      by_cases hunmatched : isUnmatchedFreeK T k hk c
      · -- Unmatched free k → T' c = k+1, and it becomes unmatched free (k+1) in T'
        have hT'c : T' c = ⟨k.val + 1, hk⟩ := benderKnuth_unmatched_k' k hk T hT c hunmatched
        have hfree' : ¬isForcedKSucc T' k hk c := unmatched_k_becomes_free_kSucc' k hk T hT c hunmatched
        -- Use the helper lemma to get that c is unmatched free (k+1) in T'
        obtain ⟨_, _, hunmatched'⟩ := unmatched_k_becomes_unmatched_kSucc' k hk T hT c hunmatched
        -- Since c is unmatched free (k+1) in T', BK swaps it back to k
        rw [benderKnuth_unmatched_kSucc' k hk T' hT'_ss c hunmatched', hunmatched.1]
      · -- Matched free k → T' c = k (unchanged)
        -- A free k that is not unmatched stays as k
        unfold benderKnuth at hT'_def
        have hT'c : T' c = k := by
          simp only [hT'_def]
          simp only [hunmatched, ↓reduceIte]
          -- Not unmatched as k, and not a (k+1), so stays as T c = k
          split_ifs with h2
          · exfalso
            have := h2.1
            rw [h1] at this
            simp only [Fin.ext_iff] at this
            omega
          · exact h1
        -- T' c = k and it should also be matched in T', so BK(T') c = k
        -- We need to show BK(T') c = k, which means c is not unmatched in T'
        -- Since T' c = k and c is not forced (forced status preserved), we need to show
        -- freeKCountUpTo T' c.val.1 k hk c.val.2 ≤ freeKSuccCount T' c.val.1 k hk
        -- This is the key counting argument: matched k's stay matched under BK
        -- The proof requires showing that the counts in T' satisfy the matching condition
        -- This follows from the symmetry of the parenthesis-matching algorithm
        unfold benderKnuth
        have h_not_unmatched_k' : ¬isUnmatchedFreeK T' k hk c := by
          -- Use matched_k_stays_matched' to show c remains matched in T'
          have hfree : ¬isForcedK T k hk c := hf1
          obtain ⟨_, _, h_matched'⟩ := matched_k_stays_matched' k hk T hT c h1 hfree hunmatched
          exact h_matched'
        have h_not_unmatched_kSucc' : ¬isUnmatchedFreeKSucc T' k hk c := by
          intro h
          have := h.1
          rw [hT'c] at this
          simp only [Fin.ext_iff] at this
          omega
        simp only [h_not_unmatched_k', h_not_unmatched_kSucc', ↓reduceIte, hT'c, h1]
  · by_cases h2 : T c = ⟨k.val + 1, hk⟩
    · by_cases hf2 : isForcedKSucc T k hk c
      · -- T c = k+1 (forced) → T' c = k+1 (forced in T') → T'' c = k+1
        have hT'c : T' c = ⟨k.val + 1, hk⟩ := benderKnuth_forced_kSucc' k hk T hT c hf2
        have hf2' : isForcedKSucc T' k hk c := forced_kSucc_preserved' k hk T hT c hf2
        rw [benderKnuth_forced_kSucc' k hk T' hT'_ss c hf2', h2]
      · -- T c = k+1 (free) - need to distinguish matched vs unmatched
        by_cases hunmatched : isUnmatchedFreeKSucc T k hk c
        · -- Unmatched free (k+1) → T' c = k, and it becomes unmatched free k in T'
          have hT'c : T' c = k := benderKnuth_unmatched_kSucc' k hk T hT c hunmatched
          have hfree' : ¬isForcedK T' k hk c := unmatched_kSucc_becomes_free_k' k hk T hT c hunmatched
          -- Use the helper lemma to get that c is unmatched free k in T'
          obtain ⟨_, _, hunmatched'⟩ := unmatched_kSucc_becomes_unmatched_k' k hk T hT c hunmatched
          -- Since c is unmatched free k in T', BK swaps it back to k+1
          rw [benderKnuth_unmatched_k' k hk T' hT'_ss c hunmatched', hunmatched.1]
        · -- Matched free (k+1) → T' c = k+1 (unchanged)
          unfold benderKnuth at hT'_def
          have hT'c : T' c = ⟨k.val + 1, hk⟩ := by
            simp only [hT'_def]
            have hne : ¬(T c = k) := by rw [h2]; simp only [Fin.ext_iff]; omega
            have h_not_unmatched_k : ¬isUnmatchedFreeK T k hk c := by
              unfold isUnmatchedFreeK; simp only [hne, false_and, not_false_eq_true]
            simp only [h_not_unmatched_k, hunmatched, ↓reduceIte, h2]
          -- T' c = k+1 and it should also be matched in T', so BK(T') c = k+1
          unfold benderKnuth
          have h_not_unmatched_k' : ¬isUnmatchedFreeK T' k hk c := by
            intro h
            have := h.1
            rw [hT'c] at this
            simp only [Fin.ext_iff] at this
            omega
          have h_not_unmatched_kSucc' : ¬isUnmatchedFreeKSucc T' k hk c := by
            -- Use matched_kSucc_stays_matched' to show c remains matched in T'
            have hfree : ¬isForcedKSucc T k hk c := hf2
            obtain ⟨_, _, h_matched'⟩ := matched_kSucc_stays_matched' k hk T hT c h2 hfree hunmatched
            exact h_matched'
          simp only [h_not_unmatched_k', h_not_unmatched_kSucc', ↓reduceIte, hT'c, h2]
    · -- T c ∉ {k, k+1} → T' c = T c → T'' c = T' c = T c
      have hT'c : T' c = T c := benderKnuth_unchanged' k hk T hT c h1 h2
      have h1' : T' c ≠ k := by rw [hT'c]; exact h1
      have h2' : T' c ≠ ⟨k.val + 1, hk⟩ := by rw [hT'c]; exact h2
      rw [benderKnuth_unchanged' k hk T' hT'_ss c h1' h2', hT'c]

/-- The Bender-Knuth involution preserves semistandardness. -/
theorem benderKnuth_semistandard {lam mu : Fin N → ℕ} 
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T) :
    IsSemistandard (benderKnuth k hk T hT) := by
  obtain ⟨hT', _⟩ := benderKnuth_involutive hlam hmu k hk T hT
  exact hT'

/-- The Bender-Knuth involution is an involution for N-partitions.
    
    This is a version of `benderKnuth_involutive` that uses the partition hypotheses
    to prove column-strict preservation via `benderKnuth_column_strict`. -/
theorem benderKnuth_involutive_partition {lam mu : Fin N → ℕ} 
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T) :
    let T' := benderKnuth k hk T hT
    ∃ (hT' : IsSemistandard T'), benderKnuth k hk T' hT' = T := by
  classical
  set T' := benderKnuth k hk T hT with hT'_def
  -- Part 1: T' is semistandard (using partition hypotheses for column-strict)
  have hT'_ss : IsSemistandard T' := by
    constructor
    · intro c₁ c₂ h_row h_col
      exact benderKnuth_row_weak hlam hmu k hk T hT c₁ c₂ h_row h_col
    · intro c₁ c₂ h_col h_row
      exact benderKnuth_column_strict hlam hmu k hk T hT c₁ c₂ h_col h_row
  use hT'_ss
  -- Part 2: BK(BK(T)) = T (same proof as benderKnuth_involutive)
  funext c
  by_cases h1 : T c = k
  · by_cases hf1 : isForcedK T k hk c
    · have hT'c : T' c = k := benderKnuth_forced_k' k hk T hT c hf1
      have hf1' : isForcedK T' k hk c := forced_k_preserved' k hk T hT c hf1
      rw [benderKnuth_forced_k' k hk T' hT'_ss c hf1', h1]
    · by_cases hunmatched : isUnmatchedFreeK T k hk c
      · have hT'c : T' c = ⟨k.val + 1, hk⟩ := benderKnuth_unmatched_k' k hk T hT c hunmatched
        have hfree' : ¬isForcedKSucc T' k hk c := unmatched_k_becomes_free_kSucc' k hk T hT c hunmatched
        obtain ⟨_, _, hunmatched'⟩ := unmatched_k_becomes_unmatched_kSucc' k hk T hT c hunmatched
        rw [benderKnuth_unmatched_kSucc' k hk T' hT'_ss c hunmatched', hunmatched.1]
      · unfold benderKnuth at hT'_def
        have hT'c : T' c = k := by
          simp only [hT'_def]
          simp only [hunmatched, ↓reduceIte]
          split_ifs with h2
          · exfalso
            have := h2.1
            rw [h1] at this
            simp only [Fin.ext_iff] at this
            omega
          · exact h1
        unfold benderKnuth
        have h_not_unmatched_k' : ¬isUnmatchedFreeK T' k hk c := by
          have hfree : ¬isForcedK T k hk c := hf1
          obtain ⟨_, _, h_matched'⟩ := matched_k_stays_matched' k hk T hT c h1 hfree hunmatched
          exact h_matched'
        have h_not_unmatched_kSucc' : ¬isUnmatchedFreeKSucc T' k hk c := by
          intro h
          have := h.1
          rw [hT'c] at this
          simp only [Fin.ext_iff] at this
          omega
        simp only [h_not_unmatched_k', h_not_unmatched_kSucc', ↓reduceIte, hT'c, h1]
  · by_cases h2 : T c = ⟨k.val + 1, hk⟩
    · by_cases hf2 : isForcedKSucc T k hk c
      · have hT'c : T' c = ⟨k.val + 1, hk⟩ := benderKnuth_forced_kSucc' k hk T hT c hf2
        have hf2' : isForcedKSucc T' k hk c := forced_kSucc_preserved' k hk T hT c hf2
        rw [benderKnuth_forced_kSucc' k hk T' hT'_ss c hf2', h2]
      · by_cases hunmatched : isUnmatchedFreeKSucc T k hk c
        · have hT'c : T' c = k := benderKnuth_unmatched_kSucc' k hk T hT c hunmatched
          have hfree' : ¬isForcedK T' k hk c := unmatched_kSucc_becomes_free_k' k hk T hT c hunmatched
          obtain ⟨_, _, hunmatched'⟩ := unmatched_kSucc_becomes_unmatched_k' k hk T hT c hunmatched
          rw [benderKnuth_unmatched_k' k hk T' hT'_ss c hunmatched', hunmatched.1]
        · unfold benderKnuth at hT'_def
          have hT'c : T' c = ⟨k.val + 1, hk⟩ := by
            simp only [hT'_def]
            have hne : ¬(T c = k) := by rw [h2]; simp only [Fin.ext_iff]; omega
            have h_not_unmatched_k : ¬isUnmatchedFreeK T k hk c := by
              unfold isUnmatchedFreeK; simp only [hne, false_and, not_false_eq_true]
            simp only [h_not_unmatched_k, hunmatched, ↓reduceIte, h2]
          unfold benderKnuth
          have h_not_unmatched_k' : ¬isUnmatchedFreeK T' k hk c := by
            intro h
            have := h.1
            rw [hT'c] at this
            simp only [Fin.ext_iff] at this
            omega
          have h_not_unmatched_kSucc' : ¬isUnmatchedFreeKSucc T' k hk c := by
            have hfree : ¬isForcedKSucc T k hk c := hf2
            obtain ⟨_, _, h_matched'⟩ := matched_kSucc_stays_matched' k hk T hT c h2 hfree hunmatched
            exact h_matched'
          simp only [h_not_unmatched_k', h_not_unmatched_kSucc', ↓reduceIte, hT'c, h2]
    · have hT'c : T' c = T c := benderKnuth_unchanged' k hk T hT c h1 h2
      have h1' : T' c ≠ k := by rw [hT'c]; exact h1
      have h2' : T' c ≠ ⟨k.val + 1, hk⟩ := by rw [hT'c]; exact h2
      rw [benderKnuth_unchanged' k hk T' hT'_ss c h1' h2', hT'c]

/-! ### Content swap proof structure

The key insight for `benderKnuth_content_swap` is:

**Decomposition of cells by type:**
- `{c | T c = k}` = `{forced k}` ⊔ `{free k}`
- `{c | T c = k+1}` = `{forced (k+1)}` ⊔ `{free (k+1)}`

**Forced pairs bijection:**
Forced k and forced (k+1) cells are in bijection: each forced k cell has a unique
(k+1) directly below it, and vice versa. So `|forced k| = |forced (k+1)|`.

**Free cell transformation by BK:**
In each row with m free k's and n free (k+1)'s:
- min(m,n) pairs are "matched" (paired by parenthesis matching)
- max(0, m-n) free k's are "unmatched" → become (k+1)
- max(0, n-m) free (k+1)'s are "unmatched" → become k
- After BK: new free k count = n, new free (k+1) count = m

**Content swap:**
```
cont(T')_k = |forced k| + |new free k|
          = |forced k| + Σ_rows (free (k+1) count in row)
          = |forced (k+1)| + |free (k+1)|
          = cont(T)_{k+1}
```
Similarly for cont(T')_{k+1} = cont(T)_k.
-/

/-- The content of BK_k(T) differs from cont(T) by swapping entries k and k+1.
    Specifically: cont(BK_k(T))_k = cont(T)_{k+1} and cont(BK_k(T))_{k+1} = cont(T)_k,
    while cont(BK_k(T))_i = cont(T)_i for i ≠ k, k+1.

    This is the key property that makes Bender-Knuth involutions useful for
    proving symmetry of Schur polynomials. -/
theorem benderKnuth_content_swap {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T) :
    let T' := benderKnuth k hk T hT
    contentTableau T' k = contentTableau T ⟨k.val + 1, hk⟩ ∧
    contentTableau T' ⟨k.val + 1, hk⟩ = contentTableau T k ∧
    ∀ i : Fin N, i ≠ k → i.val ≠ k.val + 1 → contentTableau T' i = contentTableau T i := by
  classical
  intro T'
  -- Helper lemmas for the benderKnuth characterization
  -- Note: With the corrected parenthesis-matching BK definition, the characterization is more complex.
  -- T' c = k iff c had an unmatched free (k+1) that got swapped, OR c had a k that wasn't unmatched
  -- T' c = k+1 iff c had an unmatched free k that got swapped, OR c had a (k+1) that wasn't unmatched
  have bk_eq_other : ∀ c i, i ≠ k → i.val ≠ k.val + 1 → (T' c = i ↔ T c = i) := by
    intro c i hi_ne_k hi_ne_ksucc
    show benderKnuth k hk T hT c = i ↔ T c = i
    simp only [benderKnuth]
    split_ifs with h1 h2
    · constructor
      · intro heq; simp only [Fin.ext_iff] at heq; exact absurd heq.symm hi_ne_ksucc
      · intro heq; have := h1.1; rw [this] at heq; exact absurd heq.symm hi_ne_k
    · constructor
      · intro heq; exact absurd heq.symm hi_ne_k
      · intro heq; have := h2.1; rw [this] at heq; simp only [Fin.ext_iff] at heq
        exact absurd heq.symm hi_ne_ksucc
    · rfl
  -- The content swap property: with the corrected BK, the counts of k and k+1 are swapped
  -- This is because BK swaps unmatched free k's with unmatched free (k+1)'s
  -- The number of unmatched free k's equals total free k's minus matched pairs
  -- The number of unmatched free (k+1)'s equals total free (k+1)'s minus matched pairs
  -- After swapping, the counts are exchanged
  --
  -- **Proof sketch for contentTableau T' k = contentTableau T (k+1):**
  -- We need to show #{c | T' c = k} = #{c | T c = k+1}
  --
  -- Cells where T' c = k are exactly:
  --   (A) Cells where T c = k AND c is forced k
  --   (B) Cells where T c = k AND c is matched free k
  --   (C) Cells where T c = k+1 AND c is unmatched free (k+1)
  --
  -- Cells where T c = k+1 are exactly:
  --   (A') Cells where T c = k+1 AND c is forced (k+1)
  --   (B') Cells where T c = k+1 AND c is matched free (k+1)
  --   (C') Cells where T c = k+1 AND c is unmatched free (k+1)
  --
  -- By forced_k_kSucc_bijection: #(A) = #(A')
  -- By matching definition: #(B) = #(B') (in each row, matched free k's = matched free (k+1)'s)
  -- By definition: #(C) = #(C')
  --
  -- Therefore: #{T' c = k} = #(A) + #(B) + #(C) = #(A') + #(B') + #(C') = #{T c = k+1}
  --
  -- The symmetric argument shows contentTableau T' (k+1) = contentTableau T k.
  -- The third part (other indices unchanged) follows from bk_eq_other.
  --
  -- Part 3: For i ≠ k and i.val ≠ k.val + 1, content is unchanged
  have h3 : ∀ i : Fin N, i ≠ k → i.val ≠ k.val + 1 → contentTableau T' i = contentTableau T i := by
    intro i hi_ne_k hi_ne_ksucc
    exact contentTableau_eq_of_iff T T' i (fun c => bk_eq_other c i hi_ne_k hi_ne_ksucc)
  -- Helper: isUnmatchedFreeKSucc implies T c = k+1
  have h_unmatched_kSucc_val : ∀ c, isUnmatchedFreeKSucc T k hk c → T c = ⟨k.val + 1, hk⟩ := by
    intro c h; exact h.1
  -- Helper: isUnmatchedFreeK implies T c = k
  have h_unmatched_k_val : ∀ c, isUnmatchedFreeK T k hk c → T c = k := by
    intro c h; exact h.1
  -- Decomposition of {c | T c = k+1} using the unmatched property
  have h_kSucc_decomp : {c | T c = ⟨k.val + 1, hk⟩} = 
      {c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} ∪ {c | isUnmatchedFreeKSucc T k hk c} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hTc
      by_cases h : isUnmatchedFreeKSucc T k hk c
      · right; exact h
      · left; exact ⟨hTc, h⟩
    · intro h
      rcases h with ⟨hTc, _⟩ | h_unmatched
      · exact hTc
      · exact h_unmatched_kSucc_val c h_unmatched
  -- Decomposition of {c | T c = k} using the unmatched property
  have h_k_decomp : {c | T c = k} = 
      {c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} ∪ {c | isUnmatchedFreeK T k hk c} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro hTc
      by_cases h : isUnmatchedFreeK T k hk c
      · right; exact h
      · left; exact ⟨hTc, h⟩
    · intro h
      rcases h with ⟨hTc, _⟩ | h_unmatched
      · exact hTc
      · exact h_unmatched_k_val c h_unmatched
  -- Set equality for {c | T' c = k} using benderKnuth_eq_k_iff
  have h_T'_k_set : {c | T' c = k} = 
      {c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} ∪ {c | isUnmatchedFreeKSucc T k hk c} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    exact benderKnuth_eq_k_iff k hk T hT c
  -- Set equality for {c | T' c = k+1} using benderKnuth_eq_kSucc_iff
  have h_T'_kSucc_set : {c | T' c = ⟨k.val + 1, hk⟩} = 
      {c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} ∪ {c | isUnmatchedFreeK T k hk c} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    exact benderKnuth_eq_kSucc_iff k hk T hT c
  -- Disjointness: {T c = k ∧ ¬isUnmatchedFreeK} and {isUnmatchedFreeKSucc} are disjoint
  have h_disj1 : Disjoint {c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} {c | isUnmatchedFreeKSucc T k hk c} := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨hTc, _⟩, h_unmatched⟩
    have := h_unmatched_kSucc_val c h_unmatched
    rw [hTc] at this
    simp only [Fin.ext_iff] at this
    omega
  -- Disjointness: {T c = k+1 ∧ ¬isUnmatchedFreeKSucc} and {isUnmatchedFreeKSucc} are disjoint
  have h_disj2 : Disjoint {c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} {c | isUnmatchedFreeKSucc T k hk c} := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨_, h_not⟩, h_is⟩
    exact h_not h_is
  -- Disjointness: {T c = k+1 ∧ ¬isUnmatchedFreeKSucc} and {isUnmatchedFreeK} are disjoint
  have h_disj3 : Disjoint {c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} {c | isUnmatchedFreeK T k hk c} := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨hTc, _⟩, h_unmatched⟩
    have := h_unmatched_k_val c h_unmatched
    rw [hTc] at this
    simp only [Fin.ext_iff] at this
    omega
  -- Disjointness: {T c = k ∧ ¬isUnmatchedFreeK} and {isUnmatchedFreeK} are disjoint
  have h_disj4 : Disjoint {c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} {c | isUnmatchedFreeK T k hk c} := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨_, h_not⟩, h_is⟩
    exact h_not h_is
  -- Finiteness
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  have hfin_notUnmatchedK : Set.Finite {c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} := Set.toFinite _
  have hfin_notUnmatchedKSucc : Set.Finite {c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} := Set.toFinite _
  have hfin_unmatchedK : Set.Finite {c | isUnmatchedFreeK T k hk c} := Set.toFinite _
  have hfin_unmatchedKSucc : Set.Finite {c | isUnmatchedFreeKSucc T k hk c} := Set.toFinite _
  haveI : Fintype ↑{c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} := hfin_notUnmatchedK.fintype
  haveI : Fintype ↑{c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} := hfin_notUnmatchedKSucc.fintype
  haveI : Fintype ↑{c | isUnmatchedFreeK T k hk c} := hfin_unmatchedK.fintype
  haveI : Fintype ↑{c | isUnmatchedFreeKSucc T k hk c} := hfin_unmatchedKSucc.fintype
  -- Key cardinality equality from notUnmatched_k_kSucc_card_eq
  have h_card_notUnmatched := notUnmatched_k_kSucc_card_eq T hT k hk
  refine ⟨?_, ?_, h3⟩
  -- Part 1: contentTableau T' k = contentTableau T ⟨k.val + 1, hk⟩
  · -- Use the set equalities to show the cardinalities are equal
    unfold contentTableau
    -- First, convert {c // T' c = k} to the union form using h_T'_k_set
    have h1 : Nat.card {c // T' c = k} = 
        Nat.card ↑({c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} ∪ {c | isUnmatchedFreeKSucc T k hk c}) := by
      apply Nat.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _) (fun c => by 
        simp only [Set.ext_iff, Set.mem_union, Set.mem_ofPred_eq] at h_T'_k_set
        exact h_T'_k_set c)
    -- Second, convert {c // T c = k+1} to the union form using h_kSucc_decomp
    have h2 : Nat.card {c // T c = ⟨k.val + 1, hk⟩} = 
        Nat.card ↑({c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} ∪ {c | isUnmatchedFreeKSucc T k hk c}) := by
      apply Nat.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _) (fun c => by 
        simp only [Set.ext_iff, Set.mem_union, Set.mem_ofPred_eq] at h_kSucc_decomp
        exact h_kSucc_decomp c)
    rw [h1, h2]
    -- Now use the disjoint union cardinality
    haveI : Fintype ↑({c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} ∪ {c | isUnmatchedFreeKSucc T k hk c}) := 
      (hfin_notUnmatchedK.union hfin_unmatchedKSucc).fintype
    haveI : Fintype ↑({c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} ∪ {c | isUnmatchedFreeKSucc T k hk c}) := 
      (hfin_notUnmatchedKSucc.union hfin_unmatchedKSucc).fintype
    rw [Nat.card_eq_card_toFinset, Nat.card_eq_card_toFinset]
    rw [Set.toFinset_union, Set.toFinset_union]
    rw [Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr h_disj1)]
    rw [Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr h_disj2)]
    simp only [Nat.card_eq_card_toFinset] at h_card_notUnmatched
    omega
  -- Part 2: contentTableau T' ⟨k.val + 1, hk⟩ = contentTableau T k
  · -- Use the set equalities to show the cardinalities are equal
    unfold contentTableau
    -- First, convert {c // T' c = k+1} to the union form using h_T'_kSucc_set
    have h1 : Nat.card {c // T' c = ⟨k.val + 1, hk⟩} = 
        Nat.card ↑({c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} ∪ {c | isUnmatchedFreeK T k hk c}) := by
      apply Nat.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _) (fun c => by 
        simp only [Set.ext_iff, Set.mem_union, Set.mem_ofPred_eq] at h_T'_kSucc_set
        exact h_T'_kSucc_set c)
    -- Second, convert {c // T c = k} to the union form using h_k_decomp
    have h2 : Nat.card {c // T c = k} = 
        Nat.card ↑({c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} ∪ {c | isUnmatchedFreeK T k hk c}) := by
      apply Nat.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _) (fun c => by 
        simp only [Set.ext_iff, Set.mem_union, Set.mem_ofPred_eq] at h_k_decomp
        exact h_k_decomp c)
    rw [h1, h2]
    -- Now use the disjoint union cardinality
    haveI : Fintype ↑({c | T c = ⟨k.val + 1, hk⟩ ∧ ¬isUnmatchedFreeKSucc T k hk c} ∪ {c | isUnmatchedFreeK T k hk c}) := 
      (hfin_notUnmatchedKSucc.union hfin_unmatchedK).fintype
    haveI : Fintype ↑({c | T c = k ∧ ¬isUnmatchedFreeK T k hk c} ∪ {c | isUnmatchedFreeK T k hk c}) := 
      (hfin_notUnmatchedK.union hfin_unmatchedK).fintype
    rw [Nat.card_eq_card_toFinset, Nat.card_eq_card_toFinset]
    rw [Set.toFinset_union, Set.toFinset_union]
    rw [Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr h_disj3)]
    rw [Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr h_disj4)]
    simp only [Nat.card_eq_card_toFinset] at h_card_notUnmatched
    omega

/-- The monomial x_{BK_k(T)} equals s_k · x_T, where s_k swaps x_k and x_{k+1}.
    This follows from benderKnuth_content_swap. -/
theorem benderKnuth_monomial {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T) :
    (monomialTableau (benderKnuth k hk T hT) : MvPolynomial (Fin N) R) =
    MvPolynomial.rename (Equiv.swap k ⟨k.val + 1, hk⟩) (monomialTableau T) := by
  -- Get the content swap property from benderKnuth_content_swap
  obtain ⟨h1, h2, h3⟩ := benderKnuth_content_swap k hk T hT
  -- Unfold monomialTableau to xPow
  simp only [monomialTableau]
  -- Show that contentTableau T' = contentTableau T ∘ swap k k'
  have hcontent : contentTableau (benderKnuth k hk T hT) =
      contentTableau T ∘ Equiv.swap k ⟨k.val + 1, hk⟩ := by
    ext i
    simp only [Function.comp_apply]
    by_cases hik : i = k
    · subst hik
      rw [h1, Equiv.swap_apply_left]
    · by_cases hik1 : i.val = k.val + 1
      · have hi : i = ⟨k.val + 1, hk⟩ := Fin.ext hik1
        subst hi
        rw [h2, Equiv.swap_apply_right]
      · rw [h3 i hik hik1, Equiv.swap_apply_of_ne_of_ne hik]
        intro h
        apply hik1
        exact congrArg Fin.val h
  -- Rewrite using hcontent
  rw [hcontent]
  -- Now show xPow (α ∘ swap) = rename swap (xPow α)
  simp only [xPow_eq_monomialExp, AlgebraicCombinatorics.SymmetricFunctions.monomialExp]
  rw [map_prod]
  simp only [map_pow, rename_X]
  -- Reindex the product using the swap equivalence
  symm
  rw [Fintype.prod_equiv (Equiv.swap k ⟨k.val + 1, hk⟩)
                          (fun i => X i ^ (contentTableau T ∘ Equiv.swap k ⟨k.val + 1, hk⟩) i)
                          (fun i => X (Equiv.swap k ⟨k.val + 1, hk⟩ i) ^ contentTableau T i)]
  intro x
  simp only [Function.comp_apply]
  have h : Equiv.swap k ⟨k.val + 1, hk⟩ (Equiv.swap k ⟨k.val + 1, hk⟩ x) = x :=
    Equiv.swap_apply_self k ⟨k.val + 1, hk⟩ x
  rw [h]

/-! ## Stembridge's Involution for Non-Yamanouchi Tableaux

For Stembridge's lemma, we need a sign-reversing involution on non-Yamanouchi tableaux.
Given a tableau T that is not ν-Yamanouchi:
1. Find the largest "violator" column j (where ν + cont(col_{≥j}(T)) fails to be a partition)
2. Find the smallest "misstep" index k (where the partition condition fails)
3. Apply Bender-Knuth BK_k to columns 1, ..., j-1

This involution has the property that the paired tableaux contribute opposite signs
to the alternant sum, causing them to cancel. -/

/-- When j is beyond all columns in the diagram, contentColGeq T j = 0. -/
lemma contentColGeq_eq_zero_of_large {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (j : ℕ) (hj : ∀ i : Fin N, lam i < j) :
    contentColGeq T j = 0 := by
  ext i
  unfold contentColGeq
  simp only [Pi.zero_apply]
  rw [Nat.card_eq_zero]
  left
  constructor
  intro ⟨⟨c, hc_mem, hc_col⟩, _⟩
  have hc_le : c.2 ≤ lam c.1 := hc_mem.2
  have hc_lt : lam c.1 < j := hj c.1
  omega

/-- Check if ν + cont(col_{≥j}(T)) is an N-partition. -/
noncomputable def isPartitionAtColumn {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (T : Tableau lam mu) (j : ℕ) : Prop :=
  IsNPartition (nu + contentColGeq T j)

/-- Decidability of isPartitionAtColumn. -/
noncomputable instance isPartitionAtColumn_decidable {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (T : Tableau lam mu) (j : ℕ) : Decidable (isPartitionAtColumn nu T j) := by
  unfold isPartitionAtColumn IsNPartition
  infer_instance

/-- The set of columns where ν + cont(col_{≥j}(T)) fails to be a partition.

    Note: We use `maxCol + 2` in the range to ensure that `j = maxCol + 1` is included.
    This is important because for `j > maxCol`, `contentColGeq T j = 0`, so we're checking
    if `nu` itself is an N-partition. Without this, the lemma
    `violatorColumns_nonempty_of_not_yamanouchi` would fail when `nu` is not an N-partition
    but `nu + contentColGeq T j` is an N-partition for all `j ≤ maxCol`. -/
noncomputable def violatorColumns {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (T : Tableau lam mu) : Finset ℕ :=
  let maxCol := Finset.sup Finset.univ lam
  (Finset.range (maxCol + 2)).filter (fun j => j > 0 ∧ ¬isPartitionAtColumn nu T j)

/-- Find the largest column j where ν + cont(col_{≥j}(T)) fails to be an N-partition.
    Returns `none` if T is ν-Yamanouchi (i.e., no such column exists). -/
noncomputable def findViolatorColumn {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (T : Tableau lam mu) : Option ℕ :=
  if h : (violatorColumns nu T).Nonempty then some ((violatorColumns nu T).max' h) else none

/-- Check if index k is a misstep: α_k < α_{k+1}. -/
def isMisstep (α : Fin N → ℕ) (k : Fin N) : Prop :=
  ∃ h : k.val + 1 < N, α k < α ⟨k.val + 1, h⟩

/-- Decidability of isMisstep. -/
instance isMisstep_decidable (α : Fin N → ℕ) (k : Fin N) : Decidable (isMisstep α k) := by
  unfold isMisstep
  infer_instance

/-- The set of misstep indices for a tuple α. -/
noncomputable def misstepSet (α : Fin N → ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun k => isMisstep α k)

/-- Find the smallest index k where α_k < α_{k+1}. Returns `none` if α is a partition. -/
noncomputable def findFirstMisstep (α : Fin N → ℕ) : Option (Fin N) :=
  if h : (misstepSet α).Nonempty then some ((misstepSet α).min' h) else none

/-- Find the smallest index k where ν + cont(col_{≥j}(T)) fails the partition condition.
    That is, find k such that (ν + cont(col_{≥j}(T)))_k < (ν + cont(col_{≥j}(T)))_{k+1}. -/
noncomputable def findMisstepIndex {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (T : Tableau lam mu) (j : ℕ) : Option (Fin N) :=
  findFirstMisstep (nu + contentColGeq T j)

/-! ### Prefix-restricted count functions for benderKnuthPrefixMatching

The following definitions compute matching for the Bender-Knuth involution restricted
to a column prefix (columns < j). This infrastructure is used by `benderKnuthPrefixMatching`
to correctly preserve row-weak ordering.

**Key insight**: When applying BK_k to columns < j only, the matching should be
computed using only the free entries in columns < j, not the entire row. This ensures
that unmatched entries are at the k/(k+1) boundary within the prefix. -/

/-- Count of free k's in row i restricted to columns < j.
    This is an alias for `freeKCountBefore` for use in the prefix-matching context. -/
noncomputable abbrev freeKCountPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) : ℕ :=
  freeKCountBefore T i k hk j

/-- Count of free (k+1)'s in row i restricted to columns < j. -/
noncomputable def freeKSuccCountPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c}

/-- Count of free k's in row i with column ≤ col, restricted to columns < j.
    Used for the parenthesis-matching algorithm in benderKnuthPrefixMatching. -/
noncomputable def freeKCountUpToPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) (col : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 ≤ col ∧ c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c}

/-- Count of free (k+1)'s in row i with column ≤ col, restricted to columns < j.
    Used for the parenthesis-matching algorithm in benderKnuthPrefixMatching. -/
noncomputable def freeKSuccCountUpToPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) (col : ℕ) : ℕ :=
  Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
    c.val.1 = i ∧ c.val.2 ≤ col ∧ c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c}

/-- A free k at position c is "unmatched" within the column prefix (columns < j).

    This is the prefix-restricted version of `isUnmatchedFreeK`. The matching is computed
    using only free entries in columns < j, not the entire row.

    A free k is unmatched in the prefix iff at its position, the cumulative count of
    free k's (in the prefix) exceeds the TOTAL count of free (k+1)'s (in the prefix).

    **Usage**: Used by `benderKnuthPrefixMatching` to correctly preserve row-weak ordering. -/
def isUnmatchedFreeKPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c ∧
  freeKCountUpToPrefix T c.val.1 k hk j c.val.2 > freeKSuccCountPrefix T c.val.1 k hk j

/-- A free (k+1) at position c is "unmatched" within the column prefix (columns < j).

    This is the prefix-restricted version of `isUnmatchedFreeKSucc`. The matching is computed
    using only free entries in columns < j, not the entire row.

    A free (k+1) is unmatched in the prefix iff it's among the leftmost excess (k+1)'s,
    i.e., the cumulative count of free (k+1)'s up to c plus the total free k count
    is at most the total free (k+1) count (all counts restricted to the prefix).

    **Usage**: Used by `benderKnuthPrefixMatching` to correctly preserve row-weak ordering. -/
def isUnmatchedFreeKSuccPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c ∧
  freeKCountPrefix T c.val.1 k hk j + freeKSuccCountUpToPrefix T c.val.1 k hk j c.val.2 ≤
    freeKSuccCountPrefix T c.val.1 k hk j

/-- A matched free k in the prefix (columns < j) is a free k that is not unmatched.
    In the parenthesis-matching algorithm restricted to the prefix, these are the k's
    that get paired with (k+1)'s. -/
def isMatchedFreeKPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c ∧ ¬isUnmatchedFreeKPrefix T k hk j c

/-- A matched free (k+1) in the prefix (columns < j) is a free (k+1) that is not unmatched.
    In the parenthesis-matching algorithm restricted to the prefix, these are the (k+1)'s
    that get paired with k's. -/
def isMatchedFreeKSuccPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) : Prop :=
  c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c ∧ ¬isUnmatchedFreeKSuccPrefix T k hk j c

/-! ### Cardinality lemmas for prefix-restricted matching

These lemmas establish cardinalities of matched/unmatched cells in the prefix,
analogous to `matchedFreeK_row_card` and `unmatchedFreeK_row_card` for the full-row version.

**Key results**:
- `matchedFreeKPrefix_row_card`: #{matched free k's in row i, prefix} = min(m, n)
- `unmatchedFreeKPrefix_row_card`: #{unmatched free k's in row i, prefix} = m - min(m, n)
- `matchedFreeKSuccPrefix_row_card`: #{matched free (k+1)'s in row i, prefix} = min(m, n)
- `unmatchedFreeKSuccPrefix_row_card`: #{unmatched free (k+1)'s in row i, prefix} = n - min(m, n)

where m = freeKCountPrefix T i k hk j and n = freeKSuccCountPrefix T i k hk j.

These are the prefix-restricted versions of the lemmas at lines 3244-3550. -/

/-- The number of matched free k's in row i within the prefix equals min(m, n)
    where m = freeKCountPrefix and n = freeKSuccCountPrefix.
    
    This is the prefix-restricted version of `matchedFreeK_row_card`.
    
    **Proof strategy**: Same as `matchedFreeK_row_card` but restricted to columns < j.
    The key insight is that the parenthesis-matching algorithm pairs k's with (k+1)'s
    from left to right, so the number of matched pairs equals min(m, n). -/
private lemma matchedFreeKPrefix_row_card {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) :
    Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKPrefix T k hk j c} = 
    min (freeKCountPrefix T i k hk j) (freeKSuccCountPrefix T i k hk j) := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Step 1: Define the finset of free k cells in row i within the prefix (columns < j)
  set cells := Finset.univ.filter (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} =>
    c.val.1 = i ∧ c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c) with hcells_def
  -- Define S as the columns of free k cells in the prefix (local version of freeKColsPrefix)
  set S := cells.image (fun c => c.val.2) with hS_def
  set n := freeKSuccCountPrefix T i k hk j with hn_def
  
  -- Step 2: Show S.card = freeKCountPrefix
  have hS_card : S.card = freeKCountPrefix T i k hk j := by
    rw [hS_def, hcells_def]
    unfold freeKCountPrefix freeKCountBefore
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply Finset.card_image_of_injOn
    intro c₁ hc₁ c₂ hc₂ hcol
    have hc₁' := Finset.mem_filter.mp hc₁
    have hc₂' := Finset.mem_filter.mp hc₂
    ext
    · rw [hc₁'.2.1, hc₂'.2.1]
    · exact hcol
  
  -- Step 3: Show freeKCountUpToPrefix equals filter cardinality of S
  have h_upTo_eq_filter : ∀ col : ℕ, 
      freeKCountUpToPrefix T i k hk j col = (S.filter (· ≤ col)).card := by
    intro col
    unfold freeKCountUpToPrefix
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hS_def, hcells_def]
    -- Both sides count cells with column ≤ col in the prefix
    rw [Finset.filter_image]
    -- Goal: #{c | row=i ∧ col≤col ∧ col<j ∧ T c=k ∧ ¬forced} = #(filter.image col)
    symm
    rw [Finset.card_image_of_injOn]
    · -- The filter sets have the same cardinality
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨⟨h1, h3, h4, h5⟩, h2⟩
        exact ⟨h1, h2, h3, h4, h5⟩
      · intro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨⟨h1, h3, h4, h5⟩, h2⟩
    · -- Injectivity on the filtered set
      intro c₁ hc₁ c₂ hc₂ hcol
      have hc₁' := Finset.mem_filter.mp hc₁
      have hc₂' := Finset.mem_filter.mp hc₂
      have hc₁'' := Finset.mem_filter.mp hc₁'.1
      have hc₂'' := Finset.mem_filter.mp hc₂'.1
      ext
      · rw [hc₁''.2.1, hc₂''.2.1]
      · exact hcol
  
  -- Step 4: Show the filter of matched cells equals the filter with the column condition
  have h_filter_eq : (Finset.univ.filter (fun c => c.val.1 = i ∧ isMatchedFreeKPrefix T k hk j c)).card = 
      (cells.filter (fun c => (S.filter (· ≤ c.val.2)).card ≤ n)).card := by
    congr 1
    ext c
    rw [hcells_def]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hrow, hmatched⟩
      unfold isMatchedFreeKPrefix at hmatched
      obtain ⟨hcol_lt_j, hval, hfree, hunmatched⟩ := hmatched
      refine ⟨⟨hrow, hcol_lt_j, hval, hfree⟩, ?_⟩
      -- ¬isUnmatchedFreeKPrefix means freeKCountUpToPrefix c.col ≤ freeKSuccCountPrefix
      unfold isUnmatchedFreeKPrefix at hunmatched
      push Not at hunmatched
      have h := hunmatched hcol_lt_j hval hfree
      -- Use hrow to rewrite c.val.1 to i in h
      rw [hrow] at h
      -- freeKCountUpToPrefix c.col = (S.filter (· ≤ c.col)).card
      rw [h_upTo_eq_filter c.val.2] at h
      -- freeKSuccCountPrefix = n
      rw [← hn_def] at h
      exact h
    · intro ⟨⟨hrow, hcol_lt_j, hval, hfree⟩, hcond⟩
      refine ⟨hrow, ?_⟩
      unfold isMatchedFreeKPrefix
      refine ⟨hcol_lt_j, hval, hfree, ?_⟩
      -- Need to show ¬isUnmatchedFreeKPrefix
      unfold isUnmatchedFreeKPrefix
      push Not
      intro _ _ _
      -- hcond: (S.filter (· ≤ c.col)).card ≤ n
      -- Need: freeKCountUpToPrefix c.col ≤ freeKSuccCountPrefix
      rw [hrow, h_upTo_eq_filter c.val.2, ← hn_def]
      exact hcond
  -- The goal after Fintype.card_subtype is: #{x | x ∈ {c | ...}} = ...
  convert h_filter_eq using 1
  on_goal 1 => rfl
  
  -- Step 5: Show the bijection between cells and columns in S
  have h_col_mem : ∀ c ∈ cells, c.val.2 ∈ S := by
    intro c hc
    rw [hS_def]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  
  have h_col_inj : ∀ c₁ ∈ cells, ∀ c₂ ∈ cells, c₁.val.2 = c₂.val.2 → c₁ = c₂ := by
    intro c₁ hc₁ c₂ hc₂ hcol
    rw [hcells_def] at hc₁ hc₂
    have hc₁' := Finset.mem_filter.mp hc₁
    have hc₂' := Finset.mem_filter.mp hc₂
    ext
    · rw [hc₁'.2.1, hc₂'.2.1]
    · exact hcol
  
  have h_col_surj : ∀ s ∈ S, ∃ c ∈ cells, c.val.2 = s := by
    intro s hs
    rw [hS_def] at hs
    obtain ⟨c, hc, hcol⟩ := Finset.mem_image.mp hs
    exact ⟨c, hc, hcol⟩
  
  -- Step 6: Apply the bijection to get the equality with column filter
  have h_bij : (cells.filter (fun c => (S.filter (· ≤ c.val.2)).card ≤ n)).card = 
      (S.filter (fun s => (S.filter (· ≤ s)).card ≤ n)).card := by
    apply Finset.card_bij (fun c _ => c.val.2)
    · intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      exact ⟨h_col_mem c hc.1, hc.2⟩
    · intro c₁ hc₁ c₂ hc₂ heq
      simp only [Finset.mem_filter] at hc₁ hc₂
      exact h_col_inj c₁ hc₁.1 c₂ hc₂.1 heq
    · intro s hs
      simp only [Finset.mem_filter] at hs
      obtain ⟨c, hc, hcol⟩ := h_col_surj s hs.1
      refine ⟨c, ?_, hcol⟩
      simp only [Finset.mem_filter]
      exact ⟨hc, hcol ▸ hs.2⟩
  rw [h_bij]
  
  -- Step 7: Apply matched_cols_count
  rw [matched_cols_count S n]
  -- Now need to show min S.card n = min m n where m = freeKCountPrefix
  rw [hS_card, hn_def]

/-- The number of unmatched free k's in row i within the prefix equals m - min(m, n)
    where m = freeKCountPrefix and n = freeKSuccCountPrefix.
    
    This is the prefix-restricted version of `unmatchedFreeK_row_card`. -/
private lemma unmatchedFreeKPrefix_row_card {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) :
    Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isUnmatchedFreeKPrefix T k hk j c} = 
    freeKCountPrefix T i k hk j - min (freeKCountPrefix T i k hk j) (freeKSuccCountPrefix T i k hk j) := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  -- Free k's in row i in prefix = matched + unmatched (disjoint union)
  set m := freeKCountPrefix T i k hk j with hm_def
  set n := freeKSuccCountPrefix T i k hk j with hn_def
  -- Matched free k's in prefix
  have h_matched : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKPrefix T k hk j c} = min m n := matchedFreeKPrefix_row_card T i k hk j
  -- Free k's in prefix = matched ∪ unmatched (disjoint)
  have h_partition : {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c} =
    {c | c.val.1 = i ∧ isMatchedFreeKPrefix T k hk j c} ∪ {c | c.val.1 = i ∧ isUnmatchedFreeKPrefix T k hk j c} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro ⟨hrow, hcol, hval, hfree⟩
      by_cases h : isUnmatchedFreeKPrefix T k hk j c
      · right; exact ⟨hrow, h⟩
      · left
        unfold isMatchedFreeKPrefix
        exact ⟨hrow, hcol, hval, hfree, h⟩
    · intro h
      rcases h with ⟨hrow, hmatched⟩ | ⟨hrow, hunmatched⟩
      · unfold isMatchedFreeKPrefix at hmatched
        exact ⟨hrow, hmatched.1, hmatched.2.1, hmatched.2.2.1⟩
      · unfold isUnmatchedFreeKPrefix at hunmatched
        exact ⟨hrow, hunmatched.1, hunmatched.2.1, hunmatched.2.2.1⟩
  -- Disjointness
  have h_disj : Disjoint {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKPrefix T k hk j c} 
    {c | c.val.1 = i ∧ isUnmatchedFreeKPrefix T k hk j c} := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨_, hmatched⟩, ⟨_, hunmatched⟩⟩
    unfold isMatchedFreeKPrefix at hmatched
    exact hmatched.2.2.2 hunmatched
  -- Finiteness
  have hfin1 : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKPrefix T k hk j c} := Set.toFinite _
  have hfin2 : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isUnmatchedFreeKPrefix T k hk j c} := Set.toFinite _
  -- Compute total from partition
  have h_total_eq : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c} = 
    Nat.card {c | c.val.1 = i ∧ isMatchedFreeKPrefix T k hk j c} + 
    Nat.card {c | c.val.1 = i ∧ isUnmatchedFreeKPrefix T k hk j c} := by
    rw [h_partition]
    rw [Nat.card_eq_card_toFinset, Set.toFinset_union, 
        Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr h_disj)]
    simp only [Nat.card_eq_card_toFinset]
  -- Total = m (by definition of freeKCountPrefix = freeKCountBefore)
  have h_total_m : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ c.val.2 < j ∧ T c = k ∧ ¬isForcedK T k hk c} = m := rfl
  -- Combine
  rw [h_total_m, h_matched] at h_total_eq
  omega

/-- The number of matched free (k+1)'s in row i within the prefix equals min(m, n)
    where m = freeKCountPrefix and n = freeKSuccCountPrefix.
    
    This is the prefix-restricted version of `matchedFreeKSucc_row_card`. -/
private lemma matchedFreeKSuccPrefix_row_card {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) :
    Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKSuccPrefix T k hk j c} = 
    min (freeKCountPrefix T i k hk j) (freeKSuccCountPrefix T i k hk j) := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Define the cells and S
  set cells := Finset.univ.filter (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} =>
    c.val.1 = i ∧ c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c) with hcells
  set S := cells.image (fun c => c.val.2) with hS
  set m := freeKCountPrefix T i k hk j with hm
  
  -- S.card = freeKSuccCountPrefix
  have hS_card : S.card = freeKSuccCountPrefix T i k hk j := by
    rw [hS, hcells]
    unfold freeKSuccCountPrefix
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply Finset.card_image_of_injOn
    intro c₁ hc₁ c₂ hc₂ hcol
    have hc₁' := Finset.mem_filter.mp hc₁
    have hc₂' := Finset.mem_filter.mp hc₂
    have hrow₁ : c₁.val.1 = i := hc₁'.2.1
    have hrow₂ : c₂.val.1 = i := hc₂'.2.1
    ext
    · rw [hrow₁, hrow₂]
    · exact hcol
  
  -- freeKSuccCountUpToPrefix = (S.filter (· ≤ col)).card
  have hS_filter_card : ∀ col, freeKSuccCountUpToPrefix T i k hk j col = (S.filter (· ≤ col)).card := by
    intro col
    rw [hS, hcells]
    unfold freeKSuccCountUpToPrefix
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [Finset.filter_image]
    -- First show the sets are equal
    have h_sets_eq : (Finset.univ.filter (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} =>
        c.val.1 = i ∧ c.val.2 ≤ col ∧ c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c)) =
      ((Finset.univ.filter (fun c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} =>
        c.val.1 = i ∧ c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c)).filter 
        (fun c => c.val.2 ≤ col)) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hi, hle, hlt, hval, hfree⟩
        exact ⟨⟨hi, hlt, hval, hfree⟩, hle⟩
      · intro ⟨⟨hi, hlt, hval, hfree⟩, hle⟩
        exact ⟨hi, hle, hlt, hval, hfree⟩
    rw [h_sets_eq]
    symm
    apply Finset.card_image_of_injOn
    intro c₁ hc₁ c₂ hc₂ hcol'
    have hc₁' := Finset.mem_filter.mp hc₁
    have hc₂' := Finset.mem_filter.mp hc₂
    have hc₁'' := Finset.mem_filter.mp hc₁'.1
    have hc₂'' := Finset.mem_filter.mp hc₂'.1
    have hrow₁ : c₁.val.1 = i := hc₁''.2.1
    have hrow₂ : c₂.val.1 = i := hc₂''.2.1
    ext
    · rw [hrow₁, hrow₂]
    · exact hcol'
  
  -- Main filter equality
  have h_filter_eq : (Finset.univ.filter (fun c => c.val.1 = i ∧ isMatchedFreeKSuccPrefix T k hk j c)).card = 
      (cells.filter (fun c => m + (S.filter (· ≤ c.val.2)).card > S.card)).card := by
    congr 1
    ext c
    rw [hcells]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hrow, hmatched⟩
      unfold isMatchedFreeKSuccPrefix at hmatched
      obtain ⟨hcol, hval, hfree, hunmatched⟩ := hmatched
      refine ⟨⟨hrow, hcol, hval, hfree⟩, ?_⟩
      unfold isUnmatchedFreeKSuccPrefix at hunmatched
      push Not at hunmatched
      have h := hunmatched hcol hval hfree
      rw [hrow] at h
      -- h : freeKSuccCountPrefix T i k hk j < freeKCountPrefix T i k hk j + freeKSuccCountUpToPrefix T i k hk j c.val.2
      -- goal : m + (S.filter (· ≤ c.val.2)).card > S.card
      -- Use hS_filter_card, hS_card, hm to convert
      have h' : (S.filter (· ≤ c.val.2)).card = freeKSuccCountUpToPrefix T i k hk j c.val.2 := 
        (hS_filter_card c.val.2).symm
      rw [h', hm, hS_card]
      omega
    · intro ⟨⟨hrow, hcol, hval, hfree⟩, hcond⟩
      refine ⟨hrow, ?_⟩
      unfold isMatchedFreeKSuccPrefix
      refine ⟨hcol, hval, hfree, ?_⟩
      unfold isUnmatchedFreeKSuccPrefix
      push Not
      intro _ _ _
      rw [hrow]
      -- hcond : m + (S.filter (· ≤ c.val.2)).card > S.card
      -- goal : freeKSuccCountPrefix T i k hk j < freeKCountPrefix T i k hk j + freeKSuccCountUpToPrefix T i k hk j c.val.2
      have h' : (S.filter (· ≤ c.val.2)).card = freeKSuccCountUpToPrefix T i k hk j c.val.2 := 
        (hS_filter_card c.val.2).symm
      rw [← h', ← hm, ← hS_card]
      omega
  
  have h_col_mem : ∀ c, c ∈ cells → c.val.2 ∈ S := by
    intro c hc
    rw [hS]
    exact Finset.mem_image_of_mem _ hc
  
  have h_col_inj : ∀ c₁, c₁ ∈ cells → ∀ c₂, c₂ ∈ cells → c₁.val.2 = c₂.val.2 → c₁ = c₂ := by
    intro c₁ hc₁ c₂ hc₂ hcol
    rw [hcells] at hc₁ hc₂
    have hc₁' := Finset.mem_filter.mp hc₁
    have hc₂' := Finset.mem_filter.mp hc₂
    have hrow₁ : c₁.val.1 = i := hc₁'.2.1
    have hrow₂ : c₂.val.1 = i := hc₂'.2.1
    ext
    · rw [hrow₁, hrow₂]
    · exact hcol
  
  have h_col_surj : ∀ s, s ∈ S → ∃ c, c ∈ cells ∧ c.val.2 = s := by
    intro s hs
    rw [hS] at hs
    exact Finset.mem_image.mp hs
  
  -- Apply bijection
  have h_bij : (cells.filter (fun c => m + (S.filter (· ≤ c.val.2)).card > S.card)).card = 
      (S.filter (fun s => m + (S.filter (· ≤ s)).card > S.card)).card := by
    apply Finset.card_bij (fun c _ => c.val.2)
    · intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      exact ⟨h_col_mem c hc.1, hc.2⟩
    · intro c₁ hc₁ c₂ hc₂ heq
      simp only [Finset.mem_filter] at hc₁ hc₂
      exact h_col_inj c₁ hc₁.1 c₂ hc₂.1 heq
    · intro s hs
      simp only [Finset.mem_filter] at hs
      obtain ⟨c, hc, hcol⟩ := h_col_surj s hs.1
      refine ⟨c, ?_, hcol⟩
      simp only [Finset.mem_filter]
      exact ⟨hc, hcol ▸ hs.2⟩
    
  -- Combine everything
  simp only [Set.mem_ofPred_eq]
  rw [h_filter_eq, h_bij, matched_kSucc_cols_count S m, hS_card, hm]



/-- The number of unmatched free (k+1)'s in row i within the prefix equals n - min(m, n)
    where m = freeKCountPrefix and n = freeKSuccCountPrefix.
    
    This is the prefix-restricted version of `unmatchedFreeKSucc_row_card`. -/
private lemma unmatchedFreeKSuccPrefix_row_card {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (i : Fin N) (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) :
    Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isUnmatchedFreeKSuccPrefix T k hk j c} = 
    freeKSuccCountPrefix T i k hk j - min (freeKCountPrefix T i k hk j) (freeKSuccCountPrefix T i k hk j) := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  -- Free (k+1)'s in row i within prefix = matched + unmatched (disjoint union)
  set m := freeKCountPrefix T i k hk j with hm_def
  set n := freeKSuccCountPrefix T i k hk j with hn_def
  -- Matched free (k+1)'s in prefix
  have h_matched : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKSuccPrefix T k hk j c} = min m n := matchedFreeKSuccPrefix_row_card T i k hk j
  -- Free (k+1)'s in prefix = matched ∪ unmatched (disjoint)
  have h_partition : {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c} =
    {c | c.val.1 = i ∧ isMatchedFreeKSuccPrefix T k hk j c} ∪ {c | c.val.1 = i ∧ isUnmatchedFreeKSuccPrefix T k hk j c} := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro ⟨hrow, hcol, hval, hfree⟩
      by_cases h : isUnmatchedFreeKSuccPrefix T k hk j c
      · right; exact ⟨hrow, h⟩
      · left
        unfold isMatchedFreeKSuccPrefix
        exact ⟨hrow, hcol, hval, hfree, h⟩
    · intro h
      rcases h with ⟨hrow, hmatched⟩ | ⟨hrow, hunmatched⟩
      · unfold isMatchedFreeKSuccPrefix at hmatched
        exact ⟨hrow, hmatched.1, hmatched.2.1, hmatched.2.2.1⟩
      · unfold isUnmatchedFreeKSuccPrefix at hunmatched
        exact ⟨hrow, hunmatched.1, hunmatched.2.1, hunmatched.2.2.1⟩
  -- Disjointness
  have h_disj : Disjoint {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKSuccPrefix T k hk j c} 
    {c | c.val.1 = i ∧ isUnmatchedFreeKSuccPrefix T k hk j c} := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨_, hmatched⟩, ⟨_, hunmatched⟩⟩
    unfold isMatchedFreeKSuccPrefix at hmatched
    exact hmatched.2.2.2 hunmatched
  -- Finiteness
  have hfin1 : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKSuccPrefix T k hk j c} := Set.toFinite _
  have hfin2 : Set.Finite {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isUnmatchedFreeKSuccPrefix T k hk j c} := Set.toFinite _
  -- Compute total from partition
  have h_total_eq : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c} = 
    Nat.card {c | c.val.1 = i ∧ isMatchedFreeKSuccPrefix T k hk j c} + 
    Nat.card {c | c.val.1 = i ∧ isUnmatchedFreeKSuccPrefix T k hk j c} := by
    rw [h_partition]
    rw [Nat.card_eq_card_toFinset, Set.toFinset_union, 
        Finset.card_union_of_disjoint (Set.disjoint_toFinset.mpr h_disj)]
    simp only [Nat.card_eq_card_toFinset]
  -- Total = n (by definition of freeKSuccCountPrefix)
  have h_total_n : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ c.val.2 < j ∧ T c = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c} = n := rfl
  -- Combine
  rw [h_total_n, h_matched] at h_total_eq
  omega

/-! ### Helper lemmas for prefix-restricted matching

These lemmas establish key properties of `isUnmatchedFreeKPrefix` and `isUnmatchedFreeKSuccPrefix`
that are used by `benderKnuthPrefixMatching_row_weak_stembridge` and related proofs.

**Key insight**: In the prefix-restricted matching:
- Unmatched free k's are the RIGHTMOST excess free k's (after matching with free (k+1)'s)
- Unmatched free (k+1)'s are the LEFTMOST excess free (k+1)'s

This means if c₁ is unmatched free k and c₂ is unmatched free (k+1) in the same row,
then c₁.col > c₂.col (c₁ is to the right of c₂). This is crucial for row-weak preservation. -/

/-- Monotonicity of `freeKCountUpToPrefix` in the column argument. -/
private lemma freeKCountUpToPrefix_mono {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) (col₁ col₂ : ℕ) (h : col₁ ≤ col₂) :
    freeKCountUpToPrefix T i k hk j col₁ ≤ freeKCountUpToPrefix T i k hk j col₂ := by
  unfold freeKCountUpToPrefix
  apply Nat.card_mono
  · haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
      Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
    exact Set.toFinite _
  · intro ⟨c, hc⟩ hmem
    exact ⟨hmem.1, le_trans hmem.2.1 h, hmem.2.2⟩

/-- Monotonicity of `freeKSuccCountUpToPrefix` in the column argument. -/
private lemma freeKSuccCountUpToPrefix_mono {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) (col₁ col₂ : ℕ) (h : col₁ ≤ col₂) :
    freeKSuccCountUpToPrefix T i k hk j col₁ ≤ freeKSuccCountUpToPrefix T i k hk j col₂ := by
  unfold freeKSuccCountUpToPrefix
  apply Nat.card_mono
  · haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
      Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
    exact Set.toFinite _
  · intro ⟨c, hc⟩ hmem
    exact ⟨hmem.1, le_trans hmem.2.1 h, hmem.2.2⟩

/-- `freeKCountUpToPrefix` is bounded by `freeKCountPrefix`. -/
private lemma freeKCountUpToPrefix_le_freeKCountPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) (col : ℕ) :
    freeKCountUpToPrefix T i k hk j col ≤ freeKCountPrefix T i k hk j := by
  unfold freeKCountUpToPrefix freeKCountPrefix
  apply Nat.card_mono
  · haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
      Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
    exact Set.toFinite _
  · intro ⟨c, hc⟩ hmem
    exact ⟨hmem.1, hmem.2.2.1, hmem.2.2.2⟩

/-- `freeKSuccCountUpToPrefix` is bounded by `freeKSuccCountPrefix`. -/
private lemma freeKSuccCountUpToPrefix_le_freeKSuccCountPrefix {lam mu : Fin N → ℕ} (T : Tableau lam mu) (i : Fin N)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) (col : ℕ) :
    freeKSuccCountUpToPrefix T i k hk j col ≤ freeKSuccCountPrefix T i k hk j := by
  unfold freeKSuccCountUpToPrefix freeKSuccCountPrefix
  apply Nat.card_mono
  · haveI : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
      Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
    exact Set.toFinite _
  · intro ⟨c, hc⟩ hmem
    exact ⟨hmem.1, hmem.2.2.1, hmem.2.2.2⟩

/-- In the prefix-restricted matching, an unmatched free k cannot be to the left of an
    unmatched free (k+1) in the same row. This is the key lemma for row-weak preservation.
    
    **Proof sketch**: 
    - If c₁ is unmatched free k at column j₁, then freeKCountUpToPrefix(j₁) > freeKSuccCountPrefix
    - If c₂ is unmatched free (k+1) at column j₂, then freeKCountPrefix + freeKSuccCountUpToPrefix(j₂) ≤ freeKSuccCountPrefix
    - If j₁ < j₂, then freeKCountUpToPrefix(j₁) ≤ freeKCountPrefix (since j₁ < j)
    - Combining: freeKCountPrefix ≥ freeKCountUpToPrefix(j₁) > freeKSuccCountPrefix ≥ freeKCountPrefix + freeKSuccCountUpToPrefix(j₂)
    - This gives freeKSuccCountUpToPrefix(j₂) < 0, contradiction. -/
private lemma not_unmatched_k_left_of_unmatched_kSucc_prefix {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) (j : ℕ)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (_h_col : c₁.val.2 < c₂.val.2)
    (h1 : isUnmatchedFreeKPrefix T k hk j c₁) (h2 : isUnmatchedFreeKSuccPrefix T k hk j c₂) :
    False := by
  -- Extract the conditions from h1 and h2
  have hc₁j : c₁.val.2 < j := h1.1
  have hc₂j : c₂.val.2 < j := h2.1
  have h1_cond : freeKCountUpToPrefix T c₁.val.1 k hk j c₁.val.2 > freeKSuccCountPrefix T c₁.val.1 k hk j := h1.2.2.2
  have h2_cond : freeKCountPrefix T c₂.val.1 k hk j + freeKSuccCountUpToPrefix T c₂.val.1 k hk j c₂.val.2 ≤
                 freeKSuccCountPrefix T c₂.val.1 k hk j := h2.2.2.2
  -- Rewrite using h_row
  rw [h_row] at h1_cond
  -- freeKCountUpToPrefix(c₁.col) ≤ freeKCountPrefix because c₁.col < j
  have h_mono : freeKCountUpToPrefix T c₂.val.1 k hk j c₁.val.2 ≤ freeKCountPrefix T c₂.val.1 k hk j :=
    freeKCountUpToPrefix_le_freeKCountPrefix T c₂.val.1 k hk j c₁.val.2
  -- Combine the inequalities
  have h_contra : freeKSuccCountPrefix T c₂.val.1 k hk j < freeKCountPrefix T c₂.val.1 k hk j + freeKSuccCountUpToPrefix T c₂.val.1 k hk j c₂.val.2 := by
    calc freeKSuccCountPrefix T c₂.val.1 k hk j 
        < freeKCountUpToPrefix T c₂.val.1 k hk j c₁.val.2 := h1_cond
      _ ≤ freeKCountPrefix T c₂.val.1 k hk j := h_mono
      _ ≤ freeKCountPrefix T c₂.val.1 k hk j + freeKSuccCountUpToPrefix T c₂.val.1 k hk j c₂.val.2 := Nat.le_add_right _ _
  omega

/-- Matched free k propagates to the left within the prefix.

    If c₂ is a free k in the prefix that is NOT unmatched (i.e., matched), and c₁ is also
    a free k in the prefix to the left of c₂ in the same row, then c₁ is also matched.

    **Proof**: The matching condition for c₂ is:
      freeKCountUpToPrefix(c₂.col) ≤ freeKSuccCountPrefix
    Since c₁.col < c₂.col and both are in the prefix:
      freeKCountUpToPrefix(c₁.col) ≤ freeKCountUpToPrefix(c₂.col) ≤ freeKSuccCountPrefix
    So c₁ is also matched. -/
private lemma matched_k_propagates_left_prefix {lam mu : Fin N → ℕ} (T : Tableau lam mu)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (h_col : c₁.val.2 < c₂.val.2)
    (_h_c₁_free_k_prefix : c₁.val.2 < j ∧ T c₁ = k ∧ ¬isForcedK T k hk c₁)
    (h_c₂_free_k_prefix : c₂.val.2 < j ∧ T c₂ = k ∧ ¬isForcedK T k hk c₂)
    (h_c₂_matched : ¬isUnmatchedFreeKPrefix T k hk j c₂) :
    ¬isUnmatchedFreeKPrefix T k hk j c₁ := by
  intro h_c₁_unmatched
  apply h_c₂_matched
  unfold isUnmatchedFreeKPrefix at h_c₁_unmatched ⊢
  refine ⟨h_c₂_free_k_prefix.1, h_c₂_free_k_prefix.2.1, h_c₂_free_k_prefix.2.2, ?_⟩
  -- Need: freeKCountUpToPrefix(c₂.col) > freeKSuccCountPrefix
  -- From h_c₁_unmatched: freeKCountUpToPrefix(c₁.col) > freeKSuccCountPrefix
  have h_gt := h_c₁_unmatched.2.2.2
  -- freeKSuccCountPrefix is the same for both (it's the total count in the row within prefix)
  have h_succ_eq : freeKSuccCountPrefix T c₂.val.1 k hk j = freeKSuccCountPrefix T c₁.val.1 k hk j := by
    rw [h_row]
  -- freeKCountUpToPrefix is monotone
  have h_mono : freeKCountUpToPrefix T c₁.val.1 k hk j c₁.val.2 ≤
                freeKCountUpToPrefix T c₂.val.1 k hk j c₂.val.2 := by
    rw [h_row]
    exact freeKCountUpToPrefix_mono T c₂.val.1 k hk j c₁.val.2 c₂.val.2 (Nat.le_of_lt h_col)
  -- Combine: freeKCountUpToPrefix(c₂) ≥ freeKCountUpToPrefix(c₁) > freeKSuccCountPrefix(c₁) = freeKSuccCountPrefix(c₂)
  rw [h_succ_eq]
  omega

/-- Matched free (k+1) propagates to the right within the prefix.

    If c₁ is a free (k+1) in the prefix that is NOT unmatched (i.e., matched), and c₂ is also
    a free (k+1) in the prefix to the right of c₁ in the same row, then c₂ is also matched.

    **Proof**: The matching condition for c₁ is:
      freeKCountPrefix + freeKSuccCountUpToPrefix(c₁.col) > freeKSuccCountPrefix
    Since c₁.col < c₂.col and both are in the prefix:
      freeKSuccCountUpToPrefix(c₂.col) ≥ freeKSuccCountUpToPrefix(c₁.col)
    So: freeKCountPrefix + freeKSuccCountUpToPrefix(c₂.col) ≥ freeKCountPrefix + freeKSuccCountUpToPrefix(c₁.col) > freeKSuccCountPrefix
    Hence c₂ is also matched. -/
private lemma matched_kSucc_propagates_right_prefix {lam mu : Fin N → ℕ} (T : Tableau lam mu)
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (h_col : c₁.val.2 < c₂.val.2)
    (h_c₁_free_kSucc_prefix : c₁.val.2 < j ∧ T c₁ = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c₁)
    (_h_c₂_free_kSucc_prefix : c₂.val.2 < j ∧ T c₂ = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c₂)
    (h_c₁_matched : ¬isUnmatchedFreeKSuccPrefix T k hk j c₁) :
    ¬isUnmatchedFreeKSuccPrefix T k hk j c₂ := by
  -- Extract the counting inequality from h_c₁_matched
  unfold isUnmatchedFreeKSuccPrefix at h_c₁_matched ⊢
  push Not at h_c₁_matched
  -- h_c₁_matched: c₁.col < j → T c₁ = k+1 → ¬isForcedKSucc c₁ → freeKCountPrefix + freeKSuccCountUpToPrefix(c₁) > freeKSuccCountPrefix
  have h_gt : freeKSuccCountPrefix T c₁.val.1 k hk j < freeKCountPrefix T c₁.val.1 k hk j + freeKSuccCountUpToPrefix T c₁.val.1 k hk j c₁.val.2 :=
    h_c₁_matched h_c₁_free_kSucc_prefix.1 h_c₁_free_kSucc_prefix.2.1 h_c₁_free_kSucc_prefix.2.2
  -- Monotonicity: freeKSuccCountUpToPrefix(c₁) ≤ freeKSuccCountUpToPrefix(c₂)
  have h_mono : freeKSuccCountUpToPrefix T c₁.val.1 k hk j c₁.val.2 ≤ freeKSuccCountUpToPrefix T c₂.val.1 k hk j c₂.val.2 := by
    rw [h_row]
    exact freeKSuccCountUpToPrefix_mono T c₂.val.1 k hk j c₁.val.2 c₂.val.2 (le_of_lt h_col)
  -- Show c₂ is matched
  intro ⟨_, _, _, h_le⟩
  -- h_le: freeKCountPrefix(c₂.row) + freeKSuccCountUpToPrefix(c₂) ≤ freeKSuccCountPrefix(c₂.row)
  -- Rewrite h_gt to use c₂.val.1
  rw [h_row] at h_gt
  rw [h_row] at h_mono
  -- Contradiction via omega
  omega

/-! ### Cross-boundary case analysis for benderKnuthPrefixMatching

The following lemma addresses the "cross-boundary" case in `benderKnuthPrefixMatching_row_weak_stembridge`:
when c₁ is in the prefix (col < j) and c₂ is in the suffix (col ≥ j).

**Problem**: If c₁ is unmatched free k in the prefix and T c₂ = k in the suffix,
then after transformation: T' c₁ = k+1 > k = T' c₂, violating row-weak.

**Key insight**: In the Stembridge involution, j is chosen as the largest violator column.
This means ν + cont(col_{≥j}(T)) is NOT a partition, but ν + cont(col_{≥j+1}(T)) IS a partition.
The misstep index k is chosen such that (ν + cont(col_{≥j}(T)))_k < (ν + cont(col_{≥j}(T)))_{k+1}.

This structure constrains what values can appear in which columns, potentially ruling out
the problematic cross-boundary case. -/

/-- **Column j has no k entries at max violator**.

When j is the MAX violator column and k is the misstep index for α = ν + cont(col_{≥j}(T)),
column j contains no cells with entry k. This is expressed as:
  contentColGeq T j k = contentColGeq T (j + 1) k

**Context**: In the Stembridge involution:
- j is a violator column (α = ν + cont(col_{≥j}(T)) is not a partition)
- j is the LARGEST violator (β = ν + cont(col_{≥j+1}(T)) IS a partition)
- k is the smallest misstep index (α k < α (k+1))

**Proof idea**:
- From misstep: α k < α (k+1), i.e., ν k + cont(col_{≥j}) k < ν (k+1) + cont(col_{≥j}) (k+1)
- From β partition: β (k+1) ≤ β k, i.e., ν (k+1) + cont(col_{≥j+1}) (k+1) ≤ ν k + cont(col_{≥j+1}) k
- From semistandard: cont(col_{≥j}) i ≤ cont(col_{≥j+1}) i + 1 (at most 1 entry per column)
- From monotonicity: cont(col_{≥j+1}) i ≤ cont(col_{≥j}) i
- Combining these constraints forces cont(col_{≥j}) k = cont(col_{≥j+1}) k -/
lemma column_j_no_k_at_max_violator {lam mu : Fin N → ℕ}
    (nu : Fin N → ℕ)
    (k : Fin N) (_hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (hT : IsSemistandard T)
    -- j is the LARGEST violator, so j+1 gives a partition
    (hbeta : IsNPartition (nu + contentColGeq T (j + 1)))
    -- k is a misstep index for α = ν + cont(col_{≥j}(T))
    (hk_misstep : isMisstep (nu + contentColGeq T j) k) :
    contentColGeq T j k = contentColGeq T (j + 1) k := by
  -- Extract the misstep condition: α k < α (k+1) where α = ν + cont(col_{≥j}(T))
  obtain ⟨hk', hα_misstep⟩ := hk_misstep
  simp only [Pi.add_apply] at hα_misstep
  -- Define k' = k + 1
  let k' : Fin N := ⟨k.val + 1, hk'⟩
  -- Key inequalities from partition and monotonicity
  have hle : k ≤ k' := Fin.mk_le_mk.mpr (Nat.le_succ k.val)
  have hbeta_mono : (nu + contentColGeq T (j + 1)) k' ≤ (nu + contentColGeq T (j + 1)) k :=
    hbeta k k' hle
  simp only [Pi.add_apply] at hbeta_mono
  -- Get the monotonicity and bound lemmas
  have hmono_k := contentColGeq_mono T j k
  have _hmono_kp1 := contentColGeq_mono T j k'
  have hsucc_k := contentColGeq_succ_le T hT j k
  have _hsucc_kp1 := contentColGeq_succ_le T hT j k'
  -- Rewrite hα_misstep to use k'
  have _hα_misstep' : nu k + contentColGeq T j k < nu k' + contentColGeq T j k' := by
    simp only [k']
    exact hα_misstep
  -- The key fact follows from omega combining all constraints
  omega

/-- In the cross-boundary case where c₁ is in the prefix and c₂ is in the suffix,
    if c₁ is an unmatched free k in the prefix, then T c₂ cannot equal k.
    
    This lemma is specific to the **Stembridge involution context** where:
    - `j` is a violator column (i.e., `ν + cont(col_{≥j}(T))` is not a partition)
    - `k` is a misstep index for `α = ν + cont(col_{≥j}(T))` (i.e., `α k < α (k+1)`)
    
    **Proof sketch**:
    - The misstep condition `α k < α (k+1)` means there are more (k+1)'s than k's in col_{≥j}(T)
      (relative to ν)
    - If c₁ is unmatched free k in prefix with T c₂ = k in suffix (same row),
      then the row-weak property of T gives T c₁ ≤ T c₂ = k, so T c₁ = k
    - But c₁ being unmatched means there are excess k's in the prefix
    - Combined with the misstep condition, this leads to a contradiction
    
    **Usage**: This lemma is used in `benderKnuthPrefixMatching_row_weak_stembridge`. -/
private lemma cross_boundary_unmatched_k_not_eq_suffix_k {lam mu : Fin N → ℕ}
    (_hmu : IsNPartition mu)
    (nu : Fin N → ℕ)
    (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (_hj_pos : j > 0) (T : Tableau lam mu) (hT : IsSemistandard T)
    -- Stembridge context: j is a violator column
    (_hj_violator : ¬IsNPartition (nu + contentColGeq T j))
    -- Stembridge context: j is the LARGEST violator, so j+1 gives a partition
    (hbeta : IsNPartition (nu + contentColGeq T (j + 1)))
    -- Stembridge context: k is a misstep index for α = ν + cont(col_{≥j}(T))
    (hk_misstep : isMisstep (nu + contentColGeq T j) k)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (_h_col : c₁.val.2 < c₂.val.2)
    (hc₁_prefix : c₁.val.2 < j) (hc₂_suffix : c₂.val.2 ≥ j)
    (h_unmatched : isUnmatchedFreeKPrefix T k hk j c₁)
    (hT2k : T c₂ = k) : False := by
  -- Extract the misstep condition: α k < α (k+1) where α = ν + cont(col_{≥j}(T))
  obtain ⟨hk', hα_misstep⟩ := hk_misstep
  simp only [Pi.add_apply] at hα_misstep
  
  -- Define k' = k + 1
  let k' : Fin N := ⟨k.val + 1, hk'⟩
  
  -- Key inequalities from partition and monotonicity
  have hle : k ≤ k' := Fin.mk_le_mk.mpr (Nat.le_succ k.val)
  have hbeta_mono : (nu + contentColGeq T (j + 1)) k' ≤ (nu + contentColGeq T (j + 1)) k := 
    hbeta k k' hle
  simp only [Pi.add_apply] at hbeta_mono
  
  -- Get the monotonicity and bound lemmas
  have hmono_k := contentColGeq_mono T j k
  have hmono_kp1 := contentColGeq_mono T j k'
  have hsucc_k := contentColGeq_succ_le T hT j k
  have hsucc_kp1 := contentColGeq_succ_le T hT j k'
  
  -- Rewrite hα_misstep to use k'
  have hα_misstep' : nu k + contentColGeq T j k < nu k' + contentColGeq T j k' := by
    simp only [k']
    exact hα_misstep
  
  -- Key fact: contentColGeq T j k = contentColGeq T (j+1) k (no k's in column j)
  -- This follows from the column_j_no_k_at_max_violator lemma
  have hcontent_k_eq : contentColGeq T j k = contentColGeq T (j + 1) k :=
    column_j_no_k_at_max_violator nu k hk j T hT hbeta ⟨hk', hα_misstep⟩
  
  -- Extract T c₁ = k from the unmatched condition
  have hT1k : T c₁ = k := h_unmatched.2.1
  
  -- Cell at column j in the same row as c₁ and c₂ is in the skew diagram
  have hj_in : (c₁.val.1, j) ∈ skewYoungDiagram lam mu := by
    simp only [skewYoungDiagram, Set.mem_ofPred_eq]
    have hc₁_in := c₁.prop
    have hc₂_in := c₂.prop
    simp only [skewYoungDiagram, Set.mem_ofPred_eq] at hc₁_in hc₂_in
    constructor
    · omega  -- mu c₁.val.1 < c₁.val.2 < j
    · have : lam c₂.val.1 = lam c₁.val.1 := by rw [h_row]
      omega  -- j ≤ c₂.val.2 ≤ lam c₂.val.1 = lam c₁.val.1
  
  let cj : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := ⟨(c₁.val.1, j), hj_in⟩
  
  -- By row-weak, T cj = k (since T c₁ = k and T c₂ = k)
  have hTjk : T cj = k := by
    have hrow_weak := hT.1
    have h1 : T c₁ ≤ T cj := hrow_weak c₁ cj rfl hc₁_prefix
    by_cases hj_eq : j = c₂.val.2
    · have hcj_eq : cj = c₂ := by
        apply Subtype.ext
        exact Prod.ext h_row hj_eq
      rw [hcj_eq, hT2k]
    · have hcj_col : cj.val.2 < c₂.val.2 := by simp only [cj]; omega
      have h2 : T cj ≤ T c₂ := hrow_weak cj c₂ h_row hcj_col
      rw [hT1k] at h1
      rw [hT2k] at h2
      exact Fin.le_antisymm h2 h1
  
  -- Now we derive a contradiction:
  -- hcontent_k_eq says contentColGeq T j k = contentColGeq T (j+1) k
  -- But cj is at column j with entry k, so it contributes to contentColGeq T j k
  -- but not to contentColGeq T (j+1) k (since j < j+1)
  -- So contentColGeq T j k > contentColGeq T (j+1) k, contradicting hcontent_k_eq
  
  -- Define the two sets
  let Sj := {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} // T ⟨c.val, c.prop.1⟩ = k}
  let Sj1 := {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j + 1} // T ⟨c.val, c.prop.1⟩ = k}
  
  -- Finiteness
  haveI hfin_j : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} := by
    apply Set.Finite.to_subtype
    apply Set.Finite.subset (skewYoungDiagram_finite lam mu)
    intro c ⟨hc, _⟩; exact hc
  haveI : Finite Sj := Subtype.finite
  haveI hfin_j1 : Finite {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j + 1} := by
    apply Set.Finite.to_subtype
    apply Set.Finite.subset (skewYoungDiagram_finite lam mu)
    intro c ⟨hc, _⟩; exact hc
  haveI : Finite Sj1 := Subtype.finite
  
  -- Define injection from Sj1 to Sj
  let f : Sj1 → Sj :=
    fun ⟨⟨c, hc_in, hc_ge⟩, hTc⟩ => ⟨⟨c, hc_in, Nat.le_of_succ_le hc_ge⟩, hTc⟩
  
  have hf_inj : Function.Injective f := by
    intro ⟨⟨c1, _, _⟩, _⟩ ⟨⟨c2, _, _⟩, _⟩ h
    have heq : c1 = c2 := by
      have h1 := congrArg (fun x => x.val.val) h
      simp only [f] at h1
      exact h1
    subst heq
    rfl
  
  -- f is not surjective (cj' is not in the range)
  let cj' : Sj := ⟨⟨cj.val, cj.prop, by simp only [cj]; exact le_refl j⟩, hTjk⟩
  
  have hcj'_not_in_range : cj' ∉ Set.range f := by
    intro ⟨⟨⟨cx, hcx_in, hcx_ge⟩, hTcx⟩, hfx⟩
    have heq : cx = cj.val := by
      have h1 := congrArg (fun x => x.val.val) hfx
      simp only [f, cj'] at h1
      exact h1
    rw [heq] at hcx_ge
    simp only [cj] at hcx_ge
    omega
  
  -- Nat.card Sj1 ≤ Nat.card Sj
  have hcard_le : Nat.card Sj1 ≤ Nat.card Sj := Nat.card_le_card_of_injective f hf_inj
  
  -- But hcontent_k_eq says Nat.card Sj = Nat.card Sj1 (unfolding contentColGeq)
  have hcard_eq : Nat.card Sj = Nat.card Sj1 := by
    unfold contentColGeq at hcontent_k_eq
    exact hcontent_k_eq
  
  -- If |Sj1| = |Sj| and f : Sj1 → Sj is injective, then f is bijective
  have hbij : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card f]
    exact ⟨hf_inj, hcard_eq.symm⟩
  
  -- But f is not surjective (cj' is not in range), contradiction
  exact hcj'_not_in_range (hbij.2 cj')

/-- Apply the Bender-Knuth involution BK_k to columns < j of a tableau (matching-based version).

    This definition uses `isUnmatchedFreeKPrefix` and `isUnmatchedFreeKSuccPrefix`
    (which compute matching restricted to columns < j) instead of simple free conditions.
    This is the correct definition that preserves row-weak ordering.

    The matching-based conditions ensure that only unmatched free entries are swapped,
    preserving the row-weak property. See `benderKnuthPrefixMatching_row_weak_stembridge` below. -/
noncomputable def benderKnuthPrefixMatching {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (_hT : IsSemistandard T) : Tableau lam mu := by
  classical
  exact fun c =>
    -- Only apply BK_k transformation to cells in columns < j
    if isUnmatchedFreeKPrefix T k hk j c then
      -- Unmatched free k → k+1
      ⟨k.val + 1, hk⟩
    else if isUnmatchedFreeKSuccPrefix T k hk j c then
      -- Unmatched free k+1 → k
      k
    else
      -- All other cells unchanged
      T c

/-- benderKnuthPrefixMatching agrees with the original tableau on columns ≥ j. -/
theorem benderKnuthPrefixMatching_eq_on_suffix {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}) (hc : c.val.2 ≥ j) :
    benderKnuthPrefixMatching k hk j T hT c = T c := by
  unfold benderKnuthPrefixMatching isUnmatchedFreeKPrefix isUnmatchedFreeKSuccPrefix
  simp only [not_lt.mpr hc, false_and, ↓reduceIte]

/-! ### Count swap lemmas for benderKnuthPrefixMatching

After applying `benderKnuthPrefixMatching`, the counts of free k's and free (k+1)'s swap.
These are the prefix-restricted versions of `freeKCount_benderKnuth` and `freeKSuccCount_benderKnuth`.

**Key results** (now proved):
- `freeKCountPrefix_benderKnuthPrefixMatching`: freeKCountPrefix T' = freeKSuccCountPrefix T
- `freeKSuccCountPrefix_benderKnuthPrefixMatching`: freeKSuccCountPrefix T' = freeKCountPrefix T

These lemmas, combined with the cardinality lemmas in the previous section, are used in
`benderKnuthPrefixMatching_involutive_stembridge`. -/

/-- After benderKnuthPrefixMatching, the count of free k's in the prefix equals
    the original count of free (k+1)'s in the prefix.
    
    **Proof strategy**: Free k's in T' = matched free k's from T + unmatched free (k+1)'s from T
    - #{matched free k's} = min(m, n) (by matchedFreeKPrefix_row_card)
    - #{unmatched free (k+1)'s} = n - min(m, n) (by unmatchedFreeKSuccPrefix_row_card)
    - Total = min(m, n) + (n - min(m, n)) = n = freeKSuccCountPrefix T -/
private lemma freeKCountPrefix_benderKnuthPrefixMatching {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T) (i : Fin N) :
    freeKCountPrefix (benderKnuthPrefixMatching k hk j T hT) i k hk j = freeKSuccCountPrefix T i k hk j := by
  -- Proof strategy (adapting freeKCount_benderKnuth):
  -- 1. Show that free k's in T' (in prefix) = matched free k's from T ∪ unmatched free (k+1)'s from T
  --    - Matched free k's stay as k (not unmatched, so unchanged)
  --    - Unmatched free (k+1)'s become k
  --    - Unmatched free k's become k+1 (not in the set)
  --    - Other cells are unchanged
  -- 2. These sets are disjoint (T c = k vs T c = k+1)
  -- 3. Use cardinality lemmas:
  --    - #{matched free k's} = min(m, n) by matchedFreeKPrefix_row_card
  --    - #{unmatched free (k+1)'s} = n - min(m, n) by unmatchedFreeKSuccPrefix_row_card
  -- 4. Total = min(m, n) + (n - min(m, n)) = n = freeKSuccCountPrefix T
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  let T' := benderKnuthPrefixMatching k hk j T hT
  set m := freeKCountPrefix T i k hk j with hm_def
  set n := freeKSuccCountPrefix T i k hk j with hn_def
  
  -- Define the sets
  let A : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ isMatchedFreeKPrefix T k hk j c}
  let B : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ isUnmatchedFreeKSuccPrefix T k hk j c}
  let LHS : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
    {c | c.val.1 = i ∧ c.val.2 < j ∧ T' c = k ∧ ¬isForcedK T' k hk c}
  
  -- Get cardinalities
  have h_matchedK : Nat.card A = min m n := matchedFreeKPrefix_row_card T i k hk j
  have h_unmatchedKSucc : Nat.card B = n - min m n := unmatchedFreeKSuccPrefix_row_card T i k hk j
  
  -- Disjointness (A has T c = k, B has T c = k+1)
  have h_disj : Disjoint A B := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨_, hA⟩, ⟨_, hB⟩⟩
    have h1 : T c = k := hA.2.1
    have h2 : T c = ⟨k.val + 1, hk⟩ := hB.2.1
    rw [h1] at h2
    simp only [Fin.ext_iff] at h2
    omega
  
  -- The key set equality: LHS = A ∪ B
  have h_LHS_eq : LHS = A ∪ B := by
    ext c
    simp only [Set.mem_ofPred_eq, Set.mem_union, LHS, A, B]
    constructor
    · intro ⟨hrow, hcol, hT'c, hfree'⟩
      -- T' c = k in the prefix. Analyze how this happens.
      -- First, determine what T' c is based on the matching conditions
      by_cases h_unmatched_k : isUnmatchedFreeKPrefix T k hk j c
      · -- c was unmatched free k in T, so T' c = k+1, contradiction with T' c = k
        have hT'c_kSucc : T' c = ⟨k.val + 1, hk⟩ := by
          simp only [T', benderKnuthPrefixMatching, h_unmatched_k, ↓reduceIte]
        rw [hT'c_kSucc] at hT'c
        simp only [Fin.ext_iff] at hT'c
        omega
      · by_cases h_unmatched_kSucc : isUnmatchedFreeKSuccPrefix T k hk j c
        · -- c was unmatched free (k+1) in T, so T' c = k ✓
          right
          exact ⟨hrow, h_unmatched_kSucc⟩
        · -- c was unchanged, so T' c = T c
          have hT'c_eq : T' c = T c := by
            simp only [T', benderKnuthPrefixMatching, h_unmatched_k, h_unmatched_kSucc, ↓reduceIte]
          -- So T c = k
          have hTc : T c = k := by rw [← hT'c_eq]; exact hT'c
          left
          refine ⟨hrow, hcol, hTc, ?_, ?_⟩
          · -- ¬isForcedK T k hk c
            intro hforced
            obtain ⟨hval, c_below, h_col, h_row, hT_below⟩ := hforced
            -- c is forced in T means there's k+1 directly below
            have hcb_col : c_below.val.2 < j := by rw [h_col]; exact hcol
            -- Check if c_below is unmatched free k or unmatched free (k+1)
            by_cases hcb_k : isUnmatchedFreeKPrefix T k hk j c_below
            · -- c_below was unmatched free k in T, so T c_below = k
              have : T c_below = k := hcb_k.2.1
              rw [hT_below] at this
              simp only [Fin.ext_iff] at this
              omega
            · by_cases hcb_kSucc : isUnmatchedFreeKSuccPrefix T k hk j c_below
              · -- c_below was unmatched free (k+1) in T
                -- But c is directly above c_below with T c = k
                -- So c_below is forced as (k+1), contradicting isUnmatchedFreeKSuccPrefix
                have hcb_forced : isForcedKSucc T k hk c_below := ⟨hcb_kSucc.2.1, c, h_col.symm, h_row, hTc⟩
                exact hcb_kSucc.2.2.1 hcb_forced
              · -- c_below was unchanged, so T' c_below = T c_below = k+1
                have hT'cb : T' c_below = T c_below := by
                  simp only [T', benderKnuthPrefixMatching, hcb_k, hcb_kSucc, ↓reduceIte]
                rw [hT_below] at hT'cb
                -- c is forced in T' (since T' c_below = k+1)
                apply hfree'
                exact ⟨hT'c, c_below, h_col, h_row, hT'cb⟩
          · -- ¬isUnmatchedFreeKPrefix T k hk j c
            exact h_unmatched_k
    · intro h
      rcases h with ⟨hrow, hmatched⟩ | ⟨hrow, hunmatched⟩
      · -- c is matched free k in T (in prefix)
        have hcol : c.val.2 < j := hmatched.1
        have hval : T c = k := hmatched.2.1
        have hfree : ¬isForcedK T k hk c := hmatched.2.2.1
        have h_not_unmatched : ¬isUnmatchedFreeKPrefix T k hk j c := hmatched.2.2.2
        -- T' c = T c = k (since c is not unmatched)
        have hT'c : T' c = k := by
          simp only [T', benderKnuthPrefixMatching]
          simp only [h_not_unmatched, ↓reduceIte]
          -- Also need to show c is not unmatched (k+1), which is true since T c = k
          have h_not_kSucc : ¬isUnmatchedFreeKSuccPrefix T k hk j c := by
            intro h
            have : T c = ⟨k.val + 1, hk⟩ := h.2.1
            rw [hval] at this
            simp only [Fin.ext_iff] at this
            omega
          simp only [h_not_kSucc, ↓reduceIte, hval]
        refine ⟨hrow, hcol, hT'c, ?_⟩
        -- Need: ¬isForcedK T' k hk c
        intro hforced'
        obtain ⟨_, c_below, h_col, h_row, hT'_below⟩ := hforced'
        -- By column-strictness in T, T c < T c_below
        have h_lt : T c < T c_below := hT.2 c c_below h_col.symm (by simp only [Fin.lt_def]; omega)
        rw [hval] at h_lt
        -- So T c_below > k, hence T c_below ≥ k+1
        have h_ge_kSucc : (T c_below).val ≥ k.val + 1 := h_lt
        have hcb_col : c_below.val.2 < j := by rw [h_col]; exact hcol
        -- Analyze T' c_below
        by_cases hcb_k : isUnmatchedFreeKPrefix T k hk j c_below
        · -- c_below was unmatched free k in T, so T c_below = k
          have : T c_below = k := hcb_k.2.1
          simp only [this, Fin.lt_def] at h_lt
          omega
        · by_cases hcb_kSucc : isUnmatchedFreeKSuccPrefix T k hk j c_below
          · -- c_below was unmatched free (k+1) in T, so T' c_below = k
            have hT'cb : T' c_below = k := by
              simp only [T', benderKnuthPrefixMatching, hcb_k, hcb_kSucc, ↓reduceIte]
            rw [hT'cb] at hT'_below
            simp only [Fin.ext_iff] at hT'_below
            omega
          · -- c_below was unchanged, so T' c_below = T c_below
            have hT'cb : T' c_below = T c_below := by
              simp only [T', benderKnuthPrefixMatching, hcb_k, hcb_kSucc, ↓reduceIte]
            rw [hT'cb] at hT'_below
            -- T' c_below = k+1 means T c_below = k+1
            -- But then c was forced in T (contradiction with hfree)
            exact hfree ⟨hval, c_below, h_col, h_row, hT'_below⟩
      · -- c is unmatched free (k+1) in T (in prefix)
        have hcol : c.val.2 < j := hunmatched.1
        have hval : T c = ⟨k.val + 1, hk⟩ := hunmatched.2.1
        have hfree : ¬isForcedKSucc T k hk c := hunmatched.2.2.1
        -- T' c = k (since c is unmatched (k+1))
        have hT'c : T' c = k := by
          simp only [T', benderKnuthPrefixMatching]
          -- First show c is not unmatched free k (since T c = k+1 ≠ k)
          have h_not_k : ¬isUnmatchedFreeKPrefix T k hk j c := by
            intro h
            have : T c = k := h.2.1
            rw [hval] at this
            simp only [Fin.ext_iff] at this
            omega
          simp only [h_not_k, hunmatched, ↓reduceIte]
        refine ⟨hrow, hcol, hT'c, ?_⟩
        -- Need: ¬isForcedK T' k hk c
        intro hforced'
        obtain ⟨_, c_below, h_col, h_row, hT'_below⟩ := hforced'
        -- By column-strictness in T, T c < T c_below
        have h_lt : T c < T c_below := hT.2 c c_below h_col.symm (by simp only [Fin.lt_def]; omega)
        rw [hval] at h_lt
        -- So T c_below > k+1
        have h_gt_kSucc : (T c_below).val > k.val + 1 := h_lt
        have hcb_col : c_below.val.2 < j := by rw [h_col]; exact hcol
        -- Analyze T' c_below
        by_cases hcb_k : isUnmatchedFreeKPrefix T k hk j c_below
        · -- c_below was unmatched free k in T, so T c_below = k
          have : T c_below = k := hcb_k.2.1
          simp only [this, Fin.lt_def] at h_lt
          omega
        · by_cases hcb_kSucc : isUnmatchedFreeKSuccPrefix T k hk j c_below
          · -- c_below was unmatched free (k+1) in T, so T c_below = k+1
            have : T c_below = ⟨k.val + 1, hk⟩ := hcb_kSucc.2.1
            simp only [this, Fin.lt_def] at h_lt
            omega
          · -- c_below was unchanged, so T' c_below = T c_below
            have hT'cb : T' c_below = T c_below := by
              simp only [T', benderKnuthPrefixMatching, hcb_k, hcb_kSucc, ↓reduceIte]
            rw [hT'cb] at hT'_below
            -- T' c_below = k+1 means T c_below = k+1
            -- But T c_below > k+1, contradiction
            simp only [Fin.ext_iff] at hT'_below
            omega
  
  -- Use disjoint union cardinality (via ncard)
  have h_ncard : (A ∪ B).ncard = A.ncard + B.ncard := Set.ncard_union_eq h_disj
  
  -- Convert goal to ncard form
  change LHS.ncard = n
  rw [h_LHS_eq, h_ncard]
  
  -- Now use the cardinality facts
  have hA : A.ncard = min m n := h_matchedK
  have hB : B.ncard = n - min m n := h_unmatchedKSucc
  rw [hA, hB]
  
  -- Now we have: min m n + (n - min m n) = n
  omega

/-- After benderKnuthPrefixMatching, the count of free (k+1)'s in the prefix equals
    the original count of free k's in the prefix.
    
    **Proof strategy**: Free (k+1)'s in T' = matched free (k+1)'s from T + unmatched free k's from T
    - #{matched free (k+1)'s} = min(m, n) (by matchedFreeKSuccPrefix_row_card)
    - #{unmatched free k's} = m - min(m, n) (by unmatchedFreeKPrefix_row_card)
    - Total = min(m, n) + (m - min(m, n)) = m = freeKCountPrefix T -/
private lemma freeKSuccCountPrefix_benderKnuthPrefixMatching {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T) (i : Fin N) :
    freeKSuccCountPrefix (benderKnuthPrefixMatching k hk j T hT) i k hk j = freeKCountPrefix T i k hk j := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  set m := freeKCountPrefix T i k hk j with hm_def
  set n := freeKSuccCountPrefix T i k hk j with hn_def
  
  -- Helper: how benderKnuthPrefixMatching transforms a cell
  have hT'_def : ∀ c, benderKnuthPrefixMatching k hk j T hT c = 
      if isUnmatchedFreeKPrefix T k hk j c then ⟨k.val + 1, hk⟩
      else if isUnmatchedFreeKSuccPrefix T k hk j c then k
      else T c := by
    intro c
    unfold benderKnuthPrefixMatching
    simp only
  
  -- Define the key sets
  let A : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ isMatchedFreeKSuccPrefix T k hk j c}
  let B : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.1 = i ∧ isUnmatchedFreeKPrefix T k hk j c}
  let LHS : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
    {c | c.val.1 = i ∧ c.val.2 < j ∧ benderKnuthPrefixMatching k hk j T hT c = ⟨k.val + 1, hk⟩ ∧ 
         ¬isForcedKSucc (benderKnuthPrefixMatching k hk j T hT) k hk c}
  
  -- Step 1: Establish set equality LHS = A ∪ B
  have h_union : LHS = A ∪ B := by
    ext c
    simp only [Set.mem_union]
    constructor
    · -- (→) If c is a free (k+1) in T' in prefix, show it was matched free (k+1) or unmatched free k in T
      intro ⟨hrow, hcol, hT'c, hfree'⟩
      rw [hT'_def] at hT'c
      by_cases h_unmatchedK : isUnmatchedFreeKPrefix T k hk j c
      · -- Case: c was unmatched free k in T
        right
        exact ⟨hrow, h_unmatchedK⟩
      · -- Case: c was NOT unmatched free k in T
        simp only [h_unmatchedK, ↓reduceIte] at hT'c
        by_cases h_unmatchedKSucc : isUnmatchedFreeKSuccPrefix T k hk j c
        · -- c was unmatched free (k+1) in T, so T' c = k, contradiction
          simp only [h_unmatchedKSucc, ↓reduceIte, Fin.ext_iff] at hT'c
          omega
        · -- c was neither unmatched free k nor unmatched free (k+1), so T' c = T c
          simp only [h_unmatchedKSucc, ↓reduceIte] at hT'c
          -- hT'c is now: T c = k+1
          -- We need to reconstruct the T' c = k+1 fact
          have hT'c_orig : benderKnuthPrefixMatching k hk j T hT c = ⟨k.val + 1, hk⟩ := by
            rw [hT'_def]
            simp only [h_unmatchedK, h_unmatchedKSucc, ↓reduceIte]
            exact hT'c
          left
          refine ⟨hrow, hcol, hT'c, ?_, h_unmatchedKSucc⟩
          -- Show c was not forced in T
          intro hforced
          apply hfree'
          obtain ⟨hTc_ksucc, c_above, hc_col, hc_row, hTc_above_k⟩ := hforced
          -- Show T' c_above = k (so c is forced in T')
          have h_above_unchanged : benderKnuthPrefixMatching k hk j T hT c_above = T c_above := by
            rw [hT'_def]
            by_cases h1 : isUnmatchedFreeKPrefix T k hk j c_above
            · -- c_above is unmatched free k → contradiction (c_above would be forced)
              exfalso
              have hT_above : T c_above = k := h1.2.1
              have h_not_forced : ¬isForcedK T k hk c_above := h1.2.2.1
              have h_forced_above : isForcedK T k hk c_above := ⟨hT_above, c, hc_col.symm, hc_row, hTc_ksucc⟩
              exact h_not_forced h_forced_above
            · simp only [h1, ↓reduceIte]
              by_cases h2 : isUnmatchedFreeKSuccPrefix T k hk j c_above
              · -- c_above is unmatched free (k+1) → contradiction (T c_above = k+1 ≠ k)
                exfalso
                have hT_above_ksucc : T c_above = ⟨k.val + 1, hk⟩ := h2.2.1
                rw [hTc_above_k] at hT_above_ksucc
                simp only [Fin.ext_iff] at hT_above_ksucc
                omega
              · simp only [h2, ↓reduceIte]
          have h_T'_above_k : benderKnuthPrefixMatching k hk j T hT c_above = k := h_above_unchanged.trans hTc_above_k
          exact ⟨hT'c_orig, c_above, hc_col, hc_row, h_T'_above_k⟩
    · -- (←) If c was matched free (k+1) or unmatched free k, show it's free (k+1) in T'
      intro h
      rcases h with ⟨hrow, hmatched⟩ | ⟨hrow, hunmatched⟩
      · -- Case: c was a matched free (k+1) in T
        obtain ⟨hcol, hTc, hfree, h_not_unmatched⟩ := hmatched
        refine ⟨hrow, hcol, ?_, ?_⟩
        · -- T' c = k+1
          rw [hT'_def]
          have h_not_unmatchedK : ¬isUnmatchedFreeKPrefix T k hk j c := by
            intro h
            have hTc_k : T c = k := h.2.1
            rw [hTc] at hTc_k
            simp only [Fin.ext_iff] at hTc_k
            omega
          simp only [h_not_unmatchedK, h_not_unmatched, ↓reduceIte]
          exact hTc
        · -- c is not forced in T'
          intro hforced'
          obtain ⟨_, c_above, hc_col, hc_row, hT'_above_k⟩ := hforced'
          rw [hT'_def] at hT'_above_k
          by_cases h1 : isUnmatchedFreeKPrefix T k hk j c_above
          · simp only [h1, ↓reduceIte, Fin.ext_iff] at hT'_above_k
            omega
          · simp only [h1, ↓reduceIte] at hT'_above_k
            by_cases h2 : isUnmatchedFreeKSuccPrefix T k hk j c_above
            · -- c_above was unmatched free (k+1) → column-strict contradiction
              simp only [h2, ↓reduceIte] at hT'_above_k
              have hT_above_ksucc : T c_above = ⟨k.val + 1, hk⟩ := h2.2.1
              have h_col_strict : T c_above < T c := hT.2 c_above c hc_col (by simp only [Fin.lt_def] at hc_row ⊢; omega)
              rw [hT_above_ksucc, hTc] at h_col_strict
              simp only [Fin.lt_def] at h_col_strict
              omega
            · simp only [h2, ↓reduceIte] at hT'_above_k
              have hforced : isForcedKSucc T k hk c := ⟨hTc, c_above, hc_col, hc_row, hT'_above_k⟩
              exact hfree hforced
      · -- Case: c was an unmatched free k in T
        obtain ⟨hcol, hTc, hfree, h_unmatched⟩ := hunmatched
        have h_isUnmatchedFreeKPrefix : isUnmatchedFreeKPrefix T k hk j c := ⟨hcol, hTc, hfree, h_unmatched⟩
        refine ⟨hrow, hcol, ?_, ?_⟩
        · -- T' c = k+1 (unmatched free k becomes k+1)
          rw [hT'_def]
          simp only [h_isUnmatchedFreeKPrefix, ↓reduceIte]
        · -- c is not forced in T' (no k above it)
          intro hforced'
          obtain ⟨_, c_above, hc_col, hc_row, hT'_above_k⟩ := hforced'
          rw [hT'_def] at hT'_above_k
          by_cases h1 : isUnmatchedFreeKPrefix T k hk j c_above
          · -- c_above was unmatched free k → T' c_above = k+1 ≠ k
            simp only [h1, ↓reduceIte, Fin.ext_iff] at hT'_above_k
            omega
          · simp only [h1, ↓reduceIte] at hT'_above_k
            by_cases h2 : isUnmatchedFreeKSuccPrefix T k hk j c_above
            · -- c_above was unmatched free (k+1) → column-strict contradiction
              simp only [h2, ↓reduceIte] at hT'_above_k
              have hT_above_ksucc : T c_above = ⟨k.val + 1, hk⟩ := h2.2.1
              have h_col_strict : T c_above < T c := hT.2 c_above c hc_col (by simp only [Fin.lt_def] at hc_row ⊢; omega)
              rw [hT_above_ksucc, hTc] at h_col_strict
              simp only [Fin.lt_def] at h_col_strict
              omega
            · simp only [h2, ↓reduceIte] at hT'_above_k
              -- T c_above = k, but by column-strict T c_above < T c = k, contradiction
              have h_col_strict : T c_above < T c := hT.2 c_above c hc_col (by simp only [Fin.lt_def] at hc_row ⊢; omega)
              rw [hT'_above_k, hTc] at h_col_strict
              simp only [Fin.lt_def] at h_col_strict
              omega
  
  -- Step 2: Disjointness: A and B are disjoint (different original values)
  have h_disj : Disjoint A B := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨_, hA⟩, ⟨_, hB⟩⟩
    have h1 : T c = ⟨k.val + 1, hk⟩ := hA.2.1
    have h2 : T c = k := hB.2.1
    rw [h1] at h2
    simp only [Fin.ext_iff] at h2
    omega
  
  -- Step 3: Get cardinalities
  have h_matchedKSucc : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isMatchedFreeKSuccPrefix T k hk j c} = min m n := matchedFreeKSuccPrefix_row_card T i k hk j
  have h_unmatchedK : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
      c.val.1 = i ∧ isUnmatchedFreeKPrefix T k hk j c} = m - min m n := unmatchedFreeKPrefix_row_card T i k hk j
  
  -- Step 4: Compute the final result
  show Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} //
      c.val.1 = i ∧ c.val.2 < j ∧ benderKnuthPrefixMatching k hk j T hT c = ⟨k.val + 1, hk⟩ ∧ 
      ¬isForcedKSucc (benderKnuthPrefixMatching k hk j T hT) k hk c} = m
  
  -- Use disjoint union cardinality (via ncard)
  have h_ncard : (A ∪ B).ncard = A.ncard + B.ncard := Set.ncard_union_eq h_disj
  
  change LHS.ncard = m
  rw [h_union, h_ncard]
  
  have hA : A.ncard = min m n := h_matchedKSucc
  have hB : B.ncard = m - min m n := h_unmatchedK
  rw [hA, hB]
  omega

/-- If c is not an unmatched free k or unmatched free (k+1) in the prefix, then
    benderKnuthPrefixMatching leaves c unchanged. -/
private lemma benderKnuthPrefixMatching_unchanged' {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_not_unmatchedK : ¬isUnmatchedFreeKPrefix T k hk j c)
    (h_not_unmatchedKSucc : ¬isUnmatchedFreeKSuccPrefix T k hk j c) :
    benderKnuthPrefixMatching k hk j T hT c = T c := by
  unfold benderKnuthPrefixMatching
  simp only [h_not_unmatchedK, h_not_unmatchedKSucc, ↓reduceIte]

/-- An unmatched free k in the prefix becomes a free (k+1) in T' (not forced).
    This is the prefix-restricted version of `unmatched_k_becomes_free_kSucc'`. -/
private lemma unmatched_k_becomes_free_kSucc_prefix' {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hunmatched : isUnmatchedFreeKPrefix T k hk j c) :
    let T' := benderKnuthPrefixMatching k hk j T hT
    ¬isForcedKSucc T' k hk c := by
  intro T' hforced'
  obtain ⟨_, c_above, h_col, h_row, hT'_above⟩ := hforced'
  -- hunmatched gives us: c.col < j, T c = k, ¬isForcedK T k hk c
  have hval := hunmatched.2.1
  have hcol_lt_j := hunmatched.1
  -- By column-strict in T: T c_above < T c = k
  have h_lt : T c_above < T c := hT.2 c_above c h_col (by simp only [Fin.lt_def]; omega)
  rw [hval] at h_lt
  -- So T c_above < k, meaning T c_above ≠ k and T c_above ≠ k+1
  have h_ne_k : T c_above ≠ k := Fin.ne_of_lt h_lt
  have h_ne_k1 : T c_above ≠ ⟨k.val + 1, hk⟩ := by
    intro h; rw [h] at h_lt; simp only [Fin.lt_def] at h_lt; omega
  -- c_above has the same column as c, which is < j
  have hcol_above : c_above.val.2 = c.val.2 := h_col
  have hcol_above_lt_j : c_above.val.2 < j := by rw [hcol_above]; exact hcol_lt_j
  -- c_above is not unmatched free k (since T c_above < k)
  have h_not_unmatchedK : ¬isUnmatchedFreeKPrefix T k hk j c_above := by
    intro h
    have := h.2.1
    rw [this] at h_lt
    simp only [Fin.lt_def] at h_lt
    omega
  -- c_above is not unmatched free (k+1) (since T c_above < k < k+1)
  have h_not_unmatchedKSucc : ¬isUnmatchedFreeKSuccPrefix T k hk j c_above := by
    intro h
    have := h.2.1
    rw [this] at h_lt
    simp only [Fin.lt_def] at h_lt
    omega
  -- So T' c_above = T c_above
  have hT'_eq : T' c_above = T c_above := benderKnuthPrefixMatching_unchanged' k hk j T hT c_above
    h_not_unmatchedK h_not_unmatchedKSucc
  rw [hT'_eq] at hT'_above
  exact h_ne_k hT'_above

/-- A matched free (k+1) in the prefix stays as (k+1) in T'.
    This is the prefix-restricted version of staying unchanged for matched cells. -/
private lemma matched_kSucc_stays_kSucc_prefix' {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hmatched : isMatchedFreeKSuccPrefix T k hk j c) :
    benderKnuthPrefixMatching k hk j T hT c = ⟨k.val + 1, hk⟩ := by
  -- A matched free (k+1) is not unmatched free k or unmatched free (k+1)
  have h_not_unmatchedK : ¬isUnmatchedFreeKPrefix T k hk j c := by
    intro h
    have h1 := h.2.1  -- T c = k
    have h2 := hmatched.2.1  -- T c = k+1
    rw [h1] at h2
    simp only [Fin.ext_iff] at h2
    omega
  have h_not_unmatchedKSucc : ¬isUnmatchedFreeKSuccPrefix T k hk j c := by
    intro h
    -- hmatched says c is matched (¬isUnmatchedFreeKSuccPrefix)
    exact hmatched.2.2.2 h
  rw [benderKnuthPrefixMatching_unchanged' k hk j T hT c h_not_unmatchedK h_not_unmatchedKSucc]
  exact hmatched.2.1

/-- Helper lemma: In a semistandard tableau with partition shape, if c₁ and c₂ are in the
    same row with c₁.col < c₂.col, and c₂ is forced (has k+1 directly below), then
    c₁ is also forced.

    This is a key lemma for proving row-weak preservation of benderKnuthPrefixMatching.

    Proof: By partition property (mu weakly decreasing), if (row+1, c₂.col) is in the
    diagram, then (row+1, c₁.col) is also in the diagram. By row-weak on row+1:
    T(row+1, c₁.col) ≤ T(row+1, c₂.col) = k+1. By column-strict: T(row, c₁.col) < T(row+1, c₁.col).
    If T c₁ = k, then T(row+1, c₁.col) > k, so T(row+1, c₁.col) = k+1, making c₁ forced. -/
private lemma row_forced_propagates_left' {lam mu : Fin N → ℕ}
    (hmu : IsNPartition mu)
    (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hrow : c₁.val.1 = c₂.val.1) (hcol : c₁.val.2 < c₂.val.2)
    (hc₁_k : T c₁ = k) (hc₂_forced : isForcedK T k hk c₂) :
    isForcedK T k hk c₁ := by
  obtain ⟨hc₂_k, c₂_below, hc₂b_col, hc₂b_row, hc₂b_ksucc⟩ := hc₂_forced
  have hi : c₁.val.1.val + 1 < N := by
    have := c₂_below.val.1.isLt
    have heq : c₁.val.1.val = c₂.val.1.val := by
      simp only [Fin.ext_iff] at hrow
      exact hrow
    rw [heq]
    omega
  have h_c₁b_mem : (⟨c₁.val.1.val + 1, hi⟩, c₁.val.2) ∈ skewYoungDiagram lam mu := by
    apply skewYoungDiagram_cell_below_exists' hmu c₁.val.1 hi c₁.val.2 c₂.val.2 hcol c₁.prop
    convert c₂_below.prop using 1
    ext
    · simp only [Fin.ext_iff] at hrow ⊢
      omega
    · simp only [hc₂b_col]
  let c₁_below : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
    ⟨(⟨c₁.val.1.val + 1, hi⟩, c₁.val.2), h_c₁b_mem⟩
  have h_row_weak : T c₁_below ≤ T c₂_below := by
    apply hT.1 c₁_below c₂_below
    · simp only [c₁_below, Fin.ext_iff] at hrow ⊢
      omega
    · simp only [c₁_below, hc₂b_col]; exact hcol
  rw [hc₂b_ksucc] at h_row_weak
  have h_col_strict : T c₁ < T c₁_below := by
    apply hT.2 c₁ c₁_below
    · simp only [c₁_below]
    · simp only [c₁_below, Fin.lt_def]; omega
  rw [hc₁_k] at h_col_strict
  have h_c₁b_ksucc : T c₁_below = ⟨k.val + 1, hk⟩ := by
    apply Fin.ext
    have h1' : k.val < (T c₁_below).val := h_col_strict
    have h2' : (T c₁_below).val ≤ k.val + 1 := h_row_weak
    simp only
    omega
  exact ⟨hc₁_k, c₁_below, rfl, rfl, h_c₁b_ksucc⟩

/-- Symmetric helper: if (i, j₁) and (i-1, j₂) are in the diagram with j₁ > j₂,
    then (i-1, j₁) is also in the diagram. Requires lam to be a partition. -/
private lemma skewYoungDiagram_cell_above_exists'' {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam)
    (i : Fin N) (hi : 0 < i.val) (j₁ j₂ : ℕ) (hj : j₂ < j₁)
    (h1 : ((i, j₁) : Fin N × ℕ) ∈ skewYoungDiagram lam mu)
    (h2 : ((⟨i.val - 1, by omega⟩ : Fin N), j₂) ∈ skewYoungDiagram lam mu) :
    ((⟨i.val - 1, by omega⟩ : Fin N), j₁) ∈ skewYoungDiagram lam mu := by
  simp only [skewYoungDiagram, Set.mem_ofPred_eq] at h1 h2 ⊢
  constructor
  · omega
  · have hlam_le : lam i ≤ lam ⟨i.val - 1, by omega⟩ := hlam ⟨i.val - 1, by omega⟩ i (by simp only [Fin.le_def]; omega)
    omega

/-- Forced k+1 propagates to the right: if c₂ is forced k+1 and c₁ is to the right
    of c₂ in the same row with T c₁ = k+1, then c₁ is also forced k+1.
    
    This is the symmetric version of `row_forced_propagates_left'` for isForcedKSucc.
    
    Proof: c₂ has a k directly above it (c₂_above). By row-weak, the cell above c₁
    has value ≥ k. By column-strict, it has value < k+1. So it equals k, and c₁ is forced. -/
private lemma row_forcedKSucc_propagates_right' {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam)
    (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hrow : c₁.val.1 = c₂.val.1) (hcol : c₂.val.2 < c₁.val.2)
    (hc₁_ksucc : T c₁ = ⟨k.val + 1, hk⟩) (hc₂_forced : isForcedKSucc T k hk c₂) :
    isForcedKSucc T k hk c₁ := by
  obtain ⟨hc₂_ksucc, c₂_above, hc₂a_col, hc₂a_row, hc₂a_k⟩ := hc₂_forced
  -- c₁.val.1.val > 0 since c₂_above is one row above c₂ and c₁.row = c₂.row
  have hi : 0 < c₁.val.1.val := by
    have heq : c₁.val.1.val = c₂.val.1.val := by simp only [Fin.ext_iff] at hrow; exact hrow
    rw [heq]
    omega
  -- The cell above c₁ exists in the diagram
  have h_c₁a_mem : (⟨c₁.val.1.val - 1, by omega⟩, c₁.val.2) ∈ skewYoungDiagram lam mu := by
    apply skewYoungDiagram_cell_above_exists'' hlam c₁.val.1 hi c₁.val.2 c₂.val.2 hcol c₁.prop
    convert c₂_above.prop using 1
    ext
    · simp only [Fin.ext_iff] at hrow ⊢
      omega
    · simp only [hc₂a_col]
  let c₁_above : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} :=
    ⟨(⟨c₁.val.1.val - 1, by omega⟩, c₁.val.2), h_c₁a_mem⟩
  -- By row-weak: T c₂_above ≤ T c₁_above
  have h_row_weak : T c₂_above ≤ T c₁_above := by
    apply hT.1 c₂_above c₁_above
    · simp only [c₁_above, Fin.ext_iff] at hrow ⊢
      omega
    · simp only [c₁_above, hc₂a_col]; exact hcol
  rw [hc₂a_k] at h_row_weak
  -- By column-strict: T c₁_above < T c₁
  have h_col_strict : T c₁_above < T c₁ := by
    apply hT.2 c₁_above c₁
    · simp only [c₁_above]
    · simp only [c₁_above, Fin.lt_def]; omega
  rw [hc₁_ksucc] at h_col_strict
  -- Combine: k ≤ T c₁_above < k+1 implies T c₁_above = k
  have h_c₁a_k : T c₁_above = k := by
    apply Fin.ext
    simp only [Fin.le_def] at h_row_weak
    simp only [Fin.lt_def] at h_col_strict
    omega
  exact ⟨hc₁_ksucc, c₁_above, rfl, by simp only [c₁_above]; omega, h_c₁a_k⟩


/-- Row-weak preservation for benderKnuthPrefixMatching in the Stembridge involution context.

    This version includes the Stembridge context hypotheses needed to handle the cross-boundary
    case where c₁ is in the prefix and c₂ is in the suffix.

    The key additional hypotheses are:
    - `nu`: the base partition for the Yamanouchi condition
    - `hj_pos`: j > 0 (the violator column is positive)
    - `hbeta`: ν + cont(col_{≥j+1}(T)) is a partition (j is the LARGEST violator)
    - `hk_misstep`: k is a misstep index for α = ν + cont(col_{≥j}(T))

    These hypotheses allow us to use `cross_boundary_unmatched_k_not_eq_suffix_k` to rule out
    the problematic case where c₁ is unmatched free k and T c₂ = k. -/
private lemma benderKnuthPrefixMatching_row_weak_stembridge {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (nu : Fin N → ℕ)
    (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (hj_pos : j > 0) (T : Tableau lam mu) (hT : IsSemistandard T)
    -- Stembridge context: j is the LARGEST violator, so j+1 gives a partition
    (hbeta : IsNPartition (nu + contentColGeq T (j + 1)))
    -- Stembridge context: k is a misstep index for α = ν + cont(col_{≥j}(T))
    (hk_misstep : isMisstep (nu + contentColGeq T j) k)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1) (h_col : c₁.val.2 < c₂.val.2) :
    benderKnuthPrefixMatching k hk j T hT c₁ ≤ benderKnuthPrefixMatching k hk j T hT c₂ := by
  have hT_weak : T c₁ ≤ T c₂ := hT.1 c₁ c₂ h_row h_col
  -- Case split on whether c₁ and c₂ are in prefix or suffix
  by_cases hc₁j : c₁.val.2 < j
  · -- c₁ is in prefix
    by_cases hc₂j : c₂.val.2 < j
    · -- Both in prefix: use matching-based argument
      unfold benderKnuthPrefixMatching
      by_cases h1 : isUnmatchedFreeKPrefix T k hk j c₁
      · -- c₁ is unmatched free k → T' c₁ = k+1
        simp only [h1, ↓reduceIte]
        by_cases h2 : isUnmatchedFreeKPrefix T k hk j c₂
        · -- c₂ is also unmatched free k → T' c₂ = k+1
          simp only [h2, ↓reduceIte]
          exact le_refl _
        · simp only [h2, ↓reduceIte]
          by_cases h3 : isUnmatchedFreeKSuccPrefix T k hk j c₂
          · -- c₂ is unmatched free k+1 → contradiction
            exfalso
            exact not_unmatched_k_left_of_unmatched_kSucc_prefix T k hk j c₁ c₂ h_row h_col h1 h3
          · -- c₂ is neither → T' c₂ = T c₂
            simp only [h3, ↓reduceIte]
            have hT1 : T c₁ = k := h1.2.1
            rw [hT1] at hT_weak
            by_cases hT2k : T c₂ = k
            · exfalso
              have hc₂_in_prefix : c₂.val.2 < j := hc₂j
              unfold isUnmatchedFreeKPrefix at h2
              push Not at h2
              have h2' := h2 hc₂_in_prefix hT2k
              by_cases hc₂_forced : isForcedK T k hk c₂
              · have h_c₁_forced := row_forced_propagates_left' hmu k hk T hT c₁ c₂ h_row h_col hT1 hc₂_forced
                exact h1.2.2.1 h_c₁_forced
              · have hc₂_matched := h2' hc₂_forced
                have h_c₁_free_prefix : c₁.val.2 < j ∧ T c₁ = k ∧ ¬isForcedK T k hk c₁ := ⟨hc₁j, hT1, h1.2.2.1⟩
                have h_c₂_free_prefix : c₂.val.2 < j ∧ T c₂ = k ∧ ¬isForcedK T k hk c₂ := ⟨hc₂_in_prefix, hT2k, hc₂_forced⟩
                have h_c₂_not_unmatched : ¬isUnmatchedFreeKPrefix T k hk j c₂ := by
                  unfold isUnmatchedFreeKPrefix
                  push Not
                  intro _ _ _
                  exact hc₂_matched
                have h_c₁_not_unmatched := matched_k_propagates_left_prefix T k hk j c₁ c₂ h_row h_col h_c₁_free_prefix h_c₂_free_prefix h_c₂_not_unmatched
                exact h_c₁_not_unmatched h1
            · simp only [Fin.le_def] at hT_weak ⊢
              have hne : (T c₂).val ≠ k.val := fun heq => hT2k (Fin.ext heq)
              omega
      · -- c₁ is not unmatched free k
        simp only [h1, ↓reduceIte]
        by_cases h2 : isUnmatchedFreeKSuccPrefix T k hk j c₁
        · -- c₁ is unmatched free k+1 → T' c₁ = k
          simp only [h2, ↓reduceIte]
          by_cases h3 : isUnmatchedFreeKPrefix T k hk j c₂
          · simp only [h3, ↓reduceIte]
            simp only [Fin.le_def]; omega
          · simp only [h3, ↓reduceIte]
            by_cases h4 : isUnmatchedFreeKSuccPrefix T k hk j c₂
            · simp only [h4, ↓reduceIte]
              exact le_refl _
            · simp only [h4, ↓reduceIte]
              have hT1 : T c₁ = ⟨k.val + 1, hk⟩ := h2.2.1
              rw [hT1] at hT_weak
              simp only [Fin.le_def] at hT_weak ⊢
              omega
        · -- c₁ is neither → T' c₁ = T c₁
          simp only [h2, ↓reduceIte]
          by_cases h3 : isUnmatchedFreeKPrefix T k hk j c₂
          · simp only [h3, ↓reduceIte]
            have hT2 : T c₂ = k := h3.2.1
            rw [hT2] at hT_weak
            simp only [Fin.le_def] at hT_weak ⊢
            omega
          · simp only [h3, ↓reduceIte]
            by_cases h4 : isUnmatchedFreeKSuccPrefix T k hk j c₂
            · simp only [h4, ↓reduceIte]
              have hT2 : T c₂ = ⟨k.val + 1, hk⟩ := h4.2.1
              rw [hT2] at hT_weak
              by_cases hT1k1 : T c₁ = ⟨k.val + 1, hk⟩
              · exfalso
                unfold isUnmatchedFreeKSuccPrefix at h2
                push Not at h2
                have h2' := h2 hc₁j hT1k1
                by_cases hc₁_forced : isForcedKSucc T k hk c₁
                · have h_c₂_forced := row_forcedKSucc_propagates_right' hlam k hk T hT c₂ c₁ h_row.symm h_col hT2 hc₁_forced
                  exact h4.2.2.1 h_c₂_forced
                · have hc₁_matched := h2' hc₁_forced
                  have h_c₁_free_prefix : c₁.val.2 < j ∧ T c₁ = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c₁ := ⟨hc₁j, hT1k1, hc₁_forced⟩
                  have h_c₂_free_prefix : c₂.val.2 < j ∧ T c₂ = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk c₂ := ⟨hc₂j, hT2, h4.2.2.1⟩
                  have h_c₁_not_unmatched : ¬isUnmatchedFreeKSuccPrefix T k hk j c₁ := by
                    unfold isUnmatchedFreeKSuccPrefix
                    push Not
                    intro _ _ _
                    exact hc₁_matched
                  have h_c₂_not_unmatched := matched_kSucc_propagates_right_prefix T k hk j c₁ c₂ h_row h_col h_c₁_free_prefix h_c₂_free_prefix h_c₁_not_unmatched
                  exact h_c₂_not_unmatched h4
              · simp only [Fin.le_def] at hT_weak ⊢
                have hne : (T c₁).val ≠ k.val + 1 := fun heq => hT1k1 (Fin.ext heq)
                omega
            · simp only [h4, ↓reduceIte]
              exact hT_weak
    · -- c₁ in prefix, c₂ in suffix (cross-boundary case)
      have hc₂_ge : c₂.val.2 ≥ j := not_lt.mp hc₂j
      rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT c₂ hc₂_ge]
      unfold benderKnuthPrefixMatching
      by_cases h1 : isUnmatchedFreeKPrefix T k hk j c₁
      · -- c₁ is unmatched free k → T' c₁ = k+1
        simp only [h1, ↓reduceIte]
        have hT1 : T c₁ = k := h1.2.1
        rw [hT1] at hT_weak
        by_cases hT2k : T c₂ = k
        · -- T c₂ = k: Use cross_boundary_unmatched_k_not_eq_suffix_k to derive contradiction
          exfalso
          -- Need to show j is a violator column
          have hj_violator : ¬IsNPartition (nu + contentColGeq T j) := by
            intro hcontra
            have hmisstep := hk_misstep
            obtain ⟨hk', hα_lt⟩ := hmisstep
            have hle : k ≤ ⟨k.val + 1, hk'⟩ := Fin.mk_le_mk.mpr (Nat.le_succ k.val)
            have hα_ge := hcontra k ⟨k.val + 1, hk'⟩ hle
            simp only [Pi.add_apply] at hα_lt hα_ge
            omega
          exact cross_boundary_unmatched_k_not_eq_suffix_k hmu nu k hk j hj_pos T hT
            hj_violator hbeta hk_misstep c₁ c₂ h_row h_col hc₁j hc₂_ge h1 hT2k
        · simp only [Fin.le_def] at hT_weak ⊢
          have hne : (T c₂).val ≠ k.val := fun heq => hT2k (Fin.ext heq)
          omega
      · simp only [h1, ↓reduceIte]
        by_cases h2 : isUnmatchedFreeKSuccPrefix T k hk j c₁
        · -- c₁ is unmatched free k+1 → T' c₁ = k
          simp only [h2, ↓reduceIte]
          have hT1 : T c₁ = ⟨k.val + 1, hk⟩ := h2.2.1
          rw [hT1] at hT_weak
          simp only [Fin.le_def] at hT_weak ⊢
          omega
        · -- c₁ is neither → T' c₁ = T c₁
          simp only [h2, ↓reduceIte]
          exact hT_weak
  · -- c₁ in suffix
    have hc₁_ge : c₁.val.2 ≥ j := not_lt.mp hc₁j
    have hc₂_ge : c₂.val.2 ≥ j := Nat.le_trans hc₁_ge (Nat.le_of_lt h_col)
    rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT c₁ hc₁_ge]
    rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT c₂ hc₂_ge]
    exact hT_weak

/-- Column-strict preservation for benderKnuthPrefixMatching.

    This lemma proves that benderKnuthPrefixMatching preserves column-strict ordering when
    lam and mu are N-partitions. The proof uses the partition hypotheses to show that
    if T c₁ = k and T c₂ = k+1 in the same column, they must be adjacent (hence forced).

    Since c₁.col = c₂.col, both cells are either in the prefix (col < j) or in the suffix
    (col ≥ j). In the suffix, both are unchanged. In the prefix, the proof uses the
    matching-based conditions `isUnmatchedFreeKPrefix` and `isUnmatchedFreeKSuccPrefix`.

    The key insight is that column-strict is easier than row-weak because:
    - If T c₁ = k and T c₂ = k+1 in the same column with c₁ above c₂, they must be adjacent
      by `adjacent_k_kSucc_in_column`, so both are forced and remain unchanged.
    - This rules out the problematic case where c₁ becomes k+1 and c₂ becomes k. -/
private lemma benderKnuthPrefixMatching_column_strict {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (hT : IsSemistandard T)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_col : c₁.val.2 = c₂.val.2) (h_row : c₁.val.1 < c₂.val.1) :
    benderKnuthPrefixMatching k hk j T hT c₁ < benderKnuthPrefixMatching k hk j T hT c₂ := by
  have hT_strict : T c₁ < T c₂ := hT.2 c₁ c₂ h_col h_row
  -- Since c₁.col = c₂.col, either both are < j or both are >= j
  by_cases hc₁j : c₁.val.2 < j
  · -- Both cells in columns < j (since c₁.col = c₂.col)
    have hc₂j : c₂.val.2 < j := by rw [← h_col]; exact hc₁j
    unfold benderKnuthPrefixMatching
    by_cases h1 : isUnmatchedFreeKPrefix T k hk j c₁
    · simp only [h1, ↓reduceIte]
      by_cases h2 : isUnmatchedFreeKPrefix T k hk j c₂
      · simp only [h2, ↓reduceIte]
        -- Both become k+1, contradiction with strict ordering
        have hT1 : T c₁ = k := h1.2.1
        have hT2 : T c₂ = k := h2.2.1
        rw [hT1, hT2] at hT_strict
        exact absurd hT_strict (lt_irrefl k)
      · simp only [h2, ↓reduceIte]
        by_cases h3 : isUnmatchedFreeKSuccPrefix T k hk j c₂
        · simp only [h3, ↓reduceIte]
          -- c₁ becomes k+1, c₂ becomes k, would give k+1 > k, bad!
          -- But this is impossible: T c₁ = k and T c₂ = k+1 in same column
          -- means they're adjacent by partition property, so both are forced.
          exfalso
          have hT1 : T c₁ = k := h1.2.1
          have hT2 : T c₂ = ⟨k.val + 1, hk⟩ := h3.2.1
          have h_adj := adjacent_k_kSucc_in_column hlam hmu T hT k hk c₁ c₂ h_col h_row hT1 hT2
          -- c₁ is adjacent to c₂ with T c₂ = k+1 means c₁ is forced
          have hi : c₁.val.1.val + 1 < N := by have := c₂.val.1.isLt; omega
          have h_c₂_row : c₂.val.1 = ⟨c₁.val.1.val + 1, hi⟩ := by ext; exact h_adj.symm
          have h_c₁_forced : isForcedK T k hk c₁ := by
            refine ⟨hT1, c₂, ?_, ?_, hT2⟩
            · exact h_col.symm
            · simp only [h_c₂_row]
          exact h1.2.2.1 h_c₁_forced
        · simp only [h3, ↓reduceIte]
          -- c₁ becomes k+1, c₂ unchanged
          -- Need k+1 < T c₂. We know T c₁ = k < T c₂.
          -- If T c₂ = k+1, then by adjacent_k_kSucc_in_column, c₁ and c₂ are adjacent,
          -- so c₁ is forced, contradicting h1.
          have hT1 : T c₁ = k := h1.2.1
          rw [hT1] at hT_strict
          simp only [Fin.lt_def] at hT_strict ⊢
          by_cases hT2 : T c₂ = ⟨k.val + 1, hk⟩
          · -- T c₂ = k+1, use adjacent_k_kSucc_in_column
            exfalso
            have h_adj := adjacent_k_kSucc_in_column hlam hmu T hT k hk c₁ c₂ h_col h_row hT1 hT2
            have hi : c₁.val.1.val + 1 < N := by have := c₂.val.1.isLt; omega
            have h_c₂_row : c₂.val.1 = ⟨c₁.val.1.val + 1, hi⟩ := by ext; exact h_adj.symm
            have h_c₁_forced : isForcedK T k hk c₁ := by
              refine ⟨hT1, c₂, ?_, ?_, hT2⟩
              · exact h_col.symm
              · simp only [h_c₂_row]
            exact h1.2.2.1 h_c₁_forced
          · have hne : (T c₂).val ≠ k.val + 1 := fun heq => hT2 (Fin.ext heq)
            omega
    · simp only [h1, ↓reduceIte]
      by_cases h2 : isUnmatchedFreeKSuccPrefix T k hk j c₁
      · simp only [h2, ↓reduceIte]
        by_cases h3 : isUnmatchedFreeKPrefix T k hk j c₂
        · simp only [h3, ↓reduceIte]
          -- c₁ becomes k, c₂ becomes k+1, need k < k+1 ✓
          simp only [Fin.lt_def]; omega
        · simp only [h3, ↓reduceIte]
          by_cases h4 : isUnmatchedFreeKSuccPrefix T k hk j c₂
          · simp only [h4, ↓reduceIte]
            -- Both become k, contradiction with strict ordering
            have hT1 : T c₁ = ⟨k.val + 1, hk⟩ := h2.2.1
            have hT2 : T c₂ = ⟨k.val + 1, hk⟩ := h4.2.1
            rw [hT1, hT2] at hT_strict
            exact absurd hT_strict (lt_irrefl _)
          · simp only [h4, ↓reduceIte]
            -- c₁ becomes k, c₂ unchanged
            have hT1 : T c₁ = ⟨k.val + 1, hk⟩ := h2.2.1
            rw [hT1] at hT_strict
            simp only [Fin.lt_def] at hT_strict ⊢
            omega
      · simp only [h2, ↓reduceIte]
        by_cases h3 : isUnmatchedFreeKPrefix T k hk j c₂
        · simp only [h3, ↓reduceIte]
          -- c₁ unchanged, c₂ becomes k+1
          have hT2 : T c₂ = k := h3.2.1
          rw [hT2] at hT_strict
          simp only [Fin.lt_def] at hT_strict ⊢
          omega
        · simp only [h3, ↓reduceIte]
          by_cases h4 : isUnmatchedFreeKSuccPrefix T k hk j c₂
          · simp only [h4, ↓reduceIte]
            -- c₁ unchanged, c₂ becomes k
            -- Need T c₁ < k. We know T c₁ < T c₂ = k+1.
            -- If T c₁ = k, then by adjacent_k_kSucc_in_column, c₁ and c₂ are adjacent.
            -- Since c₁ is above c₂ with T c₁ = k, c₂ is forced, contradicting h4.2.
            have hT2 : T c₂ = ⟨k.val + 1, hk⟩ := h4.2.1
            rw [hT2] at hT_strict
            simp only [Fin.lt_def] at hT_strict ⊢
            by_cases hT1k : T c₁ = k
            · exfalso
              have h_adj := adjacent_k_kSucc_in_column hlam hmu T hT k hk c₁ c₂ h_col h_row hT1k hT2
              -- c₁ and c₂ are adjacent, so c₂ is forced (k directly above)
              have h_c₂_forced : isForcedKSucc T k hk c₂ := by
                refine ⟨hT2, c₁, h_col, ?_, hT1k⟩
                omega
              exact h4.2.2.1 h_c₂_forced
            · have hne : (T c₁).val ≠ k.val := fun heq => hT1k (Fin.ext heq)
              omega
          · simp only [h4, ↓reduceIte]
            -- Both unchanged
            exact hT_strict
  · -- Both cells in columns >= j (since c₁.col = c₂.col)
    have hc₁_ge : c₁.val.2 ≥ j := not_lt.mp hc₁j
    have hc₂_ge : c₂.val.2 ≥ j := by rw [← h_col]; exact hc₁_ge
    rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT c₁ hc₁_ge]
    rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT c₂ hc₂_ge]
    exact hT_strict

/-- benderKnuthPrefixMatching preserves semistandardness in the Stembridge involution context.

    This combines `benderKnuthPrefixMatching_row_weak_stembridge` and
    `benderKnuthPrefixMatching_column_strict` to show that the resulting tableau is semistandard.

    The Stembridge context hypotheses (nu, hj_pos, hbeta, hk_misstep) are needed for the
    row-weak part to handle the cross-boundary case. -/
theorem benderKnuthPrefixMatching_semistandard_stembridge {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (nu : Fin N → ℕ)
    (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (hj_pos : j > 0) (T : Tableau lam mu) (hT : IsSemistandard T)
    (hbeta : IsNPartition (nu + contentColGeq T (j + 1)))
    (hk_misstep : isMisstep (nu + contentColGeq T j) k) :
    IsSemistandard (benderKnuthPrefixMatching k hk j T hT) := by
  constructor
  · intro c₁ c₂ h_row h_col
    exact benderKnuthPrefixMatching_row_weak_stembridge hlam hmu nu k hk j hj_pos T hT hbeta hk_misstep c₁ c₂ h_row h_col
  · intro c₁ c₂ h_col h_row
    exact benderKnuthPrefixMatching_column_strict hlam hmu k hk j T hT c₁ c₂ h_col h_row

/-- benderKnuthPrefixMatching preserves contentColGeq for columns >= j.
    Since benderKnuthPrefixMatching only modifies cells in columns < j, the content
    in columns >= j is unchanged. -/
theorem benderKnuthPrefixMatching_contentColGeq {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (hT : IsSemistandard T) :
    contentColGeq (benderKnuthPrefixMatching k hk j T hT) j = contentColGeq T j := by
  ext i
  simp only [contentColGeq]
  apply Nat.card_congr
  refine ⟨fun ⟨⟨c, hc⟩, hTc⟩ => ⟨⟨c, hc⟩, ?_⟩, fun ⟨⟨c, hc⟩, hTc⟩ => ⟨⟨c, hc⟩, ?_⟩, ?_, ?_⟩
  · rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT ⟨c, hc.1⟩ hc.2] at hTc
    exact hTc
  · rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT ⟨c, hc.1⟩ hc.2]
    exact hTc
  · intro ⟨⟨c, hc⟩, _⟩; rfl
  · intro ⟨⟨c, hc⟩, _⟩; rfl

/-- benderKnuthPrefixMatching preserves contentColGeq for all j' >= j.
    This generalizes benderKnuthPrefixMatching_contentColGeq to any column >= j. -/
theorem benderKnuthPrefixMatching_contentColGeq_ge {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (hT : IsSemistandard T)
    (j' : ℕ) (hj' : j' ≥ j) :
    contentColGeq (benderKnuthPrefixMatching k hk j T hT) j' = contentColGeq T j' := by
  ext i
  simp only [contentColGeq]
  apply Nat.card_congr
  refine ⟨fun ⟨⟨c, hc⟩, hTc⟩ => ⟨⟨c, hc⟩, ?_⟩, fun ⟨⟨c, hc⟩, hTc⟩ => ⟨⟨c, hc⟩, ?_⟩, ?_, ?_⟩
  · have hc_ge : c.2 ≥ j := Nat.le_trans hj' hc.2
    rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT ⟨c, hc.1⟩ hc_ge] at hTc
    exact hTc
  · have hc_ge : c.2 ≥ j := Nat.le_trans hj' hc.2
    rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT ⟨c, hc.1⟩ hc_ge]
    exact hTc
  · intro ⟨⟨c, hc⟩, _⟩; rfl
  · intro ⟨⟨c, hc⟩, _⟩; rfl

/-- benderKnuthPrefixMatching preserves contentTableau for indices i ≠ k, k+1.
    This is because the transformation only swaps k ↔ k+1 entries. -/
theorem benderKnuthPrefixMatching_contentTableau_other {lam mu : Fin N → ℕ} (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (hT : IsSemistandard T)
    (i : Fin N) (hi_ne_k : i ≠ k) (hi_ne_ksucc : i.val ≠ k.val + 1) :
    contentTableau (benderKnuthPrefixMatching k hk j T hT) i = contentTableau T i := by
  apply contentTableau_eq_of_iff
  intro c
  by_cases hcol : c.val.2 < j
  · constructor
    · intro hT'c
      simp only [benderKnuthPrefixMatching] at hT'c
      split_ifs at hT'c with h1 h2
      · simp only [Fin.ext_iff] at hT'c
        exact absurd hT'c.symm hi_ne_ksucc
      · exact absurd hT'c.symm hi_ne_k
      · exact hT'c
    · intro hTc
      simp only [benderKnuthPrefixMatching]
      split_ifs with h1 h2
      · have := h1.2.1
        rw [hTc] at this
        exact absurd this hi_ne_k
      · have := h2.2.1
        rw [hTc] at this
        simp only [Fin.ext_iff] at this
        exact absurd this hi_ne_ksucc
      · exact hTc
  · push Not at hcol
    rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT c hcol]

/-! ### Helper lemmas for the involution proof

The following helper lemmas establish the counting arguments needed to prove
`benderKnuthPrefixMatching_involutive_stembridge`. The key insight is that
the counts swap under the transformation:
- `freeKCountPrefix T' = freeKSuccCountPrefix T`
- `freeKSuccCountPrefix T' = freeKCountPrefix T`

These lemmas are analogous to `unmatched_k_becomes_unmatched_kSucc'` for the
full-row version, but restricted to the prefix (columns < j). -/

/-- In a semistandard tableau, if c₁ and c₂ are in the same row with T c₁ = k and T c₂ = k+1,
    then c₁.col < c₂.col. This follows from row-weak ordering.

    **Proof**: By row-weak, if c₂.col ≤ c₁.col then T c₂ ≤ T c₁ = k, contradicting T c₂ = k+1. -/
private lemma k_col_lt_kSucc_col {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N)
    (T : Tableau lam mu) (hT : IsSemistandard T)
    (c₁ c₂ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h_row : c₁.val.1 = c₂.val.1)
    (h_c₁ : T c₁ = k) (h_c₂ : T c₂ = ⟨k.val + 1, hk⟩) :
    c₁.val.2 < c₂.val.2 := by
  by_contra h_not_lt
  push Not at h_not_lt
  rcases Nat.lt_or_eq_of_le h_not_lt with h_gt | h_eq
  · -- Case: c₂.col < c₁.col
    have h_le : T c₂ ≤ T c₁ := hT.1 c₂ c₁ h_row.symm h_gt
    rw [h_c₁, h_c₂] at h_le
    simp only [Fin.le_def] at h_le
    omega
  · -- Case: c₂.col = c₁.col (same column)
    -- By column-strict, if c₁.row < c₂.row then T c₁ < T c₂
    -- If c₂.row < c₁.row then T c₂ < T c₁
    -- If c₁.row = c₂.row then c₁ = c₂, so T c₁ = T c₂, contradiction
    by_cases h_row_lt : c₁.val.1 < c₂.val.1
    · have h_lt : T c₁ < T c₂ := hT.2 c₁ c₂ h_eq.symm h_row_lt
      rw [h_c₁, h_c₂] at h_lt
      simp only [Fin.lt_def] at h_lt
      omega
    · push Not at h_row_lt
      rcases Nat.lt_or_eq_of_le h_row_lt with h_row_gt | h_row_eq
      · have h_lt : T c₂ < T c₁ := hT.2 c₂ c₁ h_eq h_row_gt
        rw [h_c₁, h_c₂] at h_lt
        simp only [Fin.lt_def] at h_lt
        omega
      · -- c₁ = c₂
        have h_eq_cell : c₁ = c₂ := by
          apply Subtype.ext
          ext
          · exact congrArg Fin.val h_row
          · exact h_eq.symm
        rw [h_eq_cell, h_c₂] at h_c₁
        simp only [Fin.ext_iff] at h_c₁
        omega

/-- An unmatched free k in T becomes an unmatched free (k+1) in T' = benderKnuthPrefixMatching T.

    **Proof idea**: If c is unmatched free k in T, then:
    - T' c = k+1 (by definition of benderKnuthPrefixMatching)
    - c is not forced (k+1) in T' (column-strictness argument)
    - The counting condition: freeKCountPrefix T' + freeKSuccCountUpToPrefix T' c.col ≤ freeKSuccCountPrefix T'
    
    The key is that the unmatched k's (including c) become the leftmost free k+1's in T',
    so freeKSuccCountUpToPrefix T' c.col counts exactly the unmatched k's up to c. -/
private lemma unmatchedFreeK_becomes_unmatchedFreeKSucc {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h1 : isUnmatchedFreeKPrefix T k hk j c) :
    let T' := benderKnuthPrefixMatching k hk j T hT
    freeKCountPrefix T' c.val.1 k hk j + freeKSuccCountUpToPrefix T' c.val.1 k hk j c.val.2 ≤
      freeKSuccCountPrefix T' c.val.1 k hk j := by
  -- The key insight is that after benderKnuthPrefixMatching:
  -- - Free k's in T' come from: matched k's in T + unmatched (k+1)'s in T
  -- - Free (k+1)'s in T' come from: matched (k+1)'s in T + unmatched k's in T
  --
  -- Let m = freeKCountPrefix T, n = freeKSuccCountPrefix T, m_c = freeKCountUpToPrefix T c.col.
  -- From h1: m_c > n (c is unmatched), so m ≥ m_c > n, hence m > n.
  --
  -- Count swap (when m > n):
  -- - freeKCountPrefix T' = min(m,n) + (n - min(m,n)) = n (matched k's + unmatched (k+1)'s)
  -- - freeKSuccCountPrefix T' = min(m,n) + (m - min(m,n)) = m (matched (k+1)'s + unmatched k's)
  --
  -- For freeKSuccCountUpToPrefix T' c.col:
  -- The free (k+1)'s in T' at cols ≤ c.col are exactly the unmatched k's in T at cols ≤ c.col.
  -- (Matched (k+1)'s are to the right of c since c is a k and (k+1)'s come after k's.)
  -- So freeKSuccCountUpToPrefix T' c.col = #{unmatched k's in T at cols ≤ c.col}.
  --
  -- Since c is an unmatched k, unmatched k's at cols ≤ c.col = m_c - n (the excess k's up to c).
  -- (The first n k's are matched, the remaining m_c - n are unmatched.)
  --
  -- Goal: freeKCountPrefix T' + freeKSuccCountUpToPrefix T' c.col ≤ freeKSuccCountPrefix T'
  --       n + (m_c - n) ≤ m
  --       m_c ≤ m ✓ (by freeKCountUpToPrefix_le_freeKCountPrefix)
  classical
  intro T'
  haveI : Finite {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} :=
    Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
  let m := freeKCountPrefix T c.val.1 k hk j
  let n := freeKSuccCountPrefix T c.val.1 k hk j
  let m_c := freeKCountUpToPrefix T c.val.1 k hk j c.val.2
  
  -- From h1: m_c > n
  have h_m_c_gt_n : m_c > n := h1.2.2.2
  -- m_c ≤ m
  have h_m_c_le_m : m_c ≤ m := freeKCountUpToPrefix_le_freeKCountPrefix T c.val.1 k hk j c.val.2
  -- m > n (since m ≥ m_c > n)
  have h_m_gt_n : m > n := Nat.lt_of_lt_of_le h_m_c_gt_n h_m_c_le_m
  
  -- We'll show:
  -- 1. freeKCountPrefix T' ≤ n
  -- 2. freeKSuccCountUpToPrefix T' c.col ≤ m_c - n  
  -- 3. freeKSuccCountPrefix T' ≥ m
  -- Then: LHS ≤ n + (m_c - n) = m_c ≤ m ≤ RHS
  
  -- Bound 1: freeKCountPrefix T' ≤ n
  -- Use the count swap lemma: freeKCountPrefix T' = freeKSuccCountPrefix T = n
  have h_bound1 : freeKCountPrefix T' c.val.1 k hk j ≤ n := by
    rw [freeKCountPrefix_benderKnuthPrefixMatching k hk j T hT c.val.1]
    
  -- Bound 2: freeKSuccCountUpToPrefix T' c.col ≤ m_c - n
  -- Free (k+1)'s in T' at cols ≤ c.col = unmatched k's in T at cols ≤ c.col = m_c - n.
  -- This is because:
  -- - By semistandardness, all (k+1)'s in T are at cols > c.col (since c is a k)
  -- - So matched (k+1)'s from T don't contribute to freeKSuccCountUpToPrefix T' c.col
  -- - Only unmatched k's from T (which become (k+1)'s in T') contribute
  -- - There are exactly m_c - n unmatched k's at cols ≤ c.col (first n are matched)
  have h_bound2 : freeKSuccCountUpToPrefix T' c.val.1 k hk j c.val.2 ≤ m_c - n := by
    -- The free (k+1)'s in T' at cols ≤ c.col are exactly the unmatched k's in T at cols ≤ c.col.
    -- Since there are m_c k's at cols ≤ c.col and the first n are matched (m_c > n),
    -- there are m_c - n unmatched k's at cols ≤ c.col.
    
    -- Helper: how benderKnuthPrefixMatching transforms a cell
    have hT'_def : ∀ d, T' d = 
        if isUnmatchedFreeKPrefix T k hk j d then ⟨k.val + 1, hk⟩
        else if isUnmatchedFreeKSuccPrefix T k hk j d then k
        else T d := fun d => rfl
    
    -- Define the key sets
    let LHS_set : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
      {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ 
           T' d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk d}
    let unmatchedK_upTo : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
      {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ isUnmatchedFreeKPrefix T k hk j d}
    
    -- Step 1: Show LHS_set ⊆ unmatchedK_upTo
    have h_subset : LHS_set ⊆ unmatchedK_upTo := by
      intro d ⟨hd_row, hd_col, hd_col_j, hT'd_val, hd_free'⟩
      -- d is a free (k+1) in T' at cols ≤ c.col
      -- By definition of benderKnuthPrefixMatching, T' d = k+1 means either:
      -- (1) d was unmatched free k in T (becomes k+1), or
      -- (2) d was matched free (k+1) in T (stays k+1), or
      -- (3) d was unchanged (T d = k+1 and not unmatched free k or k+1)
      
      -- Case (2) and (3) are impossible: by semistandardness, all (k+1)'s in T are at cols > c.col
      -- since c is a free k. Since d.col ≤ c.col, T d ≠ k+1.
      
      -- So d must have been an unmatched free k in T.
      have h_was_unmatchedK : isUnmatchedFreeKPrefix T k hk j d := by
        -- Check what benderKnuthPrefixMatching does to d
        rw [hT'_def] at hT'd_val
        by_cases h_unmatchedK : isUnmatchedFreeKPrefix T k hk j d
        · exact h_unmatchedK
        · -- d was not unmatched free k
          simp only [h_unmatchedK, ↓reduceIte] at hT'd_val
          by_cases h_unmatchedKSucc : isUnmatchedFreeKSuccPrefix T k hk j d
          · -- d was unmatched free (k+1) → T' d = k, contradiction
            simp only [h_unmatchedKSucc, ↓reduceIte, Fin.ext_iff] at hT'd_val
            omega
          · -- d was neither → T' d = T d
            simp only [h_unmatchedKSucc, ↓reduceIte] at hT'd_val
            -- hT'd_val : T d = k+1
            -- But d.col ≤ c.col and c is a free k, so by semistandardness T d ≤ T c = k
            have hTc := h1.2.1  -- T c = k
            by_cases h_eq : d.val.2 = c.val.2
            · -- d.col = c.col, and both are in same row
              have h_d_eq_c : d = c := Subtype.ext (Prod.ext hd_row h_eq)
              rw [h_d_eq_c, hTc] at hT'd_val
              simp only [Fin.ext_iff] at hT'd_val; omega
            · -- d.col < c.col
              have h_lt : d.val.2 < c.val.2 := Nat.lt_of_le_of_ne hd_col h_eq
              have h_weak : T d ≤ T c := hT.1 d c hd_row h_lt
              rw [hT'd_val, hTc] at h_weak
              simp only [Fin.le_def] at h_weak; omega
      exact ⟨hd_row, hd_col, h_was_unmatchedK⟩
    
    -- Step 2: Count the unmatched k's at cols ≤ c.col
    -- The unmatched k's are those free k's d with freeKCountUpToPrefix(d.col) > n.
    -- At cols ≤ c.col, we have freeKCountUpToPrefix ≤ m_c.
    -- The unmatched k's at cols ≤ c.col are exactly those at positions n+1, ..., m_c,
    -- which is m_c - n cells.
    have h_unmatchedK_card : unmatchedK_upTo.ncard ≤ m_c - n := by
      -- The unmatched k's at cols ≤ c.col are a subset of all free k's at cols ≤ c.col
      -- There are m_c free k's at cols ≤ c.col (by definition of m_c)
      -- Among these, the first n (by column order) are matched
      -- So there are at most m_c - n unmatched k's at cols ≤ c.col
      
      -- We bound by: unmatchedK_upTo ⊆ {free k's at cols ≤ c.col} and use counting
      let freeK_upTo : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
        {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ T d = k ∧ ¬isForcedK T k hk d}
      
      have h_upTo_subset : unmatchedK_upTo ⊆ freeK_upTo := by
        intro d ⟨hd_row, hd_col, hd_unmatch⟩
        unfold isUnmatchedFreeKPrefix at hd_unmatch
        exact ⟨hd_row, hd_col, hd_unmatch.1, hd_unmatch.2.1, hd_unmatch.2.2.1⟩
      
      have h_freeK_upTo_card : freeK_upTo.ncard = m_c := by
        unfold freeKCountUpToPrefix at *
        rfl
      
      -- The key: among m_c free k's, at most m_c - n are unmatched
      -- This is because the first n are matched (freeKCountUpToPrefix ≤ n)
      -- and the remaining m_c - n are unmatched (freeKCountUpToPrefix > n)
      -- 
      -- More precisely: for each free k d at cols ≤ c.col, d is unmatched iff
      -- freeKCountUpToPrefix(d.col) > n. The count freeKCountUpToPrefix increases
      -- by 1 for each free k, so exactly m_c - n of them satisfy this condition.
      
      -- We use a simpler bound: unmatchedK_upTo ⊆ freeK_upTo, so
      -- unmatchedK_upTo.ncard ≤ freeK_upTo.ncard = m_c
      -- But we need the tighter bound ≤ m_c - n.
      
      -- The tighter bound follows from: the first n free k's (by column order) are matched.
      -- Since there are m_c free k's at cols ≤ c.col and the first n are matched,
      -- at most m_c - n are unmatched.
      
      -- We'll prove this by showing that matched free k's at cols ≤ c.col number at least n
      -- (actually exactly min(m_c, n) = n since m_c > n).
      
      -- Simpler approach: use the fact that unmatchedK_upTo ⊆ {all unmatched k's in prefix}
      -- and count.
      have h_all_unmatched : Nat.card {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
          d.val.1 = c.val.1 ∧ isUnmatchedFreeKPrefix T k hk j d} = m - min m n := 
        unmatchedFreeKPrefix_row_card T c.val.1 k hk j
      have h_min : min m n = n := Nat.min_eq_right (le_of_lt h_m_gt_n)
      rw [h_min] at h_all_unmatched
      
      -- unmatchedK_upTo ⊆ {all unmatched k's in prefix}
      have h_upTo_all : unmatchedK_upTo ⊆ {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
          d.val.1 = c.val.1 ∧ isUnmatchedFreeKPrefix T k hk j d} := by
        intro d ⟨hd_row, _, hd_unmatch⟩
        exact ⟨hd_row, hd_unmatch⟩
      
      -- So unmatchedK_upTo.ncard ≤ m - n
      have h_le_m_minus_n : unmatchedK_upTo.ncard ≤ m - n := by
        calc unmatchedK_upTo.ncard 
            ≤ {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
                d.val.1 = c.val.1 ∧ isUnmatchedFreeKPrefix T k hk j d}.ncard := 
              Set.ncard_le_ncard h_upTo_all (Set.toFinite _)
          _ = m - n := h_all_unmatched
      
      -- Now we need m - n ≤ m_c - n, which follows from... wait, that's wrong!
      -- We have m_c ≤ m, so m - n ≥ m_c - n.
      -- 
      -- The correct argument: all unmatched k's in the prefix are at cols ≤ c.col.
      -- This is because c is an unmatched k, and unmatched k's are the rightmost ones.
      -- So unmatchedK_upTo = {all unmatched k's in prefix}, and the card is m - n.
      -- But we want ≤ m_c - n, which is ≤ m - n (since m_c ≤ m).
      -- 
      -- Actually, the bound m_c - n is NOT tight. We have:
      -- unmatchedK_upTo.ncard = #{unmatched k's at cols ≤ c.col} ≤ #{all unmatched k's} = m - n
      -- And m - n ≤ m_c - n is FALSE (it's the other way around).
      --
      -- Wait, I need to reconsider. The goal is to show freeKSuccCountUpToPrefix T' c.col ≤ m_c - n.
      -- Let me check: free (k+1)'s in T' at cols ≤ c.col = unmatched k's in T at cols ≤ c.col.
      -- The number of unmatched k's at cols ≤ c.col is exactly m_c - n (not m - n).
      -- This is because:
      -- - There are m_c free k's at cols ≤ c.col
      -- - The first n of these (by column order) are matched
      -- - The remaining m_c - n are unmatched
      --
      -- So we need to prove unmatchedK_upTo.ncard ≤ m_c - n directly, not via m - n.
      
      -- Actually, the correct bound is: unmatchedK_upTo.ncard = m_c - n (equality!).
      -- But proving ≤ is sufficient and easier.
      
      -- Key insight: a free k at position d is unmatched iff freeKCountUpToPrefix(d.col) > n.
      -- The free k's at cols ≤ c.col have freeKCountUpToPrefix ranging from 1 to m_c.
      -- Those with freeKCountUpToPrefix > n are unmatched.
      -- Since m_c > n, the unmatched ones are at positions n+1, ..., m_c, totaling m_c - n.
      
      -- For the ≤ bound, we can use: each unmatched k d at cols ≤ c.col satisfies
      -- freeKCountUpToPrefix(d.col) > n, and freeKCountUpToPrefix(d.col) ≤ m_c.
      -- So freeKCountUpToPrefix(d.col) ∈ {n+1, ..., m_c}, giving at most m_c - n values.
      
      -- This is a counting argument that's hard to formalize directly.
      -- Instead, we use: the unmatched k's at cols ≤ c.col form a subset of
      -- {d | freeKCountUpToPrefix(d.col) > n ∧ freeKCountUpToPrefix(d.col) ≤ m_c}.
      -- The size of this set is at most m_c - n.
      
      -- Simpler: we directly bound by m_c - n using the structure of the matching.
      -- Since c is the m_c-th free k (by freeKCountUpToPrefix(c.col) = m_c),
      -- and the first n are matched, the unmatched k's at cols ≤ c.col are
      -- the (n+1)-th through m_c-th free k's, which is m_c - n cells.
      
      -- For now, let's use a different approach: partition freeK_upTo into matched and unmatched.
      -- Define the set of matched k's at cols ≤ c.col
      let matchedK_upTo : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
        {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ isMatchedFreeKPrefix T k hk j d}
      
      -- freeK_upTo = matchedK_upTo ∪ unmatchedK_upTo (disjoint)
      have h_partition : freeK_upTo = matchedK_upTo ∪ unmatchedK_upTo := by
        ext d
        simp only [Set.mem_union]
        constructor
        · intro ⟨hd_row, hd_col, hd_col_j, hd_val, hd_free⟩
          by_cases h_unmatch : isUnmatchedFreeKPrefix T k hk j d
          · right; exact ⟨hd_row, hd_col, h_unmatch⟩
          · left
            exact ⟨hd_row, hd_col, hd_col_j, hd_val, hd_free, h_unmatch⟩
        · intro h
          rcases h with ⟨hd_row, hd_col, hd_matched⟩ | ⟨hd_row, hd_col, hd_unmatch⟩
          · exact ⟨hd_row, hd_col, hd_matched.1, hd_matched.2.1, hd_matched.2.2.1⟩
          · unfold isUnmatchedFreeKPrefix at hd_unmatch
            exact ⟨hd_row, hd_col, hd_unmatch.1, hd_unmatch.2.1, hd_unmatch.2.2.1⟩
      
      -- Disjointness
      have h_disj : Disjoint matchedK_upTo unmatchedK_upTo := by
        rw [Set.disjoint_iff]
        intro d ⟨⟨_, _, hd_matched⟩, ⟨_, _, hd_unmatch⟩⟩
        exact hd_matched.2.2.2 hd_unmatch
      
      -- Matched k's at cols ≤ c.col = {all matched k's in prefix} 
      -- (since all matched k's are at cols ≤ c.col, because matched k's are the leftmost ones)
      have h_matched_all_upTo : matchedK_upTo = {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
          d.val.1 = c.val.1 ∧ isMatchedFreeKPrefix T k hk j d} := by
        ext d
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro ⟨hd_row, _, hd_matched⟩; exact ⟨hd_row, hd_matched⟩
        · intro ⟨hd_row, hd_matched⟩
          -- d is a matched k, so d.col ≤ c.col (matched k's are to the left of unmatched k's)
          refine ⟨hd_row, ?_, hd_matched⟩
          -- Show d.col ≤ c.col
          have hd_not_unmatch := hd_matched.2.2.2
          unfold isUnmatchedFreeKPrefix at hd_not_unmatch
          push Not at hd_not_unmatch
          have hd_cond := hd_not_unmatch hd_matched.1 hd_matched.2.1 hd_matched.2.2.1
          -- hd_cond : freeKCountUpToPrefix T d.row k hk j d.col ≤ freeKSuccCountPrefix T d.row k hk j
          -- h_m_c_gt_n : m_c > n where m_c = freeKCountUpToPrefix T c.row k hk j c.col
          -- By monotonicity of freeKCountUpToPrefix, d.col ≤ c.col
          by_contra h_gt; push Not at h_gt
          -- First rewrite hd_cond to use c.row instead of d.row
          rw [hd_row] at hd_cond
          -- Now hd_cond : freeKCountUpToPrefix T c.row k hk j d.col ≤ freeKSuccCountPrefix T c.row k hk j = n
          have h_mono := freeKCountUpToPrefix_mono T c.val.1 k hk j c.val.2 d.val.2 (le_of_lt h_gt)
          -- h_mono : freeKCountUpToPrefix T c.row k hk j c.col ≤ freeKCountUpToPrefix T c.row k hk j d.col
          -- i.e., m_c ≤ freeKCountUpToPrefix T c.row k hk j d.col
          have h_contra : m_c ≤ n := le_trans h_mono hd_cond
          omega
      
      have h_matchedK_card : matchedK_upTo.ncard = min m n := by
        rw [h_matched_all_upTo]
        exact matchedFreeKPrefix_row_card T c.val.1 k hk j
      
      have h_min_eq : min m n = n := Nat.min_eq_right (le_of_lt h_m_gt_n)
      rw [h_min_eq] at h_matchedK_card
      
      -- Now: |freeK_upTo| = |matchedK_upTo| + |unmatchedK_upTo|
      -- m_c = n + |unmatchedK_upTo|
      -- |unmatchedK_upTo| = m_c - n
      have h_card_eq : freeK_upTo.ncard = matchedK_upTo.ncard + unmatchedK_upTo.ncard := by
        rw [h_partition]
        exact Set.ncard_union_eq h_disj
      rw [h_freeK_upTo_card, h_matchedK_card] at h_card_eq
      omega
    
    -- Combine: LHS ⊆ unmatchedK_upTo, so LHS.ncard ≤ unmatchedK_upTo.ncard ≤ m_c - n
    unfold freeKSuccCountUpToPrefix
    calc Nat.card ↑LHS_set ≤ unmatchedK_upTo.ncard := 
        Set.ncard_le_ncard h_subset (Set.toFinite _)
      _ ≤ m_c - n := h_unmatchedK_card
    
  -- Bound 3: freeKSuccCountPrefix T' ≥ m
  -- Use the count swap lemma: freeKSuccCountPrefix T' = freeKCountPrefix T = m
  have h_bound3 : freeKSuccCountPrefix T' c.val.1 k hk j ≥ m := by
    rw [freeKSuccCountPrefix_benderKnuthPrefixMatching k hk j T hT c.val.1]
  
  -- Combine the bounds
  calc freeKCountPrefix T' c.val.1 k hk j + freeKSuccCountUpToPrefix T' c.val.1 k hk j c.val.2
      ≤ n + (m_c - n) := Nat.add_le_add h_bound1 h_bound2
    _ = m_c := by omega
    _ ≤ m := h_m_c_le_m
    _ ≤ freeKSuccCountPrefix T' c.val.1 k hk j := h_bound3

/-- An unmatched free k+1 in T becomes an unmatched free k in T' = benderKnuthPrefixMatching T.

    **Proof idea**: Symmetric to `unmatchedFreeK_becomes_unmatchedFreeKSucc`.
    If c is unmatched free k+1 in T, then freeKCountPrefix T + freeKSuccCountUpToPrefix T c.col ≤ freeKSuccCountPrefix T.

    After transformation, c becomes a free k in T'. For c to be unmatched free k in T',
    we need freeKCountUpToPrefix T' c.col > freeKSuccCountPrefix T'.

    Since the counts swap and unmatched k+1's become k's at their original positions,
    freeKCountUpToPrefix T' c.col = #{unmatched k+1's in T at cols ≤ c.col} > freeKSuccCountPrefix T'.
    
    **Detailed proof sketch**:
    Let m = freeKCountPrefix T, n = freeKSuccCountPrefix T, cnt = freeKSuccCountUpToPrefix T c.col.
    From the unmatched condition: m + cnt ≤ n, which implies m ≤ n (all free k's are matched).
    
    Key observations:
    1. cnt ≥ 1 (c contributes to freeKSuccCountUpToPrefix)
    2. By semistandardness, all free k's in prefix are at cols < c.col (since c is k+1)
    3. After transformation:
       - All free k's stay as k's (they're matched since m ≤ n)
       - Unmatched free k+1's at cols ≤ c.col become k's
    4. freeKCountUpToPrefix T' c.col ≥ m + cnt (free k's + unmatched k+1's)
    5. freeKSuccCountPrefix T' = m (only matched k+1's stay, no unmatched k's to become k+1's)
    6. Since cnt ≥ 1: m + cnt > m = freeKSuccCountPrefix T'
    
    The proof requires helper lemmas analogous to `freeKCountUpTo_after_BK_ge` and 
    `freeKSuccCount_after_BK_eq` but for the prefix-restricted counts. -/
private lemma unmatchedFreeKSucc_becomes_unmatchedFreeK {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (h2 : isUnmatchedFreeKSuccPrefix T k hk j c) :
    let T' := benderKnuthPrefixMatching k hk j T hT
    freeKCountUpToPrefix T' c.val.1 k hk j c.val.2 > freeKSuccCountPrefix T' c.val.1 k hk j := by
  -- The key insight is that after benderKnuthPrefixMatching:
  -- - Free k's in T' come from: matched k's in T + unmatched (k+1)'s in T
  -- - Free (k+1)'s in T' come from: matched (k+1)'s in T + unmatched k's in T
  --
  -- Let m = freeKCountPrefix T, n = freeKSuccCountPrefix T.
  -- Let n_c = freeKSuccCountUpToPrefix T c.col.
  -- From h2: m + n_c ≤ n (c is unmatched (k+1)), so n > m (more (k+1)'s than k's).
  --
  -- Count swap (when n > m):
  -- - freeKCountPrefix T' = min(m,n) + (n - min(m,n)) = m + (n - m) = n
  -- - freeKSuccCountPrefix T' = min(m,n) + (m - min(m,n)) = m + 0 = m
  --
  -- For freeKCountUpToPrefix T' c.col:
  -- The free k's in T' at cols ≤ c.col are:
  -- - matched k's in T at cols ≤ c.col (stay as k)
  -- - unmatched (k+1)'s in T at cols ≤ c.col (become k)
  --
  -- Since n > m, all k's are matched, so matched k's at cols ≤ c.col = m (all of them).
  -- Actually, matched k's at cols ≤ c.col ≤ m.
  -- Unmatched (k+1)'s at cols ≤ c.col: since c is unmatched (k+1), there are n_c - m unmatched (k+1)'s
  -- up to c.col (the first m (k+1)'s are matched, the rest are unmatched).
  -- Wait, that's not quite right either...
  --
  -- Let's think more carefully. In the row:
  -- - There are m free k's and n free (k+1)'s.
  -- - By semistandardness, all k's come before all (k+1)'s.
  -- - The matching pairs the rightmost min(m,n) k's with the leftmost min(m,n) (k+1)'s.
  -- - If n > m: all m k's are matched with the leftmost m (k+1)'s.
  --   The remaining n - m (k+1)'s are unmatched (the leftmost ones!).
  --
  -- Wait, that's wrong. The unmatched (k+1)'s are the LEFTMOST ones, not the rightmost.
  -- Let me reconsider the matching algorithm.
  --
  -- The matching for (k+1)'s: a free (k+1) at position c is unmatched iff
  -- freeKCountPrefix T + freeKSuccCountUpToPrefix T c.col ≤ freeKSuccCountPrefix T
  -- i.e., m + n_c ≤ n, i.e., n_c ≤ n - m.
  -- So the first n - m (k+1)'s (by column order) are unmatched.
  --
  -- After transformation:
  -- - Unmatched (k+1)'s become k's at their original positions.
  -- - Matched (k+1)'s stay as (k+1)'s.
  -- - Matched k's stay as k's.
  -- - Unmatched k's become (k+1)'s (but there are none when n > m).
  --
  -- So freeKCountUpToPrefix T' c.col counts:
  -- - matched k's at cols ≤ c.col (all m of them, since k's are to the left of (k+1)'s)
  -- - unmatched (k+1)'s at cols ≤ c.col that become k's
  --
  -- Since c is an unmatched (k+1), and unmatched (k+1)'s are the leftmost n - m (k+1)'s,
  -- c is among the leftmost n - m (k+1)'s.
  -- Unmatched (k+1)'s at cols ≤ c.col = n_c (since c is the (n_c)-th (k+1) and all (k+1)'s up to c are unmatched).
  -- Wait, that's not right. Let me reconsider.
  --
  -- If c is the j-th (k+1) in the row (0-indexed), then n_c = j + 1 (1-indexed count).
  -- c is unmatched iff m + n_c ≤ n, i.e., n_c ≤ n - m.
  -- So c is among the first n - m (k+1)'s.
  -- All (k+1)'s up to c are unmatched (since they're all among the first n - m).
  -- So unmatched (k+1)'s at cols ≤ c.col = n_c.
  --
  -- Therefore: freeKCountUpToPrefix T' c.col = m + n_c (all k's + unmatched (k+1)'s up to c).
  -- Goal: freeKCountUpToPrefix T' c.col > freeKSuccCountPrefix T'
  --       m + n_c > m (since freeKSuccCountPrefix T' = m when n > m)
  --       n_c > 0 ✓ (since c is a (k+1), n_c ≥ 1)
  classical
  intro T'
  haveI : Finite {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} :=
    Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
  let m := freeKCountPrefix T c.val.1 k hk j
  let n := freeKSuccCountPrefix T c.val.1 k hk j
  let n_c := freeKSuccCountUpToPrefix T c.val.1 k hk j c.val.2
  
  -- From h2: m + n_c ≤ n
  have h_unmatched_cond : m + n_c ≤ n := h2.2.2.2
  -- n_c ≥ 1 (since c is a (k+1) at cols ≤ c.col)
  have h_n_c_pos : n_c ≥ 1 := by
    show freeKSuccCountUpToPrefix T c.val.1 k hk j c.val.2 ≥ 1
    unfold freeKSuccCountUpToPrefix
    have h_c_in : c ∈ {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
        d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} := 
      ⟨rfl, le_refl _, h2.1, h2.2.1, h2.2.2.1⟩
    have h_nonempty : Nonempty {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} // 
        d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} :=
      ⟨⟨c, h_c_in⟩⟩
    haveI h_finite : Finite {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} // 
        d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} :=
      (Set.toFinite _).to_subtype
    exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨h_nonempty, h_finite⟩)
  
  -- We'll show:
  -- 1. freeKCountUpToPrefix T' c.col ≥ m + n_c
  -- 2. freeKSuccCountPrefix T' ≤ m
  -- Then: LHS ≥ m + n_c > m ≥ RHS (since n_c ≥ 1)
  
  -- Bound 1: freeKCountUpToPrefix T' c.col ≥ m + n_c
  have h_bound1 : freeKCountUpToPrefix T' c.val.1 k hk j c.val.2 ≥ m + n_c := by
    -- Free k's in T' at cols ≤ c.col include:
    -- - All m free k's from T (they're all to the left of c, and matched k's stay as k)
    -- - All n_c unmatched (k+1)'s from T at cols ≤ c.col (they become k's)
    
    -- Since m + n_c ≤ n, we have m ≤ n, so all free k's are matched
    have h_m_le_n : m ≤ n := by omega
    
    -- All free k's in prefix are matched (not unmatched)
    have h_all_freeK_matched : ∀ d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu},
        d.val.1 = c.val.1 → d.val.2 < j → T d = k → ¬isForcedK T k hk d → 
        ¬isUnmatchedFreeKPrefix T k hk j d := by
      intro d hrow hcol hval hfree hunmatched
      -- isUnmatchedFreeKPrefix means freeKCountUpToPrefix d.col > freeKSuccCountPrefix
      have h_gt := hunmatched.2.2.2
      -- But freeKCountUpToPrefix d.col ≤ freeKCountPrefix = m ≤ n = freeKSuccCountPrefix
      have h_le : freeKCountUpToPrefix T d.val.1 k hk j d.val.2 ≤ freeKCountPrefix T d.val.1 k hk j := by
        unfold freeKCountUpToPrefix freeKCountPrefix freeKCountBefore
        apply Nat.card_le_card_of_injective (fun ⟨e, he⟩ => ⟨e, ⟨he.1, Nat.lt_of_le_of_lt he.2.1 hcol, he.2.2.2.1, he.2.2.2.2⟩⟩)
        intro ⟨e1, _⟩ ⟨e2, _⟩ h; simp only [Subtype.mk.injEq] at h ⊢; exact h
      rw [hrow] at h_le h_gt
      omega
    
    -- All free (k+1)'s at cols ≤ c.col in prefix are unmatched
    have h_all_kSucc_unmatched : ∀ d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu},
        d.val.1 = c.val.1 → d.val.2 ≤ c.val.2 → d.val.2 < j → 
        T d = ⟨k.val + 1, hk⟩ → ¬isForcedKSucc T k hk d → 
        isUnmatchedFreeKSuccPrefix T k hk j d := by
      intro d hrow hcol hcolj hval hfree
      unfold isUnmatchedFreeKSuccPrefix
      refine ⟨hcolj, hval, hfree, ?_⟩
      -- Need: freeKCountPrefix + freeKSuccCountUpToPrefix d.col ≤ freeKSuccCountPrefix
      have h_mono : freeKSuccCountUpToPrefix T c.val.1 k hk j d.val.2 ≤ 
                    freeKSuccCountUpToPrefix T c.val.1 k hk j c.val.2 := by
        unfold freeKSuccCountUpToPrefix
        apply Nat.card_le_card_of_injective (fun ⟨e, he⟩ => ⟨e, ⟨he.1, Nat.le_trans he.2.1 hcol, he.2.2.1, he.2.2.2.1, he.2.2.2.2⟩⟩)
        intro ⟨e1, _⟩ ⟨e2, _⟩ h; simp only [Subtype.mk.injEq] at h ⊢; exact h
      calc freeKCountPrefix T d.val.1 k hk j + freeKSuccCountUpToPrefix T d.val.1 k hk j d.val.2
          = freeKCountPrefix T c.val.1 k hk j + freeKSuccCountUpToPrefix T c.val.1 k hk j d.val.2 := by rw [hrow]
        _ ≤ freeKCountPrefix T c.val.1 k hk j + freeKSuccCountUpToPrefix T c.val.1 k hk j c.val.2 := by omega
        _ = m + n_c := rfl
        _ ≤ n := h_unmatched_cond
        _ = freeKSuccCountPrefix T c.val.1 k hk j := rfl
        _ = freeKSuccCountPrefix T d.val.1 k hk j := by rw [hrow]
    
    -- By semistandardness, all free k's in prefix are at cols ≤ c.col
    have h_freeK_cols_le : ∀ d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu},
        d.val.1 = c.val.1 → d.val.2 < j → T d = k → ¬isForcedK T k hk d → d.val.2 ≤ c.val.2 := by
      intro d hrow hcolj hval hfree
      by_contra h_gt; push Not at h_gt
      -- c is a (k+1) at col c.col, d is a k at col d.col > c.col
      -- By row-weak: T c ≤ T d, i.e., k+1 ≤ k, contradiction
      have h_weak : T c ≤ T d := hT.1 c d (by rw [hrow]) h_gt
      rw [h2.2.1, hval] at h_weak
      simp only [Fin.le_def] at h_weak; omega
    
    -- Define the sets
    let A : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
      {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ T d = k ∧ ¬isForcedK T k hk d}
    let B : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
      {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ isUnmatchedFreeKSuccPrefix T k hk j d}
    let LHS : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} :=
      {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ T' d = k ∧ ¬isForcedK T' k hk d}
    
    -- A ∪ B ⊆ LHS
    have h_subset : A ∪ B ⊆ LHS := by
      intro d hd
      rcases hd with ⟨hrow, hcol, hcolj, hval, hfree⟩ | ⟨hrow, hcol, hunmatched⟩
      · -- d is a free k in T at cols ≤ c.col
        -- d is matched (not unmatched), so T' d = T d = k
        have h_not_unmatchedK := h_all_freeK_matched d hrow hcolj hval hfree
        have h_not_unmatchedKSucc : ¬isUnmatchedFreeKSuccPrefix T k hk j d := by
          intro h; rw [h.2.1] at hval; simp only [Fin.ext_iff] at hval; omega
        have hT'd : T' d = T d := benderKnuthPrefixMatching_unchanged' k hk j T hT d 
          h_not_unmatchedK h_not_unmatchedKSucc
        -- Need to show d is not forced in T'
        have hfree' : ¬isForcedK T' k hk d := by
          intro ⟨hT'd_k, d_below, hd_col, hd_row, hT'_below⟩
          -- isForcedK means: T' d = k and there's k+1 directly below
          -- hd_col : d_below.val.2 = d.val.2 (same column)
          -- hd_row : d.val.1.val + 1 = d_below.val.1.val (d_below is below d)
          -- hT'_below : T' d_below = ⟨k.val + 1, hk⟩
          -- 
          -- d_below is directly below d, so d_below.col = d.col < j
          have hd_below_colj : d_below.val.2 < j := by rw [hd_col]; exact hcolj
          -- d.val.1 < d_below.val.1 (d is above d_below)
          have h_row_lt : d.val.1 < d_below.val.1 := by simp only [Fin.lt_def]; omega
          -- T d < T d_below by column-strict in T (since d.col = d_below.col and d.row < d_below.row)
          have h_strict : T d < T d_below := hT.2 d d_below hd_col.symm h_row_lt
          rw [hval] at h_strict
          -- So T d_below > k, meaning T d_below ≥ k+1
          -- We need to show T' d_below ≠ ⟨k.val + 1, hk⟩
          -- If T d_below = k+1, then d_below is a free (k+1) or forced (k+1)
          -- If T d_below ≠ k+1, then T' d_below = T d_below ≠ k+1
          -- 
          -- Case 1: T d_below = k+1
          -- Then d_below is either forced or free (k+1) in T
          -- If d_below is forced (k+1) in T: there's k above d_below in T
          -- But d is above d_below and T d = k, so d_below IS forced in T
          -- A forced (k+1) stays as (k+1) in T' (not unmatched)
          -- So T' d_below = k+1, which matches hT'_below. But this is fine.
          -- 
          -- Actually, let me think about this differently.
          -- d is a free k in T (matched, so not unmatched)
          -- d_below has T d_below > k (by column-strict)
          -- If T d_below = k+1, then d_below is a (k+1) with k directly above (d)
          -- So d_below is forced as (k+1) in T
          -- A forced (k+1) is not unmatched, so T' d_below = T d_below = k+1
          -- This is consistent with hT'_below : T' d_below = k+1
          -- So there's no contradiction here!
          -- 
          -- Wait, but we're trying to show d is NOT forced in T'.
          -- isForcedK T' k hk d means T' d = k and there's k+1 below in T'
          -- We have T' d = T d = k (from hT'd)
          -- And hT'_below says T' d_below = k+1
          -- So d IS forced in T' if T' d = k and T' d_below = k+1
          -- 
          -- But hT'd_k says T' d = k, and hT'_below says T' d_below = k+1
          -- So d IS forced in T'! This contradicts what we're trying to prove.
          -- 
          -- The issue is that if d is a matched free k in T, and there's k+1 below d in T,
          -- then d is actually FORCED in T, not free!
          -- 
          -- Wait, let me reconsider. hfree says d is NOT forced in T.
          -- So there's no k+1 directly below d in T.
          -- But we're assuming d IS forced in T' (to derive a contradiction).
          -- 
          -- If d is forced in T', then T' d_below = k+1.
          -- We need to show this leads to a contradiction.
          -- 
          -- Since d_below is in the same column as d, and d.col < j, we have d_below.col < j.
          -- T' d_below = k+1 means d_below is either:
          -- 1. An unmatched free k in T that became k+1
          -- 2. A cell that was already k+1 in T and stayed k+1
          -- 
          -- Case 1: d_below was an unmatched free k in T
          -- Then T d_below = k, but h_strict says T d_below > k, contradiction.
          -- 
          -- Case 2: d_below was k+1 in T and stayed k+1
          -- Then T d_below = k+1
          -- d_below is either forced or free (k+1) in T
          -- If forced: d_below has k directly above, but d is directly above d_below and T d = k
          --   So d_below IS forced in T
          --   But then d is forced in T (has k+1 directly below), contradicting hfree!
          -- If free (k+1): d_below is either matched or unmatched
          --   If unmatched: T' d_below = k, not k+1, contradiction with hT'_below
          --   If matched: T' d_below = k+1, which is consistent
          --     But for d_below to be a free (k+1), it must NOT have k directly above
          --     But d is directly above d_below and T d = k
          --     So d_below is NOT free, it's forced!
          -- 
          -- In all cases, if T d_below = k+1, then d_below is forced, which means d is forced in T.
          -- But hfree says d is NOT forced in T. Contradiction!
          
          -- Let's prove this formally
          -- T d_below > k (from h_strict), so T d_below ≥ k+1
          have h_T_below_ge : T d_below ≥ ⟨k.val + 1, hk⟩ := by
            simp only [Fin.le_def, Fin.lt_def] at h_strict ⊢; omega
          -- If T d_below = k+1, then d_below is forced (since d is k directly above)
          -- which makes d forced in T, contradicting hfree
          by_cases h_T_below_eq : T d_below = ⟨k.val + 1, hk⟩
          · -- T d_below = k+1, so d is forced in T (has k+1 directly below)
            exfalso
            have h_d_forced : isForcedK T k hk d := ⟨hval, d_below, hd_col, hd_row, h_T_below_eq⟩
            exact hfree h_d_forced
          · -- T d_below ≠ k+1, so T' d_below = T d_below ≠ k+1
            -- d_below is not unmatched free k (since T d_below > k)
            have h_not_unmatchedK_below : ¬isUnmatchedFreeKPrefix T k hk j d_below := by
              intro h
              have h_eq := h.2.1  -- T d_below = k
              simp only [Fin.lt_def] at h_strict
              rw [h_eq] at h_strict; omega
            -- d_below is not unmatched free (k+1) (since T d_below ≠ k+1)
            have h_not_unmatchedKSucc_below : ¬isUnmatchedFreeKSuccPrefix T k hk j d_below := by
              intro h
              exact h_T_below_eq h.2.1
            have hT'_eq : T' d_below = T d_below := benderKnuthPrefixMatching_unchanged' k hk j T hT d_below
              h_not_unmatchedK_below h_not_unmatchedKSucc_below
            rw [hT'_eq] at hT'_below
            exact h_T_below_eq hT'_below
        refine ⟨hrow, hcol, hcolj, ?_, hfree'⟩
        rw [hT'd, hval]
      · -- d is an unmatched (k+1) in T at cols ≤ c.col
        -- T' d = k by definition of benderKnuthPrefixMatching
        have hT'd : T' d = k := by
          show benderKnuthPrefixMatching k hk j T hT d = k
          unfold benderKnuthPrefixMatching
          have h_not_unmatchedK : ¬isUnmatchedFreeKPrefix T k hk j d := by
            intro h
            -- h.2.1 : T d = k, but hunmatched.2.1 : T d = k+1
            have h1 := h.2.1  -- T d = k
            have h2 := hunmatched.2.1  -- T d = k+1
            rw [h1] at h2
            simp only [Fin.ext_iff] at h2
            exact (Nat.succ_ne_self k.val) h2.symm
          simp only [h_not_unmatchedK, ↓reduceIte, hunmatched, ↓reduceIte]
        have hcolj := hunmatched.1
        -- Need to show d is not forced in T'
        have hfree' : ¬isForcedK T' k hk d := by
          intro ⟨_, d_below, hd_col, hd_row, hT'_below⟩
          -- isForcedK means: T' d = k and there's k+1 directly below
          -- hd_col : d_below.val.2 = d.val.2 (same column)
          -- hd_row : d.val.1.val + 1 = d_below.val.1.val (d_below is below d)
          -- hT'_below : T' d_below = ⟨k.val + 1, hk⟩
          have hd_below_colj : d_below.val.2 < j := by rw [hd_col]; exact hcolj
          -- d.val.1 < d_below.val.1 (d is above d_below)
          have h_row_lt : d.val.1 < d_below.val.1 := by simp only [Fin.lt_def]; omega
          -- T d < T d_below by column-strict in T
          have h_strict : T d < T d_below := hT.2 d d_below hd_col.symm h_row_lt
          rw [hunmatched.2.1] at h_strict
          -- So T d_below > k+1
          -- But T' d_below = k+1, so either:
          -- 1. T d_below = k+1 and d_below stayed as k+1 (not unmatched)
          -- 2. T d_below = k and d_below was unmatched, became k+1
          -- Case 2 is impossible since T d_below > k+1 > k
          -- Case 1: T d_below = k+1
          -- But h_strict says T d_below > k+1, so T d_below ≠ k+1
          -- Contradiction!
          have h_T_below_gt : T d_below > ⟨k.val + 1, hk⟩ := h_strict
          -- T' d_below = k+1, but T d_below > k+1
          -- If T d_below > k+1, then d_below is not k or k+1 in T
          -- So d_below is unchanged in T', meaning T' d_below = T d_below > k+1
          -- But hT'_below says T' d_below = k+1, contradiction
          have h_not_unmatchedK_below : ¬isUnmatchedFreeKPrefix T k hk j d_below := by
            intro h
            have h_eq := h.2.1  -- T d_below = k
            simp only [Fin.lt_def] at h_T_below_gt
            rw [h_eq] at h_T_below_gt; omega
          have h_not_unmatchedKSucc_below : ¬isUnmatchedFreeKSuccPrefix T k hk j d_below := by
            intro h
            have h_eq := h.2.1  -- T d_below = k+1
            simp only [Fin.lt_def] at h_T_below_gt
            rw [h_eq] at h_T_below_gt; omega
          have hT'_eq : T' d_below = T d_below := benderKnuthPrefixMatching_unchanged' k hk j T hT d_below
            h_not_unmatchedK_below h_not_unmatchedKSucc_below
          rw [hT'_eq] at hT'_below
          -- hT'_below : T d_below = k+1, but h_T_below_gt : T d_below > k+1
          simp only [Fin.lt_def] at h_T_below_gt
          rw [hT'_below] at h_T_below_gt; omega
        exact ⟨hrow, hcol, hcolj, hT'd, hfree'⟩
    
    -- A and B are disjoint
    have h_disj : Disjoint A B := by
      rw [Set.disjoint_iff]
      intro d ⟨⟨_, _, _, hval, _⟩, ⟨_, _, hunmatched⟩⟩
      -- hval : T d = k, hunmatched.2.1 : T d = k+1
      have h2 := hunmatched.2.1
      rw [hval] at h2
      simp only [Fin.ext_iff] at h2
      exact (Nat.succ_ne_self k.val) h2.symm
    
    -- |A| = m (all free k's in prefix are at cols ≤ c.col)
    have h_A_card : A.ncard = m := by
      have h_A_eq : A = {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
          d.val.1 = c.val.1 ∧ d.val.2 < j ∧ T d = k ∧ ¬isForcedK T k hk d} := by
        ext d; simp only [Set.mem_ofPred_eq, A]
        constructor
        · intro ⟨hrow, _, hcolj, hval, hfree⟩; exact ⟨hrow, hcolj, hval, hfree⟩
        · intro ⟨hrow, hcolj, hval, hfree⟩
          exact ⟨hrow, h_freeK_cols_le d hrow hcolj hval hfree, hcolj, hval, hfree⟩
      rw [h_A_eq]
      rfl
    
    -- |B| = n_c
    have h_B_card : B.ncard = n_c := by
      have h_B_eq : B = {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
          d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} := by
        ext d; simp only [Set.mem_ofPred_eq, B]
        constructor
        · intro ⟨hrow, hcol, hunmatched⟩
          exact ⟨hrow, hcol, hunmatched.1, hunmatched.2.1, hunmatched.2.2.1⟩
        · intro ⟨hrow, hcol, hcolj, hval, hfree⟩
          exact ⟨hrow, hcol, h_all_kSucc_unmatched d hrow hcol hcolj hval hfree⟩
      rw [h_B_eq]
      rfl
    
    -- Combine
    calc freeKCountUpToPrefix T' c.val.1 k hk j c.val.2 
        = LHS.ncard := rfl
      _ ≥ (A ∪ B).ncard := Set.ncard_le_ncard h_subset (Set.toFinite _)
      _ = A.ncard + B.ncard := Set.ncard_union_eq h_disj
      _ = m + n_c := by rw [h_A_card, h_B_card]
  
  -- Bound 2: freeKSuccCountPrefix T' = m
  have h_bound2 : freeKSuccCountPrefix T' c.val.1 k hk j = m :=
    freeKSuccCountPrefix_benderKnuthPrefixMatching k hk j T hT c.val.1
  
  -- Combine the bounds
  calc freeKCountUpToPrefix T' c.val.1 k hk j c.val.2 
      ≥ m + n_c := h_bound1
    _ > m := by omega
    _ = freeKSuccCountPrefix T' c.val.1 k hk j := h_bound2.symm


/-- A matched free k in T stays matched (i.e., not unmatched) in T' = benderKnuthPrefixMatching T.

    **Proof idea**: If c is a matched free k in T, then T' c = T c = k (unchanged).
    For c to be unmatched free k in T', we would need freeKCountUpToPrefix T' c.col > freeKSuccCountPrefix T'.
    
    But since c was matched in T, we have freeKCountUpToPrefix T c.col ≤ freeKSuccCountPrefix T.
    The counts swap, so freeKCountUpToPrefix T' c.col ≤ freeKSuccCountPrefix T' (approximately),
    contradicting the unmatched condition. -/
private lemma matchedFreeK_stays_matched {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (_hcj : c.val.2 < j) (hTc : T c = k) (_hfree : ¬isForcedK T k hk c)
    (_h_matched : freeKCountUpToPrefix T c.val.1 k hk j c.val.2 ≤ freeKSuccCountPrefix T c.val.1 k hk j) :
    let T' := benderKnuthPrefixMatching k hk j T hT
    freeKCountUpToPrefix T' c.val.1 k hk j c.val.2 ≤ freeKSuccCountPrefix T' c.val.1 k hk j := by
  -- c is a matched free k in T: T c = k, not forced, and freeKCountUpToPrefix T c.col ≤ n.
  -- Since c is matched (not unmatched), T' c = T c = k.
  --
  -- Let m = freeKCountPrefix T, n = freeKSuccCountPrefix T, m_c = freeKCountUpToPrefix T c.col.
  -- From h_matched: m_c ≤ n.
  --
  -- We need: freeKCountUpToPrefix T' c.col ≤ freeKSuccCountPrefix T'.
  --
  -- Key insight: Since c is a matched k, all k's up to c.col are matched (matched_k_propagates_left).
  -- Matched k's stay as k in T'. Unmatched (k+1)'s become k, but they're to the right of c
  -- (by semistandardness, (k+1)'s come after k's).
  -- So freeKCountUpToPrefix T' c.col = freeKCountUpToPrefix T c.col = m_c.
  --
  -- For freeKSuccCountPrefix T':
  -- - When m ≥ n: freeKSuccCountPrefix T' = m (matched (k+1)'s + unmatched k's = n + (m-n) = m).
  --   Since m_c ≤ n ≤ m = freeKSuccCountPrefix T'. ✓
  -- - When m < n: freeKSuccCountPrefix T' = m (matched (k+1)'s + 0 unmatched k's = m).
  --   Since all k's are matched when m < n, m_c ≤ m = freeKSuccCountPrefix T'. ✓
  classical
  intro T'
  haveI : Finite {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} :=
    Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
  let m := freeKCountPrefix T c.val.1 k hk j
  let n := freeKSuccCountPrefix T c.val.1 k hk j
  let m_c := freeKCountUpToPrefix T c.val.1 k hk j c.val.2
  
  -- m_c ≤ m (cumulative ≤ total)
  have h_m_c_le_m : m_c ≤ m := freeKCountUpToPrefix_le_freeKCountPrefix T c.val.1 k hk j c.val.2
  
  -- Bound 1: freeKCountUpToPrefix T' c.col ≤ m_c
  -- (k's in T' at cols ≤ c.col ⊆ k's in T at cols ≤ c.col, since unmatched k's become (k+1)'s)
  have h_bound1 : freeKCountUpToPrefix T' c.val.1 k hk j c.val.2 ≤ m_c := by
    -- Every free k in T' at cols ≤ c.col was a free k in T at cols ≤ c.col
    -- (Unmatched k's become (k+1)'s, so they don't contribute to free k's in T')
    unfold freeKCountUpToPrefix
    apply Nat.card_mono
    · exact Set.toFinite _
    · intro d ⟨hd_row, hd_col, hd_col_j, hT'd, hd_free'⟩
      -- Need: T d = k ∧ ¬isForcedK T k hk d
      -- From T' d = k, analyze using the definition of benderKnuthPrefixMatching
      have hT'd' : benderKnuthPrefixMatching k hk j T hT d = k := hT'd
      unfold benderKnuthPrefixMatching at hT'd'
      split_ifs at hT'd' with h_unmatched_k h_unmatched_kSucc
      · -- Case: d was unmatched free k in T, so T' d = k+1, not k
        simp only [Fin.ext_iff] at hT'd'
        omega
      · -- Case: d was unmatched free (k+1) in T, so T' d = k
        -- But there are no free (k+1)'s at columns ≤ c.col (by semistandardness)
        exfalso
        -- h_unmatched_kSucc : isUnmatchedFreeKSuccPrefix T k hk j d
        -- This means T d = k+1 and d.col < j
        unfold isUnmatchedFreeKSuccPrefix at h_unmatched_kSucc
        obtain ⟨_, hd_val_kSucc, _, _⟩ := h_unmatched_kSucc
        -- d is a (k+1) at column ≤ c.col, but T c = k
        -- By semistandardness (row-weak), T d ≤ T c if d.col ≤ c.col
        -- But T d = k+1 > k = T c, contradiction
        by_cases h_col_eq : d.val.2 = c.val.2
        · -- d.col = c.col, so d = c (same row, same col)
          have h_eq : d = c := Subtype.ext (Prod.ext hd_row h_col_eq)
          rw [h_eq, hTc] at hd_val_kSucc
          simp only [Fin.ext_iff] at hd_val_kSucc
          omega
        · -- d.col < c.col
          have h_col_lt : d.val.2 < c.val.2 := Nat.lt_of_le_of_ne hd_col h_col_eq
          have h1 : T d ≤ T c := hT.1 d c hd_row h_col_lt
          rw [hd_val_kSucc, hTc] at h1
          simp only [Fin.le_def] at h1
          omega
      · -- Case: T d unchanged, so T' d = T d = k
        -- Need to show d is free in T (¬isForcedK T k hk d)
        refine ⟨hd_row, hd_col, hd_col_j, hT'd', ?_⟩
        -- If d were forced in T, we show d would be forced in T' (contradiction with hd_free')
        intro hd_forced
        -- A forced k has k+1 directly below. Forced cells are unchanged by benderKnuthPrefixMatching.
        obtain ⟨hd_val_k, d_below, hd_below_col, hd_below_row, hd_below_kSucc⟩ := hd_forced
        -- Show d is forced in T': T' d = k and T' d_below = k+1
        -- T' d = k follows from hT'd
        -- T' d_below = k+1: d_below is a forced (k+1) in T (has k directly above)
        have hd_below_forced : isForcedKSucc T k hk d_below := ⟨hd_below_kSucc, d, hd_below_col.symm, hd_below_row, hd_val_k⟩
        -- Forced (k+1) is not unmatched, so it stays unchanged
        have h_not_unmatched_kSucc : ¬isUnmatchedFreeKSuccPrefix T k hk j d_below := by
          intro h
          exact h.2.2.1 hd_below_forced
        have h_not_unmatched_k : ¬isUnmatchedFreeKPrefix T k hk j d_below := by
          intro h
          rw [h.2.1] at hd_below_kSucc
          simp only [Fin.ext_iff] at hd_below_kSucc
          omega
        have hT'_below : T' d_below = ⟨k.val + 1, hk⟩ := by
          show benderKnuthPrefixMatching k hk j T hT d_below = ⟨k.val + 1, hk⟩
          unfold benderKnuthPrefixMatching
          simp only [h_not_unmatched_k, h_not_unmatched_kSucc, ↓reduceIte, hd_below_kSucc]
        exact hd_free' ⟨hT'd, d_below, hd_below_col, hd_below_row, hT'_below⟩
    
  -- Bound 2: freeKSuccCountPrefix T' ≥ m
  -- (Free (k+1)'s in T' = matched (k+1)'s + unmatched k's = min(m,n) + (m - min(m,n)) = m)
  have h_bound2 : freeKSuccCountPrefix T' c.val.1 k hk j ≥ m := by
    -- Use the count swap lemma: freeKSuccCountPrefix T' = freeKCountPrefix T = m
    rw [freeKSuccCountPrefix_benderKnuthPrefixMatching k hk j T hT c.val.1]
  
  -- Combine: m_c ≤ n ≤ m ≤ freeKSuccCountPrefix T' (when m ≥ n)
  -- or: m_c ≤ m ≤ freeKSuccCountPrefix T' (when m < n, since all k's matched means m_c ≤ m)
  calc freeKCountUpToPrefix T' c.val.1 k hk j c.val.2 
      ≤ m_c := h_bound1
    _ ≤ m := h_m_c_le_m
    _ ≤ freeKSuccCountPrefix T' c.val.1 k hk j := h_bound2

/-- A matched free (k+1) in T stays matched (i.e., not unmatched) in T' = benderKnuthPrefixMatching T.

    **Proof idea**: If c is a matched free (k+1) in T, then T' c = T c = k+1 (unchanged).
    For c to be unmatched free (k+1) in T', we would need 
    freeKCountPrefix T' + freeKSuccCountUpToPrefix T' c.col ≤ freeKSuccCountPrefix T'.
    
    But since c was matched in T, we have freeKCountPrefix T + freeKSuccCountUpToPrefix T c.col > freeKSuccCountPrefix T.
    The counts swap, so the condition for being unmatched is not satisfied. -/
private lemma matchedFreeKSucc_stays_matched {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (T : Tableau lam mu) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hcj : c.val.2 < j) (hTc : T c = ⟨k.val + 1, hk⟩) (hfree : ¬isForcedKSucc T k hk c)
    (h_matched : freeKCountPrefix T c.val.1 k hk j + freeKSuccCountUpToPrefix T c.val.1 k hk j c.val.2 >
      freeKSuccCountPrefix T c.val.1 k hk j) :
    let T' := benderKnuthPrefixMatching k hk j T hT
    freeKCountPrefix T' c.val.1 k hk j + freeKSuccCountUpToPrefix T' c.val.1 k hk j c.val.2 >
      freeKSuccCountPrefix T' c.val.1 k hk j := by
  -- c is a matched free (k+1) in T: T c = k+1, not forced, and m + n_c > n.
  -- Since c is matched (not unmatched), T' c = T c = k+1.
  --
  -- Let m = freeKCountPrefix T, n = freeKSuccCountPrefix T, n_c = freeKSuccCountUpToPrefix T c.col.
  -- From h_matched: m + n_c > n.
  --
  -- We need: freeKCountPrefix T' + freeKSuccCountUpToPrefix T' c.col > freeKSuccCountPrefix T'.
  --
  -- Key insight: Matched (k+1)'s stay as (k+1) in T'. Unmatched k's become (k+1), but they're
  -- to the left of c (by semistandardness, k's come before (k+1)'s).
  --
  -- freeKCountPrefix T' = n (matched k's + unmatched (k+1)'s = min(m,n) + (n - min(m,n)) = n)
  -- freeKSuccCountUpToPrefix T' c.col ≥ n_c (matched (k+1)'s up to c stay, plus unmatched k's become (k+1))
  -- freeKSuccCountPrefix T' = m (matched (k+1)'s + unmatched k's = min(m,n) + (m - min(m,n)) = m)
  --
  -- From h_matched: m + n_c > n.
  -- We need: freeKCountPrefix T' + freeKSuccCountUpToPrefix T' c.col > freeKSuccCountPrefix T'
  --          n + n_c' > m (where n_c' = freeKSuccCountUpToPrefix T' c.col)
  --
  -- Case m ≥ n: n_c' ≥ n_c (matched (k+1)'s stay, unmatched k's add more).
  --   Actually, unmatched k's are to the left of c, so they contribute to n_c'.
  --   n_c' = n_c + #{unmatched k's at cols ≤ c.col} ≥ n_c.
  --   But we need n + n_c' > m, i.e., n_c' > m - n.
  --   From h_matched: m + n_c > n, so n_c > n - m. If n ≥ m, this gives n_c > 0.
  --   If m > n, then n_c > n - m is always true (RHS is negative or zero).
  --
  -- Let me reconsider. The key is that:
  -- - freeKSuccCountUpToPrefix T' c.col ≥ freeKSuccCountUpToPrefix T c.col = n_c
  --   (matched (k+1)'s up to c stay, and unmatched k's at cols < c become (k+1)'s)
  -- - freeKCountPrefix T' ≤ n (matched k's + unmatched (k+1)'s ≤ n)
  -- - freeKSuccCountPrefix T' ≤ m (matched (k+1)'s + unmatched k's ≤ m)
  --
  -- Wait, we need > not ≤. Let me think again.
  --
  -- Goal: freeKCountPrefix T' + freeKSuccCountUpToPrefix T' c.col > freeKSuccCountPrefix T'
  --
  -- We have:
  -- - freeKCountPrefix T' = n (count swap)
  -- - freeKSuccCountPrefix T' = m (count swap)
  -- - freeKSuccCountUpToPrefix T' c.col ≥ n_c + #{unmatched k's at cols ≤ c.col}
  --
  -- Since k's are to the left of (k+1)'s, all k's are at cols < c.col.
  -- So #{unmatched k's at cols ≤ c.col} = #{unmatched k's} = m - min(m,n).
  --
  -- Therefore: freeKSuccCountUpToPrefix T' c.col ≥ n_c + (m - min(m,n)).
  --
  -- Goal becomes: n + n_c + (m - min(m,n)) > m
  --               n + n_c > min(m,n)
  --
  -- From h_matched: m + n_c > n.
  -- If m ≥ n: min(m,n) = n, so we need n + n_c > n, i.e., n_c > 0. ✓ (c is a (k+1))
  -- If m < n: min(m,n) = m, so we need n + n_c > m. From h_matched: m + n_c > n ≥ m, so n_c > 0.
  --   We need n + n_c > m. Since n > m and n_c > 0, n + n_c > m. ✓
  classical
  intro T'
  haveI : Finite {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} :=
    Set.finite_coe_iff.mpr (skewYoungDiagram_finite lam mu)
  let m := freeKCountPrefix T c.val.1 k hk j
  let n := freeKSuccCountPrefix T c.val.1 k hk j
  let n_c := freeKSuccCountUpToPrefix T c.val.1 k hk j c.val.2
  
  -- n_c ≥ 1 (since c is a (k+1) at cols ≤ c.col)
  have h_n_c_pos : n_c ≥ 1 := by
    show freeKSuccCountUpToPrefix T c.val.1 k hk j c.val.2 ≥ 1
    unfold freeKSuccCountUpToPrefix
    have h_c_in : c ∈ {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
        d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} := 
      ⟨rfl, le_refl _, hcj, hTc, hfree⟩
    have h_nonempty : Nonempty {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} // 
        d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} :=
      ⟨⟨c, h_c_in⟩⟩
    haveI h_finite : Finite {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} // 
        d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} :=
      (Set.toFinite _).to_subtype
    exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨h_nonempty, h_finite⟩)
  
  -- We'll show:
  -- 1. freeKCountPrefix T' ≥ n
  -- 2. freeKSuccCountUpToPrefix T' c.col ≥ n_c
  -- 3. freeKSuccCountPrefix T' ≤ m
  -- Then: LHS ≥ n + n_c > m ≥ RHS (using h_matched: m + n_c > n, so n + n_c > m when rearranged properly)
  
  -- Wait, h_matched says m + n_c > n, which doesn't directly give n + n_c > m.
  -- Let me reconsider.
  --
  -- Actually, the key is that freeKSuccCountUpToPrefix T' c.col includes not just n_c but also
  -- the unmatched k's that became (k+1)'s at cols ≤ c.col.
  --
  -- Since all k's are at cols < c.col (by semistandardness), all unmatched k's are at cols < c.col.
  -- So: freeKSuccCountUpToPrefix T' c.col ≥ n_c + (m - min(m,n)).
  --
  -- Goal: n + (n_c + (m - min(m,n))) > m
  --       n + n_c + m - min(m,n) > m
  --       n + n_c > min(m,n)
  --
  -- From h_matched: m + n_c > n.
  -- Case m ≥ n: min(m,n) = n. Need n + n_c > n, i.e., n_c > 0. ✓
  -- Case m < n: min(m,n) = m. Need n + n_c > m. Since n > m and n_c ≥ 1, n + n_c ≥ n + 1 > m. ✓
  
  -- Bound 1: freeKCountPrefix T' = n (by swap lemma), so ≥ n
  have h_bound1 : freeKCountPrefix T' c.val.1 k hk j ≥ n := by
    rw [freeKCountPrefix_benderKnuthPrefixMatching]
    
  -- Bound 3: freeKSuccCountPrefix T' = m (by swap lemma), so ≤ m
  have h_bound3 : freeKSuccCountPrefix T' c.val.1 k hk j ≤ m := by
    rw [freeKSuccCountPrefix_benderKnuthPrefixMatching]
  
  -- Bound 2: freeKSuccCountUpToPrefix T' c.col ≥ n_c + m - n
  -- This counts free (k+1)'s in T' at cols ≤ c.col, which includes:
  -- - Matched (k+1)'s from T at cols ≤ c.col (stay as (k+1)'s): n_c - max(0, n - m)
  -- - Unmatched k's from T at cols ≤ c.col (become (k+1)'s): max(0, m - n)
  -- Total = n_c - max(0, n - m) + max(0, m - n) = n_c + m - n
  --
  -- The key insight is that c is a matched (k+1), so it stays as (k+1) in T'.
  -- Since c contributes to the count and m + n_c > n, we have n_c + m - n > 0.
  have h_bound2 : freeKSuccCountUpToPrefix T' c.val.1 k hk j c.val.2 ≥ n_c + m - n := by
    -- Strategy: Show that the set of free (k+1)'s in T' at cols ≤ c.col contains
    -- the disjoint union of:
    -- A = matched (k+1)'s from T at cols ≤ c.col (they stay as (k+1)'s)
    -- B = unmatched k's from T (all at cols ≤ c.col by semistandardness)
    -- 
    -- |A| = n_c (all (k+1)'s at cols ≤ c.col are matched since c is matched)
    -- |B| = m - min(m,n)
    -- Total ≥ n_c + (m - min(m,n)) ≥ n_c + m - n
    
    -- Define the sets
    let A : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
      {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ isMatchedFreeKSuccPrefix T k hk j d}
    let B : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
      {d | d.val.1 = c.val.1 ∧ isUnmatchedFreeKPrefix T k hk j d}
    let LHS : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} :=
      {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ 
           T' d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T' k hk d}
    
    -- A ∪ B ⊆ LHS
    have h_subset : A ∪ B ⊆ LHS := by
      intro d hd
      rcases hd with ⟨hd_row, hd_col, hd_matched⟩ | ⟨hd_row, hd_unmatched⟩
      · -- d ∈ A: matched (k+1) at cols ≤ c.col stays as (k+1)
        have hT'd : T' d = ⟨k.val + 1, hk⟩ := matched_kSucc_stays_kSucc_prefix' k hk j T hT d hd_matched
        have hfree' : ¬isForcedKSucc T' k hk d := by
          intro hforced'
          obtain ⟨_, d_above, h_col, h_row, hT'_above⟩ := hforced'
          -- Since d is not forced in T, T d_above ≠ k (for any d_above in same col and row above)
          have h_ne_k : T d_above ≠ k := by
            intro h_eq_k
            have h_forced_T : isForcedKSucc T k hk d := 
              ⟨hd_matched.2.1, d_above, h_col, h_row, h_eq_k⟩
            exact hd_matched.2.2.1 h_forced_T
          -- By column-strictness in T, T d_above < T d = k+1
          have h_lt : T d_above < T d := hT.2 d_above d h_col (by simp only [Fin.lt_def]; omega)
          rw [hd_matched.2.1] at h_lt
          have h_ne_kSucc : T d_above ≠ ⟨k.val + 1, hk⟩ := by
            intro h; rw [h] at h_lt; simp only [Fin.lt_def] at h_lt; omega
          have h_not_unmatchedK : ¬isUnmatchedFreeKPrefix T k hk j d_above := by
            intro h; exact h_ne_k h.2.1
          have h_not_unmatchedKSucc : ¬isUnmatchedFreeKSuccPrefix T k hk j d_above := by
            intro h; exact h_ne_kSucc h.2.1
          have hT'_eq : T' d_above = T d_above := benderKnuthPrefixMatching_unchanged' k hk j T hT d_above
            h_not_unmatchedK h_not_unmatchedKSucc
          rw [hT'_eq] at hT'_above
          exact h_ne_k hT'_above
        exact ⟨hd_row, hd_col, hd_matched.1, hT'd, hfree'⟩
      · -- d ∈ B: unmatched k becomes (k+1)
        -- First show d.col ≤ c.col (by semistandardness, k's come before (k+1)'s)
        have hd_col : d.val.2 ≤ c.val.2 := by
          by_contra h_gt; push Not at h_gt
          -- d is a k at col > c.col, c is a (k+1)
          -- By row-weak: T c ≤ T d, so k+1 ≤ k, contradiction
          have h_weak : T c ≤ T d := hT.1 c d hd_row.symm h_gt
          rw [hTc, hd_unmatched.2.1] at h_weak
          simp only [Fin.le_def] at h_weak; omega
        have hT'd : T' d = ⟨k.val + 1, hk⟩ := by
          simp only [T', benderKnuthPrefixMatching, hd_unmatched, ↓reduceIte]
        have hfree' : ¬isForcedKSucc T' k hk d := unmatched_k_becomes_free_kSucc_prefix' k hk j T hT d hd_unmatched
        exact ⟨hd_row, hd_col, hd_unmatched.1, hT'd, hfree'⟩
    
    -- Disjointness: A has T d = k+1, B has T d = k
    have h_disj : Disjoint A B := by
      rw [Set.disjoint_iff]
      intro d ⟨⟨_, _, hA⟩, ⟨_, hB⟩⟩
      have h1 : T d = ⟨k.val + 1, hk⟩ := hA.2.1
      have h2 : T d = k := hB.2.1
      rw [h1] at h2
      simp only [Fin.ext_iff] at h2; omega
    
    -- |B| = m - min(m, n) (number of unmatched free k's in the row)
    have hB_card : B.ncard = m - min m n := unmatchedFreeKPrefix_row_card T c.val.1 k hk j
    
    -- |A ∪ B| ≥ n_c + m - n
    -- The key insight is that in both cases (m ≥ n and m < n), we get |A ∪ B| = n_c + m - n:
    -- - When m ≥ n: All free (k+1)'s at cols ≤ c.col are matched, so |A| = n_c, |B| = m - n
    -- - When m < n: Only (k+1)'s with index > n - m are matched, so |A| = n_c - (n - m), |B| = 0
    -- In both cases: |A ∪ B| = n_c + m - n
    have h_union_bound : (A ∪ B).ncard ≥ n_c + m - n := by
      by_cases h_mn : m ≥ n
      · -- Case m ≥ n: |A| = n_c (all free (k+1)'s at cols ≤ c.col are matched), |B| = m - n
        -- First prove |A| = n_c by showing A = {all free (k+1)'s at cols ≤ c.col}
        have hA_card : A.ncard = n_c := by
          have h_eq : A = {d : {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} | 
              d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ 
              T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d} := by
            ext d
            simp only [Set.mem_ofPred_eq, A]
            constructor
            · intro ⟨hrow, hcol, hmatched⟩
              exact ⟨hrow, hcol, hmatched.1, hmatched.2.1, hmatched.2.2.1⟩
            · intro ⟨hrow, hcol, hcolj, hval, hfree_d⟩
              refine ⟨hrow, hcol, hcolj, hval, hfree_d, ?_⟩
              -- Show d is matched when m ≥ n (all free (k+1)'s are matched)
              unfold isUnmatchedFreeKSuccPrefix
              push Not
              intro _ _ _
              -- Since m ≥ n and freeKSuccCountUpToPrefix(d.col) ≥ 1, we have m + 1 > n
              have h_d_counted : freeKSuccCountUpToPrefix T d.val.1 k hk j d.val.2 ≥ 1 := by
                unfold freeKSuccCountUpToPrefix
                have h_d_in : d ∈ {e : {e : Fin N × ℕ // e ∈ skewYoungDiagram lam mu} | 
                    e.val.1 = d.val.1 ∧ e.val.2 ≤ d.val.2 ∧ e.val.2 < j ∧ 
                    T e = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk e} := 
                  ⟨rfl, le_refl _, hcolj, hval, hfree_d⟩
                have h_nonempty : Nonempty {e : {e : Fin N × ℕ // e ∈ skewYoungDiagram lam mu} // 
                    e.val.1 = d.val.1 ∧ e.val.2 ≤ d.val.2 ∧ e.val.2 < j ∧ 
                    T e = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk e} := ⟨⟨d, h_d_in⟩⟩
                haveI h_finite : Finite {e : {e : Fin N × ℕ // e ∈ skewYoungDiagram lam mu} // 
                    e.val.1 = d.val.1 ∧ e.val.2 ≤ d.val.2 ∧ e.val.2 < j ∧ 
                    T e = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk e} := (Set.toFinite _).to_subtype
                exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨h_nonempty, h_finite⟩)
              simp only [hrow]
              have h_d_counted' : freeKSuccCountUpToPrefix T c.val.1 k hk j d.val.2 ≥ 1 := by
                simp only [← hrow]; exact h_d_counted
              omega
          rw [h_eq]
          rfl
        have h_eq : (A ∪ B).ncard = n_c + (m - n) := by
          rw [Set.ncard_union_eq h_disj, hA_card, hB_card]
          simp only [Nat.min_eq_right h_mn]
        rw [h_eq]
        omega
      · -- Case m < n: |A| = n_c - (n - m) = n_c + m - n, |B| = 0
        -- When m < n, only (k+1)'s with index > n - m are matched.
        -- Since c has index n_c and is matched (m + n_c > n), we have n_c > n - m.
        -- The matched (k+1)'s at cols ≤ c.col have indices from (n - m + 1) to n_c,
        -- giving n_c - (n - m) = n_c + m - n cells.
        push Not at h_mn
        have hB_zero : B.ncard = 0 := by
          rw [hB_card]
          simp only [Nat.min_eq_left (le_of_lt h_mn), Nat.sub_self]
        -- |A ∪ B| = |A| + |B| = |A| + 0 = |A|
        rw [Set.ncard_union_eq h_disj, hB_zero, add_zero]
        -- Now prove |A| ≥ n_c + m - n
        -- Key fact: n_c > n - m (since c is matched: m + n_c > n)
        have h_n_c_gt : n_c > n - m := by omega
        -- In ℕ, n_c + m - n = n_c - (n - m) when n_c > n - m
        have h_nat_eq : n_c + m - n = n_c - (n - m) := by omega
        -- We need to show |A| ≥ n_c - (n - m)
        -- A contains all matched (k+1)'s at cols ≤ c.col
        -- The matched (k+1)'s at cols ≤ c.col are those with index > n - m
        -- Since indices range from 1 to n_c, the matched ones have indices from (n - m + 1) to n_c
        -- That's exactly n_c - (n - m) cells
        -- We show |A| ≥ n_c - (n - m) by showing c is in A and using monotonicity
        -- Actually, we prove |A| = n_c - (n - m) by constructing a bijection
        
        -- A simpler approach: show A contains c, and use that the cells in A are exactly
        -- those free (k+1)'s at cols ≤ c.col with index > n - m
        -- Since there are n_c free (k+1)'s at cols ≤ c.col total, and the first (n - m) are unmatched,
        -- we have |A| = n_c - (n - m)
        
        -- For now, prove the bound directly using the structure of matching
        -- A free (k+1) at position d (with d.col ≤ c.col) is matched iff 
        -- m + freeKSuccCountUpToPrefix(d.col) > n, i.e., freeKSuccCountUpToPrefix(d.col) > n - m
        -- The free (k+1)'s at cols ≤ c.col have indices 1, 2, ..., n_c
        -- Those with index > n - m are matched, giving n_c - (n - m) matched cells
        
        -- Define the set of all free (k+1)'s at cols ≤ c.col
        let AllKSuccUpTo : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
          {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ d.val.2 < j ∧ 
               T d = ⟨k.val + 1, hk⟩ ∧ ¬isForcedKSucc T k hk d}
        
        -- |AllKSuccUpTo| = n_c by definition
        have h_all_card : AllKSuccUpTo.ncard = n_c := rfl
        
        -- A ⊆ AllKSuccUpTo (matched ones are a subset of all)
        have h_A_subset : A ⊆ AllKSuccUpTo := by
          intro d ⟨hrow, hcol, hmatched⟩
          exact ⟨hrow, hcol, hmatched.1, hmatched.2.1, hmatched.2.2.1⟩
        
        -- The unmatched (k+1)'s at cols ≤ c.col are exactly the first (n - m) ones
        -- So |A| = n_c - (n - m)
        -- To prove this, we show that A = AllKSuccUpTo \ {unmatched ones}
        -- and |unmatched ones at cols ≤ c.col| = min(n - m, n_c) = n - m (since n_c > n - m)
        
        -- A cleaner approach: directly count using the matching criterion
        -- A cell d with index idx (= freeKSuccCountUpToPrefix(d.col)) is in A iff idx > n - m
        -- The indices of cells in AllKSuccUpTo form the set {1, 2, ..., n_c}
        -- Those with idx > n - m are {n - m + 1, ..., n_c}, which has n_c - (n - m) elements
        
        -- We prove |A| = n_c - (n - m) using a bijection argument
        -- The key is that freeKSuccCountUpToPrefix is strictly increasing on AllKSuccUpTo
        -- (each cell has a unique index)
        
        -- For the bound, we just need |A| ≥ n_c - (n - m) = n_c + m - n
        -- Since c ∈ A (c is matched by assumption h_matched), we have |A| ≥ 1
        -- But we need the exact count.
        
        -- Prove by showing the complement has size n - m
        -- Let U = AllKSuccUpTo \ A (unmatched (k+1)'s at cols ≤ c.col)
        -- We show |U| = n - m, so |A| = n_c - (n - m)
        
        let U : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
          {d | d.val.1 = c.val.1 ∧ d.val.2 ≤ c.val.2 ∧ isUnmatchedFreeKSuccPrefix T k hk j d}
        
        -- A and U partition AllKSuccUpTo
        have h_partition : AllKSuccUpTo = A ∪ U := by
          ext d
          simp only [Set.mem_ofPred_eq, Set.mem_union, A, U, AllKSuccUpTo]
          constructor
          · intro ⟨hrow, hcol, hcolj, hval, hfree⟩
            by_cases h : isUnmatchedFreeKSuccPrefix T k hk j d
            · right; exact ⟨hrow, hcol, h⟩
            · left; exact ⟨hrow, hcol, hcolj, hval, hfree, h⟩
          · intro h
            rcases h with ⟨hrow, hcol, hmatched⟩ | ⟨hrow, hcol, hunmatched⟩
            · exact ⟨hrow, hcol, hmatched.1, hmatched.2.1, hmatched.2.2.1⟩
            · unfold isUnmatchedFreeKSuccPrefix at hunmatched
              exact ⟨hrow, hcol, hunmatched.1, hunmatched.2.1, hunmatched.2.2.1⟩
        
        -- A and U are disjoint
        have h_AU_disj : Disjoint A U := by
          rw [Set.disjoint_iff]
          intro d ⟨⟨_, _, hmatched⟩, ⟨_, _, hunmatched⟩⟩
          exact hmatched.2.2.2 hunmatched
        
        -- |U| ≤ n - m (there are at most n - m unmatched (k+1)'s)
        -- Actually, |U| = min(n - m, n_c) = n - m since n_c > n - m
        -- The unmatched (k+1)'s in the row are exactly the first (n - m) free (k+1)'s
        -- Since n_c > n - m, all of these are at cols ≤ c.col
        have h_U_card : U.ncard ≤ n - m := by
          -- U ⊆ {unmatched (k+1)'s in row c.val.1}
          let U_row : Set {d : Fin N × ℕ // d ∈ skewYoungDiagram lam mu} := 
            {d | d.val.1 = c.val.1 ∧ isUnmatchedFreeKSuccPrefix T k hk j d}
          have h_U_subset : U ⊆ U_row := by
            intro d ⟨hrow, _, hunmatched⟩
            exact ⟨hrow, hunmatched⟩
          have h_U_row_card : U_row.ncard = n - min m n := by
            -- U_row is the set of unmatched (k+1)'s in row c.val.1
            -- By unmatchedFreeKSuccPrefix_row_card, this has cardinality n - min m n
            have h := unmatchedFreeKSuccPrefix_row_card T c.val.1 k hk j
            -- h : Nat.card {c | c.val.1 = c.val.1 ∧ isUnmatchedFreeKSuccPrefix T k hk j c} = n - min m n
            -- U_row = {d | d.val.1 = c.val.1 ∧ isUnmatchedFreeKSuccPrefix T k hk j d}
            -- Nat.card_coe_set_eq says Nat.card s = s.ncard
            simp only [← Nat.card_coe_set_eq] at h ⊢
            convert h using 2
          calc U.ncard ≤ U_row.ncard := Set.ncard_le_ncard h_U_subset (Set.toFinite _)
            _ = n - min m n := h_U_row_card
            _ = n - m := by simp only [Nat.min_eq_left (le_of_lt h_mn)]
        
        -- From the partition: |AllKSuccUpTo| = |A| + |U|
        -- So |A| = |AllKSuccUpTo| - |U| ≥ n_c - (n - m)
        have h_card_eq : AllKSuccUpTo.ncard = A.ncard + U.ncard := by
          rw [h_partition, Set.ncard_union_eq h_AU_disj]
        rw [h_all_card] at h_card_eq
        -- |A| = n_c - |U| ≥ n_c - (n - m)
        have h_A_ge : A.ncard ≥ n_c - (n - m) := by
          have : A.ncard = n_c - U.ncard := by omega
          calc A.ncard = n_c - U.ncard := this
            _ ≥ n_c - (n - m) := Nat.sub_le_sub_left h_U_card n_c
        rw [h_nat_eq]
        exact h_A_ge
    
    -- Final calculation
    calc freeKSuccCountUpToPrefix T' c.val.1 k hk j c.val.2 
        = LHS.ncard := rfl
      _ ≥ (A ∪ B).ncard := Set.ncard_le_ncard h_subset (Set.toFinite _)
      _ ≥ n_c + m - n := h_union_bound
    
  -- Simplified calculation using the corrected bound
  -- We show: n + (n_c + m - n) = n_c + m > m (since n_c ≥ 1)
  have h_sum_gt : n + (n_c + m - n) > m := by
    have h_pos : n_c + m > n := by omega  -- from h_matched: m + n_c > n
    calc n + (n_c + m - n) = n_c + m := by omega
      _ > m := by omega
  
  calc freeKCountPrefix T' c.val.1 k hk j + freeKSuccCountUpToPrefix T' c.val.1 k hk j c.val.2 
      ≥ n + (n_c + m - n) := Nat.add_le_add h_bound1 h_bound2
    _ > m := h_sum_gt
    _ ≥ freeKSuccCountPrefix T' c.val.1 k hk j := h_bound3

/-- `benderKnuthPrefixMatching` is an involution in the Stembridge context.

    This theorem proves that applying `benderKnuthPrefixMatching` twice returns the original
    tableau, when the Stembridge context hypotheses are satisfied.

    **Proof strategy**:
    The key insight is that the matching-based conditions are symmetric:
    - If c is unmatched free k in T, then T' c = k+1, and c becomes unmatched free (k+1) in T'
    - If c is unmatched free (k+1) in T, then T' c = k, and c becomes unmatched free k in T'
    - Forced cells and cells outside the prefix are unchanged

    The matching counts are preserved because:
    - freeKCountPrefix T' = freeKSuccCountPrefix T (unmatched k's become k+1's)
    - freeKSuccCountPrefix T' = freeKCountPrefix T (unmatched k+1's become k's)
    - The matching structure is exactly reversed

    **Note**: This requires the Stembridge context hypotheses to ensure the result is
    semistandard, which is needed for the second application of `benderKnuthPrefixMatching`. -/
theorem benderKnuthPrefixMatching_involutive_stembridge {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (nu : Fin N → ℕ)
    (k : Fin N) (hk : k.val + 1 < N)
    (j : ℕ) (hj_pos : j > 0) (T : Tableau lam mu) (hT : IsSemistandard T)
    (hbeta : IsNPartition (nu + contentColGeq T (j + 1)))
    (hk_misstep : isMisstep (nu + contentColGeq T j) k) :
    let T' := benderKnuthPrefixMatching k hk j T hT
    ∃ (hT' : IsSemistandard T')
      (_hbeta' : IsNPartition (nu + contentColGeq T' (j + 1)))
      (_hk_misstep' : isMisstep (nu + contentColGeq T' j) k),
      benderKnuthPrefixMatching k hk j T' hT' = T := by
  classical
  intro T'
  -- First, prove T' is semistandard using the existing theorem
  have hT' : IsSemistandard T' :=
    benderKnuthPrefixMatching_semistandard_stembridge hlam hmu nu k hk j hj_pos T hT hbeta hk_misstep
  -- The content in columns >= j+1 is unchanged since benderKnuthPrefixMatching only modifies columns < j
  have hcontent_suffix : contentColGeq T' (j + 1) = contentColGeq T (j + 1) := by
    ext i
    simp only [contentColGeq]
    -- The cardinality is preserved because T' c = T c for all c with c.2 ≥ j+1
    apply Nat.card_congr
    refine ⟨fun ⟨⟨c, hc⟩, hTc⟩ => ⟨⟨c, hc⟩, ?_⟩, fun ⟨⟨c, hc⟩, hTc⟩ => ⟨⟨c, hc⟩, ?_⟩, ?_, ?_⟩
    · have hc_ge : c.2 ≥ j := Nat.le_of_succ_le hc.2
      simp only [T'] at hTc
      rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT ⟨c, hc.1⟩ hc_ge] at hTc
      exact hTc
    · have hc_ge : c.2 ≥ j := Nat.le_of_succ_le hc.2
      simp only [T']
      rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT ⟨c, hc.1⟩ hc_ge]
      exact hTc
    · intro ⟨⟨c, hc⟩, _⟩; rfl
    · intro ⟨⟨c, hc⟩, _⟩; rfl
  have hbeta' : IsNPartition (nu + contentColGeq T' (j + 1)) := by
    rw [hcontent_suffix]
    exact hbeta
  -- The content in columns >= j is unchanged since benderKnuthPrefixMatching only modifies columns < j
  have hcontent_j : contentColGeq T' j = contentColGeq T j := by
    ext i
    simp only [contentColGeq]
    apply Nat.card_congr
    refine ⟨fun ⟨⟨c, hc⟩, hTc⟩ => ⟨⟨c, hc⟩, ?_⟩, fun ⟨⟨c, hc⟩, hTc⟩ => ⟨⟨c, hc⟩, ?_⟩, ?_, ?_⟩
    · simp only [T'] at hTc
      rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT ⟨c, hc.1⟩ hc.2] at hTc
      exact hTc
    · simp only [T']
      rw [benderKnuthPrefixMatching_eq_on_suffix k hk j T hT ⟨c, hc.1⟩ hc.2]
      exact hTc
    · intro ⟨⟨c, hc⟩, _⟩; rfl
    · intro ⟨⟨c, hc⟩, _⟩; rfl
  -- The misstep condition is preserved since contentColGeq T' j = contentColGeq T j
  have hk_misstep' : isMisstep (nu + contentColGeq T' j) k := by
    rw [hcontent_j]
    exact hk_misstep
  use hT', hbeta', hk_misstep'
  -- Now prove T'' = T by showing the involution property
  -- The key insight is that the matching is symmetric:
  -- - Unmatched free k in T becomes unmatched free (k+1) in T', which maps back to k
  -- - Unmatched free (k+1) in T becomes unmatched free k in T', which maps back to k+1
  -- - Forced and other cells are unchanged in both directions
  funext c
  -- Case split on whether c is in the prefix (col < j) or suffix (col >= j)
  by_cases hcj : c.val.2 < j
  · -- c is in the prefix
    unfold benderKnuthPrefixMatching
    -- Case split on the matching conditions for c in T
    by_cases h1 : isUnmatchedFreeKPrefix T k hk j c
    · -- c is unmatched free k in T, so T' c = k+1
      have hT'c : T' c = ⟨k.val + 1, hk⟩ := by
        simp only [T', benderKnuthPrefixMatching, h1, ↓reduceIte]
      -- First, c is not unmatched free k in T' (since T' c = k+1 ≠ k)
      have h1' : ¬isUnmatchedFreeKPrefix T' k hk j c := by
        unfold isUnmatchedFreeKPrefix
        intro ⟨_, hT'c_eq_k, _⟩
        rw [hT'c] at hT'c_eq_k
        simp only [Fin.ext_iff] at hT'c_eq_k
        omega
      simp only [h1', ↓reduceIte]
      -- Now we need to show c is unmatched free k+1 in T'
      by_cases h2' : isUnmatchedFreeKSuccPrefix T' k hk j c
      · -- c is unmatched free k+1 in T', so T'' c = k = T c
        simp only [h2', ↓reduceIte]
        exact h1.2.1.symm
      · -- c is not unmatched free k+1 in T', so T'' c = T' c = k+1
        -- This contradicts the fact that c was unmatched free k in T
        simp only [h2', ↓reduceIte, hT'c]
        -- We derive a contradiction using the counting argument
        exfalso
        apply h2'
        unfold isUnmatchedFreeKSuccPrefix
        refine ⟨hcj, hT'c, ?_, ?_⟩
        · -- ¬isForcedKSucc T' k hk c
          intro ⟨_, c_above, hcol, hrow, hT'ca⟩
          have hT_col_strict : T c_above < T c := hT.2 c_above c hcol (by simp only [Fin.lt_def]; omega)
          rw [h1.2.1] at hT_col_strict
          have hTca_lt_k : (T c_above).val < k.val := hT_col_strict
          simp only [T', benderKnuthPrefixMatching] at hT'ca
          split_ifs at hT'ca with ha1 ha2
          · simp only [Fin.ext_iff] at hT'ca; omega
          · have hTca_eq_ksucc : T c_above = ⟨k.val + 1, hk⟩ := ha2.2.1
            simp only [hTca_eq_ksucc] at hTca_lt_k; omega
          · simp only [Fin.ext_iff] at hT'ca; omega
        · -- The counting condition - use helper lemma
          exact unmatchedFreeK_becomes_unmatchedFreeKSucc k hk j T hT c h1
    · by_cases h2 : isUnmatchedFreeKSuccPrefix T k hk j c
      · -- c is unmatched free k+1 in T, so T' c = k
        have hT'c : T' c = k := by
          simp only [T', benderKnuthPrefixMatching, h1, h2, ↓reduceIte]
        by_cases h1' : isUnmatchedFreeKPrefix T' k hk j c
        · -- c is unmatched free k in T', so T'' c = k+1 = T c
          simp only [h1', ↓reduceIte]
          exact h2.2.1.symm
        · simp only [h1', ↓reduceIte]
          by_cases h2' : isUnmatchedFreeKSuccPrefix T' k hk j c
          · -- c is unmatched free k+1 in T', but T' c = k ≠ k+1
            exfalso
            have hT'c_eq_ksucc : T' c = ⟨k.val + 1, hk⟩ := h2'.2.1
            rw [hT'c] at hT'c_eq_ksucc
            simp only [Fin.ext_iff] at hT'c_eq_ksucc; omega
          · simp only [h2', ↓reduceIte, hT'c]
            -- T'' c = T' c = k, but T c = k+1, contradiction
            exfalso
            apply h1'
            unfold isUnmatchedFreeKPrefix
            refine ⟨hcj, hT'c, ?_, ?_⟩
            · -- ¬isForcedK T' k hk c
              intro ⟨_, c_below, hcol, hrow, hT'cb⟩
              have hT_col_strict : T c < T c_below := hT.2 c c_below hcol.symm (by simp only [Fin.lt_def]; omega)
              rw [h2.2.1] at hT_col_strict
              simp only [T', benderKnuthPrefixMatching] at hT'cb
              split_ifs at hT'cb with hb1 hb2
              · have hTcb_eq_k : T c_below = k := hb1.2.1
                simp only [hTcb_eq_k, Fin.lt_def] at hT_col_strict; omega
              · simp only [Fin.ext_iff] at hT'cb; omega
              · -- T' c_below = T c_below, so T c_below > k+1
                have hTcb_gt : (T c_below).val > k.val + 1 := by
                  simp only [Fin.lt_def] at hT_col_strict
                  exact hT_col_strict
                -- But hT'cb says T' c_below = k+1
                simp only [Fin.ext_iff] at hT'cb
                omega
            · -- The counting condition - use helper lemma
              exact unmatchedFreeKSucc_becomes_unmatchedFreeK k hk j T hT c h2
      · -- c is neither unmatched free k nor unmatched free k+1 in T
        have hT'c : T' c = T c := by
          simp only [T', benderKnuthPrefixMatching, h1, h2, ↓reduceIte]
        by_cases h1' : isUnmatchedFreeKPrefix T' k hk j c
        · simp only [h1', ↓reduceIte]
          exfalso
          have hTc_eq_k : T c = k := by rw [← hT'c]; exact h1'.2.1
          -- c was not unmatched free k in T, but T c = k
          -- So either c was forced k or c was matched free k
          have h1_impl : isForcedK T k hk c ∨ freeKCountUpToPrefix T c.val.1 k hk j c.val.2 ≤ freeKSuccCountPrefix T c.val.1 k hk j := by
            by_contra h_contra
            push Not at h_contra
            apply h1
            exact ⟨hcj, hTc_eq_k, h_contra.1, h_contra.2⟩
          rcases h1_impl with hforced | h_matched
          · -- c is forced k in T
            obtain ⟨_, c_below, hcol, hrow, hTcb⟩ := hforced
            have hcb_j : c_below.val.2 < j := by rw [hcol]; exact hcj
            have hT'cb : T' c_below = T c_below := by
              simp only [T', benderKnuthPrefixMatching]
              have hcb_not_k : ¬isUnmatchedFreeKPrefix T k hk j c_below := by
                unfold isUnmatchedFreeKPrefix
                intro ⟨_, hTcb_eq_k, _⟩
                rw [hTcb] at hTcb_eq_k
                simp only [Fin.ext_iff] at hTcb_eq_k; omega
              simp only [hcb_not_k, ↓reduceIte]
              by_cases hcb_ksucc : isUnmatchedFreeKSuccPrefix T k hk j c_below
              · exfalso
                have hcb_forced : isForcedKSucc T k hk c_below := ⟨hTcb, c, hcol.symm, hrow, hTc_eq_k⟩
                exact hcb_ksucc.2.2.1 hcb_forced
              · simp only [hcb_ksucc, ↓reduceIte]
            rw [hTcb] at hT'cb
            have hforced' : isForcedK T' k hk c := ⟨h1'.2.1, c_below, hcol, hrow, hT'cb⟩
            exact h1'.2.2.1 hforced'
          · -- c is matched free k in T (counting condition fails)
            -- First, we need to show c is not forced in T
            -- If c were forced in T, we would have taken the `hforced` case above
            -- But h1_impl is a disjunction, so we need to explicitly rule out forced
            -- Actually, we can derive ¬isForcedK from the fact that if c were forced,
            -- then c would be forced in T' (forced cells are unchanged), contradicting h1'.2.2.1
            have hfree : ¬isForcedK T k hk c := by
              intro hforced
              -- If c is forced in T, then c is forced in T' (forced cells are unchanged)
              -- This contradicts h1'.2.2.1
              obtain ⟨_, c_below, hcol, hrow, hTcb⟩ := hforced
              have hcb_j : c_below.val.2 < j := by rw [hcol]; exact hcj
              have hT'cb : T' c_below = T c_below := by
                simp only [T', benderKnuthPrefixMatching]
                have hcb_not_k : ¬isUnmatchedFreeKPrefix T k hk j c_below := by
                  unfold isUnmatchedFreeKPrefix
                  intro ⟨_, hTcb_eq_k, _⟩
                  rw [hTcb] at hTcb_eq_k
                  simp only [Fin.ext_iff] at hTcb_eq_k; omega
                simp only [hcb_not_k, ↓reduceIte]
                by_cases hcb_ksucc : isUnmatchedFreeKSuccPrefix T k hk j c_below
                · exfalso
                  have hcb_forced : isForcedKSucc T k hk c_below := ⟨hTcb, c, hcol.symm, hrow, hTc_eq_k⟩
                  exact hcb_ksucc.2.2.1 hcb_forced
                · simp only [hcb_ksucc, ↓reduceIte]
              rw [hTcb] at hT'cb
              have hforced' : isForcedK T' k hk c := ⟨h1'.2.1, c_below, hcol, hrow, hT'cb⟩
              exact h1'.2.2.1 hforced'
            -- Now use the helper lemma
            have h_stays_matched := matchedFreeK_stays_matched k hk j T hT c hcj hTc_eq_k hfree h_matched
            -- h1'.2.2.2 says freeKCountUpToPrefix T' c.col > freeKSuccCountPrefix T'
            -- h_stays_matched says freeKCountUpToPrefix T' c.col ≤ freeKSuccCountPrefix T'
            -- These contradict
            have h_unmatched := h1'.2.2.2
            exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_unmatched h_stays_matched)
        · by_cases h2' : isUnmatchedFreeKSuccPrefix T' k hk j c
          · simp only [h2', ↓reduceIte]
            exfalso
            have hTc_eq_ksucc : T c = ⟨k.val + 1, hk⟩ := by rw [← hT'c]; exact h2'.2.1
            have h2_impl : isForcedKSucc T k hk c ∨ freeKCountPrefix T c.val.1 k hk j + freeKSuccCountUpToPrefix T c.val.1 k hk j c.val.2 > freeKSuccCountPrefix T c.val.1 k hk j := by
              by_contra h_contra
              push Not at h_contra
              apply h2
              exact ⟨hcj, hTc_eq_ksucc, h_contra.1, h_contra.2⟩
            rcases h2_impl with hforced | h_matched
            · -- c is forced k+1 in T
              obtain ⟨_, c_above, hcol, hrow, hTca⟩ := hforced
              have hca_j : c_above.val.2 < j := by rw [hcol]; exact hcj
              have hT'ca : T' c_above = T c_above := by
                simp only [T', benderKnuthPrefixMatching]
                have hca_not_ksucc : ¬isUnmatchedFreeKSuccPrefix T k hk j c_above := by
                  unfold isUnmatchedFreeKSuccPrefix
                  intro ⟨_, hTca_eq_ksucc, _⟩
                  rw [hTca] at hTca_eq_ksucc
                  simp only [Fin.ext_iff] at hTca_eq_ksucc; omega
                by_cases hca_k : isUnmatchedFreeKPrefix T k hk j c_above
                · exfalso
                  have hca_forced : isForcedK T k hk c_above := ⟨hTca, c, hcol.symm, hrow, hTc_eq_ksucc⟩
                  exact hca_k.2.2.1 hca_forced
                · simp only [hca_k, hca_not_ksucc, ↓reduceIte]
              rw [hTca] at hT'ca
              have hforced' : isForcedKSucc T' k hk c := ⟨h2'.2.1, c_above, hcol, hrow, hT'ca⟩
              exact h2'.2.2.1 hforced'
            · -- c is matched free k+1 in T (counting condition > instead of ≤)
              -- First, we need to show c is not forced in T
              have hfree : ¬isForcedKSucc T k hk c := by
                intro hforced
                -- If c is forced in T, then c is forced in T' (forced cells are unchanged)
                -- This contradicts h2'.2.2.1
                obtain ⟨_, c_above, hcol, hrow, hTca⟩ := hforced
                have hca_j : c_above.val.2 < j := by rw [hcol]; exact hcj
                have hT'ca : T' c_above = T c_above := by
                  simp only [T', benderKnuthPrefixMatching]
                  have hca_not_ksucc : ¬isUnmatchedFreeKSuccPrefix T k hk j c_above := by
                    unfold isUnmatchedFreeKSuccPrefix
                    intro ⟨_, hTca_eq_ksucc, _⟩
                    rw [hTca] at hTca_eq_ksucc
                    simp only [Fin.ext_iff] at hTca_eq_ksucc; omega
                  by_cases hca_k : isUnmatchedFreeKPrefix T k hk j c_above
                  · exfalso
                    have hca_forced : isForcedK T k hk c_above := ⟨hTca, c, hcol.symm, hrow, hTc_eq_ksucc⟩
                    exact hca_k.2.2.1 hca_forced
                  · simp only [hca_k, hca_not_ksucc, ↓reduceIte]
                rw [hTca] at hT'ca
                have hforced' : isForcedKSucc T' k hk c := ⟨h2'.2.1, c_above, hcol, hrow, hT'ca⟩
                exact h2'.2.2.1 hforced'
              -- Now use the helper lemma
              have h_stays_matched := matchedFreeKSucc_stays_matched k hk j T hT c hcj hTc_eq_ksucc hfree h_matched
              -- h2'.2.2.2 says freeKCountPrefix T' + freeKSuccCountUpToPrefix T' c.col ≤ freeKSuccCountPrefix T'
              -- h_stays_matched says freeKCountPrefix T' + freeKSuccCountUpToPrefix T' c.col > freeKSuccCountPrefix T'
              -- These contradict
              have h_unmatched := h2'.2.2.2
              exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h_unmatched h_stays_matched)
          · simp only [h1', h2', ↓reduceIte, hT'c]
  · -- c is in the suffix (c.col >= j)
    have hc_ge : c.val.2 ≥ j := Nat.le_of_not_lt hcj
    -- The goal is: (if ... then ... else ...) = T c
    -- Since c.col >= j, both conditions in the if are false
    unfold benderKnuthPrefixMatching isUnmatchedFreeKPrefix isUnmatchedFreeKSuccPrefix
    simp only [not_lt.mpr hc_ge, false_and, ↓reduceIte]
    -- Now the goal is T' c = T c, and T' c = T c since c is in the suffix
    simp only [T', benderKnuthPrefixMatching, isUnmatchedFreeKPrefix, isUnmatchedFreeKSuccPrefix, not_lt.mpr hc_ge, false_and, ↓reduceIte]



/-! ## Helper lemmas for Stembridge's involution

The following lemmas establish the key properties needed for defining
and proving properties of Stembridge's involution. -/

/-- If α is not an N-partition, then there exists a misstep index. -/
lemma not_isNPartition_iff_exists_misstep (α : Fin N → ℕ) :
    ¬IsNPartition α ↔ ∃ k : Fin N, isMisstep α k := by
  simp only [_root_.IsNPartition, isMisstep]
  push Not
  constructor
  · intro ⟨i, j, hij, hαij⟩
    -- We have α j > α i with i ≤ j
    -- First handle the case i = j (which is impossible given hαij)
    have hne : i ≠ j := by
      intro heq
      subst heq
      omega
    have hlt : i < j := lt_of_le_of_ne hij hne
    -- Use well-founded induction on j.val - i.val to find a consecutive increase
    have hpos : 0 < j.val - i.val := by
      simp only [Fin.lt_def] at hlt
      omega
    generalize hd : j.val - i.val = d at hpos
    induction d using Nat.strong_induction_on generalizing i j with
    | _ d ih =>
      by_cases hcons : d = 1
      · -- Consecutive case: j.val = i.val + 1
        have hj_eq : j.val = i.val + 1 := by omega
        refine ⟨i, ?_, ?_⟩
        · have : j.val < N := j.isLt
          omega
        · convert hαij using 1
          congr 1
          ext
          exact hj_eq.symm
      · -- Non-consecutive case: d ≥ 2, check the middle
        have hd_ge_2 : d ≥ 2 := by omega
        have hmid_lt_N : i.val + 1 < N := by
          have : j.val < N := j.isLt
          omega
        let mid : Fin N := ⟨i.val + 1, hmid_lt_N⟩
        by_cases hcmp : α i < α mid
        · -- Found consecutive increase at i
          exact ⟨i, hmid_lt_N, by convert hcmp using 1⟩
        · -- α mid ≤ α i, so α mid < α j
          push Not at hcmp
          have hmid_lt_j : α mid < α j := Nat.lt_of_le_of_lt hcmp hαij
          have hmid_le_j : mid ≤ j := by simp only [Fin.le_def, mid]; omega
          have hmid_ne_j : mid ≠ j := by simp only [ne_eq, Fin.ext_iff, mid]; omega
          have hmid_lt : mid < j := lt_of_le_of_ne hmid_le_j hmid_ne_j
          have hdiff : j.val - mid.val = d - 1 := by simp only [mid]; omega
          have hdiff_pos : 0 < d - 1 := by omega
          have hdiff_lt : d - 1 < d := by omega
          exact ih (d - 1) hdiff_lt mid j hmid_le_j hmid_lt_j hmid_ne_j hmid_lt hdiff hdiff_pos
  · intro ⟨k, hk, hαk⟩
    use k, ⟨k.val + 1, hk⟩
    constructor
    · simp only [Fin.le_def]; omega
    · exact Nat.lt_of_lt_of_le hαk (le_refl _)

/-- A semistandard tableau T is not ν-Yamanouchi iff it's not semistandard or
    there exists j > 0 such that ν + cont(col_{≥j}(T)) is not an N-partition. -/
lemma not_isYamanouchi_iff {lam mu : Fin N → ℕ} {nu : Fin N → ℕ} {T : Tableau lam mu} :
    ¬IsYamanouchi nu T ↔
    ¬IsSemistandard T ∨ ∃ j : ℕ, j > 0 ∧ ¬IsNPartition (nu + contentColGeq T j) := by
  simp only [IsYamanouchi, not_and_or]
  constructor
  · intro h
    cases h with
    | inl hnotSS => left; exact hnotSS
    | inr hnotPart =>
      right
      push Not at hnotPart
      exact hnotPart
  · intro h
    cases h with
    | inl hnotSS => left; exact hnotSS
    | inr hex =>
      right
      push Not
      exact hex

/-- For a semistandard tableau T that is not ν-Yamanouchi, the violator columns set is nonempty. -/
lemma violatorColumns_nonempty_of_not_yamanouchi {lam mu : Fin N → ℕ} {nu : Fin N → ℕ}
    {T : Tableau lam mu} (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    (violatorColumns nu T).Nonempty := by
  rw [not_isYamanouchi_iff] at hnotYam
  cases hnotYam with
  | inl hnotSS => exact absurd hT hnotSS
  | inr hex =>
    obtain ⟨j, hj_pos, hnotPart⟩ := hex
    unfold violatorColumns
    simp only [Finset.filter_nonempty_iff]
    -- We need to show j is in the range and satisfies the filter condition
    let maxCol := Finset.sup Finset.univ lam
    by_cases hj_le : j ≤ maxCol + 1
    · use j
      constructor
      · exact Finset.mem_range.mpr (Nat.lt_add_one_of_le hj_le)
      · exact ⟨hj_pos, by simp only [isPartitionAtColumn]; exact hnotPart⟩
    · -- j > maxCol + 1, so contentColGeq T j = 0
      -- Use j' = maxCol + 1 instead, which is in the range
      push Not at hj_le
      use maxCol + 1
      constructor
      · exact Finset.mem_range.mpr (Nat.lt_add_one_of_le (le_refl _))
      · constructor
        · omega
        · simp only [isPartitionAtColumn]
          -- contentColGeq T (maxCol + 1) = 0 since maxCol + 1 > all column indices
          have hzero : contentColGeq T (maxCol + 1) = 0 := by
            apply contentColGeq_eq_zero_of_large
            intro i
            exact Nat.lt_add_one_of_le (Finset.le_sup (Finset.mem_univ i))
          rw [hzero, add_zero]
          -- Now we need to show nu is not an N-partition
          -- Since j > maxCol + 1, contentColGeq T j = 0 as well
          have hzero_j : contentColGeq T j = 0 := by
            apply contentColGeq_eq_zero_of_large
            intro i
            calc lam i ≤ maxCol := Finset.le_sup (Finset.mem_univ i)
              _ < maxCol + 1 := Nat.lt_succ_self _
              _ < j := hj_le
          rw [hzero_j, add_zero] at hnotPart
          exact hnotPart

/-- The misstep set is nonempty when the tuple is not a partition. -/
lemma misstepSet_nonempty_of_not_partition {α : Fin N → ℕ} (h : ¬IsNPartition α) :
    (misstepSet α).Nonempty := by
  rw [not_isNPartition_iff_exists_misstep] at h
  obtain ⟨k, hk⟩ := h
  use k
  simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hk

/-- Any column in violatorColumns is positive (j > 0). -/
lemma violatorColumn_pos {lam mu : Fin N → ℕ} {nu : Fin N → ℕ} {T : Tableau lam mu}
    {j : ℕ} (hj : j ∈ violatorColumns nu T) : j > 0 := by
  simp only [violatorColumns, Finset.mem_filter] at hj
  exact hj.2.1

/-- When j is the max violator column, j+1 gives an N-partition (or is out of range).
    This is the key hypothesis needed for benderKnuthPrefixMatching_involutive_stembridge.
    
    Note: This lemma requires `hnu : IsNPartition nu` to handle the edge case where
    j = maxCol + 1 and contentColGeq T (j+1) = 0. In that case, we need to show
    IsNPartition nu, which is given by hypothesis. -/
lemma max_violator_succ_isNPartition {lam mu : Fin N → ℕ} {nu : Fin N → ℕ}
    (hnu : IsNPartition nu)
    {T : Tableau lam mu} (_hT : IsSemistandard T)
    (hviolator : (violatorColumns nu T).Nonempty) :
    let j := (violatorColumns nu T).max' hviolator
    IsNPartition (nu + contentColGeq T (j + 1)) := by
  intro j
  have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
  simp only [violatorColumns, Finset.mem_filter, Finset.mem_range] at hj_mem
  -- j+1 is not in violatorColumns (since j is max)
  have hj1_not_violator : j + 1 ∉ violatorColumns nu T := by
    intro hj1_in
    have hle : j + 1 ≤ (violatorColumns nu T).max' hviolator := Finset.le_max' _ _ hj1_in
    omega
  simp only [violatorColumns, Finset.mem_filter, Finset.mem_range, not_and, not_not] at hj1_not_violator
  -- Either j+1 is out of range, or j+1 = 0, or isPartitionAtColumn holds
  by_cases hj1_range : j + 1 < Finset.sup Finset.univ lam + 2
  · by_cases hj1_pos : j + 1 > 0
    · -- isPartitionAtColumn nu T (j+1) holds
      exact hj1_not_violator hj1_range hj1_pos
    · -- j + 1 > 0 since j ≥ 0 (natural number), so j + 1 ≥ 1 > 0, contradiction
      omega
  · -- j+1 is beyond all columns, so contentColGeq T (j+1) = 0
    push Not at hj1_range
    have hcontent_zero : contentColGeq T (j + 1) = 0 := by
      apply contentColGeq_eq_zero_of_large
      intro i
      calc lam i ≤ Finset.sup Finset.univ lam := Finset.le_sup (Finset.mem_univ i)
        _ < j + 1 := by omega
    rw [hcontent_zero, add_zero]
    -- Need to show nu is an N-partition, which is given by hypothesis
    exact hnu

/-- Stembridge's involution on non-Yamanouchi tableaux.
    For T not ν-Yamanouchi:
    1. Let j = findViolatorColumn ν T (largest column where ν + cont(col_{≥j}(T)) is not a partition)
    2. Let k = findMisstepIndex ν T j (smallest index where the partition condition fails)
    3. Apply BK_k to columns 1, ..., j-1 of T using benderKnuthPrefixMatching

    This involution pairs non-Yamanouchi tableaux such that their alternant
    contributions cancel.

    **Key insight**: The violator column j and misstep index k are the same for T and T'
    because benderKnuthPrefixMatching leaves columns ≥ j unchanged.
    This ensures the involution is well-defined and pairs tableaux correctly.

    **Implementation note**: We use the helper functions findViolatorColumn and findMisstepIndex
    to extract j and k, then apply benderKnuthPrefixMatching. The proofs that these functions return
    valid values (Some j, Some k) follow from the non-Yamanouchi assumption.

    **Implementation**: Uses `violatorColumns_nonempty_of_not_yamanouchi` to find j,
    `misstepSet_nonempty_of_not_partition` to find k, then applies `benderKnuthPrefixMatching k j T`. -/
noncomputable def stembridgeInvolution {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    Tableau lam mu := by
  classical
  -- Step 1: Find the violator column j using violatorColumns_nonempty_of_not_yamanouchi
  have hviolator : (violatorColumns nu T).Nonempty :=
    violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
  let j := (violatorColumns nu T).max' hviolator
  -- Step 2: Get the tuple α = ν + cont(col_{≥j}(T)) and show it's not a partition
  let α := nu + contentColGeq T j
  have hnotPart : ¬IsNPartition α := by
    -- j is a violator column, so ν + cont(col_{≥j}(T)) is not a partition
    have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
    simp only [violatorColumns, Finset.mem_filter] at hj_mem
    exact hj_mem.2.2
  -- Step 3: Find the misstep index k
  have hmisstep : (misstepSet α).Nonempty := misstepSet_nonempty_of_not_partition hnotPart
  let k := (misstepSet α).min' hmisstep
  -- Step 4: Extract the bound k.val + 1 < N from the misstep property
  have hk_mem : k ∈ misstepSet α := Finset.min'_mem _ hmisstep
  have hk : k.val + 1 < N := by
    simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
    exact hk_mem.choose
  -- Step 5: Apply benderKnuthPrefixMatching k j T (using matching-based version)
  exact benderKnuthPrefixMatching k hk j T hT

/-! ### Matching-based Stembridge involution

The `stembridgeInvolutionMatching` definition is an alternative to `stembridgeInvolution` that
explicitly requires partition hypotheses. Both use `benderKnuthPrefixMatching` internally.

**Port status**: Complete. (The port to matching-based BK was completed and old code removed.)
- `stembridgeInvolutionMatching`: Definition using matching-based BK ✓
- Involutivity: Uses `benderKnuthPrefixMatching_involutive_stembridge` which is sorry-free

**Key difference from `stembridgeInvolution`**:
- Requires `hlam : IsNPartition lam`, `hmu : IsNPartition mu`, and `hnu : IsNPartition nu` parameters
- Uses matching-based conditions to determine which cells to swap
-/

/-- Stembridge's involution using matching-based Bender-Knuth (version with explicit partition hypotheses).

    This version of the Stembridge involution explicitly requires partition hypotheses for
    `lam`, `mu`, and `nu`. The matching-based approach correctly preserves row-weak
    ordering by only swapping unmatched free entries.

    **Parameters**:
    - `hlam`, `hmu`: Partition hypotheses needed for the matching-based BK to preserve semistandardness
    - `hnu`: Partition hypothesis for ν (needed to prove β is a partition when j is max violator)
    - `nu`: The ν parameter for the Yamanouchi condition
    - `T`: Input semistandard tableau
    - `hnotYam`: Proof that T is not ν-Yamanouchi

    **Implementation**: Same as `stembridgeInvolution`, but uses `benderKnuthPrefixMatching`
    in the final step. -/
noncomputable def stembridgeInvolutionMatching {lam mu : Fin N → ℕ}
    (_hlam : IsNPartition lam) (_hmu : IsNPartition mu)
    (nu : Fin N → ℕ) (_hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    Tableau lam mu := by
  classical
  -- Step 1: Find the violator column j using violatorColumns_nonempty_of_not_yamanouchi
  have hviolator : (violatorColumns nu T).Nonempty :=
    violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
  let j := (violatorColumns nu T).max' hviolator
  -- Step 2: Get the tuple α = ν + cont(col_{≥j}(T)) and show it's not a partition
  let α := nu + contentColGeq T j
  have hnotPart : ¬IsNPartition α := by
    have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
    simp only [violatorColumns, Finset.mem_filter] at hj_mem
    exact hj_mem.2.2
  -- Step 3: Find the misstep index k
  have hmisstep : (misstepSet α).Nonempty := misstepSet_nonempty_of_not_partition hnotPart
  let k := (misstepSet α).min' hmisstep
  -- Step 4: Extract the bound k.val + 1 < N from the misstep property
  have hk_mem : k ∈ misstepSet α := Finset.min'_mem _ hmisstep
  have hk : k.val + 1 < N := by
    simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
    exact hk_mem.choose
  -- Step 5: Apply benderKnuthPrefixMatching k j T (the correct matching-based version)
  exact benderKnuthPrefixMatching k hk j T hT

/-- Helper lemma: j > 0 for the max violator column.
    This is needed for `benderKnuthPrefixMatching_semistandard_stembridge`. -/
private lemma max_violator_pos {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    let hviolator := violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
    let j := (violatorColumns nu T).max' hviolator
    j > 0 := by
  intro hviolator j
  have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
  simp only [violatorColumns, Finset.mem_filter] at hj_mem
  exact hj_mem.2.1

/-- Helper lemma: β = ν + cont(col_{≥j+1}(T)) is a partition when j is the max violator.
    This is needed for `benderKnuthPrefixMatching_semistandard_stembridge`.
    
    **Note**: Requires `hnu : IsNPartition nu` to handle the edge case where j = maxCol + 1. -/
private lemma max_violator_beta_partition {lam mu : Fin N → ℕ} (nu : Fin N → ℕ) (hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    let hviolator := violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
    let j := (violatorColumns nu T).max' hviolator
    IsNPartition (nu + contentColGeq T (j + 1)) := by
  intro hviolator j
  have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
  simp only [violatorColumns, Finset.mem_filter, Finset.mem_range] at hj_mem
  -- j+1 is not in violatorColumns (since j is max)
  have hj1_not_violator : j + 1 ∉ violatorColumns nu T := by
    intro hj1_in
    have hle : j + 1 ≤ (violatorColumns nu T).max' hviolator := Finset.le_max' _ _ hj1_in
    omega
  simp only [violatorColumns, Finset.mem_filter, Finset.mem_range, not_and, not_not] at hj1_not_violator
  by_cases hj1_range : j + 1 < Finset.sup Finset.univ lam + 2
  · by_cases hj1_pos : j + 1 > 0
    · exact hj1_not_violator hj1_range hj1_pos
    · omega
  · -- j+1 is beyond all columns, so contentColGeq T (j+1) = 0
    -- In this case, nu + contentColGeq T (j+1) = nu, which is a partition by hnu
    push Not at hj1_range
    have hcontent_zero : contentColGeq T (j + 1) = 0 := by
      apply contentColGeq_eq_zero_of_large
      intro i
      calc lam i ≤ Finset.sup Finset.univ lam := Finset.le_sup (Finset.mem_univ i)
        _ < Finset.sup Finset.univ lam + 1 := Nat.lt_succ_self _
        _ ≤ j := by omega
        _ < j + 1 := Nat.lt_succ_self _
    rw [hcontent_zero, add_zero]
    exact hnu

/-- Helper lemma: k is a misstep for α = ν + cont(col_{≥j}(T)).
    This is needed for `benderKnuthPrefixMatching_semistandard_stembridge`. -/
private lemma max_violator_misstep {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    let hviolator := violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
    let j := (violatorColumns nu T).max' hviolator
    let α := nu + contentColGeq T j
    let hnotPart : ¬IsNPartition α := by
      have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
      simp only [violatorColumns, Finset.mem_filter] at hj_mem
      exact hj_mem.2.2
    let hmisstep := misstepSet_nonempty_of_not_partition hnotPart
    let k := (misstepSet α).min' hmisstep
    isMisstep α k := by
  intro hviolator j α hnotPart hmisstep k
  have hk_mem : k ∈ misstepSet α := Finset.min'_mem _ hmisstep
  simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
  exact hk_mem

/-- stembridgeInvolutionMatching preserves semistandardness. -/
theorem stembridgeInvolutionMatching_semistandard {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (nu : Fin N → ℕ) (hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    IsSemistandard (stembridgeInvolutionMatching hlam hmu nu hnu T hT hnotYam) := by
  unfold stembridgeInvolutionMatching
  -- Extract the parameters
  have hviolator := violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
  let j := (violatorColumns nu T).max' hviolator
  let α := nu + contentColGeq T j
  have hnotPart : ¬IsNPartition α := by
    have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
    simp only [violatorColumns, Finset.mem_filter] at hj_mem
    exact hj_mem.2.2
  have hmisstep := misstepSet_nonempty_of_not_partition hnotPart
  let k := (misstepSet α).min' hmisstep
  have hk_mem : k ∈ misstepSet α := Finset.min'_mem _ hmisstep
  have hk : k.val + 1 < N := by
    simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
    exact hk_mem.choose
  -- Get the required hypotheses
  have hj_pos : j > 0 := max_violator_pos nu T hT hnotYam
  have hbeta : IsNPartition (nu + contentColGeq T (j + 1)) := max_violator_beta_partition nu hnu T hT hnotYam
  have hk_misstep : isMisstep (nu + contentColGeq T j) k := max_violator_misstep nu T hT hnotYam
  -- Apply the semistandard theorem
  exact benderKnuthPrefixMatching_semistandard_stembridge hlam hmu nu k hk j hj_pos T hT hbeta hk_misstep

set_option backward.isDefEq.respectTransparency false in
/-- stembridgeInvolutionMatching is an involution on non-Yamanouchi tableaux.

    This theorem uses `benderKnuthPrefixMatching_involutive_stembridge` which is
    sorry-free. -/
theorem stembridgeInvolutionMatching_involutive {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (nu : Fin N → ℕ) (hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    let T' := stembridgeInvolutionMatching hlam hmu nu hnu T hT hnotYam
    ∃ (hT' : IsSemistandard T') (hnotYam' : ¬IsYamanouchi nu T'),
      stembridgeInvolutionMatching hlam hmu nu hnu T' hT' hnotYam' = T := by
  classical
  intro T'
  -- Extract parameters for T
  have hviolator := violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
  let j := (violatorColumns nu T).max' hviolator
  let α := nu + contentColGeq T j
  have hnotPart : ¬IsNPartition α := by
    have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
    simp only [violatorColumns, Finset.mem_filter] at hj_mem
    exact hj_mem.2.2
  have hmisstep_nonempty := misstepSet_nonempty_of_not_partition hnotPart
  let k := (misstepSet α).min' hmisstep_nonempty
  have hk_mem : k ∈ misstepSet α := Finset.min'_mem _ hmisstep_nonempty
  have hk : k.val + 1 < N := by
    simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
    exact hk_mem.choose
  -- Get the required hypotheses
  have hj_pos : j > 0 := max_violator_pos nu T hT hnotYam
  have hbeta : IsNPartition (nu + contentColGeq T (j + 1)) := max_violator_beta_partition nu hnu T hT hnotYam
  have hk_misstep : isMisstep (nu + contentColGeq T j) k := max_violator_misstep nu T hT hnotYam
  -- T' = benderKnuthPrefixMatching k hk j T hT (by definition)
  have hT'_def : T' = benderKnuthPrefixMatching k hk j T hT := rfl
  -- Use the involutivity theorem for benderKnuthPrefixMatching
  obtain ⟨hT', hbeta', hk_misstep', hT''_eq⟩ :=
    benderKnuthPrefixMatching_involutive_stembridge hlam hmu nu k hk j hj_pos T hT hbeta hk_misstep
  -- Show T' is not Yamanouchi
  have hj_violator_T' : j ∈ violatorColumns nu T' := by
    simp only [violatorColumns, Finset.mem_filter, Finset.mem_range]
    have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
    simp only [violatorColumns, Finset.mem_filter, Finset.mem_range] at hj_mem
    refine ⟨hj_mem.1, hj_mem.2.1, ?_⟩
    rw [hT'_def]
    have heq := benderKnuthPrefixMatching_contentColGeq k hk j T hT
    simp only [isPartitionAtColumn, heq]
    exact hj_mem.2.2
  have hnotYam' : ¬IsYamanouchi nu T' := by
    intro ⟨_, hyam⟩
    simp only [violatorColumns, Finset.mem_filter, Finset.mem_range] at hj_violator_T'
    exact hj_violator_T'.2.2 (hyam j hj_violator_T'.2.1)
  use hT', hnotYam'
  -- Show j' = j (max violator column for T' equals j)
  have hviolator' := violatorColumns_nonempty_of_not_yamanouchi hT' hnotYam'
  have hj'_eq : (violatorColumns nu T').max' hviolator' = j := by
    apply le_antisymm
    · apply Finset.max'_le
      intro j'' hj''_mem
      simp only [violatorColumns, Finset.mem_filter, Finset.mem_range] at hj''_mem
      by_contra hj''_gt; push Not at hj''_gt
      have hj''_ge : j'' ≥ j := Nat.le_of_lt hj''_gt
      have heq : isPartitionAtColumn nu T' j'' = isPartitionAtColumn nu T j'' := by
        simp only [isPartitionAtColumn, hT'_def]
        have hcontent := benderKnuthPrefixMatching_contentColGeq_ge k hk j T hT j'' hj''_ge
        rw [hcontent]
      rw [heq] at hj''_mem
      have hj''_not_violator : j'' ∉ violatorColumns nu T := by
        intro hj''_in
        have hle : j'' ≤ (violatorColumns nu T).max' hviolator := Finset.le_max' _ _ hj''_in
        omega
      simp only [violatorColumns, Finset.mem_filter, Finset.mem_range, not_and, not_not] at hj''_not_violator
      exact hj''_mem.2.2 (hj''_not_violator hj''_mem.1 hj''_mem.2.1)
    · exact Finset.le_max' _ _ hj_violator_T'
  -- Show α' = α
  have hα'_eq : nu + contentColGeq T' ((violatorColumns nu T').max' hviolator') = α := by
    rw [hj'_eq, hT'_def, benderKnuthPrefixMatching_contentColGeq k hk j T hT]
  -- Show misstepSet α' = misstepSet α
  have hmisstep_eq : misstepSet (nu + contentColGeq T' ((violatorColumns nu T').max' hviolator')) = misstepSet α := by
    rw [hα'_eq]
  -- Now show stembridgeInvolutionMatching nu T' hT' hnotYam' = T
  unfold stembridgeInvolutionMatching
  convert hT''_eq using 3

/-- stembridgeInvolutionMatching preserves the content in columns ≥ j. -/
theorem stembridgeInvolutionMatching_contentColGeq {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (nu : Fin N → ℕ) (hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    let hviolator := violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
    let j := (violatorColumns nu T).max' hviolator
    contentColGeq (stembridgeInvolutionMatching hlam hmu nu hnu T hT hnotYam) j = contentColGeq T j := by
  intro hviolator j
  unfold stembridgeInvolutionMatching
  exact benderKnuthPrefixMatching_contentColGeq _ _ j T hT

/-- Stembridge's involution is an involution on non-Yamanouchi tableaux.

    **Proof outline**:

    Let T' = stembridgeInvolution ν T. The involution is defined as:
    1. Let j = findViolatorColumn ν T (largest column where ν + cont(col_{≥j}(T)) is not a partition)
    2. Let k = findMisstepIndex ν T j (smallest index where the partition condition fails)
    3. Apply BK_k to columns 1, ..., j-1 of T

    To prove T' is semistandard:
    - BK_k preserves semistandardness (benderKnuthPrefixMatching_semistandard_stembridge)
    - The column restriction and recombination preserve semistandardness

    To prove T' is not Yamanouchi:
    - The violator column j and misstep index k are the same for T and T'
    - This is because BK_k only affects columns < j, not columns ≥ j

    To prove stembridgeInvolution T' = T:
    - BK_k is an involution (benderKnuthPrefixMatching_involutive_stembridge)
    - Applying BK_k twice to columns 1, ..., j-1 returns the original -/
theorem stembridgeInvolution_involutive {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (nu : Fin N → ℕ) (hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    let T' := stembridgeInvolution nu T hT hnotYam
    ∃ (hT' : IsSemistandard T') (hnotYam' : ¬IsYamanouchi nu T'),
      stembridgeInvolution nu T' hT' hnotYam' = T := by
  classical
  intro T'
  -- Extract j, k, hk from the definition of stembridgeInvolution
  have hviolator : (violatorColumns nu T).Nonempty :=
    violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
  let j := (violatorColumns nu T).max' hviolator
  let α := nu + contentColGeq T j
  have hnotPart : ¬IsNPartition α := by
    have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
    simp only [violatorColumns, Finset.mem_filter] at hj_mem
    exact hj_mem.2.2
  have hmisstep : (misstepSet α).Nonempty := misstepSet_nonempty_of_not_partition hnotPart
  let k := (misstepSet α).min' hmisstep
  have hk_mem : k ∈ misstepSet α := Finset.min'_mem _ hmisstep
  have hk : k.val + 1 < N := by
    simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
    exact hk_mem.choose
  -- Extract Stembridge context hypotheses
  have hj_pos : j > 0 := violatorColumn_pos (Finset.max'_mem _ hviolator)
  have hbeta : IsNPartition (nu + contentColGeq T (j + 1)) :=
    max_violator_succ_isNPartition hnu hT hviolator
  have hk_misstep : isMisstep (nu + contentColGeq T j) k := by
    simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
    exact hk_mem
  -- T' = benderKnuthPrefixMatching k hk j T hT (by definition)
  have hT'_def : T' = benderKnuthPrefixMatching k hk j T hT := rfl
  -- hT' : IsSemistandard T'
  have hT' : IsSemistandard T' := by
    rw [hT'_def]
    exact benderKnuthPrefixMatching_semistandard_stembridge hlam hmu nu k hk j hj_pos T hT hbeta hk_misstep
  -- Show j is a violator column for T'
  have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
  have hj_violator_T' : j ∈ violatorColumns nu T' := by
    simp only [violatorColumns, Finset.mem_filter, Finset.mem_range] at hj_mem ⊢
    refine ⟨hj_mem.1, hj_mem.2.1, ?_⟩
    rw [hT'_def]
    have heq := benderKnuthPrefixMatching_contentColGeq k hk j T hT
    simp only [isPartitionAtColumn, heq]
    exact hj_mem.2.2
  -- hnotYam' : T' is not Yamanouchi
  have hnotYam' : ¬IsYamanouchi nu T' := by
    intro ⟨_, hyam⟩
    simp only [violatorColumns, Finset.mem_filter, Finset.mem_range] at hj_violator_T'
    exact hj_violator_T'.2.2 (hyam j hj_violator_T'.2.1)
  use hT', hnotYam'
  -- Get involutivity from benderKnuthPrefixMatching_involutive_stembridge
  obtain ⟨hT'_ss, hbeta', hk_misstep', hT''_eq⟩ :=
    benderKnuthPrefixMatching_involutive_stembridge hlam hmu nu k hk j hj_pos T hT hbeta hk_misstep
  -- Show j' = j (max violator column for T' equals j)
  have hviolator' := violatorColumns_nonempty_of_not_yamanouchi hT' hnotYam'
  have hj'_eq : (violatorColumns nu T').max' hviolator' = j := by
    apply le_antisymm
    · apply Finset.max'_le
      intro j'' hj''_mem
      simp only [violatorColumns, Finset.mem_filter, Finset.mem_range] at hj''_mem
      by_contra hj''_gt; push Not at hj''_gt
      have hj''_ge : j'' ≥ j := Nat.le_of_lt hj''_gt
      have heq : isPartitionAtColumn nu T' j'' = isPartitionAtColumn nu T j'' := by
        simp only [isPartitionAtColumn, hT'_def]
        have hcontent := benderKnuthPrefixMatching_contentColGeq_ge k hk j T hT j'' hj''_ge
        rw [hcontent]
      rw [heq] at hj''_mem
      have hj''_not_violator : j'' ∉ violatorColumns nu T := by
        intro hj''_in
        have hle : j'' ≤ (violatorColumns nu T).max' hviolator := Finset.le_max' _ _ hj''_in
        omega
      simp only [violatorColumns, Finset.mem_filter, Finset.mem_range, not_and, not_not] at hj''_not_violator
      exact hj''_mem.2.2 (hj''_not_violator hj''_mem.1 hj''_mem.2.1)
    · exact Finset.le_max' _ _ hj_violator_T'
  -- Show α' = α
  have hα'_eq : nu + contentColGeq T' ((violatorColumns nu T').max' hviolator') = α := by
    rw [hj'_eq, hT'_def, benderKnuthPrefixMatching_contentColGeq k hk j T hT]
  -- Show misstepSet α' = misstepSet α
  have hmisstep_eq : misstepSet (nu + contentColGeq T' ((violatorColumns nu T').max' hviolator')) = misstepSet α := by
    rw [hα'_eq]
  -- Show k' = k
  have hnotPart' : ¬IsNPartition (nu + contentColGeq T' ((violatorColumns nu T').max' hviolator')) := by
    rw [hα'_eq]; exact hnotPart
  have hmisstep' : (misstepSet (nu + contentColGeq T' ((violatorColumns nu T').max' hviolator'))).Nonempty :=
    misstepSet_nonempty_of_not_partition hnotPart'
  have hk'_eq : (misstepSet (nu + contentColGeq T' ((violatorColumns nu T').max' hviolator'))).min' hmisstep' = k := by
    simp only [hmisstep_eq]; rfl
  -- Now show stembridgeInvolution nu T' hT' hnotYam' = T
  -- The key is that the computed parameters (j', k') equal (j, k)
  -- and benderKnuthPrefixMatching k hk j T' hT' = T by benderKnuthPrefixMatching_involutive_stembridge
  -- Use unfold instead of simp to avoid timeout
  unfold stembridgeInvolution
  -- After unfolding, the goal involves max' and min' with different proofs
  -- but these are proof-irrelevant. The goal should be:
  -- benderKnuthPrefixMatching k' hk' j' T' hT' = T
  -- where k' and j' are computed from T' using the same formulas as for T
  -- Since j' = j (by hj'_eq) and k' = k (since misstepSet α' = misstepSet α),
  -- this equals benderKnuthPrefixMatching k hk j T' hT' = T, which is hT''_eq
  convert hT''_eq using 3

/-- Stembridge's involution preserves semistandardness. -/
theorem stembridgeInvolution_semistandard {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (nu : Fin N → ℕ) (hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    IsSemistandard (stembridgeInvolution nu T hT hnotYam) := by
  obtain ⟨hT', _, _⟩ := stembridgeInvolution_involutive hlam hmu nu hnu T hT hnotYam
  exact hT'

/-- Stembridge's involution maps non-Yamanouchi to non-Yamanouchi. -/
theorem stembridgeInvolution_not_yamanouchi {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (nu : Fin N → ℕ) (hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    ¬IsYamanouchi nu (stembridgeInvolution nu T hT hnotYam) := by
  obtain ⟨_, hnotYam', _⟩ := stembridgeInvolution_involutive hlam hmu nu hnu T hT hnotYam
  exact hnotYam'

/-- The forced bijection preserves columns: if c is a forced k cell at column col,
    then its partner is a forced k+1 cell at the same column col.
    This is crucial for showing the prefix-restricted forced bijection. -/
private lemma forcedK_partner_col_eq {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedK T k hk c) :
    (forcedK_partner T k hk c hc).val.2 = c.val.2 :=
  (forcedK_partner_spec T k hk c hc).1

/-- The forced bijection preserves columns (k+1 direction). -/
private lemma forcedKSucc_partner_col_eq {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu})
    (hc : isForcedKSucc T k hk c) :
    (forcedKSucc_partner T k hk c hc).val.2 = c.val.2 :=
  (forcedKSucc_partner_spec T k hk c hc).1

/-- The forced bijection restricted to prefix: forced k cells in columns < j
    are in bijection with forced k+1 cells in columns < j.
    This follows from the full forced bijection since it preserves columns. -/
private lemma forced_k_kSucc_prefix_bijection {lam mu : Fin N → ℕ}
    (T : Tableau lam mu) (k : Fin N) (hk : k.val + 1 < N) (j : ℕ) :
    Nat.card {c // isForcedK T k hk c ∧ c.val.2 < j} =
    Nat.card {c // isForcedKSucc T k hk c ∧ c.val.2 < j} := by
  apply Nat.card_congr
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  · -- Forward: forced k in prefix → forced k+1 in prefix
    intro ⟨c, hc_forced, hc_col⟩
    refine ⟨forcedK_partner T k hk c hc_forced, forcedK_partner_isForcedKSucc T k hk c hc_forced, ?_⟩
    rw [forcedK_partner_col_eq T k hk c hc_forced]
    exact hc_col
  · -- Backward: forced k+1 in prefix → forced k in prefix
    intro ⟨c, hc_forced, hc_col⟩
    refine ⟨forcedKSucc_partner T k hk c hc_forced, forcedKSucc_partner_isForcedK T k hk c hc_forced, ?_⟩
    rw [forcedKSucc_partner_col_eq T k hk c hc_forced]
    exact hc_col
  · -- Left inverse
    intro ⟨c, hc_forced, _⟩
    simp only [Subtype.mk.injEq]
    exact forcedKSucc_partner_forcedK_partner T k hk c hc_forced
  · -- Right inverse
    intro ⟨c, hc_forced, _⟩
    simp only [Subtype.mk.injEq]
    exact forcedK_partner_forcedKSucc_partner T k hk c hc_forced

/-- The prefix content swap lemma: the count of k's in the prefix of T' equals
    the count of k+1's in the prefix of T, where T' = benderKnuthPrefixMatching.
    
    This is the key lemma for proving the content transposition property.
    
    **Proof strategy**:
    - prefix k in T' = (forced k in prefix of T) + (free k in prefix of T')
    - prefix k' in T = (forced k' in prefix of T) + (free k' in prefix of T)
    - By forced bijection: #{forced k in prefix} = #{forced k' in prefix}
    - By count swap: #{free k in prefix of T'} = #{free k' in prefix of T}
    - Therefore: prefix k in T' = prefix k' in T -/
lemma benderKnuthPrefixMatching_content_swap {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T) :
    contentTableau (benderKnuthPrefixMatching k hk j T hT) k + contentColGeq T j ⟨k.val + 1, hk⟩ =
    contentTableau T ⟨k.val + 1, hk⟩ + contentColGeq T j k := by
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  let T' := benderKnuthPrefixMatching k hk j T hT
  let k' : Fin N := ⟨k.val + 1, hk⟩
  
  -- The suffix is unchanged by benderKnuthPrefixMatching
  have h_suffix_eq : contentColGeq T' j = contentColGeq T j := 
    benderKnuthPrefixMatching_contentColGeq k hk j T hT
  have h_suffix_k : contentColGeq T' j k = contentColGeq T j k := congr_fun h_suffix_eq k
  have h_suffix_k' : contentColGeq T' j k' = contentColGeq T j k' := congr_fun h_suffix_eq k'
  
  -- Define prefix counts: cells with value i in columns < j
  let prefixCount (S : Tableau lam mu) (i : Fin N) : ℕ := 
    Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // c.val.2 < j ∧ S c = i}
  
  -- Decompose contentTableau into prefix + suffix
  have h_decomp : ∀ (S : Tableau lam mu) (i : Fin N), 
      contentTableau S i = prefixCount S i + contentColGeq S j i := by
    intro S i
    unfold contentTableau contentColGeq prefixCount
    -- Decompose {c | S c = i} into prefix ∪ suffix
    let S_all : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := {c | S c = i}
    let S_prefix : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := {c | c.val.2 < j ∧ S c = i}
    let S_suffix : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := {c | c.val.2 ≥ j ∧ S c = i}
    have h_decomp_set : S_all = S_prefix ∪ S_suffix := by
      ext c; simp only [Set.mem_ofPred_eq, Set.mem_union, S_all, S_prefix, S_suffix]
      constructor
      · intro h; by_cases hcol : c.val.2 < j
        · left; exact ⟨hcol, h⟩
        · right; exact ⟨Nat.le_of_not_lt hcol, h⟩
      · intro h; rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
    have h_disj : Disjoint S_prefix S_suffix := by
      rw [Set.disjoint_iff]; intro c ⟨⟨hlt, _⟩, ⟨hge, _⟩⟩; omega
    have h_card : S_all.ncard = S_prefix.ncard + S_suffix.ncard := by
      rw [h_decomp_set]; exact Set.ncard_union_eq h_disj
    have h_suffix_bij : S_suffix.ncard = 
        Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu ∧ c.2 ≥ j} // S ⟨c.val, c.prop.1⟩ = i} := by
      apply Nat.card_congr
      refine ⟨fun ⟨c, hc⟩ => ⟨⟨c.val, c.prop, hc.1⟩, hc.2⟩, 
              fun ⟨c, hc⟩ => ⟨⟨c.val, c.prop.1⟩, ⟨c.prop.2, hc⟩⟩, 
              fun _ => rfl, fun _ => rfl⟩
    rw [← h_suffix_bij]; exact h_card
  
  -- Apply decomposition
  have h_T'_k : contentTableau T' k = prefixCount T' k + contentColGeq T' j k := h_decomp T' k
  have h_T_k' : contentTableau T k' = prefixCount T k' + contentColGeq T j k' := h_decomp T k'
  
  -- Rewrite goal using decomposition
  -- The goal is: contentTableau T' k + contentColGeq T j k' = contentTableau T k' + contentColGeq T j k
  -- Using h_T'_k: contentTableau T' k = prefixCount T' k + contentColGeq T' j k
  -- Using h_suffix_k: contentColGeq T' j k = contentColGeq T j k
  -- Using h_T_k': contentTableau T k' = prefixCount T k' + contentColGeq T j k'
  -- Goal becomes: prefixCount T' k + contentColGeq T j k + contentColGeq T j k' = 
  --               prefixCount T k' + contentColGeq T j k' + contentColGeq T j k
  -- Which simplifies to: prefixCount T' k = prefixCount T k'
  suffices h_prefix_swap : prefixCount T' k = prefixCount T k' by
    calc contentTableau T' k + contentColGeq T j k' 
        = prefixCount T' k + contentColGeq T' j k + contentColGeq T j k' := by rw [h_T'_k]
      _ = prefixCount T' k + contentColGeq T j k + contentColGeq T j k' := by rw [h_suffix_k]
      _ = prefixCount T k' + contentColGeq T j k + contentColGeq T j k' := by rw [h_prefix_swap]
      _ = prefixCount T k' + contentColGeq T j k' + contentColGeq T j k := by ring
      _ = contentTableau T k' + contentColGeq T j k := by rw [← h_T_k']
  
  -- The key: show prefixCount T' k = prefixCount T k'
  -- This follows from the characterization of benderKnuthPrefixMatching
  
  -- Define the relevant sets
  let LHS : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := {c | c.val.2 < j ∧ T' c = k}
  let RHS : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := {c | c.val.2 < j ∧ T c = k'}
  
  -- Characterize LHS using the definition of benderKnuthPrefixMatching
  -- T' c = k iff (T c = k ∧ ¬isUnmatchedFreeKPrefix) ∨ isUnmatchedFreeKSuccPrefix
  have h_LHS_char : ∀ c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}, 
      c.val.2 < j ∧ T' c = k ↔ 
      (c.val.2 < j ∧ T c = k ∧ ¬isUnmatchedFreeKPrefix T k hk j c) ∨ 
      isUnmatchedFreeKSuccPrefix T k hk j c := by
    intro c
    constructor
    · intro ⟨hcol, hT'c⟩
      by_cases h_unmatched_k : isUnmatchedFreeKPrefix T k hk j c
      · -- c was unmatched free k, so T' c = k+1 ≠ k
        have hT'c_kSucc : T' c = k' := by
          show benderKnuthPrefixMatching k hk j T hT c = k'
          simp only [benderKnuthPrefixMatching, h_unmatched_k, ↓reduceIte, k']
        rw [hT'c_kSucc] at hT'c
        simp only [Fin.ext_iff, k'] at hT'c
        omega
      · by_cases h_unmatched_kSucc : isUnmatchedFreeKSuccPrefix T k hk j c
        · right; exact h_unmatched_kSucc
        · have hT'c_eq : T' c = T c := by
            show benderKnuthPrefixMatching k hk j T hT c = T c
            simp only [benderKnuthPrefixMatching, h_unmatched_k, h_unmatched_kSucc, ↓reduceIte]
          rw [hT'c_eq] at hT'c
          left; exact ⟨hcol, hT'c, h_unmatched_k⟩
    · intro h
      rcases h with ⟨hcol, hTc, h_not_unmatched⟩ | h_unmatched_kSucc
      · have h_not_kSucc : ¬isUnmatchedFreeKSuccPrefix T k hk j c := by
          intro h; have : T c = k' := h.2.1; rw [hTc] at this
          simp only [Fin.ext_iff, k'] at this; omega
        have hT'c : T' c = k := by
          show benderKnuthPrefixMatching k hk j T hT c = k
          simp only [benderKnuthPrefixMatching, h_not_unmatched, h_not_kSucc, ↓reduceIte, hTc]
        exact ⟨hcol, hT'c⟩
      · have hcol : c.val.2 < j := h_unmatched_kSucc.1
        have h_not_k : ¬isUnmatchedFreeKPrefix T k hk j c := by
          intro h; have h1 : T c = k := h.2.1; have h2 : T c = k' := h_unmatched_kSucc.2.1
          rw [h1] at h2; simp only [Fin.ext_iff, k'] at h2; omega
        have hT'c : T' c = k := by
          show benderKnuthPrefixMatching k hk j T hT c = k
          simp only [benderKnuthPrefixMatching, h_not_k, h_unmatched_kSucc, ↓reduceIte]
        exact ⟨hcol, hT'c⟩
  
  -- Decompose LHS = A ∪ B where A = {not unmatched k in prefix}, B = {unmatched k' in prefix}
  let A : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.2 < j ∧ T c = k ∧ ¬isUnmatchedFreeKPrefix T k hk j c}
  let B : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | isUnmatchedFreeKSuccPrefix T k hk j c}
  
  have h_LHS_eq : LHS = A ∪ B := by
    ext c; simp only [Set.mem_ofPred_eq, Set.mem_union, LHS, A, B]; exact h_LHS_char c
  
  have h_disj_AB : Disjoint A B := by
    rw [Set.disjoint_iff]
    intro c ⟨⟨_, hTc, _⟩, h_unmatched⟩
    have : T c = k' := h_unmatched.2.1
    rw [hTc] at this; simp only [Fin.ext_iff, k'] at this; omega
  
  -- Decompose RHS = C ∪ B where C = {not unmatched k' in prefix}
  let C : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
    {c | c.val.2 < j ∧ T c = k' ∧ ¬isUnmatchedFreeKSuccPrefix T k hk j c}
  
  have h_RHS_eq : RHS = C ∪ B := by
    ext c; simp only [Set.mem_ofPred_eq, Set.mem_union, RHS, C, B]
    constructor
    · intro ⟨hcol, hTc⟩
      by_cases h : isUnmatchedFreeKSuccPrefix T k hk j c
      · right; exact h
      · left; exact ⟨hcol, hTc, h⟩
    · intro h
      rcases h with ⟨hcol, hTc, _⟩ | h_unmatched
      · exact ⟨hcol, hTc⟩
      · exact ⟨h_unmatched.1, h_unmatched.2.1⟩
  
  have h_disj_CB : Disjoint C B := by
    rw [Set.disjoint_iff]; intro c ⟨⟨_, _, h_not⟩, h_is⟩; exact h_not h_is
  
  -- LHS.ncard = A.ncard + B.ncard, RHS.ncard = C.ncard + B.ncard
  have h_LHS_card : LHS.ncard = A.ncard + B.ncard := by rw [h_LHS_eq]; exact Set.ncard_union_eq h_disj_AB
  have h_RHS_card : RHS.ncard = C.ncard + B.ncard := by rw [h_RHS_eq]; exact Set.ncard_union_eq h_disj_CB
  
  -- The key: A.ncard = C.ncard (not unmatched k's = not unmatched k''s in prefix)
  -- This follows from the same argument as notUnmatched_k_kSucc_card_eq but restricted to prefix
  -- A = {forced k in prefix} ∪ {matched free k in prefix}
  -- C = {forced k' in prefix} ∪ {matched free k' in prefix}
  
  have h_A_eq_C : A.ncard = C.ncard := by
    -- Decompose A and C into forced and matched free parts
    let A_forced : Set _ := {c | c.val.2 < j ∧ isForcedK T k hk c}
    let A_matched : Set _ := {c | c.val.2 < j ∧ isMatchedFreeKPrefix T k hk j c}
    let C_forced : Set _ := {c | c.val.2 < j ∧ isForcedKSucc T k hk c}
    let C_matched : Set _ := {c | c.val.2 < j ∧ isMatchedFreeKSuccPrefix T k hk j c}
    
    have h_A_decomp : A = A_forced ∪ A_matched := by
      ext c; simp only [Set.mem_ofPred_eq, Set.mem_union, A, A_forced, A_matched]
      constructor
      · intro ⟨hcol, hTc, h_not_unmatched⟩
        by_cases hforced : isForcedK T k hk c
        · left; exact ⟨hcol, hforced⟩
        · right; exact ⟨hcol, hcol, hTc, hforced, h_not_unmatched⟩
      · intro h; rcases h with ⟨hcol, hforced⟩ | ⟨hcol, hmatched⟩
        · exact ⟨hcol, hforced.1, fun h => h.2.2.1 hforced⟩
        · exact ⟨hcol, hmatched.2.1, hmatched.2.2.2⟩
    
    have h_C_decomp : C = C_forced ∪ C_matched := by
      ext c; simp only [Set.mem_ofPred_eq, Set.mem_union, C, C_forced, C_matched]
      constructor
      · intro ⟨hcol, hTc, h_not_unmatched⟩
        by_cases hforced : isForcedKSucc T k hk c
        · left; exact ⟨hcol, hforced⟩
        · right; exact ⟨hcol, hcol, hTc, hforced, h_not_unmatched⟩
      · intro h; rcases h with ⟨hcol, hforced⟩ | ⟨hcol, hmatched⟩
        · exact ⟨hcol, hforced.1, fun h => h.2.2.1 hforced⟩
        · exact ⟨hcol, hmatched.2.1, hmatched.2.2.2⟩
    
    -- Forced cells in prefix are in bijection (forced bijection preserves column)
    have h_forced_bij : A_forced.ncard = C_forced.ncard := by
      apply Nat.card_congr
      refine ⟨fun ⟨c, hc⟩ => ?_, fun ⟨c, hc⟩ => ?_, ?_, ?_⟩
      · -- toFun: forced k → forced k'
        have hforced : isForcedK T k hk c := hc.2
        let c_partner := forcedK_partner T k hk c hforced
        have h_partner_forced : isForcedKSucc T k hk c_partner := 
          forcedK_partner_isForcedKSucc T k hk c hforced
        have h_same_col : c_partner.val.2 = c.val.2 := 
          (forcedK_partner_spec T k hk c hforced).1
        exact ⟨c_partner, ⟨h_same_col ▸ hc.1, h_partner_forced⟩⟩
      · -- invFun: forced k' → forced k
        have hforced : isForcedKSucc T k hk c := hc.2
        let c_partner := forcedKSucc_partner T k hk c hforced
        have h_partner_forced : isForcedK T k hk c_partner := 
          forcedKSucc_partner_isForcedK T k hk c hforced
        have h_same_col : c_partner.val.2 = c.val.2 := 
          (forcedKSucc_partner_spec T k hk c hforced).1
        exact ⟨c_partner, ⟨h_same_col ▸ hc.1, h_partner_forced⟩⟩
      · intro ⟨c, hc⟩; simp only [Subtype.mk.injEq]
        exact forcedKSucc_partner_forcedK_partner T k hk c hc.2
      · intro ⟨c, hc⟩; simp only [Subtype.mk.injEq]
        exact forcedK_partner_forcedKSucc_partner T k hk c hc.2
    
    -- Matched free cells in prefix are in bijection
    have h_matched_bij : A_matched.ncard = C_matched.ncard := by
      -- Both equal ∑ᵢ min(freeKCountPrefix, freeKSuccCountPrefix) over rows
      -- Use matchedFreeK_card_eq_matchedFreeKSucc_card adapted to prefix
      -- The key is that isMatchedFreeKPrefix and isMatchedFreeKSuccPrefix have the same count
      -- because both equal min(freeKCountPrefix, freeKSuccCountPrefix) summed over rows
      
      -- Define the sets by row
      let A_row (i : Fin N) : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
        {c | c.val.1 = i ∧ isMatchedFreeKPrefix T k hk j c}
      let C_row (i : Fin N) : Set {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := 
        {c | c.val.1 = i ∧ isMatchedFreeKSuccPrefix T k hk j c}
      
      -- A_matched = ⋃ᵢ A_row i
      have h_A_union : A_matched = ⋃ i : Fin N, A_row i := by
        ext c; simp only [Set.mem_ofPred_eq, Set.mem_iUnion, A_matched, A_row]
        constructor
        · intro ⟨_, hmatched⟩; exact ⟨c.val.1, rfl, hmatched⟩
        · intro ⟨_, _, hmatched⟩; exact ⟨hmatched.1, hmatched⟩
      
      -- C_matched = ⋃ᵢ C_row i
      have h_C_union : C_matched = ⋃ i : Fin N, C_row i := by
        ext c; simp only [Set.mem_ofPred_eq, Set.mem_iUnion, C_matched, C_row]
        constructor
        · intro ⟨_, hmatched⟩; exact ⟨c.val.1, rfl, hmatched⟩
        · intro ⟨_, _, hmatched⟩; exact ⟨hmatched.1, hmatched⟩
      
      -- The unions are disjoint
      have h_A_disj : ∀ i i' : Fin N, i ≠ i' → Disjoint (A_row i) (A_row i') := by
        intro i i' hne; rw [Set.disjoint_iff]
        intro c ⟨⟨hi, _⟩, ⟨hi', _⟩⟩; rw [hi] at hi'; exact hne hi'
      have h_C_disj : ∀ i i' : Fin N, i ≠ i' → Disjoint (C_row i) (C_row i') := by
        intro i i' hne; rw [Set.disjoint_iff]
        intro c ⟨⟨hi, _⟩, ⟨hi', _⟩⟩; rw [hi] at hi'; exact hne hi'
      
      -- Per-row cardinality equality
      have h_row_eq : ∀ i : Fin N, (A_row i).ncard = (C_row i).ncard := by
        intro i
        -- A_row i = {c | c.val.1 = i ∧ isMatchedFreeKPrefix T k hk j c}
        -- matchedFreeKPrefix_row_card gives Nat.card of this set = min(m, n)
        have h1 : (A_row i).ncard = Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
            c.val.1 = i ∧ isMatchedFreeKPrefix T k hk j c} := rfl
        have h2 : (C_row i).ncard = Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} | 
            c.val.1 = i ∧ isMatchedFreeKSuccPrefix T k hk j c} := rfl
        rw [h1, h2, matchedFreeKPrefix_row_card T i k hk j, matchedFreeKSuccPrefix_row_card T i k hk j]
      
      -- Use finsum for the disjoint union
      rw [h_A_union, h_C_union]
      have hfin_A : ∀ i, (A_row i).Finite := fun i => Set.toFinite _
      have hfin_C : ∀ i, (C_row i).Finite := fun i => Set.toFinite _
      have h_A_pw : Pairwise fun i j => Disjoint (A_row i) (A_row j) := 
        fun i j hij => h_A_disj i j hij
      have h_C_pw : Pairwise fun i j => Disjoint (C_row i) (C_row j) := 
        fun i j hij => h_C_disj i j hij
      rw [Set.ncard_iUnion_of_finite hfin_A h_A_pw]
      rw [Set.ncard_iUnion_of_finite hfin_C h_C_pw]
      congr 1; ext i; exact h_row_eq i
    
    -- Disjointness
    have h_disj_A : Disjoint A_forced A_matched := by
      rw [Set.disjoint_iff]; intro c ⟨⟨_, hforced⟩, ⟨_, hmatched⟩⟩
      exact hmatched.2.2.1 hforced
    have h_disj_C : Disjoint C_forced C_matched := by
      rw [Set.disjoint_iff]; intro c ⟨⟨_, hforced⟩, ⟨_, hmatched⟩⟩
      exact hmatched.2.2.1 hforced
    
    calc A.ncard = (A_forced ∪ A_matched).ncard := by rw [h_A_decomp]
      _ = A_forced.ncard + A_matched.ncard := Set.ncard_union_eq h_disj_A
      _ = C_forced.ncard + C_matched.ncard := by rw [h_forced_bij, h_matched_bij]
      _ = (C_forced ∪ C_matched).ncard := (Set.ncard_union_eq h_disj_C).symm
      _ = C.ncard := by rw [← h_C_decomp]
  
  -- Final calculation
  calc prefixCount T' k = LHS.ncard := rfl
    _ = A.ncard + B.ncard := h_LHS_card
    _ = C.ncard + B.ncard := by rw [h_A_eq_C]
    _ = RHS.ncard := h_RHS_card.symm
    _ = prefixCount T k' := rfl

/-- The total count of k and k' entries is preserved by benderKnuthPrefixMatching.
    This follows from the fact that the transformation only swaps k and k' values,
    so the sum of their counts is unchanged. -/
private lemma benderKnuthPrefixMatching_content_total {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T) :
    contentTableau (benderKnuthPrefixMatching k hk j T hT) k + 
    contentTableau (benderKnuthPrefixMatching k hk j T hT) ⟨k.val + 1, hk⟩ =
    contentTableau T k + contentTableau T ⟨k.val + 1, hk⟩ := by
  -- The key insight: benderKnuthPrefixMatching only swaps k and k' values in the prefix,
  -- so the total count of k + k' is preserved.
  let T' := benderKnuthPrefixMatching k hk j T hT
  let k' : Fin N := ⟨k.val + 1, hk⟩
  
  -- For each cell c: T' c ∈ {k, k'} ↔ T c ∈ {k, k'}
  have h_eq_set : ∀ c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu}, 
      T' c = k ∨ T' c = k' ↔ T c = k ∨ T c = k' := by
    intro c
    simp only [T', benderKnuthPrefixMatching]
    split_ifs with h1 h2
    · -- c is unmatched free k in prefix, so T' c = k'
      constructor
      · intro _; left; exact h1.2.1
      · intro _; right; rfl
    · -- c is unmatched free k' in prefix, so T' c = k
      constructor
      · intro _; right; exact h2.2.1
      · intro _; left; rfl
    · -- c is neither, so T' c = T c
      rfl
  
  classical
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} := skewYoungDiagram_fintype lam mu
  
  -- The key: cells with value k or k' form the same set in T' and T
  -- So the total count is preserved
  
  -- Use Finset.card instead of Nat.card for easier manipulation
  simp only [contentTableau]
  
  -- Convert to Finset.card
  have h1 : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // T' c = k} = 
      Finset.card (Finset.univ.filter (fun c => T' c = k)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h2 : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // T' c = k'} = 
      Finset.card (Finset.univ.filter (fun c => T' c = k')) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h3 : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // T c = k} = 
      Finset.card (Finset.univ.filter (fun c => T c = k)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h4 : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam mu} // T c = k'} = 
      Finset.card (Finset.univ.filter (fun c => T c = k')) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  
  rw [h1, h2, h3, h4]
  
  -- Now we need to show the Finset.card equation
  -- The sets {c | T' c = k ∨ T' c = k'} and {c | T c = k ∨ T c = k'} are equal
  have h_union_T' : Finset.univ.filter (fun c => T' c = k) ∪ Finset.univ.filter (fun c => T' c = k') = 
      Finset.univ.filter (fun c => T' c = k ∨ T' c = k') := by
    ext c; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  
  have h_union_T : Finset.univ.filter (fun c => T c = k) ∪ Finset.univ.filter (fun c => T c = k') = 
      Finset.univ.filter (fun c => T c = k ∨ T c = k') := by
    ext c; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  
  have h_eq : Finset.univ.filter (fun c => T' c = k ∨ T' c = k') = 
      Finset.univ.filter (fun c => T c = k ∨ T c = k') := by
    ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h_eq_set c
  
  have h_disjoint_T' : Disjoint (Finset.univ.filter (fun c => T' c = k)) 
      (Finset.univ.filter (fun c => T' c = k')) := by
    rw [Finset.disjoint_filter]
    intro c _ h1 h2; rw [h1] at h2; simp only [Fin.ext_iff, k'] at h2; omega
  
  have h_disjoint_T : Disjoint (Finset.univ.filter (fun c => T c = k)) 
      (Finset.univ.filter (fun c => T c = k')) := by
    rw [Finset.disjoint_filter]
    intro c _ h1 h2; rw [h1] at h2; simp only [Fin.ext_iff, k'] at h2; omega
  
  calc Finset.card (Finset.univ.filter (fun c => T' c = k)) + 
       Finset.card (Finset.univ.filter (fun c => T' c = k'))
      = Finset.card (Finset.univ.filter (fun c => T' c = k) ∪ Finset.univ.filter (fun c => T' c = k')) := by
          rw [Finset.card_union_of_disjoint h_disjoint_T']
    _ = Finset.card (Finset.univ.filter (fun c => T' c = k ∨ T' c = k')) := by rw [h_union_T']
    _ = Finset.card (Finset.univ.filter (fun c => T c = k ∨ T c = k')) := by rw [h_eq]
    _ = Finset.card (Finset.univ.filter (fun c => T c = k) ∪ Finset.univ.filter (fun c => T c = k')) := by rw [← h_union_T]
    _ = Finset.card (Finset.univ.filter (fun c => T c = k)) + 
          Finset.card (Finset.univ.filter (fun c => T c = k')) := by
            rw [Finset.card_union_of_disjoint h_disjoint_T]


/-- Symmetric version of the content swap lemma: the content of k' in T' plus the suffix count of k
    equals the content of k in T plus the suffix count of k'. -/
private lemma benderKnuthPrefixMatching_content_swap' {lam mu : Fin N → ℕ}
    (k : Fin N) (hk : k.val + 1 < N) (j : ℕ)
    (T : Tableau lam mu) (hT : IsSemistandard T) :
    contentTableau (benderKnuthPrefixMatching k hk j T hT) ⟨k.val + 1, hk⟩ + contentColGeq T j k =
    contentTableau T k + contentColGeq T j ⟨k.val + 1, hk⟩ := by
  -- This follows from the fact that the total content of k and k' is preserved
  -- combined with the original content swap lemma
  have h1 := benderKnuthPrefixMatching_content_swap k hk j T hT
  let T' := benderKnuthPrefixMatching k hk j T hT
  let k' : Fin N := ⟨k.val + 1, hk⟩
  
  -- Total content preservation using the lemma above
  have h_total := benderKnuthPrefixMatching_content_total k hk j T hT
  
  -- Now use h1 and h_total to prove the goal
  -- h1: contentTableau T' k + contentColGeq T j k' = contentTableau T k' + contentColGeq T j k
  -- h_total: contentTableau T' k + contentTableau T' k' = contentTableau T k + contentTableau T k'
  -- Goal: contentTableau T' k' + contentColGeq T j k = contentTableau T k + contentColGeq T j k'
  -- Note: T' and k' are let bindings that are automatically unfolded by omega
  omega


/-- The Stembridge involution changes the content in such a way that
    ν + cont(T') + ρ differs from ν + cont(T) + ρ by a transposition.

    Specifically, if T' = stembridgeInvolution ν T, then there exist indices k ≠ k'
    such that ν + cont(T') + ρ = (ν + cont(T) + ρ) ∘ swap(k, k').

    This is the key property that enables the sign-reversing argument:
    the Stembridge involution applies BK_k to a prefix of T, which swaps the
    counts of k and k+1 in that prefix. Combined with the specific choice of
    the misstep index k, this results in the full expression being related
    by a transposition. -/
theorem stembridgeInvolution_content_transposition {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    ∃ k k' : Fin N, k ≠ k' ∧
      nu + contentTableau (stembridgeInvolution nu T hT hnotYam) + rho N =
      (nu + contentTableau T + rho N) ∘ Equiv.swap k k' := by
  classical
  -- Step 1: Extract j, k, hk from stembridgeInvolution definition
  -- (These are the same computations as in stembridgeInvolution)
  have hviolator : (violatorColumns nu T).Nonempty :=
    violatorColumns_nonempty_of_not_yamanouchi hT hnotYam
  let j := (violatorColumns nu T).max' hviolator
  let α := nu + contentColGeq T j
  have hnotPart : ¬IsNPartition α := by
    have hj_mem : j ∈ violatorColumns nu T := Finset.max'_mem _ hviolator
    simp only [violatorColumns, Finset.mem_filter] at hj_mem
    exact hj_mem.2.2
  have hmisstep : (misstepSet α).Nonempty := misstepSet_nonempty_of_not_partition hnotPart
  let k := (misstepSet α).min' hmisstep
  have hk_mem : k ∈ misstepSet α := Finset.min'_mem _ hmisstep
  have hk : k.val + 1 < N := by
    simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
    exact hk_mem.choose
  -- Step 2: Define k' = k + 1
  let k' : Fin N := ⟨k.val + 1, hk⟩
  -- Step 3: Show k ≠ k'
  have hkk' : k ≠ k' := by
    intro h
    simp only [Fin.ext_iff, k'] at h
    omega
  -- Step 4: The key is that stembridgeInvolution = benderKnuthPrefixMatching k hk j T hT
  use k, k', hkk'
  -- Step 5: Show that stembridgeInvolution equals benderKnuthPrefixMatching with our extracted parameters
  have hT'_eq : stembridgeInvolution nu T hT hnotYam = benderKnuthPrefixMatching k hk j T hT := by
    unfold stembridgeInvolution
    rfl
    
  -- Derive the key identity α k' = α k + 1 (needed for both k and k' cases)
  have hk_misstep : isMisstep α k := by
    simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
    exact hk_mem
  have hbeta : IsNPartition (nu + contentColGeq T (j + 1)) := max_violator_beta_partition nu hnu T hT hnotYam
  have hcontent_k_eq : contentColGeq T j k = contentColGeq T (j + 1) k := 
    column_j_no_k_at_max_violator nu k hk j T hT hbeta hk_misstep
  have hα_diff : α k' = α k + 1 := by
    obtain ⟨hk', hα_lt⟩ := hk_misstep
    simp only [Pi.add_apply, α] at hα_lt
    have hβ_mono : (nu + contentColGeq T (j + 1)) k' ≤ (nu + contentColGeq T (j + 1)) k := by
      apply hbeta
      simp only [Fin.le_def, k']
      omega
    simp only [Pi.add_apply] at hβ_mono
    have hsucc_k' := contentColGeq_succ_le T hT j k'
    simp only [Pi.add_apply, α, k'] at *
    rw [hcontent_k_eq] at hα_lt
    omega
    
  -- The content transposition property follows from the structure of benderKnuthPrefixMatching.
  --
  -- Key insight: We need to show that (nu + contentTableau T' + rho N) = (nu + contentTableau T + rho N) ∘ swap k k'
  --
  -- This is equivalent to showing:
  -- 1. For i ≠ k, k': contentTableau T' i = contentTableau T i (unchanged)
  -- 2. nu k + contentTableau T' k + rho N k = nu k' + contentTableau T k' + rho N k'
  -- 3. nu k' + contentTableau T' k' + rho N k' = nu k + contentTableau T k + rho N k
  --
  -- Part 1 follows from benderKnuthPrefixMatching only changing k and k+1 entries.
  --
  -- Parts 2 and 3 follow from:
  -- - contentColGeq T' j = contentColGeq T j (suffix unchanged)
  -- - The prefix content swaps: (k's in prefix of T') = (k+1's in prefix of T) and vice versa
  -- - The specific choice of k as the misstep index ensures the rho contribution balances out
  --
  -- The proof proceeds by showing the function equality pointwise.
  -- For each i, we need: (nu + contentTableau T' + rho N) i = (nu + contentTableau T + rho N) (swap k k' i)
  let T' := stembridgeInvolution nu T hT hnotYam
  funext i
  simp only [Pi.add_apply, Function.comp_apply]
  by_cases hi_k : i = k
  · -- Case i = k: need LHS k = RHS k' (since swap k k' k = k')
    subst hi_k
    simp only [Equiv.swap_apply_left]
    -- Need: nu k + contentTableau T' k + rho N k = nu k' + contentTableau T k' + rho N k'
    
    -- Step 3: Compute the content change
    -- The BK transformation swaps unmatched free k's with unmatched free k+1's in the prefix.
    -- The change in k-count is Δ = (unmatched free k+1's) - (unmatched free k's) in prefix.
    -- 
    -- Key fact: Δ = (prefix k+1 count) - (prefix k count) because:
    -- - forced k's = forced k+1's (bijection between forced pairs)
    -- - So Δ = (free k+1's) - (free k's) = (prefix k+1's - forced k+1's) - (prefix k's - forced k's)
    --        = (prefix k+1's) - (prefix k's)
    --
    -- Therefore:
    -- contentTableau T' k = contentTableau T k + Δ = contentTableau T k + (prefix k+1's) - (prefix k's)
    -- contentTableau T' k' = contentTableau T k' - Δ = contentTableau T k' - (prefix k+1's) + (prefix k's)
    --
    -- The goal is: nu k + contentTableau T' k + rho N k = nu k' + contentTableau T k' + rho N k'
    -- 
    -- Substituting and simplifying:
    -- nu k + contentTableau T k + Δ + rho N k = nu k' + contentTableau T k' + rho N k'
    -- Δ = (nu k' - nu k) + (contentTableau T k' - contentTableau T k) + (rho N k' - rho N k)
    -- Δ = (nu k' - nu k) + (contentTableau T k' - contentTableau T k) - 1  (since rho N k - rho N k' = 1)
    --
    -- Now, contentTableau T i = (prefix i count) + (suffix i count) = (prefix i count) + contentColGeq T j i
    -- So contentTableau T k' - contentTableau T k = (prefix k' - prefix k) + (contentColGeq T j k' - contentColGeq T j k)
    --                                             = Δ + (α k' - nu k') - (α k - nu k)
    --                                             = Δ + (α k' - α k) - (nu k' - nu k)
    --                                             = Δ + 1 - (nu k' - nu k)  (using α k' = α k + 1)
    --
    -- Substituting:
    -- Δ = (nu k' - nu k) + (Δ + 1 - (nu k' - nu k)) - 1
    -- Δ = Δ + 1 - 1
    -- Δ = Δ ✓
    --
    -- So the identity holds! The proof reduces to showing that the algebra works out.
    
    -- Directly compute using the identity α k' = α k + 1 and rho difference
    simp only [Pi.add_apply, α, k'] at hα_diff
    simp only [rho_apply]
    -- Use the fact that contentTableau = prefix + suffix, and the suffix is unchanged
    -- The key is: (nu + contentTableau T' + rho N) k = (nu + contentTableau T + rho N) k'
    -- Using α k' = α k + 1 and the structure of the transformation
    
    -- Let's compute both sides:
    -- LHS = nu k + contentTableau T' k + (N - 1 - k)
    -- RHS = nu k' + contentTableau T k' + (N - 1 - (k + 1)) = nu k' + contentTableau T k' + (N - 2 - k)
    --
    -- contentTableau T' k = contentTableau T k + Δ where Δ = (prefix k+1) - (prefix k) in T
    -- contentTableau T k = (prefix k) + α k - nu k
    -- contentTableau T k' = (prefix k') + α k' - nu k'
    --
    -- LHS = nu k + (prefix k) + Δ + α k - nu k + (N - 1 - k)
    --     = (prefix k) + Δ + α k + (N - 1 - k)
    --
    -- RHS = nu k' + (prefix k') + α k' - nu k' + (N - 2 - k)
    --     = (prefix k') + α k' + (N - 2 - k)
    --     = (prefix k') + α k + 1 + (N - 2 - k)  (using α k' = α k + 1)
    --     = (prefix k') + α k + (N - 1 - k)
    --
    -- So we need: (prefix k) + Δ = (prefix k')
    -- i.e., Δ = (prefix k') - (prefix k)
    --
    -- This is exactly what Δ is! (The change in k-count in the prefix equals the difference in k+1 and k counts in the prefix.)
    
    -- The proof follows from the structure of benderKnuthPrefixMatching
    rw [hT'_eq]
    
    -- The goal is: nu k + contentTableau T' k + rho N k = nu k' + contentTableau T k' + rho N k'
    -- 
    -- Key facts:
    -- 1. α k' = α k + 1 (proved above as hα_diff)
    -- 2. contentTableau T' k = contentTableau T k + Δ where Δ = (unmatched free k+1's) - (unmatched free k's) in prefix
    -- 3. contentTableau T' k' = contentTableau T k' - Δ
    -- 4. rho N k - rho N k' = 1
    -- 5. Δ = prefix_k' - prefix_k (because forced pairs and matched pairs are equal)
    -- 
    -- The goal follows from algebraic manipulation:
    -- LHS = nu k + (contentTableau T k + Δ) + rho N k
    -- RHS = nu k' + contentTableau T k' + rho N k'
    -- 
    -- Expanding contentTableau using prefix + suffix:
    -- contentTableau T k = prefix_k + contentColGeq T j k
    -- contentTableau T k' = prefix_k' + contentColGeq T j k'
    -- 
    -- Since α = nu + contentColGeq T j:
    -- contentColGeq T j k = α k - nu k
    -- contentColGeq T j k' = α k' - nu k' = α k + 1 - nu k' (using hα_diff)
    -- 
    -- LHS = nu k + prefix_k + Δ + (α k - nu k) + rho N k
    --     = prefix_k + Δ + α k + rho N k
    -- 
    -- RHS = nu k' + prefix_k' + (α k + 1 - nu k') + rho N k'
    --     = prefix_k' + α k + 1 + rho N k'
    --     = prefix_k' + α k + 1 + (rho N k - 1)  (since rho N k' = rho N k - 1)
    --     = prefix_k' + α k + rho N k
    -- 
    -- So LHS = RHS iff prefix_k + Δ = prefix_k'
    -- i.e., Δ = prefix_k' - prefix_k
    -- 
    -- This holds because:
    -- Δ = (unmatched free k+1's) - (unmatched free k's)
    --   = (free k+1's) - (free k's)  (since matched counts are equal)
    --   = (prefix_k' - forced k+1's) - (prefix_k - forced k's)
    --   = prefix_k' - prefix_k  (since forced counts are equal)
    
    -- The proof is a direct calculation using the above identities
    simp only [α, k'] at *
    
    -- We need to show that the content change combined with nu and rho gives the swap
    -- The key is that contentTableau T' k = contentTableau T k + (prefix_k' - prefix_k)
    -- where prefix_i = contentTableau T i - contentColGeq T j i
    
    -- Let's define the prefix counts
    let prefix_k := contentTableau T k - contentColGeq T j k
    let prefix_k' := contentTableau T k' - contentColGeq T j k'
    
    -- The content of T' at k equals (prefix of T at k') + (suffix of T at k)
    -- because the transformation swaps unmatched free k's and k+1's in the prefix
    -- and the suffix is unchanged
    
    -- Actually, the simplest approach is to use the fact that:
    -- contentTableau T' k = (k's in prefix of T') + contentColGeq T j k
    -- where (k's in prefix of T') = prefix_k + (unmatched free k+1's) - (unmatched free k's)
    --                             = prefix_k + (prefix_k' - prefix_k)  (by the argument above)
    --                             = prefix_k'
    
    -- So contentTableau T' k = prefix_k' + contentColGeq T j k
    --                        = (contentTableau T k' - contentColGeq T j k') + contentColGeq T j k
    --                        = contentTableau T k' - (α k' - nu k') + (α k - nu k)
    --                        = contentTableau T k' - α k' + nu k' + α k - nu k
    --                        = contentTableau T k' - (α k + 1) + nu k' + α k - nu k  (using hα_diff)
    --                        = contentTableau T k' + nu k' - nu k - 1
    
    -- Goal: nu k + contentTableau T' k + (N - 1 - k.val) = nu k' + contentTableau T k' + (N - 1 - (k.val + 1))
    -- LHS = nu k + (contentTableau T k' + nu k' - nu k - 1) + (N - 1 - k.val)
    --     = contentTableau T k' + nu k' - 1 + (N - 1 - k.val)
    --     = contentTableau T k' + nu k' + (N - 2 - k.val)
    -- RHS = nu k' + contentTableau T k' + (N - 2 - k.val)
    -- LHS = RHS ✓
    
    -- The proof requires showing that contentTableau T' k = contentTableau T k' + nu k' - nu k - 1
    -- This follows from the structure of benderKnuthPrefixMatching and the identity α k' = α k + 1
    
    -- Use the content swap lemma
    have h_content_swap := benderKnuthPrefixMatching_content_swap k hk j T hT
    -- h_content_swap : contentTableau T' k + contentColGeq T j k' = contentTableau T k' + contentColGeq T j k
    
    -- The goal is: nu k + contentTableau T' k + (N - 1 - k.val) = nu k' + contentTableau T k' + (N - 2 - k.val)
    -- 
    -- From h_content_swap: contentTableau T' k = contentTableau T k' + contentColGeq T j k - contentColGeq T j k'
    -- From hα_diff (after simp): nu k' + contentColGeq T j k' = nu k + contentColGeq T j k + 1
    -- So: contentColGeq T j k' = nu k + contentColGeq T j k + 1 - nu k'
    --     contentColGeq T j k - contentColGeq T j k' = contentColGeq T j k - (nu k + contentColGeq T j k + 1 - nu k')
    --                                                = nu k' - nu k - 1
    -- Therefore: contentTableau T' k = contentTableau T k' + nu k' - nu k - 1
    --
    -- Substituting into the goal:
    -- LHS = nu k + (contentTableau T k' + nu k' - nu k - 1) + (N - 1 - k.val)
    --     = contentTableau T k' + nu k' - 1 + N - 1 - k.val
    -- RHS = nu k' + contentTableau T k' + (N - 2 - k.val)
    --     = nu k' + contentTableau T k' + N - 2 - k.val
    -- LHS = RHS ✓
    
    -- The proof follows by omega using h_content_swap and hα_diff
    omega
  · by_cases hi_k' : i = k'
    · -- Case i = k': need LHS k' = RHS k (since swap k k' k' = k)
      subst hi_k'
      simp only [Equiv.swap_apply_right]
      -- Symmetric to the i = k case
      
      -- Use the content swap lemma
      have h_content_swap := benderKnuthPrefixMatching_content_swap k hk j T hT
      have h_total := benderKnuthPrefixMatching_content_total k hk j T hT
      
      -- Derive hα_diff (same as in i = k case)
      have hk_misstep : isMisstep α k := by
        simp only [misstepSet, Finset.mem_filter, Finset.mem_univ, true_and] at hk_mem
        exact hk_mem
      have hbeta : IsNPartition (nu + contentColGeq T (j + 1)) := max_violator_beta_partition nu hnu T hT hnotYam
      have hcontent_k_eq : contentColGeq T j k = contentColGeq T (j + 1) k := 
        column_j_no_k_at_max_violator nu k hk j T hT hbeta hk_misstep
      have hα_diff : α k' = α k + 1 := by
        obtain ⟨hk', hα_lt⟩ := hk_misstep
        simp only [Pi.add_apply, α] at hα_lt
        have hβ_mono : (nu + contentColGeq T (j + 1)) k' ≤ (nu + contentColGeq T (j + 1)) k := by
          apply hbeta
          simp only [Fin.le_def, k']
          omega
        simp only [Pi.add_apply] at hβ_mono
        have hsucc_k' := contentColGeq_succ_le T hT j k'
        simp only [Pi.add_apply, α, k'] at *
        rw [hcontent_k_eq] at hα_lt
        omega
      
      simp only [Pi.add_apply, α, k'] at hα_diff
      simp only [rho_apply]
      rw [hT'_eq]
      
      -- Use the symmetric content swap lemma
      have h_content_swap' := benderKnuthPrefixMatching_content_swap' k hk j T hT
      -- Note: k' = ⟨k.val + 1, hk⟩ by definition
      show nu k' + contentTableau (benderKnuthPrefixMatching k hk j T hT) k' + (N - 1 - k'.val) = 
           nu k + contentTableau T k + (N - 1 - k.val)
      -- Unfold k' in the goal
      simp only [k']
      
      omega
    · -- Case i ≠ k, k': content unchanged, swap is identity
      simp only [Equiv.swap_apply_of_ne_of_ne hi_k hi_k']
      -- Need: nu i + contentTableau T' i + rho N i = nu i + contentTableau T i + rho N i
      -- This follows because benderKnuthPrefixMatching only changes cells with value k or k'
      -- so contentTableau T' i = contentTableau T i for i ≠ k, k'
      have hcontent_eq : contentTableau (benderKnuthPrefixMatching k hk j T hT) i = contentTableau T i := by
        apply contentTableau_eq_of_iff
        intro c
        -- T' c = i ↔ T c = i when i ≠ k, k'
        simp only [benderKnuthPrefixMatching]
        split_ifs with h1 h2
        · -- c is unmatched free k in prefix, so T' c = k+1
          -- Since i ≠ k', we have T' c = k+1 ≠ i, and T c = k ≠ i
          constructor
          · intro heq
            simp only [Fin.ext_iff, k'] at heq hi_k'
            omega
          · intro heq
            have hTc : T c = k := h1.2.1
            rw [hTc] at heq
            exact (hi_k heq.symm).elim
        · -- c is unmatched free k+1 in prefix, so T' c = k
          -- Since i ≠ k, we have T' c = k ≠ i, and T c = k+1 ≠ i
          constructor
          · intro heq
            exact (hi_k heq.symm).elim
          · intro heq
            have hTc : T c = ⟨k.val + 1, hk⟩ := h2.2.1
            rw [hTc] at heq
            simp only [Fin.ext_iff, k'] at heq hi_k'
            omega
        · -- c is unchanged
          rfl
      rw [hT'_eq, hcontent_eq]

/-- The key sign-reversing property: the alternant contributions of T and its
    image under Stembridge's involution are negatives of each other.

    This is because cont(T') differs from cont(T) by swapping entries k and k+1,
    and by alternant_swap, this negates the alternant. -/
theorem stembridgeInvolution_sign_reversing {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T) :
    (alternant (nu + contentTableau (stembridgeInvolution nu T hT hnotYam) + rho N) :
      MvPolynomial (Fin N) R) =
    -(alternant (nu + contentTableau T + rho N) : MvPolynomial (Fin N) R) := by
  -- Use the content transposition property and alternant_swap
  obtain ⟨k, k', hkk', hswap⟩ := stembridgeInvolution_content_transposition nu hnu T hT hnotYam
  rw [hswap]
  exact alternant_swap hkk'

/-- Helper lemma: if f = f ∘ swap k k', then f(k) = f(k'). -/
private lemma eq_of_comp_swap_eq {f : Fin N → ℕ} {k k' : Fin N}
    (h : f = f ∘ Equiv.swap k k') : f k = f k' := by
  have : f k = (f ∘ Equiv.swap k k') k := congrFun h k
  simp only [Function.comp_apply, Equiv.swap_apply_left] at this
  exact this

/-- Helper lemma: if f = f ∘ swap k k' and k ≠ k', then f has repeated entries. -/
private lemma has_repeated_of_comp_swap_eq {f : Fin N → ℕ} {k k' : Fin N} (hkk' : k ≠ k')
    (h : f = f ∘ Equiv.swap k k') : ∃ i j : Fin N, i ≠ j ∧ f i = f j := by
  exact ⟨k, k', hkk', eq_of_comp_swap_eq h⟩

/-- If the Stembridge involution has a fixed point, then the alternant is zero.

    This is the key lemma that allows us to use `Finset.sum_involution`:
    we only need the involution to be fixed-point free when the alternant is non-zero.

    **Proof**: If T' = T, then by `stembridgeInvolution_content_transposition`:
    - `f = f ∘ swap k k'` where `f = nu + contentTableau T + rho N` and `k ≠ k'`
    - This means `f(k) = f(k')`, so `f` has repeated entries
    - By `alternant_eq_zero_of_repeated`, the alternant is zero. -/
theorem stembridgeInvolution_fixed_point_implies_alternant_zero {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T)
    (heq : stembridgeInvolution nu T hT hnotYam = T) :
    (alternant (nu + contentTableau T + rho N) : MvPolynomial (Fin N) R) = 0 := by
  -- Get k, k' from the content transposition
  obtain ⟨k, k', hkk', hswap⟩ := stembridgeInvolution_content_transposition nu hnu T hT hnotYam
  -- Since T' = T, the content is the same, so f = f ∘ swap k k'
  have hf : nu + contentTableau T + rho N = (nu + contentTableau T + rho N) ∘ Equiv.swap k k' := by
    simp only [heq] at hswap
    exact hswap
  -- This means f has repeated entries
  have hrepeated : ∃ i j : Fin N, i ≠ j ∧ (nu + contentTableau T + rho N) i = (nu + contentTableau T + rho N) j :=
    has_repeated_of_comp_swap_eq hkk' hf
  -- By alternant_eq_zero_of_repeated, the alternant is zero
  exact alternant_eq_zero_of_repeated hrepeated

/-- Stembridge's involution has no fixed points on non-Yamanouchi tableaux
    when the alternant is non-zero.

    **Proof strategy**: The contrapositive of `stembridgeInvolution_fixed_point_implies_alternant_zero`.
    If T' = T, then the alternant is zero, so if the alternant is non-zero, then T' ≠ T.

    Note: The unconditional version (without the alternant hypothesis) would require
    a detailed analysis of the Bender-Knuth structure, showing that the prefix content
    cannot be exactly balanced for non-Yamanouchi tableaux. For the application in
    `alternant_sum_non_yamanouchi_eq_zero`, the conditional version suffices. -/
theorem stembridgeInvolution_no_fixed_points_of_alternant_ne_zero {lam mu : Fin N → ℕ} (nu : Fin N → ℕ)
    (hnu : IsNPartition nu)
    (T : Tableau lam mu) (hT : IsSemistandard T) (hnotYam : ¬IsYamanouchi nu T)
    (hne : (alternant (nu + contentTableau T + rho N) : MvPolynomial (Fin N) R) ≠ 0) :
    stembridgeInvolution nu T hT hnotYam ≠ T := by
  intro heq
  exact hne (stembridgeInvolution_fixed_point_implies_alternant_zero nu hnu T hT hnotYam heq)

/-- The type of non-Yamanouchi semistandard tableaux is finite. -/
noncomputable instance nonYamanouchiTableau_fintype (lam mu nu : Fin N → ℕ) :
    Fintype {T : Tableau lam mu // IsSemistandard T ∧ ¬IsYamanouchi nu T} := by
  have h : Set.Finite {T : Tableau lam mu | IsSemistandard T ∧ ¬IsYamanouchi nu T} := by
    apply Set.Finite.subset (Set.toFinite (Set.univ : Set (Tableau lam mu)))
    intro T _
    exact Set.mem_univ T
  exact Set.Finite.fintype h

/-- Composition distributes over addition of N-tuples. -/
private lemma comp_add_tuple (α β : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) :
    (α + β) ∘ σ = α ∘ σ + β ∘ σ := by
  ext i
  simp only [Pi.add_apply, Function.comp_apply]

/-- Renaming variables in x^α by permutation σ gives x^(α ∘ σ⁻¹). -/
private theorem rename_xPow (σ : Equiv.Perm (Fin N)) (α : Fin N → ℕ) :
    MvPolynomial.rename σ (xPow α : MvPolynomial (Fin N) R) = xPow (α ∘ σ.symm) := by
  simp only [xPow_eq_monomialExp, AlgebraicCombinatorics.SymmetricFunctions.monomialExp]
  rw [map_prod]
  -- Goal: ∏ x, X (σ x) ^ α x = ∏ i, X i ^ (α ∘ σ.symm) i
  -- Reindex the RHS product by σ.symm
  rw [← Equiv.prod_comp σ.symm]
  congr 1
  ext i
  simp only [Function.comp_apply, Equiv.apply_symm_apply, map_pow, MvPolynomial.rename_X]

/-- Helper lemma: any swap in Fin N can be expressed as a product of adjacent swaps.
    This is used to prove polynomial symmetry from adjacent swap invariance. -/
private lemma swap_of_adjacent_swaps (p : MvPolynomial (Fin N) R)
    (h_adj : ∀ k : Fin N, ∀ hk : k.val + 1 < N, 
      MvPolynomial.rename (Equiv.swap k ⟨k.val + 1, hk⟩) p = p)
    (i j : Fin N) (hij : i ≠ j) :
    MvPolynomial.rename (Equiv.swap i j) p = p := by
  wlog h : i < j generalizing i j with hsymm
  · rw [Equiv.swap_comm]
    have : j < i := by
      rcases Fin.lt_or_lt_of_ne hij with h' | h'
      · exact absurd h' h
      · exact h'
    exact hsymm j i hij.symm this
  obtain ⟨d, hd⟩ : ∃ d, j.val = i.val + d + 1 := by
    use j.val - i.val - 1
    omega
  induction d generalizing i j with
  | zero =>
    have hk : i.val + 1 < N := by omega
    have hj : j = ⟨i.val + 1, hk⟩ := Fin.ext (by omega)
    subst hj
    exact h_adj i hk
  | succ d ih =>
    have hi1 : i.val + 1 < N := by omega
    let i1 : Fin N := ⟨i.val + 1, hi1⟩
    have hi_ne_i1 : i ≠ i1 := by simp only [i1, ne_eq, Fin.ext_iff]; omega
    have hi_ne_j : i ≠ j := ne_of_lt h
    have hi1_ne_j : i1 ≠ j := by simp only [i1, ne_eq, Fin.ext_iff]; omega
    have hi1_lt_j : i1 < j := by simp only [i1, Fin.lt_def]; omega
    have hd' : j.val = i1.val + d + 1 := by simp only [i1]; omega
    have key : Equiv.swap i j = Equiv.swap i1 j * Equiv.swap i i1 * Equiv.swap i1 j := by
      have h' := Equiv.swap_mul_swap_mul_swap hi_ne_i1 hi_ne_j
      rw [Equiv.swap_comm j i] at h'
      exact h'.symm
    rw [key]
    simp only [Equiv.Perm.coe_mul]
    rw [← MvPolynomial.rename_rename, ← MvPolynomial.rename_rename]
    rw [ih i1 j hi1_ne_j hi1_lt_j hd']
    rw [h_adj i hi1]
    rw [ih i1 j hi1_ne_j hi1_lt_j hd']

/-- Helper lemma: if a polynomial is invariant under all adjacent swaps, it is symmetric.
    This uses the fact that adjacent transpositions generate the symmetric group. -/
private lemma isSymmetric_of_adjacent_swap_invariant (p : MvPolynomial (Fin N) R)
    (h_adj : ∀ k : Fin N, ∀ hk : k.val + 1 < N, 
      MvPolynomial.rename (Equiv.swap k ⟨k.val + 1, hk⟩) p = p) :
    p.IsSymmetric := by
  intro σ
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => 
    simp only [Equiv.Perm.coe_one]
    exact MvPolynomial.rename_id_apply p
  | mul_swap σ i j hij ih =>
    simp only [Equiv.Perm.coe_mul]
    conv_lhs => rw [← MvPolynomial.rename_rename]
    rw [swap_of_adjacent_swaps p h_adj i j hij]
    exact ih

/-- The skew Schur polynomial is symmetric when lam and mu are N-partitions.

    This follows from Bender-Knuth involutions: for each adjacent transposition (k, k+1),
    the Bender-Knuth involution BK_k gives a bijection on semistandard tableaux
    that swaps the content entries k and k+1. Since adjacent transpositions generate
    the symmetric group, this proves skewSchurPoly is invariant under all permutations.

    The partition hypotheses are required for `benderKnuth_involutive_partition`. -/
lemma skewSchurPoly_isSymmetric (lam mu : Fin N → ℕ)
    (hlam : IsNPartition lam) (hmu : IsNPartition mu) :
    (skewSchurPoly lam mu : MvPolynomial (Fin N) R).IsSymmetric := by
  apply isSymmetric_of_adjacent_swap_invariant
  intro k hk
  -- Need to show: rename (swap k k') (∑_T xPow (cont T)) = ∑_T xPow (cont T)
  simp only [skewSchurPoly]
  rw [map_sum]
  -- Define the BK involution on the subtype of semistandard tableaux
  let BK : {T : Tableau lam mu // IsSemistandard T} → {T : Tableau lam mu // IsSemistandard T} :=
    fun ⟨T, hT⟩ => ⟨benderKnuth k hk T hT, benderKnuth_semistandard hlam hmu k hk T hT⟩
  -- Show BK is an involution
  have hBK_inv : Function.Involutive BK := by
    intro ⟨T, hT⟩
    simp only [BK]
    ext
    obtain ⟨_, hTT⟩ := benderKnuth_involutive_partition hlam hmu k hk T hT
    exact hTT
  -- Use the involution to reindex the sum
  have hbij : Function.Bijective BK := hBK_inv.bijective
  let BK' : {T : Tableau lam mu // IsSemistandard T} ≃ {T : Tableau lam mu // IsSemistandard T} :=
    Equiv.ofBijective BK hbij
  conv_lhs => rw [← Equiv.sum_comp BK']
  -- Use benderKnuth_monomial to relate the terms
  congr 1
  funext ⟨T, hT⟩
  simp only [BK', Equiv.ofBijective_apply, BK]
  -- Goal: rename (swap k k') (xPow (cont (BK_k T))) = xPow (cont T)
  -- Use benderKnuth_monomial: xPow (cont (BK_k T)) = rename (swap k k') (xPow (cont T))
  have h := benderKnuth_monomial (R := R) k hk T hT
  simp only [monomialTableau] at h
  -- h : xPow (cont (BK_k T hT)) = rename (swap k k') (xPow (cont T))
  rw [h]
  -- Goal: rename (swap k k') (rename (swap k k') (xPow (cont T))) = xPow (cont T)
  rw [MvPolynomial.rename_rename]
  -- Goal: rename ((swap k k') ∘ (swap k k')) (xPow (cont T)) = xPow (cont T)
  have swap_comp_self : (Equiv.swap k ⟨k.val + 1, hk⟩) ∘ (Equiv.swap k ⟨k.val + 1, hk⟩) = id := by
    ext x; simp only [Function.comp_apply, Equiv.swap_apply_self, id_eq]
  simp only [swap_comp_self, MvPolynomial.rename_id_apply]

/-- The sum of x^(cont(T) ∘ σ) over semistandard tableaux equals the sum of x^cont(T).
    This follows from the symmetry of skewSchurPoly. -/
private lemma sum_xPow_content_comp {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu) (σ : Equiv.Perm (Fin N)) :
    ∑ T : {T : Tableau lam mu // IsSemistandard T},
      (xPow (contentTableau T.val ∘ σ) : MvPolynomial (Fin N) R) =
    ∑ T : {T : Tableau lam mu // IsSemistandard T}, xPow (contentTableau T.val) := by
  have h := skewSchurPoly_isSymmetric (R := R) lam mu hlam hmu σ.symm
  simp only [skewSchurPoly] at h
  rw [map_sum] at h
  simp only [rename_xPow] at h
  simp only [Equiv.symm_symm] at h
  exact h

/-- The key expansion identity: alternant α * skewSchurPoly = ∑_T alternant (α + cont(T)).

    This identity is the core of Stembridge's proof. It follows from:
    1. The symmetry of skewSchurPoly (invariant under variable permutations)
    2. The fact that alternant α = ∑_σ sign(σ) · x^(α ∘ σ)
    3. For symmetric p: alternant α * p = ∑_σ sign(σ) · rename σ⁻¹ (x^α * p)

    The proof uses Bender-Knuth involutions to establish the symmetry of skewSchurPoly. -/
lemma alternant_mul_skewSchurPoly_eq_sum {lam mu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu) (α : Fin N → ℕ) :
    (alternant α : MvPolynomial (Fin N) R) * skewSchurPoly lam mu =
    ∑ T : {T : Tableau lam mu // IsSemistandard T},
      (alternant (α + contentTableau T.val) : MvPolynomial (Fin N) R) := by
  -- Expand alternant and skewSchurPoly definitions
  simp only [alternant, skewSchurPoly]
  -- LHS = (∑_σ sign(σ) • x^(α∘σ)) * (∑_T x^cont(T))
  --     = ∑_σ sign(σ) • (x^(α∘σ) * ∑_T x^cont(T))
  rw [Finset.sum_mul]
  simp only [smul_mul_assoc]
  -- RHS = ∑_T ∑_σ sign(σ) • x^((α + cont(T))∘σ)
  --     = ∑_σ ∑_T sign(σ) • x^((α + cont(T))∘σ)
  conv_rhs => rw [Finset.sum_comm]
  -- Use (α + β) ∘ σ = α ∘ σ + β ∘ σ
  simp only [comp_add_tuple]
  -- Now both sides have outer sum over σ
  congr 1
  ext σ
  -- LHS: sign(σ) • (x^(α∘σ) * ∑_T x^cont(T))
  -- RHS: ∑_T sign(σ) • x^(α∘σ + cont(T)∘σ)
  rw [Finset.mul_sum, Finset.smul_sum]
  -- Use x^α * x^β = x^(α+β)
  simp only [xPow_mul]
  -- Factor out the smul
  rw [← Finset.smul_sum, ← Finset.smul_sum]
  congr 1
  -- Need: ∑_T x^(α∘σ + cont(T)) = ∑_T x^(α∘σ + cont(T)∘σ)
  -- Factor out x^(α∘σ)
  simp only [← xPow_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- Need: ∑_T x^cont(T) = ∑_T x^(cont(T)∘σ)
  -- This follows from symmetry of skewSchurPoly
  have h := sum_xPow_content_comp (R := R) hlam hmu σ (lam := lam) (mu := mu)
  rw [h]

/-- The alternant sum over all semistandard tableaux equals the sum over Yamanouchi tableaux
    plus the sum over non-Yamanouchi tableaux. -/
lemma alternant_sum_split {lam mu nu : Fin N → ℕ} :
    ∑ T : {T : Tableau lam mu // IsSemistandard T},
      (alternant (nu + contentTableau T.val + rho N) : MvPolynomial (Fin N) R) =
    ∑ T : {T : Tableau lam mu // IsYamanouchi nu T},
      (alternant (nu + contentTableau T.val + rho N) : MvPolynomial (Fin N) R) +
    ∑ T : {T : Tableau lam mu // IsSemistandard T ∧ ¬IsYamanouchi nu T},
      (alternant (nu + contentTableau T.val + rho N) : MvPolynomial (Fin N) R) := by
  -- This follows from partitioning the semistandard tableaux into Yamanouchi and non-Yamanouchi
  -- Every Yamanouchi tableau is semistandard (by definition)
  -- The semistandard tableaux = Yamanouchi ∪ (semistandard ∧ ¬Yamanouchi)
  classical
  let yamSet : Finset {T : Tableau lam mu // IsSemistandard T} :=
    Finset.univ.filter (fun T => IsYamanouchi nu T.val)
  let nonYamSet : Finset {T : Tableau lam mu // IsSemistandard T} :=
    Finset.univ.filter (fun T => ¬IsYamanouchi nu T.val)

  have hUnion : yamSet ∪ nonYamSet = Finset.univ := by
    ext T
    constructor
    · intro _; exact Finset.mem_univ T
    · intro _
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, yamSet, nonYamSet]
      exact em (IsYamanouchi nu T.val)

  have hDisjoint : Disjoint yamSet nonYamSet := by
    rw [Finset.disjoint_filter]
    intro T _ hYam hnotYam
    exact hnotYam hYam

  conv_lhs => rw [← hUnion, Finset.sum_union hDisjoint]

  congr 1
  · symm
    refine Finset.sum_bij'
      (fun (T : {T : Tableau lam mu // IsYamanouchi nu T}) _ => (⟨T.val, T.prop.1⟩ : {T : Tableau lam mu // IsSemistandard T}))
      (fun (T : {T : Tableau lam mu // IsSemistandard T}) (hT : T ∈ yamSet) =>
        (⟨T.val, Finset.mem_filter.mp hT |>.2⟩ : {T : Tableau lam mu // IsYamanouchi nu T}))
      ?_ ?_ ?_ ?_ ?_
    · intro T _; simp only [yamSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact T.prop
    · intro T hT; simp only [Finset.mem_univ]
    · intro T _; rfl
    · intro T hT; rfl
    · intro T _; rfl
  · symm
    refine Finset.sum_bij'
      (fun (T : {T : Tableau lam mu // IsSemistandard T ∧ ¬IsYamanouchi nu T}) _ =>
        (⟨T.val, T.prop.1⟩ : {T : Tableau lam mu // IsSemistandard T}))
      (fun (T : {T : Tableau lam mu // IsSemistandard T}) (hT : T ∈ nonYamSet) =>
        (⟨T.val, T.prop, Finset.mem_filter.mp hT |>.2⟩ : {T : Tableau lam mu // IsSemistandard T ∧ ¬IsYamanouchi nu T}))
      ?_ ?_ ?_ ?_ ?_
    · intro T _; simp only [nonYamSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact T.prop.2
    · intro T hT; simp only [Finset.mem_univ]
    · intro T _; rfl
    · intro T hT; rfl
    · intro T _; rfl

/-- The sum over non-Yamanouchi tableaux is zero (they cancel in pairs via the involution). -/
lemma alternant_sum_non_yamanouchi_eq_zero {lam mu nu : Fin N → ℕ}
    (hlam : IsNPartition lam) (hmu : IsNPartition mu)
    (hnu : IsNPartition nu) :
    ∑ T : {T : Tableau lam mu // IsSemistandard T ∧ ¬IsYamanouchi nu T},
      (alternant (nu + contentTableau T.val + rho N) : MvPolynomial (Fin N) R) = 0 := by
  -- This follows from the sign-reversing involution:
  -- stembridgeInvolution pairs non-Yamanouchi tableaux T with T' such that
  -- alternant(ν + cont(T') + ρ) = -alternant(ν + cont(T) + ρ)
  -- The involution is fixed-point free, so the sum is zero.
  -- Define the involution on the subtype
  let g : {T : Tableau lam mu // IsSemistandard T ∧ ¬IsYamanouchi nu T} →
          {T : Tableau lam mu // IsSemistandard T ∧ ¬IsYamanouchi nu T} :=
    fun ⟨T, hT, hnotYam⟩ =>
      let T' := stembridgeInvolution nu T hT hnotYam
      let invol := stembridgeInvolution_involutive hlam hmu nu hnu T hT hnotYam
      ⟨T', invol.choose, invol.choose_spec.choose⟩
  -- Use sum_involution
  apply Finset.sum_involution (fun a _ => g a)
  · -- Sign-reversing: f(a) + f(g(a)) = 0
    intro ⟨T, hT, hnotYam⟩ _
    simp only [g]
    rw [stembridgeInvolution_sign_reversing nu hnu T hT hnotYam]
    ring
  · -- Non-zero implies not fixed: f(a) ≠ 0 → g(a) ≠ a
    intro ⟨T, hT, hnotYam⟩ _ hne
    simp only [g, ne_eq]
    intro heq
    -- Extract T' = T from the subtype equality
    have hT'_eq_T : stembridgeInvolution nu T hT hnotYam = T := by
      have h := congrArg Subtype.val heq
      simp only at h
      exact h
    -- Use the new lemma: if T' = T, then the alternant is zero
    have hzero := stembridgeInvolution_fixed_point_implies_alternant_zero (R := R) nu hnu T hT hnotYam hT'_eq_T
    exact hne hzero
  · -- g(a) ∈ s
    intro a _
    exact Finset.mem_univ (g a)
  · -- Involution: g(g(a)) = a
    intro ⟨T, hT, hnotYam⟩ _
    simp only [g]
    apply Subtype.ext
    simp only
    have invol := stembridgeInvolution_involutive hlam hmu nu hnu T hT hnotYam
    exact invol.choose_spec.choose_spec

/-! ## Main theorems -/

/-- **Stembridge's Lemma (lem.sf.stemb-lem)**: The key technical lemma for
    proving the Littlewood-Richardson rule.

    For N-partitions lam, mu, nu:
    a_{nu+ρ} · s_{lam/mu} = ∑_{T nu-Yamanouchi of shape lam/mu} a_{nu + cont(T) + ρ}

    The sum on the RHS is over all nu-Yamanouchi semistandard tableaux T of shape lam/mu.
    Note: The sum is finite since there are finitely many semistandard tableaux of any shape.

    ## Proof Strategy (from Stembridge 1997)

    The proof uses a sign-reversing involution on non-Yamanouchi tableaux:

    **Step 1**: Express the LHS using the alternant definition and symmetry of `skewSchurPoly`:
    ```
    a_{ν+ρ} · s_{λ/μ} = ∑_{σ ∈ S_N} (-1)^σ · σ(x^{ν+ρ}) · s_{λ/μ}
                      = ∑_{σ ∈ S_N} (-1)^σ · σ(x^{ν+ρ} · s_{λ/μ})  (since s_{λ/μ} is symmetric)
    ```

    **Step 2**: Expand `s_{λ/μ}` as a sum over semistandard tableaux:
    ```
    = ∑_{T ∈ SSYT(λ/μ)} ∑_{σ ∈ S_N} (-1)^σ · x^{σ(ν+cont(T)+ρ)}
    = ∑_{T ∈ SSYT(λ/μ)} a_{ν+cont(T)+ρ}
    ```

    **Step 3**: Define a sign-reversing involution on non-Yamanouchi tableaux:
    For T not ν-Yamanouchi:
    - Let j be the largest "violator" column (where ν + cont(col≥j T) fails to be a partition)
    - Let k be the smallest "misstep" index (where the partition condition fails)
    - Apply the Bender-Knuth involution β_k to columns 1, ..., j-1 of T
    - This gives T* with cont(T*) obtained from cont(T) by swapping entries k and k+1

    **Step 4**: Show the involution is sign-reversing:
    Since cont(T*) differs from cont(T) by swapping entries k and k+1:
    ```
    a_{ν+cont(T*)+ρ} = -a_{ν+cont(T)+ρ}  (by alternant_swap)
    ```

    **Step 5**: Conclude that non-Yamanouchi tableaux cancel in pairs.

    ## Dependencies

    This proof requires:
    1. `skewSchurPoly` to be properly defined as ∑_{T ∈ SSYT} x^{cont(T)}
    2. `alternant_swap`: swapping two entries negates the alternant
    3. `alternant_eq_zero_of_repeated`: equal entries give zero alternant
    4. Bender-Knuth involutions β_k on tableaux
    5. Properties of the involution (sign-reversing, fixed-point free on non-Yamanouchi)

    Reference: [Stembridge, *A concise proof of the Littlewood-Richardson rule*, 2002] -/
theorem stembridgeLemma (lam mu nu : Fin N → ℕ)
    (hlam : IsNPartition lam) (hmu : IsNPartition mu) (hnu : IsNPartition nu) :
    (alternant (nu + rho N) : MvPolynomial (Fin N) R) * skewSchurPoly lam mu =
    -- Sum over all nu-Yamanouchi semistandard tableaux T of shape lam/mu
    -- of a_{nu + cont(T) + rho}
    -- This requires a finiteness argument and enumeration of Yamanouchi tableaux
    ∑ T : {T : Tableau lam mu // IsYamanouchi nu T},
      (alternant (nu + contentTableau T.val + rho N) : MvPolynomial (Fin N) R) := by
  -- Step 1: Expand the LHS using alternant_mul_skewSchurPoly_eq_sum
  rw [alternant_mul_skewSchurPoly_eq_sum hlam hmu]
  -- Now LHS = ∑_T alternant ((nu + rho N) + cont(T))
  -- We need to show (nu + rho N) + cont(T) = nu + cont(T) + rho N
  have h_add : ∀ T : {T : Tableau lam mu // IsSemistandard T},
      (nu + rho N) + contentTableau T.val = nu + contentTableau T.val + rho N := by
    intro T
    ext i
    simp only [Pi.add_apply]
    ring
  simp_rw [h_add]
  -- Now LHS = ∑_T alternant (nu + cont(T) + rho N) over semistandard T
  -- Step 2: Split into Yamanouchi and non-Yamanouchi
  rw [alternant_sum_split]
  -- Step 3: The non-Yamanouchi sum is zero
  rw [alternant_sum_non_yamanouchi_eq_zero hlam hmu hnu]
  ring

/-- **Lemma (lem.sf.tab-greater-i)**: In a semistandard tableau of shape lam,
    the entry at position (i,j) is at least i.

    This follows from the strict increase down columns: for any cell (i, j) in the
    diagram, all cells (0, j), (1, j), ..., (i-1, j) are also in the diagram
    (since lam is weakly decreasing), and the entries strictly increase down
    the column, giving T(i, j) ≥ i. -/
theorem tableau_entry_ge_row {lam : Fin N → ℕ} (hlam : IsNPartition lam)
    (T : Tableau lam zeroTuple) (hT : IsSemistandard T)
    (c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam zeroTuple}) :
    c.val.1 ≤ T c := by
  -- Use strong induction on the row index
  have hcol := hT.2
  obtain ⟨⟨i, j⟩, hc⟩ := c
  -- Prove by strong induction: ∀ k ≤ i.val, for any cell (⟨k, _⟩, j) in diagram, ⟨k, _⟩ ≤ T(cell)
  suffices h : ∀ k : ℕ, k ≤ i.val → ∀ hk : k < N,
      ∀ hcell : (⟨k, hk⟩, j) ∈ skewYoungDiagram lam zeroTuple,
      (⟨k, hk⟩ : Fin N) ≤ T ⟨(⟨k, hk⟩, j), hcell⟩ by
    exact h i.val (le_refl _) i.isLt hc
  intro k hk_le_i hk hcell
  induction k with
  | zero =>
    -- Base case: k = 0
    -- Need: ⟨0, hk⟩ ≤ T ⟨(⟨0, hk⟩, j), hcell⟩
    -- i.e., 0 ≤ (T _).val, which is always true
    simp only [Fin.le_def]
    exact Nat.zero_le _
  | succ n ih =>
    -- Inductive case: k = n + 1
    have hn_le_i : n ≤ i.val := by omega
    have hn_lt_N : n < N := by omega
    -- The cell (n, j) is in the diagram since lam is weakly decreasing
    have hcell_n : (⟨n, hn_lt_N⟩, j) ∈ skewYoungDiagram lam zeroTuple := by
      simp only [skewYoungDiagram, Set.mem_ofPred_eq, zeroTuple, Pi.zero_apply]
      constructor
      · exact hcell.1  -- 0 < j
      · -- j ≤ lam ⟨n, _⟩ because lam is weakly decreasing
        have h1 : (⟨n, hn_lt_N⟩ : Fin N) ≤ ⟨n + 1, hk⟩ := by simp only [Fin.le_def]; omega
        have h2 : lam ⟨n + 1, hk⟩ ≤ lam ⟨n, hn_lt_N⟩ := hlam ⟨n, hn_lt_N⟩ ⟨n + 1, hk⟩ h1
        exact le_trans hcell.2 h2
    -- By IH: n ≤ T(n, j)
    have ih_applied : (⟨n, hn_lt_N⟩ : Fin N) ≤ T ⟨(⟨n, hn_lt_N⟩, j), hcell_n⟩ :=
      ih hn_le_i hn_lt_N hcell_n
    -- By strict column increase: T(n, j) < T(n+1, j)
    have hcol_applied : T ⟨(⟨n, hn_lt_N⟩, j), hcell_n⟩ < T ⟨(⟨n + 1, hk⟩, j), hcell⟩ := by
      apply hcol
      · rfl  -- same column
      · simp only [Fin.lt_def]; omega  -- n < n + 1
    -- Combine: n ≤ T(n,j).val and T(n,j).val < T(n+1,j).val implies n + 1 ≤ T(n+1, j).val
    simp only [Fin.le_def] at ih_applied ⊢
    simp only [Fin.lt_def] at hcol_applied
    omega

/-- The minimalistic tableau T₀ of shape lam has entry i in row i.
    (Defined in the proof of thm.sf.schur-symm (b)) -/
def minimalisticTableau (lam : Fin N → ℕ) : Tableau lam zeroTuple :=
  fun c => c.val.1

/-- The minimalistic tableau is semistandard. -/
theorem minimalisticTableau_semistandard (lam : Fin N → ℕ) :
    IsSemistandard (minimalisticTableau lam) := by
  constructor
  · -- Weakly increasing along rows (all entries in row i are i)
    intro c₁ c₂ hrow _
    simp only [minimalisticTableau]
    rw [hrow]
  · -- Strictly increasing down columns
    intro c₁ c₂ _ hcol
    simp only [minimalisticTableau]
    exact hcol

/-- The set of column indices in row i with column ≥ j in the diagram lam/0.
    Used to compute contentColGeq for the minimalistic tableau. -/
private def restrictedCellsRow (lam : Fin N → ℕ) (i : Fin N) (j : ℕ) : Set ℕ :=
  {k | j ≤ k ∧ 0 < k ∧ k ≤ lam i}

/-- The restricted cells in row i form an interval Ioc. -/
private lemma restrictedCellsRow_eq_Ioc (lam : Fin N → ℕ) (i : Fin N) (j : ℕ) (hj : j > 0) :
    restrictedCellsRow lam i j = Set.Ioc (j - 1) (lam i) := by
  ext k
  simp only [restrictedCellsRow, Set.mem_ofPred_eq, Set.mem_Ioc]
  constructor
  · intro ⟨hjk, _, hkl⟩
    exact ⟨by omega, hkl⟩
  · intro ⟨hjk, hkl⟩
    exact ⟨by omega, by omega, hkl⟩

/-- The cardinality of the restricted cells in row i. -/
private lemma card_restrictedCellsRow (lam : Fin N → ℕ) (i : Fin N) (j : ℕ) (hj : j > 0) :
    Nat.card (restrictedCellsRow lam i j) = lam i + 1 - j := by
  rw [restrictedCellsRow_eq_Ioc lam i j hj]
  have h : (Set.Ioc (j - 1) (lam i)).ncard = lam i - (j - 1) := Set.ncard_Ioc_nat (j - 1) (lam i)
  rw [Nat.card_coe_set_eq, h]
  omega

/-- The type of cells in column ≥ j with row index i. -/
private def contentColGeqType (lam : Fin N → ℕ) (j : ℕ) (i : Fin N) :=
  {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam zeroTuple ∧ c.2 ≥ j} //
   (⟨c.val, c.prop.1⟩ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam zeroTuple}).val.1 = i}

/-- Equivalence between the content type and restricted cells. -/
private def contentColGeqEquiv (lam : Fin N → ℕ) (j : ℕ) (_hj : j > 0) (i : Fin N) :
    contentColGeqType lam j i ≃ restrictedCellsRow lam i j where
  toFun := fun ⟨⟨⟨row, col⟩, hmem⟩, heq⟩ =>
    ⟨col, by
      simp only [restrictedCellsRow, Set.mem_ofPred_eq]
      simp only [skewYoungDiagram, zeroTuple, Pi.zero_apply, Set.mem_ofPred_eq] at hmem
      simp only at heq
      refine ⟨hmem.2, hmem.1.1, ?_⟩
      rw [← heq]
      exact hmem.1.2⟩
  invFun := fun ⟨k, hk⟩ =>
    ⟨⟨⟨i, k⟩, by
      simp only [skewYoungDiagram, zeroTuple, Pi.zero_apply, Set.mem_ofPred_eq]
      simp only [restrictedCellsRow, Set.mem_ofPred_eq] at hk
      exact ⟨⟨hk.2.1, hk.2.2⟩, hk.1⟩⟩, rfl⟩
  left_inv := by
    intro ⟨⟨⟨row, col⟩, hmem⟩, heq⟩
    simp only [contentColGeqType] at *
    simp only at heq
    simp only [Subtype.mk.injEq]
    ext <;> simp only [heq]
  right_inv := by
    intro ⟨k, hk⟩
    rfl

/-- For the minimalistic tableau, contentColGeq at row i equals lam i + 1 - j. -/
private lemma contentColGeq_minimalisticTableau (lam : Fin N → ℕ) (j : ℕ) (hj : j > 0) (i : Fin N) :
    contentColGeq (minimalisticTableau lam) j i = lam i + 1 - j := by
  unfold contentColGeq minimalisticTableau
  have h : Nat.card {c : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam zeroTuple ∧ c.2 ≥ j} //
                      (⟨c.val, c.prop.1⟩ : {c : Fin N × ℕ // c ∈ skewYoungDiagram lam zeroTuple}).val.1 = i} =
           Nat.card (restrictedCellsRow lam i j) := by
    exact Nat.card_congr (contentColGeqEquiv lam j hj i)
  rw [h, card_restrictedCellsRow lam i j hj]

/-- The minimalistic tableau is 0-Yamanouchi. (Observation 1 in proof)

    The key insight is that for the minimalistic tableau, contentColGeq T j at row i
    counts cells (i, k) where j ≤ k ≤ lam i. This count equals lam i + 1 - j.
    Since lam is weakly decreasing (an N-partition), so is this count, hence
    0 + contentColGeq T j is also weakly decreasing, i.e., an N-partition. -/
theorem minimalisticTableau_yamanouchi (lam : Fin N → ℕ) (hlam : IsNPartition lam) :
    IsYamanouchi zeroTuple (minimalisticTableau lam) := by
  constructor
  · exact minimalisticTableau_semistandard lam
  · intro j hj i₁ i₂ hi
    simp only [Pi.add_apply, Pi.zero_apply, zero_add]
    rw [contentColGeq_minimalisticTableau lam j hj i₁, contentColGeq_minimalisticTableau lam j hj i₂]
    -- Need: lam i₂ + 1 - j ≤ lam i₁ + 1 - j
    -- Since hlam : lam i₂ ≤ lam i₁
    have h := hlam i₁ i₂ hi
    omega

/-- The content of the minimalistic tableau equals lam.
    This follows from contentColGeq_one_eq_contentTableau and contentColGeq_minimalisticTableau:
    contentTableau T₀ = contentColGeq T₀ 1, and contentColGeq T₀ 1 i = lam i + 1 - 1 = lam i. -/
theorem contentTableau_minimalisticTableau (lam : Fin N → ℕ) :
    contentTableau (minimalisticTableau lam) = lam := by
  rw [← contentColGeq_one_eq_contentTableau]
  ext i
  rw [contentColGeq_minimalisticTableau lam 1 Nat.one_pos i]
  omega

/-- Helper: for 0-Yamanouchi T of shape lam/0, the entry at the rightmost cell
    of row i equals i. This is the key to proving uniqueness. -/
lemma yamanouchi_rightmost_entry {lam : Fin N → ℕ} (hlam : IsNPartition lam)
    (T : Tableau lam zeroTuple) (hT : IsYamanouchi zeroTuple T)
    (i : Fin N) (hi : lam i > 0) :
    let hright_mem : (i, lam i) ∈ skewYoungDiagram lam zeroTuple := by
      simp only [skewYoungDiagram, zeroTuple, Pi.zero_apply, Set.mem_ofPred_eq]
      exact ⟨hi, le_refl _⟩
    T ⟨(i, lam i), hright_mem⟩ = i := by
  intro hright_mem
  -- Strong induction on i.val
  induction' hn : i.val using Nat.strong_induction_on with n ih generalizing i
  by_contra hne
  -- T(i, lam i) ≥ i by tableau_entry_ge_row
  have hge : i ≤ T ⟨(i, lam i), hright_mem⟩ :=
    tableau_entry_ge_row hlam T hT.1 ⟨(i, lam i), hright_mem⟩
  have hgt : i < T ⟨(i, lam i), hright_mem⟩ :=
    lt_of_le_of_ne hge (fun heq => hne heq.symm)
  set m := T ⟨(i, lam i), hright_mem⟩
  -- From 0-Yamanouchi: contentColGeq T (lam i) is an N-partition
  have hyam := hT.2 (lam i) hi
  simp only [zeroTuple, zero_add] at hyam
  -- Since i < m, we have contentColGeq T (lam i) m ≤ contentColGeq T (lam i) i
  have hdecr : contentColGeq T (lam i) m ≤ contentColGeq T (lam i) i :=
    hyam i m (le_of_lt hgt)
  -- Finite instance for the content type
  have hfin_base : Set.Finite {c : Fin N × ℕ | c ∈ skewYoungDiagram lam zeroTuple ∧ c.2 ≥ lam i} := by
    apply Set.Finite.subset (skewYoungDiagram_finite lam zeroTuple)
    intro c ⟨hc, _⟩
    exact hc
  haveI : Fintype {c : Fin N × ℕ // c ∈ skewYoungDiagram lam zeroTuple ∧ c.2 ≥ lam i} :=
    Set.Finite.fintype hfin_base
  -- The cell (i, lam i) contributes to contentColGeq T (lam i) m
  have hm_pos : contentColGeq T (lam i) m ≥ 1 := by
    unfold contentColGeq
    have hne' : Nonempty {c' : {c' : Fin N × ℕ // c' ∈ skewYoungDiagram lam zeroTuple ∧ c'.2 ≥ lam i} //
                     T ⟨c'.val, c'.prop.1⟩ = m} :=
      ⟨⟨⟨(i, lam i), hright_mem, le_refl _⟩, rfl⟩⟩
    rw [ge_iff_le, Nat.one_le_iff_ne_zero, Nat.card_ne_zero]
    exact ⟨hne', Finite.of_fintype _⟩
  -- No cell in col ≥ lam i has entry i
  have hi_zero : contentColGeq T (lam i) i = 0 := by
    unfold contentColGeq
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    constructor
    intro ⟨⟨c', hc'_mem, hc'_col⟩, hc'_entry⟩
    simp only at hc'_entry
    -- Show c'.1 ≤ i
    have hc'_row_le : c'.1 ≤ i := by
      by_contra hc'_row_gt
      push Not at hc'_row_gt
      have hlam_ineq := hlam i c'.1 (le_of_lt hc'_row_gt)
      have hc'_col_eq : c'.2 = lam i := by
        have h1 : c'.2 ≤ lam c'.1 := hc'_mem.2
        omega
      have hcol_incr := hT.1.2 ⟨(i, lam i), hright_mem⟩ ⟨c', hc'_mem⟩
        (by simp [hc'_col_eq]) hc'_row_gt
      simp only [hc'_entry] at hcol_incr
      have h1 : (m : ℕ) < (i : ℕ) := Fin.lt_def.mp hcol_incr
      have h2 : (i : ℕ) < (m : ℕ) := Fin.lt_def.mp hgt
      omega
    -- Case analysis on c'.1
    by_cases hc'_row_eq : c'.1 = i
    · -- c'.1 = i: then c' = (i, lam i) and T c' = m ≠ i
      have hc'_col_eq : c'.2 = lam i := by
        have h1 : c'.2 ≤ lam c'.1 := hc'_mem.2
        rw [hc'_row_eq] at h1
        omega
      have hc'_eq : c' = (i, lam i) := Prod.ext hc'_row_eq hc'_col_eq
      have hT_eq : T ⟨c', hc'_mem⟩ = T ⟨(i, lam i), hright_mem⟩ := by
        congr 1; exact Subtype.ext hc'_eq
      rw [hT_eq] at hc'_entry
      have h1 : (m : ℕ) = (i : ℕ) := Fin.ext_iff.mp hc'_entry
      have h2 : (i : ℕ) < (m : ℕ) := Fin.lt_def.mp hgt
      omega
    · -- c'.1 < i: by IH, T(c'.1, lam c'.1) = c'.1, so T c' ≤ c'.1 < i
      have hc'_row_lt : c'.1 < i := lt_of_le_of_ne hc'_row_le hc'_row_eq
      have hc'_lam_pos : lam c'.1 > 0 := by
        have h1 : c'.2 ≤ lam c'.1 := hc'_mem.2
        omega
      have hc'_row_lt_n : (c'.1 : ℕ) < n := by
        rw [← hn]
        exact Fin.lt_def.mp hc'_row_lt
      have hih := ih c'.1.val hc'_row_lt_n c'.1 hc'_lam_pos rfl
      have hc'_right_mem : (c'.1, lam c'.1) ∈ skewYoungDiagram lam zeroTuple := by
        simp only [skewYoungDiagram, zeroTuple, Pi.zero_apply, Set.mem_ofPred_eq]
        exact ⟨hc'_lam_pos, le_refl _⟩
      have hrow_incr : T ⟨c', hc'_mem⟩ ≤ T ⟨(c'.1, lam c'.1), hc'_right_mem⟩ := by
        by_cases hcol_lt : c'.2 < lam c'.1
        · exact hT.1.1 ⟨c', hc'_mem⟩ ⟨(c'.1, lam c'.1), hc'_right_mem⟩ rfl hcol_lt
        · have hcol_eq : c'.2 = lam c'.1 := le_antisymm hc'_mem.2 (not_lt.mp hcol_lt)
          have hc'_eq : c' = (c'.1, lam c'.1) := Prod.ext rfl hcol_eq
          have hT_eq : T ⟨c', hc'_mem⟩ = T ⟨(c'.1, lam c'.1), hc'_right_mem⟩ := by
            congr 1; exact Subtype.ext hc'_eq
          rw [hT_eq]
      rw [hih] at hrow_incr
      rw [hc'_entry] at hrow_incr
      have h1 : (i : ℕ) ≤ (c'.1 : ℕ) := Fin.le_def.mp hrow_incr
      have h2 : (c'.1 : ℕ) < (i : ℕ) := Fin.lt_def.mp hc'_row_lt
      omega
  omega

/-- The minimalistic tableau is the unique 0-Yamanouchi semistandard tableau
    of shape lam/0. (Observation 2 in proof) -/
theorem minimalisticTableau_unique (lam : Fin N → ℕ) (hlam : IsNPartition lam)
    (T : Tableau lam zeroTuple) (hT : IsYamanouchi zeroTuple T) :
    T = minimalisticTableau lam := by
  -- We prove T c = c.val.1 for all cells c by showing:
  -- 1. T c ≥ c.val.1 (from tableau_entry_ge_row / semistandard)
  -- 2. T c ≤ c.val.1 (from Yamanouchi condition forcing T(i, lam i) = i)
  funext c
  obtain ⟨⟨i, j⟩, hc⟩ := c
  simp only [minimalisticTableau]
  -- From diagram membership: 0 < j ≤ lam i
  have hj_pos : j > 0 := by simp [skewYoungDiagram, zeroTuple] at hc; omega
  have hj_le : j ≤ lam i := hc.2
  have hlam_pos : lam i > 0 := by omega
  -- The rightmost cell (i, lam i) is in the diagram
  have hright_mem : (i, lam i) ∈ skewYoungDiagram lam zeroTuple := by
    simp only [skewYoungDiagram, zeroTuple, Pi.zero_apply, Set.mem_ofPred_eq]
    exact ⟨hlam_pos, le_refl _⟩
  -- Key: T(i, lam i) = i
  have hright := yamanouchi_rightmost_entry hlam T hT i hlam_pos
  -- By row weak increase: T(i, j) ≤ T(i, lam i) = i
  have hrow_incr : T ⟨(i, j), hc⟩ ≤ T ⟨(i, lam i), hright_mem⟩ := by
    by_cases hjlam : j < lam i
    · exact hT.1.1 ⟨(i, j), hc⟩ ⟨(i, lam i), hright_mem⟩ rfl hjlam
    · have hjeq : j = lam i := le_antisymm hj_le (not_lt.mp hjlam)
      have hc_eq : (i, j) = (i, lam i) := Prod.ext rfl hjeq
      have hT_eq : T ⟨(i, j), hc⟩ = T ⟨(i, lam i), hright_mem⟩ := by
        congr 1; exact Subtype.ext hc_eq
      rw [hT_eq]
  rw [hright] at hrow_incr
  -- Also T(i, j) ≥ i from semistandard
  have hge : i ≤ T ⟨(i, j), hc⟩ := tableau_entry_ge_row hlam T hT.1 ⟨(i, j), hc⟩
  -- Combine: i ≤ T(i, j) ≤ i
  exact le_antisymm hrow_incr hge

/-- **Theorem (thm.sf.schur-symm (b))**: The fundamental relation between
    Schur polynomials and alternants: a_{lam+ρ} = a_ρ · s_lam.

    ## Proof Strategy

    The proof derives this from Stembridge's Lemma by setting μ = 0 and ν = 0:

    1. By Stembridge's Lemma: a_{0+ρ} · s_{λ/0} = ∑_{T 0-Yamanouchi} a_{0+cont(T)+ρ}
    2. The only 0-Yamanouchi semistandard tableau of shape λ/0 is the minimalistic
       tableau T₀ (where each row i contains only i's).
    3. The content of T₀ equals λ.
    4. Therefore: a_ρ · s_λ = a_{λ+ρ}

    This is equivalent to: a_{λ+ρ} = a_ρ · s_λ. -/
theorem schurPoly_eq_alternant_div (lam : Fin N → ℕ) (hlam : IsNPartition lam) :
    (alternant (lam + rho N) : MvPolynomial (Fin N) R) =
    alternant (rho N) * schurPoly lam := by
  -- Apply Stembridge's Lemma with μ = 0 and ν = 0
  have h_stemb := stembridgeLemma (R := R) lam zeroTuple zeroTuple hlam isNPartition_zero isNPartition_zero
  -- h_stemb: a_{0+ρ} · s_{λ/0} = ∑_{T 0-Yamanouchi} a_{0 + cont(T) + ρ}
  -- First, establish that there's exactly one 0-Yamanouchi tableau
  have h_unique : ∀ T : {T : Tableau lam zeroTuple // IsYamanouchi zeroTuple T},
      T.val = minimalisticTableau lam := by
    intro T
    exact minimalisticTableau_unique lam hlam T.val T.prop
  -- The minimalistic tableau is 0-Yamanouchi
  have h_min_yam := minimalisticTableau_yamanouchi lam hlam
  -- The content of each (unique) 0-Yamanouchi tableau is lam
  have h_singleton : ∀ T : {T : Tableau lam zeroTuple // IsYamanouchi zeroTuple T},
      contentTableau T.val = lam := by
    intro T
    rw [h_unique T, contentTableau_minimalisticTableau]
  -- The type has exactly one element
  have h_subsingleton : Subsingleton {T : Tableau lam zeroTuple // IsYamanouchi zeroTuple T} := by
    constructor
    intro T₁ T₂
    ext
    rw [h_unique T₁, h_unique T₂]
  haveI : Unique {T : Tableau lam zeroTuple // IsYamanouchi zeroTuple T} :=
    uniqueOfSubsingleton ⟨minimalisticTableau lam, h_min_yam⟩
  -- Sum over a unique type is just the single element
  rw [Fintype.sum_unique] at h_stemb
  -- h_stemb: a_{0+ρ} * s_{λ/0} = a_{0 + cont(T₀) + ρ} where T₀ is the unique element
  -- Since cont(T₀) = lam, we have a_{0+ρ} * s_{λ/0} = a_{0 + lam + ρ}
  have h_content := h_singleton default
  simp only [h_content] at h_stemb
  -- Now simplify: zeroTuple = 0, so 0 + ρ = ρ, s_{λ/0} = s_λ, 0 + lam + ρ = lam + ρ
  simp only [zeroTuple, zero_add] at h_stemb
  -- h_stemb: a_ρ * s_λ = a_{lam + ρ}
  exact h_stemb.symm

/-- **Zelevinsky's generalized Littlewood-Richardson rule (thm.sf.lr-zy)**:

    For N-partitions lam, mu, nu:
    s_nu · s_{lam/mu} = ∑_{T nu-Yamanouchi of shape lam/mu} s_{nu + cont(T)}

    This expresses the product of a Schur polynomial with a skew Schur polynomial
    as a sum of Schur polynomials. Setting mu = 0 gives the classical
    Littlewood-Richardson rule for products of two Schur polynomials.

    Note: For each nu-Yamanouchi tableau T, the tuple nu + cont(T) is automatically
    an N-partition (this follows from the definition of Yamanouchi with j=1).

    ## Proof Strategy (from the textbook)

    The proof derives thm.sf.lr-zy from Stembridge's Lemma (lem.sf.stemb-lem):

    **Step 1**: By Theorem thm.sf.schur-symm (b) applied to ν instead of λ:
      a_{ν+ρ} = a_ρ · s_ν

    **Step 2**: By Stembridge's Lemma (lem.sf.stemb-lem):
      a_{ν+ρ} · s_{λ/μ} = ∑_{T ν-Yamanouchi} a_{ν+cont(T)+ρ}

    **Step 3**: For each ν-Yamanouchi tableau T, ν+cont(T) is an N-partition
    (by the j=1 case of the Yamanouchi condition), so by thm.sf.schur-symm (b):
      a_{ν+cont(T)+ρ} = a_ρ · s_{ν+cont(T)}

    **Step 4**: Substituting Steps 1 and 3 into Step 2:
      a_ρ · s_ν · s_{λ/μ} = a_ρ · ∑_{T ν-Yamanouchi} s_{ν+cont(T)}

    **Step 5**: Since a_ρ is regular (lem.sf.arho-reg), we can cancel it
    (using lem.cring.reg.cancel) to obtain:
      s_ν · s_{λ/μ} = ∑_{T ν-Yamanouchi} s_{ν+cont(T)}

    This completes the proof. -/
theorem littlewoodRichardson [IsDomain R] (lam mu nu : Fin N → ℕ)
    (hlam : IsNPartition lam) (hmu : IsNPartition mu) (hnu : IsNPartition nu) :
    (schurPoly nu : MvPolynomial (Fin N) R) * skewSchurPoly lam mu =
    -- Sum over all nu-Yamanouchi semistandard tableaux T of shape lam/mu
    -- of s_{nu + cont(T)}
    ∑ T : {T : Tableau lam mu // IsYamanouchi nu T},
      (schurPoly (nu + contentTableau T.val) : MvPolynomial (Fin N) R) := by
  -- Step 1: a_{ν+ρ} = a_ρ · s_ν (by schurPoly_eq_alternant_div)
  have h_nu : (alternant (nu + rho N) : MvPolynomial (Fin N) R) = alternant (rho N) * schurPoly nu :=
    schurPoly_eq_alternant_div nu hnu
  -- Step 2: Apply Stembridge's Lemma
  have h_stemb := stembridgeLemma (R := R) lam mu nu hlam hmu hnu
  -- Step 3: For each ν-Yamanouchi T, ν+cont(T) is an N-partition
  -- and therefore a_{ν+cont(T)+ρ} = a_ρ · s_{ν+cont(T)}
  have h_each : ∀ T : {T : Tableau lam mu // IsYamanouchi nu T},
      (alternant (nu + contentTableau T.val + rho N) : MvPolynomial (Fin N) R) =
      alternant (rho N) * schurPoly (nu + contentTableau T.val) := by
    intro T
    -- T is ν-Yamanouchi, so ν + cont(T) is an N-partition
    have h_part : IsNPartition (nu + contentTableau T.val) :=
      T.prop.isNPartition_add_content
    exact schurPoly_eq_alternant_div (nu + contentTableau T.val) h_part
  -- Rewrite the RHS of Stembridge's Lemma using h_each
  have h_rhs : (∑ T : {T : Tableau lam mu // IsYamanouchi nu T},
        (alternant (nu + contentTableau T.val + rho N) : MvPolynomial (Fin N) R)) =
      alternant (rho N) * ∑ T : {T : Tableau lam mu // IsYamanouchi nu T},
        (schurPoly (nu + contentTableau T.val) : MvPolynomial (Fin N) R) := by
    rw [mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    exact h_each T
  -- Step 4: Combine Steps 1 and 2
  -- From h_stemb: a_{ν+ρ} · s_{λ/μ} = ∑_T a_{ν+cont(T)+ρ}
  -- Using h_nu: (a_ρ · s_ν) · s_{λ/μ} = ∑_T a_{ν+cont(T)+ρ}
  rw [h_nu] at h_stemb
  -- Using h_rhs: a_ρ · s_ν · s_{λ/μ} = a_ρ · ∑_T s_{ν+cont(T)}
  rw [h_rhs] at h_stemb
  -- Now h_stemb says: (a_ρ * s_ν) * s_{λ/μ} = a_ρ * ∑_T s_{ν+cont(T)}
  rw [mul_assoc] at h_stemb
  -- Step 5: Cancel a_ρ (which is regular)
  have h_reg : _root_.IsRegular (alternant (rho N) : MvPolynomial (Fin N) R) :=
    alternant_rho_isRegular
  exact h_reg.left h_stemb

/-! ## Examples -/

/-- Example (exa.sf.lr-zy.1): For N=3, nu=(1,0,0), lam=(2,1,0), mu=(0,0,0):
    s_{(1,0,0)} · s_{(2,1,0)} = s_{(3,1,0)} + s_{(2,2,0)} + s_{(2,1,1)}

    The (1,0,0)-Yamanouchi semistandard tableaux of shape (2,1,0)/0 are:
    - T₁ with entries [[1,1],[2]] and cont(T₁) = (2,1,0), giving s_{(3,1,0)}
    - T₂ with entries [[1,2],[2]] and cont(T₂) = (1,2,0), giving s_{(2,2,0)}
    - T₃ with entries [[1,2],[3]] and cont(T₃) = (1,1,1), giving s_{(2,1,1)}

    Note: s_{(1,0,0)} = x₁ + x₂ + x₃ (the elementary symmetric polynomial e₁). -/
example : True := trivial -- Requires explicit computation with concrete tableaux

/-! ## The Littlewood-Richardson coefficients

The coefficients c(nu, lam, omega) appearing in the expansion
s_nu · s_lam = ∑_omega c(nu, lam, omega) · s_omega
are called the Littlewood-Richardson coefficients. They have deep connections
to representation theory: they are the multiplicities in the tensor product
decomposition V_nu ⊗ V_lam ≅ ⊕_omega V_omega^{c(nu,lam,omega)} of irreducible polynomial
representations of GL_N(ℂ). -/

/-- The Littlewood-Richardson coefficient c(nu, lam, omega) counts the number of
    nu-Yamanouchi semistandard tableaux T of shape lam/0 such that nu + cont(T) = omega.

    This is a finite count since there are finitely many semistandard tableaux of any shape. -/
noncomputable def littlewoodRichardsonCoeff (nu lam omega : Fin N → ℕ) : ℕ :=
  Nat.card {T : Tableau lam 0 // IsYamanouchi nu T ∧ nu + contentTableau T = omega}

/-- The product s_nu · s_lam expands as ∑_omega c(nu, lam, omega) · s_omega.

    This is a corollary of the Littlewood-Richardson rule with mu = 0. -/
theorem schurPoly_mul_expansion [IsDomain R] (nu lam : Fin N → ℕ)
    (hnu : IsNPartition nu) (hlam : IsNPartition lam) :
    (schurPoly nu : MvPolynomial (Fin N) R) * schurPoly lam =
    -- Sum over all nu-Yamanouchi semistandard tableaux T of shape lam/0
    -- of s_{nu + cont(T)}
    ∑ T : {T : Tableau lam 0 // IsYamanouchi nu T},
      (schurPoly (nu + contentTableau T.val) : MvPolynomial (Fin N) R) := by
  -- This follows from littlewoodRichardson with mu = 0
  -- schurPoly lam = skewSchurPoly lam 0 by definition
  have h0 : IsNPartition (0 : Fin N → ℕ) := fun _ _ _ => le_refl 0
  exact littlewoodRichardson lam 0 nu hlam h0 hnu

end AlgebraicCombinatorics
