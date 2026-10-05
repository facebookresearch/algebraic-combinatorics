/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# The Lindström-Gessel-Viennot Lemma: Weighted and Generalized Versions

This file formalizes the weighted version of the LGV lemma and related results,
following Section "The weighted version ... The nonpermutable case" (sec.det.comb.lgv)
of the Algebraic Combinatorics notes.

## Main definitions

* `LGV.SimpleDigraph`: A digraph structure with no self-loops (irreflexive adjacency)
* `LGV.SimpleDigraph.toDigraph`: Conversion to Mathlib's `Digraph` type
* `LGV.ArcWeight`: A weight function on arcs of a digraph
* `LGV.pathWeight`: The weight of a path (product of arc weights)
* `LGV.pathTupleWeight`: The weight of a path tuple (product of path weights)
* `LGV.pathWeightMatrix`: The matrix of sums of path weights between source/target vertices
* `LGV.catalanHankelMatrix`: The Hankel matrix of Catalan numbers

## Main results

* `LGV.lgv_weighted_lattice`: LGV lemma, lattice weight version (Theorem thm.lgv.kpaths.wt)
* `LGV.lgv_weighted_digraph`: LGV lemma, digraph weight version (Theorem thm.lgv.kpaths.wt-dg)
* `LGV.lgv_nonpermutable`: LGV lemma, nonpermutable lattice weight version
    (Corollary cor.lgv.kpaths.wt-np)
* `LGV.binom_det_nonneg`: Determinant of binomial coefficient matrix is nonnegative
    (Corollary cor.lgv.binom-det-nonneg)
* `LGV.catalan_hankel_det`: Hankel determinant of Catalan numbers equals 1
    (Corollary cor.lgv.catalan-hankel-det-0)
* `LGV.catalan_hankel_det_zero` through `LGV.catalan_hankel_det_seven`: Base cases proved
    by computation

## References

* Source: AlgebraicCombinatorics/tex/Determinants/LGV2.tex
* [Lindström, *On the vector representations of induced matroids*][Lindstrom73]
* [Gessel-Viennot, *Binomial determinants, paths, and hook length formulae*][GesVie85]

## Implementation notes

We formalize the LGV lemma for general path-finite acyclic digraphs, with the integer
lattice ℤ² as a special case. The key construction is a sign-reversing involution
on intersecting path tuples that exchanges tails at the first intersection point.

The nonpermutable case applies when the source and target vertices are "sorted" in
a way that prevents non-identity permutations from having non-intersecting path tuples.

For the Catalan Hankel determinant, we use Mathlib's `catalan` function and prove
the base cases (k = 0, 1, ..., 7) by direct computation using `native_decide`.
The general theorem uses the LGV lemma with Dyck paths.

### Relationship with LGV1.lean

This file (LGV2.lean) and LGV1.lean both work with the integer lattice digraph, but
use different representations:

- **LGV1.lean**: Uses Mathlib's `Digraph` type and `LatticePath` (list of steps: east/north)
- **LGV2.lean**: Uses `LGV.SimpleDigraph` (custom structure with irreflexivity) and
  `SimpleDigraph.Path` (list of vertices)

The integer lattice definitions have equivalent adjacency relations, proven by
`integerLattice_arc_iff` and `integerLattice_toDigraph_adj_iff`. The conversion
`SimpleDigraph.toDigraph` allows transferring results between the two representations.

This file contains the complete weighted LGV lemma proof. LGV1.lean contains the
counting case infrastructure with lattice-specific path counting results.
-/

open Finset BigOperators Matrix

namespace LGV

/-!
## Digraph Definitions

We work with simple digraphs that are path-finite and acyclic.
-/

/-- A simple digraph with vertex set V.
    Convention conv.lgv.digraph(d): A simple digraph has arcs as pairs of distinct vertices. -/
structure SimpleDigraph (V : Type*) where
  /-- The arc relation: `arc u v` means there is an arc from `u` to `v` -/
  arc : V → V → Prop
  /-- No self-loops -/
  arc_irrefl : ∀ v, ¬arc v v

namespace SimpleDigraph

variable {V : Type*} [DecidableEq V]

/-- A path in a digraph is a list of vertices where consecutive vertices are connected by arcs.
    A path may contain 0 arcs (in which case start and end are identical). -/
structure Path (D : SimpleDigraph V) where
  /-- The vertices of the path, in order -/
  vertices : List V
  /-- The path is nonempty -/
  nonempty : vertices ≠ []
  /-- Consecutive vertices are connected by arcs -/
  arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, D.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
      (vertices.get ⟨i + 1, hi⟩)

/-- The starting vertex of a path -/
def Path.start {D : SimpleDigraph V} (p : Path D) : V :=
  p.vertices.head p.nonempty

/-- The ending vertex of a path -/
def Path.finish {D : SimpleDigraph V} (p : Path D) : V :=
  p.vertices.getLast p.nonempty

omit [DecidableEq V] in
/-- Simp lemma for `Path.start` on a constructed path -/
@[simp] lemma Path.start_mk {D : SimpleDigraph V} (vs : List V) (hne : vs ≠ [])
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < vs.length, D.arc (vs.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vs.get ⟨i + 1, hi⟩)) :
    (Path.mk vs hne harcs).start = vs.head hne := rfl

omit [DecidableEq V] in
/-- Simp lemma for `Path.finish` on a constructed path -/
@[simp] lemma Path.finish_mk {D : SimpleDigraph V} (vs : List V) (hne : vs ≠ [])
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < vs.length, D.arc (vs.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vs.get ⟨i + 1, hi⟩)) :
    (Path.mk vs hne harcs).finish = vs.getLast hne := rfl

/-- A digraph is path-finite if there are only finitely many paths between any two vertices.
    Convention conv.lgv.digraph(b) -/
def IsPathFinite (D : SimpleDigraph V) : Prop :=
  ∀ u v : V, Set.Finite {p : Path D | p.start = u ∧ p.finish = v}

/-- A digraph is acyclic if it has no directed cycles.
    Convention conv.lgv.digraph(c) -/
def IsAcyclic (D : SimpleDigraph V) : Prop :=
  ∀ p : Path D, p.start = p.finish → p.vertices.length = 1

/-- Extract a subpath from index `i` to index `j` (inclusive).
    The resulting path has `j - i + 1` vertices. -/
def Path.subpath {D : SimpleDigraph V} (p : Path D) (i j : ℕ) (hij : i ≤ j) 
    (hj : j < p.vertices.length) : Path D where
  vertices := (p.vertices.drop i).take (j - i + 1)
  nonempty := by
    simp only [ne_eq, List.take_eq_nil_iff, List.drop_eq_nil_iff]
    push Not
    constructor <;> omega
  arcs_valid := by
    intro k hk
    simp only [List.length_take, List.length_drop] at hk
    have hk' : k + 1 < min (j - i + 1) (p.vertices.length - i) := hk
    have hk'' : k < j - i := by omega
    simp only [List.getElem_take, List.getElem_drop, List.get_eq_getElem]
    have hi' : i + k < p.vertices.length := by omega
    have hi'' : i + k + 1 < p.vertices.length := by omega
    convert p.arcs_valid (i + k) hi'' using 2

omit [DecidableEq V] in
/-- The start of a subpath is the vertex at index `i`. -/
lemma Path.subpath_start {D : SimpleDigraph V} (p : Path D) (i j : ℕ) (hij : i ≤ j) 
    (hj : j < p.vertices.length) :
    (p.subpath i j hij hj).start = p.vertices.get ⟨i, Nat.lt_of_le_of_lt hij hj⟩ := by
  simp only [subpath, start, List.head_eq_getElem, List.getElem_take, List.getElem_drop, 
             List.get_eq_getElem, add_zero]

omit [DecidableEq V] in
/-- The finish of a subpath is the vertex at index `j`. -/
lemma Path.subpath_finish {D : SimpleDigraph V} (p : Path D) (i j : ℕ) (hij : i ≤ j) 
    (hj : j < p.vertices.length) :
    (p.subpath i j hij hj).finish = p.vertices.get ⟨j, hj⟩ := by
  simp only [subpath, finish]
  rw [List.getLast_eq_getElem]
  simp only [List.length_take, List.length_drop, List.getElem_take, List.getElem_drop]
  congr 1
  omega

omit [DecidableEq V] in
/-- The length of a subpath from `i` to `j` is `j - i + 1`. -/
lemma Path.subpath_length {D : SimpleDigraph V} (p : Path D) (i j : ℕ) (hij : i ≤ j) 
    (hj : j < p.vertices.length) :
    (p.subpath i j hij hj).vertices.length = j - i + 1 := by
  simp only [subpath, List.length_take, List.length_drop]
  omega

omit [DecidableEq V] in
/-- In an acyclic digraph, all vertices on a path are distinct.
    This follows from the fact that if a vertex appears twice, we could extract
    a cycle (a path from that vertex back to itself). -/
lemma Path.vertices_nodup_of_acyclic {D : SimpleDigraph V} (hac : D.IsAcyclic) 
    (p : Path D) : p.vertices.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro ⟨i, hi⟩ ⟨j, hj⟩ hget
  simp only [Fin.mk.injEq]
  -- hget : p.vertices[i] = p.vertices[j]
  -- WLOG i ≤ j
  by_cases hij : i ≤ j
  · -- Case i ≤ j: Extract subpath from i to j
    let sp := p.subpath i j hij hj
    -- This subpath starts and ends at the same vertex
    have hcycle : sp.start = sp.finish := by
      simp only [sp, subpath_start, subpath_finish, List.get_eq_getElem]
      exact hget
    -- By acyclicity, the subpath has length 1
    have hlen1 := hac sp hcycle
    -- The subpath length is j - i + 1
    have hlen2 : sp.vertices.length = j - i + 1 := subpath_length p i j hij hj
    -- So j - i + 1 = 1, i.e., j = i
    omega
  · -- Case j < i: symmetric
    push Not at hij
    have hij' : j ≤ i := le_of_lt hij
    let sp := p.subpath j i hij' hi
    have hcycle : sp.start = sp.finish := by
      simp only [sp, subpath_start, subpath_finish, List.get_eq_getElem]
      exact hget.symm
    have hlen1 := hac sp hcycle
    have hlen2 : sp.vertices.length = i - j + 1 := subpath_length p j i hij' hi
    omega

/-!
### Conversion to Mathlib's Digraph

`LGV.SimpleDigraph` is a specialized digraph structure that enforces irreflexivity
(no self-loops). Mathlib's `Digraph` is more general and allows self-loops.

We provide a conversion that forgets the irreflexivity proof, allowing use of
Mathlib's digraph infrastructure when needed.
-/

variable {V : Type*}

/-- Convert a `SimpleDigraph` to Mathlib's `Digraph`.
    This forgets the irreflexivity proof but preserves the adjacency relation.
    
    Note: LGV1.lean uses Mathlib's `Digraph` directly, while LGV2.lean uses this
    `SimpleDigraph` structure. This conversion enables interoperability. -/
def toDigraph (D : SimpleDigraph V) : Digraph V where
  Adj := D.arc

/-- The adjacency relation is preserved by `toDigraph`. -/
@[simp]
theorem toDigraph_adj (D : SimpleDigraph V) (u v : V) :
    D.toDigraph.Adj u v ↔ D.arc u v := Iff.rfl

end SimpleDigraph

/-!
## The Integer Lattice ℤ²

Definition def.lgv.lattice: The integer lattice has vertex set ℤ² with arcs
(i,j) → (i+1,j) (east-steps) and (i,j) → (i,j+1) (north-steps).

### Relationship with LGV1.lean

LGV1.lean defines `LGV.integerLattice : Digraph LatticePoint` using Mathlib's `Digraph`.
This file defines `LGV.integerLattice : SimpleDigraph (ℤ × ℤ)` using our custom structure.

The two definitions have semantically identical adjacency relations:
- LGV1: `IntegerLatticeAdj p q ↔ q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1)`
- LGV2: `integerLattice.arc u v ↔ (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 ∧ v.2 = u.2 + 1)`

The lemma `integerLattice_arc_iff` proves these are equivalent, enabling
results from either file to be transferred to the other.
-/

/-- The integer lattice digraph ℤ².
    
    This is the same lattice as in LGV1.lean, but using `SimpleDigraph` instead of
    Mathlib's `Digraph`. See `integerLattice_arc_iff` for the characterization
    and `integerLattice_toDigraph_adj_iff` for the equivalence with LGV1's definition. -/
def integerLattice : SimpleDigraph (ℤ × ℤ) where
  arc u v := (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 ∧ v.2 = u.2 + 1)
  arc_irrefl := by
    intro ⟨x, y⟩
    simp only [not_or, not_and]
    constructor <;> omega

/-- Characterization of adjacency in the integer lattice.
    An arc exists from u to v iff v is one step east or north of u.
    
    This matches the form of `integerLattice_adj_iff` in LGV1.lean. -/
theorem integerLattice_arc_iff (u v : ℤ × ℤ) :
    integerLattice.arc u v ↔ v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1) := by
  simp only [integerLattice, Prod.ext_iff]

/-- The integer lattice adjacency relation in LGV2 matches the one in LGV1.
    
    This bridges the two definitions:
    - LGV1.lean: `integerLattice.Adj p q` where `integerLattice : Digraph LatticePoint`
    - LGV2.lean: `integerLattice.arc u v` where `integerLattice : SimpleDigraph (ℤ × ℤ)`
    
    Both are equivalent to: `v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1)` -/
theorem integerLattice_toDigraph_adj_iff (u v : ℤ × ℤ) :
    integerLattice.toDigraph.Adj u v ↔ v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1) :=
  integerLattice_arc_iff u v

/-- Each arc in the integer lattice increases coordinates (or keeps them equal) -/
private lemma integerLattice_arc_nondecreasing (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    u.1 ≤ v.1 ∧ u.2 ≤ v.2 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega

/-- Each arc in the integer lattice increases the sum x + y by exactly 1 -/
private lemma integerLattice_arc_sum (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    v.1 + v.2 = u.1 + u.2 + 1 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega

/-- Coordinates are monotone along a path in the integer lattice -/
private lemma integerLattice_path_monotone (p : SimpleDigraph.Path integerLattice) (i j : ℕ)
    (hi : i < p.vertices.length) (hj : j < p.vertices.length) (hij : i ≤ j) :
    (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j, hj⟩).1 ∧
    (p.vertices.get ⟨i, hi⟩).2 ≤ (p.vertices.get ⟨j, hj⟩).2 := by
  induction j with
  | zero =>
    simp only [Nat.le_zero] at hij
    subst hij
    constructor <;> rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hik
    · constructor <;> rfl
    · have hk : k < p.vertices.length := Nat.lt_of_succ_lt hj
      have hik' : i ≤ k := Nat.lt_succ_iff.mp hik
      obtain ⟨h1, h2⟩ := ih hk hik'
      have harc : integerLattice.arc (p.vertices.get ⟨k, hk⟩) (p.vertices.get ⟨k + 1, hj⟩) :=
        p.arcs_valid k hj
      obtain ⟨h3, h4⟩ := integerLattice_arc_nondecreasing _ _ harc
      exact ⟨le_trans h1 h3, le_trans h2 h4⟩

/-- Start coordinates ≤ finish coordinates for any path in the integer lattice -/
private lemma integerLattice_path_start_le_finish (p : SimpleDigraph.Path integerLattice) :
    p.start.1 ≤ p.finish.1 ∧ p.start.2 ≤ p.finish.2 := by
  have hne := p.nonempty
  have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil hne
  have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
  have h := integerLattice_path_monotone p 0 (p.vertices.length - 1) hlen hlast (Nat.zero_le _)
  simp only [SimpleDigraph.Path.start, SimpleDigraph.Path.finish]
  convert h using 2 <;> simp [List.head_eq_getElem, List.getLast_eq_getElem]

/-- Helper for path_sum_eq: proves the sum formula by induction on the list -/
private lemma integerLattice_path_sum_eq_aux (l : List (ℤ × ℤ)) (hne : l ≠ [])
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < l.length, integerLattice.arc (l.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (l.get ⟨i + 1, hi⟩)) :
    (l.getLast hne).1 + (l.getLast hne).2 = (l.head hne).1 + (l.head hne).2 + (l.length - 1) := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      have hne' : y :: ys ≠ [] := List.cons_ne_nil y ys
      have harcs' : ∀ i : ℕ, ∀ hi : i + 1 < (y :: ys).length,
          integerLattice.arc ((y :: ys).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((y :: ys).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (x :: y :: ys).length := by simp at hi ⊢; omega
        have := harcs (i + 1) hi'
        simp only [List.length_cons, List.get_cons_succ] at this ⊢
        exact this
      have harc_xy : integerLattice.arc x y := by
        have := harcs 0 (by simp : 0 + 1 < (x :: y :: ys).length)
        simp at this
        exact this
      have hsum_xy := integerLattice_arc_sum x y harc_xy
      specialize ih hne' harcs'
      simp only [List.getLast_cons hne', List.head_cons, List.length_cons] at ih ⊢
      omega

/-- The sum of coordinates increases by exactly (length - 1) along a path -/
private lemma integerLattice_path_sum_eq (p : SimpleDigraph.Path integerLattice) :
    p.finish.1 + p.finish.2 = p.start.1 + p.start.2 + (p.vertices.length - 1) :=
  integerLattice_path_sum_eq_aux p.vertices p.nonempty p.arcs_valid

/-- Path length is determined by start and finish coordinates -/
lemma integerLattice_path_length_eq (p : SimpleDigraph.Path integerLattice) :
    (p.vertices.length : ℤ) = p.finish.1 + p.finish.2 - p.start.1 - p.start.2 + 1 := by
  have h := integerLattice_path_sum_eq p
  have hpos : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
  omega

/-- Sum at vertex i equals start sum + i -/
lemma integerLattice_path_vertex_sum (p : SimpleDigraph.Path integerLattice) (i : ℕ)
    (hi : i < p.vertices.length) :
    (p.vertices.get ⟨i, hi⟩).1 + (p.vertices.get ⟨i, hi⟩).2 = p.start.1 + p.start.2 + i := by
  induction i with
  | zero =>
    simp only [SimpleDigraph.Path.start, CharP.cast_eq_zero, add_zero]
    have : p.vertices.get ⟨0, hi⟩ = p.vertices.head p.nonempty := by
      simp [List.head_eq_getElem, List.get_eq_getElem]
    rw [this]
  | succ k ih =>
    have hk : k < p.vertices.length := Nat.lt_of_succ_lt hi
    have ihk := ih hk
    have harc := p.arcs_valid k hi
    have hsum := integerLattice_arc_sum _ _ harc
    omega

/-- x-coordinate change at each step is 0 or 1 -/
lemma integerLattice_path_x_step (p : SimpleDigraph.Path integerLattice) (i : ℕ)
    (hi : i + 1 < p.vertices.length) :
    (p.vertices.get ⟨i + 1, hi⟩).1 - (p.vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩).1 = 0 ∨
    (p.vertices.get ⟨i + 1, hi⟩).1 - (p.vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩).1 = 1 := by
  have harc := p.arcs_valid i hi
  rcases harc with ⟨hx, _⟩ | ⟨hx, _⟩ <;> [right; left] <;> omega

/-- Vertices of a lattice path are bounded by start and finish coordinates -/
lemma integerLattice_path_vertices_bounded (p : SimpleDigraph.Path integerLattice) (i : ℕ)
    (hi : i < p.vertices.length) :
    p.start.1 ≤ (p.vertices.get ⟨i, hi⟩).1 ∧ (p.vertices.get ⟨i, hi⟩).1 ≤ p.finish.1 ∧
    p.start.2 ≤ (p.vertices.get ⟨i, hi⟩).2 ∧ (p.vertices.get ⟨i, hi⟩).2 ≤ p.finish.2 := by
  have hne := p.nonempty
  have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil hne
  have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
  have h1 := integerLattice_path_monotone p 0 i hlen hi (Nat.zero_le _)
  have h2 := integerLattice_path_monotone p i (p.vertices.length - 1) hi hlast (Nat.le_sub_one_of_lt hi)
  simp only [SimpleDigraph.Path.start, SimpleDigraph.Path.finish]
  constructor
  · convert h1.1 using 1; simp [List.head_eq_getElem]
  constructor
  · convert h2.1 using 1; simp [List.getLast_eq_getElem]
  constructor
  · convert h1.2 using 1; simp [List.head_eq_getElem]
  · convert h2.2 using 1; simp [List.getLast_eq_getElem]

/-- Paths in the integer lattice are determined by their vertex list -/
private lemma integerLattice_path_ext (p q : SimpleDigraph.Path integerLattice)
    (h : p.vertices = q.vertices) : p = q := by
  cases p; cases q
  simp only [SimpleDigraph.Path.mk.injEq] at h ⊢
  exact h

/-- The integer lattice is acyclic -/
theorem integerLattice_acyclic : integerLattice.IsAcyclic := by
  intro p hp
  -- We'll show that any path in the integer lattice that returns to its start must be trivial
  -- Key observation: each arc increases x+y by exactly 1
  by_contra h
  -- If the path has length > 1, it has at least one arc
  have hpos : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
  have hlen : 1 < p.vertices.length := by
    rcases Nat.eq_or_lt_of_le (Nat.one_le_of_lt hpos) with heq | hlt
    · exact (h heq.symm).elim
    · exact hlt
  -- We'll prove by induction that for all i, the sum x+y at position i is at least x+y at position 0 plus i
  have hmono : ∀ i : ℕ, ∀ hi : i < p.vertices.length,
      (p.vertices.get ⟨i, hi⟩).1 + (p.vertices.get ⟨i, hi⟩).2 ≥
      (p.vertices.get ⟨0, hpos⟩).1 + (p.vertices.get ⟨0, hpos⟩).2 + i := by
    intro i
    induction i with
    | zero => intro hi; simp
    | succ n ih =>
      intro hi
      have hn : n < p.vertices.length := Nat.lt_of_succ_lt hi
      have harci : n + 1 < p.vertices.length := hi
      have harc_n := p.arcs_valid n harci
      simp only [integerLattice] at harc_n
      have ih_n := ih hn
      rcases harc_n with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
  -- Apply to the last vertex
  have hlast_idx : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hpos Nat.one_pos
  have hlast := hmono (p.vertices.length - 1) hlast_idx
  -- The last vertex is getLast
  have hlast_eq : p.vertices.get ⟨p.vertices.length - 1, hlast_idx⟩ = p.vertices.getLast p.nonempty := by
    simp [List.getLast_eq_getElem]
  rw [hlast_eq] at hlast
  -- start = head = get 0
  have hstart : p.start = p.vertices.get ⟨0, hpos⟩ := by
    simp [SimpleDigraph.Path.start, List.head_eq_getElem]
  -- finish = getLast
  have hfinish : p.finish = p.vertices.getLast p.nonempty := rfl
  -- Since start = finish
  rw [← hfinish, ← hp, hstart] at hlast
  -- We get a contradiction since length - 1 ≥ 1
  have hlen' : p.vertices.length - 1 ≥ 1 := Nat.le_sub_one_of_lt hlen
  omega

/-- The integer lattice is path-finite -/
theorem integerLattice_pathFinite : integerLattice.IsPathFinite := by
  intro u v
  by_cases h : v.1 < u.1 ∨ v.2 < u.2
  · -- Case 1: No paths exist (would need to go backwards)
    convert Set.finite_empty
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hstart hfinish
    have hle := integerLattice_path_start_le_finish p
    rw [hstart, hfinish] at hle
    omega
  · -- Case 2: Paths exist but are finite
    push Not at h
    -- Define the path length and bounding box
    let n := (v.1 - u.1 + v.2 - u.2 + 1).toNat
    let box : Finset (ℤ × ℤ) := (Finset.Icc u.1 v.1) ×ˢ (Finset.Icc u.2 v.2)
    -- Define the subtype of paths from u to v
    let S := {p : SimpleDigraph.Path integerLattice | p.start = u ∧ p.finish = v}
    -- Show S is finite by injecting into Fin n → box
    suffices Finite S by exact Set.finite_coe_iff.mpr this
    -- Define the injection: map each path to its vertex list as a function
    let f : S → (Fin n → box) := fun ⟨p, hp⟩ i =>
      let hi : i.val < p.vertices.length := by
        have hlen := integerLattice_path_length_eq p
        rw [hp.1, hp.2] at hlen
        simp only [n] at hlen ⊢
        have := i.isLt
        omega
      ⟨p.vertices.get ⟨i.val, hi⟩, by
        have hbd := integerLattice_path_vertices_bounded p i.val hi
        rw [hp.1, hp.2] at hbd
        simp only [box, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hbd.1, hbd.2.1⟩, ⟨hbd.2.2.1, hbd.2.2.2⟩⟩⟩
    have hinj : Function.Injective f := by
      intro ⟨p, hp⟩ ⟨q, hq⟩ heq
      simp only [Subtype.mk.injEq, f] at heq ⊢
      apply integerLattice_path_ext
      apply List.ext_get
      · -- Lengths are equal (both determined by u and v)
        have hlenp := integerLattice_path_length_eq p
        have hlenq := integerLattice_path_length_eq q
        rw [hp.1, hp.2] at hlenp
        rw [hq.1, hq.2] at hlenq
        omega
      · -- Elements are equal at each position
        intro i hip hiq
        have heqi := congr_fun heq ⟨i, by
          have hlenp := integerLattice_path_length_eq p
          rw [hp.1, hp.2] at hlenp
          simp only [n]
          omega⟩
        simp only [Subtype.mk.injEq] at heqi
        exact heqi
    exact Finite.of_injective f hinj

/-!
## Path Weights

For each arc, we assign a weight from a commutative ring K.
The weight of a path is the product of its arc weights.
-/

variable {V : Type*} [DecidableEq V] {K : Type*} [CommRing K]

/-- An arc weight function assigns a ring element to each arc.
    Definition in Theorem thm.lgv.kpaths.wt -/
def ArcWeight (D : SimpleDigraph V) (K : Type*) := (u v : V) → D.arc u v → K

/-- Helper function to compute the product of arc weights along a vertex list.
    Uses recursion on the structure of the list.
    - For an empty list or single vertex, the weight is 1 (no arcs).
    - For a list [v₀, v₁, ...], the weight is w(v₀, v₁) * (weight of [v₁, ...]). -/
noncomputable def pathWeightAux {D : SimpleDigraph V} (w : ArcWeight D K)
    (vertices : List V) (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      D.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) : K :=
  match vertices with
  | [] => 1
  | [_] => 1
  | v₀ :: v₁ :: rest =>
    have h : 0 + 1 < (v₀ :: v₁ :: rest).length := by simp
    have arc_proof : D.arc v₀ v₁ := by
      have := arcs_valid 0 h
      simp at this
      exact this
    have rest_arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
        D.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
      intro i hi
      have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
      have := arcs_valid (i + 1) hi'
      simp only [List.length_cons, List.get_cons_succ] at this ⊢
      exact this
    w v₀ v₁ arc_proof * pathWeightAux w (v₁ :: rest) rest_arcs_valid

/-- The weight of a path is the product of weights of its arcs.
    w(p) := ∏_{a is an arc of p} w(a) -/
noncomputable def pathWeight {D : SimpleDigraph V} (w : ArcWeight D K) (p : SimpleDigraph.Path D) : K :=
  pathWeightAux w p.vertices p.arcs_valid

omit [DecidableEq V] in
/-- pathWeightAux is independent of the proof of arcs_valid (proof irrelevance). -/
lemma pathWeightAux_proof_irrel {D : SimpleDigraph V} (w : ArcWeight D K)
    (l : List V) (arcs1 arcs2 : ∀ i : ℕ, ∀ hi : i + 1 < l.length,
      D.arc (l.get ⟨i, Nat.lt_of_succ_lt hi⟩) (l.get ⟨i + 1, hi⟩)) :
    pathWeightAux w l arcs1 = pathWeightAux w l arcs2 := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    cases vs with
    | nil => rfl
    | cons v' vs' =>
      unfold pathWeightAux
      show (w v v' _ * pathWeightAux w (v' :: vs') _) = (w v v' _ * pathWeightAux w (v' :: vs') _)
      rfl

omit [DecidableEq V] in
/-- pathWeightAux equality when lists are equal (combines substitution with proof irrelevance). -/
lemma pathWeightAux_eq_of_eq {D : SimpleDigraph V} (w : ArcWeight D K) {l1 l2 : List V} (h : l1 = l2)
    (arcs1 : ∀ i : ℕ, ∀ hi : i + 1 < l1.length,
      D.arc (l1.get ⟨i, Nat.lt_of_succ_lt hi⟩) (l1.get ⟨i + 1, hi⟩))
    (arcs2 : ∀ i : ℕ, ∀ hi : i + 1 < l2.length,
      D.arc (l2.get ⟨i, Nat.lt_of_succ_lt hi⟩) (l2.get ⟨i + 1, hi⟩)) :
    pathWeightAux w l1 arcs1 = pathWeightAux w l2 arcs2 := by
  subst h
  exact pathWeightAux_proof_irrel w l1 arcs1 arcs2

omit [DecidableEq V] in
/-- pathWeightAux of a singleton list is 1. -/
@[simp]
lemma pathWeightAux_singleton {D : SimpleDigraph V} (w : ArcWeight D K) (v : V)
    (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < [v].length,
      D.arc ([v].get ⟨i, Nat.lt_of_succ_lt hi⟩) ([v].get ⟨i + 1, hi⟩)) :
    pathWeightAux w [v] arcs_valid = 1 := rfl

omit [DecidableEq V] in
/-- pathWeightAux of a two-element list is just the arc weight. -/
lemma pathWeightAux_pair {D : SimpleDigraph V} (w : ArcWeight D K) (u v : V)
    (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < [u, v].length,
      D.arc ([u, v].get ⟨i, Nat.lt_of_succ_lt hi⟩) ([u, v].get ⟨i + 1, hi⟩)) :
    pathWeightAux w [u, v] arcs_valid = w u v (arcs_valid 0 (by simp)) := by
  unfold pathWeightAux
  simp

omit [DecidableEq V] in
/-- pathWeightAux of a cons-cons list factors into an arc weight times the tail. -/
lemma pathWeightAux_cons_cons {D : SimpleDigraph V} (w : ArcWeight D K) (u v : V) (rest : List V)
    (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < (u :: v :: rest).length,
      D.arc ((u :: v :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((u :: v :: rest).get ⟨i + 1, hi⟩))
    (rest_arcs : ∀ i : ℕ, ∀ hi : i + 1 < (v :: rest).length,
      D.arc ((v :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((v :: rest).get ⟨i + 1, hi⟩))
    (arc_uv : D.arc u v) :
    pathWeightAux w (u :: v :: rest) arcs_valid = 
      w u v arc_uv * pathWeightAux w (v :: rest) rest_arcs := by
  simp only [pathWeightAux]

omit [DecidableEq V] in
/-- pathWeightAux is multiplicative over list append when the lists share a common vertex.
    If l1 = [..., v] and l2 = [v, ...], then pathWeightAux (l1 ++ l2.tail) = pathWeightAux l1 * pathWeightAux l2. -/
lemma pathWeightAux_append {D : SimpleDigraph V} (w : ArcWeight D K)
    (l1 l2 : List V) (h1_ne : l1 ≠ []) (h2_ne : l2 ≠ [])
    (h_join : l1.getLast h1_ne = l2.head h2_ne)
    (arcs1 : ∀ i : ℕ, ∀ hi : i + 1 < l1.length,
      D.arc (l1.get ⟨i, Nat.lt_of_succ_lt hi⟩) (l1.get ⟨i + 1, hi⟩))
    (arcs2 : ∀ i : ℕ, ∀ hi : i + 1 < l2.length,
      D.arc (l2.get ⟨i, Nat.lt_of_succ_lt hi⟩) (l2.get ⟨i + 1, hi⟩))
    (arcs_concat : ∀ i : ℕ, ∀ hi : i + 1 < (l1 ++ l2.tail).length,
      D.arc ((l1 ++ l2.tail).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((l1 ++ l2.tail).get ⟨i + 1, hi⟩)) :
    pathWeightAux w (l1 ++ l2.tail) arcs_concat = pathWeightAux w l1 arcs1 * pathWeightAux w l2 arcs2 := by
  induction l1 generalizing l2 with
  | nil => simp at h1_ne
  | cons v1 vs1 ih =>
    cases vs1 with
    | nil => 
      -- l1 = [v1], so l1 ++ l2.tail = v1 :: l2.tail
      simp only [List.singleton_append, List.getLast_singleton] at h_join ⊢
      rw [pathWeightAux_singleton]
      simp only [one_mul]
      -- Need to show pathWeightAux (v1 :: l2.tail) = pathWeightAux l2
      -- Since l2 = v1 :: l2.tail (by h_join), this follows from proof irrelevance
      cases l2 with
      | nil => simp at h2_ne
      | cons v2 vs2 =>
        simp only [List.head_cons] at h_join
        subst h_join
        simp only [List.tail_cons]
    | cons v2 vs2 =>
      -- l1 = v1 :: v2 :: vs2
      simp only [List.cons_append]
      have h1_tail_ne : v2 :: vs2 ≠ [] := List.cons_ne_nil _ _
      have h_join_tail : (v2 :: vs2).getLast h1_tail_ne = l2.head h2_ne := by
        simp only [List.getLast_cons h1_tail_ne] at h_join
        exact h_join
      have arcs1_tail : ∀ i : ℕ, ∀ hi : i + 1 < (v2 :: vs2).length,
          D.arc ((v2 :: vs2).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((v2 :: vs2).get ⟨i + 1, hi⟩) := fun i hi =>
        arcs1 (i + 1) (by simp at hi ⊢; omega)
      have arcs_concat_tail : ∀ i : ℕ, ∀ hi : i + 1 < ((v2 :: vs2) ++ l2.tail).length,
          D.arc (((v2 :: vs2) ++ l2.tail).get ⟨i, Nat.lt_of_succ_lt hi⟩) 
                (((v2 :: vs2) ++ l2.tail).get ⟨i + 1, hi⟩) := fun i hi => by
        have := arcs_concat (i + 1) (by simp at hi ⊢; omega)
        simp only [List.get_eq_getElem, List.cons_append, List.getElem_cons_succ] at this ⊢
        exact this
      have ih_applied := ih l2 h1_tail_ne h2_ne h_join_tail arcs1_tail arcs2 arcs_concat_tail
      have h_eq : pathWeightAux w (v2 :: (vs2 ++ l2.tail)) arcs_concat_tail = 
                  pathWeightAux w (v2 :: vs2) arcs1_tail * pathWeightAux w l2 arcs2 := by
        convert ih_applied using 1; rfl
      simp only [pathWeightAux, h_eq]
      ring

/-- The weight of a path tuple is the product of weights of its component paths.
    w(𝐩) := w(p₁) w(p₂) ⋯ w(pₖ) -/
noncomputable def pathTupleWeight {D : SimpleDigraph V} {k : ℕ} (w : ArcWeight D K)
    (ps : Fin k → SimpleDigraph.Path D) : K :=
  ∏ i, pathWeight w (ps i)

/-!
## k-Vertices and Path Tuples

Definition def.lgv.path-tups: A k-vertex is a k-tuple of vertices.
A path tuple from 𝐀 to 𝐁 is a k-tuple of paths where pᵢ goes from Aᵢ to Bᵢ.
-/

/-- A k-vertex is a k-tuple of vertices of D.
    Definition def.lgv.path-tups(a) -/
abbrev kVertex (V : Type*) (k : ℕ) := Fin k → V

/-- Permute a k-vertex by a permutation σ: σ(𝐀) = (A_{σ(1)}, A_{σ(2)}, ..., A_{σ(k)}).
    Definition def.lgv.path-tups(b) -/
def permuteKVertex {V : Type*} {k : ℕ} (σ : Equiv.Perm (Fin k)) (A : kVertex V k) : kVertex V k :=
  fun i => A (σ i)

/-- A path tuple from 𝐀 to 𝐁 is a k-tuple (p₁, ..., pₖ) where pᵢ is a path from Aᵢ to Bᵢ.
    Definition def.lgv.path-tups(c) -/
structure PathTuple {V : Type*} [DecidableEq V] (D : SimpleDigraph V) (k : ℕ)
    (A B : kVertex V k) where
  /-- The paths in the tuple -/
  paths : Fin k → SimpleDigraph.Path D
  /-- Each path starts at the corresponding source vertex -/
  starts : ∀ i, (paths i).start = A i
  /-- Each path ends at the corresponding target vertex -/
  finishes : ∀ i, (paths i).finish = B i

@[ext]
lemma PathTuple.ext {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt1 pt2 : PathTuple D k A B)
    (h : ∀ i, pt1.paths i = pt2.paths i) : pt1 = pt2 := by
  cases pt1; cases pt2
  simp only [PathTuple.mk.injEq]
  ext i
  exact h i

/-- Two paths have a vertex in common -/
def pathsIntersect {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) : Prop :=
  ∃ v, v ∈ p.vertices ∧ v ∈ q.vertices

/-- A path tuple is non-intersecting (nipat) if no two paths share a vertex.
    Definition def.lgv.path-tups(d) -/
def PathTuple.isNonIntersecting {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) : Prop :=
  ∀ i j, i ≠ j → ¬pathsIntersect (pt.paths i) (pt.paths j)

/-- A path tuple is intersecting (ipat) if some two paths share a vertex.
    Definition def.lgv.path-tups(e) -/
def PathTuple.isIntersecting {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) : Prop :=
  ¬pt.isNonIntersecting

/-!
## The Path Weight Matrix

The matrix M where M_{i,j} = ∑_{p : Aᵢ → Bⱼ} w(p).
-/

/-- The set of paths from u to v in a path-finite digraph -/
noncomputable def pathsFromTo {V : Type*} [DecidableEq V] (D : SimpleDigraph V)
    (hpf : D.IsPathFinite) (u v : V) : Finset (SimpleDigraph.Path D) :=
  (hpf u v).toFinset

/-- The sum of weights of all paths from u to v.
    ∑_{p : u → v} w(p) -/
noncomputable def pathWeightSum {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (w : ArcWeight D K) (u v : V) : K :=
  ∑ p ∈ pathsFromTo D hpf u v, pathWeight w p

/-- The path weight matrix M_{i,j} = ∑_{p : Aᵢ → Bⱼ} w(p) -/
noncomputable def pathWeightMatrix {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (w : ArcWeight D K) {k : ℕ}
    (A B : kVertex V k) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => pathWeightSum hpf w (A i) (B j)

/-!
## LGV Lemma: Weighted Lattice Version

Theorem thm.lgv.kpaths.wt: For the integer lattice with arc weights w,
det(M) = ∑_{σ ∈ Sₖ} (-1)^σ ∑_{𝐩 nipat from 𝐀 to σ(𝐁)} w(𝐩)
-/

/-- The set of non-intersecting path tuples from 𝐀 to 𝐁 -/
noncomputable def nipatSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (PathTuple D k A B) :=
  {pt | pt.isNonIntersecting}

set_option backward.isDefEq.respectTransparency false in
/-- The set of nipats is finite (follows from path-finiteness) -/
theorem nipatSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Set.Finite (nipatSet (D := D) A B) := by
  -- The set of all path tuples from A to B is finite
  have h_all_finite : Set.Finite {pt : PathTuple D k A B | True} := by
    let pathSets : Fin k → Set (SimpleDigraph.Path D) := fun i => 
      {p : SimpleDigraph.Path D | p.start = A i ∧ p.finish = B i}
    have h_each_finite : ∀ i, Set.Finite (pathSets i) := fun i => hpf (A i) (B i)
    have h_prod_finite : Set.Finite (Set.pi Set.univ pathSets) := 
      Set.Finite.pi (fun i => h_each_finite i)
    -- Define the map from PathTuple to the pi type
    let f : {pt : PathTuple D k A B | True} → Set.pi Set.univ pathSets := fun ⟨pt, _⟩ =>
      ⟨pt.paths, fun i _ => ⟨pt.starts i, pt.finishes i⟩⟩
    have hf_inj : Function.Injective f := by
      intro ⟨pt1, _⟩ ⟨pt2, _⟩ heq
      simp only [Subtype.mk.injEq, f] at heq ⊢
      cases pt1; cases pt2
      simp only [PathTuple.mk.injEq] at heq ⊢
      exact heq
    -- The pi type is finite
    have h_pi_finite : Finite (Set.pi Set.univ pathSets) := h_prod_finite
    -- Since f is injective and the codomain is finite, the domain is finite
    have h_finite : Finite {pt : PathTuple D k A B | True} := Finite.of_injective f hf_inj
    exact Set.finite_coe_iff.mp h_finite
  exact h_all_finite.subset (fun _ _ => trivial)

/-- Convert nipatSet to Finset using the finiteness proof -/
noncomputable def nipatFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Finset (PathTuple D k A B) :=
  (nipatSetFinite hpf A B).toFinset

/-- When nipatSet is empty, nipatFinset is empty -/
theorem nipatFinset_of_empty {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k)
    (h : nipatSet (D := D) A B = ∅) :
    nipatFinset hpf A B = ∅ := by
  unfold nipatFinset
  rw [Set.Finite.toFinset_eq_empty]
  exact h

/-- Sum of weights over all nipats from 𝐀 to 𝐁
    Note: σ is not used in this definition since the permutation is already
    encoded in B (which should be permuteKVertex σ B' for some B') -/
noncomputable def nipatWeightSum {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (w : ArcWeight D K) {k : ℕ}
    (A B : kVertex V k) (_σ : Equiv.Perm (Fin k)) : K :=
  ∑ pt ∈ nipatFinset hpf A B, pathTupleWeight w pt.paths

/-!
## Path Tuple Infrastructure for LGV

The key step in the LGV proof is to express the product of sums as a sum over path tuples:
  ∏_j (∑_{p : A_j → B_j} w(p)) = ∑_{pt : PathTuple} pathTupleWeight w pt.paths

This uses `Finset.prod_univ_sum` and a bijection between PathTuple and the piFinset.
-/

/-- Bijection between PathTuple and the piFinset of pathsFromTo.
    This is the key to converting the product of sums to a sum over path tuples. -/
noncomputable def pathTupleEquivPiFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    PathTuple D k A B ≃ (Fintype.piFinset (fun j => pathsFromTo D hpf (A j) (B j))) := by
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  case toFun =>
    intro pt
    refine ⟨pt.paths, ?_⟩
    simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    intro j
    exact ⟨pt.starts j, pt.finishes j⟩
  case invFun =>
    intro ⟨f, hf⟩
    simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hf
    exact ⟨f, fun j => (hf j).1, fun j => (hf j).2⟩
  case left_inv =>
    intro pt
    rfl
  case right_inv =>
    intro ⟨f, hf⟩
    rfl

/-!
## LGV Lemma: General Digraph Version

Theorem thm.lgv.kpaths.wt-dg: The same result holds for any path-finite acyclic digraph.

The proof uses a sign-reversing involution on intersecting path tuples. The key steps are:

1. Express det(M) using the Leibniz formula as ∑_σ (-1)^σ ∏_i M_{i,σ(i)}
2. Expand each product as a sum over path tuples from 𝐀 to σ(𝐁)
3. Define a sign-reversing involution f on intersecting path tuples:
   - Find the first crowded point (vertex in multiple paths)
   - Pick the smallest index i whose path contains a crowded point
   - Pick the first crowded point v on path p_i
   - Pick the largest index j such that v is on path p_j
   - Exchange the tails of p_i and p_j at v
   - This maps (σ, 𝐩) to (σ ∘ t_{i,j}, 𝐩'), where t_{i,j} is the transposition
4. The involution preserves weight but flips sign, so intersecting tuples cancel
5. Only non-intersecting path tuples (nipats) contribute to the sum
-/

variable {V : Type*} [DecidableEq V]

/-- A crowded point in a path tuple is a vertex that appears in at least two paths -/
def PathTuple.isCrowded {D : SimpleDigraph V} {k : ℕ} {A B : kVertex V k}
    (pt : PathTuple D k A B) (v : V) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧ v ∈ (pt.paths i).vertices ∧ v ∈ (pt.paths j).vertices

/-- An intersecting path tuple has at least one crowded point -/
theorem PathTuple.isIntersecting_iff_exists_crowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt.isIntersecting ↔ ∃ v, pt.isCrowded v := by
  unfold isIntersecting isNonIntersecting isCrowded pathsIntersect
  push Not
  constructor
  · intro ⟨i, j, hij, v, hvi, hvj⟩
    exact ⟨v, i, j, hij, hvi, hvj⟩
  · intro ⟨v, i, j, hij, hvi, hvj⟩
    exact ⟨i, j, hij, v, hvi, hvj⟩

/-- The set of path tuples from 𝐀 to σ(𝐁) paired with the permutation σ -/
def pathTupleWithPerm {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Type _ :=
  (σ : Equiv.Perm (Fin k)) × PathTuple D k A (permuteKVertex σ B)

/-- The sign of a path tuple with permutation is (-1)^σ -/
def signOfPathTupleWithPerm {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (sp : pathTupleWithPerm (D := D) A B) : ℤˣ :=
  Equiv.Perm.sign sp.1

/-- The weight of a path tuple with permutation -/
noncomputable def weightOfPathTupleWithPerm {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (w : ArcWeight D K) (sp : pathTupleWithPerm (D := D) A B) : K :=
  pathTupleWeight w sp.2.paths

/-- The index of the first occurrence of a vertex in a path's vertex list -/
def firstIndexIn {D : SimpleDigraph V} (p : SimpleDigraph.Path D) (v : V) : ℕ :=
  p.vertices.findIdx (· = v)

-- Helper: findIdx returns the index of the first element satisfying the predicate
/-- Helper lemma: findIdx returns n if element at n satisfies predicate and all before don't.
    This is useful for showing that firstCrowdedIndexOnPath is preserved under signReversing. -/
private lemma findIdx_eq_of_first_satisfies {α : Type*} (l : List α) (p : α → Bool) (n : ℕ) (hn : n < l.length)
    (h_at_n : p l[n] = true)
    (h_before : ∀ m : ℕ, (hm : m < n) → p l[m] = false) :
    l.findIdx p = n := by
  induction l generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero =>
      simp only [List.findIdx_cons, List.getElem_cons_zero] at *
      simp only [h_at_n, ↓reduceIte]
    | succ m =>
      simp only [List.findIdx_cons]
      have h_not_px : p x = false := by
        have := h_before 0 (Nat.zero_lt_succ m)
        simp only [List.getElem_cons_zero] at this
        exact this
      simp only [h_not_px, Bool.false_eq_true, ↓reduceIte]
      apply congrArg (· + 1)
      have hm_lt : m < xs.length := by
        simp only [List.length_cons] at hn; omega
      apply ih m hm_lt
      · simp only [List.getElem_cons_succ] at h_at_n; exact h_at_n
      · intro k hk
        have := h_before (k + 1) (by omega)
        simp only [List.getElem_cons_succ] at this
        exact this

private lemma findIdx_get_eq (l : List V) (v : V) (hv : v ∈ l) :
    l[l.findIdx (· = v)]'(List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩) = v := by
  have h := @List.findIdx_getElem (α := V) (p := (· = v)) (xs := l) 
    (w := List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩)
  simp at h
  exact h

-- Helper: findIdx is bounded by the index of any element satisfying the predicate
omit [DecidableEq V] in
private lemma findIdx_le_of_mem (l : List V) (i : ℕ) (hi : i < l.length)
    (pred : V → Bool) (hp : pred l[i] = true) : l.findIdx pred ≤ i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => 
      simp only [List.getElem_cons_zero] at hp
      simp only [List.findIdx_cons, hp, le_refl, ↓reduceIte]
    | succ j =>
      simp only [List.findIdx_cons]
      simp only [List.getElem_cons_succ] at hp
      cases hx : pred x with
      | true => simp
      | false => 
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp at hi
        have := ih j (by omega : j < xs.length) hp
        omega

-- Helper: if two elements have the same findIdx, they are equal
private lemma findIdx_inj (l : List V) (v w : V) (hv : v ∈ l) (hw : w ∈ l)
    (heq : l.findIdx (· = v) = l.findIdx (· = w)) : v = w := by
  have hv_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hv, by simp⟩
  have hw_lt := List.findIdx_lt_length_of_exists (p := (· = w)) ⟨w, hw, by simp⟩
  have hv_get := findIdx_get_eq l v hv
  have hw_get := findIdx_get_eq l w hw
  have hv_lt' : l.findIdx (· = w) < l.length := by rw [← heq]; exact hv_lt
  have key : l[l.findIdx (· = v)]'hv_lt = l[l.findIdx (· = w)]'hv_lt' := by
    simp only [heq]
  rw [hv_get] at key
  have key2 : l[l.findIdx (· = w)]'hv_lt' = l[l.findIdx (· = w)]'hw_lt := by
    congr 1
  rw [key2, hw_get] at key
  exact key

/-- In an acyclic digraph, the first intersection of two paths (if they intersect)
    is well-defined: it's the same whether we look from path p or path q.
    This is because if they were different, we could form a cycle. -/
theorem first_intersection_unique {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (hp : pathsIntersect p q) :
    ∃! v, v ∈ p.vertices ∧ v ∈ q.vertices ∧
      (∀ v' ∈ p.vertices, v' ∈ q.vertices →
        firstIndexIn p v ≤ firstIndexIn p v') := by
  -- Get a common vertex from the intersection hypothesis
  obtain ⟨v₀, hv₀_p, hv₀_q⟩ := hp
  -- Define the predicate: index i has a common vertex at that position
  let P : ℕ → Prop := fun i => ∃ (hi : i < p.vertices.length), 
    p.vertices[i] ∈ q.vertices
  -- P is decidable
  have hP_dec : DecidablePred P := by
    intro i
    by_cases hi : i < p.vertices.length
    · exact decidable_of_iff (p.vertices[i] ∈ q.vertices) (by
        simp only [P]
        constructor
        · intro h
          exact ⟨hi, h⟩
        · intro ⟨_, h⟩
          convert h)
    · exact isFalse (by simp only [P, not_exists]; intro h; exact absurd h hi)
  -- There exists an index with a common vertex
  have hP_exists : ∃ i, P i := by
    have hfind_lt := List.findIdx_lt_length_of_exists (p := (· = v₀)) ⟨v₀, hv₀_p, by simp⟩
    use p.vertices.findIdx (· = v₀)
    simp only [P]
    refine ⟨hfind_lt, ?_⟩
    have : p.vertices[p.vertices.findIdx (· = v₀)] = v₀ := 
      findIdx_get_eq p.vertices v₀ hv₀_p
    rw [this]
    exact hv₀_q
  -- Find the minimum such index
  let min_idx := Nat.find hP_exists
  -- Get the vertex at this index
  have hmin_P : P min_idx := Nat.find_spec hP_exists
  simp only [P] at hmin_P
  obtain ⟨hmin_lt, hv_q⟩ := hmin_P
  -- Define v as the vertex at min_idx
  let v := p.vertices[min_idx]
  -- v is in p.vertices
  have hv_p : v ∈ p.vertices := List.getElem_mem hmin_lt
  -- Claim: v is the unique first intersection
  use v
  constructor
  · -- v satisfies the properties
    refine ⟨hv_p, hv_q, ?_⟩
    intro v' hv'_p hv'_q
    -- Show firstIndexIn p v ≤ firstIndexIn p v'
    unfold firstIndexIn
    -- The index of v in p is at most min_idx
    have hv_findIdx : p.vertices.findIdx (· = v) ≤ min_idx := by
      apply findIdx_le_of_mem p.vertices min_idx hmin_lt (· = v)
      simp [v]
    -- Also, min_idx ≤ findIdx (· = v') by minimality
    have hmin_le_v' : min_idx ≤ p.vertices.findIdx (· = v') := by
      apply Nat.find_le
      simp only [P]
      have hfind'_lt := List.findIdx_lt_length_of_exists (p := (· = v')) ⟨v', hv'_p, by simp⟩
      refine ⟨hfind'_lt, ?_⟩
      have : p.vertices[p.vertices.findIdx (· = v')] = v' := 
        findIdx_get_eq p.vertices v' hv'_p
      rw [this]
      exact hv'_q
    -- We need findIdx v ≤ findIdx v'
    -- We have findIdx v ≤ min_idx ≤ findIdx v'
    exact le_trans hv_findIdx hmin_le_v'
  · -- Uniqueness
    intro w ⟨hw_p, hw_q, hw_min⟩
    -- w also achieves the minimum
    have hw_findIdx_le : firstIndexIn p w ≤ firstIndexIn p v := hw_min v hv_p hv_q
    have hv_findIdx_le : firstIndexIn p v ≤ firstIndexIn p w := by
      unfold firstIndexIn
      have hv_findIdx : p.vertices.findIdx (· = v) ≤ min_idx := by
        apply findIdx_le_of_mem p.vertices min_idx hmin_lt (· = v)
        simp [v]
      have hmin_le_w : min_idx ≤ p.vertices.findIdx (· = w) := by
        apply Nat.find_le
        simp only [P]
        have hfind'_lt := List.findIdx_lt_length_of_exists (p := (· = w)) ⟨w, hw_p, by simp⟩
        refine ⟨hfind'_lt, ?_⟩
        have : p.vertices[p.vertices.findIdx (· = w)] = w := 
          findIdx_get_eq p.vertices w hw_p
        rw [this]
        exact hw_q
      exact le_trans hv_findIdx hmin_le_w
    have heq_idx : firstIndexIn p v = firstIndexIn p w := le_antisymm hv_findIdx_le hw_findIdx_le
    exact (findIdx_inj p.vertices v w hv_p hw_p heq_idx).symm

/-- Split a path at a vertex v, returning (head ending at v, tail starting at v).
    The head includes v, the tail starts at v. -/
noncomputable def SimpleDigraph.Path.splitAt {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : SimpleDigraph.Path D × SimpleDigraph.Path D :=
  let idx := p.vertices.findIdx (· = v)
  let head := p.vertices.take (idx + 1)
  let tail := p.vertices.drop idx
  have h_idx_lt : idx < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_head_ne : head ≠ [] := by
    intro h
    have hlen : head.length = 0 := by simp [h]
    simp only [head, List.length_take] at hlen
    omega
  have h_tail_ne : tail ≠ [] := by
    intro h
    have hlen : tail.length = 0 := by rw [h]; rfl
    simp only [tail, List.length_drop] at hlen
    omega
  have h_head_arcs : ∀ i : ℕ, ∀ hi : i + 1 < head.length,
      D.arc (head.get ⟨i, Nat.lt_of_succ_lt hi⟩) (head.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [head, List.length_take, lt_min_iff] at hi
    have hi2 : i + 1 < p.vertices.length := by omega
    have := p.arcs_valid i hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [head]
    rw [List.getElem_take, List.getElem_take]
    exact this
  have h_tail_arcs : ∀ i : ℕ, ∀ hi : i + 1 < tail.length,
      D.arc (tail.get ⟨i, Nat.lt_of_succ_lt hi⟩) (tail.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [tail, List.length_drop] at hi
    have hi2 : idx + i + 1 < p.vertices.length := by omega
    have := p.arcs_valid (idx + i) hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [tail]
    rw [List.getElem_drop, List.getElem_drop]
    convert this using 2
  (⟨head, h_head_ne, h_head_arcs⟩, ⟨tail, h_tail_ne, h_tail_arcs⟩)

/-- The head of splitAt ends at v -/
lemma SimpleDigraph.Path.splitAt_head_finish {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).1.finish = v := by
  unfold splitAt SimpleDigraph.Path.finish
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_len : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length = 
               p.vertices.findIdx (· = v) + 1 := by
    rw [List.length_take]
    omega
  have h_ne : p.vertices.take (p.vertices.findIdx (· = v) + 1) ≠ [] := by
    intro h
    have : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length = 0 := by simp [h]
    omega
  rw [List.getLast_eq_getElem]
  have h_idx : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length - 1 = 
               p.vertices.findIdx (· = v) := by
    rw [h_len]; omega
  simp only [h_idx, List.getElem_take]
  have := @List.findIdx_getElem V (· = v) p.vertices h_idx_lt
  simp at this
  exact this

/-- The tail of splitAt starts at v -/
lemma SimpleDigraph.Path.splitAt_tail_start {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).2.start = v := by
  unfold splitAt SimpleDigraph.Path.start
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_ne : p.vertices.drop (p.vertices.findIdx (· = v)) ≠ [] := by
    intro h
    have hlen : (p.vertices.drop (p.vertices.findIdx (· = v))).length = 0 := by rw [h]; rfl
    simp only [List.length_drop] at hlen
    omega
  rw [List.head_eq_getElem]
  simp only [List.getElem_drop, Nat.add_zero]
  have := @List.findIdx_getElem V (· = v) p.vertices h_idx_lt
  simp at this
  exact this

/-- Concatenate two paths where the first path ends at v and the second starts at v.
    The resulting path goes from the start of the first to the end of the second.
    The vertex v appears once in the result (not duplicated). -/
noncomputable def SimpleDigraph.Path.concat {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : SimpleDigraph.Path D :=
  let vertices := p.vertices ++ q.vertices.tail
  have h_ne : vertices ≠ [] := by
    simp only [vertices]
    intro h
    have hlen : (p.vertices ++ q.vertices.tail).length = 0 := by rw [h]; rfl
    simp only [List.length_append, List.length_tail] at hlen
    have hp_ne := p.nonempty
    have hp_len : p.vertices.length ≠ 0 := by
      intro h
      exact hp_ne (List.eq_nil_of_length_eq_zero h)
    omega
  have h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      D.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [vertices, List.length_append, List.length_tail] at hi
    simp only [List.get_eq_getElem, vertices]
    by_cases h : i + 1 < p.vertices.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left h]
      exact p.arcs_valid i h
    · push Not at h
      by_cases h' : i < p.vertices.length
      · have hi_eq : i = p.vertices.length - 1 := by omega
        have hq_len : 1 < q.vertices.length := by
          have hq_ne := q.nonempty
          by_contra hq_short
          push Not at hq_short
          have htail_len : q.vertices.tail.length = 0 := by simp only [List.length_tail]; omega
          omega
        rw [List.getElem_append_left h', List.getElem_append_right (by omega)]
        have h1 : p.vertices[i]'h' = p.finish := by 
          simp only [SimpleDigraph.Path.finish, hi_eq, List.getLast_eq_getElem]
        have h_idx : i + 1 - p.vertices.length = 0 := by omega
        have h2 : q.vertices.tail[i + 1 - p.vertices.length]'(by simp; omega) = q.vertices[1]'hq_len := by
          simp only [h_idx, List.getElem_tail]
        rw [h1, h2, hpq]
        have hq_arc := q.arcs_valid 0 hq_len
        simp only [List.get_eq_getElem, SimpleDigraph.Path.start, List.head_eq_getElem] at hq_arc ⊢
        exact hq_arc
      · push Not at h'
        have hi1 : i - p.vertices.length < q.vertices.tail.length := by simp; omega
        have hi2 : i + 1 - p.vertices.length < q.vertices.tail.length := by simp; omega
        rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
        have h1 : q.vertices.tail[i - p.vertices.length]'hi1 = 
                  q.vertices[i - p.vertices.length + 1]'(by simp at hi1; omega) := by 
          simp only [List.getElem_tail]
        have h2 : q.vertices.tail[i + 1 - p.vertices.length]'hi2 = 
                  q.vertices[i + 1 - p.vertices.length + 1]'(by simp at hi2; omega) := by 
          simp only [List.getElem_tail]
        rw [h1, h2]
        have hq_arc := q.arcs_valid (i - p.vertices.length + 1) (by simp at hi2; omega)
        simp only [List.get_eq_getElem] at hq_arc
        convert hq_arc using 2; omega
  ⟨vertices, h_ne, h_arcs⟩

omit [DecidableEq V] in
/-- The concatenation of two paths starts at the first path's start -/
lemma SimpleDigraph.Path.concat_start {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : (p.concat q hpq).start = p.start := by
  unfold concat start
  simp only
  exact List.head_append_of_ne_nil (l' := q.vertices.tail) p.nonempty

omit [DecidableEq V] in
/-- The concatenation of two paths ends at the second path's finish -/
lemma SimpleDigraph.Path.concat_finish {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : (p.concat q hpq).finish = q.finish := by
  unfold concat finish
  simp only
  have hq_ne := q.nonempty
  by_cases h : q.vertices.tail = []
  · have hq_len : q.vertices.length = 1 := by
      have : q.vertices.tail.length = 0 := by simp [h]
      simp only [List.length_tail] at this
      have hq_pos : 0 < q.vertices.length := List.length_pos_of_ne_nil hq_ne
      omega
    have hq_finish_eq_start : q.vertices.getLast hq_ne = q.vertices.head hq_ne := by
      rw [List.getLast_eq_getElem, List.head_eq_getElem]; congr; omega
    simp only [h, List.append_nil]
    rw [hq_finish_eq_start]
    unfold start at hpq
    rw [← hpq]; unfold finish; rfl
  · rw [List.getLast_append_of_ne_nil _ h, List.getLast_tail h]

omit [DecidableEq V] in
/-- pathWeight is multiplicative over path concatenation. -/
lemma pathWeight_concat {D : SimpleDigraph V} (w : ArcWeight D K) 
    (p q : SimpleDigraph.Path D) (hpq : p.finish = q.start) :
    pathWeight w (p.concat q hpq) = pathWeight w p * pathWeight w q := by
  unfold pathWeight SimpleDigraph.Path.concat
  simp only
  have h_join : p.vertices.getLast p.nonempty = q.vertices.head q.nonempty := by
    unfold SimpleDigraph.Path.finish SimpleDigraph.Path.start at hpq
    exact hpq
  exact pathWeightAux_append w p.vertices q.vertices p.nonempty q.nonempty h_join p.arcs_valid q.arcs_valid _

/-- pathWeight factors over splitAt: the weight of a path is the product of the weights
    of its head and tail after splitting at any vertex. -/
lemma pathWeight_splitAt {D : SimpleDigraph V} (w : ArcWeight D K) 
    (p : SimpleDigraph.Path D) (v : V) (hv : v ∈ p.vertices) :
    pathWeight w p = pathWeight w (p.splitAt v hv).1 * pathWeight w (p.splitAt v hv).2 := by
  unfold pathWeight SimpleDigraph.Path.splitAt
  simp only
  set idx := p.vertices.findIdx (· = v) with h_idx_def
  set head := p.vertices.take (idx + 1) with h_head_def
  set tail := p.vertices.drop idx with h_tail_def
  have h_idx_lt : idx < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_head_ne : head ≠ [] := by
    intro h
    have hlen : head.length = 0 := by simp [h]
    simp only [h_head_def, List.length_take] at hlen
    omega
  have h_tail_ne : tail ≠ [] := by
    intro h
    have hlen : tail.length = 0 := by rw [h]; rfl
    simp only [h_tail_def, List.length_drop] at hlen
    omega
  -- The key: head ++ tail.tail = p.vertices
  have h_concat : head ++ tail.tail = p.vertices := by
    simp only [h_head_def, h_tail_def]
    have htail : (p.vertices.drop idx).tail = p.vertices.drop (idx + 1) := List.tail_drop
    rw [htail, List.take_append_drop]
  -- The join condition
  have h_head_last : head.getLast h_head_ne = v := by
    simp only [h_head_def]
    rw [List.getLast_eq_getElem]
    have h_len : (p.vertices.take (idx + 1)).length = idx + 1 := by
      rw [List.length_take]; omega
    simp only [h_len]
    rw [List.getElem_take]
    have := @List.findIdx_getElem V (· = v) p.vertices h_idx_lt
    simp at this
    exact this
  have h_tail_head : tail.head h_tail_ne = v := by
    simp only [h_tail_def]
    rw [List.head_eq_getElem]
    simp only [List.getElem_drop, Nat.add_zero]
    have := @List.findIdx_getElem V (· = v) p.vertices h_idx_lt
    simp at this
    exact this
  have h_join : head.getLast h_head_ne = tail.head h_tail_ne := by
    rw [h_head_last, h_tail_head]
  -- Arc proofs
  have h_arcs_head : ∀ i : ℕ, ∀ hi : i + 1 < head.length,
      D.arc (head.get ⟨i, Nat.lt_of_succ_lt hi⟩) (head.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [h_head_def, List.length_take, lt_min_iff] at hi
    have hi2 : i + 1 < p.vertices.length := by omega
    have := p.arcs_valid i hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [h_head_def]
    rw [List.getElem_take, List.getElem_take]
    exact this
  have h_arcs_tail : ∀ i : ℕ, ∀ hi : i + 1 < tail.length,
      D.arc (tail.get ⟨i, Nat.lt_of_succ_lt hi⟩) (tail.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [h_tail_def, List.length_drop] at hi
    have hi2 : idx + i + 1 < p.vertices.length := by omega
    have := p.arcs_valid (idx + i) hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [h_tail_def]
    rw [List.getElem_drop, List.getElem_drop]
    convert this using 2
  -- Construct arcs_concat from p.arcs_valid using h_concat
  have h_len_eq : (head ++ tail.tail).length = p.vertices.length := by
    rw [h_concat]
  have h_arcs_concat : ∀ i : ℕ, ∀ hi : i + 1 < (head ++ tail.tail).length,
      D.arc ((head ++ tail.tail).get ⟨i, Nat.lt_of_succ_lt hi⟩) 
            ((head ++ tail.tail).get ⟨i + 1, hi⟩) := by
    intro i hi
    have hi' : i + 1 < p.vertices.length := h_len_eq ▸ hi
    have := p.arcs_valid i hi'
    simp only [List.get_eq_getElem] at this ⊢
    convert this using 2
  -- Apply pathWeightAux_append
  have h_main := pathWeightAux_append w head tail h_head_ne h_tail_ne h_join h_arcs_head h_arcs_tail h_arcs_concat
  -- Connect LHS to RHS using h_concat
  calc pathWeightAux w p.vertices p.arcs_valid 
      = pathWeightAux w (head ++ tail.tail) h_arcs_concat := 
          pathWeightAux_eq_of_eq w h_concat.symm _ _
    _ = pathWeightAux w head h_arcs_head * pathWeightAux w tail h_arcs_tail := h_main
    _ = pathWeightAux w head _ * pathWeightAux w tail _ := rfl

/-- The head of splitAt starts at the original path's start -/
lemma SimpleDigraph.Path.splitAt_head_start {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).1.start = p.start := by
  unfold splitAt start
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_head_ne : p.vertices.take (p.vertices.findIdx (· = v) + 1) ≠ [] := by
    intro h; have hlen : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length = 0 := by simp [h]
    simp only [List.length_take] at hlen; omega
  exact List.head_take h_head_ne

/-- The tail of splitAt ends at the original path's finish -/
lemma SimpleDigraph.Path.splitAt_tail_finish {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).2.finish = p.finish := by
  unfold splitAt finish
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_drop_ne : p.vertices.drop (p.vertices.findIdx (· = v)) ≠ [] := by
    intro h; have hlen : (p.vertices.drop (p.vertices.findIdx (· = v))).length = 0 := by rw [h]; rfl
    simp only [List.length_drop] at hlen; omega
  rw [List.getLast_drop h_drop_ne]

/-- Exchange the tails of two paths at a common vertex.
    If p goes A → v → B and q goes A' → v → B', then after exchange:
    p' goes A → v → B' and q' goes A' → v → B -/
noncomputable def exchangeTails {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    SimpleDigraph.Path D × SimpleDigraph.Path D :=
  let sp_p := p.splitAt v hv_p
  let sp_q := q.splitAt v hv_q
  let head_p := sp_p.1
  let tail_p := sp_p.2
  let head_q := sp_q.1
  let tail_q := sp_q.2
  have h1 : head_p.finish = tail_q.start := by
    have hp := SimpleDigraph.Path.splitAt_head_finish p v hv_p
    have hq := SimpleDigraph.Path.splitAt_tail_start q v hv_q
    simp only [head_p, sp_p, tail_q, sp_q] at *
    rw [hp, hq]
  have h2 : head_q.finish = tail_p.start := by
    have hp := SimpleDigraph.Path.splitAt_tail_start p v hv_p
    have hq := SimpleDigraph.Path.splitAt_head_finish q v hv_q
    simp only [tail_p, sp_p, head_q, sp_q] at *
    rw [hq, hp]
  (SimpleDigraph.Path.concat head_p tail_q h1, SimpleDigraph.Path.concat head_q tail_p h2)

/-- The first path from exchangeTails starts at the original first path's start -/
lemma exchangeTails_fst_start {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).1.start = p.start := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_start]
  exact SimpleDigraph.Path.splitAt_head_start p v hv_p

/-- The first path from exchangeTails ends at the original second path's finish -/
lemma exchangeTails_fst_finish {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).1.finish = q.finish := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_finish]
  exact SimpleDigraph.Path.splitAt_tail_finish q v hv_q

/-- The second path from exchangeTails starts at the original second path's start -/
lemma exchangeTails_snd_start {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).2.start = q.start := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_start]
  exact SimpleDigraph.Path.splitAt_head_start q v hv_q

/-- The second path from exchangeTails ends at the original first path's finish -/
lemma exchangeTails_snd_finish {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).2.finish = p.finish := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_finish]
  exact SimpleDigraph.Path.splitAt_tail_finish p v hv_p

omit [DecidableEq V] in
/-- If p.finish = v, then v is in (concat p q).vertices -/
lemma SimpleDigraph.Path.concat_mem_of_finish {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : p.finish ∈ (p.concat q hpq).vertices := by
  unfold concat
  simp only
  apply List.mem_append_left
  exact List.getLast_mem p.nonempty

/-- The crowded point v is in the first exchanged path's vertices.
    Since head_p ends at v, and concat uses head_p.vertices ++ tail_q.vertices.tail,
    v is in the first path. -/
lemma exchangeTails_fst_mem_v {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    v ∈ (exchangeTails p q v hv_p hv_q).1.vertices := by
  unfold exchangeTails
  simp only
  apply List.mem_append_left
  have h := SimpleDigraph.Path.splitAt_head_finish p v hv_p
  unfold SimpleDigraph.Path.finish at h
  have hmem := List.getLast_mem (p.splitAt v hv_p).1.nonempty
  rw [h] at hmem
  exact hmem

/-- The crowded point v is in the second exchanged path's vertices.
    Since head_q ends at v, and concat uses head_q.vertices ++ tail_p.vertices.tail,
    v is in the second path. -/
lemma exchangeTails_snd_mem_v {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    v ∈ (exchangeTails p q v hv_p hv_q).2.vertices := by
  unfold exchangeTails
  simp only
  apply List.mem_append_left
  have h := SimpleDigraph.Path.splitAt_head_finish q v hv_q
  unfold SimpleDigraph.Path.finish at h
  have hmem := List.getLast_mem (q.splitAt v hv_q).1.nonempty
  rw [h] at hmem
  exact hmem

/-- Exchanging tails twice at the same vertex returns the original paths.
    This is the key involutivity property needed for the sign-reversing involution.
    
    **Proof idea:** When we exchange tails at v:
    - p becomes head_p ++ tail_q
    - q becomes head_q ++ tail_p
    
    When we exchange again at v:
    - head_p ++ tail_q splits at v into (head_p, tail_q) 
    - head_q ++ tail_p splits at v into (head_q, tail_p)
    - Exchanging gives (head_p ++ tail_p, head_q ++ tail_q) = (p, q)
    
    The key lemma is that splitAt(concat(head, tail), v) = (head, tail) when head ends at v
    and tail starts at v, and v appears only once in head (which holds for acyclic paths). -/
-- Helper: findIdx on head after splitAt equals head.length - 1
private lemma splitAt_head_findIdx_eq (l : List V) (v : V) (hv : v ∈ l) :
    let idx := l.findIdx (· = v)
    let head := l.take (idx + 1)
    head.findIdx (· = v) = head.length - 1 := by
  simp only
  have h_idx_lt : l.findIdx (· = v) < l.length := List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_len : (l.take (l.findIdx (· = v) + 1)).length = l.findIdx (· = v) + 1 := by
    rw [List.length_take]; omega
  have h_getElem : l[l.findIdx (· = v)]'h_idx_lt = v := by
    have := @List.findIdx_getElem V (· = v) l h_idx_lt
    simp at this; exact this
  have h_head_getElem : (l.take (l.findIdx (· = v) + 1))[l.findIdx (· = v)]'(by rw [h_len]; omega) = v := by
    rw [List.getElem_take]; exact h_getElem
  have hv_mem_head : v ∈ l.take (l.findIdx (· = v) + 1) := by
    rw [List.mem_iff_getElem]
    exact ⟨l.findIdx (· = v), by rw [h_len]; omega, h_head_getElem⟩
  have h_head_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hv_mem_head, by simp⟩
  have h_le : (l.take (l.findIdx (· = v) + 1)).findIdx (· = v) ≤ l.findIdx (· = v) := by
    by_contra h_neg; push Not at h_neg; omega
  have h_ge : l.findIdx (· = v) ≤ (l.take (l.findIdx (· = v) + 1)).findIdx (· = v) := by
    by_contra h_neg; push Not at h_neg
    have h_found : (l.take (l.findIdx (· = v) + 1))[(l.take (l.findIdx (· = v) + 1)).findIdx (· = v)]'h_head_lt = v := by
      have := @List.findIdx_getElem V (· = v) (l.take (l.findIdx (· = v) + 1)) h_head_lt
      simp only [decide_eq_true_eq] at this; exact this
    have h_in_l : l[(l.take (l.findIdx (· = v) + 1)).findIdx (· = v)]'(by omega) = v := by
      have : (l.take (l.findIdx (· = v) + 1))[(l.take (l.findIdx (· = v) + 1)).findIdx (· = v)]'h_head_lt = 
             l[(l.take (l.findIdx (· = v) + 1)).findIdx (· = v)]'(by omega) := by
        rw [List.getElem_take]
      rw [← this]; exact h_found
    have h_not_before : ∀ j, (hj : j < l.findIdx (· = v)) → ¬(l[j]'(Nat.lt_trans hj h_idx_lt) = v) := by
      intro j hj
      have := List.not_of_lt_findIdx hj
      simp at this; exact this
    exact h_not_before _ h_neg h_in_l
  have h_eq := le_antisymm h_le h_ge
  rw [h_eq, h_len]; omega

-- Key lemma: splitAt on concatenated path gives back original components
private lemma splitAt_concat_vertices_eq (head_verts tail_verts : List V) (v : V)
    (hhead_ne : head_verts ≠ [])
    (htail_ne : tail_verts ≠ [])
    (hhead_last : head_verts.getLast hhead_ne = v)
    (htail_first : tail_verts.head htail_ne = v)
    (hhead_findIdx : head_verts.findIdx (· = v) = head_verts.length - 1) :
    let combined := head_verts ++ tail_verts.tail
    let idx := combined.findIdx (· = v)
    (combined.take (idx + 1), combined.drop idx) = (head_verts, tail_verts) := by
  simp only
  have hv_mem : v ∈ head_verts := by rw [← hhead_last]; exact List.getLast_mem hhead_ne
  have h_findIdx : (head_verts ++ tail_verts.tail).findIdx (· = v) = head_verts.length - 1 := by
    rw [List.findIdx_append]
    have h_lt : head_verts.findIdx (· = v) < head_verts.length := by
      exact List.findIdx_lt_length_of_exists ⟨v, hv_mem, by simp⟩
    simp only [h_lt, ↓reduceIte]
    exact hhead_findIdx
  rw [h_findIdx]
  have h_len : head_verts.length - 1 + 1 = head_verts.length := by
    have := List.length_pos_of_ne_nil hhead_ne; omega
  have h_take : (head_verts ++ tail_verts.tail).take head_verts.length = head_verts := List.take_left
  have hhead_len : 0 < head_verts.length := List.length_pos_of_ne_nil hhead_ne
  have h_drop : (head_verts ++ tail_verts.tail).drop (head_verts.length - 1) = tail_verts := by
    rw [List.drop_append]
    have h_drop_head : head_verts.drop (head_verts.length - 1) = [head_verts.getLast hhead_ne] := by
      rw [List.drop_eq_getElem_cons (by omega)]
      simp only [List.getLast_eq_getElem]
      congr 1
      rw [List.drop_eq_nil_of_le (by omega)]
    rw [h_drop_head]
    have h_sub : head_verts.length - 1 - head_verts.length = 0 := by omega
    simp only [h_sub, List.drop_zero, List.singleton_append]
    rw [hhead_last, ← htail_first]
    exact List.cons_head_tail htail_ne
  rw [h_len, h_take, h_drop]

-- Helper lemma: splitAt vertices for the head
private lemma splitAt_fst_vertices {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : 
    (p.splitAt v hv).1.vertices = p.vertices.take (p.vertices.findIdx (· = v) + 1) := by
  unfold SimpleDigraph.Path.splitAt
  simp only

-- Helper lemma: splitAt vertices for the tail
private lemma splitAt_snd_vertices {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : 
    (p.splitAt v hv).2.vertices = p.vertices.drop (p.vertices.findIdx (· = v)) := by
  unfold SimpleDigraph.Path.splitAt
  simp only

-- Helper lemma: concat vertices
omit [DecidableEq V] in
private lemma concat_vertices {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : (p.concat q hpq).vertices = p.vertices ++ q.vertices.tail := by
  unfold SimpleDigraph.Path.concat
  simp only

-- Helper lemma: paths are determined by their vertices
omit [DecidableEq V] in
private lemma path_ext {D : SimpleDigraph V} (p q : SimpleDigraph.Path D)
    (h : p.vertices = q.vertices) : p = q := by
  cases p; cases q
  simp only [SimpleDigraph.Path.mk.injEq] at h ⊢
  exact h

-- Helper lemma: exchangeTails first component vertices
private lemma exchangeTails_fst_vertices {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).1.vertices = 
    (p.splitAt v hv_p).1.vertices ++ (q.splitAt v hv_q).2.vertices.tail := by
  unfold exchangeTails
  simp only [concat_vertices]

-- Helper lemma: exchangeTails second component vertices  
private lemma exchangeTails_snd_vertices {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).2.vertices = 
    (q.splitAt v hv_q).1.vertices ++ (p.splitAt v hv_p).2.vertices.tail := by
  unfold exchangeTails
  simp only [concat_vertices]

-- concat of splitAt components gives back original
private lemma concat_splitAt_vertices_eq {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) :
    (p.splitAt v hv).1.vertices ++ (p.splitAt v hv).2.vertices.tail = p.vertices := by
  rw [splitAt_fst_vertices, splitAt_snd_vertices]
  have h1 : (p.vertices.drop (p.vertices.findIdx (· = v))).tail = 
            p.vertices.drop (p.vertices.findIdx (· = v) + 1) := List.tail_drop
  simp only [h1]
  exact List.take_append_drop _ _

lemma exchangeTails_involutive {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    let p' := (exchangeTails p q v hv_p hv_q).1
    let q' := (exchangeTails p q v hv_p hv_q).2
    let hv_p' : v ∈ p'.vertices := exchangeTails_fst_mem_v p q v hv_p hv_q
    let hv_q' : v ∈ q'.vertices := exchangeTails_snd_mem_v p q v hv_p hv_q
    exchangeTails p' q' v hv_p' hv_q' = (p, q) := by
  simp only
  -- Define the components
  set head_p := (p.splitAt v hv_p).1 with h_head_p_def
  set tail_p := (p.splitAt v hv_p).2 with h_tail_p_def
  set head_q := (q.splitAt v hv_q).1 with h_head_q_def
  set tail_q := (q.splitAt v hv_q).2 with h_tail_q_def
  -- Key facts about the splitAt components
  have h_head_p_last : head_p.vertices.getLast head_p.nonempty = v := 
    SimpleDigraph.Path.splitAt_head_finish p v hv_p
  have h_tail_p_first : tail_p.vertices.head tail_p.nonempty = v := 
    SimpleDigraph.Path.splitAt_tail_start p v hv_p
  have h_head_q_last : head_q.vertices.getLast head_q.nonempty = v := 
    SimpleDigraph.Path.splitAt_head_finish q v hv_q
  have h_tail_q_first : tail_q.vertices.head tail_q.nonempty = v := 
    SimpleDigraph.Path.splitAt_tail_start q v hv_q
  -- The head findIdx properties
  have h_head_p_findIdx : head_p.vertices.findIdx (· = v) = head_p.vertices.length - 1 := by
    rw [splitAt_fst_vertices]
    exact splitAt_head_findIdx_eq p.vertices v hv_p
  have h_head_q_findIdx : head_q.vertices.findIdx (· = v) = head_q.vertices.length - 1 := by
    rw [splitAt_fst_vertices]
    exact splitAt_head_findIdx_eq q.vertices v hv_q
  -- p' = head_p ++ tail_q.tail, q' = head_q ++ tail_p.tail
  have h_p'_verts : (exchangeTails p q v hv_p hv_q).1.vertices = 
                    head_p.vertices ++ tail_q.vertices.tail := exchangeTails_fst_vertices p q v hv_p hv_q
  have h_q'_verts : (exchangeTails p q v hv_p hv_q).2.vertices = 
                    head_q.vertices ++ tail_p.vertices.tail := exchangeTails_snd_vertices p q v hv_p hv_q
  -- Use splitAt_concat_vertices_eq to show splitAt on p' gives (head_p, tail_q)
  have h_split_p' := splitAt_concat_vertices_eq 
    head_p.vertices tail_q.vertices v 
    head_p.nonempty tail_q.nonempty 
    h_head_p_last h_tail_q_first h_head_p_findIdx
  have h_split_q' := splitAt_concat_vertices_eq 
    head_q.vertices tail_p.vertices v 
    head_q.nonempty tail_p.nonempty 
    h_head_q_last h_tail_p_first h_head_q_findIdx
  -- Extract the components from the split
  have h_p'_split_fst : ((exchangeTails p q v hv_p hv_q).1.splitAt v 
      (exchangeTails_fst_mem_v p q v hv_p hv_q)).1.vertices = head_p.vertices := by
    rw [splitAt_fst_vertices, h_p'_verts]
    have := h_split_p'
    simp only at this
    exact congr_arg Prod.fst this
  have h_p'_split_snd : ((exchangeTails p q v hv_p hv_q).1.splitAt v 
      (exchangeTails_fst_mem_v p q v hv_p hv_q)).2.vertices = tail_q.vertices := by
    rw [splitAt_snd_vertices, h_p'_verts]
    have := h_split_p'
    simp only at this
    exact congr_arg Prod.snd this
  have h_q'_split_fst : ((exchangeTails p q v hv_p hv_q).2.splitAt v 
      (exchangeTails_snd_mem_v p q v hv_p hv_q)).1.vertices = head_q.vertices := by
    rw [splitAt_fst_vertices, h_q'_verts]
    have := h_split_q'
    simp only at this
    exact congr_arg Prod.fst this
  have h_q'_split_snd : ((exchangeTails p q v hv_p hv_q).2.splitAt v 
      (exchangeTails_snd_mem_v p q v hv_p hv_q)).2.vertices = tail_p.vertices := by
    rw [splitAt_snd_vertices, h_q'_verts]
    have := h_split_q'
    simp only at this
    exact congr_arg Prod.snd this
  -- Now show the result equals (p, q)
  apply Prod.ext
  · -- First component
    apply path_ext
    rw [exchangeTails_fst_vertices, h_p'_split_fst, h_q'_split_snd]
    exact concat_splitAt_vertices_eq p v hv_p
  · -- Second component
    apply path_ext
    rw [exchangeTails_snd_vertices, h_q'_split_fst, h_p'_split_snd]
    exact concat_splitAt_vertices_eq q v hv_q

/-- The head of path p (vertices before v) is preserved after exchangeTails.
    This is the key lemma for proving that the canonical selection is invariant. -/
lemma exchangeTails_head_eq {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    let p' := (exchangeTails p q v hv_p hv_q).1
    let hv_p' := exchangeTails_fst_mem_v p q v hv_p hv_q
    (p'.splitAt v hv_p').1.vertices = (p.splitAt v hv_p).1.vertices := by
  simp only
  rw [splitAt_fst_vertices, splitAt_fst_vertices]
  rw [exchangeTails_fst_vertices]
  -- The head of p' = head_p ++ tail_q.tail is just head_p (up to v)
  -- We need: (head_p ++ tail_q.tail).take (findIdx (· = v) + 1) = head_p.take (findIdx (· = v) + 1)
  have h_head_p := splitAt_fst_vertices p v hv_p
  have h_tail_q := splitAt_snd_vertices q v hv_q
  -- head_p.vertices ends with v, so findIdx in the concatenation finds v at the same position
  have h_head_p_last : (p.splitAt v hv_p).1.vertices.getLast (p.splitAt v hv_p).1.nonempty = v := 
    SimpleDigraph.Path.splitAt_head_finish p v hv_p
  have h_findIdx_head : (p.splitAt v hv_p).1.vertices.findIdx (· = v) = 
      (p.splitAt v hv_p).1.vertices.length - 1 := splitAt_head_findIdx_eq p.vertices v hv_p
  -- In the concatenation, findIdx finds v at the same position (end of head_p)
  have h_concat := splitAt_concat_vertices_eq 
    (p.splitAt v hv_p).1.vertices (q.splitAt v hv_q).2.vertices v
    (p.splitAt v hv_p).1.nonempty (q.splitAt v hv_q).2.nonempty
    h_head_p_last (SimpleDigraph.Path.splitAt_tail_start q v hv_q)
    h_findIdx_head
  simp only at h_concat
  exact congr_arg Prod.fst h_concat

/-- Exchanging tails preserves the total weight.


    **Proof outline:** The key insight is that `pathWeight` is multiplicative over path
    concatenation: if p = p₁ ++ p₂ (concatenation at a shared vertex), then
    w(p) = w(p₁) * w(p₂).

    When we exchange tails at vertex v:
    - p has weight w(p_head) * w(p_tail) where p_head ends at v and p_tail starts at v
    - q has weight w(q_head) * w(q_tail) where q_head ends at v and q_tail starts at v
    - p' = p_head ++ q_tail has weight w(p_head) * w(q_tail)
    - q' = q_head ++ p_tail has weight w(q_head) * w(p_tail)

    Thus: w(p) * w(q) = w(p_head) * w(p_tail) * w(q_head) * w(q_tail)
                      = w(p_head) * w(q_tail) * w(q_head) * w(p_tail)  (by commutativity)
                      = w(p') * w(q')

    **Status:** Now that `exchangeTails` is defined, the proof follows from
    multiplicativity of `pathWeight` and commutativity of multiplication in K.
    The proof requires showing pathWeight is multiplicative over path concatenation. -/
theorem exchangeTails_weight {D : SimpleDigraph V}
    (w : ArcWeight D K) (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    pathWeight w p * pathWeight w q =
      pathWeight w (exchangeTails p q v hv_p hv_q).1 *
      pathWeight w (exchangeTails p q v hv_p hv_q).2 := by
  -- Split both paths at v
  let sp_p := p.splitAt v hv_p
  let sp_q := q.splitAt v hv_q
  let head_p := sp_p.1
  let tail_p := sp_p.2
  let head_q := sp_q.1
  let tail_q := sp_q.2
  -- By pathWeight_splitAt:
  -- pathWeight p = pathWeight head_p * pathWeight tail_p
  -- pathWeight q = pathWeight head_q * pathWeight tail_q
  have hp : pathWeight w p = pathWeight w head_p * pathWeight w tail_p := pathWeight_splitAt w p v hv_p
  have hq : pathWeight w q = pathWeight w head_q * pathWeight w tail_q := pathWeight_splitAt w q v hv_q
  -- exchangeTails gives us (head_p ++ tail_q, head_q ++ tail_p)
  -- By pathWeight_concat:
  -- pathWeight (head_p ++ tail_q) = pathWeight head_p * pathWeight tail_q
  -- pathWeight (head_q ++ tail_p) = pathWeight head_q * pathWeight tail_p
  unfold exchangeTails
  simp only
  have h1 : head_p.finish = tail_q.start := by
    rw [SimpleDigraph.Path.splitAt_head_finish, SimpleDigraph.Path.splitAt_tail_start]
  have h2 : head_q.finish = tail_p.start := by
    rw [SimpleDigraph.Path.splitAt_head_finish, SimpleDigraph.Path.splitAt_tail_start]
  rw [pathWeight_concat w head_p tail_q h1, pathWeight_concat w head_q tail_p h2]
  rw [hp, hq]
  ring

/-!
### Deterministic Intersection Data Selection

The sign-reversing involution requires selecting intersection data (i, j, v) deterministically
so that applying the involution twice returns the original path tuple. The algorithm from
the LaTeX source is:
1. Pick the smallest i such that path i contains a crowded point
2. Pick the first crowded point v on path i (by position in the path)
3. Pick the largest j such that v is on path j

This selection is preserved under the involution because:
- The heads of paths i and j (before v) are unchanged
- So v is still the first crowded point on path i
- And j is still the largest index containing v
-/

/-- The set of path indices that have a crowded vertex (shared with another path) -/
def PathTuple.crowdedPathIndices {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) : Finset (Fin k) :=
  Finset.univ.filter fun i =>
    ∃ j : Fin k, i ≠ j ∧ ((pt.paths i).vertices.toFinset ∩ (pt.paths j).vertices.toFinset).Nonempty

/-- The set of crowded vertices on a specific path -/
def PathTuple.crowdedVerticesOnPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (i : Fin k) : Finset V :=
  (pt.paths i).vertices.toFinset.filter fun v =>
    ∃ j : Fin k, i ≠ j ∧ v ∈ (pt.paths j).vertices

/-- The set of path indices that contain a given vertex -/
def PathTuple.pathIndicesContaining {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (v : V) : Finset (Fin k) :=
  Finset.univ.filter fun i => v ∈ (pt.paths i).vertices

/-- The index of the first crowded vertex on a path (by position) -/
def PathTuple.firstCrowdedIndexOnPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (i : Fin k) : ℕ :=
  (pt.paths i).vertices.findIdx fun v => v ∈ pt.crowdedVerticesOnPath i

/-- An intersecting path tuple has nonempty crowdedPathIndices -/
lemma PathTuple.isIntersecting_iff_crowdedPathIndices_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt.isIntersecting ↔ pt.crowdedPathIndices.Nonempty := by
  rw [PathTuple.isIntersecting_iff_exists_crowded]
  constructor
  · intro ⟨v, i, j, hij, hvi, hvj⟩
    use i
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij, v
    simp only [Finset.mem_inter, List.mem_toFinset]
    exact ⟨hvi, hvj⟩
  · intro ⟨i, hi⟩
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨j, hij, v, hv⟩ := hi
    simp only [Finset.mem_inter, List.mem_toFinset] at hv
    exact ⟨v, i, j, hij, hv.1, hv.2⟩

/-- Key lemma: if i is the smallest crowded path index and v is a crowded vertex on path i,
    then all other paths containing v have index > i -/
lemma PathTuple.crowded_vertex_other_paths_gt {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi_min : ∀ i' ∈ pt.crowdedPathIndices, i ≤ i')
    (v : V) (hv : v ∈ pt.crowdedVerticesOnPath i)
    (j : Fin k) (hj : j ∈ pt.pathIndicesContaining v) (hjne : j ≠ i) :
    i < j := by
  simp only [pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
  obtain ⟨hvi, j', hij', hvj'⟩ := hv
  by_contra h
  push Not at h
  have hj_lt : j < i := lt_of_le_of_ne h hjne
  have hj_crowded : j ∈ pt.crowdedPathIndices := by
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use i
    constructor
    · exact hjne
    · use v
      simp only [Finset.mem_inter, List.mem_toFinset]
      exact ⟨hj, hvi⟩
  have hi_le_j := hi_min j hj_crowded
  omega

/-!
### Canonical Intersection Data Selection

The sign-reversing involution requires selecting intersection data (i, j, v) canonically
so that applying the involution twice returns the original path tuple. The algorithm is:
1. i = the smallest path index that contains a crowded point
2. v = the first crowded point on path i (by position in the vertex list)
3. j = the largest path index that contains v

This selection is preserved under the involution because:
- The heads of paths i and j (before v) are unchanged by exchangeTails
- So v is still the first crowded point on path i
- And j is still the largest index containing v
-/

/-- Get the smallest crowded path index. -/
def PathTuple.minCrowdedPathIndex {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : Fin k :=
  pt.crowdedPathIndices.min' (pt.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip)

/-- The minimum crowded path index is in crowdedPathIndices -/
lemma PathTuple.minCrowdedPathIndex_mem {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.minCrowdedPathIndex hip ∈ pt.crowdedPathIndices :=
  Finset.min'_mem _ _

/-- The minimum crowded path index is minimal -/
lemma PathTuple.minCrowdedPathIndex_le {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    pt.minCrowdedPathIndex hip ≤ i :=
  Finset.min'_le _ _ hi

/-- The crowded vertices on the minimum path are nonempty -/
lemma PathTuple.crowdedVerticesOnPath_minCrowded_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    (pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip)).Nonempty := by
  have hi_mem := pt.minCrowdedPathIndex_mem hip
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi_mem
  obtain ⟨j, hij, v, hv⟩ := hi_mem
  simp only [Finset.mem_inter, List.mem_toFinset] at hv
  use v
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
  exact ⟨hv.1, j, hij, hv.2⟩

/-- Get the first crowded vertex on the minimum crowded path.
    This uses List.find? to get the first vertex in the path that is crowded. -/
noncomputable def PathTuple.firstCrowdedVertex {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : V :=
  let i := pt.minCrowdedPathIndex hip
  let crowded := pt.crowdedVerticesOnPath i
  -- Find the first vertex in the path that is crowded
  ((pt.paths i).vertices.find? (fun v => v ∈ crowded)).get (by
    -- Prove that find? returns some
    have hne := pt.crowdedVerticesOnPath_minCrowded_nonempty hip
    obtain ⟨v, hv⟩ := hne
    apply List.find?_isSome.mpr
    use v
    constructor
    · -- v is in the path
      simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
      exact hv.1
    · -- v ∈ crowded
      simp only [decide_eq_true_eq]
      exact hv)

/-- The first crowded vertex is in the minimum crowded path -/
lemma PathTuple.firstCrowdedVertex_mem_path {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.firstCrowdedVertex hip ∈ (pt.paths (pt.minCrowdedPathIndex hip)).vertices := by
  unfold firstCrowdedVertex
  have h := Option.get_mem (by
    have hne := pt.crowdedVerticesOnPath_minCrowded_nonempty hip
    obtain ⟨v, hv⟩ := hne
    simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
    apply List.find?_isSome.mpr
    use v, hv.1
    simp only [decide_eq_true_eq, crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
    exact hv : ((pt.paths (pt.minCrowdedPathIndex hip)).vertices.find? 
      (fun v => v ∈ pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip))).isSome)
  exact List.mem_of_find?_eq_some h

/-- The first crowded vertex is in the crowdedVerticesOnPath set -/
lemma PathTuple.firstCrowdedVertex_mem_crowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.firstCrowdedVertex hip ∈ pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip) := by
  unfold firstCrowdedVertex
  have hne := pt.crowdedVerticesOnPath_minCrowded_nonempty hip
  obtain ⟨v, hv⟩ := hne
  have h_isSome : ((pt.paths (pt.minCrowdedPathIndex hip)).vertices.find? 
      (fun v => v ∈ pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip))).isSome := by
    apply List.find?_isSome.mpr
    use v
    constructor
    · simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
      exact hv.1
    · simp only [decide_eq_true_eq]
      exact hv
  have h := Option.get_mem h_isSome
  have hprop := List.find?_some h
  simp only [decide_eq_true_eq] at hprop
  exact hprop

/-- The first crowded vertex is crowded (shared with another path) -/
lemma PathTuple.firstCrowdedVertex_is_crowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    ∃ j : Fin k, pt.minCrowdedPathIndex hip ≠ j ∧ 
      pt.firstCrowdedVertex hip ∈ (pt.paths j).vertices := by
  have hcrowded := pt.firstCrowdedVertex_mem_crowded hip
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hcrowded
  exact hcrowded.2

/-- The set of path indices containing the first crowded vertex (excluding the minimum) -/
noncomputable def PathTuple.otherPathsContainingFirstCrowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : Finset (Fin k) :=
  (pt.pathIndicesContaining (pt.firstCrowdedVertex hip)).filter 
    (fun j => j ≠ pt.minCrowdedPathIndex hip)

/-- The set of other paths containing the first crowded vertex is nonempty -/
lemma PathTuple.otherPathsContainingFirstCrowded_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    (pt.otherPathsContainingFirstCrowded hip).Nonempty := by
  obtain ⟨j, hij, hvj⟩ := pt.firstCrowdedVertex_is_crowded hip
  use j
  simp only [otherPathsContainingFirstCrowded, Finset.mem_filter, pathIndicesContaining,
    Finset.mem_univ, true_and]
  exact ⟨hvj, hij.symm⟩

/-- Get the largest path index containing the first crowded vertex (other than the minimum) -/
noncomputable def PathTuple.maxOtherPathIndex {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : Fin k :=
  (pt.otherPathsContainingFirstCrowded hip).max' (pt.otherPathsContainingFirstCrowded_nonempty hip)

/-- The max other path index is different from the min crowded path index -/
lemma PathTuple.maxOtherPathIndex_ne_min {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.maxOtherPathIndex hip ≠ pt.minCrowdedPathIndex hip := by
  have hmem := Finset.max'_mem _ (pt.otherPathsContainingFirstCrowded_nonempty hip)
  simp only [otherPathsContainingFirstCrowded, Finset.mem_filter] at hmem
  exact hmem.2

/-- The first crowded vertex is in the max other path -/
lemma PathTuple.firstCrowdedVertex_mem_maxOtherPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.firstCrowdedVertex hip ∈ (pt.paths (pt.maxOtherPathIndex hip)).vertices := by
  have hmem := Finset.max'_mem _ (pt.otherPathsContainingFirstCrowded_nonempty hip)
  simp only [otherPathsContainingFirstCrowded, Finset.mem_filter, pathIndicesContaining,
    Finset.mem_univ, true_and] at hmem
  exact hmem.1

/-- Helper function to extract intersection indices from an intersecting path tuple.
    Returns a pair (i, j) with i ≠ j such that paths i and j intersect. -/
noncomputable def getIntersectionIndices {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    { p : Fin k × Fin k // p.1 ≠ p.2 } :=
  Classical.choice (by
    -- Convert isIntersecting to existential form using isIntersecting_iff_exists_crowded
    rw [PathTuple.isIntersecting_iff_exists_crowded] at hip
    obtain ⟨v, i, j, hij, _, _⟩ := hip
    exact ⟨⟨(i, j), hij⟩⟩)

/-- Helper function to extract full intersection data from an intersecting path tuple.
    Returns (i, j, v, hvi, hvj) where i ≠ j and v is on both paths i and j. -/
noncomputable def getIntersectionData {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    { data : (i : Fin k) × (j : Fin k) × { v : V // v ∈ (pt.paths i).vertices ∧ v ∈ (pt.paths j).vertices } // 
      data.1 ≠ data.2.1 } :=
  Classical.choice (by
    rw [PathTuple.isIntersecting_iff_exists_crowded] at hip
    obtain ⟨v, i, j, hij, hvi, hvj⟩ := hip
    exact ⟨⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩⟩)

/-!
### Canonical (Deterministic) Intersection Data Selection

To prove that signReversing is an involution, we need to select intersection data
(i, j, v) deterministically so that the same selection is made before and after
applying the involution.

The canonical selection algorithm:
1. i = smallest index in crowdedPathIndices (using Finset.min')
2. v = first crowded vertex on path i (by position in the path)
3. j = largest index in pathIndicesContaining v, excluding i (using Finset.max')

This selection is preserved under exchangeTails because:
- The head of path i (vertices before v) is unchanged
- So v is still the first crowded vertex on path i
- And j is still the largest index containing v
-/

/-- A crowded path index has at least 2 paths containing some crowded vertex -/
lemma PathTuple.crowdedPathIndex_pathIndicesContaining_card {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices)
    (v : V) (hv : v ∈ pt.crowdedVerticesOnPath i) :
    1 < (pt.pathIndicesContaining v).card := by
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
  obtain ⟨hvi, j, hij, hvj⟩ := hv
  have hi_mem : i ∈ pt.pathIndicesContaining v := by
    simp only [pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hvi
  have hj_mem : j ∈ pt.pathIndicesContaining v := by
    simp only [pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hvj
  have hne : i ≠ j := hij
  calc (pt.pathIndicesContaining v).card 
      ≥ ({i, j} : Finset (Fin k)).card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hi_mem
        · exact hj_mem)
    _ = 2 := by simp [hne]
    _ > 1 := by omega

/-- If i is a crowded path index, the set of other path indices containing a crowded vertex on i
    is nonempty -/
lemma PathTuple.pathIndicesContaining_sdiff_singleton_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices)
    (v : V) (hv : v ∈ pt.crowdedVerticesOnPath i) :
    (pt.pathIndicesContaining v \ {i}).Nonempty := by
  have hcard := pt.crowdedPathIndex_pathIndicesContaining_card i hi v hv
  rw [Finset.sdiff_nonempty]
  intro h
  have hsub : pt.pathIndicesContaining v ⊆ {i} := h
  have : (pt.pathIndicesContaining v).card ≤ ({i} : Finset (Fin k)).card := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at this
  omega

/-- A crowded path index has nonempty crowdedVerticesOnPath -/
lemma PathTuple.crowdedPathIndex_crowdedVerticesOnPath_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    (pt.crowdedVerticesOnPath i).Nonempty := by
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨j, hij, v, hv⟩ := hi
  simp only [Finset.mem_inter, List.mem_toFinset] at hv
  use v
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
  exact ⟨hv.1, j, hij, hv.2⟩

/-- The first crowded vertex on path i (when i is a crowded path index) exists in the path -/
lemma PathTuple.firstCrowdedIndexOnPath_lt_length {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    pt.firstCrowdedIndexOnPath i < (pt.paths i).vertices.length := by
  have hne := pt.crowdedPathIndex_crowdedVerticesOnPath_nonempty i hi
  obtain ⟨v, hv⟩ := hne
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
  unfold firstCrowdedIndexOnPath
  apply List.findIdx_lt_length_of_exists
  use v, hv.1
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq]
  exact hv

/-- The vertex at firstCrowdedIndexOnPath is in crowdedVerticesOnPath -/
lemma PathTuple.firstCrowdedVertex_mem_crowdedVerticesOnPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    let idx := pt.firstCrowdedIndexOnPath i
    let h := pt.firstCrowdedIndexOnPath_lt_length i hi
    (pt.paths i).vertices.get ⟨idx, h⟩ ∈ pt.crowdedVerticesOnPath i := by
  simp only
  unfold firstCrowdedIndexOnPath
  have h_lt := pt.firstCrowdedIndexOnPath_lt_length i hi
  unfold firstCrowdedIndexOnPath at h_lt
  have h_findIdx := @List.findIdx_getElem _ (fun v => v ∈ pt.crowdedVerticesOnPath i) 
    (pt.paths i).vertices h_lt
  simp only [List.get_eq_getElem]
  simp at h_findIdx
  exact h_findIdx

/-- Canonical intersection data: deterministically selects (i, j, v) for an intersecting path tuple.
    - i = smallest crowded path index
    - v = first crowded vertex on path i
    - j = largest path index containing v (other than i) -/
noncomputable def getCanonicalIntersectionData {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    { data : (i : Fin k) × (j : Fin k) × { v : V // v ∈ (pt.paths i).vertices ∧ v ∈ (pt.paths j).vertices } // 
      data.1 ≠ data.2.1 } :=
  let hne := pt.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip
  let i := pt.crowdedPathIndices.min' hne
  let hi : i ∈ pt.crowdedPathIndices := Finset.min'_mem _ hne
  let idx := pt.firstCrowdedIndexOnPath i
  let h_idx := pt.firstCrowdedIndexOnPath_lt_length i hi
  let v := (pt.paths i).vertices.get ⟨idx, h_idx⟩
  let hv_crowded := pt.firstCrowdedVertex_mem_crowdedVerticesOnPath i hi
    let hv_i : v ∈ (pt.paths i).vertices := by
      simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv_crowded
      exact hv_crowded.1
    let h_sdiff_ne := pt.pathIndicesContaining_sdiff_singleton_nonempty i hi v hv_crowded
    let j := (pt.pathIndicesContaining v \ {i}).max' h_sdiff_ne
    let hj_mem : j ∈ pt.pathIndicesContaining v \ {i} := Finset.max'_mem _ h_sdiff_ne
    let hj_ne_i : j ≠ i := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj_mem
      exact hj_mem.2
    let hv_j : v ∈ (pt.paths j).vertices := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton, PathTuple.pathIndicesContaining, 
                 Finset.mem_filter, Finset.mem_univ, true_and] at hj_mem
      exact hj_mem.1
  ⟨⟨i, j, ⟨v, hv_i, hv_j⟩⟩, hj_ne_i.symm⟩


/-- The sign-reversing involution on intersecting path tuples.
    For an ipat (σ, 𝐩), we:
    1. Find the smallest i such that p_i contains a crowded point
    2. Find the first crowded point v on p_i
    3. Find the largest j such that v is on p_j
    4. Exchange tails of p_i and p_j at v
    5. Compose σ with the transposition t_{i,j}
    This gives (σ ∘ t_{i,j}, 𝐩') which is still an ipat.

    **Implementation note:** The permutation component is `sp.1 * Equiv.swap i j` where
    i and j are the intersection indices. The path tuple component uses `exchangeTails`
    to swap the tails of paths i and j at the crowded vertex v. -/
noncomputable def signReversing {D : SimpleDigraph V} (_hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) : pathTupleWithPerm (D := D) A B :=
  let ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := getCanonicalIntersectionData sp.2 hip
  let newPaths : Fin k → SimpleDigraph.Path D := fun l =>
    if h : l = i then (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1
    else if h' : l = j then (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2
    else sp.2.paths l
  have h_starts : ∀ l, (newPaths l).start = A l := by
    intro l
    simp only [newPaths]
    split_ifs with h h'
    · rw [h, exchangeTails_fst_start, sp.2.starts]
    · rw [h', exchangeTails_snd_start, sp.2.starts]
    · exact sp.2.starts l
  have h_finishes : ∀ l, (newPaths l).finish = (permuteKVertex (sp.1 * Equiv.swap i j) B) l := by
    intro l
    simp only [newPaths, permuteKVertex, Equiv.Perm.coe_mul, Function.comp_apply]
    split_ifs with h h'
    · -- l = i case
      rw [h, exchangeTails_fst_finish, sp.2.finishes]
      simp only [permuteKVertex, Equiv.swap_apply_left]
    · -- l = j case  
      rw [h', exchangeTails_snd_finish, sp.2.finishes]
      simp only [permuteKVertex, Equiv.swap_apply_right]
    · -- l ≠ i, l ≠ j case
      rw [sp.2.finishes]
      simp only [permuteKVertex]
      congr 1
      rw [Equiv.swap_apply_of_ne_of_ne h h']
    ⟨sp.1 * Equiv.swap i j, ⟨newPaths, h_starts, h_finishes⟩⟩

/-- The signReversing map preserves the intersecting property.
    The crowded point v at indices i and j is preserved in the exchanged paths. -/
lemma signReversing_isIntersecting {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    (signReversing hac sp hip).2.isIntersecting := by
  -- Extract the intersection data used by signReversing
  generalize h_data : getCanonicalIntersectionData sp.2 hip = data
  obtain ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := data
  -- Show v is a crowded point in the new paths at indices i and j
  rw [PathTuple.isIntersecting_iff_exists_crowded]
  use v
  unfold PathTuple.isCrowded
  use i, j, hij
  constructor
  · -- v is in path i of sp'
    show v ∈ ((signReversing hac sp hip).2.paths i).vertices
    conv_lhs => unfold signReversing; rw [h_data]; simp only [dite_true]
    exact exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  · -- v is in path j of sp'
    show v ∈ ((signReversing hac sp hip).2.paths j).vertices
    conv_lhs => unfold signReversing; rw [h_data]; simp only [hij.symm, dite_false, dite_true]
    exact exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj

/-- Helper: The paths of sp' at index i is the first component of exchangeTails -/
private lemma signReversing_path_i {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 := by
  conv_lhs => unfold signReversing; rw [h_data]; simp only [dite_true]

/-- Helper: The paths of sp' at index j is the second component of exchangeTails -/
private lemma signReversing_path_j {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).2.paths j = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 := by
  conv_lhs => unfold signReversing; rw [h_data]; simp only [hij.symm, dite_false, dite_true]

/-- Helper: The paths of sp' at index l ≠ i, j are unchanged -/
private lemma signReversing_path_other {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩)
    (l : Fin k) (hl_ne_i : l ≠ i) (hl_ne_j : l ≠ j) :
    (signReversing hac sp hip).2.paths l = sp.2.paths l := by
  conv_lhs => unfold signReversing; rw [h_data]; simp only [hl_ne_i, dite_false, hl_ne_j]

/-- Helper: The permutation of sp' is sp.1 * swap i j -/
private lemma signReversing_perm_eq {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).1 = sp.1 * Equiv.swap i j := by
  conv_lhs => unfold signReversing; rw [h_data]

/-- Helper: A vertex w is in the head of path p (before v) iff it's in the head of the exchanged path -/
private lemma mem_head_iff_mem_exchangeTails_head {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (v w : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    let p' := (exchangeTails p q v hv_p hv_q).1
    let hv_p' := exchangeTails_fst_mem_v p q v hv_p hv_q
    w ∈ (p.splitAt v hv_p).1.vertices ↔ w ∈ (p'.splitAt v hv_p').1.vertices := by
  simp only
  rw [exchangeTails_head_eq _hac p q v hv_p hv_q]

/-- Helper: exchangeTails preserves head vertices (snd version) -/
private lemma exchangeTails_head_eq_snd {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    let q' := (exchangeTails p q v hv_p hv_q).2
    let hv_q' := exchangeTails_snd_mem_v p q v hv_p hv_q
    (q'.splitAt v hv_q').1.vertices = (q.splitAt v hv_q).1.vertices := by
  simp only
  rw [splitAt_fst_vertices, splitAt_fst_vertices]
  rw [exchangeTails_snd_vertices]
  -- The head of q' = head_q ++ tail_p.tail is just head_q (up to v)
  have h_head_q := splitAt_fst_vertices q v hv_q
  have h_tail_p := splitAt_snd_vertices p v hv_p
  have h_head_q_last : (q.splitAt v hv_q).1.vertices.getLast (q.splitAt v hv_q).1.nonempty = v := 
    SimpleDigraph.Path.splitAt_head_finish q v hv_q
  have h_findIdx_head : (q.splitAt v hv_q).1.vertices.findIdx (· = v) = 
      (q.splitAt v hv_q).1.vertices.length - 1 := splitAt_head_findIdx_eq q.vertices v hv_q
  have h_concat := splitAt_concat_vertices_eq 
    (q.splitAt v hv_q).1.vertices (p.splitAt v hv_p).2.vertices v
    (q.splitAt v hv_q).1.nonempty (p.splitAt v hv_p).2.nonempty
    h_head_q_last (SimpleDigraph.Path.splitAt_tail_start p v hv_p)
    h_findIdx_head
  simp only at h_concat
  exact congr_arg Prod.fst h_concat

/-- Key invariance lemma: pathIndicesContaining v is preserved after signReversing.
    This holds because v is in the HEAD of paths i and j (since v is the first crowded vertex
    on path i, and v is shared with j). After exchangeTails at v, the heads are preserved,
    so v is still on exactly the same paths. -/
private lemma signReversing_pathIndicesContaining_eq {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).2.pathIndicesContaining v = sp.2.pathIndicesContaining v := by
  ext l
  simp only [PathTuple.pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and]
  -- We need to show: v ∈ sp'.paths l ↔ v ∈ sp.paths l
  by_cases hl_i : l = i
  · -- l = i case
    constructor
    · intro hv_sp'
      rw [hl_i]
      exact hvi
    · intro _
      rw [hl_i, signReversing_path_i hac sp hip i j hij v hvi hvj h_data]
      exact exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  · by_cases hl_j : l = j
    · -- l = j case
      constructor
      · intro hv_sp'
        rw [hl_j]
        exact hvj
      · intro _
        rw [hl_j, signReversing_path_j hac sp hip i j hij v hvi hvj h_data]
        exact exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
    · -- l ≠ i, l ≠ j case: path l is unchanged
      rw [signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hl_i hl_j]

/-- Helper lemma: findIdx returns n if the element at position n satisfies the predicate
    and all elements before it do not. -/
private lemma findIdx_eq_of_first {α : Type*} (l : List α) (p : α → Bool)
    (n : ℕ) (hn : n < l.length)
    (h_first : ∀ m : ℕ, ∀ hm : m < n, ¬p (l[m]'(Nat.lt_trans hm hn)))
    (h_p_n : p (l[n]'hn)) :
    l.findIdx p = n := by
  induction l generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => 
      simp only [List.findIdx_cons, List.getElem_cons_zero] at h_p_n ⊢
      simp [h_p_n]
    | succ n' =>
      simp only [List.findIdx_cons]
      have h_not_x : p x = false := by
        have := h_first 0 (Nat.zero_lt_succ n')
        simp at this
        exact this
      simp only [h_not_x, Bool.false_eq_true, ↓reduceIte]
      have hn' : n' < xs.length := by simp at hn; omega
      have h_first' : ∀ m : ℕ, ∀ hm : m < n', ¬p (xs[m]'(Nat.lt_trans hm hn')) := by
        intro m hm
        have hm1 : m + 1 < n' + 1 := by omega
        have := h_first (m + 1) hm1
        simp only [List.getElem_cons_succ] at this
        exact this
      have h_p_n' : p (xs[n']'hn') := by
        have := h_p_n
        simp only [List.getElem_cons_succ] at this
        exact this
      have h_ih := ih n' hn' h_first' h_p_n'
      omega

/-- Helper lemma: vertices before v on path i are not crowded in sp'.
    This is the key insight for proving that firstCrowdedIndexOnPath is preserved.
    
    For any vertex w at index m < idx on path i (where idx is the index of v):
    - w is not crowded in sp (since v at idx is the FIRST crowded vertex)
    - w is only on path i in sp (not on any other path)
    - After exchangeTails, w is still only on path i:
      * w is in the head of path i (preserved by exchangeTails_head_eq)
      * w is not in path j' = head_j ++ tail_i.tail (w not in head_j since not in path j,
        and w not in tail_i.tail since w is before v which starts tail_i)
      * w is not in any other path l (paths l are unchanged for l ≠ i, j)
    - So w is not crowded in sp' -/
private lemma vertices_before_v_not_crowded_in_sp' {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩)
    (w : V) (m : ℕ) (hm_lt_idx : m < (sp.2.paths i).vertices.findIdx (· = v))
    (hm_lt_len : m < (sp.2.paths i).vertices.length)
    (hw_eq : (sp.2.paths i).vertices[m] = w) :
    w ∉ (signReversing hac sp hip).2.crowdedVerticesOnPath i := by
  -- Step 1: Show w is NOT crowded in sp (since v is the first crowded vertex)
  -- This means w is only on path i in sp, not shared with any other path
  
  -- Extract key facts from h_data
  have hi_crowded : i ∈ sp.2.crowdedPathIndices := by
    simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij
    simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
    exact ⟨v, hvi, hvj⟩
  
  -- From h_data, i is the min of crowdedPathIndices
  have hi_min_sp : i = sp.2.crowdedPathIndices.min' 
      (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip) := by
    have h := h_data
    simp only [getCanonicalIntersectionData] at h
    exact (congrArg (fun x => x.val.1) h).symm
  
  -- v is at position firstCrowdedIndexOnPath i
  have h_v_at_idx : (sp.2.paths i).vertices[sp.2.firstCrowdedIndexOnPath i]'
      (sp.2.firstCrowdedIndexOnPath_lt_length i hi_crowded) = v := by
    -- Extract from getCanonicalIntersectionData definition
    have h := h_data
    simp only [getCanonicalIntersectionData] at h
    -- The equality gives us that v is the vertex at firstCrowdedIndexOnPath i
    have h_eq := congrArg (fun x => x.val.2.2.val) h
    simp only [List.get_eq_getElem] at h_eq
    -- h_eq says v = (paths i').vertices[firstCrowdedIndexOnPath i']
    -- where i' = crowdedPathIndices.min'
    -- Since i = i' (from hi_min_sp), we can use simp with hi_min_sp
    simp only [← hi_min_sp] at h_eq
    exact h_eq
  
  -- Since paths have nodup vertices (acyclic), findIdx (· = v) = firstCrowdedIndexOnPath i
  have hnd := SimpleDigraph.Path.vertices_nodup_of_acyclic hac (sp.2.paths i)
  have h_findIdx_eq : (sp.2.paths i).vertices.findIdx (· = v) = sp.2.firstCrowdedIndexOnPath i := by
    have h_idx : (sp.2.paths i).vertices.idxOf v = sp.2.firstCrowdedIndexOnPath i := by
      rw [← h_v_at_idx]
      exact hnd.idxOf_getElem _ _
    simp only [List.idxOf] at h_idx
    exact h_idx
  
  -- Therefore m < firstCrowdedIndexOnPath i
  have hm_lt_first : m < sp.2.firstCrowdedIndexOnPath i := by
    rw [← h_findIdx_eq]
    exact hm_lt_idx
  
  -- So w = (paths i).vertices[m] is NOT in crowdedVerticesOnPath i
  -- (because firstCrowdedIndexOnPath is the FIRST index where the crowded predicate holds)
  have hw_not_crowded_sp : w ∉ sp.2.crowdedVerticesOnPath i := by
    rw [← hw_eq]
    -- The predicate for crowdedVerticesOnPath is decidable
    have h_pred : ¬ ((sp.2.paths i).vertices[m] ∈ sp.2.crowdedVerticesOnPath i) := by
      intro h_in
      -- firstCrowdedIndexOnPath i = findIdx (fun v => v ∈ crowdedVerticesOnPath i)
      unfold PathTuple.firstCrowdedIndexOnPath at hm_lt_first
      -- If (paths i).vertices[m] ∈ crowdedVerticesOnPath i, then findIdx should be ≤ m
      have h_findIdx_le : (sp.2.paths i).vertices.findIdx 
          (fun v => v ∈ sp.2.crowdedVerticesOnPath i) ≤ m := by
        -- If the element at position m satisfies the predicate, then findIdx ≤ m
        have hp : (sp.2.paths i).vertices[m] ∈ sp.2.crowdedVerticesOnPath i := h_in
        -- Use the fact that findIdx returns the first index satisfying the predicate
        -- If element at m satisfies it, findIdx must be ≤ m
        by_contra h_gt
        push Not at h_gt
        -- All elements before findIdx don't satisfy the predicate
        -- In particular, element at m doesn't satisfy it (since m < findIdx)
        have h_not_p : ¬ (fun v => v ∈ sp.2.crowdedVerticesOnPath i) (sp.2.paths i).vertices[m] := by
          have h_lt : m < (sp.2.paths i).vertices.findIdx (fun v => v ∈ sp.2.crowdedVerticesOnPath i) := h_gt
          -- For all n < findIdx, the element at n doesn't satisfy the predicate
          have := List.not_of_lt_findIdx h_lt
          simp only [decide_eq_false_iff_not] at this
          exact this
        exact h_not_p hp
      omega
    exact h_pred
  
  -- This means w is only on path i in sp (not shared with any other path)
  have hw_only_on_i : ∀ l : Fin k, l ≠ i → w ∉ (sp.2.paths l).vertices := by
    intro l hl
    by_contra hw_l
    apply hw_not_crowded_sp
    simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
    constructor
    · rw [← hw_eq]; exact List.getElem_mem hm_lt_len
    · exact ⟨l, hl.symm, hw_l⟩
  
  -- Step 2: Show w is not crowded in sp'
  -- w ∉ sp'.crowdedVerticesOnPath i means:
  -- either w ∉ sp'.paths i, or ∀ l ≠ i, w ∉ sp'.paths l
  -- We'll show the second
  
  simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset, not_and]
  intro hw_in_sp'_i
  push Not
  intro l hl
  
  -- Case analysis on l
  by_cases hl_j : l = j
  · -- l = j: w is not on path j in sp', which is head_j ++ tail_i.tail
    rw [hl_j, signReversing_path_j hac sp hip i j hij v hvi hvj h_data]
    rw [exchangeTails_snd_vertices]
    simp only [List.mem_append, not_or]
    constructor
    · -- w not in head_j (= take part of path j up to v)
      -- Since w is only on path i in sp, w ∉ path j in sp
      have hw_not_j := hw_only_on_i j hij.symm
      intro hw_head_j
      apply hw_not_j
      have := splitAt_fst_vertices (sp.2.paths j) v hvj
      rw [this] at hw_head_j
      exact List.mem_of_mem_take hw_head_j
    · -- w not in tail_i.tail (= drop part of path i after v)
      -- Since w is at position m < findIdx(v), w is before v on path i
      -- So w cannot be in tail_i.tail (which starts after v)
      intro hw_tail_i
      -- w is at position m < findIdx(v), so w is in take (findIdx(v)+1)
      -- But tail starts at findIdx(v), so tail.tail starts at findIdx(v)+1
      -- By nodup, w cannot be in both take(findIdx(v)+1) and drop(findIdx(v)+1)
      have h_w_in_take : w ∈ (sp.2.paths i).vertices.take ((sp.2.paths i).vertices.findIdx (· = v) + 1) := by
        have h_take_len : m < ((sp.2.paths i).vertices.take ((sp.2.paths i).vertices.findIdx (· = v) + 1)).length := by
          simp only [List.length_take]
          omega
        have := List.getElem_mem h_take_len
        simp only [List.getElem_take] at this
        rw [hw_eq] at this
        exact this
      have h_tail_drop : ((sp.2.paths i).splitAt v hvi).2.vertices.tail = 
          (sp.2.paths i).vertices.drop ((sp.2.paths i).vertices.findIdx (· = v) + 1) := by
        rw [splitAt_snd_vertices]
        exact List.tail_drop
      rw [h_tail_drop] at hw_tail_i
      have h_disjoint : ((sp.2.paths i).vertices.take ((sp.2.paths i).vertices.findIdx (· = v) + 1)).Disjoint 
          ((sp.2.paths i).vertices.drop ((sp.2.paths i).vertices.findIdx (· = v) + 1)) := 
        List.disjoint_take_drop hnd (Nat.le_refl _)
      exact List.disjoint_left.mp h_disjoint h_w_in_take hw_tail_i
  · -- l ≠ j (and l ≠ i by hl)
    -- Path l is unchanged in sp'
    have h_path_l_eq : (signReversing hac sp hip).2.paths l = sp.2.paths l := 
      signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hl.symm hl_j
    rw [h_path_l_eq]
    exact hw_only_on_i l hl.symm

/-- Key invariance lemma: The canonical selection returns the same (i, j, v) for sp' as for sp.
    This is the heart of the involutive proof. -/
lemma signReversing_canonical_eq {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩)
    (hip' : (signReversing hac sp hip).2.isIntersecting) :
    ∃ hvi' : v ∈ ((signReversing hac sp hip).2.paths i).vertices,
    ∃ hvj' : v ∈ ((signReversing hac sp hip).2.paths j).vertices,
    getCanonicalIntersectionData (signReversing hac sp hip).2 hip' = ⟨⟨i, j, ⟨v, hvi', hvj'⟩⟩, hij⟩ := by
  -- The membership facts for v in sp'
  have hvi' : v ∈ ((signReversing hac sp hip).2.paths i).vertices := by
    rw [signReversing_path_i hac sp hip i j hij v hvi hvj h_data]
    exact exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  have hvj' : v ∈ ((signReversing hac sp hip).2.paths j).vertices := by
    rw [signReversing_path_j hac sp hip i j hij v hvi hvj h_data]
    exact exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  use hvi', hvj'
  
  -- We need to show that getCanonicalIntersectionData returns the same (i, j, v)
  -- This requires showing:
  -- 1. i = sp'.2.crowdedPathIndices.min'
  -- 2. v = sp'.2.paths i at firstCrowdedIndexOnPath
  -- 3. j = (sp'.2.pathIndicesContaining v \ {i}).max'
  
  -- The key insight is that v is the FIRST crowded vertex on path i.
  -- After exchangeTails, the head of path i (vertices up to and including v) is preserved.
  -- Therefore:
  -- - v is still crowded on path i (shared with j, whose head also contains v)
  -- - All vertices before v on path i are still not crowded
  -- - So v is still the first crowded vertex on path i
  -- - i is still the smallest crowded index (any smaller index has unchanged path)
  -- - pathIndicesContaining v is preserved (shown above)
  -- - So j is still the largest in pathIndicesContaining v \ {i}
  
  -- Set up sp' for convenience
  set sp' := signReversing hac sp hip with h_sp'
  
  -- First, establish that i is in sp'.2.crowdedPathIndices
  have hi'_crowded : i ∈ sp'.2.crowdedPathIndices := by
    simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij
    simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
    exact ⟨v, hvi', hvj'⟩
  
  -- Extract that i was the min for sp
  have hi_min_sp : i = sp.2.crowdedPathIndices.min' 
      (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip) := by
    have h := h_data
    simp only [getCanonicalIntersectionData] at h
    exact (congrArg (fun x => x.val.1) h).symm
  
  -- Show that no index < i is crowded in sp'
  -- This is the key case analysis: for any l < i, l was not crowded in sp,
  -- and after signReversing, l is still not crowded because:
  -- - If l ∉ {i, j}, path l is unchanged
  -- - If l = j, then j < i, but j is crowded (shares v with i), so j ≥ i, contradiction
  have h_no_smaller_crowded : ∀ l : Fin k, l < i → l ∉ sp'.2.crowdedPathIndices := by
    intro l hl_lt
    have hl_not_crowded_sp : l ∉ sp.2.crowdedPathIndices := by
      intro hl_in
      have h_le := Finset.min'_le sp.2.crowdedPathIndices l hl_in
      rw [← hi_min_sp] at h_le
      omega
    -- Case analysis: is l = j?
    by_cases hlj : l = j
    · -- Case l = j: This is a contradiction
      -- j is crowded in sp (shares v with i), so j ∈ crowdedPathIndices
      -- Since i is the minimum, i ≤ j. But l = j < i, contradiction.
      have hj_crowded : j ∈ sp.2.crowdedPathIndices := by
        simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        use i, hij.symm
        simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
        exact ⟨v, hvj, hvi⟩
      have hi_le_j := Finset.min'_le sp.2.crowdedPathIndices j hj_crowded
      rw [← hi_min_sp] at hi_le_j
      omega
    · -- Case l ≠ j (and l ≠ i since l < i)
      have hli : l ≠ i := by omega
      -- Path l is unchanged in sp'
      have h_path_l_eq : sp'.2.paths l = sp.2.paths l := 
        signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hli hlj
      -- Suppose l is crowded in sp'. Then there exists m ≠ l with shared vertex w.
      intro hl_crowded'
      simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hl_crowded'
      obtain ⟨m, hlm, w, hw_inter⟩ := hl_crowded'
      simp only [Finset.mem_inter, List.mem_toFinset] at hw_inter
      obtain ⟨hw_l', hw_m'⟩ := hw_inter
      -- w is on path l in sp' = path l in sp
      rw [h_path_l_eq] at hw_l'
      -- Case analysis on m
      by_cases hmi : m = i
      · -- m = i: w is on path l (unchanged) and path i' = head_i ++ tail_j.tail
        rw [hmi, signReversing_path_i hac sp hip i j hij v hvi hvj h_data] at hw_m'
        rw [exchangeTails_fst_vertices] at hw_m'
        simp only [List.mem_append] at hw_m'
        rcases hw_m' with hw_head_i | hw_tail_j
        · -- w is in head_i: w was on path l and path i in sp
          have hw_i : w ∈ (sp.2.paths i).vertices := by
            have := splitAt_fst_vertices (sp.2.paths i) v hvi
            rw [this] at hw_head_i
            exact List.mem_of_mem_take hw_head_i
          apply hl_not_crowded_sp
          simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨i, hli, w, by simp [hw_l', hw_i]⟩
        · -- w is in tail_j.tail: w was on path l and path j in sp
          have hw_j : w ∈ (sp.2.paths j).vertices := by
            have := splitAt_snd_vertices (sp.2.paths j) v hvj
            rw [this] at hw_tail_j
            exact List.mem_of_mem_drop (List.mem_of_mem_tail hw_tail_j)
          apply hl_not_crowded_sp
          simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, hlj, w, by simp [hw_l', hw_j]⟩
      · by_cases hmj : m = j
        · -- m = j: w is on path l (unchanged) and path j' = head_j ++ tail_i.tail
          rw [hmj, signReversing_path_j hac sp hip i j hij v hvi hvj h_data] at hw_m'
          rw [exchangeTails_snd_vertices] at hw_m'
          simp only [List.mem_append] at hw_m'
          rcases hw_m' with hw_head_j | hw_tail_i
          · -- w is in head_j: w was on path l and path j in sp
            have hw_j : w ∈ (sp.2.paths j).vertices := by
              have := splitAt_fst_vertices (sp.2.paths j) v hvj
              rw [this] at hw_head_j
              exact List.mem_of_mem_take hw_head_j
            apply hl_not_crowded_sp
            simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hlj, w, by simp [hw_l', hw_j]⟩
          · -- w is in tail_i.tail: w was on path l and path i in sp
            have hw_i : w ∈ (sp.2.paths i).vertices := by
              have := splitAt_snd_vertices (sp.2.paths i) v hvi
              rw [this] at hw_tail_i
              exact List.mem_of_mem_drop (List.mem_of_mem_tail hw_tail_i)
            apply hl_not_crowded_sp
            simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨i, hli, w, by simp [hw_l', hw_i]⟩
        · -- m ∉ {i, j}: path m is unchanged
          have h_path_m_eq : sp'.2.paths m = sp.2.paths m := 
            signReversing_path_other hac sp hip i j hij v hvi hvj h_data m hmi hmj
          rw [h_path_m_eq] at hw_m'
          -- w was shared between l and m in sp, so l was crowded
          apply hl_not_crowded_sp
          simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨m, hlm, w, by simp [hw_l', hw_m']⟩
  
  -- Now we can show i is the min of sp'.2.crowdedPathIndices
  have hi'_min : i = sp'.2.crowdedPathIndices.min' 
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip') := by
    apply le_antisymm
    · apply Finset.le_min'
      intro l hl
      by_contra h
      push Not at h
      exact h_no_smaller_crowded l h hl
    · exact Finset.min'_le sp'.2.crowdedPathIndices i hi'_crowded
  
  -- v is crowded in sp' (on both paths i and j)
  have hv_crowded' : v ∈ sp'.2.crowdedVerticesOnPath i := by
    simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
    exact ⟨hvi', j, hij, hvj'⟩
  
  -- pathIndicesContaining v is preserved
  have h_pathIndices_eq := signReversing_pathIndicesContaining_eq hac sp hip i j hij v hvi hvj h_data
  
  -- The final equality requires showing that all components of getCanonicalIntersectionData match:
  -- 1. i is the min of crowdedPathIndices (shown in hi'_min)
  -- 2. The firstCrowdedIndexOnPath gives the same index (v is still first crowded vertex)
  -- 3. The vertex at that index is v (since heads are preserved)
  -- 4. j is the max of (pathIndicesContaining v \ {i}) (by h_pathIndices_eq)
  
  -- For (2) and (3): The head of path i is preserved by exchangeTails_head_eq,
  -- and the crowded status of vertices before v is preserved (shown in h_no_smaller_crowded analysis).
  -- Since v was the first crowded vertex in sp, it remains the first in sp'.
  
  -- Extract key facts from h_data
  have hi_crowded : i ∈ sp.2.crowdedPathIndices := by
    simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij
    simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
    exact ⟨v, hvi, hvj⟩
  
  -- The index of v on path i
  let idx := sp.2.firstCrowdedIndexOnPath i
  have h_idx : idx < (sp.2.paths i).vertices.length := sp.2.firstCrowdedIndexOnPath_lt_length i hi_crowded
  
  -- Key fact: v is at index idx on path i
  have h_v_at_idx : (sp.2.paths i).vertices[idx]'h_idx = v := by
    -- By definition of getCanonicalIntersectionData, v is defined as the vertex at firstCrowdedIndexOnPath i
    -- We extract this from h_data
    have h_v_eq : v = (getCanonicalIntersectionData sp.2 hip).val.2.2.val := by
      rw [h_data]
    -- Unfold getCanonicalIntersectionData to see that the result is (paths i').get ⟨idx', h_idx'⟩
    -- where i' = crowdedPathIndices.min' and idx' = firstCrowdedIndexOnPath i'
    simp only [getCanonicalIntersectionData] at h_v_eq
    -- h_v_eq now shows v = (sp.2.paths (min' ...)).vertices.get ⟨firstCrowdedIndexOnPath (min' ...), _⟩
    -- Since i = min' (by hi_min_sp), this gives us what we need
    rw [h_v_eq]
    -- Now need to show (sp.2.paths i).vertices[idx] = (sp.2.paths (min' ...)).vertices.get ...
    -- Use hi_min_sp: i = min' ...
    -- First, rewrite i to min' in the goal
    have h_idx_eq : idx = sp.2.firstCrowdedIndexOnPath (sp.2.crowdedPathIndices.min' 
        (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip)) := by
      exact congrArg sp.2.firstCrowdedIndexOnPath hi_min_sp
    simp only [hi_min_sp, h_idx_eq, List.get_eq_getElem]
  
  -- Key fact: idx equals the findIdx of v on path i
  have h_idx_eq_findIdx : idx = (sp.2.paths i).vertices.findIdx (· = v) := by
    -- Since v is at position idx on path i (by h_v_at_idx), and vertices are distinct
    -- (by acyclicity), findIdx (· = v) = idx
    have hnodup := SimpleDigraph.Path.vertices_nodup_of_acyclic hac (sp.2.paths i)
    have h_mem : v ∈ (sp.2.paths i).vertices := hvi
    have h_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, h_mem, by simp⟩
    have h_get := @List.findIdx_getElem _ (· = v) (sp.2.paths i).vertices h_lt
    simp only [decide_eq_true_eq] at h_get
    -- h_get : (sp.2.paths i).vertices[findIdx] = v
    -- h_v_at_idx : (sp.2.paths i).vertices[idx] = v
    -- Since vertices are distinct, findIdx = idx
    have h_eq : (sp.2.paths i).vertices[(sp.2.paths i).vertices.findIdx (· = v)]'h_lt = 
                (sp.2.paths i).vertices[idx]'h_idx := by
      rw [h_get, h_v_at_idx]
    exact (hnodup.getElem_inj_iff.mp h_eq).symm

  -- Key fact: firstCrowdedIndexOnPath gives the same index in sp' as in sp
  have h_firstCrowded_eq : sp'.2.firstCrowdedIndexOnPath i = idx := by
      -- This follows from:
      -- 1. Vertices before v on path i are not crowded in sp' (by vertices_before_v_not_crowded_in_sp')
      -- 2. v is crowded in sp' (by hv_crowded')
      -- 3. The head of path i is preserved (by exchangeTails_head_eq)
      
      -- First, show that the head of path i is preserved
      have h_path_i_eq : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
        signReversing_path_i hac sp hip i j hij v hvi hvj h_data
      
      simp only [PathTuple.firstCrowdedIndexOnPath]
      
      -- sp'.paths i has vertices = head_p ++ tail_q.tail
      have h_sp'_verts : (sp'.2.paths i).vertices = 
          ((sp.2.paths i).splitAt v hvi).1.vertices ++ 
          ((sp.2.paths j).splitAt v hvj).2.vertices.tail := by
        rw [h_path_i_eq, exchangeTails_fst_vertices]
      
      -- head_p has length idx + 1
      have h_head_len : ((sp.2.paths i).splitAt v hvi).1.vertices.length = idx + 1 := by
        rw [splitAt_fst_vertices]
        rw [List.length_take]
        have h_findIdx_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hvi, by simp⟩
        rw [h_idx_eq_findIdx]
        omega
      
      -- idx < length of sp'.paths i
      have h_idx_lt' : idx < (sp'.2.paths i).vertices.length := by
        rw [h_sp'_verts, List.length_append]
        have : 0 < ((sp.2.paths j).splitAt v hvj).2.vertices.tail.length ∨ 
               ((sp.2.paths j).splitAt v hvj).2.vertices.tail.length = 0 := by omega
        rcases this with hpos | hzero
        · omega
        · rw [h_head_len]; omega
      
      -- The key insight: sp'.paths i has the same first (idx+1) vertices as sp.paths i
      have h_prefix : ∀ m : ℕ, (hm : m ≤ idx) → 
          (sp'.2.paths i).vertices[m]'(Nat.lt_of_le_of_lt hm h_idx_lt') = 
          (sp.2.paths i).vertices[m]'(Nat.lt_of_le_of_lt hm h_idx) := by
        intro m hm
        have h_m_lt_head : m < ((sp.2.paths i).splitAt v hvi).1.vertices.length := by
          rw [h_head_len]; omega
        have h1 : (sp'.2.paths i).vertices[m]'(Nat.lt_of_le_of_lt hm h_idx_lt') = 
            (((sp.2.paths i).splitAt v hvi).1.vertices ++ 
             ((sp.2.paths j).splitAt v hvj).2.vertices.tail)[m]'(by
               rw [List.length_append]; omega) := by
          simp only [h_sp'_verts]
        rw [h1, List.getElem_append_left h_m_lt_head]
        simp only [splitAt_fst_vertices, List.getElem_take]

      -- The vertex at position idx in sp'.paths i is v
      have h_v_at_idx' : (sp'.2.paths i).vertices[idx]'h_idx_lt' = v := 
        (h_prefix idx (Nat.le_refl idx)).trans h_v_at_idx
      
      -- v is crowded in sp' (already have hv_crowded')
      have h_v_crowded_bool : (fun w => w ∈ sp'.2.crowdedVerticesOnPath i) v := hv_crowded'
      
      -- For m < idx, the vertex at position m is not crowded in sp'
      have h_before_not_crowded : ∀ m : ℕ, (hm : m < idx) → 
          ¬((sp'.2.paths i).vertices[m]'(Nat.lt_trans hm h_idx_lt') ∈ sp'.2.crowdedVerticesOnPath i) := by
        intro m hm
        have h_m_lt_sp : m < (sp.2.paths i).vertices.length := Nat.lt_trans hm h_idx
        have h_getElem_eq : (sp'.2.paths i).vertices[m]'(Nat.lt_trans hm h_idx_lt') = 
            (sp.2.paths i).vertices[m]'h_m_lt_sp := h_prefix m (Nat.le_of_lt hm)
        rw [h_getElem_eq]
        have h_m_lt_findIdx : m < (sp.2.paths i).vertices.findIdx (· = v) := by
          rw [← h_idx_eq_findIdx]; exact hm
        exact vertices_before_v_not_crowded_in_sp' hac sp hip i j hij v hvi hvj h_data 
          ((sp.2.paths i).vertices[m]'h_m_lt_sp) m h_m_lt_findIdx h_m_lt_sp rfl
      
      -- Apply findIdx_eq_of_first
      exact findIdx_eq_of_first (sp'.2.paths i).vertices 
        (fun w => decide (w ∈ sp'.2.crowdedVerticesOnPath i)) idx h_idx_lt'
        (fun m hm => by
          have := h_before_not_crowded m hm
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          exact this)
        (by simp only [decide_eq_true_eq]; rw [h_v_at_idx']; exact h_v_crowded_bool)
  
  -- Now we can show getCanonicalIntersectionData returns the same (i, j, v)
  -- The component equalities are established (hi'_min, h_firstCrowded_eq, h_pathIndices_eq)
  -- The final equality follows from these.
  
  -- First, establish that the min equals i
  have h_min_eq : sp'.2.crowdedPathIndices.min' 
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip') = i := hi'_min.symm
  
  -- The vertex at the first crowded index on path i in sp' is v
  -- We need to re-derive h_v_at_idx' here since it was local to h_firstCrowded_eq
  have h_idx_lt' : idx < (sp'.2.paths i).vertices.length := by
    have h_path_i_eq : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
      signReversing_path_i hac sp hip i j hij v hvi hvj h_data
    have h_sp'_verts : (sp'.2.paths i).vertices = 
        ((sp.2.paths i).splitAt v hvi).1.vertices ++ 
        ((sp.2.paths j).splitAt v hvj).2.vertices.tail := by
      rw [h_path_i_eq, exchangeTails_fst_vertices]
    have h_head_len : ((sp.2.paths i).splitAt v hvi).1.vertices.length = idx + 1 := by
      rw [splitAt_fst_vertices, List.length_take]
      have h_findIdx_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hvi, by simp⟩
      rw [h_idx_eq_findIdx]; omega
    rw [h_sp'_verts, List.length_append, h_head_len]; omega
  
  have h_v_at_idx'_new : (sp'.2.paths i).vertices[idx]'h_idx_lt' = v := by
    have h_path_i_eq : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
      signReversing_path_i hac sp hip i j hij v hvi hvj h_data
    have h_sp'_verts : (sp'.2.paths i).vertices = 
        ((sp.2.paths i).splitAt v hvi).1.vertices ++ 
        ((sp.2.paths j).splitAt v hvj).2.vertices.tail := by
      rw [h_path_i_eq, exchangeTails_fst_vertices]
    have h_head_len : ((sp.2.paths i).splitAt v hvi).1.vertices.length = idx + 1 := by
      rw [splitAt_fst_vertices, List.length_take]
      have h_findIdx_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hvi, by simp⟩
      rw [h_idx_eq_findIdx]; omega
    have h_idx_lt_head : idx < ((sp.2.paths i).splitAt v hvi).1.vertices.length := by
      rw [h_head_len]; omega
    calc (sp'.2.paths i).vertices[idx]'h_idx_lt' 
        = (((sp.2.paths i).splitAt v hvi).1.vertices ++ 
           ((sp.2.paths j).splitAt v hvj).2.vertices.tail)[idx]'(by rw [List.length_append]; omega) := by
          simp only [h_sp'_verts]
      _ = ((sp.2.paths i).splitAt v hvi).1.vertices[idx]'h_idx_lt_head := by
          rw [List.getElem_append_left h_idx_lt_head]
      _ = (sp.2.paths i).vertices[idx]'h_idx := by
          simp only [splitAt_fst_vertices, List.getElem_take]
      _ = v := h_v_at_idx
  
  -- Now show the vertex computed by getCanonicalIntersectionData equals v
  have h_v_eq' : (sp'.2.paths (sp'.2.crowdedPathIndices.min' 
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip'))).vertices.get 
      ⟨sp'.2.firstCrowdedIndexOnPath (sp'.2.crowdedPathIndices.min' 
        (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip')), 
       sp'.2.firstCrowdedIndexOnPath_lt_length _ (Finset.min'_mem _ _)⟩ = v := by
    simp only [h_min_eq, h_firstCrowded_eq, List.get_eq_getElem]
    exact h_v_at_idx'_new
  
  -- The max of (pathIndicesContaining v \ {i}) in sp' equals j
  have h_max_eq : ∀ h_sdiff_ne : (sp'.2.pathIndicesContaining v \ {i}).Nonempty,
      (sp'.2.pathIndicesContaining v \ {i}).max' h_sdiff_ne = j := by
    intro h_sdiff_ne
    have h_eq : sp'.2.pathIndicesContaining v \ {i} = sp.2.pathIndicesContaining v \ {i} := by
      rw [h_pathIndices_eq]
    -- j is in the set
    have hj_mem_sp' : j ∈ sp'.2.pathIndicesContaining v \ {i} := by
      simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                 Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨hvj', hij.symm⟩
    -- j is maximal: for all k in the set, k ≤ j
    have hj_max : ∀ k ∈ sp'.2.pathIndicesContaining v \ {i}, k ≤ j := by
      intro k hk
      rw [h_eq] at hk
      -- k is in sp.2.pathIndicesContaining v \ {i}
      -- j is the max' of this set (from h_data)
      -- We use the fact that h_data tells us j = max' of pathIndicesContaining v \ {i}
      have hj_mem_sp : j ∈ sp.2.pathIndicesContaining v \ {i} := by
        simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                   Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨hvj, hij.symm⟩
      -- From h_data, j is the max' of sp.2.pathIndicesContaining v \ {i}
      -- We need to show k ≤ j
      -- Since both k and j are in the same finite set, and j is the max from h_data
      have h_sdiff_ne_sp : (sp.2.pathIndicesContaining v \ {i}).Nonempty := ⟨j, hj_mem_sp⟩
      -- Extract from h_data that j equals the max'
      -- getCanonicalIntersectionData returns j = max' (pathIndicesContaining (vertex at idx) \ {i})
      -- where vertex at idx = v (by h_v_at_idx) and i = min' (by hi_min_sp)
      -- So j = max' (pathIndicesContaining v \ {i})
      have h_j_is_max : j = (sp.2.pathIndicesContaining v \ {i}).max' h_sdiff_ne_sp := by
        -- From the definition of getCanonicalIntersectionData and h_data
        -- The j component equals max' (pathIndicesContaining v \ {i})
        -- This is a consequence of h_data which specifies the exact form
        simp only [getCanonicalIntersectionData] at h_data
        have h := congrArg (fun x => x.val.2.1) h_data
        simp only at h
        rw [← h]
        -- Now we need to show the sets are equal
        -- The vertex in the definition equals v, and min' = i
        have h_vert : (sp.2.paths (sp.2.crowdedPathIndices.min' 
            (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip))).vertices.get 
            ⟨sp.2.firstCrowdedIndexOnPath (sp.2.crowdedPathIndices.min' 
              (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip)), 
             sp.2.firstCrowdedIndexOnPath_lt_length _ (Finset.min'_mem _ _)⟩ = v := by
          -- Use hi_min_sp : i = min' ... to rewrite
          have h_eq : sp.2.crowdedPathIndices.min' 
              (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip) = i := hi_min_sp.symm
          simp only [h_eq, List.get_eq_getElem]
          exact h_v_at_idx
        simp only [h_vert, hi_min_sp]
      rw [h_j_is_max]
      exact Finset.le_max' _ _ hk
    exact le_antisymm (Finset.max'_le _ h_sdiff_ne j hj_max) (Finset.le_max' _ j hj_mem_sp')
  
  -- Now construct the equality using Subtype.ext
  -- The goal is to show:
  -- getCanonicalIntersectionData sp'.2 hip' = ⟨⟨i, j, ⟨v, hvi', hvj'⟩⟩, hij⟩
  -- 
  -- We have established:
  -- - h_min_eq: min' crowdedPathIndices = i
  -- - h_firstCrowded_eq: firstCrowdedIndexOnPath i = idx
  -- - h_v_eq': vertex at that index = v
  -- - h_max_eq: max' (pathIndicesContaining v \ {i}) = j
  --
  -- The final equality involves complex dependent type transport.
  -- The key insight is that all components (i, j, v) are the same,
  -- so the equality holds by construction.
  simp only [getCanonicalIntersectionData]
  apply Subtype.ext
  simp only
  
  -- Use Sigma.ext for the nested sigma types
  have h1 : sp'.2.crowdedPathIndices.min' 
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip') = i := h_min_eq
  
  -- Get the vertex at firstCrowdedIndexOnPath i
  have h_vert : (sp'.2.paths i).vertices.get 
      ⟨sp'.2.firstCrowdedIndexOnPath i, 
       sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩ = v := by
    simp only [h_firstCrowded_eq, List.get_eq_getElem]
    exact h_v_at_idx'_new
  
  -- Get the nonemptiness proof
  have h_ne : (sp'.2.pathIndicesContaining 
      ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
        sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}).Nonempty := by
    have h_mem := sp'.2.firstCrowdedVertex_mem_crowdedVerticesOnPath i 
      (by rw [← h1]; exact Finset.min'_mem _ _)
    exact sp'.2.pathIndicesContaining_sdiff_singleton_nonempty i 
      (by rw [← h1]; exact Finset.min'_mem _ _) _ h_mem
  
  -- The j computed by getCanonicalIntersectionData equals j
  have h_j_eq : (sp'.2.pathIndicesContaining 
      ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
        sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}).max' h_ne = j := by
    -- The vertex equals v, so pathIndicesContaining (vertex) = pathIndicesContaining v
    -- j is in the set and is maximal
    have hj_mem : j ∈ sp'.2.pathIndicesContaining 
        ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
          sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i} := by
      simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                 Finset.mem_univ, true_and, Finset.mem_singleton, h_vert]
      exact ⟨hvj', hij.symm⟩
    have hj_max : ∀ k ∈ sp'.2.pathIndicesContaining 
        ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
          sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}, k ≤ j := by
      intro k hk
      simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                 Finset.mem_univ, true_and, Finset.mem_singleton, h_vert] at hk
      -- k ∈ pathIndicesContaining v \ {i}
      have hk' : k ∈ sp'.2.pathIndicesContaining v \ {i} := by
        simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                   Finset.mem_univ, true_and, Finset.mem_singleton]
        exact hk
      -- j is the max of pathIndicesContaining v \ {i}
      have h_ne' : (sp'.2.pathIndicesContaining v \ {i}).Nonempty := ⟨j, by
        simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                   Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨hvj', hij.symm⟩⟩
      have hj_is_max := h_max_eq h_ne'
      rw [← hj_is_max]
      exact Finset.le_max' _ _ hk'
    exact le_antisymm (Finset.max'_le _ h_ne j hj_max) (Finset.le_max' _ j hj_mem)
  
  -- The equality follows from h1, h_vert, h_j_eq
  -- All components match: i = min', v = vertex at idx, j = max'
  -- The proof involves dependent type transport
  -- 
  -- The key insight is that:
  -- - i = min' crowdedPathIndices (by h_min_eq = hi'_min.symm)
  -- - v = vertex at firstCrowdedIndexOnPath (by h_vert)
  -- - j = max' (pathIndicesContaining v \ {i}) (by h_j_eq)
  --
  -- After subst h1, the goal becomes showing equality of sigma types
  -- where all components are definitionally equal after the substitution.
  -- The final equality is a technical dependent type manipulation.
  -- All the mathematical content has been verified above.
  
  -- Use subst to eliminate h1, then use HEq for the remaining components
  -- First, convert the equalities to HEq before subst
  have h_j_heq : HEq 
      ((sp'.2.pathIndicesContaining 
        ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
          sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}).max' h_ne)
      j := heq_of_eq h_j_eq
  
  -- The vertex subtype needs HEq as well
  have h_vert_heq : HEq 
      ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
        sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩)
      v := heq_of_eq h_vert
  
  subst h1
  -- Now use cases on the HEq
  cases h_j_heq
  cases h_vert_heq
  rfl

theorem signReversing_involutive {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    let sp' := signReversing hac sp hip
    ∃ hip' : sp'.2.isIntersecting, signReversing hac sp' hip' = sp := by
  -- The proof uses the canonical (deterministic) selection of intersection data.
  -- With getCanonicalIntersectionData, the same (i, j, v) is selected for both sp and sp'.
  --
  -- Key insight: After exchangeTails at (i, j, v):
  -- - The head of path i (vertices before v) is unchanged
  -- - The head of path j (vertices before v) is unchanged
  -- - So crowdedPathIndices is the same, i is still the smallest
  -- - v is still the first crowded vertex on path i
  -- - pathIndicesContaining v is the same, j is still the largest
  --
  -- Once we have the same (i, j, v), the result follows from:
  -- - Permutation: (σ * swap i j) * swap i j = σ (by Equiv.swap_mul_self)
  -- - Paths: exchangeTails(exchangeTails(p_i, p_j, v)) = (p_i, p_j) (by exchangeTails_involutive)
  use signReversing_isIntersecting hac sp hip
  -- Extract the canonical intersection data for sp
  generalize h_data : getCanonicalIntersectionData sp.2 hip = data
  obtain ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := data
  
  -- Set up sp' and its properties
  set sp' := signReversing hac sp hip with h_sp'
  set hip' := signReversing_isIntersecting hac sp hip with h_hip'
  
  -- First, let's establish the path equalities we need
  have h_sp'_path_i : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
    signReversing_path_i hac sp hip i j hij v hvi hvj h_data
  have h_sp'_path_j : sp'.2.paths j = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 :=
    signReversing_path_j hac sp hip i j hij v hvi hvj h_data
  have h_sp'_perm : sp'.1 = sp.1 * Equiv.swap i j :=
    signReversing_perm_eq hac sp hip i j hij v hvi hvj h_data
  
  -- Use the key invariance lemma
  obtain ⟨hvi', hvj', h_data'⟩ := signReversing_canonical_eq hac sp hip i j hij v hvi hvj h_data hip'
  
  -- Now we can prove signReversing hac sp' hip' = sp
  -- First show the permutations are equal
  have h_perm_eq : (signReversing hac sp' hip').1 = sp.1 := by
    have h_perm' : (signReversing hac sp' hip').1 = sp'.1 * Equiv.swap i j := by
      conv_lhs => unfold signReversing; rw [h_data']
    rw [h_perm', h_sp'_perm]
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  
  -- Show path equality using exchangeTails_involutive
  -- Key: sp'.paths i = exchangeTails(sp.paths i, sp.paths j, v).1
  --      sp'.paths j = exchangeTails(sp.paths i, sp.paths j, v).2
  -- So: (signReversing sp' hip').paths i = exchangeTails(sp'.paths i, sp'.paths j, v).1
  --     = exchangeTails(exchangeTails(sp.paths i, sp.paths j, v).1, 
  --                     exchangeTails(sp.paths i, sp.paths j, v).2, v).1
  --     = sp.paths i  (by exchangeTails_involutive)
  
  -- Use exchangeTails_involutive to show the paths are equal to sp's paths
  have h_invol := exchangeTails_involutive hac (sp.2.paths i) (sp.2.paths j) v hvi hvj
  
  -- Define the intermediate paths for clarity
  set p_i' := (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 with h_p_i'_def
  set p_j' := (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 with h_p_j'_def
  
  -- The membership proofs from exchangeTails
  have hvi_exch : v ∈ p_i'.vertices := exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  have hvj_exch : v ∈ p_j'.vertices := exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  
  -- Extract the equalities from h_invol
  have h_invol_fst : (exchangeTails p_i' p_j' v hvi_exch hvj_exch).1 = sp.2.paths i := by
    have := congr_arg Prod.fst h_invol
    simp only at this
    exact this
  have h_invol_snd : (exchangeTails p_i' p_j' v hvi_exch hvj_exch).2 = sp.2.paths j := by
    have := congr_arg Prod.snd h_invol
    simp only at this
    exact this
  
  -- Key: sp'.paths i = p_i' and sp'.paths j = p_j'
  have h_sp'_i_eq : sp'.2.paths i = p_i' := h_sp'_path_i
  have h_sp'_j_eq : sp'.2.paths j = p_j' := h_sp'_path_j
  
  -- Cast the membership proofs to the correct types
  have hvi'_cast : v ∈ p_i'.vertices := h_sp'_i_eq ▸ hvi'
  have hvj'_cast : v ∈ p_j'.vertices := h_sp'_j_eq ▸ hvj'
  
  -- Show path i equality
  have h_path_i_eq : (signReversing hac sp' hip').2.paths i = sp.2.paths i := by
    -- (signReversing hac sp' hip').paths i = exchangeTails(sp'.paths i, sp'.paths j, v, hvi', hvj').1
    have h1 : (signReversing hac sp' hip').2.paths i = 
        (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').1 :=
      signReversing_path_i hac sp' hip' i j hij v hvi' hvj' h_data'
    -- Rewrite using the path equalities
    have h2 : (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').1 = 
              (exchangeTails p_i' p_j' v hvi'_cast hvj'_cast).1 := by
      simp only [h_sp'_i_eq, h_sp'_j_eq]
    rw [h1, h2]
    -- Now use proof irrelevance: hvi'_cast and hvi_exch are both proofs of v ∈ p_i'.vertices
    convert h_invol_fst using 2
      
  -- Show path j equality
  have h_path_j_eq : (signReversing hac sp' hip').2.paths j = sp.2.paths j := by
    have h1 : (signReversing hac sp' hip').2.paths j = 
        (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').2 :=
      signReversing_path_j hac sp' hip' i j hij v hvi' hvj' h_data'
    have h2 : (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').2 = 
              (exchangeTails p_i' p_j' v hvi'_cast hvj'_cast).2 := by
      simp only [h_sp'_i_eq, h_sp'_j_eq]
    rw [h1, h2]
    convert h_invol_snd using 2
      
  -- Show other paths are unchanged
  have h_path_other : ∀ l, l ≠ i → l ≠ j → (signReversing hac sp' hip').2.paths l = sp.2.paths l := by
    intro l hl_ne_i hl_ne_j
    have h1 : (signReversing hac sp' hip').2.paths l = sp'.2.paths l := 
      signReversing_path_other hac sp' hip' i j hij v hvi' hvj' h_data' l hl_ne_i hl_ne_j
    have h2 : sp'.2.paths l = sp.2.paths l := 
      signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hl_ne_i hl_ne_j
    rw [h1, h2]
  
  -- Combine to show full equality
  -- We need to show signReversing hac sp' hip' = sp
  -- Both are elements of pathTupleWithPerm A B = (σ : Perm (Fin k)) × PathTuple D k A (permuteKVertex σ B)
  -- We have h_perm_eq : (signReversing hac sp' hip').1 = sp.1
  -- And we need to show the PathTuples are equal
  
  -- First, let's show all paths are equal
  have h_paths_eq : ∀ l, (signReversing hac sp' hip').2.paths l = sp.2.paths l := by
    intro l
    by_cases hl_i : l = i
    · subst hl_i; exact h_path_i_eq
    · by_cases hl_j : l = j
      · subst hl_j; exact h_path_j_eq
      · exact h_path_other l hl_i hl_j
  
  -- Use Sigma.ext with the permutation equality
  -- The key is that h_perm_eq shows the first components are equal
  -- We need HEq for the second components
  -- Since the first components are equal, the types are equal, so HEq reduces to Eq
  have h_type_eq : PathTuple D k A (permuteKVertex (signReversing hac sp' hip').1 B) = 
                   PathTuple D k A (permuteKVertex sp.1 B) := by
    congr 1
    exact congrArg (permuteKVertex · B) h_perm_eq
  
  -- Now we can use the type equality to cast
  -- The key insight is that we need to show HEq between the PathTuples
  -- Since the permutations are equal, the target types are equal
  
  -- Direct approach: construct the equality using cases
  cases sp with
  | mk σ pt =>
    simp only at h_perm_eq h_paths_eq ⊢
    -- h_perm_eq : (signReversing hac sp' hip').1 = σ
    -- h_paths_eq : ∀ l, (signReversing hac sp' hip').2.paths l = pt.paths l
    -- Goal: signReversing hac sp' hip' = ⟨σ, pt⟩
    
    -- Destruct the signReversing result
    set sr := signReversing hac sp' hip' with h_sr_def
    obtain ⟨sr_perm, sr_pt⟩ := sr
    simp only at h_perm_eq h_paths_eq
    -- h_perm_eq : sr_perm = σ
    -- h_paths_eq : ∀ l, sr_pt.paths l = pt.paths l
    
    -- Subst the permutation equality
    subst h_perm_eq
    -- Now sr_pt and pt have the same type
    -- Goal: ⟨σ, sr_pt⟩ = ⟨σ, pt⟩
    congr 1
    -- Goal: sr_pt = pt
    ext l
    exact h_paths_eq l


/-- The permutation of signReversing is the original permutation composed with a transposition.
    This captures the essential structural property of the sign-reversing involution:
    when we exchange tails at indices i and j, we compose σ with the transposition (i j). -/
theorem signReversing_perm {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    ∃ i j : Fin k, i ≠ j ∧ (signReversing hac sp hip).1 = sp.1 * Equiv.swap i j := by
  -- By definition of signReversing, the permutation component is sp.1 * Equiv.swap i j
  -- where (i, j, v) are extracted by getCanonicalIntersectionData
  unfold signReversing
  let ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := getCanonicalIntersectionData sp.2 hip
  exact ⟨i, j, hij, rfl⟩

/-- The paths of signReversing are obtained by exchanging tails at indices i and j.
    This captures the essential structural property of the sign-reversing involution
    for the paths: paths at indices i and j have their tails exchanged at the crowded
    point v, while all other paths remain unchanged. -/
theorem signReversing_paths {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    ∃ i j : Fin k, i ≠ j ∧
      ∃ v : V, ∃ hvi : v ∈ (sp.2.paths i).vertices, ∃ hvj : v ∈ (sp.2.paths j).vertices,
        (signReversing hac sp hip).2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 ∧
        (signReversing hac sp hip).2.paths j = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 ∧
          ∀ l, l ≠ i → l ≠ j → (signReversing hac sp hip).2.paths l = sp.2.paths l := by
  -- signReversing uses getCanonicalIntersectionData to get (i, j, v, hvi, hvj)
  -- Since getCanonicalIntersectionData is deterministic, the same call returns the same value
  -- We use generalize to ensure we're working with the same data
  generalize h_data : getCanonicalIntersectionData sp.2 hip = data
  obtain ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := data
  -- Now signReversing uses h_data to get the same (i, j, v, hvi, hvj)
  refine ⟨i, j, hij, v, hvi, hvj, ?_, ?_, ?_⟩
  · -- Path i is the first component of exchangeTails
    show (signReversing hac sp hip).2.paths i = _
    conv_lhs => unfold signReversing; rw [h_data]; simp only [dite_true]
  · -- Path j is the second component of exchangeTails
    show (signReversing hac sp hip).2.paths j = _
    conv_lhs => unfold signReversing; rw [h_data]; simp only [hij.symm, dite_false, dite_true]
  · -- Other paths are unchanged
    intro l hl_ne_i hl_ne_j
    show (signReversing hac sp hip).2.paths l = sp.2.paths l
    conv_lhs => unfold signReversing; rw [h_data]; simp only [hl_ne_i, dite_false, hl_ne_j]

/-- The sign-reversing map flips the sign -/
theorem signReversing_sign {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    signOfPathTupleWithPerm (signReversing hac sp hip) = -signOfPathTupleWithPerm sp := by
  -- The sign-reversing map composes the permutation with a transposition (i j)
  -- Since sign(σ * swap i j) = sign(σ) * sign(swap i j) = sign(σ) * (-1) = -sign(σ)
  obtain ⟨i, j, hij, heq⟩ := signReversing_perm hac sp hip
  unfold signOfPathTupleWithPerm
  rw [heq, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  exact mul_neg_one (Equiv.Perm.sign sp.1)

/-- The sign-reversing map preserves weight -/
theorem signReversing_weight {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k} (w : ArcWeight D K)
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    weightOfPathTupleWithPerm w (signReversing hac sp hip) = weightOfPathTupleWithPerm w sp := by
  -- The sign-reversing map exchanges tails of paths at indices i and j
  -- All other paths remain unchanged
  -- The product of weights is preserved because:
  --   w(p_i) * w(p_j) = w(p'_i) * w(p'_j) (by exchangeTails_weight)
  --   and all other w(p_k) are unchanged
  obtain ⟨i, j, hij, v, hvi, hvj, hi_eq, hj_eq, h_rest⟩ := signReversing_paths hac sp hip
  unfold weightOfPathTupleWithPerm pathTupleWeight
  -- Show the product at indices i and j is preserved
  have h_ij : pathWeight w ((signReversing hac sp hip).2.paths i) *
              pathWeight w ((signReversing hac sp hip).2.paths j) =
              pathWeight w (sp.2.paths i) * pathWeight w (sp.2.paths j) := by
    rw [hi_eq, hj_eq]
    exact (exchangeTails_weight w (sp.2.paths i) (sp.2.paths j) v hvi hvj).symm
  -- Factor the products
  have h1 : ∏ l, pathWeight w ((signReversing hac sp hip).2.paths l) =
            pathWeight w ((signReversing hac sp hip).2.paths i) *
            pathWeight w ((signReversing hac sp hip).2.paths j) *
            ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w ((signReversing hac sp hip).2.paths l) := by
    rw [← Finset.prod_erase_mul (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.prod_erase_mul (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    ring
  have h2 : ∏ l, pathWeight w (sp.2.paths l) =
            pathWeight w (sp.2.paths i) * pathWeight w (sp.2.paths j) *
            ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w (sp.2.paths l) := by
    rw [← Finset.prod_erase_mul (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.prod_erase_mul (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    ring
  -- Show the rest of the product is unchanged
  have h3 : ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w ((signReversing hac sp hip).2.paths l) =
            ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w (sp.2.paths l) := by
    apply Finset.prod_congr rfl
    intro l hl
    simp only [Finset.mem_erase] at hl
    rw [h_rest l hl.2.1 hl.1]
  rw [h1, h2, h_ij, h3]

/-- The sign-reversing map has no fixed points (since it always flips the sign) -/
theorem signReversing_no_fixed_points {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    signReversing hac sp hip ≠ sp := by
  intro heq
  have hsign := signReversing_sign hac sp hip
  rw [heq] at hsign
  simp at hsign

/-!
## Infrastructure for LGV Proof

The following definitions and lemmas provide the infrastructure needed to complete
the LGV theorem proof. The key steps are:
1. Define the finset of all path tuples
2. Define the finset of intersecting path tuples (ipats)
3. Prove that the signed sum over ipats is 0 using the sign-reversing involution
-/

/-- The set of all path tuples from A to B -/
def allPathTupleSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (PathTuple D k A B) :=
  Set.univ

set_option backward.isDefEq.respectTransparency false in
/-- The set of all path tuples is finite (follows from path-finiteness) -/
theorem allPathTupleSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (allPathTupleSet (D := D) A B) := by
  -- The proof is essentially the same as nipatSetFinite
  let pathSets : Fin k → Set (SimpleDigraph.Path D) := fun i => 
    {p : SimpleDigraph.Path D | p.start = A i ∧ p.finish = B i}
  have h_each_finite : ∀ i, Set.Finite (pathSets i) := fun i => hpf (A i) (B i)
  have h_prod_finite : Set.Finite (Set.pi Set.univ pathSets) := 
    Set.Finite.pi (fun i => h_each_finite i)
  let f : (allPathTupleSet (D := D) A B) → Set.pi Set.univ pathSets := fun ⟨pt, _⟩ =>
    ⟨pt.paths, fun i _ => ⟨pt.starts i, pt.finishes i⟩⟩
  have hf_inj : Function.Injective f := by
    intro ⟨pt1, _⟩ ⟨pt2, _⟩ heq
    simp only [Subtype.mk.injEq, f] at heq ⊢
    cases pt1; cases pt2
    simp only [PathTuple.mk.injEq] at heq ⊢
    exact heq
  have h_pi_finite : Finite (Set.pi Set.univ pathSets) := h_prod_finite
  have h_finite : Finite (allPathTupleSet (D := D) A B) := Finite.of_injective f hf_inj
  exact Set.finite_coe_iff.mp h_finite

/-- Convert allPathTupleSet to Finset -/
noncomputable def allPathTupleFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Finset (PathTuple D k A B) :=
  (allPathTupleSetFinite hpf A B).toFinset

/-- Every path tuple is in allPathTupleFinset -/
theorem mem_allPathTupleFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt ∈ allPathTupleFinset hpf A B := by
  simp only [allPathTupleFinset, Set.Finite.mem_toFinset, allPathTupleSet, Set.mem_univ]

/-- The set of intersecting path tuples (ipats) -/
def ipatSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (PathTuple D k A B) :=
  {pt | pt.isIntersecting}

/-- The set of ipats is finite -/
noncomputable def ipatSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Set.Finite (ipatSet (D := D) A B) :=
  (allPathTupleSetFinite hpf A B).subset (fun _ _ => trivial)

/-- Convert ipatSet to Finset -/
noncomputable def ipatFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Finset (PathTuple D k A B) :=
  (ipatSetFinite hpf A B).toFinset

/-- Membership in ipatFinset -/
theorem mem_ipatFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt ∈ ipatFinset hpf A B ↔ pt.isIntersecting := by
  simp only [ipatFinset, Set.Finite.mem_toFinset, ipatSet, Set.mem_ofPred_eq]

/-- Membership in nipatFinset -/
theorem mem_nipatFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt ∈ nipatFinset hpf A B ↔ pt.isNonIntersecting := by
  simp only [nipatFinset, Set.Finite.mem_toFinset, nipatSet, Set.mem_ofPred_eq]

/-- nipats and ipats are disjoint -/
theorem nipatFinset_disjoint_ipatFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Disjoint (nipatFinset hpf A B) (ipatFinset hpf A B) := by
  rw [Finset.disjoint_iff_ne]
  intro pt1 h1 pt2 h2 heq
  rw [mem_nipatFinset_iff] at h1
  rw [mem_ipatFinset_iff] at h2
  subst heq
  -- h1 : pt1.isNonIntersecting, h2 : pt1.isIntersecting
  -- isIntersecting = ¬isNonIntersecting, so we have a contradiction
  exact h2 h1

/-- nipats ∪ ipats = all path tuples (set-level equality) -/
theorem nipatFinset_union_ipatFinset_eq {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    ∀ pt, pt ∈ nipatFinset hpf A B ∨ pt ∈ ipatFinset hpf A B ↔ 
          pt ∈ allPathTupleFinset hpf A B := by
  intro pt
  simp only [mem_nipatFinset_iff, mem_ipatFinset_iff, mem_allPathTupleFinset]
  constructor
  · intro _; trivial
  · intro _
    -- isIntersecting = ¬isNonIntersecting, so exactly one holds
    by_cases h : pt.isNonIntersecting
    · exact Or.inl h
    · exact Or.inr h

/-- The product of path weights equals the sum over path tuples -/
theorem prod_pathWeightSum_eq_sum_pathTupleWeight {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K) (A B : kVertex V k) :
    ∏ j, pathWeightSum hpf w (A j) (B j) = 
    ∑ pt ∈ allPathTupleFinset hpf A B, pathTupleWeight w pt.paths := by
  -- Use prod_univ_sum to expand the product
  simp only [pathWeightSum]
  rw [Finset.prod_univ_sum]
  -- Establish bijection between piFinset and allPathTupleFinset
  refine Finset.sum_bij' 
    -- forward: function → PathTuple
    (fun g hg => PathTuple.mk g 
      (fun j => by
        simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, 
                   Set.mem_ofPred_eq] at hg
        exact (hg j).1)
      (fun j => by
        simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, 
                   Set.mem_ofPred_eq] at hg
        exact (hg j).2))
    -- backward: PathTuple → function
    (fun pt _ => pt.paths)
    -- hi: forward maps into allPathTupleFinset
    (fun g hg => mem_allPathTupleFinset hpf _)
    -- hj: backward maps into piFinset
    (fun pt hpt => by
      simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      intro j
      exact ⟨pt.starts j, pt.finishes j⟩)
    -- left_inv: j(i(g)) = g
    (fun g hg => rfl)
    -- right_inv: i(j(pt)) = pt
    (fun pt hpt => by cases pt; rfl)
    -- function equality
    (fun g hg => rfl)

/-- The set of all intersecting path tuples with permutation.
    This is the domain of the sign-reversing involution. -/
def ipatWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  {sp | sp.2.isIntersecting}

/-- PathTuple is finite when the digraph is path-finite. -/
theorem pathTupleFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finite (PathTuple D k A B) := by
  have h := allPathTupleSetFinite hpf A B
  -- allPathTupleSet A B = Set.univ, so h : Set.Finite Set.univ
  -- We need to convert this to Finite (PathTuple D k A B)
  rw [allPathTupleSet] at h
  exact Set.finite_univ_iff.mp h

/-- pathTupleWithPerm is finite when the digraph is path-finite. -/
theorem pathTupleWithPermFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finite (pathTupleWithPerm (D := D) A B) := by
  unfold pathTupleWithPerm
  have h_perm_finite : Finite (Equiv.Perm (Fin k)) := inferInstance
  have h_pt_finite : ∀ σ : Equiv.Perm (Fin k), 
      Finite (PathTuple D k A (permuteKVertex σ B)) := by
    intro σ
    exact pathTupleFinite hpf A (permuteKVertex σ B)
  exact inferInstance

/-- The set of intersecting path tuples with permutation is finite. -/
noncomputable def ipatWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (ipatWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ.subset (fun _ _ => trivial)

/-- Convert ipatWithPermSet to Finset -/
noncomputable def ipatWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finset (pathTupleWithPerm (D := D) A B) :=
  (ipatWithPermSetFinite hpf A B).toFinset

/-- Membership in ipatWithPermFinset -/
theorem mem_ipatWithPermFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} 
    (sp : pathTupleWithPerm (D := D) A B) :
    sp ∈ ipatWithPermFinset hpf A B ↔ sp.2.isIntersecting := by
  simp only [ipatWithPermFinset, Set.Finite.mem_toFinset, ipatWithPermSet, Set.mem_ofPred_eq]

/-- The signed sum over ALL intersecting path tuples (with permutation) is zero.
    
    This is the correct formulation of the cancellation lemma. The sign-reversing
    involution `signReversing` maps (σ, pt) to (σ * swap i j, pt'), where:
    - sign(σ * swap i j) = -sign(σ)  (sign flips)
    - weight(pt') = weight(pt)       (weight preserved)
    
    So each pair {sp, signReversing(sp)} contributes:
      sign(σ) * w(pt) + sign(σ * swap i j) * w(pt')
    = sign(σ) * w(pt) + (-sign(σ)) * w(pt)
    = 0
    
    The total sum is therefore 0.
    
    Note: This works in any CommRing K, including characteristic 2, because we're
    summing pairs that each contribute 0, not just showing 2x = 0. -/
theorem sum_ipatWithPerm_signed_weight_eq_zero {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (hac : D.IsAcyclic) {k : ℕ} (w : ArcWeight D K) 
    (A B : kVertex V k) :
    ∑ sp ∈ ipatWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths = 0 := by
  -- The proof uses signReversing as a fixed-point-free involution that:
  -- 1. Maps ipatWithPermFinset to itself (signReversing_isIntersecting)
  -- 2. Flips the sign (signReversing_sign)
  -- 3. Preserves the weight (signReversing_weight)
  -- 4. Has no fixed points (signReversing_no_fixed_points)
  -- 5. Is an involution (signReversing_involutive)
  --
  -- We use Finset.sum_involution to show the sum is 0.
  apply Finset.sum_involution 
    (fun sp hsp => signReversing hac sp ((mem_ipatWithPermFinset_iff hpf sp).mp hsp))
  case hg₁ =>
    -- Show: f(sp) + f(g(sp)) = 0
    intro sp hsp
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    -- signReversing flips the sign and preserves the weight
    have hsign := signReversing_sign hac sp hip
    have hweight := signReversing_weight hac w sp hip
    simp only [signOfPathTupleWithPerm] at hsign
    simp only [weightOfPathTupleWithPerm] at hweight
    rw [hsign, hweight]
    simp only [Units.val_neg, Int.cast_neg]
    ring
  case hg₃ =>
    -- Show: f(sp) ≠ 0 → g(sp) ≠ sp (no fixed points)
    intro sp hsp _
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    exact signReversing_no_fixed_points hac sp hip
  case g_mem =>
    -- Show: g(sp) ∈ s (signReversing preserves membership)
    intro sp hsp
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    rw [mem_ipatWithPermFinset_iff]
    exact signReversing_isIntersecting hac sp hip
  case hg₄ =>
    -- Show: g(g(sp)) = sp (involution)
    intro sp hsp
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    exact (signReversing_involutive hac sp hip).choose_spec

/-- The set of all path tuples with permutation -/
def allPathTupleWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  Set.univ

/-- The set of all path tuples with permutation is finite -/
noncomputable def allPathTupleWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (allPathTupleWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ

/-- Convert allPathTupleWithPermSet to Finset -/
noncomputable def allPathTupleWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finset (pathTupleWithPerm (D := D) A B) :=
  (allPathTupleWithPermSetFinite hpf A B).toFinset

/-- Every path tuple with permutation is in allPathTupleWithPermFinset -/
theorem mem_allPathTupleWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} 
    (sp : pathTupleWithPerm (D := D) A B) :
    sp ∈ allPathTupleWithPermFinset hpf A B := by
  simp only [allPathTupleWithPermFinset, Set.Finite.mem_toFinset, allPathTupleWithPermSet, 
             Set.mem_univ]

/-- The set of non-intersecting path tuples with permutation -/
def nipatWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  {sp | sp.2.isNonIntersecting}

/-- The set of non-intersecting path tuples with permutation is finite -/
noncomputable def nipatWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (nipatWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ.subset (fun _ _ => trivial)

/-- Convert nipatWithPermSet to Finset -/
noncomputable def nipatWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finset (pathTupleWithPerm (D := D) A B) :=
  (nipatWithPermSetFinite hpf A B).toFinset

/-- Membership in nipatWithPermFinset -/
theorem mem_nipatWithPermFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} 
    (sp : pathTupleWithPerm (D := D) A B) :
    sp ∈ nipatWithPermFinset hpf A B ↔ sp.2.isNonIntersecting := by
  simp only [nipatWithPermFinset, Set.Finite.mem_toFinset, nipatWithPermSet, Set.mem_ofPred_eq]

/-- nipats and ipats with permutation are disjoint -/
theorem nipatWithPermFinset_disjoint_ipatWithPermFinset {V : Type*} [DecidableEq V] 
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Disjoint (nipatWithPermFinset hpf A B) (ipatWithPermFinset hpf A B) := by
  rw [Finset.disjoint_iff_ne]
  intro sp1 h1 sp2 h2 heq
  rw [mem_nipatWithPermFinset_iff] at h1
  rw [mem_ipatWithPermFinset_iff] at h2
  subst heq
  exact h2 h1

/-- nipats ∪ ipats with permutation = all path tuples with permutation (as a sum equality) -/
theorem nipatWithPermFinset_union_ipatWithPermFinset_sum {V : Type*} [DecidableEq V] 
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) 
    (f : pathTupleWithPerm (D := D) A B → K) :
    ∑ sp ∈ nipatWithPermFinset hpf A B, f sp + ∑ sp ∈ ipatWithPermFinset hpf A B, f sp =
    ∑ sp ∈ allPathTupleWithPermFinset hpf A B, f sp := by
  symm
  have hdec : DecidablePred (fun sp : pathTupleWithPerm (D := D) A B => sp.2.isNonIntersecting) := by
    intro sp
    exact Classical.dec _
  rw [← Finset.sum_filter_add_sum_filter_not (s := allPathTupleWithPermFinset hpf A B) 
      (p := fun sp => sp.2.isNonIntersecting)]
  congr 1
  · -- Show: filter for nipats = nipatWithPermFinset
    apply Finset.sum_congr
    · ext sp
      simp only [Finset.mem_filter, mem_allPathTupleWithPermFinset, true_and, 
                 mem_nipatWithPermFinset_iff]
    · intro _ _; rfl
  · -- Show: filter for ipats = ipatWithPermFinset
    apply Finset.sum_congr
    · ext sp
      simp only [Finset.mem_filter, mem_allPathTupleWithPermFinset, true_and, 
                 mem_ipatWithPermFinset_iff]
      rfl
    · intro _ _; rfl

/-- The sum over all path tuples with permutation splits into nipats and ipats -/
theorem sum_allPathTupleWithPerm_eq_sum_nipat_add_sum_ipat {V : Type*} [DecidableEq V] 
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K) 
    (A B : kVertex V k) :
    ∑ sp ∈ allPathTupleWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths =
    ∑ sp ∈ nipatWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths +
    ∑ sp ∈ ipatWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths := by
  rw [← nipatWithPermFinset_union_ipatWithPermFinset_sum hpf A B]

set_option backward.isDefEq.respectTransparency false in
/-- The sum over nipats with permutation equals the sum over permutations of nipatWeightSum -/
theorem sum_nipatWithPerm_eq_sum_nipatWeightSum {V : Type*} [DecidableEq V] 
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K) 
    (A B : kVertex V k) :
    ∑ sp ∈ nipatWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths =
    ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • nipatWeightSum hpf w A (permuteKVertex σ B) σ := by
  -- Step 1: Show nipatWithPermFinset = univ.sigma (fun σ => nipatFinset A (σB))
  have h_eq : nipatWithPermFinset hpf A B = 
      Finset.univ.sigma (fun σ => nipatFinset hpf A (permuteKVertex σ B)) := by
    ext sp
    constructor
    · intro h
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_univ _, (mem_nipatWithPermFinset_iff hpf sp).mp h |> 
            (mem_nipatFinset_iff hpf _).mpr⟩
    · intro h
      rw [Finset.mem_sigma] at h
      exact (mem_nipatWithPermFinset_iff hpf sp).mpr ((mem_nipatFinset_iff hpf _).mp h.2)
  -- Step 2: Rewrite using sigma sum and factor out sign(σ)
  rw [h_eq]
  calc ∑ sp ∈ Finset.univ.sigma (fun σ => nipatFinset hpf A (permuteKVertex σ B)),
        (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths
      = ∑ σ : Equiv.Perm (Fin k), ∑ pt ∈ nipatFinset hpf A (permuteKVertex σ B),
          (Equiv.Perm.sign σ : K) * pathTupleWeight w pt.paths := Finset.sum_sigma _ _ _
    _ = ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : K) * 
          ∑ pt ∈ nipatFinset hpf A (permuteKVertex σ B), pathTupleWeight w pt.paths := by
        apply Finset.sum_congr rfl
        intro σ _
        exact (Finset.mul_sum _ _ _).symm
    _ = ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • 
          nipatWeightSum hpf w A (permuteKVertex σ B) σ := by
        apply Finset.sum_congr rfl
        intro σ _
        simp only [nipatWeightSum, Units.smul_def, zsmul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
/-- The determinant can be written as a sum over all path tuples with permutation -/
theorem det_eq_sum_allPathTupleWithPerm {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K) (A B : kVertex V k) :
    (pathWeightMatrix hpf w A B).det =
    ∑ sp ∈ allPathTupleWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths := by
  -- Step 1-2: Reindex the determinant using Leibniz formula
  -- det(M) = ∑_σ sign(σ) ∏_i M_{σ(i), i} → ∑_τ sign(τ) ∏_j M_{j, τ(j)}
  rw [Matrix.det_apply']
  rw [Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin k))) _ 
      (fun τ => (Equiv.Perm.sign τ : K) * ∏ j, (pathWeightMatrix hpf w A B) j (τ j))]
  · -- Step 3: Each product ∏_j M_{j, τ(j)} = ∑_{pt : A → τB} w(pt)
    -- Note: M j (τ j) = pathWeightSum (A j) (B (τ j)) = pathWeightSum (A j) ((permuteKVertex τ B) j)
    have hprod : ∀ τ : Equiv.Perm (Fin k), 
        ∏ j, (pathWeightMatrix hpf w A B) j (τ j) = 
        ∑ pt ∈ allPathTupleFinset hpf A (permuteKVertex τ B), pathTupleWeight w pt.paths := by
      intro τ
      have heq : ∏ j, (pathWeightMatrix hpf w A B) j (τ j) = 
          ∏ j, pathWeightSum hpf w (A j) ((permuteKVertex τ B) j) := by
        apply Finset.prod_congr rfl
        intro j _
        simp only [pathWeightMatrix, Matrix.of_apply, permuteKVertex]
      rw [heq, prod_pathWeightSum_eq_sum_pathTupleWeight hpf w A (permuteKVertex τ B)]
    simp_rw [hprod]
    -- Now we have: ∑_τ sign(τ) * ∑_{pt ∈ allPathTupleFinset A (τB)} w(pt)
    -- Step 4: Show allPathTupleWithPermFinset = univ.sigma allPathTupleFinset
    have hS : allPathTupleWithPermFinset hpf A B = 
        Finset.univ.sigma (fun σ => allPathTupleFinset hpf A (permuteKVertex σ B)) := by
      ext ⟨σ, pt⟩
      constructor
      · intro _
        rw [Finset.mem_sigma]
        exact ⟨Finset.mem_univ σ, mem_allPathTupleFinset hpf pt⟩
      · intro _
        exact mem_allPathTupleWithPermFinset hpf ⟨σ, pt⟩
    rw [hS]
    -- Step 5: Use sum_sigma to combine
    let f : (Σ σ : Equiv.Perm (Fin k), PathTuple D k A (permuteKVertex σ B)) → K := 
      fun sp => (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths
    show ∑ τ, _ = ∑ sp ∈ Finset.univ.sigma _, f sp
    rw [Finset.sum_sigma]
    congr 1
    ext τ
    simp only [f]
    rw [Finset.mul_sum]
  · -- Prove the reindexing equality
    intro τ
    simp only [Equiv.inv_apply, Equiv.Perm.sign_inv]
    congr 1
    rw [← Equiv.prod_comp τ⁻¹]
    congr 1
    ext i
    simp



/-- LGV lemma, digraph weight version (Theorem thm.lgv.kpaths.wt-dg)
    Label: thm.lgv.kpaths.wt-dg

    For any path-finite acyclic digraph D with arc weights w ∈ K:
    det((∑_{p : Aᵢ → Bⱼ} w(p))_{i,j}) = ∑_{σ ∈ Sₖ} (-1)^σ ∑_{𝐩 nipat from 𝐀 to σ(𝐁)} w(𝐩)

    This generalizes the lattice version - we only use that D is path-finite and acyclic.

    **Proof outline:**
    1. By Leibniz formula: det(M) = ∑_σ (-1)^σ ∏_i M_{i,σ(i)}
    2. Each M_{i,σ(i)} = ∑_{p : A_i → B_{σ(i)}} w(p), so the product expands to
       ∑_{𝐩 : path tuple from 𝐀 to σ(𝐁)} w(𝐩)
    3. Thus det(M) = ∑_σ (-1)^σ ∑_{𝐩 : 𝐀 → σ(𝐁)} w(𝐩)
    4. Split the inner sum into nipats and ipats
    5. The sign-reversing involution on ipats shows ∑_{ipats} (-1)^σ w(𝐩) = 0
    6. Only nipats remain: det(M) = ∑_σ (-1)^σ ∑_{𝐩 nipat from 𝐀 to σ(𝐁)} w(𝐩) -/
theorem lgv_weighted_digraph {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (hac : D.IsAcyclic) {k : ℕ}
    (w : ArcWeight D K) (A B : kVertex V k) :
    (pathWeightMatrix hpf w A B).det =
      ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
        nipatWeightSum hpf w A (permuteKVertex σ B) σ := by
  -- Step 1-3: Write determinant as sum over all (σ, pt) pairs
  rw [det_eq_sum_allPathTupleWithPerm hpf w A B]
  -- Step 4: Split into nipats and ipats
  rw [sum_allPathTupleWithPerm_eq_sum_nipat_add_sum_ipat hpf w A B]
  -- Step 5: The ipat sum is 0 by sign-reversing involution
  rw [sum_ipatWithPerm_signed_weight_eq_zero hpf hac w A B, add_zero]
  -- Step 6: The nipat sum equals the RHS
  exact sum_nipatWithPerm_eq_sum_nipatWeightSum hpf w A B

/-- LGV lemma, lattice weight version (Theorem thm.lgv.kpaths.wt)
    Label: thm.lgv.kpaths.wt

    For the integer lattice ℤ² with arc weights w ∈ K:
    det((∑_{p : Aᵢ → Bⱼ} w(p))_{i,j}) = ∑_{σ ∈ Sₖ} (-1)^σ ∑_{𝐩 nipat from 𝐀 to σ(𝐁)} w(𝐩)

    The proof uses a sign-reversing involution on intersecting path tuples:
    when two paths intersect, exchange their tails at the first intersection point.
    This changes the sign (via the permutation) but preserves the weight.

    This is a special case of `lgv_weighted_digraph` for the integer lattice. -/
theorem lgv_weighted_lattice {k : ℕ} (w : ArcWeight integerLattice K)
    (A B : kVertex (ℤ × ℤ) k) :
    (pathWeightMatrix integerLattice_pathFinite w A B).det =
      ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
        nipatWeightSum integerLattice_pathFinite w A (permuteKVertex σ B) σ :=
  lgv_weighted_digraph integerLattice_pathFinite integerLattice_acyclic w A B

/-!
## The Nonpermutable Case

Corollary cor.lgv.kpaths.wt-np: When the source and target vertices are "sorted"
(x-coordinates decreasing, y-coordinates increasing), only the identity permutation
contributes to the sum.
-/

/-- The x-coordinate of a lattice point -/
def xCoord : ℤ × ℤ → ℤ := Prod.fst

/-- The y-coordinate of a lattice point -/
def yCoord : ℤ × ℤ → ℤ := Prod.snd

/-- A k-vertex has weakly decreasing x-coordinates -/
def xDecreasing {k : ℕ} (A : kVertex (ℤ × ℤ) k) : Prop :=
  ∀ i j : Fin k, i ≤ j → xCoord (A j) ≤ xCoord (A i)

/-- A k-vertex has weakly increasing y-coordinates -/
def yIncreasing {k : ℕ} (A : kVertex (ℤ × ℤ) k) : Prop :=
  ∀ i j : Fin k, i ≤ j → yCoord (A i) ≤ yCoord (A j)

/-- Discrete intermediate value theorem for integers (auxiliary version with explicit n) -/
lemma discrete_ivt_aux (n : ℕ) : ∀ (a b : ℤ) (f : ℤ → ℤ),
    a ≤ b → (b - a).toNat = n →
    (∀ m : ℤ, a ≤ m → m < b → |f (m + 1) - f m| ≤ 1) →
    0 ≤ f a → f b ≤ 0 →
    ∃ c : ℤ, a ≤ c ∧ c ≤ b ∧ f c = 0 := by
  induction n with
  | zero =>
    intro a b f hab hn hf hfa hfb
    have hab' : a = b := by omega
    refine ⟨a, le_refl _, by omega, ?_⟩
    subst hab'
    omega
  | succ k ih =>
    intro a b f hab hn hf hfa hfb
    by_cases hfa0 : f a = 0
    · exact ⟨a, le_refl _, hab, hfa0⟩
    · have ha1_le_b : a + 1 ≤ b := by omega
      have hf_step := hf a (le_refl _) (by omega : a < b)
      have hfa1_ge : f (a + 1) ≥ f a - 1 := by rw [abs_le] at hf_step; omega
      by_cases hfa1 : f (a + 1) ≤ 0
      · exact ⟨a + 1, by omega, ha1_le_b, by omega⟩
      · push Not at hfa1
        have hn' : (b - (a + 1)).toNat = k := by omega
        have hf' : ∀ m : ℤ, a + 1 ≤ m → m < b → |f (m + 1) - f m| ≤ 1 :=
          fun m hm1 hm2 => hf m (by omega) hm2
        obtain ⟨c, hc1, hc2, hc3⟩ := ih (a + 1) b f ha1_le_b hn' hf' (by omega) hfb
        exact ⟨c, by omega, hc2, hc3⟩

/-- Discrete intermediate value theorem for integers.
    If f : ℤ → ℤ satisfies |f(n+1) - f(n)| ≤ 1 for all n in [a, b),
    and f(a) ≥ 0 and f(b) ≤ 0, then there exists c in [a, b] with f(c) = 0. -/
lemma discrete_ivt {a b : ℤ} (hab : a ≤ b) (f : ℤ → ℤ)
    (hf : ∀ n : ℤ, a ≤ n → n < b → |f (n + 1) - f n| ≤ 1)
    (hfa : 0 ≤ f a) (hfb : f b ≤ 0) :
    ∃ c : ℤ, a ≤ c ∧ c ≤ b ∧ f c = 0 :=
  discrete_ivt_aux (b - a).toNat a b f hab rfl hf hfa hfb

/-- Baby Jordan curve theorem (Proposition prop.lgv.jordan-2)
    Label: prop.lgv.jordan-2

    If A' is weakly northwest of A, and B' is weakly northwest of B,
    then any path from A to B' and any path from A' to B must intersect.

    This is used to show that non-identity permutations have no nipats.

    **Proof sketch:**
    Both paths visit vertices with consecutive sum values (x + y).
    The sum ranges [A.1+A.2, B'.1+B'.2] for p and [A'.1+A'.2, B.1+B.2] for p' overlap.
    At each sum s in the overlap, path p has x-coordinate x_p(s) and p' has x_p'(s).
    At s_lo = max(A.1+A.2, A'.1+A'.2): x_p ≥ x_p' (because A.1 ≥ A'.1 and A.2 ≤ A'.2).
    At s_hi = min(B'.1+B'.2, B.1+B.2): x_p ≤ x_p' (because B'.1 ≤ B.1 and B'.2 ≥ B.2).
    By discrete IVT, there exists s where x_p(s) = x_p'(s), so the vertices coincide. -/
theorem baby_jordan {A A' B B' : ℤ × ℤ}
    (hxA : xCoord A' ≤ xCoord A) (hyA : yCoord A ≤ yCoord A')
    (hxB : xCoord B' ≤ xCoord B) (hyB : yCoord B ≤ yCoord B')
    (p : SimpleDigraph.Path integerLattice) (hp_start : p.start = A) (hp_finish : p.finish = B')
    (p' : SimpleDigraph.Path integerLattice) (hp'_start : p'.start = A') (hp'_finish : p'.finish = B) :
    pathsIntersect p p' := by
  simp only [xCoord, yCoord] at hxA hyA hxB hyB
  -- Path monotonicity gives coordinate bounds
  have hp_mono := integerLattice_path_start_le_finish p
  have hp'_mono := integerLattice_path_start_le_finish p'
  rw [hp_start, hp_finish] at hp_mono
  rw [hp'_start, hp'_finish] at hp'_mono
  -- Path lengths are determined by start/finish coordinates
  have hp_len_eq : (p.vertices.length : ℤ) = B'.1 + B'.2 - A.1 - A.2 + 1 := by
    rw [← hp_start, ← hp_finish]; exact integerLattice_path_length_eq p
  have hp'_len_eq : (p'.vertices.length : ℤ) = B.1 + B.2 - A'.1 - A'.2 + 1 := by
    rw [← hp'_start, ← hp'_finish]; exact integerLattice_path_length_eq p'
  -- The overlap [s_lo, s_hi] is nonempty
  set s_lo := max (A.1 + A.2) (A'.1 + A'.2) with hs_lo_def
  set s_hi := min (B'.1 + B'.2) (B.1 + B.2) with hs_hi_def
  have h_overlap : s_lo ≤ s_hi := by
    simp only [hs_lo_def, hs_hi_def, max_le_iff, le_min_iff]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  -- Define x-coordinate functions for each path at a given sum value
  -- For path p: at sum s, the index is (s - A.1 - A.2) and the x-coordinate is the first component
  -- For path p': at sum s, the index is (s - A'.1 - A'.2)
  have hp_pos : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
  have hp'_pos : 0 < p'.vertices.length := List.length_pos_of_ne_nil p'.nonempty
  -- Define the x-coordinate at sum s for path p
  let x_p (s : ℤ) : ℤ :=
    let idx := (s - A.1 - A.2).toNat
    if h : idx < p.vertices.length then (p.vertices.get ⟨idx, h⟩).1 else 0
  -- Define the x-coordinate at sum s for path p'
  let x_p' (s : ℤ) : ℤ :=
    let idx := (s - A'.1 - A'.2).toNat
    if h : idx < p'.vertices.length then (p'.vertices.get ⟨idx, h⟩).1 else 0
  -- The difference function
  let diff (s : ℤ) : ℤ := x_p s - x_p' s
  -- Key lemma: at sum s in the valid range, the index is valid and the vertex has sum s
  have hp_valid : ∀ s : ℤ, A.1 + A.2 ≤ s → s ≤ B'.1 + B'.2 →
      ∃ (hidx : (s - A.1 - A.2).toNat < p.vertices.length),
        (p.vertices.get ⟨(s - A.1 - A.2).toNat, hidx⟩).1 +
         (p.vertices.get ⟨(s - A.1 - A.2).toNat, hidx⟩).2 = s := by
    intro s hs_lo hs_hi
    have hidx_lt : (s - A.1 - A.2).toNat < p.vertices.length := by omega
    refine ⟨hidx_lt, ?_⟩
    have hsum := integerLattice_path_vertex_sum p (s - A.1 - A.2).toNat hidx_lt
    rw [hp_start] at hsum
    omega
  have hp'_valid : ∀ s : ℤ, A'.1 + A'.2 ≤ s → s ≤ B.1 + B.2 →
      ∃ (hidx : (s - A'.1 - A'.2).toNat < p'.vertices.length),
        (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat, hidx⟩).1 +
         (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat, hidx⟩).2 = s := by
    intro s hs_lo hs_hi
    have hidx_lt : (s - A'.1 - A'.2).toNat < p'.vertices.length := by omega
    refine ⟨hidx_lt, ?_⟩
    have hsum := integerLattice_path_vertex_sum p' (s - A'.1 - A'.2).toNat hidx_lt
    rw [hp'_start] at hsum
    omega
  -- At s_lo, x_p(s_lo) ≥ x_p'(s_lo)
  have hdiff_lo : 0 ≤ diff s_lo := by
    simp only [diff, x_p, x_p']
    have hs_lo_p : A.1 + A.2 ≤ s_lo := le_max_left _ _
    have hs_lo_p' : A'.1 + A'.2 ≤ s_lo := le_max_right _ _
    have hs_lo_hi_p : s_lo ≤ B'.1 + B'.2 := le_trans h_overlap (min_le_left _ _)
    have hs_lo_hi_p' : s_lo ≤ B.1 + B.2 := le_trans h_overlap (min_le_right _ _)
    obtain ⟨hp_idx_lt, hp_sum⟩ := hp_valid s_lo hs_lo_p hs_lo_hi_p
    obtain ⟨hp'_idx_lt, hp'_sum⟩ := hp'_valid s_lo hs_lo_p' hs_lo_hi_p'
    simp only [hp_idx_lt, hp'_idx_lt, dite_true]
    -- At s_lo, both vertices have sum s_lo
    -- x_p + y_p = s_lo and x_p' + y_p' = s_lo
    -- We need x_p ≥ x_p', i.e., y_p ≤ y_p'
    -- Path p starts at A, so at index (s_lo - A.1 - A.2), y ≥ A.2
    -- Path p' starts at A', so at index (s_lo - A'.1 - A'.2), y ≤ A'.2 + (s_lo - A'.1 - A'.2)
    -- Actually, we need to use monotonicity more carefully
    -- At s_lo = max(A.1+A.2, A'.1+A'.2):
    -- Case 1: s_lo = A.1 + A.2 (so A'.1 + A'.2 ≤ A.1 + A.2)
    --   Then x_p(s_lo) = A.1 (index 0)
    --   And x_p'(s_lo) is at index (A.1 + A.2 - A'.1 - A'.2) ≥ 0
    --   By monotonicity, x_p'(s_lo) ≥ A'.1
    --   We need A.1 ≥ x_p'(s_lo), which follows from A.1 ≥ A'.1 + (something)
    -- Actually, let's use: x_p + y_p = x_p' + y_p' = s_lo
    -- So x_p - x_p' = y_p' - y_p
    -- We need y_p' ≥ y_p
    -- Path p at index (s_lo - A.1 - A.2): y_p ≥ A.2 (by monotonicity from start)
    -- Path p' at index (s_lo - A'.1 - A'.2): y_p' ≥ A'.2 (by monotonicity from start)
    -- But we need y_p' ≥ y_p, not just both ≥ their starts
    -- Key insight: at s_lo, if s_lo = A.1 + A.2, then p is at A, so x_p = A.1
    --   and p' is at some point with sum s_lo and x ≤ A.1 (since A'.1 ≤ A.1 and x increases)
    -- Wait, x increases along the path, so x_p' at s_lo ≤ A'.1 + (s_lo - A'.1 - A'.2) = s_lo - A'.2
    -- And x_p at s_lo = A.1 (if s_lo = A.1 + A.2)
    -- We need A.1 ≥ s_lo - A'.2 = A.1 + A.2 - A'.2, i.e., A'.2 ≥ A.2. Yes! That's hyA.
    have hbd_p := integerLattice_path_vertices_bounded p (s_lo - A.1 - A.2).toNat hp_idx_lt
    have hbd_p' := integerLattice_path_vertices_bounded p' (s_lo - A'.1 - A'.2).toNat hp'_idx_lt
    rw [hp_start, hp_finish] at hbd_p
    rw [hp'_start, hp'_finish] at hbd_p'
    -- From hp_sum: x_p + y_p = s_lo, so y_p = s_lo - x_p
    -- From hbd_p: A.2 ≤ y_p, so A.2 ≤ s_lo - x_p, so x_p ≤ s_lo - A.2
    -- From hp'_sum: x_p' + y_p' = s_lo, so y_p' = s_lo - x_p'
    -- From hbd_p': A'.2 ≤ y_p', so x_p' ≤ s_lo - A'.2
    -- We need x_p ≥ x_p'
    -- From hbd_p: x_p ≥ A.1
    -- From hbd_p': x_p' ≤ B.1
    -- Hmm, this doesn't directly give us x_p ≥ x_p'
    -- Let's think again: x_p - x_p' = y_p' - y_p
    -- We need y_p' ≥ y_p
    -- From hbd_p: y_p ≤ B'.2
    -- From hbd_p': y_p' ≥ A'.2
    -- We need A'.2 ≥ y_p, but y_p ≥ A.2, so we need A'.2 ≥ A.2. That's hyA!
    -- Wait, but y_p could be larger than A.2...
    -- Actually, we need: y_p' - y_p ≥ 0
    -- y_p' = s_lo - x_p' and y_p = s_lo - x_p
    -- So y_p' - y_p = x_p - x_p'
    -- Circular!
    -- Let me think more carefully.
    -- At s_lo, path p is at index i_p = (s_lo - A.1 - A.2).toNat
    -- At s_lo, path p' is at index i_p' = (s_lo - A'.1 - A'.2).toNat
    -- We have i_p ≤ i_p' iff A'.1 + A'.2 ≤ A.1 + A.2 iff s_lo = A.1 + A.2
    -- Case s_lo = A.1 + A.2:
    --   i_p = 0, so p is at A, x_p = A.1
    --   i_p' = (A.1 + A.2 - A'.1 - A'.2).toNat
    --   x_p' ≤ A'.1 + i_p' = A'.1 + A.1 + A.2 - A'.1 - A'.2 = A.1 + A.2 - A'.2
    --   We need A.1 ≥ A.1 + A.2 - A'.2, i.e., A'.2 ≥ A.2. That's hyA!
    -- Case s_lo = A'.1 + A'.2:
    --   i_p = (A'.1 + A'.2 - A.1 - A.2).toNat
    --   i_p' = 0, so p' is at A', x_p' = A'.1
    --   x_p ≥ A.1 (by monotonicity)
    --   We need A.1 ≥ A'.1. That's hxA!
    -- So in both cases, x_p ≥ x_p'.
    -- The general argument: x_p ≥ A.1 and x_p' ≤ s_lo - A'.2
    -- We need A.1 ≥ s_lo - A'.2
    -- s_lo = max(A.1+A.2, A'.1+A'.2)
    -- If s_lo = A.1+A.2: A.1 ≥ A.1+A.2-A'.2 iff A'.2 ≥ A.2. ✓
    -- If s_lo = A'.1+A'.2: A.1 ≥ A'.1+A'.2-A'.2 = A'.1 iff A.1 ≥ A'.1. ✓
    -- Great! So x_p ≥ A.1 and x_p' ≤ s_lo - A'.2 and A.1 ≥ s_lo - A'.2
    have hx_p_ge : (p.vertices.get ⟨(s_lo - A.1 - A.2).toNat, hp_idx_lt⟩).1 ≥ A.1 := hbd_p.1
    have hx_p'_le : (p'.vertices.get ⟨(s_lo - A'.1 - A'.2).toNat, hp'_idx_lt⟩).1 ≤ s_lo - A'.2 := by
      have hy_p'_ge : (p'.vertices.get ⟨(s_lo - A'.1 - A'.2).toNat, hp'_idx_lt⟩).2 ≥ A'.2 := hbd_p'.2.2.1
      omega
    have hA1_ge : A.1 ≥ s_lo - A'.2 := by
      simp only [hs_lo_def]
      rcases le_or_gt (A.1 + A.2) (A'.1 + A'.2) with h | h
      · simp only [max_eq_right h]; omega
      · simp only [max_eq_left (le_of_lt h)]; omega
    omega
  -- At s_hi, x_p(s_hi) ≤ x_p'(s_hi)
  have hdiff_hi : diff s_hi ≤ 0 := by
    simp only [diff, x_p, x_p']
    have hs_hi_lo_p : A.1 + A.2 ≤ s_hi := le_trans (le_max_left _ _) h_overlap
    have hs_hi_lo_p' : A'.1 + A'.2 ≤ s_hi := le_trans (le_max_right _ _) h_overlap
    have hs_hi_p : s_hi ≤ B'.1 + B'.2 := min_le_left _ _
    have hs_hi_p' : s_hi ≤ B.1 + B.2 := min_le_right _ _
    obtain ⟨hp_idx_lt, hp_sum⟩ := hp_valid s_hi hs_hi_lo_p hs_hi_p
    obtain ⟨hp'_idx_lt, hp'_sum⟩ := hp'_valid s_hi hs_hi_lo_p' hs_hi_p'
    simp only [hp_idx_lt, hp'_idx_lt, dite_true]
    have hbd_p := integerLattice_path_vertices_bounded p (s_hi - A.1 - A.2).toNat hp_idx_lt
    have hbd_p' := integerLattice_path_vertices_bounded p' (s_hi - A'.1 - A'.2).toNat hp'_idx_lt
    rw [hp_start, hp_finish] at hbd_p
    rw [hp'_start, hp'_finish] at hbd_p'
    -- At s_hi, x_p ≤ B'.1 and x_p' ≥ s_hi - B.2
    -- We need x_p ≤ x_p', i.e., B'.1 ≤ s_hi - B.2
    -- s_hi = min(B'.1+B'.2, B.1+B.2)
    -- If s_hi = B'.1+B'.2: B'.1 ≤ B'.1+B'.2-B.2 iff B.2 ≤ B'.2. ✓ (hyB)
    -- If s_hi = B.1+B.2: B'.1 ≤ B.1+B.2-B.2 = B.1 iff B'.1 ≤ B.1. ✓ (hxB)
    have hx_p_le : (p.vertices.get ⟨(s_hi - A.1 - A.2).toNat, hp_idx_lt⟩).1 ≤ B'.1 := hbd_p.2.1
    have hx_p'_ge : (p'.vertices.get ⟨(s_hi - A'.1 - A'.2).toNat, hp'_idx_lt⟩).1 ≥ s_hi - B.2 := by
      have hy_p'_le : (p'.vertices.get ⟨(s_hi - A'.1 - A'.2).toNat, hp'_idx_lt⟩).2 ≤ B.2 := hbd_p'.2.2.2
      omega
    have hB'1_le : B'.1 ≤ s_hi - B.2 := by
      simp only [hs_hi_def]
      rcases le_or_gt (B'.1 + B'.2) (B.1 + B.2) with h | h
      · simp only [min_eq_left h]; omega
      · simp only [min_eq_right (le_of_lt h)]; omega
    omega
  -- The step property: |diff(s+1) - diff(s)| ≤ 1
  have hdiff_step : ∀ s : ℤ, s_lo ≤ s → s < s_hi → |diff (s + 1) - diff s| ≤ 1 := by
    intro s hs_lo hs_hi
    simp only [diff, x_p, x_p']
    -- At sum s and s+1, both paths are in valid range
    have hs_p_lo : A.1 + A.2 ≤ s := le_trans (le_max_left _ _) hs_lo
    have hs_p'_lo : A'.1 + A'.2 ≤ s := le_trans (le_max_right _ _) hs_lo
    have hs_p_hi : s + 1 ≤ B'.1 + B'.2 := by
      have : s < s_hi := hs_hi
      have : s_hi ≤ B'.1 + B'.2 := min_le_left _ _
      omega
    have hs_p'_hi : s + 1 ≤ B.1 + B.2 := by
      have : s < s_hi := hs_hi
      have : s_hi ≤ B.1 + B.2 := min_le_right _ _
      omega
    have hs_le_p : s ≤ B'.1 + B'.2 := by omega
    have hs_le_p' : s ≤ B.1 + B.2 := by omega
    obtain ⟨hp_idx_lt, _⟩ := hp_valid s hs_p_lo hs_le_p
    obtain ⟨hp_idx_lt', _⟩ := hp_valid (s + 1) (by omega) hs_p_hi
    obtain ⟨hp'_idx_lt, _⟩ := hp'_valid s hs_p'_lo hs_le_p'
    obtain ⟨hp'_idx_lt', _⟩ := hp'_valid (s + 1) (by omega) hs_p'_hi
    simp only [hp_idx_lt, hp_idx_lt', hp'_idx_lt, hp'_idx_lt', dite_true]
    -- The index at s+1 is the index at s plus 1
    have hidx_p : (s + 1 - A.1 - A.2).toNat = (s - A.1 - A.2).toNat + 1 := by omega
    have hidx_p' : (s + 1 - A'.1 - A'.2).toNat = (s - A'.1 - A'.2).toNat + 1 := by omega
    -- x-coordinate step for path p
    have hstep_p_idx : (s - A.1 - A.2).toNat + 1 < p.vertices.length := by omega
    have hstep_p'_idx : (s - A'.1 - A'.2).toNat + 1 < p'.vertices.length := by omega
    have hstep_p := integerLattice_path_x_step p (s - A.1 - A.2).toNat hstep_p_idx
    have hstep_p' := integerLattice_path_x_step p' (s - A'.1 - A'.2).toNat hstep_p'_idx
    -- The step properties give us bounds on the x-coordinate changes
    -- hstep_p: (p.vertices.get ⟨i+1, _⟩).1 - (p.vertices.get ⟨i, _⟩).1 ∈ {0, 1}
    -- We need to show |diff(s+1) - diff(s)| ≤ 1
    -- diff(s+1) - diff(s) = (x_p(s+1) - x_p(s)) - (x_p'(s+1) - x_p'(s))
    -- Each of x_p(s+1) - x_p(s) and x_p'(s+1) - x_p'(s) is 0 or 1
    -- So the difference is in {-1, 0, 1}
    have hp_idx_eq : (s - A.1 - A.2).toNat = (s - A.1 - A.2).toNat := rfl
    have hp'_idx_eq : (s - A'.1 - A'.2).toNat = (s - A'.1 - A'.2).toNat := rfl
    -- Get the x-coordinate differences
    have hx_p_diff : (p.vertices.get ⟨(s - A.1 - A.2).toNat + 1, hstep_p_idx⟩).1 -
                     (p.vertices.get ⟨(s - A.1 - A.2).toNat, Nat.lt_of_succ_lt hstep_p_idx⟩).1 = 0 ∨
                     (p.vertices.get ⟨(s - A.1 - A.2).toNat + 1, hstep_p_idx⟩).1 -
                     (p.vertices.get ⟨(s - A.1 - A.2).toNat, Nat.lt_of_succ_lt hstep_p_idx⟩).1 = 1 := hstep_p
    have hx_p'_diff : (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat + 1, hstep_p'_idx⟩).1 -
                      (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat, Nat.lt_of_succ_lt hstep_p'_idx⟩).1 = 0 ∨
                      (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat + 1, hstep_p'_idx⟩).1 -
                      (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat, Nat.lt_of_succ_lt hstep_p'_idx⟩).1 = 1 := hstep_p'
    -- Now relate these to the x_p and x_p' functions
    -- x_p(s+1) = (p.vertices.get ⟨(s+1 - A.1 - A.2).toNat, hp_idx_lt'⟩).1
    --          = (p.vertices.get ⟨(s - A.1 - A.2).toNat + 1, _⟩).1
    -- x_p(s) = (p.vertices.get ⟨(s - A.1 - A.2).toNat, hp_idx_lt⟩).1
    have heq_idx_p : (s + 1 - A.1 - A.2).toNat = (s - A.1 - A.2).toNat + 1 := by omega
    have heq_idx_p' : (s + 1 - A'.1 - A'.2).toNat = (s - A'.1 - A'.2).toNat + 1 := by omega
    -- The indices in hp_idx_lt and Nat.lt_of_succ_lt hstep_p_idx are the same
    have hp_idx_same : hp_idx_lt = Nat.lt_of_succ_lt hstep_p_idx := rfl
    have hp'_idx_same : hp'_idx_lt = Nat.lt_of_succ_lt hstep_p'_idx := rfl
    -- Now we can compute
    rcases hx_p_diff with hx_p_0 | hx_p_1 <;> rcases hx_p'_diff with hx_p'_0 | hx_p'_1 <;>
    · simp only [heq_idx_p, heq_idx_p']
      simp only [abs_le]
      constructor <;> omega
  -- Apply discrete IVT
  obtain ⟨s, hs_lo, hs_hi, hdiff_zero⟩ := discrete_ivt h_overlap diff hdiff_step hdiff_lo hdiff_hi
  -- At sum s, both paths have the same x-coordinate
  simp only [diff, x_p, x_p'] at hdiff_zero
  have hs_p_lo : A.1 + A.2 ≤ s := le_trans (le_max_left _ _) hs_lo
  have hs_p'_lo : A'.1 + A'.2 ≤ s := le_trans (le_max_right _ _) hs_lo
  have hs_p_hi : s ≤ B'.1 + B'.2 := le_trans hs_hi (min_le_left _ _)
  have hs_p'_hi : s ≤ B.1 + B.2 := le_trans hs_hi (min_le_right _ _)
  obtain ⟨hp_idx_lt, hp_sum⟩ := hp_valid s hs_p_lo hs_p_hi
  obtain ⟨hp'_idx_lt, hp'_sum⟩ := hp'_valid s hs_p'_lo hs_p'_hi
  simp only [hp_idx_lt, hp'_idx_lt, dite_true, sub_eq_zero] at hdiff_zero
  -- The vertices have the same x-coordinate and the same sum, so they're equal
  have hv_eq : p.vertices.get ⟨(s - A.1 - A.2).toNat, hp_idx_lt⟩ =
               p'.vertices.get ⟨(s - A'.1 - A'.2).toNat, hp'_idx_lt⟩ := by
    ext
    · exact hdiff_zero
    · omega
  -- The vertex is in both paths
  use p.vertices.get ⟨(s - A.1 - A.2).toNat, hp_idx_lt⟩
  constructor
  · exact List.get_mem p.vertices ⟨(s - A.1 - A.2).toNat, hp_idx_lt⟩
  · rw [hv_eq]
    exact List.get_mem p'.vertices ⟨(s - A'.1 - A'.2).toNat, hp'_idx_lt⟩

/-- A monotone bijection on Fin k is the identity.
    This is used to show that if σ ≠ id, then σ is not monotone. -/
lemma monotone_perm_eq_id {k : ℕ} (σ : Equiv.Perm (Fin k))
    (h : ∀ i j : Fin k, i < j → σ i ≤ σ j) : σ = Equiv.refl (Fin k) := by
  cases k with
  | zero =>
    ext i
    exact i.elim0
  | succ k =>
    have main : ∀ n : ℕ, ∀ i : Fin (k + 1), i.val = n → σ i = i := by
      intro n
      induction' n using Nat.strong_induction_on with n ih
      intro i hi
      have hih : ∀ j : Fin (k + 1), j.val < n → σ j = j := fun j hj => ih j.val hj j rfl
      have hge : i ≤ σ i := by
        by_contra hlt
        push Not at hlt
        have hlt' : σ i < i := hlt
        have hval : (σ i).val < n := by rw [← hi]; exact Fin.val_fin_lt.mpr hlt'
        have heq : σ (σ i) = σ i := hih (σ i) hval
        exact (ne_of_lt hlt') (σ.injective heq)
      have hle : σ i ≤ i := by
        by_contra hgt
        push Not at hgt
        have hgt' : i < σ i := hgt
        have hpre : σ.symm i < i := by
          by_contra hge'
          push Not at hge'
          rcases hge'.eq_or_lt with heq | hgt''
          · have := congrArg σ heq.symm
            simp at this
            exact (ne_of_gt hgt') this.symm
          · have hmono := h i (σ.symm i) hgt''
            simp at hmono
            exact not_lt.mpr hmono hgt'
        have hval : (σ.symm i).val < n := by rw [← hi]; exact Fin.val_fin_lt.mpr hpre
        have heq := hih (σ.symm i) hval
        simp at heq
        exact (ne_of_gt hpre) heq
      exact le_antisymm hle hge
    ext i
    simp only [Equiv.refl_apply]
    exact congrArg Fin.val (main i.val i rfl)

/-- When σ ≠ id, there are no nipats from 𝐀 to σ(𝐁) under the sorting conditions -/
theorem no_nipats_nonidentity {k : ℕ} (A B : kVertex (ℤ × ℤ) k)
    (hxA : xDecreasing A) (hyA : yIncreasing A)
    (hxB : xDecreasing B) (hyB : yIncreasing B)
    (σ : Equiv.Perm (Fin k)) (hσ : σ ≠ Equiv.refl (Fin k)) :
    nipatSet (D := integerLattice) A (permuteKVertex σ B) = ∅ := by
  ext pt
  simp only [nipatSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hpt
  -- σ ≠ id means σ is not monotone, so there exist i < j with σ(i) > σ(j)
  have : ∃ i j : Fin k, i < j ∧ σ j < σ i := by
    by_contra h
    push Not at h
    exact hσ (monotone_perm_eq_id σ h)
  obtain ⟨i, j, hij, hσij⟩ := this
  -- Apply baby_jordan to paths i and j
  have h_intersect : pathsIntersect (pt.paths i) (pt.paths j) := by
    apply baby_jordan
    · exact hxA i j (le_of_lt hij)
    · exact hyA i j (le_of_lt hij)
    · exact hxB (σ j) (σ i) (le_of_lt hσij)
    · exact hyB (σ j) (σ i) (le_of_lt hσij)
    · exact pt.starts i
    · exact pt.finishes i
    · exact pt.starts j
    · exact pt.finishes j
  exact hpt i j (ne_of_lt hij) h_intersect

/-- When the nipatSet is empty, the nipatWeightSum is zero -/
theorem nipatWeightSum_of_empty {k : ℕ} (w : ArcWeight integerLattice K)
    (A B : kVertex (ℤ × ℤ) k) (σ : Equiv.Perm (Fin k))
    (h : nipatSet (D := integerLattice) A B = ∅) :
    nipatWeightSum integerLattice_pathFinite w A B σ = 0 := by
  unfold nipatWeightSum
  rw [nipatFinset_of_empty _ _ _ h]
  simp

/-- Permuting a k-vertex by the identity permutation gives the same k-vertex -/
theorem permuteKVertex_refl {V : Type*} {k : ℕ} (B : kVertex V k) :
    permuteKVertex (Equiv.refl (Fin k)) B = B := by
  unfold permuteKVertex
  simp

/-- LGV lemma, nonpermutable lattice weight version (Corollary cor.lgv.kpaths.wt-np)
    Label: cor.lgv.kpaths.wt-np

    Under the sorting conditions:
    - x(A₁) ≥ x(A₂) ≥ ⋯ ≥ x(Aₖ)
    - y(A₁) ≤ y(A₂) ≤ ⋯ ≤ y(Aₖ)
    - x(B₁) ≥ x(B₂) ≥ ⋯ ≥ x(Bₖ)
    - y(B₁) ≤ y(B₂) ≤ ⋯ ≤ y(Bₖ)

    The LGV formula simplifies to:
    det((∑_{p : Aᵢ → Bⱼ} w(p))_{i,j}) = ∑_{𝐩 nipat from 𝐀 to 𝐁} w(𝐩) -/
theorem lgv_nonpermutable {k : ℕ} (w : ArcWeight integerLattice K)
    (A B : kVertex (ℤ × ℤ) k)
    (hxA : xDecreasing A) (hyA : yIncreasing A)
    (hxB : xDecreasing B) (hyB : yIncreasing B) :
    (pathWeightMatrix integerLattice_pathFinite w A B).det =
      nipatWeightSum integerLattice_pathFinite w A B (Equiv.refl (Fin k)) := by
  -- Apply the weighted LGV lemma
  rw [lgv_weighted_lattice]
  -- Split the sum: only the identity term survives
  have h_sum : ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
        nipatWeightSum integerLattice_pathFinite w A (permuteKVertex σ B) σ =
      Equiv.Perm.sign (Equiv.refl (Fin k)) •
        nipatWeightSum integerLattice_pathFinite w A (permuteKVertex (Equiv.refl (Fin k)) B)
          (Equiv.refl (Fin k)) := by
    apply Fintype.sum_eq_single
    intro σ hσ
    have h := no_nipats_nonidentity A B hxA hyA hxB hyB σ hσ
    rw [nipatWeightSum_of_empty _ _ _ _ h]
    simp
  rw [h_sum]
  simp only [Equiv.Perm.sign_refl, one_smul]
  rw [permuteKVertex_refl]

/-!
## Applications

### Binomial Coefficient Determinants (Corollary cor.lgv.binom-det-nonneg)

When the matrix entries are binomial coefficients, the determinant is nonnegative.
-/

/-!
#### The FKG Inequality for Binomial Coefficients

The key combinatorial inequality underlying the binomial determinant nonnegativity.
This is the 2×2 case of the LGV lemma, which can be proved directly by induction.
-/

/-- The FKG inequality for binomial coefficients (core case):
    C(A,C) * C(B,D) ≥ C(A,D) * C(B,C) when A ≥ B, C ≥ D, C ≤ A, and D ≤ B.

    This is equivalent to log-supermodularity of binomial coefficients.
    Combinatorially, the difference C(A,C)*C(B,D) - C(A,D)*C(B,C) equals
    the count of non-intersecting lattice path pairs, which is nonnegative. -/
private lemma binom_fkg_core (A B C D : ℕ) (hAB : B ≤ A) (hCD : D ≤ C) (hCA : C ≤ A) (hDB : D ≤ B) :
    (A.choose D : ℤ) * (B.choose C) ≤ (A.choose C) * (B.choose D) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hCD
  induction k generalizing C with
  | zero =>
    simp only [add_zero] at hk
    subst hk
    rfl
  | succ k ih =>
    simp only [← add_assoc] at hk
    subst hk
    have ih_applied := ih (D + k) (Nat.le_add_right D k) (Nat.le_of_succ_le hCA) rfl
    by_cases hBm : B < D + k + 1
    · simp only [Nat.choose_eq_zero_of_lt hBm, CharP.cast_eq_zero, mul_zero]
      exact mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    · push Not at hBm
      have hBDk : D + k ≤ B := Nat.le_of_succ_le hBm
      have hADk : D + k ≤ A := Nat.le_of_succ_le hCA
      have hA_rec := Nat.choose_succ_right_eq A (D + k)
      have hB_rec := Nat.choose_succ_right_eq B (D + k)
      have hA_rec_int : (A.choose (D + k + 1) : ℤ) * (D + k + 1) =
                        (A.choose (D + k)) * (A - (D + k)) := by
        have : (A - (D + k) : ℤ) = ((A - (D + k) : ℕ) : ℤ) := by simp [Int.ofNat_sub hADk]
        rw [this]; norm_cast
      have hB_rec_int : (B.choose (D + k + 1) : ℤ) * (D + k + 1) =
                        (B.choose (D + k)) * (B - (D + k)) := by
        have : (B - (D + k) : ℤ) = ((B - (D + k) : ℕ) : ℤ) := by simp [Int.ofNat_sub hBDk]
        rw [this]; norm_cast
      have key : (A.choose D : ℤ) * (B.choose (D + k + 1)) * (D + k + 1) ≤
                 (A.choose (D + k + 1)) * (B.choose D) * (D + k + 1) := by
        calc (A.choose D : ℤ) * (B.choose (D + k + 1)) * (D + k + 1)
            = (A.choose D) * ((B.choose (D + k + 1)) * (D + k + 1)) := by ring
          _ = (A.choose D) * ((B.choose (D + k)) * (B - (D + k))) := by rw [hB_rec_int]
          _ = (A.choose D) * (B.choose (D + k)) * (B - (D + k)) := by ring
          _ ≤ (A.choose (D + k)) * (B.choose D) * (B - (D + k)) := by
              have h1 : (0 : ℤ) ≤ (B : ℤ) - (D + k) := by
                simp only [sub_nonneg]; exact Int.ofNat_le.mpr hBDk
              nlinarith
          _ ≤ (A.choose (D + k)) * (B.choose D) * (A - (D + k)) := by
              have h1 : (B : ℤ) - (D + k) ≤ (A : ℤ) - (D + k) := by
                simp only [sub_le_sub_iff_right]; exact Int.ofNat_le.mpr hAB
              have h2 : (0 : ℤ) ≤ (A.choose (D + k)) * (B.choose D) :=
                mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
              nlinarith
          _ = ((A.choose (D + k)) * (A - (D + k))) * (B.choose D) := by ring
          _ = (A.choose (D + k + 1)) * (D + k + 1) * (B.choose D) := by rw [hA_rec_int]
          _ = (A.choose (D + k + 1)) * (B.choose D) * (D + k + 1) := by ring
      have hpos : (0 : ℤ) < (D + k + 1 : ℕ) := by positivity
      have := Int.le_of_mul_le_mul_right key hpos
      convert this using 1

/-- The FKG inequality for binomial coefficients:
    C(a,c) * C(b,d) ≥ C(a,d) * C(b,c) when a ≥ b and c ≥ d.

    This handles all cases including when some choose values are zero. -/
lemma binom_2x2_ineq (a b c d : ℕ) (hab : b ≤ a) (hcd : d ≤ c) :
    (a.choose d : ℤ) * (b.choose c) ≤ (a.choose c) * (b.choose d) := by
  by_cases hca : c > a
  · have hbc : c > b := Nat.lt_of_le_of_lt hab hca
    simp [Nat.choose_eq_zero_of_lt hca, Nat.choose_eq_zero_of_lt hbc]
  · push Not at hca
    by_cases hdb : d > b
    · have hbc : c > b := Nat.lt_of_lt_of_le hdb hcd
      simp [Nat.choose_eq_zero_of_lt hdb, Nat.choose_eq_zero_of_lt hbc]
    · push Not at hdb
      exact binom_fkg_core a b c d hab hcd hca hdb

/-!
#### Base cases for binomial determinant nonnegativity
-/

/-- Base case k=0: empty matrix has determinant 1 ≥ 0 -/
private theorem binom_det_nonneg_zero (a b : Fin 0 → ℕ)
    (_ha : ∀ i j : Fin 0, i ≤ j → a j ≤ a i)
    (_hb : ∀ i j : Fin 0, i ≤ j → b j ≤ b i) :
    0 ≤ (Matrix.of fun i j => (a i).choose (b j) : Matrix (Fin 0) (Fin 0) ℤ).det := by
  simp [det_isEmpty]

/-- Base case k=1: 1×1 matrix has determinant = C(a₀, b₀) ≥ 0 -/
private theorem binom_det_nonneg_one (a b : Fin 1 → ℕ)
    (_ha : ∀ i j : Fin 1, i ≤ j → a j ≤ a i)
    (_hb : ∀ i j : Fin 1, i ≤ j → b j ≤ b i) :
    0 ≤ (Matrix.of fun i j => (a i).choose (b j) : Matrix (Fin 1) (Fin 1) ℤ).det := by
  simp only [det_unique, of_apply, Fin.default_eq_zero]
  exact Int.natCast_nonneg _

/-- Base case k=2: 2×2 binomial determinant is nonnegative.
    This uses the FKG inequality for binomial coefficients. -/
private theorem binom_det_nonneg_two (a b : Fin 2 → ℕ)
    (ha : ∀ i j : Fin 2, i ≤ j → a j ≤ a i)
    (hb : ∀ i j : Fin 2, i ≤ j → b j ≤ b i) :
    0 ≤ (Matrix.of fun i j => (a i).choose (b j) : Matrix (Fin 2) (Fin 2) ℤ).det := by
  simp only [det_fin_two, of_apply]
  have ha01 : a 1 ≤ a 0 := ha 0 1 (Fin.zero_le 1)
  have hb01 : b 1 ≤ b 0 := hb 0 1 (Fin.zero_le 1)
  have := binom_2x2_ineq (a 0) (a 1) (b 0) (b 1) ha01 hb01
  linarith

/-!
#### Lattice point setup for binomial determinants

The key construction: set Aᵢ = (0, -aᵢ) and Bᵢ = (bᵢ, -bᵢ).
These satisfy the sorting conditions for lgv_nonpermutable.
-/

/-- The source lattice points for the binomial coefficient determinant:
    A_i = (0, -a_i) for the LGV lemma application. -/
def binomLatticeA {k : ℕ} (a : Fin k → ℕ) : kVertex (ℤ × ℤ) k :=
  fun i => (0, -(a i : ℤ))

/-- The target lattice points for the binomial coefficient determinant:
    B_i = (b_i, -b_i) for the LGV lemma application. -/
def binomLatticeB {k : ℕ} (b : Fin k → ℕ) : kVertex (ℤ × ℤ) k :=
  fun i => (b i, -(b i : ℤ))

/-- The source lattice points have constant x-coordinate 0, so xDecreasing holds trivially. -/
theorem binomLatticeA_xDecreasing {k : ℕ} (a : Fin k → ℕ) :
    xDecreasing (binomLatticeA a) := by
  intro i j _
  simp [binomLatticeA, xCoord]

/-- The source lattice points satisfy yIncreasing when a is weakly decreasing.
    If a_i ≥ a_j for i ≤ j, then -a_i ≤ -a_j. -/
theorem binomLatticeA_yIncreasing {k : ℕ} (a : Fin k → ℕ)
    (ha : ∀ i j : Fin k, i ≤ j → a j ≤ a i) :
    yIncreasing (binomLatticeA a) := by
  intro i j hij
  simp only [binomLatticeA, yCoord, neg_le_neg_iff, Int.ofNat_le]
  exact ha i j hij

/-- The target lattice points satisfy xDecreasing when b is weakly decreasing.
    If b_i ≥ b_j for i ≤ j, then x-coordinate b_i ≥ b_j. -/
theorem binomLatticeB_xDecreasing {k : ℕ} (b : Fin k → ℕ)
    (hb : ∀ i j : Fin k, i ≤ j → b j ≤ b i) :
    xDecreasing (binomLatticeB b) := by
  intro i j hij
  simp only [binomLatticeB, xCoord, Int.ofNat_le]
  exact hb i j hij

/-- The target lattice points satisfy yIncreasing when b is weakly decreasing.
    If b_i ≥ b_j for i ≤ j, then -b_i ≤ -b_j. -/
theorem binomLatticeB_yIncreasing {k : ℕ} (b : Fin k → ℕ)
    (hb : ∀ i j : Fin k, i ≤ j → b j ≤ b i) :
    yIncreasing (binomLatticeB b) := by
  intro i j hij
  simp only [binomLatticeB, yCoord, neg_le_neg_iff, Int.ofNat_le]
  exact hb i j hij

/-!
#### Helper definitions for the path-subset bijection

The bijection between paths from (0, -a) to (b, -b) and b-element subsets of Fin a
is constructed using the following helpers:
- `eastStepCount a S i`: count of elements j ∈ S with j < i
- `vertexAtPos a S i`: the vertex at position i in the path determined by S
- `pathVerticesList a S`: the list of vertices for the path determined by S
-/

/-- Count of east steps before index i: |{j ∈ S : j < i}| -/
private def eastStepCount (a : ℕ) (S : Finset (Fin a)) (i : ℕ) : ℕ :=
  (S.filter fun j => j.val < i).card

/-- Vertex at position i in the path determined by east-step set S.
    x-coordinate = number of east steps taken so far
    y-coordinate = -a + (i - number of east steps) = -a + number of north steps -/
private def vertexAtPos (a : ℕ) (S : Finset (Fin a)) (i : ℕ) : ℤ × ℤ :=
  let e := eastStepCount a S i
  ((e : ℤ), -(a : ℤ) + ((i : ℤ) - (e : ℤ)))

/-- vertexAtPos 0 = (0, -a) -/
private lemma vertexAtPos_zero (a : ℕ) (S : Finset (Fin a)) : 
    vertexAtPos a S 0 = (0, -(a : ℤ)) := by
  simp only [vertexAtPos, eastStepCount]
  have h : S.filter (fun j => j.val < 0) = ∅ := by
    ext j; simp only [Finset.mem_filter]
    constructor
    · intro ⟨_, hlt⟩; exact (Nat.not_lt_zero _ hlt).elim
    · simp
  simp only [h, Finset.card_empty, CharP.cast_eq_zero, sub_zero, add_zero]

/-- eastStepCount a S a = S.card (all elements of Fin a are < a) -/
private lemma eastStepCount_last (a : ℕ) (S : Finset (Fin a)) :
    eastStepCount a S a = S.card := by
  simp only [eastStepCount]
  congr 1
  ext j
  simp only [Finset.mem_filter, and_iff_left j.isLt]

/-- When |S| = b, vertexAtPos a S a = (b, -b) -/
private lemma vertexAtPos_last_eq (a b : ℕ) (S : Finset (Fin a)) (hcard : S.card = b) :
    vertexAtPos a S a = ((b : ℤ), -(b : ℤ)) := by
  simp only [vertexAtPos, eastStepCount_last, hcard]
  ring_nf

/-- The list of vertices for the path determined by S -/
private def pathVerticesList (a : ℕ) (S : Finset (Fin a)) : List (ℤ × ℤ) :=
  List.ofFn (fun i : Fin (a + 1) => vertexAtPos a S i.val)

private lemma pathVerticesList_length (a : ℕ) (S : Finset (Fin a)) :
    (pathVerticesList a S).length = a + 1 := by simp [pathVerticesList]

private lemma pathVerticesList_nonempty (a : ℕ) (S : Finset (Fin a)) :
    pathVerticesList a S ≠ [] := by simp [pathVerticesList]

private lemma pathVerticesList_getElem (a : ℕ) (S : Finset (Fin a)) (i : ℕ) (hi : i < a + 1) :
    (pathVerticesList a S)[i]'(by rw [pathVerticesList_length]; exact hi) = vertexAtPos a S i := by
  simp only [pathVerticesList, List.getElem_ofFn]

/-- Consecutive vertices in the path satisfy the arc relation -/
private lemma vertexAtPos_arc (a : ℕ) (S : Finset (Fin a)) (i : Fin a) :
    integerLattice.arc (vertexAtPos a S i.val) (vertexAtPos a S (i.val + 1)) := by
  simp only [vertexAtPos, eastStepCount, integerLattice]
  by_cases hi : i ∈ S
  · -- i ∈ S: east step (x increases by 1, y stays the same)
    left
    have hfilter : (S.filter (fun j => j.val < i.val + 1)).card = 
                   (S.filter (fun j => j.val < i.val)).card + 1 := by
      have heq : S.filter (fun j => j.val < i.val + 1) = 
                 insert i (S.filter (fun j => j.val < i.val)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · intro ⟨hj, hlt⟩
          by_cases hji : j = i
          · left; exact hji
          · right; exact ⟨hj, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) (fun h => hji (Fin.ext h))⟩
        · intro h; rcases h with rfl | ⟨hj, hlt⟩
          · exact ⟨hi, Nat.lt_succ_self _⟩
          · exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
      rw [heq]
      have hnotmem : i ∉ S.filter (fun j => j.val < i.val) := by
        simp only [Finset.mem_filter, not_and, not_lt]; intro _; exact le_refl _
      rw [Finset.card_insert_eq_ite, ite_eq_right hnotmem]
    constructor
    · simp only [hfilter]; push_cast; ring
    · simp only [hfilter]; push_cast; ring
  · -- i ∉ S: north step (x stays the same, y increases by 1)
    right
    have hfilter : (S.filter (fun j => j.val < i.val + 1)).card = 
                   (S.filter (fun j => j.val < i.val)).card := by
      congr 1; ext j; simp only [Finset.mem_filter]
      constructor
      · intro ⟨hj, hlt⟩
        constructor
        · exact hj
        · by_cases hji : j.val = i.val
          · exfalso; have : j = i := Fin.ext hji; rw [this] at hj; exact hi hj
          · exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hji
      · intro ⟨hj, hlt⟩; exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
    constructor
    · simp only [hfilter]
    · simp only [hfilter]; push_cast; ring

/-- Construct a path from (0, -a) to (b, -b) given a b-element subset S of Fin a -/
private noncomputable def eastStepsToPath (a b : ℕ) (S : Finset (Fin a)) (_hcard : S.card = b) :
    SimpleDigraph.Path integerLattice where
  vertices := pathVerticesList a S
  nonempty := pathVerticesList_nonempty a S
  arcs_valid := by
    intro i hi
    rw [pathVerticesList_length] at hi
    have hi' : i < a := by omega
    simp only [List.get_eq_getElem]
    have h1 : i < a + 1 := by omega
    have h2 : i + 1 < a + 1 := hi
    rw [pathVerticesList_getElem a S i h1, pathVerticesList_getElem a S (i + 1) h2]
    exact vertexAtPos_arc a S ⟨i, hi'⟩

private lemma eastStepsToPath_start (a b : ℕ) (S : Finset (Fin a)) (hcard : S.card = b) :
    (eastStepsToPath a b S hcard).start = (0, -(a : ℤ)) := by
  simp only [eastStepsToPath, SimpleDigraph.Path.start, List.head_eq_getElem]
  have h : 0 < a + 1 := Nat.zero_lt_succ a
  rw [pathVerticesList_getElem a S 0 h]
  exact vertexAtPos_zero a S

private lemma eastStepsToPath_finish (a b : ℕ) (S : Finset (Fin a)) (hcard : S.card = b) :
    (eastStepsToPath a b S hcard).finish = ((b : ℤ), -(b : ℤ)) := by
  simp only [eastStepsToPath, SimpleDigraph.Path.finish]
  have hne : pathVerticesList a S ≠ [] := pathVerticesList_nonempty a S
  rw [List.getLast_eq_getElem]
  simp only [pathVerticesList, List.length_ofFn, List.getElem_ofFn]
  have h : a + 1 - 1 = a := by omega
  simp only [h, vertexAtPos, eastStepCount]
  have hfilter : S.filter (fun j => j.val < a) = S := by
    ext j; simp only [Finset.mem_filter, and_iff_left j.isLt]
  simp only [hfilter, hcard]
  ring_nf

/-- The length of eastStepsToPath is a + 1 -/
private lemma eastStepsToPath_length (a b : ℕ) (S : Finset (Fin a)) (hcard : S.card = b) :
    (eastStepsToPath a b S hcard).vertices.length = a + 1 := by
  simp only [eastStepsToPath, pathVerticesList_length]

/-- For an arc in the integer lattice, the x-coordinate change is 0 or 1. -/
private lemma integerLattice_arc_x_diff (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    v.1 - u.1 = 0 ∨ v.1 - u.1 = 1 := by
  rcases h with ⟨hx, _⟩ | ⟨hx, _⟩
  · right; omega
  · left; omega

/-- Telescoping sum: ∑ (f(i+1) - f(i)) = f(n) - f(0). -/
private lemma sum_range_telescope' (n : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ m ih => 
    rw [Finset.sum_range_succ, ih]
    ring

/-- When consecutive differences are 0 or 1, the count of 1s equals the total change. -/
private lemma count_ones_eq_sum' (n b : ℕ) (f : ℕ → ℤ) 
    (hdiff : ∀ i < n, f (i + 1) - f i = 0 ∨ f (i + 1) - f i = 1)
    (hfirst : f 0 = 0) (hlast : f n = (b : ℤ)) :
    ((Finset.range n).filter (fun i => f (i + 1) = f i + 1)).card = b := by
  have h1 : ((Finset.range n).filter (fun i => f (i + 1) = f i + 1)).card = 
            ∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then 1 else 0 := by
    rw [Finset.card_filter]
  have h2 : ∀ i ∈ Finset.range n, (if f (i + 1) = f i + 1 then (1 : ℤ) else 0) = f (i + 1) - f i := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rcases hdiff i hi' with h | h
    · have hne : f (i + 1) ≠ f i + 1 := by omega
      simp only [hne, ↓reduceIte, h]
    · have heq : f (i + 1) = f i + 1 := by omega
      simp only [heq, ↓reduceIte]; ring
  have h3 : (∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then (1 : ℤ) else 0) = 
            ∑ i ∈ Finset.range n, (f (i + 1) - f i) := by
    apply Finset.sum_congr rfl h2
  have h4 : (∑ i ∈ Finset.range n, (f (i + 1) - f i)) = (b : ℤ) := by
    rw [sum_range_telescope', hlast, hfirst]; ring
  have h5 : (∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then (1 : ℤ) else 0) = (b : ℤ) := h3.trans h4
  have h6 : (↑(∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then (1 : ℕ) else 0) : ℤ) = 
            ∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then (1 : ℤ) else 0 := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [h1]
  have h7 : (↑(∑ i ∈ Finset.range n, if f (i + 1) = f i + 1 then (1 : ℕ) else 0) : ℤ) = (b : ℤ) := by
    rw [h6, h5]
  exact Int.ofNat_inj.mp h7

/-- Extract the set of east-step indices from a path.
    For a path p from (0, -a) to (b, -b), step i is east iff x increases at step i. -/
private noncomputable def pathToEastSteps (a : ℕ) (p : SimpleDigraph.Path integerLattice) 
    (hlen : p.vertices.length = a + 1) : Finset (Fin a) :=
  Finset.univ.filter fun i => 
    let hi : i.val + 1 < p.vertices.length := by rw [hlen]; omega
    (p.vertices.get ⟨i.val + 1, hi⟩).1 = (p.vertices.get ⟨i.val, Nat.lt_of_succ_lt hi⟩).1 + 1

/-- The east-step set has cardinality b for a path from (0, -a) to (b, -b) -/
private lemma pathToEastSteps_card (a b : ℕ) (p : SimpleDigraph.Path integerLattice)
    (hstart : p.start = (0, -(a : ℤ))) (hfinish : p.finish = ((b : ℤ), -(b : ℤ)))
    (hlen : p.vertices.length = a + 1) :
    (pathToEastSteps a p hlen).card = b := by
  -- Define f(i) = x-coordinate of vertex i
  let f : ℕ → ℤ := fun i => 
    if h : i < p.vertices.length then (p.vertices.get ⟨i, h⟩).1 else 0
  -- Verify f(0) = 0
  have hf0 : f 0 = 0 := by
    simp only [f]
    have h0 : 0 < p.vertices.length := by rw [hlen]; omega
    simp only [h0, ↓reduceDIte]
    have heq : (p.vertices.get ⟨0, h0⟩).1 = p.start.1 := by
      simp [SimpleDigraph.Path.start, List.head_eq_getElem]
    rw [heq, hstart]
  -- Verify f(a) = b
  have hfa : f a = (b : ℤ) := by
    simp only [f]
    have ha : a < p.vertices.length := by rw [hlen]; omega
    simp only [ha, ↓reduceDIte]
    have h_last : p.vertices.get ⟨a, ha⟩ = p.finish := by
      simp only [SimpleDigraph.Path.finish, List.getLast_eq_getElem]
      congr 1
      simp only [hlen, Fin.ext_iff]
      omega
    rw [h_last, hfinish]
  -- Verify consecutive differences are 0 or 1
  have hdiff : ∀ i < a, f (i + 1) - f i = 0 ∨ f (i + 1) - f i = 1 := by
    intro i hi
    simp only [f]
    have hi1 : i + 1 < p.vertices.length := by rw [hlen]; omega
    have hi0 : i < p.vertices.length := Nat.lt_of_succ_lt hi1
    simp only [hi1, hi0, ↓reduceDIte]
    exact integerLattice_arc_x_diff _ _ (p.arcs_valid i hi1)
  -- Apply count_ones_eq_sum'
  have h := count_ones_eq_sum' a b f hdiff hf0 hfa
  -- Convert from Finset.range to Finset.univ (Fin a)
  have h_card_eq : (pathToEastSteps a p hlen).card = 
      ((Finset.range a).filter (fun i => f (i + 1) = f i + 1)).card := by
    simp only [pathToEastSteps]
    rw [Finset.card_filter, Finset.card_filter]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < a := Finset.mem_range.mp hi
    simp only [f]
    have hi1 : i + 1 < p.vertices.length := by rw [hlen]; omega
    have hi0 : i < p.vertices.length := Nat.lt_of_succ_lt hi1
    simp only [hi1, hi0, ↓reduceDIte, hi', ↓reduceDIte]
  rw [h_card_eq, h]

/-- Round-trip: pathToEastSteps (eastStepsToPath S) = S -/
private lemma pathToEastSteps_eastStepsToPath (a b : ℕ) (S : Finset (Fin a)) (hcard : S.card = b) :
    pathToEastSteps a (eastStepsToPath a b S hcard) (eastStepsToPath_length a b S hcard) = S := by
  ext i
  simp only [pathToEastSteps, Finset.mem_filter, Finset.mem_univ, true_and]
  -- We need to show: step i is east in eastStepsToPath iff i ∈ S
  -- The vertices of eastStepsToPath are given by vertexAtPos
  have hlen : (eastStepsToPath a b S hcard).vertices.length = a + 1 := eastStepsToPath_length a b S hcard
  have hi1 : i.val + 1 < (eastStepsToPath a b S hcard).vertices.length := by rw [hlen]; omega
  have hi0 : i.val < (eastStepsToPath a b S hcard).vertices.length := Nat.lt_of_succ_lt hi1
  -- Get the vertices
  have hget0 : (eastStepsToPath a b S hcard).vertices.get ⟨i.val, hi0⟩ = vertexAtPos a S i.val := by
    simp only [eastStepsToPath]
    have h1 : i.val < a + 1 := by omega
    have := pathVerticesList_getElem a S i.val h1
    convert this using 1
  have hget1 : (eastStepsToPath a b S hcard).vertices.get ⟨i.val + 1, hi1⟩ = vertexAtPos a S (i.val + 1) := by
    simp only [eastStepsToPath]
    have h2 : i.val + 1 < a + 1 := by rw [hlen] at hi1; exact hi1
    have := pathVerticesList_getElem a S (i.val + 1) h2
    convert this using 1
  rw [hget0, hget1]
  -- Now use the definition of vertexAtPos
  simp only [vertexAtPos, eastStepCount]
  constructor
  · -- If x increases, then i ∈ S
    intro hx
    -- x at i+1 minus x at i = 1 means i ∈ S
    have hfilter_i1 : (S.filter (fun j => j.val < i.val + 1)).card = 
                      (S.filter (fun j => j.val < i.val)).card + if i ∈ S then 1 else 0 := by
      by_cases hi : i ∈ S
      · simp only [hi, ↓reduceIte]
        have heq : S.filter (fun j => j.val < i.val + 1) = insert i (S.filter (fun j => j.val < i.val)) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · intro ⟨hj, hlt⟩
            by_cases hji : j = i
            · left; exact hji
            · right; exact ⟨hj, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) (fun h => hji (Fin.ext h))⟩
          · intro h; rcases h with rfl | ⟨hj, hlt⟩
            · exact ⟨hi, Nat.lt_succ_self _⟩
            · exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
        rw [heq]
        have hnotmem : i ∉ S.filter (fun j => j.val < i.val) := by
          simp only [Finset.mem_filter, not_and, not_lt]; intro _; exact le_refl _
        rw [Finset.card_insert_eq_ite, ite_eq_right hnotmem]
      · simp only [hi, ↓reduceIte, add_zero]
        congr 1; ext j; simp only [Finset.mem_filter]
        constructor
        · intro ⟨hj, hlt⟩
          constructor
          · exact hj
          · by_cases hji : j.val = i.val
            · exfalso; have : j = i := Fin.ext hji; rw [this] at hj; exact hi hj
            · exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hji
        · intro ⟨hj, hlt⟩; exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
    -- From hx, we have that the x-coordinate increased by 1
    have hx' : (S.filter (fun j => j.val < i.val + 1)).card = 
               (S.filter (fun j => j.val < i.val)).card + 1 := by
      have := hx
      push_cast at this
      omega
    rw [hfilter_i1] at hx'
    by_cases hi : i ∈ S
    · exact hi
    · simp only [hi, ↓reduceIte, add_zero] at hx'; omega
  · -- If i ∈ S, then x increases
    intro hi
    have hfilter : (S.filter (fun j => j.val < i.val + 1)).card = 
                   (S.filter (fun j => j.val < i.val)).card + 1 := by
      have heq : S.filter (fun j => j.val < i.val + 1) = insert i (S.filter (fun j => j.val < i.val)) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · intro ⟨hj, hlt⟩
          by_cases hji : j = i
          · left; exact hji
          · right; exact ⟨hj, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) (fun h => hji (Fin.ext h))⟩
        · intro h; rcases h with rfl | ⟨hj, hlt⟩
          · exact ⟨hi, Nat.lt_succ_self _⟩
          · exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
      rw [heq]
      have hnotmem : i ∉ S.filter (fun j => j.val < i.val) := by
        simp only [Finset.mem_filter, not_and, not_lt]; intro _; exact le_refl _
      rw [Finset.card_insert_eq_ite, ite_eq_right hnotmem]
    simp only [hfilter]
    push_cast
    ring

/-- Path length for paths from (0, -a) to (b, -b) is a + 1 -/
private lemma path_length_from_endpoints (a b : ℕ) (p : SimpleDigraph.Path integerLattice)
    (hstart : p.start = (0, -(a : ℤ))) (hfinish : p.finish = ((b : ℤ), -(b : ℤ))) :
    p.vertices.length = a + 1 := by
  have h := integerLattice_path_length_eq p
  rw [hstart, hfinish] at h
  omega

/-- The x-coordinate at position i equals the number of east steps before i -/
private lemma path_x_coord_eq_eastSteps (a _b : ℕ) (p : SimpleDigraph.Path integerLattice)
    (hstart : p.start = (0, -(a : ℤ))) (hlen : p.vertices.length = a + 1) (i : ℕ) 
    (hi : i < p.vertices.length) :
    (p.vertices[i]).1 = ((pathToEastSteps a p hlen).filter (fun j => j.val < i)).card := by
  induction i with
  | zero =>
    have heq : p.vertices[0] = p.start := by
      simp [SimpleDigraph.Path.start, List.head_eq_getElem]
    rw [heq, hstart]
    have hempty : (pathToEastSteps a p hlen).filter (fun j => j.val < 0) = ∅ := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · intro ⟨_, hlt⟩; exact (Nat.not_lt_zero _ hlt).elim
      · simp
    simp only [hempty, Finset.card_empty, CharP.cast_eq_zero]
  | succ k ih =>
    have hk : k < p.vertices.length := Nat.lt_of_succ_lt hi
    specialize ih hk
    -- x at k+1 = x at k + (1 if step k is east, 0 otherwise)
    have harc := p.arcs_valid k hi
    rcases integerLattice_arc_x_diff _ _ harc with hstep | hstep
    · -- North step: x stays the same
      have hx_same : (p.vertices[k + 1]).1 = (p.vertices[k]).1 := by
        simp only [List.get_eq_getElem] at hstep; omega
      have hfilter_same : ((pathToEastSteps a p hlen).filter (fun j => j.val < k + 1)).card = 
                          ((pathToEastSteps a p hlen).filter (fun j => j.val < k)).card := by
        congr 1; ext j; simp only [Finset.mem_filter]
        have hkk : k < a := by omega
        constructor
        · intro ⟨hj, hlt⟩
          constructor
          · exact hj
          · by_cases hjk : j.val = k
            · -- j = k means step k is east, but we have north step
              exfalso
              simp only [pathToEastSteps, Finset.mem_filter, Finset.mem_univ, true_and] at hj
              have hj1 : j.val + 1 < p.vertices.length := by rw [hlen]; omega
              have hj' : (p.vertices[j.val + 1]).1 = (p.vertices[j.val]).1 + 1 := by
                convert hj using 2
              have hk1 : k + 1 < p.vertices.length := hi
              have : (p.vertices[k + 1]).1 = (p.vertices[k]).1 + 1 := by
                have hjk' : j.val = k := hjk
                simp only [hjk'] at hj'
                exact hj'
              omega
            · exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hjk
        · intro ⟨hj, hlt⟩; exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
      rw [hx_same, ih, hfilter_same]
    · -- East step: x increases by 1
      have hx_inc : (p.vertices[k + 1]).1 = (p.vertices[k]).1 + 1 := by
        simp only [List.get_eq_getElem] at hstep; omega
      have hkk : k < a := by omega
      have hk_in : (⟨k, hkk⟩ : Fin a) ∈ pathToEastSteps a p hlen := by
        simp only [pathToEastSteps, Finset.mem_filter, Finset.mem_univ, true_and]
        convert hx_inc using 2
      have hfilter_inc : ((pathToEastSteps a p hlen).filter (fun j => j.val < k + 1)).card = 
                         ((pathToEastSteps a p hlen).filter (fun j => j.val < k)).card + 1 := by
        have heq : (pathToEastSteps a p hlen).filter (fun j => j.val < k + 1) = 
                   insert ⟨k, hkk⟩ ((pathToEastSteps a p hlen).filter (fun j => j.val < k)) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff]
          constructor
          · intro ⟨hj, hlt⟩
            by_cases hjk : j.val = k
            · left; exact hjk
            · right; exact ⟨hj, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hjk⟩
          · intro h; rcases h with rfl | ⟨hj, hlt⟩
            · exact ⟨hk_in, Nat.lt_succ_self _⟩
            · exact ⟨hj, Nat.lt_succ_of_lt hlt⟩
        rw [heq]
        have hnotmem : (⟨k, hkk⟩ : Fin a) ∉ (pathToEastSteps a p hlen).filter (fun j => j.val < k) := by
          simp only [Finset.mem_filter, not_and, not_lt]; intro _; exact le_refl _
        rw [Finset.card_insert_eq_ite, ite_eq_right hnotmem]
      rw [hx_inc, ih, hfilter_inc]
      push_cast; ring

/-- Round-trip: eastStepsToPath (pathToEastSteps p) produces a path with the same vertices -/
private lemma eastStepsToPath_pathToEastSteps_vertices (a b : ℕ) (p : SimpleDigraph.Path integerLattice)
    (hstart : p.start = (0, -(a : ℤ))) (_hfinish : p.finish = ((b : ℤ), -(b : ℤ)))
    (hlen : p.vertices.length = a + 1) (hcard : (pathToEastSteps a p hlen).card = b) :
    (eastStepsToPath a b (pathToEastSteps a p hlen) hcard).vertices = p.vertices := by
  -- Both paths have the same length
  have hlen' : (eastStepsToPath a b (pathToEastSteps a p hlen) hcard).vertices.length = a + 1 := 
    eastStepsToPath_length a b (pathToEastSteps a p hlen) hcard
  -- Show vertices are equal by showing each vertex is equal
  apply List.ext_getElem
  · rw [hlen', hlen]
  · intro i hi1 hi2
    -- hi1 : i < (eastStepsToPath ...).vertices.length
    -- hi2 : i < p.vertices.length
    have hi1' : i < a + 1 := by rw [hlen'] at hi1; exact hi1
    -- Get the i-th vertex of eastStepsToPath
    have hget_east : (eastStepsToPath a b (pathToEastSteps a p hlen) hcard).vertices[i] = 
                     vertexAtPos a (pathToEastSteps a p hlen) i := by
      simp only [eastStepsToPath]
      have := pathVerticesList_getElem a (pathToEastSteps a p hlen) i hi1'
      convert this using 1
    rw [hget_east]
    -- Show vertexAtPos matches p.vertices[i]
    simp only [vertexAtPos, eastStepCount]
    -- Use the extracted lemma for x-coordinate
    have hx := path_x_coord_eq_eastSteps a b p hstart hlen i hi2
    have hy : (p.vertices[i]).2 = 
              -(a : ℤ) + ((i : ℤ) - ((pathToEastSteps a p hlen).filter (fun j => j.val < i)).card) := by
      have hsum := integerLattice_path_vertex_sum p i hi2
      rw [hstart] at hsum
      simp only [List.get_eq_getElem] at hsum
      omega
    ext
    · exact hx.symm
    · exact hy.symm

/-- Bijection between paths from (0, -a) to (b, -b) and b-element subsets of Fin a.

    This encapsulates the key combinatorial bijection from Proposition prop.lgv.1-paths.ct:
    - A path from (0, -a) to (b, -b) has exactly a steps (coordinate sum goes from -a to 0)
    - A path has exactly b east-steps (x-coordinate goes from 0 to b)
    - A path is uniquely determined by which of its a steps are east-steps
    - This gives a bijection to b-element subsets of Fin a -/
noncomputable def paths_equiv_powersetCard (a b : ℕ) :
    (pathsFromTo integerLattice integerLattice_pathFinite (0, -(a : ℤ)) (b, -(b : ℤ))) ≃
      (Finset.powersetCard b (Finset.univ : Finset (Fin a))) := by
  -- The bijection: path ↔ set of east-step indices
  -- Forward: p ↦ {i : Fin a | step i is east}
  -- Backward: S ↦ path where step i is east iff i ∈ S
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  case toFun =>
    intro ⟨p, hp⟩
    simp only [pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
    have hstart := hp.1
    have hfinish := hp.2
    have hlen := path_length_from_endpoints a b p hstart hfinish
    have hcard := pathToEastSteps_card a b p hstart hfinish hlen
    exact ⟨pathToEastSteps a p hlen, by simp [Finset.mem_powersetCard, hcard]⟩
  case invFun =>
    intro ⟨S, hS⟩
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS
    have hstart := eastStepsToPath_start a b S hS
    have hfinish := eastStepsToPath_finish a b S hS
    exact ⟨eastStepsToPath a b S hS, by simp [pathsFromTo, hstart, hfinish]⟩
  case left_inv =>
    intro ⟨p, hp⟩
    simp only [pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hp
    have hstart := hp.1
    have hfinish := hp.2
    have hlen := path_length_from_endpoints a b p hstart hfinish
    have hcard := pathToEastSteps_card a b p hstart hfinish hlen
    simp only [Subtype.mk.injEq]
    -- Need to show: eastStepsToPath (pathToEastSteps p) = p
    have hvert := eastStepsToPath_pathToEastSteps_vertices a b p hstart hfinish hlen hcard
    -- Paths are equal iff their vertices are equal
    cases p
    simp only [eastStepsToPath] at hvert ⊢
    congr
  case right_inv =>
    intro ⟨S, hS⟩
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS
    simp only [Subtype.mk.injEq]
    -- Need to show: pathToEastSteps (eastStepsToPath S) = S
    exact pathToEastSteps_eastStepsToPath a b S hS

/-- The number of paths from (0, -a) to (b, -b) in the integer lattice equals C(a, b).
    This follows from Proposition prop.lgv.1-paths.ct. -/
theorem paths_count_eq_choose (a b : ℕ) :
    (pathsFromTo integerLattice integerLattice_pathFinite (0, -(a : ℤ)) (b, -(b : ℤ))).card =
      a.choose b := by
  rw [Finset.card_eq_of_equiv (paths_equiv_powersetCard a b)]
  simp [Finset.card_powersetCard]

/-!
#### Unit weight infrastructure for binomial determinant proof

The unit weight function assigns weight 1 to every arc. With this weight:
- pathWeight p = 1 for any path p
- pathTupleWeight ps = 1 for any path tuple ps
- pathWeightSum = cardinality of paths
- nipatWeightSum = cardinality of nipats ≥ 0
-/

/-- The unit arc weight function assigns 1 to every arc -/
noncomputable def unitArcWeight : ArcWeight integerLattice ℤ :=
  fun _ _ _ => 1

/-- With unit weight, pathWeightAux always returns 1 -/
private theorem pathWeightAux_unitArcWeight (vertices : List (ℤ × ℤ))
    (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      integerLattice.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) :
    pathWeightAux unitArcWeight vertices arcs_valid = 1 := by
  induction vertices with
  | nil => rfl
  | cons v vs ih =>
    cases vs with
    | nil => rfl
    | cons v' vs' =>
      simp only [pathWeightAux, unitArcWeight, one_mul]
      apply ih

/-- With unit weight, pathWeight is always 1 -/
theorem pathWeight_unitArcWeight (p : SimpleDigraph.Path integerLattice) :
    pathWeight unitArcWeight p = 1 := by
  unfold pathWeight
  exact pathWeightAux_unitArcWeight p.vertices p.arcs_valid

/-- With unit weight, pathTupleWeight is always 1 -/
theorem pathTupleWeight_unitArcWeight {k : ℕ} (ps : Fin k → SimpleDigraph.Path integerLattice) :
    pathTupleWeight unitArcWeight ps = 1 := by
  simp only [pathTupleWeight, pathWeight_unitArcWeight, Finset.prod_const_one]

/-- With unit weight, pathWeightSum equals cardinality of paths -/
theorem pathWeightSum_unitArcWeight (u v : ℤ × ℤ) :
    pathWeightSum integerLattice_pathFinite unitArcWeight u v =
    (pathsFromTo integerLattice integerLattice_pathFinite u v).card := by
  simp only [pathWeightSum, pathWeight_unitArcWeight, Finset.sum_const]
  simp

/-- The binomial matrix equals pathWeightMatrix with unit weight -/
theorem binom_matrix_eq_pathWeightMatrix {k : ℕ} (a b : Fin k → ℕ) :
    (Matrix.of fun i j => ((a i).choose (b j) : ℤ)) =
    pathWeightMatrix integerLattice_pathFinite unitArcWeight (binomLatticeA a) (binomLatticeB b) := by
  ext i j
  simp only [Matrix.of_apply, pathWeightMatrix]
  rw [pathWeightSum_unitArcWeight]
  simp only [binomLatticeA, binomLatticeB]
  rw [paths_count_eq_choose]

/-- With unit weight, nipatWeightSum equals cardinality of nipats -/
theorem nipatWeightSum_unitArcWeight {k : ℕ} (A B : kVertex (ℤ × ℤ) k) (σ : Equiv.Perm (Fin k)) :
    nipatWeightSum integerLattice_pathFinite unitArcWeight A B σ =
    (nipatFinset integerLattice_pathFinite A B).card := by
  simp only [nipatWeightSum, pathTupleWeight_unitArcWeight, Finset.sum_const]
  simp

/-- nipatWeightSum with unit weight is nonnegative -/
theorem nipatWeightSum_unitArcWeight_nonneg {k : ℕ} (A B : kVertex (ℤ × ℤ) k) (σ : Equiv.Perm (Fin k)) :
    0 ≤ nipatWeightSum integerLattice_pathFinite unitArcWeight A B σ := by
  rw [nipatWeightSum_unitArcWeight]
  exact Int.natCast_nonneg _

set_option backward.isDefEq.respectTransparency false in
/-- The ipatWithPermFinset can be decomposed as a sigma type over permutations.
    This is the ipat analogue of the decomposition used for nipats. -/
theorem ipatWithPermFinset_eq_sigma {k : ℕ} (A B : kVertex (ℤ × ℤ) k) :
    ipatWithPermFinset integerLattice_pathFinite A B = 
    Finset.univ.sigma (fun σ => ipatFinset integerLattice_pathFinite A (permuteKVertex σ B)) := by
  ext ⟨σ, pt⟩
  constructor
  · intro h
    rw [Finset.mem_sigma]
    constructor
    · exact Finset.mem_univ σ
    · rw [mem_ipatFinset_iff]
      exact (mem_ipatWithPermFinset_iff integerLattice_pathFinite ⟨σ, pt⟩).mp h
  · intro h
    rw [Finset.mem_sigma] at h
    rw [mem_ipatWithPermFinset_iff]
    exact (mem_ipatFinset_iff integerLattice_pathFinite pt).mp h.2

/-- The sum over ipatWithPermFinset equals the sum over permutations of ipat counts.
    With unit weight, pathTupleWeight = 1, so this becomes a signed count. -/
theorem sum_ipatWithPerm_eq_sum_ipatFinset_card {k : ℕ} (A B : kVertex (ℤ × ℤ) k) :
    ∑ sp ∈ ipatWithPermFinset integerLattice_pathFinite A B, 
      (Equiv.Perm.sign sp.1 : ℤ) * pathTupleWeight unitArcWeight sp.2.paths =
    ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) * 
      (ipatFinset integerLattice_pathFinite A (permuteKVertex σ B)).card := by
  have hS := ipatWithPermFinset_eq_sigma A B
  rw [hS]
  let f : (Σ σ : Equiv.Perm (Fin k), PathTuple integerLattice k A (permuteKVertex σ B)) → ℤ := 
    fun sp => (Equiv.Perm.sign sp.1 : ℤ) * pathTupleWeight unitArcWeight sp.2.paths
  show ∑ sp ∈ Finset.univ.sigma _, f sp = _
  rw [Finset.sum_sigma]
  congr 1
  ext σ
  simp only [f, pathTupleWeight_unitArcWeight, mul_one, Finset.sum_const]
  ring

/-- The signed sum of ipat counts over all permutations is zero.
    This is the counting version of `sum_ipatWithPerm_signed_weight_eq_zero`.
    
    The proof uses the sign-reversing involution on intersecting path tuples:
    for each ipat (σ, pt), swap tails at the first intersection point to get
    (σ * swap i j, pt'), which has opposite sign but the same weight (= 1).
    
    This lemma is the key step needed to complete LGV1.lean's `lgv_involution_cancellation`. -/
theorem sum_signed_ipatFinset_card_eq_zero {k : ℕ} (A B : kVertex (ℤ × ℤ) k) :
    ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) * 
      (ipatFinset integerLattice_pathFinite A (permuteKVertex σ B)).card = 0 := by
  rw [← sum_ipatWithPerm_eq_sum_ipatFinset_card]
  exact sum_ipatWithPerm_signed_weight_eq_zero integerLattice_pathFinite integerLattice_acyclic 
    unitArcWeight A B

theorem binom_det_nonneg {k : ℕ} (a b : Fin k → ℕ)
    (ha : ∀ i j : Fin k, i ≤ j → a j ≤ a i)
    (hb : ∀ i j : Fin k, i ≤ j → b j ≤ b i) :
    0 ≤ (Matrix.of fun i j => (a i).choose (b j) : Matrix (Fin k) (Fin k) ℤ).det := by
  match k with
  | 0 => exact binom_det_nonneg_zero a b ha hb
  | 1 => exact binom_det_nonneg_one a b ha hb
  | 2 => exact binom_det_nonneg_two a b ha hb
  | _ + 3 =>
    -- General case: Use the LGV machinery
    -- Define the lattice points
    let A := binomLatticeA a
    let B := binomLatticeB b
    -- Verify sorting conditions
    have hxA : xDecreasing A := binomLatticeA_xDecreasing a
    have hyA : yIncreasing A := binomLatticeA_yIncreasing a ha
    have hxB : xDecreasing B := binomLatticeB_xDecreasing b hb
    have hyB : yIncreasing B := binomLatticeB_yIncreasing b hb
    -- Step 1: Show binomial matrix = pathWeightMatrix with unit weight
    have heq : (Matrix.of fun i j => ((a i).choose (b j) : ℤ)) =
        pathWeightMatrix integerLattice_pathFinite unitArcWeight A B :=
      binom_matrix_eq_pathWeightMatrix a b
    rw [heq]
    -- Step 2: Apply lgv_nonpermutable to get det = nipatWeightSum
    rw [lgv_nonpermutable unitArcWeight A B hxA hyA hxB hyB]
    -- Step 3: nipatWeightSum with unit weight is nonnegative
    exact nipatWeightSum_unitArcWeight_nonneg A B (Equiv.refl (Fin (_ + 3)))

/-!
### Catalan Hankel Determinant (Corollary cor.lgv.catalan-hankel-det-0)

The Hankel determinant of Catalan numbers equals 1.

We use Mathlib's `catalan` function from `Mathlib.Combinatorics.Enumerative.Catalan`.
The Catalan numbers are defined by cₙ = C(2n,n)/(n+1), and the Hankel matrix
has entry (i,j) equal to c_{i+j}. This is a famous result that can be proven
using the LGV lemma with Dyck paths.
-/

/-- The Catalan Hankel matrix of size k×k, where entry (i,j) is c_{i+j}.
    Uses Mathlib's `catalan` function directly. -/
def catalanHankelMatrix (k : ℕ) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j => (catalan ((i : ℕ) + (j : ℕ)) : ℤ)

/-- The Catalan Hankel matrix is symmetric (since c_{i+j} = c_{j+i}). -/
theorem catalanHankelMatrix_symm (k : ℕ) (i j : Fin k) :
    catalanHankelMatrix k i j = catalanHankelMatrix k j i := by
  simp [catalanHankelMatrix, add_comm]

/-- The (0,0) entry of the Catalan Hankel matrix is 1 (= c₀). -/
theorem catalanHankelMatrix_zero_zero (k : ℕ) (hk : 0 < k) :
    catalanHankelMatrix k ⟨0, hk⟩ ⟨0, hk⟩ = 1 := by
  simp [catalanHankelMatrix, catalan_zero]

/-- Entry (i,j) of the Catalan Hankel matrix is catalan(i+j). -/
@[simp]
theorem catalanHankelMatrix_apply (k : ℕ) (i j : Fin k) :
    catalanHankelMatrix k i j = catalan ((i : ℕ) + (j : ℕ)) := by
  simp [catalanHankelMatrix]

/-- Catalan Hankel determinant for k=0: empty matrix has determinant 1. -/
theorem catalan_hankel_det_zero : (catalanHankelMatrix 0).det = 1 := by
  simp [catalanHankelMatrix, Matrix.det_isEmpty]

/-- Catalan Hankel determinant for k=1: 1×1 matrix [c₀] = [1], det = 1. -/
theorem catalan_hankel_det_one : (catalanHankelMatrix 1).det = 1 := by
  simp [catalanHankelMatrix, Matrix.det_unique, catalan_zero]

/-- Catalan Hankel determinant for k=2: 2×2 matrix [[c₀, c₁], [c₁, c₂]] = [[1, 1], [1, 2]].
    det = 1·2 - 1·1 = 1. -/
theorem catalan_hankel_det_two : (catalanHankelMatrix 2).det = 1 := by
  simp only [catalanHankelMatrix, Matrix.det_fin_two, Matrix.of_apply]
  native_decide

/-- Catalan Hankel determinant for k=3. -/
theorem catalan_hankel_det_three : (catalanHankelMatrix 3).det = 1 := by
  simp only [catalanHankelMatrix, Matrix.det_fin_three, Matrix.of_apply]
  native_decide

/-- Catalan Hankel determinant for k=4. -/
theorem catalan_hankel_det_four : (catalanHankelMatrix 4).det = 1 := by
  native_decide

/-- Catalan Hankel determinant for k=5. -/
theorem catalan_hankel_det_five : (catalanHankelMatrix 5).det = 1 := by
  native_decide

/-- Catalan Hankel determinant for k=6. -/
theorem catalan_hankel_det_six : (catalanHankelMatrix 6).det = 1 := by
  native_decide

/-- The explicit 7×7 Catalan Hankel matrix for native_decide.
    Using explicit matrix avoids timeout issues with `native_decide` on `catalanHankelMatrix 7`. -/
private def catalanHankelMatrix7 : Matrix (Fin 7) (Fin 7) ℤ := 
  ![![1, 1, 2, 5, 14, 42, 132],
    ![1, 2, 5, 14, 42, 132, 429],
    ![2, 5, 14, 42, 132, 429, 1430],
    ![5, 14, 42, 132, 429, 1430, 4862],
    ![14, 42, 132, 429, 1430, 4862, 16796],
    ![42, 132, 429, 1430, 4862, 16796, 58786],
    ![132, 429, 1430, 4862, 16796, 58786, 208012]]

private theorem catalanHankelMatrix_seven_eq : catalanHankelMatrix 7 = catalanHankelMatrix7 := by 
  native_decide

/-- Catalan Hankel determinant for k=7. -/
theorem catalan_hankel_det_seven : (catalanHankelMatrix 7).det = 1 := by
  rw [catalanHankelMatrix_seven_eq]
  native_decide

/-- The Dyck path digraph: vertices are ℤ × ℕ, arcs go (i,j) → (i+1, j+1) and (i,j) → (i+1, j-1).
    Used for counting Catalan numbers via Dyck paths.

    A Dyck path from (0,0) to (2n,0) corresponds to a balanced sequence of n up-steps
    and n down-steps that never goes below the x-axis. A Dyck path is a lattice path
    that stays on or above the x-axis, where each step goes either up-right or down-right. -/
def dyckDigraph : SimpleDigraph (ℤ × ℕ) where
  arc u v := (v.1 = u.1 + 1 ∧ v.2 = u.2 + 1) ∨
             (v.1 = u.1 + 1 ∧ v.2 + 1 = u.2 ∧ 0 < u.2)
  arc_irrefl := by
    intro ⟨x, y⟩
    simp only [not_or, not_and]
    constructor <;> omega

/-- Every arc in the Dyck digraph increases the first coordinate by 1 -/
lemma dyckDigraph_arc_fst (u v : ℤ × ℕ) (h : dyckDigraph.arc u v) : v.1 = u.1 + 1 := by
  rcases h with ⟨hfst, _⟩ | ⟨hfst, _, _⟩ <;> exact hfst

/-- Along a path in the Dyck digraph, the first coordinate increases by the index -/
lemma dyckDigraph_path_vertex_fst (p : SimpleDigraph.Path dyckDigraph) (i : ℕ) (hi : i < p.vertices.length) :
    (p.vertices.get ⟨i, hi⟩).1 = p.start.1 + i := by
  induction i with
  | zero =>
    simp only [CharP.cast_eq_zero, add_zero]
    unfold SimpleDigraph.Path.start
    rw [List.get_mk_zero hi]
  | succ j ih =>
    have hj : j < p.vertices.length := Nat.lt_of_succ_lt hi
    have hih := ih hj
    have harc := p.arcs_valid j hi
    have hfst := dyckDigraph_arc_fst _ _ harc
    simp only [Nat.cast_succ]
    omega

/-- Path length is determined by start and finish x-coordinates in the Dyck digraph -/
lemma dyckDigraph_path_length_eq (p : SimpleDigraph.Path dyckDigraph) :
    (p.vertices.length : ℤ) = p.finish.1 - p.start.1 + 1 := by
  have hne := p.nonempty
  have hlen : p.vertices.length ≥ 1 := List.length_pos_of_ne_nil hne
  have h0 : 0 < p.vertices.length := hlen
  have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
  have hstart := dyckDigraph_path_vertex_fst p 0 h0
  have hfinish := dyckDigraph_path_vertex_fst p (p.vertices.length - 1) hlast
  simp only [CharP.cast_eq_zero, add_zero] at hstart
  have hstart_eq : p.start = p.vertices.get ⟨0, h0⟩ := by
    unfold SimpleDigraph.Path.start
    rw [List.get_mk_zero h0]
  have hfinish_eq : p.finish = p.vertices.get ⟨p.vertices.length - 1, hlast⟩ := by
    unfold SimpleDigraph.Path.finish
    rw [List.getLast_eq_getElem]
    rfl
  rw [hstart_eq, hfinish_eq]
  rw [← hstart] at hfinish
  omega

/-- The second coordinate stays bounded along a path in the Dyck digraph -/
lemma dyckDigraph_path_snd_bounded (p : SimpleDigraph.Path dyckDigraph) (i : ℕ) (hi : i < p.vertices.length) :
    (p.vertices.get ⟨i, hi⟩).2 ≤ p.start.2 + i := by
  induction i with
  | zero =>
    simp only [add_zero]
    unfold SimpleDigraph.Path.start
    rw [List.get_mk_zero hi]
  | succ j ih =>
    have hj : j < p.vertices.length := Nat.lt_of_succ_lt hi
    have hih := ih hj
    have harc := p.arcs_valid j hi
    rcases harc with ⟨_, hsnd⟩ | ⟨_, hsnd, _⟩
    · -- Up step: y increases by 1
      omega
    · -- Down step: y decreases by 1
      omega

/-- Paths in the Dyck digraph are determined by their vertex list -/
private lemma dyckDigraph_path_ext (p q : SimpleDigraph.Path dyckDigraph)
    (h : p.vertices = q.vertices) : p = q := by
  cases p; cases q
  simp only [SimpleDigraph.Path.mk.injEq] at h ⊢
  exact h

/-- The Dyck digraph is path-finite.

    **Proof:** We show that paths from u to v are finite by:
    1. If v.1 < u.1, no paths exist (x-coordinate strictly increases along arcs)
    2. Otherwise, paths have fixed length n = v.1 - u.1 + 1
    3. The y-coordinate is bounded: 0 ≤ y ≤ u.2 + n at each vertex
    4. Each path is determined by its vertex sequence, which is a function Fin n → box
    5. Since box is finite and n is finite, there are finitely many such functions
    6. The map from paths to vertex sequences is injective, so paths are finite -/
theorem dyckDigraph_pathFinite : dyckDigraph.IsPathFinite := by
  intro u v
  by_cases h : v.1 < u.1
  · -- Case 1: No paths exist (would need to go backwards in x)
    convert Set.finite_empty
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hstart hfinish
    have hlen := dyckDigraph_path_length_eq p
    rw [hstart, hfinish] at hlen
    have hpos : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
    omega
  · -- Case 2: Paths exist but are finite
    push Not at h
    -- Define the path length
    let n := (v.1 - u.1 + 1).toNat
    -- Define the bounding box for the second coordinate
    -- The second coordinate stays between 0 and u.2 + n
    let maxY := u.2 + n
    let box : Finset (ℤ × ℕ) := (Finset.Icc u.1 v.1) ×ˢ (Finset.range (maxY + 1))
    -- Define the subtype of paths from u to v
    let S := {p : SimpleDigraph.Path dyckDigraph | p.start = u ∧ p.finish = v}
    -- Show S is finite by injecting into Fin n → box
    suffices Finite S by exact Set.finite_coe_iff.mpr this
    -- Define the injection: map each path to its vertex list as a function
    let f : S → (Fin n → box) := fun ⟨p, hp⟩ i =>
      let hi : i.val < p.vertices.length := by
        have hlen := dyckDigraph_path_length_eq p
        rw [hp.1, hp.2] at hlen
        simp only [n] at hlen ⊢
        have := i.isLt
        omega
      ⟨p.vertices.get ⟨i.val, hi⟩, by
        have hfst := dyckDigraph_path_vertex_fst p i.val hi
        have hsnd := dyckDigraph_path_snd_bounded p i.val hi
        rw [hp.1] at hfst hsnd
        simp only [box, maxY, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
        constructor
        · constructor
          · -- u.1 ≤ vertex.1
            simp only [hfst]
            omega
          · -- vertex.1 ≤ v.1
            simp only [hfst]
            have := i.isLt
            simp only [n] at this
            omega
        · -- vertex.2 < maxY + 1
          simp only [n] at hsnd ⊢
          omega⟩
    have hinj : Function.Injective f := by
      intro ⟨p, hp⟩ ⟨q, hq⟩ heq
      simp only [Subtype.mk.injEq, f] at heq ⊢
      apply dyckDigraph_path_ext
      apply List.ext_get
      · -- Lengths are equal (both determined by u and v)
        have hlenp := dyckDigraph_path_length_eq p
        have hlenq := dyckDigraph_path_length_eq q
        rw [hp.1, hp.2] at hlenp
        rw [hq.1, hq.2] at hlenq
        omega
      · -- Elements are equal at each position
        intro i hip hiq
        have heqi := congr_fun heq ⟨i, by
          have hlenp := dyckDigraph_path_length_eq p
          rw [hp.1, hp.2] at hlenp
          simp only [n]
          omega⟩
        simp only [Subtype.mk.injEq] at heqi
        exact heqi
    exact Finite.of_injective f hinj

/-- The Dyck digraph is acyclic -/
theorem dyckDigraph_acyclic : dyckDigraph.IsAcyclic := by
  intro p hcycle
  by_contra hne
  have hlen : p.vertices.length ≥ 2 := by
    rcases hlist : p.vertices with _ | ⟨v, vs⟩
    · exact absurd hlist p.nonempty
    · cases vs with
      | nil =>
        have hlen1 : p.vertices.length = 1 := by simp [hlist]
        exact absurd hlen1 hne
      | cons w ws => simp
  -- The start and finish vertices
  have hstart_idx : 0 < p.vertices.length := Nat.lt_of_lt_of_le (by omega : 0 < 2) hlen
  have hfinish_idx : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hstart_idx (by omega)
  -- Apply our helper lemma
  have h0 := dyckDigraph_path_vertex_fst p 0 hstart_idx
  have hn := dyckDigraph_path_vertex_fst p (p.vertices.length - 1) hfinish_idx
  -- start = vertices[0], finish = vertices[length - 1]
  have hstart_eq : p.start = p.vertices.get ⟨0, hstart_idx⟩ := by
    unfold SimpleDigraph.Path.start
    rw [List.get_mk_zero hstart_idx]
  have hfinish_eq : p.finish = p.vertices.get ⟨p.vertices.length - 1, hfinish_idx⟩ := by
    unfold SimpleDigraph.Path.finish
    rw [List.getLast_eq_getElem]
    rfl
  -- From hcycle: start = finish
  rw [hstart_eq, hfinish_eq] at hcycle
  -- So start.1 = finish.1
  have hfst_eq : (p.vertices.get ⟨0, hstart_idx⟩).1 = (p.vertices.get ⟨p.vertices.length - 1, hfinish_idx⟩).1 := by
    rw [hcycle]
  -- But from our lemmas:
  -- vertices[0].1 = start.1 + 0 = start.1
  -- vertices[n-1].1 = start.1 + (n-1)
  simp only [CharP.cast_eq_zero, add_zero] at h0
  -- So start.1 = start.1 + (n-1), meaning n-1 = 0, i.e., n = 1
  rw [hstart_eq] at h0 hn
  rw [hfst_eq] at h0
  have : (p.vertices.length - 1 : ℤ) = 0 := by omega
  have hlen1 : p.vertices.length = 1 := by omega
  exact hne hlen1

/-!
### Unit Arc Weight for Dyck Digraph

Infrastructure for connecting the Catalan Hankel matrix to the LGV lemma.
-/

/-- Unit arc weight for the Dyck digraph -/
noncomputable def dyckUnitArcWeight : ArcWeight dyckDigraph ℤ :=
  fun _ _ _ => 1

/-- Helper: path weight with unit weight is 1 -/
private theorem pathWeightAux_dyckUnitArcWeight (vertices : List (ℤ × ℕ))
    (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      dyckDigraph.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) :
    pathWeightAux dyckUnitArcWeight vertices arcs_valid = 1 := by
  induction vertices with
  | nil => simp [pathWeightAux]
  | cons v₀ rest ih =>
    cases rest with
    | nil => simp [pathWeightAux]
    | cons v₁ rest' =>
      simp only [pathWeightAux, dyckUnitArcWeight, one_mul]
      apply ih

/-- Path weight with unit weight is 1 -/
theorem pathWeight_dyckUnitArcWeight (p : SimpleDigraph.Path dyckDigraph) :
    pathWeight dyckUnitArcWeight p = 1 := by
  unfold pathWeight
  exact pathWeightAux_dyckUnitArcWeight p.vertices p.arcs_valid

/-- Path tuple weight with unit weight is 1 -/
theorem pathTupleWeight_dyckUnitArcWeight {k : ℕ} (ps : Fin k → SimpleDigraph.Path dyckDigraph) :
    pathTupleWeight dyckUnitArcWeight ps = 1 := by
  simp only [pathTupleWeight, pathWeight_dyckUnitArcWeight, Finset.prod_const_one]

/-- With unit weight, pathWeightSum equals cardinality of paths -/
theorem pathWeightSum_dyckUnitArcWeight (u v : ℤ × ℕ) :
    pathWeightSum dyckDigraph_pathFinite dyckUnitArcWeight u v =
    (pathsFromTo dyckDigraph dyckDigraph_pathFinite u v).card := by
  simp only [pathWeightSum, pathWeight_dyckUnitArcWeight, Finset.sum_const]
  simp

/-- With unit weight, nipatWeightSum equals cardinality of nipats -/
theorem nipatWeightSum_dyckUnitArcWeight {k : ℕ} (A B : kVertex (ℤ × ℕ) k) (σ : Equiv.Perm (Fin k)) :
    nipatWeightSum dyckDigraph_pathFinite dyckUnitArcWeight A B σ =
    (nipatFinset dyckDigraph_pathFinite A B).card := by
  simp only [nipatWeightSum, pathTupleWeight_dyckUnitArcWeight, Finset.sum_const]
  simp

/-- Convert a Dyck path to a list of DyckSteps.
    Each arc (x,y) → (x+1,y+1) becomes U, each arc (x,y) → (x+1,y-1) becomes D. -/
def dyckPathToSteps (p : SimpleDigraph.Path dyckDigraph) : List DyckStep :=
  (List.finRange (p.vertices.length - 1)).map fun ⟨i, hi⟩ =>
    have hi' : i + 1 < p.vertices.length := by omega
    let u := p.vertices.get ⟨i, Nat.lt_of_succ_lt hi'⟩
    let v := p.vertices.get ⟨i + 1, hi'⟩
    if v.2 = u.2 + 1 then DyckStep.U else DyckStep.D

/-- The step list has length = vertices.length - 1 = number of arcs. -/
lemma dyckPathToSteps_length (p : SimpleDigraph.Path dyckDigraph) :
    (dyckPathToSteps p).length = p.vertices.length - 1 := by
  simp [dyckPathToSteps]

set_option backward.isDefEq.respectTransparency false in
/-- Key lemma: the y-coordinate at position i equals #U - #D in the first i steps (as integers). -/
private lemma dyckPath_y_eq_count_diff_int (p : SimpleDigraph.Path dyckDigraph) (i : ℕ)
    (hi : i < p.vertices.length) (hstart : p.start = (0, 0)) :
    ((p.vertices.get ⟨i, hi⟩).2 : ℤ) =
      ((dyckPathToSteps p).take i).count DyckStep.U - ((dyckPathToSteps p).take i).count DyckStep.D := by
  induction i with
  | zero =>
    simp only [List.take_zero, List.count_nil, CharP.cast_eq_zero, sub_zero]
    unfold SimpleDigraph.Path.start at hstart
    have h0 : p.vertices.get ⟨0, hi⟩ = p.vertices.head p.nonempty := by
      rw [List.get_mk_zero hi]
    rw [h0, hstart]
    rfl
  | succ j ih =>
    have hj : j < p.vertices.length := Nat.lt_of_succ_lt hi
    have ihj := ih hj
    have harc := p.arcs_valid j hi
    have hsteps_len : j < (dyckPathToSteps p).length := by
      rw [dyckPathToSteps_length]; omega
    have hstep_j : (dyckPathToSteps p)[j] =
        if (p.vertices.get ⟨j + 1, hi⟩).2 = (p.vertices.get ⟨j, hj⟩).2 + 1
        then DyckStep.U else DyckStep.D := by
      unfold dyckPathToSteps
      simp only [List.getElem_map, List.getElem_finRange]
      rfl
    unfold dyckDigraph at harc
    simp only at harc
    rcases harc with ⟨_, hy_up⟩ | ⟨_, hy_down, _⟩
    · have hU : (dyckPathToSteps p)[j] = DyckStep.U := by
        rw [hstep_j]; simp only [hy_up, ↓reduceIte]
      rw [List.take_succ_eq_append_getElem hsteps_len, List.count_append, List.count_append]
      simp only [List.count_singleton, hU]
      have h1 : (if (DyckStep.U == DyckStep.U) = true then 1 else 0) = 1 := by native_decide
      have h2 : (if (DyckStep.U == DyckStep.D) = true then 1 else 0) = 0 := by native_decide
      rw [h1, h2, add_zero, hy_up]; push_cast; omega
    · have heq : (p.vertices.get ⟨j, Nat.lt_of_succ_lt hi⟩).2 = (p.vertices.get ⟨j, hj⟩).2 := rfl
      rw [heq] at hy_down
      have hD : (dyckPathToSteps p)[j] = DyckStep.D := by
        rw [hstep_j]
        have hne : (p.vertices.get ⟨j + 1, hi⟩).2 ≠ (p.vertices.get ⟨j, hj⟩).2 + 1 := by omega
        simp only [hne, ↓reduceIte]
      rw [List.take_succ_eq_append_getElem hsteps_len, List.count_append, List.count_append]
      simp only [List.count_singleton, hD]
      have h1 : (if (DyckStep.D == DyckStep.U) = true then 1 else 0) = 0 := by native_decide
      have h2 : (if (DyckStep.D == DyckStep.D) = true then 1 else 0) = 1 := by native_decide
      rw [h1, h2, add_zero]; push_cast; omega

/-- Convert a Dyck path to a DyckWord.
    Each arc (x,y) → (x+1,y+1) becomes U, each arc (x,y) → (x+1,y-1) becomes D.

    **Note:** This definition requires substantial infrastructure to prove well-formedness.
    The key properties are:
    - count_U_eq_count_D: follows from start.2 = 0 = finish.2
    - count_D_le_count_U: follows from y ≥ 0 throughout the path (Dyck condition) -/
def dyckPathToWord (p : SimpleDigraph.Path dyckDigraph) (hstart : p.start = (0, 0))
    (hfinish : p.finish.2 = 0) : DyckWord where
  toList := dyckPathToSteps p
  count_U_eq_count_D := by
    -- The number of U steps equals the number of D steps because we start and end at y = 0
    -- Each U increases y by 1, each D decreases y by 1
    -- So #U - #D = final_y - initial_y = 0 - 0 = 0
    have hlen : p.vertices.length ≥ 1 := List.length_pos_of_ne_nil p.nonempty
    have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
    have hfinish_eq : p.finish = p.vertices.get ⟨p.vertices.length - 1, hlast⟩ := by
      unfold SimpleDigraph.Path.finish
      rw [List.getLast_eq_getElem]
      rfl
    have hy := dyckPath_y_eq_count_diff_int p (p.vertices.length - 1) hlast hstart
    have hsteps_len : (dyckPathToSteps p).length = p.vertices.length - 1 := dyckPathToSteps_length p
    have htake : (dyckPathToSteps p).take (p.vertices.length - 1) = dyckPathToSteps p := by
      conv_lhs => rw [← hsteps_len]
      exact List.take_length
    rw [htake] at hy
    rw [hfinish_eq] at hfinish
    have hfinish' : (p.vertices.get ⟨p.vertices.length - 1, hlast⟩).2 = 0 := hfinish
    rw [hfinish'] at hy
    simp only [CharP.cast_eq_zero] at hy
    omega
  count_D_le_count_U := by
    -- At any prefix, #D ≤ #U because y ≥ 0 throughout the path
    -- y = #U - #D, so #D ≤ #U ⟺ y ≥ 0
    intro i
    by_cases hi : i < p.vertices.length
    · have hy := dyckPath_y_eq_count_diff_int p i hi hstart
      -- The y-coordinate is always ≥ 0 (since it's a ℕ)
      -- So count U - count D ≥ 0, i.e., count D ≤ count U
      have hy_nonneg : (0 : ℤ) ≤ (p.vertices.get ⟨i, hi⟩).2 := Int.natCast_nonneg _
      omega
    · -- If i ≥ vertices.length, then take i = full list
      have hsteps_len : (dyckPathToSteps p).length = p.vertices.length - 1 := dyckPathToSteps_length p
      have htake : (dyckPathToSteps p).take i = dyckPathToSteps p := by
        apply List.take_of_length_le
        omega
      rw [htake]
      -- For the full list, count_U = count_D (from above), so count_D ≤ count_U
      have hlen : p.vertices.length ≥ 1 := List.length_pos_of_ne_nil p.nonempty
      have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
      have hy := dyckPath_y_eq_count_diff_int p (p.vertices.length - 1) hlast hstart
      have htake' : (dyckPathToSteps p).take (p.vertices.length - 1) = dyckPathToSteps p := by
        conv_lhs => rw [← hsteps_len]
        exact List.take_length
      rw [htake'] at hy
      have hy_nonneg : (0 : ℤ) ≤ (p.vertices.get ⟨p.vertices.length - 1, hlast⟩).2 :=
        Int.natCast_nonneg _
      omega

/-- The semilength of dyckPathToWord equals the count of U steps. -/
lemma dyckPathToWord_semilength (p : SimpleDigraph.Path dyckDigraph) (hstart : p.start = (0, 0))
    (hfinish : p.finish.2 = 0) :
    (dyckPathToWord p hstart hfinish).semilength = (dyckPathToSteps p).count DyckStep.U := by
  rfl

/-- Helper function to compute the y-coordinate at position i in a DyckWord path -/
def dyckWordY (w : DyckWord) (i : ℕ) : ℕ :=
  (w.toList.take i).count DyckStep.U - (w.toList.take i).count DyckStep.D

/-- Convert a DyckWord to a list of vertices -/
def dyckWordToVertices (w : DyckWord) : List (ℤ × ℕ) :=
  (List.finRange (w.toList.length + 1)).map fun ⟨i, _⟩ => ((i : ℤ), dyckWordY w i)

lemma dyckWordToVertices_length (w : DyckWord) : (dyckWordToVertices w).length = w.toList.length + 1 := by
  simp [dyckWordToVertices]

lemma dyckWordToVertices_nonempty (w : DyckWord) : dyckWordToVertices w ≠ [] := by
  intro h
  have := dyckWordToVertices_length w
  rw [h] at this
  simp at this

lemma dyckWordToVertices_getElem (w : DyckWord) (i : ℕ) (hi : i < (dyckWordToVertices w).length) :
    (dyckWordToVertices w)[i] = ((i : ℤ), dyckWordY w i) := by
  simp [dyckWordToVertices]

/-- Key lemma: if we take a D step at position i, then y > 0 at position i -/
lemma dyckWord_y_pos_before_D (w : DyckWord) (i : ℕ) (hi : i < w.toList.length)
    (hD : w.toList[i] = DyckStep.D) : 0 < dyckWordY w i := by
  unfold dyckWordY
  have hle := w.count_D_le_count_U i
  have hle' := w.count_D_le_count_U (i + 1)
  have htake_succ : w.toList.take (i + 1) = w.toList.take i ++ [w.toList[i]] := by
    rw [List.take_succ_eq_append_getElem hi]
  rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
      List.count_singleton] at hle'
  simp only [hD] at hle'
  have h1 : (if (DyckStep.D == DyckStep.D) = true then 1 else 0) = 1 := by native_decide
  have h2 : (if (DyckStep.D == DyckStep.U) = true then 1 else 0) = 0 := by native_decide
  simp only [h1, h2, add_zero] at hle'
  omega

/-- Convert a DyckWord to a Dyck path from (0, 0) to (2n, 0) where n = semilength.

    **Note:** The vertices are constructed as (i, y_i) where y_i = #U - #D in the first i steps.
    The Dyck word conditions ensure y_i ≥ 0 and the path stays in the valid region. -/
def dyckWordToPath (w : DyckWord) : SimpleDigraph.Path dyckDigraph where
  vertices := dyckWordToVertices w
  nonempty := dyckWordToVertices_nonempty w
  arcs_valid := by
    intro i hi
    rw [dyckWordToVertices_length] at hi
    have hi' : i < w.toList.length := by omega
    have hi1 : i + 1 < (dyckWordToVertices w).length := by rw [dyckWordToVertices_length]; omega
    have hi0 : i < (dyckWordToVertices w).length := by omega
    simp only [List.get_eq_getElem]
    rw [dyckWordToVertices_getElem w i hi0, dyckWordToVertices_getElem w (i + 1) hi1]
    have hstep : w.toList[i] = DyckStep.U ∨ w.toList[i] = DyckStep.D := DyckStep.dichotomy _
    unfold dyckWordY
    have htake_succ : w.toList.take (i + 1) = w.toList.take i ++ [w.toList[i]] := by
      rw [List.take_succ_eq_append_getElem hi']
    rcases hstep with hU | hD
    · -- U step: y increases by 1
      left
      constructor
      · push_cast; ring
      · rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
            List.count_singleton]
        simp only [hU]
        have h1 : (if (DyckStep.U == DyckStep.U) = true then 1 else 0) = 1 := by native_decide
        have h2 : (if (DyckStep.U == DyckStep.D) = true then 1 else 0) = 0 := by native_decide
        simp only [h1, h2, add_zero]
        have hle := w.count_D_le_count_U i
        omega
    · -- D step: y decreases by 1
      right
      constructor
      · push_cast; ring
      constructor
      · rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
            List.count_singleton]
        simp only [hD]
        have h1 : (if (DyckStep.D == DyckStep.D) = true then 1 else 0) = 1 := by native_decide
        have h2 : (if (DyckStep.D == DyckStep.U) = true then 1 else 0) = 0 := by native_decide
        simp only [h1, h2, add_zero]
        have hle := w.count_D_le_count_U i
        have hle' := w.count_D_le_count_U (i + 1)
        rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
            List.count_singleton] at hle'
        simp only [hD, h1, h2, add_zero] at hle'
        omega
      · exact dyckWord_y_pos_before_D w i hi' hD

/-- The start of dyckWordToPath is (0, 0) -/
lemma dyckWordToPath_start (w : DyckWord) : (dyckWordToPath w).start = (0, 0) := by
  unfold SimpleDigraph.Path.start dyckWordToPath
  simp only [List.head_eq_getElem]
  have h : 0 < (dyckWordToVertices w).length := by rw [dyckWordToVertices_length]; omega
  rw [dyckWordToVertices_getElem w 0 h]
  simp [dyckWordY]

/-- The finish of dyckWordToPath is (2 * semilength, 0) -/
lemma dyckWordToPath_finish (w : DyckWord) :
    (dyckWordToPath w).finish = (↑(2 * w.semilength), (0 : ℕ)) := by
  unfold SimpleDigraph.Path.finish dyckWordToPath
  simp only [List.getLast_eq_getElem]
  have hlen : (dyckWordToVertices w).length - 1 < (dyckWordToVertices w).length := by
    rw [dyckWordToVertices_length]; omega
  rw [dyckWordToVertices_getElem w ((dyckWordToVertices w).length - 1) hlen]
  rw [dyckWordToVertices_length]
  simp only [dyckWordY]
  ext
  · -- x-coordinate
    simp only [DyckWord.two_mul_semilength_eq_length]
    push_cast
    omega
  · -- y-coordinate = 0 (since count U = count D at the end)
    simp only
    have hlen' : w.toList.length + 1 - 1 = w.toList.length := by omega
    rw [hlen', List.take_length]
    have h := w.count_U_eq_count_D
    omega

/-- Helper: count of U plus count of D equals length for any DyckStep list -/
private lemma count_U_plus_count_D (l : List DyckStep) :
    l.count DyckStep.U + l.count DyckStep.D = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons, List.length_cons]
    cases x
    · have h1 : (if (DyckStep.U == DyckStep.U) = true then 1 else 0) = 1 := by native_decide
      have h2 : (if (DyckStep.U == DyckStep.D) = true then 1 else 0) = 0 := by native_decide
      rw [h1, h2]; omega
    · have h1 : (if (DyckStep.D == DyckStep.U) = true then 1 else 0) = 0 := by native_decide
      have h2 : (if (DyckStep.D == DyckStep.D) = true then 1 else 0) = 1 := by native_decide
      rw [h1, h2]; omega

/-- Helper: toList of dyckPathToWord equals dyckPathToSteps -/
private lemma dyckPathToWord_toList (p : SimpleDigraph.Path dyckDigraph) (hstart : p.start = (0, 0))
    (hfinish : p.finish.2 = 0) : (dyckPathToWord p hstart hfinish).toList = dyckPathToSteps p := rfl

/-- Key lemma: semilength of dyckPathToWord for path from (0,0) to (2n, 0) equals n -/
private lemma dyckPathToWord_semilength_eq (n : ℕ) (p : SimpleDigraph.Path dyckDigraph)
    (hstart : p.start = (0, 0)) (hfinish : p.finish = (↑(2 * n), (0 : ℕ))) :
    (dyckPathToWord p hstart (by rw [hfinish])).semilength = n := by
  have hfinish_y : p.finish.2 = 0 := by rw [hfinish]
  set w := dyckPathToWord p hstart hfinish_y with hw_def
  have htolist : w.toList = dyckPathToSteps p := dyckPathToWord_toList p hstart hfinish_y
  have hsemi : w.semilength = (dyckPathToSteps p).count DyckStep.U := by
    simp only [DyckWord.semilength, htolist]
  have heq : (dyckPathToSteps p).count DyckStep.U = (dyckPathToSteps p).count DyckStep.D := by
    have h := w.count_U_eq_count_D
    rw [htolist] at h
    exact h
  have hlen : (dyckPathToSteps p).length = 2 * n := by
    rw [dyckPathToSteps_length]
    have h := dyckDigraph_path_length_eq p
    rw [hstart, hfinish] at h
    simp only [sub_zero] at h
    push_cast at h
    omega
  have hsum := count_U_plus_count_D (dyckPathToSteps p)
  rw [hsemi]
  omega

/-- Membership in pathsFromTo -/
private lemma mem_pathsFromTo_dyck (u v : ℤ × ℕ) (p : SimpleDigraph.Path dyckDigraph) :
    p ∈ pathsFromTo dyckDigraph dyckDigraph_pathFinite u v ↔ p.start = u ∧ p.finish = v := by
  simp only [pathsFromTo, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- The maps dyckPathToWord and dyckWordToPath are inverses (path → word → path) -/
private lemma dyckWordToPath_dyckPathToWord (p : SimpleDigraph.Path dyckDigraph)
    (hstart : p.start = (0, 0)) (hfinish : p.finish.2 = 0) :
    dyckWordToPath (dyckPathToWord p hstart hfinish) = p := by
  apply dyckDigraph_path_ext
  -- Need to show: (dyckWordToPath (dyckPathToWord p ...)).vertices = p.vertices
  -- which is: dyckWordToVertices (dyckPathToWord p ...) = p.vertices
  show dyckWordToVertices (dyckPathToWord p hstart hfinish) = p.vertices
  apply List.ext_getElem
  · -- Length equality
    simp only [dyckWordToVertices_length, dyckPathToWord, dyckPathToSteps_length]
    have hne := p.nonempty
    have hlen : p.vertices.length ≥ 1 := List.length_pos_of_ne_nil hne
    omega
  · -- Element equality at position i
    intro i hi1 hi2
    rw [dyckWordToVertices_getElem]
    -- Goal: (i, dyckWordY (dyckPathToWord p ...) i) = p.vertices[i]
    ext
    · -- x-coordinate: show i = p.vertices[i].1
      simp only
      -- From start = (0, 0), we have p.vertices[0].1 = 0
      -- We prove by induction that p.vertices[i].1 = p.vertices[0].1 + i
      have h0 : 0 < p.vertices.length := by omega
      have hx_ind : ∀ j : ℕ, (hj : j < p.vertices.length) →
          (p.vertices.get ⟨0, h0⟩).1 + j = (p.vertices.get ⟨j, hj⟩).1 := by
        intro j hj
        induction j with
        | zero => simp
        | succ k ih =>
          have hk : k < p.vertices.length := Nat.lt_of_succ_lt hj
          have ih' := ih hk
          have harc := p.arcs_valid k (by omega : k + 1 < p.vertices.length)
          -- Arc implies x-coordinate increases by 1
          unfold dyckDigraph at harc
          simp only at harc
          rcases harc with ⟨hx, _⟩ | ⟨hx, _, _⟩
          · -- U step
            calc (p.vertices.get ⟨0, h0⟩).1 + (k + 1)
                = (p.vertices.get ⟨0, h0⟩).1 + k + 1 := by ring
              _ = (p.vertices.get ⟨k, hk⟩).1 + 1 := by rw [ih']
              _ = (p.vertices.get ⟨k + 1, hj⟩).1 := by rw [hx]
          · -- D step
            calc (p.vertices.get ⟨0, h0⟩).1 + (k + 1)
                = (p.vertices.get ⟨0, h0⟩).1 + k + 1 := by ring
              _ = (p.vertices.get ⟨k, hk⟩).1 + 1 := by rw [ih']
              _ = (p.vertices.get ⟨k + 1, hj⟩).1 := by rw [hx]
      have hmono := hx_ind i hi2
      have hstart0 : (p.vertices.get ⟨0, h0⟩).1 = 0 := by
        unfold SimpleDigraph.Path.start at hstart
        have h : p.vertices.get ⟨0, h0⟩ = p.vertices.head p.nonempty := by
          rw [List.get_mk_zero h0]
        rw [h, hstart]
      rw [hstart0] at hmono
      simp at hmono
      rw [← hmono]

    · -- y-coordinate: show dyckWordY (dyckPathToWord p ...) i = p.vertices[i].2
      simp only
      -- dyckWordY (dyckPathToWord p ...) i
      -- = ((dyckPathToWord p ...).toList.take i).count U - ((dyckPathToWord p ...).toList.take i).count D
      -- = ((dyckPathToSteps p).take i).count U - ((dyckPathToSteps p).take i).count D
      -- And dyckPath_y_eq_count_diff_int says:
      -- (p.vertices[i].2 : ℤ) = ((dyckPathToSteps p).take i).count U - ((dyckPathToSteps p).take i).count D
      have hy := dyckPath_y_eq_count_diff_int p i hi2 hstart
      simp only [dyckWordY, dyckPathToWord]
      -- The y-coordinate is always ≥ 0, so we can convert from ℤ to ℕ
      have hy_nonneg : (0 : ℤ) ≤ (p.vertices.get ⟨i, hi2⟩).2 := Int.natCast_nonneg _
      simp only [List.get_eq_getElem] at hy
      omega

/-- The maps dyckPathToWord and dyckWordToPath are inverses (word → path → word) -/
private lemma dyckPathToWord_dyckWordToPath (w : DyckWord) :
    dyckPathToWord (dyckWordToPath w) (dyckWordToPath_start w)
      (by simp only [dyckWordToPath_finish]) = w := by
  -- Need to show: dyckPathToSteps (dyckWordToPath w) = w.toList
  -- This follows from the fact that the step at position i is determined by
  -- whether y increases (U) or decreases (D), which matches w.toList[i]
  apply DyckWord.ext
  -- Goal: (dyckPathToWord (dyckWordToPath w) ...).toList = w.toList
  -- i.e., dyckPathToSteps (dyckWordToPath w) = w.toList
  show dyckPathToSteps (dyckWordToPath w) = w.toList
  apply List.ext_getElem
  · -- length equality
    simp only [dyckPathToSteps, dyckWordToPath, List.length_map, List.length_finRange]
    rw [dyckWordToVertices_length]
    omega
  · -- element equality
    intro i hi1 hi2
    simp only [dyckPathToSteps, dyckWordToPath, List.getElem_map, List.getElem_finRange,
               Fin.cast_mk, List.get_eq_getElem]
    have hlen : (dyckWordToVertices w).length = w.toList.length + 1 := dyckWordToVertices_length w
    have hi' : i < w.toList.length := hi2
    have hi1' : i + 1 < (dyckWordToVertices w).length := by rw [hlen]; omega
    have hi0 : i < (dyckWordToVertices w).length := by omega
    rw [dyckWordToVertices_getElem w i hi0, dyckWordToVertices_getElem w (i + 1) hi1']
    have hstep : w.toList[i] = DyckStep.U ∨ w.toList[i] = DyckStep.D := DyckStep.dichotomy _
    rcases hstep with hU | hD
    · -- U case: y increases by 1
      have hy_eq : dyckWordY w (i + 1) = dyckWordY w i + 1 := by
        unfold dyckWordY
        have htake_succ : w.toList.take (i + 1) = w.toList.take i ++ [w.toList[i]] := by
          rw [List.take_succ_eq_append_getElem hi']
        rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
            List.count_singleton, hU]
        have h1 : (if (DyckStep.U == DyckStep.U) = true then 1 else 0) = 1 := by native_decide
        have h2 : (if (DyckStep.U == DyckStep.D) = true then 1 else 0) = 0 := by native_decide
        rw [h1, h2]
        have hle := w.count_D_le_count_U i
        omega
      rw [ite_eq_left hy_eq, hU]
    · -- D case: y decreases by 1
      have hy_ne : dyckWordY w (i + 1) ≠ dyckWordY w i + 1 := by
        unfold dyckWordY
        have htake_succ : w.toList.take (i + 1) = w.toList.take i ++ [w.toList[i]] := by
          rw [List.take_succ_eq_append_getElem hi']
        rw [htake_succ, List.count_append, List.count_append, List.count_singleton,
            List.count_singleton, hD]
        have h1 : (if (DyckStep.D == DyckStep.U) = true then 1 else 0) = 0 := by native_decide
        have h2 : (if (DyckStep.D == DyckStep.D) = true then 1 else 0) = 1 := by native_decide
        rw [h1, h2]
        have hle := w.count_D_le_count_U i
        omega
      rw [ite_eq_right hy_ne, hD]

/-- The number of Dyck paths from (0, 0) to (2n, 0) equals the n-th Catalan number.
    This is a classical result connecting Dyck paths to Catalan numbers.

    **Proof strategy:** We construct a bijection between Dyck paths and DyckWords of semilength n.
    - Each arc (x,y) → (x+1,y+1) corresponds to U
    - Each arc (x,y) → (x+1,y-1) corresponds to D
    - The Dyck condition (y ≥ 0) ensures the prefix condition for DyckWords
    - Equal start and end y-coordinates ensures equal counts of U and D

    Then we use Mathlib's `DyckWord.card_dyckWord_semilength_eq_catalan`.

    **Key lemmas needed:**
    1. dyckPathToWord is well-defined (DyckWord conditions satisfied) ✓
    2. dyckWordToPath is well-defined (arc validity) ✓
    3. The maps are inverses (bijection) ✓
    4. dyckPathToWord maps paths from (0,0) to (2n,0) to words of semilength n ✓ -/
theorem dyck_paths_eq_catalan (n : ℕ) :
    (pathsFromTo dyckDigraph dyckDigraph_pathFinite (0, 0) (2 * n, 0)).card = catalan n := by
  -- Build equivalence between paths and DyckWords with semilength n
  have equiv : (pathsFromTo dyckDigraph dyckDigraph_pathFinite (0, 0) (2 * n, 0)) ≃
               { w : DyckWord // w.semilength = n } := by
    refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
    case toFun =>
      intro ⟨p, hp⟩
      have hmem := (mem_pathsFromTo_dyck _ _ p).mp hp
      have hstart : p.start = (0, 0) := hmem.1
      have hfinish : p.finish = (↑(2 * n), (0 : ℕ)) := hmem.2
      have hfinish_y : p.finish.2 = 0 := by rw [hfinish]
      refine ⟨dyckPathToWord p hstart hfinish_y, ?_⟩
      exact dyckPathToWord_semilength_eq n p hstart hfinish
    case invFun =>
      intro ⟨w, hw⟩
      refine ⟨dyckWordToPath w, ?_⟩
      rw [mem_pathsFromTo_dyck]
      constructor
      · exact dyckWordToPath_start w
      · rw [dyckWordToPath_finish, hw]
        ext <;> simp
    case left_inv =>
      intro ⟨p, hp⟩
      simp only [Subtype.mk.injEq]
      have hmem := (mem_pathsFromTo_dyck _ _ p).mp hp
      have hstart : p.start = (0, 0) := hmem.1
      have hfinish : p.finish = (↑(2 * n), (0 : ℕ)) := hmem.2
      have hfinish_y : p.finish.2 = 0 := by rw [hfinish]
      exact dyckWordToPath_dyckPathToWord p hstart hfinish_y
    case right_inv =>
      intro ⟨w, hw⟩
      simp only [Subtype.mk.injEq]
      exact dyckPathToWord_dyckWordToPath w
  -- Use the equivalence to transfer cardinality
  calc (pathsFromTo dyckDigraph dyckDigraph_pathFinite (0, 0) (2 * n, 0)).card
      = Fintype.card (pathsFromTo dyckDigraph dyckDigraph_pathFinite (0, 0) (2 * n, 0)) := by
        simp [Fintype.card_coe]
    _ = Fintype.card { w : DyckWord // w.semilength = n } := Fintype.card_congr equiv
    _ = catalan n := DyckWord.card_dyckWord_semilength_eq_catalan n

/-- Translation function for vertices in the Dyck digraph -/
private def translateVertex (d : ℤ) (v : ℤ × ℕ) : ℤ × ℕ := (v.1 + d, v.2)

/-- Translation preserves dyckDigraph arcs -/
private lemma dyckDigraph_arc_translate (d : ℤ) (u v : ℤ × ℕ) :
    dyckDigraph.arc u v ↔ dyckDigraph.arc (translateVertex d u) (translateVertex d v) := by
  unfold dyckDigraph translateVertex
  simp only
  constructor
  · intro h
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy, hpos⟩
    · left; constructor <;> omega
    · right; constructor; omega; constructor; omega; exact hpos
  · intro h
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy, hpos⟩
    · left; constructor <;> omega
    · right; refine ⟨?_, ?_, hpos⟩ <;> omega

/-- Create translated path by shifting x-coordinates -/
def translatePath (d : ℤ) (p : SimpleDigraph.Path dyckDigraph) :
    SimpleDigraph.Path dyckDigraph where
  vertices := p.vertices.map (translateVertex d)
  nonempty := by simp [p.nonempty]
  arcs_valid := by
    intro k hk
    simp only [List.length_map] at hk
    have hk' : k < p.vertices.length := Nat.lt_of_succ_lt hk
    have hk'' : k + 1 < p.vertices.length := hk
    -- Need to show arc at position k in the mapped list
    -- vertices.get ⟨k, _⟩ = (vertices.map f).get ⟨k, _⟩ = f (vertices.get ⟨k, _⟩)
    have h1 : (p.vertices.map (translateVertex d)).get ⟨k, by simp; exact hk'⟩ = 
              translateVertex d (p.vertices.get ⟨k, hk'⟩) := by
      simp [List.get_eq_getElem]
    have h2 : (p.vertices.map (translateVertex d)).get ⟨k + 1, by simp; exact hk''⟩ = 
              translateVertex d (p.vertices.get ⟨k + 1, hk''⟩) := by
      simp [List.get_eq_getElem]
    rw [h1, h2]
    rw [← dyckDigraph_arc_translate d]
    exact p.arcs_valid k hk

private lemma translatePath_start (d : ℤ) (p : SimpleDigraph.Path dyckDigraph) :
    (translatePath d p).start = translateVertex d p.start := by
  unfold translatePath SimpleDigraph.Path.start translateVertex
  simp only [List.head_map]

private lemma translatePath_finish (d : ℤ) (p : SimpleDigraph.Path dyckDigraph) :
    (translatePath d p).finish = translateVertex d p.finish := by
  unfold translatePath SimpleDigraph.Path.finish translateVertex
  simp only [List.getLast_map]

private lemma translatePath_neg (d : ℤ) (p : SimpleDigraph.Path dyckDigraph) :
    translatePath (-d) (translatePath d p) = p := by
  simp only [translatePath, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id p.vertices]
  congr 1
  funext v
  simp only [Function.comp_apply, translateVertex]
  ext
  · simp only [id_eq]; ring
  · rfl

lemma translatePath_injective (d : ℤ) : Function.Injective (translatePath d) := by
  intro p q hpq
  have h := congrArg (translatePath (-d)) hpq
  simp only [translatePath_neg] at h
  exact h

/-- The number of Dyck paths from (-2i, 0) to (2j, 0) equals catalan(i+j).
    This follows from translation invariance: shifting by 2i gives a bijection
    with paths from (0, 0) to (2(i+j), 0), which equal catalan(i+j) by `dyck_paths_eq_catalan`. -/
theorem dyck_paths_shifted_eq_catalan (i j : ℕ) :
    (pathsFromTo dyckDigraph dyckDigraph_pathFinite (-(2 * i : ℤ), 0) (2 * j, 0)).card =
      catalan (i + j) := by
  -- Build equivalence via translation by 2*i
  have equiv : (pathsFromTo dyckDigraph dyckDigraph_pathFinite (-(2 * i : ℤ), 0) (2 * j, 0)) ≃
               (pathsFromTo dyckDigraph dyckDigraph_pathFinite (0, 0) (2 * (i + j), 0)) := by
    refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
    case toFun =>
      intro ⟨p, hp⟩
      refine ⟨translatePath (2 * i) p, ?_⟩
      rw [mem_pathsFromTo_dyck] at hp ⊢
      constructor
      · rw [translatePath_start, hp.1]
        simp [translateVertex]
      · rw [translatePath_finish, hp.2]
        simp [translateVertex]
        ring
    case invFun =>
      intro ⟨p, hp⟩
      refine ⟨translatePath (-(2 * i : ℤ)) p, ?_⟩
      rw [mem_pathsFromTo_dyck] at hp ⊢
      constructor
      · rw [translatePath_start, hp.1]
        simp [translateVertex]
      · rw [translatePath_finish, hp.2]
        simp [translateVertex]
        ring
    case left_inv =>
      intro ⟨p, hp⟩
      simp only [Subtype.mk.injEq]
      exact translatePath_neg (2 * i) p
    case right_inv =>
      intro ⟨p, hp⟩
      simp only [Subtype.mk.injEq]
      have h : translatePath (2 * ↑i) (translatePath (-(2 * ↑i)) p) = p := by
        have := translatePath_neg (-(2 * i : ℤ)) p
        simp only [neg_neg] at this
        exact this
      exact h
  calc (pathsFromTo dyckDigraph dyckDigraph_pathFinite (-(2 * i : ℤ), 0) (2 * j, 0)).card
      = (pathsFromTo dyckDigraph dyckDigraph_pathFinite (0, 0) (2 * (i + j), 0)).card :=
        Finset.card_eq_of_equiv equiv
    _ = catalan (i + j) := dyck_paths_eq_catalan (i + j)

/-- The Catalan Hankel matrix equals the path weight matrix for the Dyck digraph.
    Entry (i,j) = catalan(i+j) = number of Dyck paths from (-2i, 0) to (2j, 0). -/
theorem catalanHankelMatrix_eq_pathWeightMatrix (k : ℕ) :
    catalanHankelMatrix k =
    pathWeightMatrix dyckDigraph_pathFinite dyckUnitArcWeight
      (fun i : Fin k => (-(2 * (i : ℤ)), 0))
      (fun j : Fin k => (2 * (j : ℤ), 0)) := by
  ext i j
  simp only [catalanHankelMatrix, pathWeightMatrix, Matrix.of_apply]
  rw [pathWeightSum_dyckUnitArcWeight]
  -- The number of paths from (-2i, 0) to (2j, 0) equals catalan(i+j)
  rw [← dyck_paths_shifted_eq_catalan]

/-- General case of Catalan Hankel determinant for k ≥ 8.
    The proof uses the LGV lemma with Dyck paths.
    Source: The TeX source says "The details are LTTR" (Left To The Reader).
    
    The full proof requires:
    1. catalan_unique_nipat: There is exactly one non-intersecting path tuple
    2. dyck_no_nipat_for_nonidentity: Non-identity permutations have no nipats
    These lemmas are defined later in this file but the proof structure
    requires them to be available here. -/
theorem catalan_hankel_det_general (n : ℕ) : (catalanHankelMatrix (n + 8)).det = 1 := by
  sorry -- [exercise] The TeX source says "The details are LTTR"

/-- Catalan Hankel determinant equals 1 (Corollary cor.lgv.catalan-hankel-det-0)
    Label: cor.lgv.catalan-hankel-det-0

    det((c_{i+j})_{0 ≤ i,j < k}) = 1

    where cₙ is the n-th Catalan number.

    Note: The TeX source uses 1-indexed notation det((c_{i+j-2})_{1 ≤ i,j ≤ k}),
    which is equivalent to our 0-indexed det((c_{i+j})_{0 ≤ i,j < k}).

    Proof sketch (via LGV lemma):
    Use the Dyck path digraph with Aᵢ = (-2i, 0) and Bᵢ = (2i, 0).
    - The (i,j) entry of the path matrix counts paths from Aᵢ to Bⱼ,
      which equals c_{i+j} (Catalan number).
    - There is exactly one non-intersecting path tuple from 𝐀 to 𝐁
      (the nested Dyck paths).
    - For non-identity permutations σ, there are no nipats from 𝐀 to σ(𝐁).
    - By LGV, det = 1 · 1 = 1. -/
theorem catalan_hankel_det (k : ℕ) : (catalanHankelMatrix k).det = 1 := by
  match k with
  | 0 => exact catalan_hankel_det_zero
  | 1 => exact catalan_hankel_det_one
  | 2 => exact catalan_hankel_det_two
  | 3 => exact catalan_hankel_det_three
  | 4 => exact catalan_hankel_det_four
  | 5 => exact catalan_hankel_det_five
  | 6 => exact catalan_hankel_det_six
  | 7 => exact catalan_hankel_det_seven
  | n + 8 => exact catalan_hankel_det_general n


/-- In the Dyck digraph, x-coordinate increases by 1 on each arc -/
lemma dyck_arc_x_inc (u v : ℤ × ℕ) (h : dyckDigraph.arc u v) : v.1 = u.1 + 1 := by
  unfold dyckDigraph at h
  simp only at h
  rcases h with ⟨hx, _⟩ | ⟨hx, _, _⟩ <;> exact hx

/-- In a Dyck path, x increases strictly along the path -/
lemma dyck_path_x_monotone (p : SimpleDigraph.Path dyckDigraph) (i j : ℕ)
    (hi : i < p.vertices.length) (hj : j < p.vertices.length) (hij : i ≤ j) :
    (p.vertices.get ⟨i, hi⟩).1 + (j - i) = (p.vertices.get ⟨j, hj⟩).1 := by
  induction j with
  | zero =>
    simp at hij
    subst hij
    simp
  | succ j ih =>
    cases Nat.lt_or_eq_of_le hij with
    | inl hlt =>
      have hj' : j < p.vertices.length := Nat.lt_of_succ_lt hj
      have hij' : i ≤ j := Nat.le_of_lt_succ hlt
      have ih' := ih hj' hij'
      have harc := p.arcs_valid j (by omega : j + 1 < p.vertices.length)
      have hx := dyck_arc_x_inc _ _ harc
      calc (p.vertices.get ⟨i, hi⟩).1 + (j + 1 - i)
          = (p.vertices.get ⟨i, hi⟩).1 + (j - i) + 1 := by omega
        _ = (p.vertices.get ⟨j, hj'⟩).1 + 1 := by rw [ih']
        _ = (p.vertices.get ⟨j + 1, hj⟩).1 := by rw [hx]
    | inr heq =>
      subst heq
      simp

/-- The x-coordinate difference between start and finish equals path length minus 1 -/
lemma dyck_path_x_diff (p : SimpleDigraph.Path dyckDigraph) :
    p.start.1 + (p.vertices.length - 1) = p.finish.1 := by
  unfold SimpleDigraph.Path.start SimpleDigraph.Path.finish
  have hne := p.nonempty
  have hlen : p.vertices.length ≥ 1 := List.length_pos_of_ne_nil hne
  have h0 : 0 < p.vertices.length := hlen
  have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
  have := dyck_path_x_monotone p 0 (p.vertices.length - 1) h0 hlast (Nat.zero_le _)
  simp at this
  have hhead : p.vertices.head hne = p.vertices[0] := by simp [List.head_eq_getElem]
  have hlastEq : p.vertices.getLast hne = p.vertices[p.vertices.length - 1] := by
    simp [List.getLast_eq_getElem]
  simp only [hhead, hlastEq]
  convert this using 1
  omega

/-- A path from (x, y) to (x, y') must have length 1 (i.e., be trivial) -/
lemma dyck_path_trivial_if_same_x (p : SimpleDigraph.Path dyckDigraph)
    (h : p.start.1 = p.finish.1) : p.vertices.length = 1 := by
  have hdiff := dyck_path_x_diff p
  have hlen : p.vertices.length ≥ 1 := List.length_pos_of_ne_nil p.nonempty
  omega

/-!
### Nested Dyck Paths for the Catalan Hankel Determinant

The nested Dyck path from (-2n, 0) to (2n, 0) goes:
(-2n, 0) → (-2n+1, 1) → ... → (0, 2n) → (1, 2n-1) → ... → (2n, 0)

At step i (0 ≤ i ≤ 4n), the vertex is (i - 2n, min(i, 4n - i)).
-/

/-- The vertices of the nested Dyck path from (-2n, 0) to (2n, 0) -/
def nestedDyckVertices (n : ℕ) : List (ℤ × ℕ) :=
  (List.finRange (4 * n + 1)).map fun ⟨i, _⟩ =>
    ((i : ℤ) - 2 * n, min i (4 * n - i))

lemma nestedDyckVertices_nonempty (n : ℕ) : nestedDyckVertices n ≠ [] := by
  simp [nestedDyckVertices]

lemma nestedDyckVertices_length (n : ℕ) : (nestedDyckVertices n).length = 4 * n + 1 := by
  simp [nestedDyckVertices]

lemma nestedDyckVertices_getElem (n : ℕ) (i : ℕ) (hi : i < (nestedDyckVertices n).length) :
    (nestedDyckVertices n)[i] = ((i : ℤ) - 2 * n, min i (4 * n - i)) := by
  simp only [nestedDyckVertices, List.getElem_map, List.getElem_finRange]
  rfl

lemma nestedDyckVertices_arcs_valid (n : ℕ) :
    ∀ i : ℕ, ∀ hi : i + 1 < (nestedDyckVertices n).length,
      dyckDigraph.arc ((nestedDyckVertices n).get ⟨i, Nat.lt_of_succ_lt hi⟩)
        ((nestedDyckVertices n).get ⟨i + 1, hi⟩) := by
  intro i hi
  have hlen : (nestedDyckVertices n).length = 4 * n + 1 := nestedDyckVertices_length n
  rw [hlen] at hi
  simp only [List.get_eq_getElem, nestedDyckVertices_getElem n i (by rw [hlen]; omega),
             nestedDyckVertices_getElem n (i + 1) (by rw [hlen]; exact hi)]
  unfold dyckDigraph
  simp only
  by_cases hcase : i < 2 * n
  · left
    constructor
    · push_cast; ring
    · have h1 : min i (4 * n - i) = i := Nat.min_eq_left (by omega)
      have h2 : min (i + 1) (4 * n - (i + 1)) = i + 1 := Nat.min_eq_left (by omega)
      rw [h1, h2]
  · push Not at hcase
    right
    constructor
    · push_cast; ring
    constructor
    · have h1 : min i (4 * n - i) = 4 * n - i := Nat.min_eq_right (by omega)
      have h2 : min (i + 1) (4 * n - (i + 1)) = 4 * n - i - 1 := Nat.min_eq_right (by omega)
      rw [h1, h2]; omega
    · have h1 : min i (4 * n - i) = 4 * n - i := Nat.min_eq_right (by omega)
      rw [h1]; omega

/-- The nested Dyck path from (-2n, 0) to (2n, 0) -/
def nestedDyckPath (n : ℕ) : SimpleDigraph.Path dyckDigraph where
  vertices := nestedDyckVertices n
  nonempty := nestedDyckVertices_nonempty n
  arcs_valid := nestedDyckVertices_arcs_valid n

lemma nestedDyckPath_start (n : ℕ) : (nestedDyckPath n).start = (-(2 * (n : ℤ)), 0) := by
  unfold SimpleDigraph.Path.start nestedDyckPath
  simp only [List.head_eq_getElem]
  have hlen : (nestedDyckVertices n).length = 4 * n + 1 := nestedDyckVertices_length n
  rw [nestedDyckVertices_getElem n 0 (by rw [hlen]; omega)]
  simp

lemma nestedDyckPath_finish (n : ℕ) : (nestedDyckPath n).finish = ((2 * (n : ℤ)), 0) := by
  unfold SimpleDigraph.Path.finish nestedDyckPath
  simp only [List.getLast_eq_getElem]
  have hlen : (nestedDyckVertices n).length = 4 * n + 1 := nestedDyckVertices_length n
  have hidx : (nestedDyckVertices n).length - 1 = 4 * n := by omega
  simp only [hidx, nestedDyckVertices_getElem n (4 * n) (by rw [hlen]; omega)]
  have hmin : min (4 * n) (4 * n - 4 * n) = 0 := by simp
  simp only [hmin]
  ext
  · push_cast; ring
  · rfl

lemma nestedDyckPath_vertex_mem (n : ℕ) (v : ℤ × ℕ) (hv : v ∈ (nestedDyckPath n).vertices) :
    ∃ i : ℕ, i ≤ 4 * n ∧ v = ((i : ℤ) - 2 * n, min i (4 * n - i)) := by
  unfold nestedDyckPath at hv
  simp only [nestedDyckVertices, List.mem_map, List.mem_finRange, true_and] at hv
  obtain ⟨⟨i, hi⟩, rfl⟩ := hv
  exact ⟨i, by omega, rfl⟩

/-- Different nested Dyck paths don't share any vertices -/
lemma nestedDyckPath_disjoint (n m : ℕ) (hnm : n ≠ m) :
    ¬pathsIntersect (nestedDyckPath n) (nestedDyckPath m) := by
  intro ⟨v, hvn, hvm⟩
  obtain ⟨i, hi, hvi⟩ := nestedDyckPath_vertex_mem n v hvn
  obtain ⟨j, hj, hvj⟩ := nestedDyckPath_vertex_mem m v hvm
  rw [hvi] at hvj
  simp only [Prod.mk.injEq] at hvj
  obtain ⟨hx, hy⟩ := hvj
  -- From hx: i - 2n = j - 2m, so i + 2m = j + 2n
  rcases Nat.lt_trichotomy n m with h | h | h
  · -- n < m case
    have hj_eq : (j : ℤ) = (i : ℤ) + 2 * (m - n) := by linarith
    have hj_nat : j = i + 2 * (m - n) := by omega
    by_cases hi_case : i ≤ 2 * n
    · have hmin_n : min i (4 * n - i) = i := Nat.min_eq_left (by omega)
      rw [hmin_n] at hy
      by_cases hj_case : j ≤ 2 * m
      · have hmin_m : min j (4 * m - j) = j := Nat.min_eq_left (by omega)
        rw [hmin_m] at hy; omega
      · push Not at hj_case
        have hmin_m : min j (4 * m - j) = 4 * m - j := Nat.min_eq_right (by omega)
        rw [hmin_m] at hy
        have hi_eq : i = m + n := by omega
        omega
    · push Not at hi_case
      have hmin_n : min i (4 * n - i) = 4 * n - i := Nat.min_eq_right (by omega)
      rw [hmin_n] at hy
      by_cases hj_case : j ≤ 2 * m
      · have hmin_m : min j (4 * m - j) = j := Nat.min_eq_left (by omega)
        rw [hmin_m] at hy
        have hi_eq : i = 3 * n - m := by omega
        omega
      · push Not at hj_case
        have hmin_m : min j (4 * m - j) = 4 * m - j := Nat.min_eq_right (by omega)
        rw [hmin_m] at hy
        omega
  · exact hnm h
  · -- m < n case (symmetric)
    have hi_eq : (i : ℤ) = (j : ℤ) + 2 * (n - m) := by linarith
    have hi_nat : i = j + 2 * (n - m) := by omega
    by_cases hj_case : j ≤ 2 * m
    · have hmin_m : min j (4 * m - j) = j := Nat.min_eq_left (by omega)
      rw [hmin_m] at hy
      by_cases hi_case : i ≤ 2 * n
      · have hmin_n : min i (4 * n - i) = i := Nat.min_eq_left (by omega)
        rw [hmin_n] at hy; omega
      · push Not at hi_case
        have hmin_n : min i (4 * n - i) = 4 * n - i := Nat.min_eq_right (by omega)
        rw [hmin_n] at hy
        have hj_eq' : j = 3 * m - n := by omega
        omega
    · push Not at hj_case
      have hmin_m : min j (4 * m - j) = 4 * m - j := Nat.min_eq_right (by omega)
      rw [hmin_m] at hy
      by_cases hi_case : i ≤ 2 * n
      · have hmin_n : min i (4 * n - i) = i := Nat.min_eq_left (by omega)
        rw [hmin_n] at hy
        have hj_eq' : j = m + n := by omega
        omega
      · push Not at hi_case
        have hmin_n : min i (4 * n - i) = 4 * n - i := Nat.min_eq_right (by omega)
        rw [hmin_n] at hy
        omega

/-- In a Dyck path, the y-coordinate at step j has the same parity as j + start.2 -/
lemma dyck_path_parity (p : SimpleDigraph.Path dyckDigraph) (j : ℕ) (hj : j < p.vertices.length) :
    (p.vertices.get ⟨j, hj⟩).2 % 2 = (j + p.start.2) % 2 := by
  induction j with
  | zero =>
    simp only [Nat.zero_add]
    unfold SimpleDigraph.Path.start
    rw [List.get_mk_zero hj]
  | succ j ih =>
    have hj' : j < p.vertices.length := Nat.lt_of_succ_lt hj
    have ih' := ih hj'
    have harc := p.arcs_valid j hj
    unfold dyckDigraph at harc
    simp only at harc
    rcases harc with ⟨_, hsnd⟩ | ⟨_, hsnd, _⟩
    · -- Up step: y increases by 1
      have hy : (p.vertices.get ⟨j + 1, hj⟩).2 = (p.vertices.get ⟨j, hj'⟩).2 + 1 := hsnd
      rw [hy]
      omega
    · -- Down step: y decreases by 1
      have hy : (p.vertices.get ⟨j + 1, hj⟩).2 + 1 = (p.vertices.get ⟨j, hj'⟩).2 := hsnd
      omega

/-- For a Dyck path from (-2n, 0) to (2n, 0), the y-coordinate at step j is ≤ min(j, 4n - j) -/
lemma dyck_path_y_upper_bound (p : SimpleDigraph.Path dyckDigraph) (n : ℕ)
    (hstart : p.start = (-(2 * (n : ℤ)), 0))
    (hfinish : p.finish = (2 * (n : ℤ), 0))
    (j : ℕ) (hj : j < p.vertices.length) :
    (p.vertices.get ⟨j, hj⟩).2 ≤ min j (4 * n - j) := by
  have hlen : p.vertices.length = 4 * n + 1 := by
    have := dyckDigraph_path_length_eq p
    rw [hstart, hfinish] at this
    simp at this
    omega
  have hj' : j ≤ 4 * n := by omega
  -- Upper bound from going up: y ≤ j
  have h1 : (p.vertices.get ⟨j, hj⟩).2 ≤ p.start.2 + j := dyckDigraph_path_snd_bounded p j hj
  rw [hstart] at h1
  simp at h1
  -- Upper bound from needing to return to 0
  have h2 : (p.vertices.get ⟨j, hj⟩).2 ≤ 4 * n - j := by
    have hfinish_idx : p.vertices.length - 1 < p.vertices.length := by omega
    have hfinish_y : (p.vertices.get ⟨p.vertices.length - 1, hfinish_idx⟩).2 = 0 := by
      have hfinish_eq : p.finish = p.vertices.get ⟨p.vertices.length - 1, hfinish_idx⟩ := by
        unfold SimpleDigraph.Path.finish
        rw [List.getLast_eq_getElem]
        rfl
      rw [← hfinish_eq, hfinish]
    -- From step j to the end, y can decrease by at most (4n - j) = (length - 1 - j)
    -- Since y ends at 0, y at step j ≤ 4n - j
    have hdecr : ∀ k : ℕ, j ≤ k → (hk : k < p.vertices.length) →
        (p.vertices.get ⟨j, hj⟩).2 ≤ (p.vertices.get ⟨k, hk⟩).2 + (k - j) := by
      intro k hjk hk
      induction k with
      | zero =>
        simp at hjk; subst hjk; simp
      | succ k ihk =>
        by_cases hjk' : j ≤ k
        · have hk' : k < p.vertices.length := Nat.lt_of_succ_lt hk
          have ihk' := ihk hjk' hk'
          have harc := p.arcs_valid k hk
          unfold dyckDigraph at harc
          simp only at harc
          rcases harc with ⟨_, hsnd⟩ | ⟨_, hsnd, _⟩
          · -- Up step
            have hy : (p.vertices.get ⟨k + 1, hk⟩).2 = (p.vertices.get ⟨k, hk'⟩).2 + 1 := hsnd
            calc (p.vertices.get ⟨j, hj⟩).2
                ≤ (p.vertices.get ⟨k, hk'⟩).2 + (k - j) := ihk'
              _ ≤ (p.vertices.get ⟨k + 1, hk⟩).2 - 1 + (k - j) := by rw [hy]; omega
              _ ≤ (p.vertices.get ⟨k + 1, hk⟩).2 + (k + 1 - j) := by omega
          · -- Down step
            have hy : (p.vertices.get ⟨k + 1, hk⟩).2 + 1 = (p.vertices.get ⟨k, hk'⟩).2 := hsnd
            calc (p.vertices.get ⟨j, hj⟩).2
                ≤ (p.vertices.get ⟨k, hk'⟩).2 + (k - j) := ihk'
              _ = (p.vertices.get ⟨k + 1, hk⟩).2 + 1 + (k - j) := by rw [hy]
              _ ≤ (p.vertices.get ⟨k + 1, hk⟩).2 + (k + 1 - j) := by omega
        · push Not at hjk'
          have : j = k + 1 := by omega
          subst this; simp
    have hdecr' := hdecr (p.vertices.length - 1) (by omega) hfinish_idx
    rw [hfinish_y] at hdecr'
    simp only [zero_add] at hdecr'
    have hlen' : p.vertices.length - 1 - j = 4 * n - j := by omega
    omega
  exact Nat.le_min.mpr ⟨h1, h2⟩

/-- Key lemma for uniqueness: if y is even, y ≤ 2i, and y ≠ 2m for all m < i, then y = 2i -/
private lemma y_eq_2i_of_constraints (y i : ℕ) (heven : y % 2 = 0) (hbound : y ≤ 2 * i) 
    (havoid : ∀ m : ℕ, m < i → y ≠ 2 * m) : y = 2 * i := by
  have hy_form : y = 2 * (y / 2) := by omega
  have hy_div_bound : y / 2 ≤ i := by omega
  have hy_div_avoid : ∀ m : ℕ, m < i → y / 2 ≠ m := by
    intro m hm heq
    have := havoid m hm
    omega
  have hy_div_eq : y / 2 = i := by
    by_contra h
    have hlt : y / 2 < i := Nat.lt_of_le_of_ne hy_div_bound h
    exact hy_div_avoid (y / 2) hlt rfl
  omega

/-- Key lemma: if y_{2i} = 2i, y changes by ±1, and y ≤ j for j ≤ 2i, then y_j = j -/
private lemma y_eq_j_of_y2i_constraints (y : ℕ → ℕ) (i : ℕ) 
    (h2i : y (2 * i) = 2 * i)
    (hstep : ∀ j, j < 2 * i → (y (j + 1) = y j + 1 ∨ y (j + 1) + 1 = y j))
    (hbound : ∀ j, j ≤ 2 * i → y j ≤ j) :
    ∀ j, j ≤ 2 * i → y j = j := by
  intro j hj
  by_contra h
  have hlt : y j < j := Nat.lt_of_le_of_ne (hbound j hj) h
  have hmax_reach : ∀ n k, k + n ≤ 2 * i → y (k + n) ≤ y k + n := by
    intro n
    induction n with
    | zero => intro k _; simp
    | succ n ihn =>
      intro k hkn
      have hkn' : k + n ≤ 2 * i := by omega
      have ihn' := ihn k (by omega)
      have hstep_kn := hstep (k + n) (by omega)
      rcases hstep_kn with hup | hdown
      · calc y (k + n + 1) = y (k + n) + 1 := hup
          _ ≤ y k + n + 1 := by omega
      · calc y (k + n + 1) = y (k + n) - 1 := by omega
          _ ≤ y k + n := by omega
          _ ≤ y k + (n + 1) := by omega
  have hj_plus : j + (2 * i - j) = 2 * i := by omega
  have hreach := hmax_reach (2 * i - j) j (by omega)
  rw [hj_plus] at hreach
  rw [h2i] at hreach
  omega

/-- Key lemma: for j ≥ 2i, if y_{2i} = 2i, y changes by ±1, and y ≤ 4i - j, then y_j = 4i - j -/
private lemma y_eq_4i_minus_j_of_y2i_constraints (y : ℕ → ℕ) (i : ℕ) 
    (h2i : y (2 * i) = 2 * i)
    (hstep : ∀ j, j < 4 * i → (y (j + 1) = y j + 1 ∨ y (j + 1) + 1 = y j))
    (hbound : ∀ j, 2 * i ≤ j → j ≤ 4 * i → y j ≤ 4 * i - j) :
    ∀ j, 2 * i ≤ j → j ≤ 4 * i → y j = 4 * i - j := by
  intro j hj_lo hj_hi
  by_contra h
  have hlt : y j < 4 * i - j := Nat.lt_of_le_of_ne (hbound j hj_lo hj_hi) h
  have hmin_reach : ∀ n k, k ≥ 2 * i → k + n ≤ 4 * i → y (k + n) ≥ y k - n := by
    intro n
    induction n with
    | zero => intro k _ _; simp
    | succ n ihn =>
      intro k hk_lo hkn
      have hkn' : k + n ≤ 4 * i := by omega
      have ihn' := ihn k hk_lo (by omega)
      have hstep_kn := hstep (k + n) (by omega)
      rcases hstep_kn with hup | hdown
      · calc y (k + n + 1) = y (k + n) + 1 := hup
          _ ≥ y k - n + 1 := by omega
          _ ≥ y k - (n + 1) := by omega
      · calc y (k + n + 1) = y (k + n) - 1 := by omega
          _ ≥ y k - n - 1 := by omega
  have hj_from_2i : (2 * i) + (j - 2 * i) = j := by omega
  have hreach2 := hmin_reach (j - 2 * i) (2 * i) (le_refl _) (by omega)
  rw [hj_from_2i, h2i] at hreach2
  have hge : y j ≥ 4 * i - j := by omega
  omega

/-- The nested path vertex at x = 0 (step 2n) has y = 2n -/
private lemma nestedDyckPath_mid_y (n : ℕ) :
    (nestedDyckPath n).vertices.get ⟨2 * n, by
      simp only [nestedDyckPath, nestedDyckVertices_length]; omega⟩ = (0, 2 * n) := by
  simp only [nestedDyckPath]
  have hlen : (nestedDyckVertices n).length = 4 * n + 1 := nestedDyckVertices_length n
  have hidx : 2 * n < (nestedDyckVertices n).length := by omega
  simp only [List.get_eq_getElem, nestedDyckVertices_getElem n (2 * n) hidx]
  have hmin : min (2 * n) (4 * n - 2 * n) = 2 * n := Nat.min_eq_left (by omega)
  simp only [hmin]
  ext <;> simp

/-- There is exactly one nipat in the Catalan Hankel setup.

    The proof constructs the canonical nipat where path_i is the "nested" Dyck path
    from (-2i, 0) to (2i, 0) that goes up to height 2i and back down:
    (-2i, 0) → (-2i+1, 1) → ... → (0, 2i) → (1, 2i-1) → ... → (2i, 0)

    **Existence**: The canonical paths form a valid PathTuple because:
    - Each path is a valid Dyck path (arcs go up-right or down-right)
    - Start/finish conditions are satisfied by construction

    **Non-intersection**: The canonical paths don't intersect because:
    - Path_i visits vertices (x, y) with y ≤ 2i
    - At height y, path_i is at x = -2i + y (going up) or x = y (going down)
    - Path_j (j > i) at height y ≤ 2i is at x = -2j + y or x = y
    - These x-coordinates differ when j ≠ i

    **Uniqueness**: Any nipat must equal the canonical one because:
    - In the Dyck digraph, paths from (-2i, 0) to (2i, 0) must have length 4i
    - For non-intersection with outer paths, inner paths must stay "inside"
    - The only way to do this is the nested structure -/
theorem catalan_unique_nipat (k : ℕ) :
    let A : kVertex (ℤ × ℕ) k := fun i => (-2 * (i : ℤ), 0)
    let B : kVertex (ℤ × ℕ) k := fun i => (2 * (i : ℤ), 0)
    ∃! pt : PathTuple dyckDigraph k A B, pt.isNonIntersecting := by
  match k with
  | 0 =>
    -- For k = 0, the unique nipat is the empty tuple
    intro A B
    use ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    constructor
    · intro i j _; exact i.elim0
    · intro pt _; cases pt with | mk paths _ _ => congr; funext i; exact i.elim0
  | 1 =>
    -- For k = 1, A_0 = (0, 0) = B_0, so the unique nipat has the trivial path
    intro A B
    have hA0 : A 0 = (0, 0) := by simp [A]
    have hB0 : B 0 = (0, 0) := by simp [B]
    -- Define the trivial path at (0, 0)
    let trivPath : SimpleDigraph.Path dyckDigraph := {
      vertices := [(0, 0)]
      nonempty := List.cons_ne_nil _ _
      arcs_valid := by intro i hi; simp only [List.length_singleton] at hi; omega
    }
    let pt : PathTuple dyckDigraph 1 A B := {
      paths := fun _ => trivPath
      starts := by intro i; fin_cases i; simp [trivPath, SimpleDigraph.Path.start, A]
      finishes := by intro i; fin_cases i; simp [trivPath, SimpleDigraph.Path.finish, B]
    }
    use pt
    constructor
    · intro i j hij; fin_cases i; fin_cases j; simp at hij
    · intro pt' _
      cases pt' with
      | mk paths' starts' finishes' =>
        congr; funext i; fin_cases i
        have hstart : (paths' 0).start = (0, 0) := starts' 0
        have hfinish : (paths' 0).finish = (0, 0) := finishes' 0
        -- Since start.1 = finish.1 = 0, the path must be trivial (length 1)
        have hsamex : (paths' 0).start.1 = (paths' 0).finish.1 := by rw [hstart, hfinish]
        have hlen1 := dyck_path_trivial_if_same_x (paths' 0) hsamex
        -- A path of length 1 has vertices = [start]
        have hvertices : (paths' 0).vertices = [(paths' 0).start] := by
          have hne := (paths' 0).nonempty
          cases hp : (paths' 0).vertices with
          | nil => exact absurd hp hne
          | cons v vs =>
            have hlen' : (v :: vs).length = 1 := by rw [← hp]; exact hlen1
            simp only [List.length_cons] at hlen'
            have hvs : vs = [] := List.eq_nil_of_length_eq_zero (Nat.succ_injective hlen')
            subst hvs; congr 1
            unfold SimpleDigraph.Path.start; simp only [hp, List.head_cons]
        -- Now show the paths are equal via path extensionality
        apply dyckDigraph_path_ext
        calc (paths' ⟨0, _⟩).vertices = (paths' 0).vertices := rfl
          _ = [(paths' 0).start] := hvertices
          _ = [(0, 0)] := by rw [hstart]
          _ = trivPath.vertices := rfl
  | n + 2 =>
    intro A B
    -- For k ≥ 2, construct the canonical nipat using nested Dyck paths
    let pt : PathTuple dyckDigraph (n + 2) A B := {
      paths := fun i => nestedDyckPath i.val
      starts := by
        intro i
        rw [nestedDyckPath_start]
        -- Goal: (-(2 * ↑↑i), 0) = A i = (-2 * ↑↑i, 0)
        rfl
      finishes := by
        intro i
        rw [nestedDyckPath_finish]
    }
    use pt
    constructor
    · -- Non-intersection: different nested paths don't share vertices
      intro i j hij
      apply nestedDyckPath_disjoint
      intro h
      apply hij
      exact Fin.ext h
    · -- Uniqueness: any nipat must equal the canonical one
      -- This follows from the structural constraints of the Dyck digraph:
      -- - Each path from (-2i, 0) to (2i, 0) has exactly 4i arcs
      -- - At each step, the choice of up/down is constrained by the
      --   non-intersection requirement with other paths
      -- - The nested structure is the only way to satisfy all constraints
      --
      -- The full proof requires showing that at each vertex, the direction
      -- is uniquely determined. This is a complex inductive argument.
      -- For now, we note that the existence and non-intersection are proven,
      -- and the uniqueness follows from the rigid structure of nested paths.
        intro pt' hni'
        cases pt' with
        | mk paths' starts' finishes' =>
          congr
          -- Helper: path length for any Fin index
          have hlen_paths : ∀ i : Fin (n + 2), (paths' i).vertices.length = 4 * i.val + 1 := by
            intro i
            have := dyckDigraph_path_length_eq (paths' i)
            have hstart := starts' i
            have hfinish := finishes' i
            simp only [A, B] at hstart hfinish
            rw [hstart, hfinish] at this
            simp at this; omega
          -- Use strong induction to prove paths' i = nestedDyckPath i.val
          have hpaths_eq : ∀ i : Fin (n + 2), (paths' i).vertices = (nestedDyckPath i.val).vertices := by
            intro i
            -- Strong induction on i.val
            have : ∀ ival, ival < n + 2 → ∀ i : Fin (n + 2), i.val = ival → 
                (paths' i).vertices = (nestedDyckPath i.val).vertices := by
              intro ival
              induction ival using Nat.strong_induction_on with
              | _ ival ih =>
                intro hival_bound i hi_eq
                have hlen : (paths' i).vertices.length = 4 * i.val + 1 := hlen_paths i
                have hlen_nested : (nestedDyckPath i.val).vertices.length = 4 * i.val + 1 := by
                  simp [nestedDyckPath, nestedDyckVertices_length]
                have hstart_paths : (paths' i).start = (-(2 * (i.val : ℤ)), 0) := starts' i
                have hfinish_paths : (paths' i).finish = (2 * (i.val : ℤ), 0) := finishes' i
                -- Key step: show y at step 2*i.val equals 2*i.val
                have h2i_lt : 2 * i.val < (paths' i).vertices.length := by rw [hlen]; omega
                have hparity := dyck_path_parity (paths' i) (2 * i.val) h2i_lt
                have hstart_y : (paths' i).start.2 = 0 := by rw [hstart_paths]
                rw [hstart_y] at hparity
                simp only [add_zero] at hparity
                have heven : ((paths' i).vertices[2 * i.val]).2 % 2 = 0 := by
                  simp only [List.get_eq_getElem] at hparity; omega
                have hbound_2i : ((paths' i).vertices[2 * i.val]).2 ≤ 2 * i.val := by
                  have hb := dyck_path_y_upper_bound (paths' i) i.val hstart_paths hfinish_paths 
                      (2 * i.val) h2i_lt
                  have hmin_2i : min (2 * i.val) (4 * i.val - 2 * i.val) = 2 * i.val := 
                      Nat.min_eq_left (by omega)
                  simp only [List.get_eq_getElem] at hb
                  rw [hmin_2i] at hb
                  exact hb
                -- y at step 2*i.val ≠ 2m for any m < i.val (by non-intersection)
                have hne_smaller : ∀ m : ℕ, m < i.val → 
                    ((paths' i).vertices[2 * i.val]).2 ≠ 2 * m := by
                  intro m hm heq
                  have hm_fin : m < n + 2 := Nat.lt_trans hm i.isLt
                  let m' : Fin (n + 2) := ⟨m, hm_fin⟩
                  have ih_m := ih m (by rw [← hi_eq]; exact hm) hm_fin m' rfl
                  have hlen_m : (nestedDyckPath m).vertices.length = 4 * m + 1 := by
                    simp [nestedDyckPath, nestedDyckVertices_length]
                  have h2m_lt : 2 * m < (nestedDyckPath m).vertices.length := by rw [hlen_m]; omega
                  have hv_nested : (nestedDyckPath m).vertices[2 * m]'h2m_lt = (0, 2 * m) := by
                    simp only [nestedDyckPath]
                    rw [nestedDyckVertices_getElem m (2 * m) (by rw [nestedDyckVertices_length]; omega)]
                    simp [Nat.min_eq_left (by omega : 2 * m ≤ 4 * m - 2 * m)]
                  have hmem_m : (0, 2 * m) ∈ (paths' m').vertices := by
                    rw [ih_m, List.mem_iff_getElem]
                    exact ⟨2 * m, h2m_lt, hv_nested⟩
                  have hx_2i : ((paths' i).vertices[2 * i.val]).1 = 0 := by
                    have hfst := dyckDigraph_path_vertex_fst (paths' i) (2 * i.val) h2i_lt
                    rw [hstart_paths] at hfst; simp at hfst; omega
                  have hmem_i : (0, 2 * m) ∈ (paths' i).vertices := by
                    rw [List.mem_iff_getElem]
                    exact ⟨2 * i.val, h2i_lt, by ext; simp [hx_2i]; simp [heq]⟩
                  have hni_im := hni' i m' (by simp [m']; intro h; exact Nat.ne_of_gt hm (Fin.ext_iff.mp h))
                  exact hni_im ⟨(0, 2 * m), hmem_i, hmem_m⟩
                -- Conclude: y at step 2*i.val = 2*i.val
                have hmid : ((paths' i).vertices[2 * i.val]).2 = 2 * i.val := by
                  have heven' : Even ((paths' i).vertices[2 * i.val]).2 := Nat.even_iff.mpr heven
                  obtain ⟨k, hk⟩ := heven'
                  have hk2 : ((paths' i).vertices[2 * i.val]).2 = 2 * k := by omega
                  have hkle : k ≤ i.val := by omega
                  by_contra hne
                  have hlt : k < i.val := Nat.lt_of_le_of_ne hkle (by omega)
                  exact hne_smaller k hlt hk2
                -- Now use the forced path argument
                apply List.ext_getElem
                · rw [hlen, hlen_nested]
                · intro j hj1 hj2
                  have hj_bound : j < (nestedDyckVertices i.val).length := by
                    rw [nestedDyckVertices_length, ← hlen_nested]; exact hj2
                  simp only [nestedDyckPath]
                  rw [nestedDyckVertices_getElem _ _ hj_bound]
                  have hx_paths : ((paths' i).vertices[j]).1 = (j : ℤ) - 2 * i.val := by
                    have hfst := dyckDigraph_path_vertex_fst (paths' i) j hj1
                    rw [hstart_paths] at hfst; simp at hfst; omega
                  ext
                  · simp [hx_paths]
                  · -- y-coordinate: use forced path argument
                    have hj4i : j ≤ 4 * i.val := by rw [hlen] at hj1; omega
                    have hbound_j : ((paths' i).vertices[j]).2 ≤ min j (4 * i.val - j) := by
                      exact dyck_path_y_upper_bound (paths' i) i.val hstart_paths hfinish_paths j hj1
                    by_cases hj2i : j ≤ 2 * i.val
                    · -- First half: y(j) = j
                      have hmin : min j (4 * i.val - j) = j := Nat.min_eq_left (by omega)
                      rw [hmin]
                      rw [hmin] at hbound_j
                      by_contra hne
                      have hlt : ((paths' i).vertices[j]).2 < j := Nat.lt_of_le_of_ne hbound_j hne
                      have hsteps : ((paths' i).vertices[2 * i.val]).2 ≤ 
                          ((paths' i).vertices[j]).2 + (2 * i.val - j) := by
                        have haux : ∀ d, j + d ≤ 2 * i.val → ∀ (hd : j + d < (paths' i).vertices.length),
                            ((paths' i).vertices[j + d]'hd).2 ≤ ((paths' i).vertices[j]).2 + d := by
                          intro d; induction d with
                          | zero => intro _ hd; simp
                          | succ d ihd =>
                            intro hd hd_lt
                            have hd' : j + d ≤ 2 * i.val := by omega
                            have hd'_lt : j + d < (paths' i).vertices.length := by omega
                            have ihd' := ihd hd' hd'_lt
                            have harc := (paths' i).arcs_valid (j + d) (by omega : j + d + 1 < _)
                            unfold dyckDigraph at harc; simp only at harc
                            have heq : j + (d + 1) = j + d + 1 := by ring
                            rcases harc with ⟨_, hsnd⟩ | ⟨_, hsnd, _⟩
                            · calc ((paths' i).vertices[j + (d + 1)]'hd_lt).2 
                                  = ((paths' i).vertices[j + d + 1]'(by omega)).2 := by simp [heq]
                                _ = ((paths' i).vertices[j + d]'hd'_lt).2 + 1 := hsnd
                                _ ≤ ((paths' i).vertices[j]).2 + d + 1 := by omega
                            · calc ((paths' i).vertices[j + (d + 1)]'hd_lt).2 
                                  = ((paths' i).vertices[j + d + 1]'(by omega)).2 := by simp [heq]
                                _ = ((paths' i).vertices[j + d]'hd'_lt).2 - 1 := by 
                                    have : ((paths' i).vertices[j + d + 1]'(by omega)).2 + 1 = 
                                           ((paths' i).vertices[j + d]'hd'_lt).2 := hsnd
                                    omega
                                _ ≤ ((paths' i).vertices[j + d]'hd'_lt).2 := Nat.sub_le _ _
                                _ ≤ ((paths' i).vertices[j]).2 + d := ihd'
                                _ ≤ ((paths' i).vertices[j]).2 + (d + 1) := by omega
                        have h2i_j : 2 * i.val - j ≤ 2 * i.val := by omega
                        have h_lt : j + (2 * i.val - j) < (paths' i).vertices.length := by rw [hlen]; omega
                        have := haux (2 * i.val - j) (by omega) h_lt
                        simp only [Nat.add_sub_cancel' hj2i] at this
                        exact this
                      rw [hmid] at hsteps; omega
                    · -- Second half: y(j) = 4*i.val - j
                      push Not at hj2i
                      have hmin : min j (4 * i.val - j) = 4 * i.val - j := Nat.min_eq_right (by omega)
                      rw [hmin]
                      rw [hmin] at hbound_j
                      by_contra hne
                      have hlt : ((paths' i).vertices[j]).2 < 4 * i.val - j := Nat.lt_of_le_of_ne hbound_j hne
                      have hsteps : ((paths' i).vertices[j]).2 ≥ 
                          ((paths' i).vertices[2 * i.val]).2 - (j - 2 * i.val) := by
                        have haux : ∀ d, 2 * i.val + d ≤ j → ∀ (hd : 2 * i.val + d < (paths' i).vertices.length),
                            ((paths' i).vertices[2 * i.val + d]'hd).2 ≥ 
                            ((paths' i).vertices[2 * i.val]).2 - d := by
                          intro d; induction d with
                          | zero => intro _ hd; simp
                          | succ d ihd =>
                            intro hd hd_lt
                            have hd' : 2 * i.val + d ≤ j := by omega
                            have hd'_lt : 2 * i.val + d < (paths' i).vertices.length := by omega
                            have ihd' := ihd hd' hd'_lt
                            have harc := (paths' i).arcs_valid (2 * i.val + d) (by omega : 2 * i.val + d + 1 < _)
                            unfold dyckDigraph at harc; simp only at harc
                            have heq : 2 * i.val + (d + 1) = 2 * i.val + d + 1 := by ring
                            rcases harc with ⟨_, hsnd⟩ | ⟨_, hsnd, _⟩
                            · calc ((paths' i).vertices[2 * i.val + (d + 1)]'hd_lt).2 
                                  = ((paths' i).vertices[2 * i.val + d + 1]'(by omega)).2 := by simp [heq]
                                _ = ((paths' i).vertices[2 * i.val + d]'hd'_lt).2 + 1 := hsnd
                                _ ≥ ((paths' i).vertices[2 * i.val]).2 - d + 1 := by omega
                                _ ≥ ((paths' i).vertices[2 * i.val]).2 - (d + 1) := by omega
                            · calc ((paths' i).vertices[2 * i.val + (d + 1)]'hd_lt).2 
                                  = ((paths' i).vertices[2 * i.val + d + 1]'(by omega)).2 := by simp [heq]
                                _ = ((paths' i).vertices[2 * i.val + d]'hd'_lt).2 - 1 := by 
                                    have : ((paths' i).vertices[2 * i.val + d + 1]'(by omega)).2 + 1 = 
                                           ((paths' i).vertices[2 * i.val + d]'hd'_lt).2 := hsnd
                                    omega
                                _ ≥ (((paths' i).vertices[2 * i.val]).2 - d) - 1 := by omega
                                _ = ((paths' i).vertices[2 * i.val]).2 - (d + 1) := by omega
                        have h_lt : j < (paths' i).vertices.length := by rw [hlen]; omega
                        have := haux (j - 2 * i.val) (by omega) (by rw [Nat.add_sub_cancel' (Nat.le_of_lt hj2i)]; exact h_lt)
                        simp only [Nat.add_sub_cancel' (Nat.le_of_lt hj2i)] at this
                        exact this
                      rw [hmid] at hsteps; omega
            exact this i.val i.isLt i rfl
          funext i
          apply dyckDigraph_path_ext
          exact hpaths_eq i

/-!
## Bridge Between LGV1 and LGV2 Path Representations

This section documents the connection between the path representations used in
LGV1.lean (list of steps) and LGV2.lean (list of vertices), and provides key
infrastructure for bridging them.

### Key Insight

A `LatticePath` (list of east/north steps) starting at point `A` can be converted to
a `SimpleDigraph.Path` by computing the list of vertices visited:
- `[east, north, east]` starting at `(0,0)` → `[(0,0), (1,0), (1,1), (2,1)]`

The conversion is bijective for paths between fixed endpoints.

### Status

The key theorem `sum_signed_ipatFinset_card_eq_zero` proves that the signed sum of
ipat counts is zero. To use this in LGV1.lean's `lgv_involution_cancellation`, we need:

```
numIpatsK A B σ = (ipatFinset integerLattice_pathFinite A (permuteKVertex σ B)).card
```

This requires showing that `ipatsFromTo` (LGV1) and `ipatFinset` (LGV2) have the same
cardinality, which follows from a bijection between the path tuple representations.

### Approach

The bijection works as follows:
1. Given a `LatticePath` (list of steps) starting at `A`, compute the vertex list
2. This vertex list forms a valid `SimpleDigraph.Path` in `integerLattice`
3. The map is injective because different step sequences give different vertex lists
4. The map is surjective because every `SimpleDigraph.Path` in `integerLattice`
   corresponds to a unique step sequence (each arc is either east or north)

The intersection property is preserved because both representations check if
any vertex appears in multiple paths of the tuple.
-/

/-- A lattice step on the integer lattice: either east (+1,0) or north (0,+1).
    
    This is the canonical definition for lattice steps. LGV1.lean defines an equivalent
    type `LGV1.LatticeStep` with an explicit equivalence `LGV1.latticeStepEquiv`.
    
    The two types are isomorphic via:
    - `LGV1.latticeStepEquiv : LGV1.LatticeStep ≃ LGV.LatticeStep'`
    - `LGV1.latticePathToLatticePath' : LGV1.LatticePath → LGV.LatticePath'`
    - `LGV1.latticePath'ToLatticePath : LGV.LatticePath' → LGV1.LatticePath`
    
    Note: The duplication exists because LGV1 imports LGV2, so LGV2 cannot reference
    LGV1's definitions. Both definitions are intentionally kept compatible. -/
inductive LatticeStep' : Type
  | east : LatticeStep'
  | north : LatticeStep'
  deriving DecidableEq, Repr

/-- Apply a step to a lattice point -/
def LatticeStep'.apply (s : LatticeStep') (p : ℤ × ℤ) : ℤ × ℤ :=
  match s with
  | east => (p.1 + 1, p.2)
  | north => (p.1, p.2 + 1)

/-- A lattice path as a list of steps (matching LGV1.lean's definition) -/
abbrev LatticePath' := List LatticeStep'

/-- Compute the endpoint of a lattice path starting from a given point -/
def LatticePath'.endpoint (path : LatticePath') (start : ℤ × ℤ) : ℤ × ℤ :=
  path.foldl (fun p s => s.apply p) start

/-- Compute all vertices visited by a lattice path, including start.
    For path = [s₁, s₂, ..., sₙ], this returns [start, s₁(start), s₂(s₁(start)), ...] -/
def LatticePath'.toVertices (path : LatticePath') (start : ℤ × ℤ) : List (ℤ × ℤ) :=
  match path with
  | [] => [start]
  | s :: rest => start :: LatticePath'.toVertices rest (s.apply start)

/-- The vertices list is nonempty -/
theorem LatticePath'.toVertices_nonempty (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toVertices path start) ≠ [] := by
  cases path <;> simp [toVertices]

/-- Each step creates a valid arc in the integer lattice -/
theorem LatticeStep'.apply_creates_arc (s : LatticeStep') (p : ℤ × ℤ) :
    integerLattice.arc p (s.apply p) := by
  cases s with
  | east => 
    simp only [apply, integerLattice]
    left
    simp
  | north => 
    simp only [apply, integerLattice]
    right
    simp

/-- Consecutive vertices in toVertices are connected by arcs -/
theorem LatticePath'.toVertices_arcs_valid (path : LatticePath') (start : ℤ × ℤ) :
    ∀ i : ℕ, ∀ hi : i + 1 < (LatticePath'.toVertices path start).length,
      integerLattice.arc ((LatticePath'.toVertices path start).get ⟨i, Nat.lt_of_succ_lt hi⟩)
        ((LatticePath'.toVertices path start).get ⟨i + 1, hi⟩) := by
  induction path generalizing start with
  | nil => intro i hi; simp [toVertices] at hi
  | cons s rest ih =>
    intro i hi
    simp only [toVertices] at hi ⊢
    cases i with
    | zero =>
      simp only [List.get_eq_getElem, List.getElem_cons_zero,
                 List.getElem_cons_succ]
      cases rest with
      | nil =>
        simp only [toVertices, List.getElem_singleton]
        exact LatticeStep'.apply_creates_arc s start
      | cons s' rest' =>
        simp only [toVertices, List.getElem_cons_zero]
        exact LatticeStep'.apply_creates_arc s start
    | succ j =>
      simp only [List.get_eq_getElem, List.getElem_cons_succ] at hi ⊢
      simp only [List.length_cons] at hi
      exact ih (s.apply start) j (by omega : j + 1 < (LatticePath'.toVertices rest (s.apply start)).length)

/-- Convert a lattice path to a SimpleDigraph.Path -/
noncomputable def LatticePath'.toPath (path : LatticePath') (start : ℤ × ℤ) : 
    SimpleDigraph.Path integerLattice where
  vertices := LatticePath'.toVertices path start
  nonempty := LatticePath'.toVertices_nonempty path start
  arcs_valid := LatticePath'.toVertices_arcs_valid path start

/-- The first vertex is the start point -/
theorem LatticePath'.toVertices_head (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toVertices path start).head (LatticePath'.toVertices_nonempty path start) = start := by
  cases path <;> simp [toVertices]

/-- The start of the converted path is the original start point -/
theorem LatticePath'.toPath_start (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toPath path start).start = start := by
  simp only [toPath, SimpleDigraph.Path.start, toVertices_head]

/-- The last vertex is the endpoint -/
theorem LatticePath'.toVertices_getLast (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toVertices path start).getLast (LatticePath'.toVertices_nonempty path start) = 
    LatticePath'.endpoint path start := by
  induction path generalizing start with
  | nil => simp [toVertices, endpoint]
  | cons s rest ih =>
    simp only [toVertices, endpoint, List.foldl_cons]
    rw [List.getLast_cons (LatticePath'.toVertices_nonempty rest (s.apply start))]
    exact ih (s.apply start)

/-- The finish of the converted path is the endpoint -/
theorem LatticePath'.toPath_finish (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toPath path start).finish = LatticePath'.endpoint path start := by
  simp only [toPath, SimpleDigraph.Path.finish, toVertices_getLast]

/-- Key bridge lemma: A lattice path going from A to B converts to a SimpleDigraph.Path
    from A to B. This is the foundation for showing the path representations are equivalent. -/
theorem LatticePath'.toPath_endpoints (path : LatticePath') (A B : ℤ × ℤ)
    (h : LatticePath'.endpoint path A = B) :
    (LatticePath'.toPath path A).start = A ∧ (LatticePath'.toPath path A).finish = B := by
  constructor
  · exact toPath_start path A
  · rw [toPath_finish, h]

/-- The length of the vertex list equals the number of steps plus one -/
theorem LatticePath'.toVertices_length (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toVertices path start).length = path.length + 1 := by
  induction path generalizing start with
  | nil => simp [toVertices]
  | cons s rest ih =>
    simp only [toVertices, List.length_cons]
    rw [ih (s.apply start)]

/-!
### Bridge Bijection Lemmas

The following lemmas establish that `LatticePath'.toPath` is a bijection between
step-based lattice paths and vertex-based digraph paths.

These lemmas provide the foundation for connecting LGV1.lean's counting results
with LGV2.lean's weighted results.
-/

/-- The vertices of a converted path match the original vertex list -/
theorem LatticePath'.toPath_vertices (path : LatticePath') (start : ℤ × ℤ) :
    (LatticePath'.toPath path start).vertices = LatticePath'.toVertices path start := rfl

/-- Two paths with the same vertices are equal -/
theorem SimpleDigraph.Path.ext_vertices' (p q : SimpleDigraph.Path integerLattice)
    (h : p.vertices = q.vertices) : p = q := by
  cases p; cases q
  simp only [SimpleDigraph.Path.mk.injEq]
  exact h

/-- toPath is injective: different step sequences give different paths.
    
    Proof sketch:
    1. If toPath p1 start = toPath p2 start, then their vertex lists are equal
    2. The vertex list uniquely determines the step sequence because:
       - Each arc in the integer lattice is uniquely determined by source and target
       - Given consecutive vertices u, v, the step is east iff v.1 = u.1 + 1
    3. By induction on the path length, equal vertex lists imply equal step sequences
    
    This is a key lemma for the bridge between LGV1 and LGV2 path representations. -/
theorem LatticePath'.toPath_injective (start : ℤ × ℤ) :
    Function.Injective (fun path => LatticePath'.toPath path start) := by
  intro p1 p2 h
  -- Two paths are equal iff their vertex lists are equal
  have hv : LatticePath'.toVertices p1 start = LatticePath'.toVertices p2 start := by
    have h1 : (LatticePath'.toPath p1 start).vertices = LatticePath'.toVertices p1 start := rfl
    have h2 : (LatticePath'.toPath p2 start).vertices = LatticePath'.toVertices p2 start := rfl
    rw [← h1, ← h2]
    exact congrArg SimpleDigraph.Path.vertices h
  -- Equal vertex lists imply equal step sequences
  -- The proof proceeds by induction on the path, showing that each step is uniquely
  -- determined by the pair of consecutive vertices in the integer lattice.
  -- Each step (east or north) produces a distinct target vertex from the same source.
  clear h
  induction p1 generalizing p2 start with
  | nil =>
    cases p2 with
    | nil => rfl
    | cons s rest =>
      exfalso
      have hlen1 : (toVertices [] start).length = 1 := by simp [toVertices]
      have hlen2 : (toVertices (s :: rest) start).length = (s :: rest).length + 1 := 
        toVertices_length (s :: rest) start
      rw [hv] at hlen1
      simp only [List.length_cons] at hlen2
      omega
  | cons s1 rest1 ih =>
    cases p2 with
    | nil =>
      exfalso
      have hlen1 : (toVertices [] start).length = 1 := by simp [toVertices]
      have hlen2 : (toVertices (s1 :: rest1) start).length = (s1 :: rest1).length + 1 := 
        toVertices_length (s1 :: rest1) start
      rw [← hv] at hlen1
      simp only [List.length_cons] at hlen2
      omega
    | cons s2 rest2 =>
      simp only [toVertices, List.cons.injEq] at hv
      -- Second vertices determine the steps
      have h_second : s1.apply start = s2.apply start := by
        have := hv.2
        cases rest1 <;> cases rest2 <;> simp only [toVertices, List.cons.injEq] at this
        all_goals first | exact this | exact this.1
      -- Since s1.apply start = s2.apply start, we have s1 = s2
      have h_step : s1 = s2 := by
        cases s1 <;> cases s2 <;> simp only [LatticeStep'.apply, Prod.mk.injEq] at h_second
        · rfl
        · omega
        · omega
        · rfl
      subst h_step
      congr 1
      -- Apply IH to the tails
      apply ih
      -- hv.2 is the equality of the tail vertex lists
      exact hv.2

/-!
### Surjectivity of toPath

To complete the bridge between path representations, we need to show that every
`SimpleDigraph.Path` in the integer lattice comes from a `LatticePath'`.

The key insight is that each arc in the integer lattice uniquely determines a step:
- If v.1 = u.1 + 1 (and v.2 = u.2), the step is east
- If v.2 = u.2 + 1 (and v.1 = u.1), the step is north
-/

/-- Convert an arc in the integer lattice to a step.
    This is the inverse operation to LatticeStep'.apply. -/
def arcToStep' (u v : ℤ × ℤ) (_h : integerLattice.arc u v) : LatticeStep' :=
  if v.1 = u.1 + 1 then LatticeStep'.east else LatticeStep'.north

/-- arcToStep' produces the correct step -/
theorem arcToStep'_apply (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    (arcToStep' u v h).apply u = v := by
  unfold arcToStep' LatticeStep'.apply
  simp only [integerLattice] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [h1, ↓reduceIte]
    ext <;> simp [h1, h2]
  · simp only [h1]
    ext <;> simp [h1, h2]

/-- Convert a vertex list to a step list (partial inverse of toVertices) -/
def verticesToSteps' : (vs : List (ℤ × ℤ)) → 
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < vs.length, 
      integerLattice.arc (vs.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vs.get ⟨i + 1, hi⟩)) → 
    LatticePath'
  | [], _ => []
  | [_], _ => []
  | u :: v :: rest, harcs => 
    let h : integerLattice.arc u v := harcs 0 (by simp)
    arcToStep' u v h :: verticesToSteps' (v :: rest) (fun i hi => harcs (i + 1) (by simp at hi ⊢; omega))

/-- Convert a SimpleDigraph.Path to a LatticePath' -/
def pathToLatticePath' (p : SimpleDigraph.Path integerLattice) : LatticePath' :=
  verticesToSteps' p.vertices p.arcs_valid

/-- verticesToSteps' produces the correct vertex list when applied to the original vertices -/
theorem verticesToSteps'_toVertices (vs : List (ℤ × ℤ)) (hne : vs ≠ [])
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < vs.length, 
      integerLattice.arc (vs.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vs.get ⟨i + 1, hi⟩)) :
    LatticePath'.toVertices (verticesToSteps' vs harcs) (vs.head hne) = vs := by
  induction vs with
  | nil => contradiction
  | cons u rest ih =>
    cases rest with
    | nil => simp [verticesToSteps', LatticePath'.toVertices]
    | cons v rest' =>
      simp only [verticesToSteps', LatticePath'.toVertices, List.head_cons, List.cons.injEq, true_and]
      have h_arc : integerLattice.arc u v := harcs 0 (by simp)
      have h_apply : (arcToStep' u v h_arc).apply u = v := arcToStep'_apply u v h_arc
      rw [h_apply]
      have harcs' : ∀ i : ℕ, ∀ hi : i + 1 < (v :: rest').length, 
          integerLattice.arc ((v :: rest').get ⟨i, Nat.lt_of_succ_lt hi⟩) 
            ((v :: rest').get ⟨i + 1, hi⟩) := fun i hi => harcs (i + 1) (by simp at hi ⊢; omega)
      exact ih (by simp) harcs'

/-- toPath is surjective: every SimpleDigraph.Path comes from a LatticePath'.
    
    This completes the bijection between step-based and vertex-based path representations.
    Together with `toPath_injective`, this shows that the two representations are equivalent. -/
theorem LatticePath'.toPath_surjective (start : ℤ × ℤ) :
    ∀ p : SimpleDigraph.Path integerLattice, p.start = start → 
      ∃ path : LatticePath', LatticePath'.toPath path start = p := by
  intro p hstart
  use pathToLatticePath' p
  unfold pathToLatticePath' LatticePath'.toPath
  apply SimpleDigraph.Path.ext_vertices'
  simp only
  have := verticesToSteps'_toVertices p.vertices p.nonempty p.arcs_valid
  rw [← hstart]
  simp only [SimpleDigraph.Path.start] at this ⊢
  exact this

/-- The bijection between LatticePath' and SimpleDigraph.Path starting at a fixed point.
    
    This establishes that the two path representations are equivalent, which is the key
    step needed to bridge LGV1.lean's counting results with LGV2.lean's weighted results. -/
noncomputable def latticePath'Equiv (start : ℤ × ℤ) :
    LatticePath' ≃ { p : SimpleDigraph.Path integerLattice // p.start = start } where
  toFun path := ⟨LatticePath'.toPath path start, LatticePath'.toPath_start path start⟩
  invFun p := pathToLatticePath' p.val
  left_inv path := by
    have h := LatticePath'.toPath_injective start
    apply h
    simp only [LatticePath'.toPath, pathToLatticePath']
    apply SimpleDigraph.Path.ext_vertices'
    have := verticesToSteps'_toVertices (LatticePath'.toVertices path start) 
      (LatticePath'.toVertices_nonempty path start) (LatticePath'.toVertices_arcs_valid path start)
    simp only [LatticePath'.toVertices_head] at this
    exact this
  right_inv p := by
    have hstart : p.val.start = start := p.property
    apply Subtype.ext
    simp only [LatticePath'.toPath, pathToLatticePath']
    apply SimpleDigraph.Path.ext_vertices'
    have := verticesToSteps'_toVertices p.val.vertices p.val.nonempty p.val.arcs_valid
    simp only [SimpleDigraph.Path.start] at this hstart
    rw [hstart] at this
    exact this

/-!
### Path Tuple Bridge

This section provides the bridge between LGV1-style path tuples (using LatticePath = List LatticeStep)
and LGV2-style path tuples (using SimpleDigraph.Path).

The key results are:
1. `latticePath'TupleEquiv` - bijection between path tuples
2. `latticePath'Tuple_isIntersecting_iff` - intersection property is preserved

These results allow us to transfer the counting result `sum_signed_ipatFinset_card_eq_zero`
from LGV2 types to LGV1 types.
-/

/-- A path tuple in the LGV1 style: k paths from A to B where each path is a list of steps. -/
structure LatticePath'Tuple (k : ℕ) (A B : kVertex (ℤ × ℤ) k) where
  /-- The paths in the tuple -/
  paths : Fin k → LatticePath'
  /-- Each path goes from A_i to B_i -/
  valid : ∀ i, LatticePath'.endpoint (paths i) (A i) = B i

@[ext]
lemma LatticePath'Tuple.ext {k : ℕ} {A B : kVertex (ℤ × ℤ) k} 
    {pt1 pt2 : LatticePath'Tuple k A B} (h : ∀ i, pt1.paths i = pt2.paths i) : pt1 = pt2 := by
  cases pt1; cases pt2
  simp only [mk.injEq]
  funext i
  exact h i

/-- The vertices visited by a path in a LatticePath'Tuple -/
def LatticePath'Tuple.verticesOf {k : ℕ} {A B : kVertex (ℤ × ℤ) k} 
    (pt : LatticePath'Tuple k A B) (i : Fin k) : Set (ℤ × ℤ) :=
  { p | p ∈ LatticePath'.toVertices (pt.paths i) (A i) }

/-- A LatticePath'Tuple is non-intersecting if no two paths share a vertex -/
def LatticePath'Tuple.isNonIntersecting {k : ℕ} {A B : kVertex (ℤ × ℤ) k} 
    (pt : LatticePath'Tuple k A B) : Prop :=
  ∀ i j, i ≠ j → Disjoint (pt.verticesOf i) (pt.verticesOf j)

/-- A LatticePath'Tuple is intersecting if it is not non-intersecting -/
def LatticePath'Tuple.isIntersecting {k : ℕ} {A B : kVertex (ℤ × ℤ) k} 
    (pt : LatticePath'Tuple k A B) : Prop :=
  ¬pt.isNonIntersecting

/-- Convert a LatticePath'Tuple to a PathTuple -/
noncomputable def latticePath'TupleToPathTuple {k : ℕ} {A B : kVertex (ℤ × ℤ) k}
    (pt : LatticePath'Tuple k A B) : PathTuple integerLattice k A B where
  paths := fun i => LatticePath'.toPath (pt.paths i) (A i)
  starts := fun i => LatticePath'.toPath_start (pt.paths i) (A i)
  finishes := fun i => by
    rw [LatticePath'.toPath_finish]
    exact pt.valid i

/-- Convert a PathTuple to a LatticePath'Tuple -/
noncomputable def pathTupleToLatticePath'Tuple {k : ℕ} {A B : kVertex (ℤ × ℤ) k}
    (pt : PathTuple integerLattice k A B) : LatticePath'Tuple k A B where
  paths := fun i => pathToLatticePath' (pt.paths i)
  valid := fun i => by
    have h := verticesToSteps'_toVertices (pt.paths i).vertices (pt.paths i).nonempty (pt.paths i).arcs_valid
    have hstart : (pt.paths i).start = A i := pt.starts i
    have hfinish : (pt.paths i).finish = B i := pt.finishes i
    simp only [SimpleDigraph.Path.start] at hstart
    simp only [SimpleDigraph.Path.finish] at hfinish
    unfold pathToLatticePath'
    -- The endpoint is computed by foldl, which equals the last vertex
    have h_toVertices : LatticePath'.toVertices (verticesToSteps' (pt.paths i).vertices (pt.paths i).arcs_valid) 
        ((pt.paths i).vertices.head (pt.paths i).nonempty) = (pt.paths i).vertices := h
    rw [hstart] at h_toVertices
    have h_endpoint : LatticePath'.endpoint (verticesToSteps' (pt.paths i).vertices (pt.paths i).arcs_valid) (A i) =
        ((pt.paths i).vertices.getLast (pt.paths i).nonempty) := by
      rw [← LatticePath'.toVertices_getLast]
      simp only [h_toVertices]
    unfold LatticePath'.endpoint at h_endpoint ⊢
    rw [h_endpoint, hfinish]

/-- The bijection between LatticePath'Tuple and PathTuple -/
noncomputable def latticePath'TupleEquiv {k : ℕ} (A B : kVertex (ℤ × ℤ) k) :
    LatticePath'Tuple k A B ≃ PathTuple integerLattice k A B where
  toFun := latticePath'TupleToPathTuple
  invFun := pathTupleToLatticePath'Tuple
  left_inv pt := by
    apply LatticePath'Tuple.ext
    intro i
    simp only [pathTupleToLatticePath'Tuple, latticePath'TupleToPathTuple]
    -- Need to show: pathToLatticePath' (LatticePath'.toPath (pt.paths i) (A i)) = pt.paths i
    have h := LatticePath'.toPath_injective (A i)
    apply h
    simp only [LatticePath'.toPath, pathToLatticePath']
    apply SimpleDigraph.Path.ext_vertices'
    have := verticesToSteps'_toVertices (LatticePath'.toVertices (pt.paths i) (A i)) 
      (LatticePath'.toVertices_nonempty (pt.paths i) (A i)) 
      (LatticePath'.toVertices_arcs_valid (pt.paths i) (A i))
    simp only [LatticePath'.toVertices_head] at this
    exact this
  right_inv pt := by
    apply PathTuple.ext
    intro i
    simp only [latticePath'TupleToPathTuple, pathTupleToLatticePath'Tuple]
    -- Need to show: LatticePath'.toPath (pathToLatticePath' (pt.paths i)) (A i) = pt.paths i
    simp only [LatticePath'.toPath, pathToLatticePath']
    apply SimpleDigraph.Path.ext_vertices'
    have := verticesToSteps'_toVertices (pt.paths i).vertices (pt.paths i).nonempty (pt.paths i).arcs_valid
    have hstart : (pt.paths i).start = A i := pt.starts i
    simp only [SimpleDigraph.Path.start] at this hstart
    rw [hstart] at this
    exact this

/-- The vertices of a converted path match the original vertices -/
theorem latticePath'TupleToPathTuple_vertices {k : ℕ} {A B : kVertex (ℤ × ℤ) k}
    (pt : LatticePath'Tuple k A B) (i : Fin k) :
    ((latticePath'TupleToPathTuple pt).paths i).vertices = 
    LatticePath'.toVertices (pt.paths i) (A i) := rfl

/-- The intersection property is preserved by the bijection -/
theorem latticePath'Tuple_isIntersecting_iff {k : ℕ} {A B : kVertex (ℤ × ℤ) k}
    (pt : LatticePath'Tuple k A B) :
    pt.isIntersecting ↔ (latticePath'TupleToPathTuple pt).isIntersecting := by
  unfold LatticePath'Tuple.isIntersecting LatticePath'Tuple.isNonIntersecting
  unfold PathTuple.isIntersecting PathTuple.isNonIntersecting
  -- Both sides check if any two paths share a vertex
  -- The vertices are the same because toPath preserves vertices
  simp only [not_forall, not_not]
  constructor
  · -- If pt is intersecting, then the converted tuple is intersecting
    intro ⟨i, j, hij, hnotdisj⟩
    use i, j, hij
    -- hnotdisj : ¬Disjoint (pt.verticesOf i) (pt.verticesOf j)
    -- goal : pathsIntersect (paths i) (paths j)
    rw [Set.not_disjoint_iff] at hnotdisj
    obtain ⟨v, hvi, hvj⟩ := hnotdisj
    unfold pathsIntersect
    use v
    simp only [LatticePath'Tuple.verticesOf, Set.mem_ofPred_eq] at hvi hvj
    simp only [latticePath'TupleToPathTuple, LatticePath'.toPath]
    exact ⟨hvi, hvj⟩
  · -- If the converted tuple is intersecting, then pt is intersecting
    intro ⟨i, j, hij, hpaths⟩
    use i, j, hij
    -- hpaths : pathsIntersect (paths i) (paths j)
    -- goal : ¬Disjoint (pt.verticesOf i) (pt.verticesOf j)
    unfold pathsIntersect at hpaths
    obtain ⟨v, hvi, hvj⟩ := hpaths
    rw [Set.not_disjoint_iff]
    use v
    simp only [latticePath'TupleToPathTuple, LatticePath'.toPath] at hvi hvj
    simp only [LatticePath'Tuple.verticesOf, Set.mem_ofPred_eq]
    exact ⟨hvi, hvj⟩

end LGV
