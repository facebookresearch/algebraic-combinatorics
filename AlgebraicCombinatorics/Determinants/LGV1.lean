/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.Determinants.LGV2

/-!
# The Lindström-Gessel-Viennot Lemma: Part 1

This file formalizes the first part of the Lindström-Gessel-Viennot (LGV) lemma,
covering the basic definitions and counting results for lattice paths.

## Main definitions

* `LGV1.LatticePoint` - A point on the integer lattice ℤ²
* `LGV1.integerLattice` - The integer lattice as a Mathlib `Digraph`
* `LGV1.LatticePath` - A path on the integer lattice using only east (right) and north (up) steps
* `LGV1.LatticePath.stepCount` - The total number of steps in a path
* `LGV1.LatticePath.eastStepCount` - The number of east steps in a path
* `LGV1.PathTuple` - A k-tuple of lattice paths from k source vertices to k target vertices
* `LGV1.PathTuple.isNonIntersecting` - Property that no two paths share a vertex (nipat)
* `LGV1.PathTuple.isIntersecting` - Property that some two paths share a vertex (ipat)
* `LGV1.kVertex` - A k-tuple of lattice points

## Main results

* `latticePath_count` - Number of paths from (a,b) to (c,d) equals C(c+d-a-b, c-a)
  (Proposition prop.lgv.1-paths.ct)
* `lgv_two_paths` - LGV lemma for k=2: determinant equals #nipats to (B,B') - #nipats to (B',B)
  (Proposition prop.lgv.2paths.count)
* `baby_jordan_curve` - Paths from A to B' and A' to B must intersect under NW conditions
  (Proposition prop.lgv.jordan-2)
* `binom_log_concave` - C(n,k)² ≥ C(n,k-1)·C(n,k+1)
  (Corollary cor.lgv.binom-unimod)
* `lgv_k_paths` - General LGV lemma: determinant equals signed sum of nipat counts
  (Proposition prop.lgv.kpaths.count)

## References

* Source: AlgebraicCombinatorics/tex/Determinants/LGV1.tex (sec.det.comb.lgv)

## Implementation notes

We formalize lattice paths as lists of steps (east or north), rather than as sequences
of vertices. This makes it easier to work with path concatenation and step counting.

The LGV lemma relates determinants to non-intersecting lattice paths. The key insight
is a sign-reversing involution that cancels intersecting path tuples.

### Relationship with LGV2.lean

This file (LGV1.lean) and LGV2.lean both work with the integer lattice digraph, but
use different representations:

- **LGV1.lean**: Uses Mathlib's `Digraph` type and `LatticePath` (list of steps: east/north)
- **LGV2.lean**: Uses `LGV.SimpleDigraph` (custom structure with irreflexivity) and
  `SimpleDigraph.Path` (list of vertices)

The integer lattice definitions have equivalent adjacency relations:
- LGV1: `integerLattice_adj_iff p q : integerLattice.Adj p q ↔ q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1)`
- LGV2: `integerLattice_arc_iff u v : integerLattice.arc u v ↔ v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1)`

### LatticeStep and LatticePath equivalence

Both files define a `LatticeStep` type for representing east/north steps:
- `LGV1.LatticeStep` (this file)
- `LGV.LatticeStep'` (in LGV2.lean)

These are equivalent types, with explicit conversion functions:
- `latticeStepEquiv : LatticeStep ≃ LGV.LatticeStep'`
- `latticePathToLatticePath' : LatticePath → LGV.LatticePath'`
- `latticePath'ToLatticePath : LGV.LatticePath' → LatticePath`

The duplication exists because LGV1 imports LGV2, preventing LGV2 from referencing
LGV1's definitions. Both definitions are kept compatible with trivial conversions.

LGV2.lean contains the complete weighted LGV lemma proof. This file contains the
counting case infrastructure with lattice-specific path counting results.
-/

open Finset BigOperators Matrix

namespace LGV1

/-!
## The Integer Lattice (Definition def.lgv.lattice)

The integer lattice ℤ² is an infinite digraph with vertices at integer points
and directed edges (arcs) going east (i,j) → (i+1,j) and north (i,j) → (i,j+1).

This digraph is acyclic and path-finite (only finitely many paths between any two points).

### Formalization of Definition def.lgv.lattice

From the TeX source (AlgebraicCombinatorics/tex/Determinants/LGV1.tex):

> We consider the infinite simple digraph with vertex set ℤ² (so the vertices are pairs
> of integers) and arcs:
>   (i,j) → (i+1,j)  for all (i,j) ∈ ℤ²  [east-steps/right-steps]
>   (i,j) → (i,j+1)  for all (i,j) ∈ ℤ²  [north-steps/up-steps]

The entire digraph is denoted by ℤ² and called the "integer lattice" or "integer grid".
-/

/-- A point on the integer lattice ℤ².
    The vertices of the integer lattice are pairs of integers.
    Label: def.lgv.lattice -/
abbrev LatticePoint := ℤ × ℤ

/-- The x-coordinate of a lattice point. -/
def LatticePoint.x (p : LatticePoint) : ℤ := p.1

/-- The y-coordinate of a lattice point. -/
def LatticePoint.y (p : LatticePoint) : ℤ := p.2

/-- Simp lemma for the x-coordinate of a constructed lattice point. -/
@[simp] lemma LatticePoint.x_mk (a b : ℤ) : LatticePoint.x (a, b) = a := rfl

/-- Simp lemma for the y-coordinate of a constructed lattice point. -/
@[simp] lemma LatticePoint.y_mk (a b : ℤ) : LatticePoint.y (a, b) = b := rfl

/-- The coordinate sum of a lattice point (x + y). -/
def LatticePoint.coordSum (p : LatticePoint) : ℤ := p.1 + p.2

/-- Simp lemma for the coordinate sum of a constructed lattice point. -/
@[simp] lemma LatticePoint.coordSum_mk (a b : ℤ) : LatticePoint.coordSum (a, b) = a + b := rfl

/-!
### The Integer Lattice as a Digraph

We formalize the integer lattice as a `Digraph` instance, where an arc exists from
vertex `p` to vertex `q` if and only if `q` is obtained from `p` by either:
- An east step: q = (p.1 + 1, p.2)
- A north step: q = (p.1, p.2 + 1)
-/

/-- The adjacency relation for the integer lattice digraph.
    There is an arc from p to q iff q is one step east or north of p.
    Label: eq.def.lgv.lattice.east, eq.def.lgv.lattice.north -/
def IntegerLatticeAdj (p q : LatticePoint) : Prop :=
  q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1)

/-- The integer lattice as a digraph.
    This is the digraph with vertex set ℤ² and arcs (i,j) → (i+1,j) and (i,j) → (i,j+1).
    Label: def.lgv.lattice -/
def integerLattice : Digraph LatticePoint where
  Adj := IntegerLatticeAdj

/-- Decidability of adjacency in the integer lattice. -/
instance : DecidableRel IntegerLatticeAdj :=
  fun p q => decidable_of_iff
    ((q.1 = p.1 + 1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2 = p.2 + 1))
    (by simp only [IntegerLatticeAdj, Prod.ext_iff])

/-- An arc exists from p to (p.1 + 1, p.2) (east step).
    Label: eq.def.lgv.lattice.east -/
theorem integerLattice_adj_east (p : LatticePoint) :
    integerLattice.Adj p (p.1 + 1, p.2) := by
  unfold integerLattice IntegerLatticeAdj
  exact Or.inl rfl

/-- An arc exists from p to (p.1, p.2 + 1) (north step).
    Label: eq.def.lgv.lattice.north -/
theorem integerLattice_adj_north (p : LatticePoint) :
    integerLattice.Adj p (p.1, p.2 + 1) := by
  unfold integerLattice IntegerLatticeAdj
  exact Or.inr rfl

/-- Characterization of adjacency: q is adjacent from p iff q is one step east or north.
    Label: def.lgv.lattice -/
theorem integerLattice_adj_iff (p q : LatticePoint) :
    integerLattice.Adj p q ↔ q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1) := by
  unfold integerLattice IntegerLatticeAdj
  rfl

/-- The integer lattice has no self-loops (irreflexive). -/
theorem integerLattice_irrefl (p : LatticePoint) : ¬integerLattice.Adj p p := by
  simp only [integerLattice_adj_iff, Prod.ext_iff]
  intro h
  rcases h with ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega

/-- The integer lattice is acyclic: the coordinate sum strictly increases along any arc.
    This implies there are no cycles. -/
theorem integerLattice_coordSum_increases {p q : LatticePoint}
    (h : integerLattice.Adj p q) : p.coordSum < q.coordSum := by
  simp only [integerLattice_adj_iff] at h
  rcases h with rfl | rfl <;>
    simp only [LatticePoint.coordSum] <;> omega

/-- The integer lattice is acyclic: if there's a chain from p to q, then p.coordSum ≤ q.coordSum.
    This implies there are no cycles: any path from p to itself would require p.coordSum < p.coordSum. -/
theorem integerLattice_acyclic : ∀ p q : LatticePoint,
    (∃ path : List LatticePoint, path.IsChain integerLattice.Adj ∧
      path.head? = some p ∧ path.getLast? = some q) →
    p.coordSum ≤ q.coordSum := by
  intro p q ⟨path, hchain, hp, hq⟩
  induction path generalizing p q with
  | nil =>
    simp at hp
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [List.head?_cons, Option.some.injEq] at hp
      simp only [List.getLast?_singleton, Option.some.injEq] at hq
      rw [← hp, ← hq]
    | cons y ys =>
      simp only [List.head?_cons, Option.some.injEq] at hp
      -- x is p, and we have a chain p :: y :: ys with last element q
      have hadj : integerLattice.Adj x y := by
        simp only [List.isChain_cons] at hchain
        exact hchain.1 y rfl
      have hchain' : (y :: ys).IsChain integerLattice.Adj := by
        simp only [List.isChain_cons] at hchain ⊢
        exact hchain.2
      have hq' : (y :: ys).getLast? = some q := hq
      have hy_head : (y :: ys).head? = some y := rfl
      have hle : y.coordSum ≤ q.coordSum := ih y q hchain' hy_head hq'
      have hlt : x.coordSum < y.coordSum := integerLattice_coordSum_increases hadj
      rw [← hp]
      omega

/-!
## Lattice Steps and Paths

A step on the lattice is either east (right) or north (up).
A lattice path is a sequence of steps starting from a given point.

We formalize paths as lists of steps rather than lists of vertices, which makes
it easier to work with path concatenation and step counting.
-/

/-- A step on the integer lattice: either east (right) or north (up).
    - east: (i,j) → (i+1,j)
    - north: (i,j) → (i,j+1)
    
    This type is equivalent to `LGV.LatticeStep'` defined in LGV2.lean.
    The equivalence is provided by `latticeStepEquiv : LatticeStep ≃ LGV.LatticeStep'`.
    
    Label: eq.def.lgv.lattice.east, eq.def.lgv.lattice.north -/
inductive LatticeStep : Type
  | east : LatticeStep  -- (i,j) → (i+1,j)
  | north : LatticeStep -- (i,j) → (i,j+1)
  deriving DecidableEq, Repr, Fintype

/-- Apply a step to a lattice point. -/
def LatticeStep.apply (s : LatticeStep) (p : LatticePoint) : LatticePoint :=
  match s with
  | east => (p.1 + 1, p.2)
  | north => (p.1, p.2 + 1)

/-- A step corresponds to an arc in the integer lattice digraph. -/
theorem LatticeStep.isArc (s : LatticeStep) (p : LatticePoint) :
    integerLattice.Adj p (s.apply p) := by
  cases s with
  | east => exact integerLattice_adj_east p
  | north => exact integerLattice_adj_north p

/-- A lattice path is a list of steps.
    
    This type is equivalent to `LGV.LatticePath'` defined in LGV2.lean.
    Conversion functions are provided:
    - `latticePathToLatticePath' : LatticePath → LGV.LatticePath'`
    - `latticePath'ToLatticePath : LGV.LatticePath' → LatticePath`
    - `latticePathToLatticePath'_endpoint` proves endpoint preservation -/
abbrev LatticePath := List LatticeStep

/-- The endpoint of a path starting from a given point. -/
def LatticePath.endpoint (path : LatticePath) (start : LatticePoint) : LatticePoint :=
  path.foldl (fun p s => s.apply p) start

/-- Simp lemma: the endpoint of an empty path is the start. -/
@[simp] lemma LatticePath.endpoint_nil (start : LatticePoint) :
    LatticePath.endpoint [] start = start := rfl

/-- Simp lemma: the endpoint of a cons path applies the first step then continues. -/
@[simp] lemma LatticePath.endpoint_cons (s : LatticeStep) (path : LatticePath) (start : LatticePoint) :
    LatticePath.endpoint (s :: path) start = LatticePath.endpoint path (s.apply start) := by
  simp [endpoint, List.foldl_cons]

/-- The endpoint of appended paths: endpoint(p1 ++ p2, A) = endpoint(p2, endpoint(p1, A)). -/
theorem LatticePath.endpoint_append (path1 path2 : LatticePath) (start : LatticePoint) :
    LatticePath.endpoint (path1 ++ path2) start =
    LatticePath.endpoint path2 (LatticePath.endpoint path1 start) := by
  unfold LatticePath.endpoint
  rw [List.foldl_append]

/-- The number of steps in a path. -/
def LatticePath.stepCount (path : LatticePath) : ℕ := path.length

/-- Simp lemma: the step count of an empty path is 0. -/
@[simp] lemma LatticePath.stepCount_nil : LatticePath.stepCount [] = 0 := rfl

/-- Simp lemma: the step count of a cons path is one more than the rest. -/
@[simp] lemma LatticePath.stepCount_cons (s : LatticeStep) (path : LatticePath) :
    LatticePath.stepCount (s :: path) = path.length + 1 := rfl

/-- The number of east steps in a path. -/
def LatticePath.eastStepCount (path : LatticePath) : ℕ :=
  path.count LatticeStep.east

/-- Simp lemma: the east step count of an empty path is 0. -/
@[simp] lemma LatticePath.eastStepCount_nil : LatticePath.eastStepCount [] = 0 := by
  simp [eastStepCount]

/-- Simp lemma: the east step count of a path starting with an east step. -/
@[simp] lemma LatticePath.eastStepCount_cons_east (path : LatticePath) :
    LatticePath.eastStepCount (LatticeStep.east :: path) = path.eastStepCount + 1 := by
  simp [eastStepCount]

/-- Simp lemma: the east step count of a path starting with a north step. -/
@[simp] lemma LatticePath.eastStepCount_cons_north (path : LatticePath) :
    LatticePath.eastStepCount (LatticeStep.north :: path) = path.eastStepCount := by
  simp [eastStepCount]

/-- The number of north steps in a path. -/
def LatticePath.northStepCount (path : LatticePath) : ℕ :=
  path.count LatticeStep.north

/-- Simp lemma: the north step count of an empty path is 0. -/
@[simp] lemma LatticePath.northStepCount_nil : LatticePath.northStepCount [] = 0 := by
  simp [northStepCount]

/-- Simp lemma: the north step count of a path starting with a north step. -/
@[simp] lemma LatticePath.northStepCount_cons_north (path : LatticePath) :
    LatticePath.northStepCount (LatticeStep.north :: path) = path.northStepCount + 1 := by
  simp [northStepCount]

/-- Simp lemma: the north step count of a path starting with an east step. -/
@[simp] lemma LatticePath.northStepCount_cons_east (path : LatticePath) :
    LatticePath.northStepCount (LatticeStep.east :: path) = path.northStepCount := by
  simp [northStepCount]

/-- A path's step count equals east steps plus north steps. -/
theorem LatticePath.stepCount_eq_east_plus_north (path : LatticePath) :
    path.stepCount = path.eastStepCount + path.northStepCount := by
  unfold stepCount eastStepCount northStepCount
  rw [List.length_eq_countP_add_countP (· == LatticeStep.east)]
  simp only [List.count, beq_iff_eq]
  congr 1
  apply List.countP_congr
  intro x _
  cases x <;> simp

/-- All vertices visited by a path, including start and end. -/
def LatticePath.vertices (path : LatticePath) (start : LatticePoint) : List LatticePoint :=
  start :: path.scanl (fun p s => s.apply p) start |>.tail

/-- Check if a path goes from point a to point b. -/
def LatticePath.isPathFromTo (path : LatticePath) (a b : LatticePoint) : Prop :=
  path.endpoint a = b

/-- If a path goes from A to B, then take n goes from A to an intermediate point,
    and drop n goes from that point to B. -/
theorem LatticePath.isPathFromTo_take_drop (path : LatticePath) (n : ℕ) (A B : LatticePoint)
    (h : LatticePath.isPathFromTo path A B) :
    let mid := LatticePath.endpoint (path.take n) A
    LatticePath.isPathFromTo (path.take n) A mid ∧ LatticePath.isPathFromTo (path.drop n) mid B := by
  constructor
  · rfl
  · unfold LatticePath.isPathFromTo at h ⊢
    have key : LatticePath.endpoint (path.take n ++ path.drop n) A = LatticePath.endpoint path A := by
      rw [List.take_append_drop]
    rw [endpoint_append] at key
    rw [key, h]

/-- If head goes A→v and tail goes v→B, then head ++ tail goes A→B. -/
theorem LatticePath.isPathFromTo_append (head tail : LatticePath) (A v B : LatticePoint)
    (hhead : LatticePath.isPathFromTo head A v) (htail : LatticePath.isPathFromTo tail v B) :
    LatticePath.isPathFromTo (head ++ tail) A B := by
  unfold LatticePath.isPathFromTo at *
  rw [endpoint_append, hhead, htail]

/-- Each step increases the coordinate sum by 1. -/
lemma LatticeStep.coordSum_apply (s : LatticeStep) (p : LatticePoint) :
    (s.apply p).coordSum = p.coordSum + 1 := by
  cases s <;> simp [LatticeStep.apply, LatticePoint.coordSum] <;> ring

/-- The coordinate sum increases by the step count along any path. -/
lemma LatticePath.coordSum_endpoint (path : LatticePath) (start : LatticePoint) :
    (path.endpoint start).coordSum = start.coordSum + path.stepCount := by
  induction path generalizing start with
  | nil => simp [endpoint, stepCount, LatticePoint.coordSum]
  | cons step rest ih =>
    simp only [endpoint, stepCount, List.foldl_cons, List.length_cons]
    have h1 := ih (step.apply start)
    simp only [endpoint, stepCount] at h1
    rw [h1]
    rw [LatticeStep.coordSum_apply]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-!
## Counting Paths (Proposition prop.lgv.1-paths.ct)

The number of lattice paths from (a,b) to (c,d) is:
- C(c+d-a-b, c-a) if c+d ≥ a+b (i.e., d-b ≥ a-c)
- 0 if c+d < a+b

This follows from:
- Observation 1: Each path has exactly c+d-a-b steps
- Observation 2: Each path has exactly c-a east steps
- Observation 3: A path with these counts from (a,b) must end at (c,d)
-/

/-- Observation 1: Any path from (a,b) to (c,d) has exactly c+d-a-b steps.
    Label: pf.prop.lgv.1-paths.ct.o1 -/
theorem path_stepCount_eq (path : LatticePath) (a b c d : ℤ)
    (h : path.isPathFromTo (a, b) (c, d)) :
    (path.stepCount : ℤ) = c + d - a - b := by
  have hsum := LatticePath.coordSum_endpoint path (a, b)
  simp only [LatticePoint.coordSum, LatticePath.endpoint] at hsum
  unfold LatticePath.isPathFromTo LatticePath.endpoint at h
  rw [h] at hsum
  omega

/-- Helper: The x-coordinate of the endpoint equals start.x + eastStepCount. -/
theorem endpoint_x_eq (path : LatticePath) (start : LatticePoint) :
    (path.endpoint start).1 = start.1 + path.eastStepCount := by
  induction path generalizing start with
  | nil => simp [LatticePath.endpoint, LatticePath.eastStepCount]
  | cons step rest ih =>
    unfold LatticePath.endpoint LatticePath.eastStepCount at ih ⊢
    simp only [List.foldl_cons, List.count_cons]
    cases step with
    | east =>
      simp only [LatticeStep.apply, beq_self_eq_true, ↓reduceIte]
      specialize ih (start.1 + 1, start.2)
      simp only [LatticeStep.apply] at ih
      rw [ih]
      push_cast
      ring
    | north =>
      simp only [LatticeStep.apply, beq_iff_eq, reduceCtorEq, ↓reduceIte, add_zero]
      specialize ih (start.1, start.2 + 1)
      simp only [LatticeStep.apply] at ih
      rw [ih]

/-- Observation 2: Any path from (a,b) to (c,d) has exactly c-a east steps.
    Label: pf.prop.lgv.1-paths.ct.o2 -/
theorem path_eastStepCount_eq (path : LatticePath) (a b c d : ℤ)
    (h : path.isPathFromTo (a, b) (c, d)) :
    (path.eastStepCount : ℤ) = c - a := by
  have hx := endpoint_x_eq path (a, b)
  simp only [LatticePath.isPathFromTo, LatticePath.endpoint] at h
  simp only [LatticePath.endpoint] at hx
  rw [h] at hx
  simp at hx
  omega

/-- The endpoint of a path equals the start shifted by east and north step counts. -/
private lemma endpoint_eq (path : LatticePath) (a : LatticePoint) :
    path.endpoint a = (a.1 + path.count LatticeStep.east, a.2 + path.count LatticeStep.north) := by
  induction path generalizing a with
  | nil => simp [LatticePath.endpoint]
  | cons s rest ih =>
    unfold LatticePath.endpoint at *
    simp only [List.foldl_cons]
    cases s with
    | east =>
      have h1 : LatticeStep.east ≠ LatticeStep.north := by decide
      simp only [LatticeStep.apply, List.count_cons_self, List.count_cons_of_ne h1]
      specialize ih (a.1 + 1, a.2)
      convert ih using 2
      all_goals push_cast; ring
    | north =>
      have h1 : LatticeStep.north ≠ LatticeStep.east := by decide
      simp only [LatticeStep.apply, List.count_cons_self, List.count_cons_of_ne h1]
      specialize ih (a.1, a.2 + 1)
      convert ih using 2
      all_goals push_cast; ring

/-- A path's length equals the sum of east and north step counts. -/
private lemma length_eq_count_sum (path : LatticePath) :
    path.length = path.count LatticeStep.east + path.count LatticeStep.north := by
  induction path with
  | nil => simp
  | cons s rest ih =>
    cases s with
    | east =>
      have h1 : LatticeStep.east ≠ LatticeStep.north := by decide
      simp only [List.length_cons, List.count_cons_self, List.count_cons_of_ne h1]
      omega
    | north =>
      have h1 : LatticeStep.north ≠ LatticeStep.east := by decide
      simp only [List.length_cons, List.count_cons_self, List.count_cons_of_ne h1]
      omega

/-- The set of all lattice paths from point a to point b. -/
def pathsFromTo (a b : LatticePoint) : Set LatticePath :=
  { path | path.isPathFromTo a b }

/-- The set of paths from a to b is finite. -/
theorem pathsFromTo_finite (a b : LatticePoint) : (pathsFromTo a b).Finite := by
  -- If b.1 < a.1 or b.2 < a.2, there are no paths
  by_cases h : a.1 ≤ b.1 ∧ a.2 ≤ b.2
  · -- Case: valid direction, paths exist but are finite
    -- Any path from a to b has exactly (b.1 - a.1) east steps and (b.2 - a.2) north steps
    -- Total length is (b.1 - a.1) + (b.2 - a.2)
    let n := (b.1 - a.1).toNat + (b.2 - a.2).toNat
    -- The set of paths is a subset of all lists of length at most n
    have hsub : pathsFromTo a b ⊆ {path : LatticePath | path.length ≤ n} := by
      intro path hpath
      simp only [Set.mem_setOf_eq]
      unfold pathsFromTo LatticePath.isPathFromTo at hpath
      rw [Set.mem_setOf_eq] at hpath
      rw [endpoint_eq] at hpath
      have hpath_pair : a.1 + ↑(path.count LatticeStep.east) = b.1 ∧
                        a.2 + ↑(path.count LatticeStep.north) = b.2 := by
        rw [Prod.ext_iff] at hpath
        exact hpath
      obtain ⟨hpath1, hpath2⟩ := hpath_pair
      have east_count : (path.count LatticeStep.east : ℤ) = b.1 - a.1 := by omega
      have north_count : (path.count LatticeStep.north : ℤ) = b.2 - a.2 := by omega
      rw [length_eq_count_sum]
      have he : path.count LatticeStep.east = (b.1 - a.1).toNat := by
        have h1 : 0 ≤ b.1 - a.1 := by omega
        omega
      have hn : path.count LatticeStep.north = (b.2 - a.2).toNat := by
        have h1 : 0 ≤ b.2 - a.2 := by omega
        omega
      omega
    apply Set.Finite.subset _ hsub
    -- Lists of bounded length from a finite type form a finite set
    exact List.finite_length_le LatticeStep n
  · -- Case: invalid direction, no paths exist
    push_neg at h
    have hempty : pathsFromTo a b = ∅ := by
      ext path
      unfold pathsFromTo LatticePath.isPathFromTo
      rw [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hpath
      rw [endpoint_eq] at hpath
      have hpath_pair : a.1 + ↑(path.count LatticeStep.east) = b.1 ∧
                        a.2 + ↑(path.count LatticeStep.north) = b.2 := by
        rw [Prod.ext_iff] at hpath
        exact hpath
      obtain ⟨hpath1, hpath2⟩ := hpath_pair
      by_cases hx : a.1 ≤ b.1
      · have h2 : b.2 < a.2 := h hx
        have : (path.count LatticeStep.north : ℤ) = b.2 - a.2 := by omega
        have hpos : (0 : ℤ) ≤ path.count LatticeStep.north := by positivity
        omega
      · have : (path.count LatticeStep.east : ℤ) = b.1 - a.1 := by omega
        have hpos : (0 : ℤ) ≤ path.count LatticeStep.east := by positivity
        omega
    rw [hempty]
    exact Set.finite_empty

/-- The number of paths from (a,b) to (c,d).
    This equals C(c+d-a-b, c-a) when c ≥ a and d ≥ b, and 0 otherwise.
    (Proposition prop.lgv.1-paths.ct)
    Label: prop.lgv.1-paths.ct -/
def numPaths (a b : LatticePoint) : ℕ :=
  if a.1 ≤ b.1 ∧ a.2 ≤ b.2 then
    ((b.1 - a.1) + (b.2 - a.2)).toNat.choose (b.1 - a.1).toNat
  else 0

/-- Helper: endpoint formula for lattice paths. -/
private lemma endpoint_formula (path : LatticePath) (start : LatticePoint) :
    path.endpoint start = (start.1 + path.eastStepCount, start.2 + path.northStepCount) := by
  unfold LatticePath.endpoint LatticePath.eastStepCount LatticePath.northStepCount
  induction path generalizing start with
  | nil => simp [List.count]
  | cons step rest ih =>
    simp only [List.foldl_cons]
    cases step with
    | east =>
      simp only [LatticeStep.apply, List.count_cons_self,
                 List.count_cons_of_ne (by decide : LatticeStep.east ≠ LatticeStep.north)]
      have h := ih (start.1 + 1, start.2)
      convert h using 1; simp only [Prod.mk.injEq, Nat.cast_add, Nat.cast_one]; try ring_nf
      exact ⟨trivial, trivial⟩
    | north =>
      simp only [LatticeStep.apply,
                 List.count_cons_of_ne (by decide : LatticeStep.north ≠ LatticeStep.east),
                 List.count_cons_self]
      have h := ih (start.1, start.2 + 1)
      convert h using 1; simp only [Prod.mk.injEq, Nat.cast_add, Nat.cast_one]; try ring_nf
      exact ⟨trivial, trivial⟩

/-- Helper: characterization of isPathFromTo in terms of step counts. -/
private lemma isPathFromTo_iff' (path : LatticePath) (a b : LatticePoint) :
    path.isPathFromTo a b ↔
      (path.eastStepCount : ℤ) = b.1 - a.1 ∧ (path.northStepCount : ℤ) = b.2 - a.2 := by
  unfold LatticePath.isPathFromTo
  rw [endpoint_formula]
  constructor
  · intro h
    have heq : (a.1 + path.eastStepCount, a.2 + path.northStepCount) = b := h
    constructor
    · have := congrArg Prod.fst heq; simp at this; linarith
    · have := congrArg Prod.snd heq; simp at this; linarith
  · intro ⟨h1, h2⟩
    ext <;> simp <;> linarith

/-- Helper: paths from a to b require a.1 ≤ b.1 and a.2 ≤ b.2. -/
private lemma isPathFromTo_le' (path : LatticePath) (a b : LatticePoint)
    (h : path.isPathFromTo a b) : a.1 ≤ b.1 ∧ a.2 ≤ b.2 := by
  rw [isPathFromTo_iff'] at h
  constructor <;> omega

/-- Helper: pathsFromTo is empty when not a ≤ b componentwise. -/
private lemma pathsFromTo_empty' (a b : LatticePoint) (h : ¬(a.1 ≤ b.1 ∧ a.2 ≤ b.2)) :
    pathsFromTo a b = ∅ := by
  ext path
  simp only [Set.mem_setOf_eq, pathsFromTo, Set.mem_empty_iff_false, iff_false]
  intro hp
  exact h (isPathFromTo_le' path a b hp)

/-!
### Bijection between paths and subsets

The key to proving the counting formula is establishing a bijection between:
- Lattice paths from (0,0) to (m,n) with m east steps and n north steps
- Subsets S ⊆ {0, 1, ..., m+n-1} of cardinality m

The bijection: A path corresponds to choosing which m positions (out of m+n total steps)
are east steps. The subset S records exactly those positions.
-/

/-- Given a subset S ⊆ Fin(m+n), construct the path where east steps are at positions in S. -/
private def pathFromSubset (m n : ℕ) (S : Finset (Fin (m + n))) : LatticePath :=
  (List.finRange (m + n)).map (fun i => if i ∈ S then LatticeStep.east else LatticeStep.north)

/-- pathFromSubset is injective. -/
private lemma pathFromSubset_injective (m n : ℕ) : Function.Injective (pathFromSubset m n) := by
  intro S T hST
  ext i
  -- The i-th element of the path tells us whether i ∈ S
  have h : (pathFromSubset m n S)[i.val]'(by simp [pathFromSubset]) =
           (pathFromSubset m n T)[i.val]'(by simp [pathFromSubset]) := by
    simp only [hST]
  unfold pathFromSubset at h
  simp only [List.getElem_map, List.getElem_finRange] at h
  -- The Fin.cast ... is just i with a different proof
  have hcast : Fin.cast List.length_finRange ⟨↑i, by simp⟩ = i := by
    simp only [Fin.ext_iff, Fin.val_cast]
  simp only [hcast] at h
  -- Now h : (if i ∈ S then east else north) = (if i ∈ T then east else north)
  by_cases hi : i ∈ S <;> by_cases hi' : i ∈ T
  · exact ⟨fun _ => hi', fun _ => hi⟩
  · -- hi : i ∈ S, hi' : i ∉ T, so LHS = east, RHS = north
    rw [if_pos hi, if_neg hi'] at h
    exact absurd h (by decide)
  · -- hi : i ∉ S, hi' : i ∈ T, so LHS = north, RHS = east
    rw [if_neg hi, if_pos hi'] at h
    exact absurd h (by decide)
  · exact ⟨fun hf => (hi hf).elim, fun hf => (hi' hf).elim⟩

/-- The cardinality of subsets of Fin(m+n) of size m equals C(m+n, m). -/
private lemma card_subsets_of_card_m (m n : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin (m + n)) => S.card = m)).card = (m + n).choose m := by
  have h := Finset.card_powersetCard m (Finset.univ : Finset (Fin (m + n)))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
             Finset.subset_univ]

/-- The set of paths with exactly m east steps (as a Finset). -/
private def pathsWithMEastSteps (m n : ℕ) : Finset LatticePath :=
  (Finset.univ.filter (fun S : Finset (Fin (m + n)) => S.card = m)).image (pathFromSubset m n)

/-- The cardinality of paths with m east steps equals C(m+n, m). -/
private theorem card_pathsWithMEastSteps (m n : ℕ) :
    (pathsWithMEastSteps m n).card = (m + n).choose m := by
  unfold pathsWithMEastSteps
  rw [Finset.card_image_of_injective _ (pathFromSubset_injective m n)]
  exact card_subsets_of_card_m m n

/-- Helper: the path from a subset has the correct length. -/
private lemma pathFromSubset_length (m n : ℕ) (S : Finset (Fin (m + n))) :
    (pathFromSubset m n S).length = m + n := by
  simp [pathFromSubset]

/-- Helper: the path from a subset of size m has exactly m east steps. -/
private lemma pathFromSubset_eastCount (m n : ℕ) (S : Finset (Fin (m + n))) (hS : S.card = m) :
    (pathFromSubset m n S).count LatticeStep.east = m := by
  unfold pathFromSubset
  rw [List.count_eq_length_filter]
  simp only [List.filter_map, List.length_map]
  have key : (List.finRange (m + n)).filter (fun i =>
      ((fun x => x == LatticeStep.east) ∘ (fun i => if i ∈ S then LatticeStep.east else LatticeStep.north)) i) =
           (List.finRange (m + n)).filter (fun i => i ∈ S) := by
    congr 1
    ext i
    simp only [Function.comp_apply]
    split_ifs with hi
    · simp only [beq_self_eq_true, hi]; rfl
    · simp only [hi]; rfl
  rw [key]
  have h2 : ((List.finRange (m + n)).filter (fun i => i ∈ S)).length = S.card := by
    rw [← List.countP_eq_length_filter]
    have h3 : List.countP (fun i => i ∈ S) (List.finRange (m + n)) = S.card := by
      have hnodup : (List.finRange (m + n)).Nodup := List.nodup_finRange (m + n)
      rw [List.countP_eq_length_filter]
      have hfilter_eq : ((List.finRange (m + n)).filter (fun i => i ∈ S)).toFinset = S := by
        ext x
        simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
      have hnodup_filter : ((List.finRange (m + n)).filter (fun i => i ∈ S)).Nodup :=
        List.Nodup.filter _ hnodup
      rw [← List.toFinset_card_of_nodup hnodup_filter, hfilter_eq]
    exact h3
  rw [h2, hS]

/-- Helper: the path from a subset is a valid path from (0,0) to (m,n). -/
private lemma pathFromSubset_isPath (m n : ℕ) (S : Finset (Fin (m + n))) (hS : S.card = m) :
    (pathFromSubset m n S).isPathFromTo (0, 0) ((m : ℤ), (n : ℤ)) := by
  rw [isPathFromTo_iff']
  constructor
  · simp only [LatticePath.eastStepCount, pathFromSubset_eastCount m n S hS, sub_zero]
  · have hlen := pathFromSubset_length m n S
    have heast := pathFromSubset_eastCount m n S hS
    have hsum := length_eq_count_sum (pathFromSubset m n S)
    simp only [LatticePath.northStepCount, sub_zero]
    omega

/-- Given a path, extract the subset of positions where east steps occur. -/
private def subsetFromPath (m n : ℕ) (path : LatticePath) (hlen : path.length = m + n) :
    Finset (Fin (m + n)) :=
  Finset.univ.filter (fun i => path[i.val]'(by omega) = LatticeStep.east)

/-- Helper: filter card equals count for lattice paths. -/
private lemma filter_card_eq_count (path : LatticePath) :
    (Finset.univ.filter (fun i : Fin path.length => path[i.val] = LatticeStep.east)).card =
    path.count LatticeStep.east := by
  induction path with
  | nil => simp
  | cons s rest ih =>
    simp only [List.length_cons]
    have h : (Finset.univ.filter (fun i : Fin (rest.length + 1) =>
             (s :: rest)[i.val] = LatticeStep.east)) =
             (if s = LatticeStep.east then {0} else ∅) ∪
             ((Finset.univ.filter (fun i : Fin rest.length => rest[i.val] = LatticeStep.east)).map
               (Fin.succEmb rest.length)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
                 Finset.mem_map, Fin.coe_succEmb]
      constructor
      · intro hi
        rcases i with ⟨i, hi'⟩
        cases i with
        | zero =>
          left
          simp only [List.getElem_cons_zero] at hi
          by_cases hs : s = LatticeStep.east
          · simp only [hs, ↓reduceIte, Finset.mem_singleton]; rfl
          · exact absurd hi hs
        | succ j =>
          right
          use ⟨j, by omega⟩
          simp only [List.getElem_cons_succ] at hi
          exact ⟨hi, rfl⟩
      · intro hi
        rcases hi with hi | ⟨j, hj, rfl⟩
        · by_cases hs : s = LatticeStep.east
          · simp only [hs, ↓reduceIte, Finset.mem_singleton] at hi
            simp [hi, hs]
          · simp only [hs, ↓reduceIte] at hi
            simp at hi
        · simp only [Fin.val_succ, List.getElem_cons_succ]
          exact hj
    rw [h]
    cases s with
    | east =>
      simp only [↓reduceIte, List.count_cons_self]
      rw [Finset.card_union_of_disjoint]
      · simp only [Finset.card_singleton, Finset.card_map, ih]
        ring
      · simp only [Finset.disjoint_singleton_left, Finset.mem_map, Fin.coe_succEmb, not_exists,
                   not_and]
        intro j _ hj
        exact Fin.succ_ne_zero j hj
    | north =>
      have hne : LatticeStep.north ≠ LatticeStep.east := by decide
      simp only [hne, ↓reduceIte, List.count_cons_of_ne hne, Finset.empty_union, Finset.card_map, ih]

/-- subsetFromPath has cardinality equal to the east step count. -/
private lemma subsetFromPath_card (m n : ℕ) (path : LatticePath) (hlen : path.length = m + n) :
    (subsetFromPath m n path hlen).card = path.count LatticeStep.east := by
  unfold subsetFromPath
  have hbij : (Finset.univ.filter (fun i : Fin (m + n) => path[i.val]'(by omega) = LatticeStep.east)).card =
              (Finset.univ.filter (fun i : Fin path.length => path[i.val] = LatticeStep.east)).card := by
    apply Finset.card_bij (fun i _ => ⟨i.val, by omega⟩)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have : path[i.val]'(by omega) = LatticeStep.east := hi
      convert this using 2
    · intro i j _ _ hij
      simp only [Fin.mk.injEq] at hij
      exact Fin.ext hij
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine ⟨⟨i.val, by omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have : path[i.val] = LatticeStep.east := hi
        convert this using 2
      · rfl
  rw [hbij, filter_card_eq_count]

/-- pathFromSubset ∘ subsetFromPath = id on valid paths. -/
private lemma pathFromSubset_subsetFromPath (m n : ℕ) (path : LatticePath) (hlen : path.length = m + n) :
    pathFromSubset m n (subsetFromPath m n path hlen) = path := by
  unfold pathFromSubset subsetFromPath
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, hlen]
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_finRange, Finset.mem_filter, Finset.mem_univ, true_and]
    have hi_fin : i < m + n := by simp only [List.length_map, List.length_finRange] at hi; exact hi
    have hi'' : i < path.length := by omega
    simp only [Fin.val_cast]
    by_cases hpath_i : path[i]'hi'' = LatticeStep.east
    · simp only [hpath_i, ↓reduceIte]
    · simp only [hpath_i, ↓reduceIte]
      cases h : path[i]'hi'' with
      | east => exact absurd h hpath_i
      | north => rfl

/-- pathsWithMEastSteps m n equals the toFinset of pathsFromTo (0,0) (m,n). -/
private lemma pathsWithMEastSteps_eq_toFinset (m n : ℕ)
    (hfin : (pathsFromTo (0, 0) ((m : ℤ), (n : ℤ))).Finite) :
    pathsWithMEastSteps m n = hfin.toFinset := by
  ext path
  constructor
  · intro hp
    simp only [Set.Finite.mem_toFinset]
    simp only [pathsWithMEastSteps, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
               true_and] at hp
    obtain ⟨S, hS, rfl⟩ := hp
    exact pathFromSubset_isPath m n S hS
  · intro hp
    simp only [Set.Finite.mem_toFinset, pathsFromTo, Set.mem_setOf_eq] at hp
    simp only [pathsWithMEastSteps, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [isPathFromTo_iff'] at hp
    obtain ⟨heast, hnorth⟩ := hp
    simp only [sub_zero] at heast hnorth
    have hlen : path.length = m + n := by
      have := length_eq_count_sum path
      have he : path.eastStepCount = m := by simp only [LatticePath.eastStepCount] at heast ⊢; omega
      have hn : path.northStepCount = n := by simp only [LatticePath.northStepCount] at hnorth ⊢; omega
      simp only [LatticePath.eastStepCount, LatticePath.northStepCount] at he hn
      omega
    use subsetFromPath m n path hlen
    constructor
    · rw [subsetFromPath_card]
      simp only [LatticePath.eastStepCount] at heast
      omega
    · exact pathFromSubset_subsetFromPath m n path hlen

/-- The number of paths formula is correct.
    Label: prop.lgv.1-paths.ct

    The proof uses a bijection between lattice paths from a to b and subsets of
    {0, ..., m+n-1} of size m, where m = (b.1 - a.1).toNat and n = (b.2 - a.2).toNat.
    A path corresponds to choosing which m positions (out of m+n total steps) are east steps.
    The number of such choices is C(m+n, m). -/
theorem numPaths_eq_card (a b : LatticePoint)
    (hfin : (pathsFromTo a b).Finite) :
    numPaths a b = hfin.toFinset.card := by
  unfold numPaths
  by_cases hle : a.1 ≤ b.1 ∧ a.2 ≤ b.2
  · simp only [hle, and_self, ↓reduceIte]
    let m := (b.1 - a.1).toNat
    let n := (b.2 - a.2).toNat
    -- Key insight: pathsFromTo a b = pathsFromTo (0,0) (m,n) (same set of paths)
    have hpaths_eq : pathsFromTo a b = pathsFromTo (0, 0) ((m : ℤ), (n : ℤ)) := by
      ext path
      simp only [pathsFromTo, Set.mem_setOf_eq]
      rw [isPathFromTo_iff', isPathFromTo_iff']
      simp only [sub_zero]
      constructor
      · intro ⟨he, hn⟩
        have h1 : 0 ≤ b.1 - a.1 := by omega
        have h2 : 0 ≤ b.2 - a.2 := by omega
        simp only [m, n, Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
        exact ⟨he, hn⟩
      · intro ⟨he, hn⟩
        have h1 : 0 ≤ b.1 - a.1 := by omega
        have h2 : 0 ≤ b.2 - a.2 := by omega
        simp only [m, Int.toNat_of_nonneg h1] at he
        simp only [n, Int.toNat_of_nonneg h2] at hn
        exact ⟨he, hn⟩
    have hfin' : (pathsFromTo (0, 0) ((m : ℤ), (n : ℤ))).Finite := by rw [← hpaths_eq]; exact hfin
    have hcard_eq : hfin.toFinset.card = hfin'.toFinset.card := by
      congr 1; ext path; simp only [Set.Finite.mem_toFinset]; rw [hpaths_eq]
    rw [hcard_eq, ← pathsWithMEastSteps_eq_toFinset m n hfin', card_pathsWithMEastSteps]
    have h1 : 0 ≤ b.1 - a.1 := by omega
    have h2 : 0 ≤ b.2 - a.2 := by omega
    simp only [m, n]
    congr 1
    rw [← Int.toNat_add h1 h2]
  · simp only [hle, ↓reduceIte]
    have hempty := pathsFromTo_empty' a b hle
    simp only [hempty, Set.Finite.toFinset_empty, Finset.card_empty]

/-- No paths exist when c+d < a+b. -/
theorem no_paths_when_sum_decreases (a b : LatticePoint)
    (h : b.coordSum < a.coordSum) : pathsFromTo a b = ∅ := by
  ext path
  simp only [pathsFromTo, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hp
  have hsum := LatticePath.coordSum_endpoint path a
  unfold LatticePath.isPathFromTo at hp
  rw [hp] at hsum
  omega

/-!
## Path Tuples, Nipats, and Ipats (Definition def.lgv.path-tups)

A k-vertex is a k-tuple of lattice points.
A path tuple from k-vertex A to k-vertex B is a k-tuple of paths where
the i-th path goes from A_i to B_i.

A path tuple is non-intersecting (nipat) if no two paths share a vertex.
A path tuple is intersecting (ipat) if some two paths share a vertex.
-/

/-- A k-vertex is a k-tuple of lattice points.
    Label: def.lgv.path-tups (a) -/
abbrev kVertex (k : ℕ) := Fin k → LatticePoint

/-- Permute a k-vertex by a permutation σ.
    Label: def.lgv.path-tups (b) -/
def kVertex.permute {k : ℕ} (v : kVertex k) (σ : Equiv.Perm (Fin k)) : kVertex k :=
  fun i => v (σ i)

/-- A path tuple from k-vertex A to k-vertex B.
    Label: def.lgv.path-tups (c) -/
structure PathTuple (k : ℕ) (A B : kVertex k) where
  /-- The i-th path in the tuple -/
  paths : Fin k → LatticePath
  /-- Each path goes from A_i to B_i -/
  valid : ∀ i, (paths i).isPathFromTo (A i) (B i)

/-- The set of vertices visited by a path in a path tuple. -/
def PathTuple.verticesOf {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B)
    (i : Fin k) : Set LatticePoint :=
  { p | p ∈ (pt.paths i).vertices (A i) }

/-- A path tuple is non-intersecting (nipat) if no two distinct paths share a vertex.
    Label: def.lgv.path-tups (d) -/
def PathTuple.isNonIntersecting {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) : Prop :=
  ∀ i j, i ≠ j → Disjoint (pt.verticesOf i) (pt.verticesOf j)

/-- A path tuple is intersecting (ipat) if it is not non-intersecting.
    Label: def.lgv.path-tups (e) -/
def PathTuple.isIntersecting {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) : Prop :=
  ¬pt.isNonIntersecting

/-- The set of all path tuples from A to B. -/
def pathTuplesFromTo {k : ℕ} (A B : kVertex k) : Set (PathTuple k A B) :=
  Set.univ

/-- The set of all non-intersecting path tuples (nipats) from A to B. -/
def nipatsFromTo {k : ℕ} (A B : kVertex k) : Set (PathTuple k A B) :=
  { pt | pt.isNonIntersecting }

/-- The set of all intersecting path tuples (ipats) from A to B. -/
def ipatsFromTo {k : ℕ} (A B : kVertex k) : Set (PathTuple k A B) :=
  { pt | pt.isIntersecting }

/-- The set of path tuples from A to B is finite (follows from finiteness of paths). -/
theorem pathTuplesFromTo_finite {k : ℕ} (A B : kVertex k) :
    (pathTuplesFromTo A B).Finite := by
  have h_paths_finite : {f : Fin k → LatticePath | ∀ i, f i ∈ pathsFromTo (A i) (B i)}.Finite :=
    Set.Finite.pi' fun i => pathsFromTo_finite (A i) (B i)
  have h_inj : Function.Injective (fun (pt : PathTuple k A B) => pt.paths) := fun pt1 pt2 h => by
    cases pt1; cases pt2; simp only at h; subst h; rfl
  have h_eq : pathTuplesFromTo A B =
      (fun (pt : PathTuple k A B) => pt.paths) ⁻¹' {f | ∀ i, f i ∈ pathsFromTo (A i) (B i)} := by
    ext pt
    simp only [pathTuplesFromTo, Set.mem_univ, Set.mem_preimage, Set.mem_setOf_eq, true_iff]
    exact pt.valid
  rw [h_eq]
  exact h_paths_finite.preimage h_inj.injOn

/-- The set of nipats from A to B is finite (subset of finite set). -/
theorem nipatsFromTo_finite {k : ℕ} (A B : kVertex k) :
    (nipatsFromTo A B).Finite := by
  exact (pathTuplesFromTo_finite A B).subset (Set.subset_univ _)

/-- The set of ipats from A to B is finite (subset of finite set). -/
theorem ipatsFromTo_finite {k : ℕ} (A B : kVertex k) :
    (ipatsFromTo A B).Finite := by
  exact (pathTuplesFromTo_finite A B).subset (Set.subset_univ _)

/-!
## General k Involution Infrastructure

The sign-reversing involution for general k path tuples works as follows:
Given an intersecting path tuple (ipat), we:
1. Find the smallest path index i that contains a "crowded" vertex (shared with another path)
2. Find the first crowded vertex v on path i (by position in the path)
3. Find the largest path index j that contains v (j > i since v is crowded)
4. Exchange the tails of paths i and j at v
5. Compose σ with the transposition (i j) to flip the sign

This maps (σ, ipat) to (σ * swap(i,j), ipat') where:
- sign(σ * swap(i,j)) = -sign(σ) (transposition flips sign)
- ipat' is still intersecting (v is still a crowded point)
- The involution is its own inverse (applying twice returns the original)

Since every ipat has at least one crowded point, the involution has no fixed points.
-/

/-- A vertex is crowded in a path tuple if it appears in at least two paths -/
def PathTuple.isCrowded {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) (v : LatticePoint) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧ v ∈ pt.verticesOf i ∧ v ∈ pt.verticesOf j

/-- An intersecting path tuple has at least one crowded vertex -/
theorem PathTuple.isIntersecting_iff_exists_crowded {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) :
    pt.isIntersecting ↔ ∃ v, pt.isCrowded v := by
  unfold isIntersecting isNonIntersecting isCrowded
  push_neg
  constructor
  · intro ⟨i, j, hij, hnotdisj⟩
    rw [Set.not_disjoint_iff] at hnotdisj
    obtain ⟨v, hvi, hvj⟩ := hnotdisj
    exact ⟨v, i, j, hij, hvi, hvj⟩
  · intro ⟨v, i, j, hij, hvi, hvj⟩
    use i, j, hij
    rw [Set.not_disjoint_iff]
    exact ⟨v, hvi, hvj⟩

/-- The set of path indices that have a crowded vertex (shared with another path) -/
noncomputable def PathTuple.crowdedPathIndices {k : ℕ} {A B : kVertex k} (pt : PathTuple k A B) : Finset (Fin k) :=
  @Finset.filter _ (fun i => ∃ j : Fin k, i ≠ j ∧ ¬Disjoint (pt.verticesOf i) (pt.verticesOf j)) 
    (Classical.decPred _) Finset.univ

/-- An intersecting path tuple has nonempty crowdedPathIndices -/
theorem PathTuple.isIntersecting_iff_crowdedPathIndices_nonempty {k : ℕ} {A B : kVertex k}
    (pt : PathTuple k A B) :
    pt.isIntersecting ↔ pt.crowdedPathIndices.Nonempty := by
  rw [isIntersecting_iff_exists_crowded]
  constructor
  · intro ⟨v, i, j, hij, hvi, hvj⟩
    use i
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨j, hij, by rw [Set.not_disjoint_iff]; exact ⟨v, hvi, hvj⟩⟩
  · intro ⟨i, hi⟩
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨j, hij, hnotdisj⟩ := hi
    rw [Set.not_disjoint_iff] at hnotdisj
    obtain ⟨v, hvi, hvj⟩ := hnotdisj
    exact ⟨v, i, j, hij, hvi, hvj⟩

/-- The minimum crowded path index for an intersecting path tuple.
    This is the smallest index i such that path i shares a vertex with some other path.
    
    This is a key component of the sign-reversing involution for general k:
    the involution swaps tails at the first crowded vertex on this path. -/
noncomputable def PathTuple.minCrowdedPathIndex {k : ℕ} {A B : kVertex k} 
    (pt : PathTuple k A B) (hip : pt.isIntersecting) : Fin k :=
  (pt.crowdedPathIndices.min' (pt.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip))

/-- The min crowded path index is in crowdedPathIndices -/
lemma PathTuple.minCrowdedPathIndex_mem {k : ℕ} {A B : kVertex k}
    (pt : PathTuple k A B) (hip : pt.isIntersecting) :
    pt.minCrowdedPathIndex hip ∈ pt.crowdedPathIndices :=
  Finset.min'_mem _ _

/-- The min crowded path index is minimal -/
lemma PathTuple.minCrowdedPathIndex_le {k : ℕ} {A B : kVertex k}
    (pt : PathTuple k A B) (hip : pt.isIntersecting) (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    pt.minCrowdedPathIndex hip ≤ i :=
  Finset.min'_le _ _ hi

/-- The crowded vertices on a specific path: vertices that appear in multiple paths -/
def PathTuple.crowdedVerticesOnPath {k : ℕ} {A B : kVertex k} 
    (pt : PathTuple k A B) (i : Fin k) : Set LatticePoint :=
  { v | v ∈ pt.verticesOf i ∧ ∃ j : Fin k, i ≠ j ∧ v ∈ pt.verticesOf j }

/-- The crowded vertices on the min crowded path are nonempty -/
lemma PathTuple.crowdedVerticesOnMinPath_nonempty {k : ℕ} {A B : kVertex k}
    (pt : PathTuple k A B) (hip : pt.isIntersecting) :
    (pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip)).Nonempty := by
  have hi_mem := pt.minCrowdedPathIndex_mem hip
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi_mem
  obtain ⟨j, hij, hnotdisj⟩ := hi_mem
  rw [Set.not_disjoint_iff] at hnotdisj
  obtain ⟨v, hvi, hvj⟩ := hnotdisj
  use v
  simp only [crowdedVerticesOnPath, Set.mem_setOf_eq]
  exact ⟨hvi, j, hij, hvj⟩

/-- The vertices on a path form a finite set -/
lemma PathTuple.verticesOf_finite {k : ℕ} {A B : kVertex k} 
    (pt : PathTuple k A B) (i : Fin k) : (pt.verticesOf i).Finite := by
  simp only [verticesOf]
  exact List.finite_toSet _

/-- A path tuple with permutation: pairs (σ, pt) where pt is a path tuple from A to σ(B) -/
def pathTupleWithPerm {k : ℕ} (A B : kVertex k) : Type :=
  (σ : Equiv.Perm (Fin k)) × PathTuple k A (B.permute σ)

/-- The sign of a path tuple with permutation -/
def signOfPathTupleWithPerm {k : ℕ} {A B : kVertex k} (sp : pathTupleWithPerm A B) : ℤ :=
  Equiv.Perm.sign sp.1

/-- The set of all ipats with permutation -/
def ipatWithPerm {k : ℕ} (A B : kVertex k) : Set (pathTupleWithPerm A B) :=
  { sp | sp.2.isIntersecting }

/-- The set of ipats with permutation is finite -/
theorem ipatWithPerm_finite {k : ℕ} (A B : kVertex k) :
    (ipatWithPerm A B).Finite := by
  -- The set of all (σ, pt) pairs is finite (finite permutations × finite path tuples)
  have h_all : (Set.univ : Set (pathTupleWithPerm A B)).Finite := by
    -- Use the fact that Sigma of finite types is finite
    have hfin : ∀ σ : Equiv.Perm (Fin k), Finite (PathTuple k A (B.permute σ)) := by
      intro σ
      have hfin_set := pathTuplesFromTo_finite A (B.permute σ)
      -- pathTuplesFromTo is Set.univ, so the set is the whole type
      have heq : pathTuplesFromTo A (B.permute σ) = Set.univ := rfl
      rw [heq] at hfin_set
      exact Set.finite_univ_iff.mp hfin_set
    have : Finite (pathTupleWithPerm A B) := by
      unfold pathTupleWithPerm
      exact inferInstance
    exact Set.finite_univ
  exact h_all.subset (Set.subset_univ _)

/-!
## The LGV Lemma for Two Paths (Proposition prop.lgv.2paths.count)

For two 2-vertices (A, A') and (B, B'):

det | #paths(A→B)   #paths(A→B')  |
    | #paths(A'→B)  #paths(A'→B') |

= #nipats from (A,A') to (B,B') - #nipats from (A,A') to (B',B)

The proof uses a sign-reversing involution on intersecting path tuples
that exchanges the tails of two intersecting paths.
-/

/-- The path count matrix for two source and target points. -/
def pathMatrix2 (A A' B B' : LatticePoint) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![numPaths A B, numPaths A B';
     numPaths A' B, numPaths A' B']

/-- Number of nipats from (A,A') to (B,B').
    Defined as the cardinality of the set of non-intersecting path tuples. -/
noncomputable def numNipats2 (A A' B B' : LatticePoint) : ℕ :=
  let AB : kVertex 2 := ![A, A']
  let BB : kVertex 2 := ![B, B']
  (nipatsFromTo AB BB).ncard

/-- Helper: the 2x2 determinant expands to the difference of products. -/
theorem pathMatrix2_det (A A' B B' : LatticePoint) :
    (pathMatrix2 A A' B B').det =
      (numPaths A B : ℤ) * numPaths A' B' - (numPaths A B' : ℤ) * numPaths A' B := by
  simp only [pathMatrix2, det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- A path tuple from (A,A') to (B,B') or (B',B) with a sign.
    Sign is +1 for (B,B') and -1 for (B',B). -/
structure SignedPathTuple2 (A A' B B' : LatticePoint) where
  /-- The first path -/
  path0 : LatticePath
  /-- The second path -/
  path1 : LatticePath
  /-- Whether this is to (B,B') (true) or (B',B) (false) -/
  toBB' : Bool
  /-- Path 0 goes from A to its destination -/
  valid0 : path0.isPathFromTo A (if toBB' then B else B')
  /-- Path 1 goes from A' to its destination -/
  valid1 : path1.isPathFromTo A' (if toBB' then B' else B)

/-- The sign of a signed path tuple. -/
def SignedPathTuple2.sign {A A' B B' : LatticePoint} (spt : SignedPathTuple2 A A' B B') : ℤ :=
  if spt.toBB' then 1 else -1

/-- Check if a signed path tuple is intersecting (the two paths share a vertex). -/
def SignedPathTuple2.isIntersecting {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') : Prop :=
  ∃ v, v ∈ spt.path0.vertices A ∧ v ∈ spt.path1.vertices A'

/-- The set of all signed path tuples from (A,A') to (B,B') or (B',B). -/
def signedPathTuples2 (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  Set.univ

/-- The set of intersecting signed path tuples. -/
def signedIpats2 (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  { spt | spt.isIntersecting }

/-- The set of non-intersecting signed path tuples. -/
def signedNipats2 (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  { spt | ¬spt.isIntersecting }

/-! ### Deterministic intersection point selection

The key to proving that the sign-reversing involution is involutive is to use a
deterministic choice of intersection point. We define `firstIntersection` to be
the first intersection point in path0's vertex list (by index). This ensures that
after swapping tails, the same point is still the first intersection.
-/

/-- The index of the first intersection point in path0's vertices.
    This is the smallest index i such that (path0.vertices A)[i] ∈ path1.vertices A'. -/
noncomputable def firstIntersectionIdx {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (_h : spt.isIntersecting) : ℕ :=
  let verts0 := spt.path0.vertices A
  let verts1 := spt.path1.vertices A'
  verts0.findIdx (fun v => decide (v ∈ verts1))

/-- The index of the first intersection point is valid (less than the length of path0's vertices). -/
lemma firstIntersectionIdx_lt {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    firstIntersectionIdx spt h < (spt.path0.vertices A).length := by
  obtain ⟨v, hv0, hv1⟩ := h
  apply List.findIdx_lt_length_of_exists
  use v, hv0
  simp [hv1]

/-- The first intersection point of two intersecting paths.
    This is the first vertex (by index in path0) that is shared by both paths. -/
noncomputable def firstIntersection {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) : LatticePoint :=
  let idx := firstIntersectionIdx spt h
  let verts0 := spt.path0.vertices A
  verts0[idx]'(firstIntersectionIdx_lt spt h)

/-- The first intersection point is in path0's vertices. -/
lemma firstIntersection_mem_path0 {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    firstIntersection spt h ∈ spt.path0.vertices A := by
  unfold firstIntersection
  apply List.getElem_mem

/-- The first intersection point is in path1's vertices. -/
lemma firstIntersection_mem_path1 {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    firstIntersection spt h ∈ spt.path1.vertices A' := by
  unfold firstIntersection firstIntersectionIdx
  simp only
  have hidx := firstIntersectionIdx_lt spt h
  have hfound := @List.findIdx_getElem _ (fun v => decide (v ∈ spt.path1.vertices A'))
                  (spt.path0.vertices A) hidx
  simp at hfound
  convert hfound

/-- Helper: findIdx returns the smallest index satisfying the predicate -/
private lemma findIdx_le_of_getElem {α : Type*} (l : List α) (p : α → Bool) (i : ℕ)
    (hi : i < l.length) (hp : p l[i] = true) : l.findIdx p ≤ i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [List.findIdx_cons]
    cases hp' : p x with
    | true => simp
    | false =>
      simp only [cond_false]
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero] at hp
        rw [hp] at hp'
        simp at hp'
      | succ j =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
        simp only [List.getElem_cons_succ] at hp
        have := ih j hi hp
        omega

/-- The first intersection point is the first vertex (by index in path0) shared by both paths.
    This is a key property for proving the involution is involutive: after swapping tails,
    the same point v is still the first intersection because:
    1. The head of path0 (indices 0..idx) is unchanged
    2. v is at index idx in both the original and swapped paths
    3. No earlier vertex in path0's head is in path1's vertices (by minimality of findIdx) -/
lemma firstIntersection_is_first {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    let v := firstIntersection spt h
    let idx := firstIntersectionIdx spt h
    -- v is at index idx in path0's vertices
    (spt.path0.vertices A)[idx]'(firstIntersectionIdx_lt spt h) = v ∧
    -- No earlier index has a shared vertex
    ∀ i (hi : i < idx), ¬((spt.path0.vertices A)[i]'(Nat.lt_trans hi (firstIntersectionIdx_lt spt h)) ∈ spt.path1.vertices A') := by
  constructor
  · -- v is at index idx
    rfl
  · -- No earlier index has a shared vertex
    intro i hi
    have hidx := firstIntersectionIdx_lt spt h
    have hlt : i < (spt.path0.vertices A).length := Nat.lt_trans hi hidx
    -- By definition of findIdx, indices before idx don't satisfy the predicate
    have hnotfound : ¬(decide ((spt.path0.vertices A)[i] ∈ spt.path1.vertices A') = true) := by
      intro hcontra
      simp at hcontra
      -- If (path0.vertices A)[i] ∈ path1.vertices A', then findIdx would return ≤ i
      have hfind := findIdx_le_of_getElem (spt.path0.vertices A)
                    (fun v => decide (v ∈ spt.path1.vertices A')) i hlt
      simp only [decide_eq_true_eq] at hfind
      have hle := hfind hcontra
      -- firstIntersectionIdx is defined as findIdx
      unfold firstIntersectionIdx at hi
      simp only at hi
      exact Nat.not_lt.mpr hle hi
    simp at hnotfound
    exact hnotfound


/-- Split a path at a vertex, returning (head, tail) where head ends at v and tail starts at v. -/
noncomputable def splitPathAt (path : LatticePath) (start v : LatticePoint)
    (_hv : v ∈ path.vertices start) : LatticePath × LatticePath :=
  -- Find the index where v occurs
  let verts := path.vertices start
  let idx := verts.findIdx (· == v)
  -- Split the path at that index
  (path.take idx, path.drop idx)

/-! ### Helper lemmas for the involution proof -/

/-- vertices equals scanl result -/
private lemma vertices_eq_scanl (path : LatticePath) (start : LatticePoint) :
    path.vertices start = path.scanl (fun p s => s.apply p) start := by
  unfold LatticePath.vertices
  cases path with
  | nil => simp [List.scanl]
  | cons step rest =>
    simp only [List.scanl, List.tail_cons]

/-- Length of vertices equals path length plus one -/
private lemma vertices_length (path : LatticePath) (start : LatticePoint) :
    (path.vertices start).length = path.length + 1 := by
  rw [vertices_eq_scanl]; simp [List.length_scanl]

/-- Coordinate sum at position i in scanl -/
private lemma scanl_coordSum_eq (path : LatticePath) (start : LatticePoint) (i : ℕ)
    (hi : i < (path.scanl (fun p s => s.apply p) start).length) :
    ((path.scanl (fun p s => s.apply p) start)[i]).coordSum = start.coordSum + i := by
  induction path generalizing start i with
  | nil =>
    simp only [List.scanl_nil, List.length_singleton, Nat.lt_one_iff] at hi
    subst hi; simp [List.scanl]
  | cons step rest ih =>
    simp only [List.scanl_cons, List.length_cons] at hi ⊢
    cases i with
    | zero => simp [LatticePoint.coordSum]
    | succ j =>
      simp only [List.getElem_cons_succ, Nat.cast_succ]
      have hj : j < (rest.scanl (fun p s => s.apply p) (step.apply start)).length := by
        simp only [List.length_scanl] at hi ⊢; omega
      rw [ih (step.apply start) j hj, LatticeStep.coordSum_apply]; ring

/-- Vertices at different indices are different (because coordSum strictly increases) -/
private lemma vertices_ne_of_ne_idx (path : LatticePath) (start : LatticePoint) (i j : ℕ)
    (hi : i < (path.vertices start).length) (hj : j < (path.vertices start).length)
    (hne : i ≠ j) : (path.vertices start)[i] ≠ (path.vertices start)[j] := by
  have heq := vertices_eq_scanl path start
  have hi' : i < (path.scanl (fun p s => s.apply p) start).length := by rwa [← heq]
  have hj' : j < (path.scanl (fun p s => s.apply p) start).length := by rwa [← heq]
  intro hvertex
  have hcsi := scanl_coordSum_eq path start i hi'
  have hcsj := scanl_coordSum_eq path start j hj'
  simp only [heq] at hvertex
  rw [hvertex] at hcsi; rw [hcsi] at hcsj; omega

/-- Helper for mem_drop_exists -/
private lemma mem_drop_exists {α : Type*} (l : List α) (n : ℕ) (x : α) (h : x ∈ l.drop n) :
    ∃ i, n ≤ i ∧ ∃ hi : i < l.length, l[i] = x := by
  obtain ⟨j, hj_lt, hj_eq⟩ := List.getElem_of_mem h
  simp only [List.length_drop] at hj_lt
  simp only [List.getElem_drop] at hj_eq
  exact ⟨n + j, by omega, by omega, hj_eq⟩

/-- A vertex in vertices cannot appear again after its first occurrence -/
private lemma vertices_not_mem_drop_after_findIdx (path : LatticePath) (start : LatticePoint)
    (v : LatticePoint) (hv : v ∈ path.vertices start) :
    let idx := (path.vertices start).findIdx (· == v)
    v ∉ (path.vertices start).drop (idx + 1) := by
  simp only
  intro hmem
  have hidx : (path.vertices start).findIdx (· == v) < (path.vertices start).length :=
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have hv_at_idx : (path.vertices start)[(path.vertices start).findIdx (· == v)] = v := by
    have := @List.findIdx_getElem _ (· == v) (path.vertices start) hidx
    simp at this; exact this
  obtain ⟨i, hi_ge, hi_lt, hi_eq⟩ := mem_drop_exists _ _ _ hmem
  have hne : (path.vertices start).findIdx (· == v) ≠ i := by omega
  have := vertices_ne_of_ne_idx path start _ _ hidx hi_lt hne
  rw [hv_at_idx, hi_eq] at this
  exact this rfl

/-- scanl of take equals take of scanl -/
private lemma scanl_take (path : LatticePath) (start : LatticePoint) (n : ℕ) :
    (path.take n).scanl (fun p s => s.apply p) start =
    (path.scanl (fun p s => s.apply p) start).take (n + 1) := by
  induction path generalizing start n with
  | nil => simp [List.scanl]
  | cons step rest ih =>
    cases n with
    | zero => simp [List.scanl]
    | succ m =>
      simp only [List.take_succ_cons, List.scanl_cons, List.take_succ_cons]
      congr 1
      exact ih (step.apply start) m

/-- scanl of append equals append of scanls (with tail adjustment) -/
private lemma scanl_append (path1 path2 : LatticePath) (start : LatticePoint) :
    (path1 ++ path2).scanl (fun p s => s.apply p) start =
    path1.scanl (fun p s => s.apply p) start ++
    (path2.scanl (fun p s => s.apply p) (path1.foldl (fun p s => s.apply p) start)).tail := by
  induction path1 generalizing start with
  | nil =>
    simp only [List.nil_append, List.scanl_nil, List.foldl_nil, List.nil_append, List.singleton_append]
    cases path2 with
    | nil => rfl
    | cons y ys => simp [List.scanl]
  | cons x xs ih =>
    simp only [List.cons_append, List.scanl_cons, List.foldl_cons]
    congr 1
    exact ih (x.apply start)

/-- Helper: findIdx equals n if the predicate holds at n and fails before n -/
private lemma findIdx_eq_of_getElem {α : Type*} (l : List α) (p : α → Bool) (n : ℕ) (hn : n < l.length)
    (hp : p (l[n]'hn) = true) (hmin : ∀ j (hj : j < n), p (l[j]'(Nat.lt_trans hj hn)) = false) :
    l.findIdx p = n := by
  induction l generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    simp only [List.findIdx_cons]
    cases hn' : n with
    | zero =>
      subst hn'
      simp only [List.getElem_cons_zero] at hp
      simp [hp]
    | succ m =>
      subst hn'
      have hpx : p x = false := hmin 0 (by omega)
      simp only [hpx, cond_false]
      have hm : m < xs.length := by simp at hn; omega
      have hpm : p (xs[m]'hm) = true := by simp only [List.getElem_cons_succ] at hp; exact hp
      have hmin' : ∀ j (hj : j < m), p (xs[j]'(Nat.lt_trans hj hm)) = false := by
        intro j hj
        have := hmin (j + 1) (by omega)
        simp only [List.getElem_cons_succ] at this
        exact this
      rw [ih m hm hpm hmin']

/-- The key lemma for firstIntersection_preserved: findIdx is preserved when the prefix is preserved. -/
private lemma findIdx_preserved_by_prefix (verts0 new_verts0 new_verts1 : List LatticePoint)
    (idx : ℕ) (hidx_lt : idx < verts0.length) (hidx_lt' : idx < new_verts0.length)
    (h_prefix : ∀ i (hi : i ≤ idx), new_verts0[i]'(Nat.lt_of_le_of_lt hi hidx_lt') = verts0[i]'(Nat.lt_of_le_of_lt hi hidx_lt))
    (h_in' : verts0[idx] ∈ new_verts1)
    (h_not_in' : ∀ i (hi : i < idx), ¬(verts0[i]'(Nat.lt_trans hi hidx_lt) ∈ new_verts1)) :
    new_verts0.findIdx (fun v => decide (v ∈ new_verts1)) = idx := by
  apply findIdx_eq_of_getElem _ _ _ hidx_lt'
  · have heq := h_prefix idx (le_refl idx); simp only [heq, decide_eq_true_eq]; exact h_in'
  · intro j hj; have hj_le : j ≤ idx := le_of_lt hj; have heq := h_prefix j hj_le
    simp only [heq, decide_eq_false_iff_not]; exact h_not_in' j hj

/-- vertices of append share prefix with first path -/
private lemma vertices_append_prefix (path1 path2 : LatticePath) (start : LatticePoint) (i : ℕ)
    (hi : i < (LatticePath.vertices path1 start).length) :
    (LatticePath.vertices (path1 ++ path2) start)[i]'(by
      simp only [vertices_length] at hi ⊢; simp only [List.length_append]; omega) =
    (LatticePath.vertices path1 start)[i] := by
  simp only [vertices_length] at hi
  induction path1 generalizing start i with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, Nat.lt_one_iff] at hi; subst hi
    simp only [List.nil_append, vertices_eq_scanl, List.scanl_nil, List.getElem_cons_zero]
    cases path2 with | nil => rfl | cons step rest => simp [List.scanl]
  | cons step rest ih =>
    simp only [List.cons_append, vertices_eq_scanl, List.scanl_cons]
    cases i with
    | zero => rfl
    | succ j =>
      simp only [List.getElem_cons_succ]
      have hj : j < (LatticePath.vertices rest (step.apply start)).length := by
        simp only [List.length_cons] at hi; simp only [vertices_length]; omega
      have := ih (step.apply start) j hj
      simp only [vertices_eq_scanl] at this
      apply this; simp only [vertices_length] at hj; omega

/-- vertices of (path.take n) ++ path2 share prefix with path.vertices for i ≤ n -/
private lemma vertices_take_append_prefix (path path2 : LatticePath) (start : LatticePoint) (n i : ℕ)
    (hi : i ≤ n) (hi_lt : i < (LatticePath.vertices path start).length) :
    (LatticePath.vertices (path.take n ++ path2) start)[i]'(by
      simp only [vertices_length] at hi_lt ⊢; simp only [List.length_append, List.length_take]; omega) =
    (LatticePath.vertices path start)[i] := by
  have h1 : i < (LatticePath.vertices (path.take n) start).length := by
    simp only [vertices_length, List.length_take] at hi_lt ⊢; omega
  have h2 := vertices_append_prefix (path.take n) path2 start i h1
  have hteq := scanl_take path start n
  have hi_lt_take : i < ((LatticePath.vertices path start).take (n + 1)).length := by
    simp only [List.length_take, vertices_length] at hi_lt ⊢; omega
  have h3 : (LatticePath.vertices (path.take n) start)[i]'h1 = (LatticePath.vertices path start)[i] := by
    have : (LatticePath.vertices (path.take n) start)[i]'h1 =
           ((LatticePath.vertices path start).take (n + 1))[i]'hi_lt_take := by
      simp only [vertices_eq_scanl, hteq]
    rw [this, List.getElem_take]
  have hi_lt_app : i < (LatticePath.vertices (path.take n ++ path2) start).length := by
    simp only [vertices_length] at hi_lt ⊢; simp only [List.length_append, List.length_take]; omega
  calc (LatticePath.vertices (path.take n ++ path2) start)[i]'hi_lt_app
      = (LatticePath.vertices (path.take n) start)[i]'h1 := h2
    _ = (LatticePath.vertices path start)[i] := h3


/-- Vertices at index i < idx are not in drop(idx).vertices.
    This uses the fact that coordSum strictly increases along a path. -/
private lemma vertex_not_mem_drop_vertices (path : LatticePath) (start : LatticePoint)
    (i idx : ℕ) (hi : i < idx) (hidx : idx < (LatticePath.vertices path start).length) :
    (LatticePath.vertices path start)[i]'(Nat.lt_trans hi hidx) ∉
    LatticePath.vertices (path.drop idx) ((LatticePath.vertices path start)[idx]'hidx) := by
  intro hmem
  have heq := vertices_eq_scanl path start
  have hi' : i < (path.scanl (fun p s => s.apply p) start).length := by
    rw [← heq]; exact Nat.lt_trans hi hidx
  have hidx' : idx < (path.scanl (fun p s => s.apply p) start).length := by
    rw [← heq]; exact hidx
  have hcsi := scanl_coordSum_eq path start i hi'
  have hcsidx := scanl_coordSum_eq path start idx hidx'
  simp only [heq] at hmem
  rw [vertices_eq_scanl] at hmem
  obtain ⟨j, hj_lt, hj_eq⟩ := List.getElem_of_mem hmem
  have hcsj := scanl_coordSum_eq (path.drop idx) ((path.scanl (fun p s => s.apply p) start)[idx]) j hj_lt
  rw [hcsidx] at hcsj
  have : ((path.scanl (fun p s => s.apply p) start)[i]).coordSum =
         ((path.drop idx).scanl (fun p s => s.apply p) ((path.scanl (fun p s => s.apply p) start)[idx]))[j].coordSum := by
    congr 1; exact hj_eq.symm
  rw [hcsi, hcsj] at this
  omega

/-- start is in vertices -/

private lemma mem_vertices_start (path : LatticePath) (start : LatticePoint) :
    start ∈ path.vertices start := by
  rw [vertices_eq_scanl]
  cases path with
  | nil => simp [List.scanl]
  | cons step rest => simp [List.scanl]

/-- vertices of append includes endpoint of first part -/
private lemma mem_vertices_append_of_endpoint (path1 path2 : LatticePath) (start : LatticePoint) :
    path1.endpoint start ∈ (path1 ++ path2).vertices start := by
  rw [vertices_eq_scanl]
  induction path1 generalizing start with
  | nil =>
    simp only [List.nil_append, LatticePath.endpoint, List.foldl_nil]
    rw [← vertices_eq_scanl]
    exact mem_vertices_start path2 start
  | cons step rest ih =>
    simp only [List.cons_append, List.scanl_cons, List.mem_cons]
    unfold LatticePath.endpoint
    simp only [List.foldl_cons]
    right
    exact ih (step.apply start)

/-- scanl[i] = (path.take i).endpoint start -/
private lemma scanl_getElem_eq_take_endpoint (path : LatticePath) (start : LatticePoint)
    (i : ℕ) (hi : i < (path.scanl (fun p s => s.apply p) start).length) :
    (path.scanl (fun p s => s.apply p) start)[i] = LatticePath.endpoint (path.take i) start := by
  induction path generalizing start i with
  | nil =>
    simp only [List.scanl_nil, List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    simp [List.scanl, LatticePath.endpoint]
  | cons step rest ih =>
    simp only [List.scanl_cons, List.length_cons] at hi ⊢
    cases i with
    | zero =>
      simp [LatticePath.endpoint]
    | succ j =>
      simp only [List.getElem_cons_succ, List.take_succ_cons, LatticePath.endpoint, List.foldl_cons]
      have hj : j < (rest.scanl (fun p s => s.apply p) (step.apply start)).length := by
        simp only [List.length_scanl] at hi ⊢
        omega
      exact ih (step.apply start) j hj

/-- vertices[i] = (path.take i).endpoint start -/
private lemma vertices_getElem_eq_take_endpoint (path : LatticePath) (start : LatticePoint)
    (i : ℕ) (hi : i < (path.vertices start).length) :
    (path.vertices start)[i] = LatticePath.endpoint (path.take i) start := by
  have heq : path.vertices start = path.scanl (fun p s => s.apply p) start := vertices_eq_scanl path start
  have hi' : i < (path.scanl (fun p s => s.apply p) start).length := by
    rw [← heq]
    exact hi
  simp only [heq]
  exact scanl_getElem_eq_take_endpoint path start i hi'

/-- The head of splitPathAt ends at v -/
private lemma splitPathAt_head_endpoint (path : LatticePath) (start v : LatticePoint)
    (hv : v ∈ path.vertices start) :
    let verts := path.vertices start
    let idx := verts.findIdx (· == v)
    LatticePath.endpoint (path.take idx) start = v := by
  simp only
  have hidx : (path.vertices start).findIdx (· == v) < (path.vertices start).length := by
    exact List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have hget : (path.vertices start)[(path.vertices start).findIdx (· == v)] = v := by
    have hfound := @List.findIdx_getElem _ (· == v) (path.vertices start) hidx
    simp at hfound
    exact hfound
  have h := vertices_getElem_eq_take_endpoint path start _ hidx
  rw [hget] at h
  exact h.symm

/-- findIdx (· == v) on newPath1.vertices equals idx1 after the involution.
    This is needed to show that the second involution uses the same index for path1. -/
private lemma findIdx_beq_newPath1_eq {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    let v := firstIntersection spt h
    let idx0 := firstIntersectionIdx spt h
    let idx1 := (spt.path1.vertices A').findIdx (· == v)
    let newPath1 := spt.path1.take idx1 ++ spt.path0.drop idx0
    (LatticePath.vertices newPath1 A').findIdx (· == v) = idx1 := by
  simp only
  let v := firstIntersection spt h
  let idx0 := firstIntersectionIdx spt h
  let hv1 := firstIntersection_mem_path1 spt h
  let idx1 := (spt.path1.vertices A').findIdx (· == v)
  let newPath1 := spt.path1.take idx1 ++ spt.path0.drop idx0

  -- idx1 < path1.vertices.length
  have hidx1_lt : idx1 < (spt.path1.vertices A').length :=
    List.findIdx_lt_length_of_exists ⟨v, hv1, by simp⟩

  -- idx1 ≤ path1.length (for take/drop)
  have hidx1_le_path : idx1 ≤ spt.path1.length := by
    simp only [vertices_length] at hidx1_lt; omega

  -- Length of take
  have hlen_take : (spt.path1.take idx1).length = idx1 := by
    simp [List.length_take, Nat.min_eq_left hidx1_le_path]

  -- idx1 < newPath1.vertices.length
  have hidx1_lt' : idx1 < (LatticePath.vertices newPath1 A').length := by
    have hlen : (LatticePath.vertices newPath1 A').length = newPath1.length + 1 := vertices_length newPath1 A'
    have hlen2 : newPath1.length = (spt.path1.take idx1).length + (spt.path0.drop idx0).length := by
      simp only [newPath1, List.length_append]
    rw [hlen, hlen2, hlen_take]
    omega

  -- v is at index idx1 in path1.vertices
  have hv_at_idx1 : (spt.path1.vertices A')[idx1]'hidx1_lt = v := by
    have hfound := @List.findIdx_getElem _ (· == v) (spt.path1.vertices A') hidx1_lt
    simp at hfound
    exact hfound

  -- First idx1+1 vertices of newPath1 equal those of path1
  have h_prefix : ∀ i (hi : i ≤ idx1),
      (LatticePath.vertices newPath1 A')[i]'(Nat.lt_of_le_of_lt hi hidx1_lt') =
      (spt.path1.vertices A')[i]'(Nat.lt_of_le_of_lt hi hidx1_lt) := by
    intro i hi
    have hi_lt : i < (spt.path1.vertices A').length := Nat.lt_of_le_of_lt hi hidx1_lt
    exact vertices_take_append_prefix spt.path1 (spt.path0.drop idx0) A' idx1 i hi hi_lt

  -- v is at index idx1 in newPath1.vertices
  have h_new_at_idx1 : (LatticePath.vertices newPath1 A')[idx1]'hidx1_lt' = v := by
    have := h_prefix idx1 (le_refl idx1)
    rw [this, hv_at_idx1]

  -- For j < idx1, newPath1.vertices[j] ≠ v (by uniqueness of vertices)
  have h_not_eq : ∀ j (hj : j < idx1), (LatticePath.vertices newPath1 A')[j]'(Nat.lt_trans hj hidx1_lt') ≠ v := by
    intro j hj
    have heq := h_prefix j (le_of_lt hj)
    rw [heq]
    -- path1.vertices[j] ≠ path1.vertices[idx1] by vertices_ne_of_ne_idx
    have hne := vertices_ne_of_ne_idx spt.path1 A' j idx1 (Nat.lt_trans hj hidx1_lt) hidx1_lt (Nat.ne_of_lt hj)
    rw [hv_at_idx1] at hne
    exact hne

  -- Apply findIdx_eq_of_getElem
  apply findIdx_eq_of_getElem _ _ _ hidx1_lt'
  · simp only [beq_iff_eq]
    exact h_new_at_idx1
  · intro j hj
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact h_not_eq j hj

/-- findIdx (· == v) on newPath0.vertices equals idx0 after the involution.
    This is needed to show that the second involution uses the same index for path0. -/
private lemma findIdx_beq_newPath0_eq {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    let v := firstIntersection spt h
    let idx0 := firstIntersectionIdx spt h
    let idx1 := (spt.path1.vertices A').findIdx (· == v)
    let newPath0 := spt.path0.take idx0 ++ spt.path1.drop idx1
    (LatticePath.vertices newPath0 A).findIdx (· == v) = idx0 := by
  simp only
  let v := firstIntersection spt h
  let idx0 := firstIntersectionIdx spt h
  let hv0 := firstIntersection_mem_path0 spt h
  let hv1 := firstIntersection_mem_path1 spt h
  let idx1 := (spt.path1.vertices A').findIdx (· == v)
  let newPath0 := spt.path0.take idx0 ++ spt.path1.drop idx1

  -- idx0 < path0.vertices.length
  have hidx0_lt : idx0 < (spt.path0.vertices A).length := firstIntersectionIdx_lt spt h

  -- idx1 < path1.vertices.length
  have hidx1_lt : idx1 < (spt.path1.vertices A').length :=
    List.findIdx_lt_length_of_exists ⟨v, hv1, by simp⟩

  -- idx0 ≤ path0.length (for take/drop)
  have hidx0_le_path : idx0 ≤ spt.path0.length := by
    simp only [vertices_length] at hidx0_lt; omega

  -- idx1 ≤ path1.length (for take/drop)
  have hidx1_le_path : idx1 ≤ spt.path1.length := by
    simp only [vertices_length] at hidx1_lt; omega

  -- Length of take
  have hlen_take : (spt.path0.take idx0).length = idx0 := by
    simp [List.length_take, Nat.min_eq_left hidx0_le_path]

  -- idx0 < newPath0.vertices.length
  have hidx0_lt' : idx0 < (LatticePath.vertices newPath0 A).length := by
    have hlen : (LatticePath.vertices newPath0 A).length = newPath0.length + 1 := vertices_length newPath0 A
    have hlen2 : newPath0.length = (spt.path0.take idx0).length + (spt.path1.drop idx1).length := by
      simp only [newPath0, List.length_append]
    rw [hlen, hlen2, hlen_take]
    omega

  -- v is at index idx0 in path0.vertices (by definition of firstIntersection)
  have hv_at_idx0 : (spt.path0.vertices A)[idx0]'hidx0_lt = v := rfl

  -- First idx0+1 vertices of newPath0 equal those of path0
  have h_prefix : ∀ i (hi : i ≤ idx0),
      (LatticePath.vertices newPath0 A)[i]'(Nat.lt_of_le_of_lt hi hidx0_lt') =
      (spt.path0.vertices A)[i]'(Nat.lt_of_le_of_lt hi hidx0_lt) := by
    intro i hi
    have hi_lt : i < (spt.path0.vertices A).length := Nat.lt_of_le_of_lt hi hidx0_lt
    exact vertices_take_append_prefix spt.path0 (spt.path1.drop idx1) A idx0 i hi hi_lt

  -- v is at index idx0 in newPath0.vertices
  have h_new_at_idx0 : (LatticePath.vertices newPath0 A)[idx0]'hidx0_lt' = v := by
    have := h_prefix idx0 (le_refl idx0)
    rw [this, hv_at_idx0]

  -- For j < idx0, newPath0.vertices[j] ≠ v (by uniqueness of vertices)
  have h_not_eq : ∀ j (hj : j < idx0), (LatticePath.vertices newPath0 A)[j]'(Nat.lt_trans hj hidx0_lt') ≠ v := by
    intro j hj
    have heq := h_prefix j (le_of_lt hj)
    rw [heq]
    -- path0.vertices[j] ≠ path0.vertices[idx0] by vertices_ne_of_ne_idx
    have hne := vertices_ne_of_ne_idx spt.path0 A j idx0 (Nat.lt_trans hj hidx0_lt) hidx0_lt (Nat.ne_of_lt hj)
    rw [hv_at_idx0] at hne
    exact hne

  -- Apply findIdx_eq_of_getElem
  apply findIdx_eq_of_getElem _ _ _ hidx0_lt'
  · simp only [beq_iff_eq]
    exact h_new_at_idx0
  · intro j hj
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact h_not_eq j hj

/-- findIdx (· == v) equals firstIntersectionIdx when v = firstIntersection -/
private lemma findIdx_beq_eq_firstIntersectionIdx {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    let v := firstIntersection spt h
    let idx0 := firstIntersectionIdx spt h
    (spt.path0.vertices A).findIdx (· == v) = idx0 := by
  simp only
  have hidx0_lt := firstIntersectionIdx_lt spt h
  -- We need to show findIdx (· == v) = idx0
  -- This follows because v = verts0[idx0] and for j < idx0, verts0[j] ≠ v
  apply findIdx_eq_of_getElem _ _ _ hidx0_lt
  · -- The predicate holds at idx0: (· == v) verts0[idx0] = true
    -- By definition, v = verts0[idx0], so this is verts0[idx0] == verts0[idx0] = true
    -- Note: firstIntersection spt h = (spt.path0.vertices A)[firstIntersectionIdx spt h]
    -- and idx0 = firstIntersectionIdx spt h, so this is beq_self_eq_true
    unfold firstIntersection
    simp only [beq_self_eq_true]
  · -- The predicate fails before idx0
    intro j hj
    simp only [beq_eq_false_iff_ne, ne_eq]
    -- For j < idx0, verts0[j] ∉ verts1 (by firstIntersection_is_first)
    have ⟨_, hmin⟩ := firstIntersection_is_first spt h
    have hj_not_in := hmin j hj
    -- Since v ∈ verts1 and verts0[j] ∉ verts1, we have verts0[j] ≠ v
    have hv_in := firstIntersection_mem_path1 spt h
    intro heq
    apply hj_not_in
    rw [heq]
    exact hv_in

/-- The sign-reversing involution on intersecting signed path tuples.
    Given an ipat, we:
    1. Find the first intersection point v (deterministically, by index in path0)
    2. Exchange the tails of the two paths at v
    3. Flip the sign (swap toBB')

    This maps ipats to (B,B') ↔ ipats to (B',B).

    Note: We use `firstIntersection` instead of `Classical.choose` to ensure the
    involution is truly involutive. The key property is that after swapping tails,
    the same point v is still the first intersection point. -/
noncomputable def ipatInvolution {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B')
    (h : spt.isIntersecting) : SignedPathTuple2 A A' B B' :=
  -- Get the first intersection point (deterministic choice)
  let v := firstIntersection spt h
  let hv0 := firstIntersection_mem_path0 spt h
  let hv1 := firstIntersection_mem_path1 spt h
  -- Get the indices where v occurs in each path's vertices
  let idx0 := (spt.path0.vertices A).findIdx (· == v)
  let idx1 := (spt.path1.vertices A').findIdx (· == v)
  -- Split both paths at v: (head, tail) where head ends at v and tail starts at v
  let head0 := spt.path0.take idx0
  let tail0 := spt.path0.drop idx0
  let head1 := spt.path1.take idx1
  let tail1 := spt.path1.drop idx1
  -- Create new paths by exchanging tails
  let newPath0 := head0 ++ tail1
  let newPath1 := head1 ++ tail0
  -- The new path tuple has flipped sign
  { path0 := newPath0
    path1 := newPath1
    toBB' := !spt.toBB'
    valid0 := by
      -- newPath0 = head0 ++ tail1 goes A → v → (dest of path1)
      -- where dest of path1 = (if spt.toBB' then B' else B)
      -- and (if !spt.toBB' then B else B') = (if spt.toBB' then B' else B)
      show LatticePath.isPathFromTo newPath0 A (if !spt.toBB' then B else B')
      -- head0 goes A → v (by splitPathAt_head_endpoint)
      have hhead0 : LatticePath.isPathFromTo head0 A v :=
        splitPathAt_head_endpoint spt.path0 A v hv0
      -- path1 goes A' → (if spt.toBB' then B' else B)
      -- so tail1 = path1.drop idx1 goes v → (if spt.toBB' then B' else B)
      have hsplit1 := LatticePath.isPathFromTo_take_drop spt.path1 idx1 A' (if spt.toBB' then B' else B) spt.valid1
      have hhead1_eq_v : LatticePath.endpoint head1 A' = v :=
        splitPathAt_head_endpoint spt.path1 A' v hv1
      simp only at hsplit1
      rw [hhead1_eq_v] at hsplit1
      have htail1 : LatticePath.isPathFromTo tail1 v (if spt.toBB' then B' else B) := hsplit1.2
      -- newPath0 = head0 ++ tail1 goes A → v → (if spt.toBB' then B' else B)
      have hconcat := LatticePath.isPathFromTo_append head0 tail1 A v
        (if spt.toBB' then B' else B) hhead0 htail1
      -- (if !spt.toBB' then B else B') = (if spt.toBB' then B' else B)
      convert hconcat using 1
      cases spt.toBB' <;> rfl
    valid1 := by
      -- newPath1 = head1 ++ tail0 goes A' → v → (dest of path0)
      -- where dest of path0 = (if spt.toBB' then B else B')
      -- and (if !spt.toBB' then B' else B) = (if spt.toBB' then B else B')
      show LatticePath.isPathFromTo newPath1 A' (if !spt.toBB' then B' else B)
      -- head1 goes A' → v (by splitPathAt_head_endpoint)
      have hhead1 : LatticePath.isPathFromTo head1 A' v :=
        splitPathAt_head_endpoint spt.path1 A' v hv1
      -- path0 goes A → (if spt.toBB' then B else B')
      -- so tail0 = path0.drop idx0 goes v → (if spt.toBB' then B else B')
      have hsplit0 := LatticePath.isPathFromTo_take_drop spt.path0 idx0 A (if spt.toBB' then B else B') spt.valid0
      have hhead0_eq_v : LatticePath.endpoint head0 A = v :=
        splitPathAt_head_endpoint spt.path0 A v hv0
      simp only at hsplit0
      rw [hhead0_eq_v] at hsplit0
      have htail0 : LatticePath.isPathFromTo tail0 v (if spt.toBB' then B else B') := hsplit0.2
      -- newPath1 = head1 ++ tail0 goes A' → v → (if spt.toBB' then B else B')
      have hconcat := LatticePath.isPathFromTo_append head1 tail0 A' v
        (if spt.toBB' then B else B') hhead1 htail0
      -- (if !spt.toBB' then B' else B) = (if spt.toBB' then B else B')
      convert hconcat using 1
      cases spt.toBB' <;> rfl
  }

/-- Helper: flipping a Bool flips the sign. -/
private theorem sign_flip (b : Bool) : (if !b then (1 : ℤ) else -1) = -(if b then 1 else -1) := by
  cases b <;> simp

/-- The involution is sign-reversing. -/
theorem ipatInvolution_sign {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    (ipatInvolution spt h).sign = -spt.sign := by
  simp only [ipatInvolution, SignedPathTuple2.sign]
  exact sign_flip spt.toBB'

/-- The involution preserves being intersecting. -/
theorem ipatInvolution_isIntersecting {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    (ipatInvolution spt h).isIntersecting := by
  -- The first intersection point v is still shared after exchanging tails
  unfold ipatInvolution SignedPathTuple2.isIntersecting
  simp only
  -- Use the deterministic first intersection point
  let v := firstIntersection spt h
  let hv0 := firstIntersection_mem_path0 spt h
  let hv1 := firstIntersection_mem_path1 spt h
  use v
  constructor
  · -- v ∈ (head0 ++ tail1).vertices A
    have hhead0_endpoint : LatticePath.endpoint (spt.path0.take ((spt.path0.vertices A).findIdx (· == v))) A = v :=
      splitPathAt_head_endpoint spt.path0 A v hv0
    have := mem_vertices_append_of_endpoint
      (spt.path0.take ((spt.path0.vertices A).findIdx (· == v)))
      (spt.path1.drop ((spt.path1.vertices A').findIdx (· == v)))
      A
    rw [hhead0_endpoint] at this
    convert this
  · -- v ∈ (head1 ++ tail0).vertices A'
    have hhead1_endpoint : LatticePath.endpoint (spt.path1.take ((spt.path1.vertices A').findIdx (· == v))) A' = v :=
      splitPathAt_head_endpoint spt.path1 A' v hv1
    have := mem_vertices_append_of_endpoint
      (spt.path1.take ((spt.path1.vertices A').findIdx (· == v)))
      (spt.path0.drop ((spt.path0.vertices A).findIdx (· == v)))
      A'
    rw [hhead1_endpoint] at this
    convert this

/-- Key lemma: The first intersection point is preserved after swapping tails.

    If we swap tails at the first intersection point v, then v is still the first
    intersection point in the new paths. This is because:
    1. The head of path0 (vertices 0..idx) is unchanged
    2. v is at index idx in both the original and new path0's vertices
    3. No earlier vertex in head0 is in path1's vertices (by minimality)

    This lemma is essential for proving that the involution is involutive. -/
lemma firstIntersection_preserved {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting)
    (h' : (ipatInvolution spt h).isIntersecting) :
    firstIntersection (ipatInvolution spt h) h' = firstIntersection spt h := by
  -- Define key values
  let v := firstIntersection spt h
  let idx0 := firstIntersectionIdx spt h
  let hv0 := firstIntersection_mem_path0 spt h
  let hv1 := firstIntersection_mem_path1 spt h
  let idx1 := (spt.path1.vertices A').findIdx (· == v)
  let newPath0 := spt.path0.take idx0 ++ spt.path1.drop idx1
  let newPath1 := spt.path1.take idx1 ++ spt.path0.drop idx0

  -- Key facts about indices
  have hidx0_lt : idx0 < (spt.path0.vertices A).length := firstIntersectionIdx_lt spt h
  have hidx1_lt : idx1 < (spt.path1.vertices A').length :=
    List.findIdx_lt_length_of_exists ⟨v, hv1, by simp⟩
  have hidx0_lt_path : idx0 < spt.path0.length + 1 := by
    simp only [vertices_length] at hidx0_lt; exact hidx0_lt
  have hidx0_le_path : idx0 ≤ spt.path0.length := by omega

  -- v is at index idx0 in path0.vertices A
  have hv_at_idx0 : (spt.path0.vertices A)[idx0]'hidx0_lt = v := rfl

  -- Length facts for newPath0
  have hlen_newPath0_path : newPath0.length = min idx0 spt.path0.length + (spt.path1.length - idx1) := by
    simp only [newPath0, List.length_append, List.length_take, List.length_drop]
  have hlen_newPath0_vertices : (LatticePath.vertices newPath0 A).length =
      min idx0 spt.path0.length + (spt.path1.length - idx1) + 1 := by
    simp only [vertices_length, hlen_newPath0_path]

  -- idx0 < newPath0.vertices.length
  have hidx0_lt' : idx0 < (LatticePath.vertices newPath0 A).length := by
    simp only [hlen_newPath0_vertices]
    have : min idx0 spt.path0.length = idx0 := Nat.min_eq_left hidx0_le_path
    omega

  -- First idx0+1 vertices of newPath0 equal those of path0
  have h_prefix : ∀ i (hi : i ≤ idx0),
      (LatticePath.vertices newPath0 A)[i]'(Nat.lt_of_le_of_lt hi hidx0_lt') =
      (spt.path0.vertices A)[i]'(Nat.lt_of_le_of_lt hi hidx0_lt) := by
    intro i hi
    have hi_lt : i < (spt.path0.vertices A).length := Nat.lt_of_le_of_lt hi hidx0_lt
    exact vertices_take_append_prefix spt.path0 (spt.path1.drop idx1) A idx0 i hi hi_lt

  -- v is in newPath1.vertices A'
  have hv_in_newPath1 : v ∈ LatticePath.vertices newPath1 A' := by
    have hhead1_endpoint : LatticePath.endpoint (spt.path1.take idx1) A' = v :=
      splitPathAt_head_endpoint spt.path1 A' v hv1
    have := mem_vertices_append_of_endpoint (spt.path1.take idx1) (spt.path0.drop idx0) A'
    rw [hhead1_endpoint] at this
    exact this

  -- For i < idx0, (path0.vertices A)[i] ∉ newPath1.vertices A'
  have h_not_in : ∀ i (hi : i < idx0),
      ¬((spt.path0.vertices A)[i]'(Nat.lt_trans hi hidx0_lt) ∈ LatticePath.vertices newPath1 A') := by
    intro i hi hmem
    have ⟨_, h_not_in_path1⟩ := firstIntersection_is_first spt h
    have h_not_in_path1' := h_not_in_path1 i hi
    rw [vertices_eq_scanl, scanl_append] at hmem
    simp only [List.mem_append] at hmem
    cases hmem with
    | inl h_in_take =>
      have h_take_prefix : (spt.path1.take idx1).scanl (fun p s => s.apply p) A' =
          (spt.path1.scanl (fun p s => s.apply p) A').take (idx1 + 1) := scanl_take spt.path1 A' idx1
      rw [h_take_prefix] at h_in_take
      have h_in_full := List.mem_of_mem_take h_in_take
      rw [← vertices_eq_scanl] at h_in_full
      exact h_not_in_path1' h_in_full
    | inr h_in_drop_tail =>
      have hfoldl_eq : (spt.path1.take idx1).foldl (fun p s => s.apply p) A' = v := by
        have := splitPathAt_head_endpoint spt.path1 A' v hv1
        unfold LatticePath.endpoint at this
        exact this
      simp only [hfoldl_eq] at h_in_drop_tail
      cases hpath0_drop : (spt.path0.drop idx0).scanl (fun p s => s.apply p) v with
      | nil =>
        simp only [hpath0_drop, List.tail_nil] at h_in_drop_tail
        simp at h_in_drop_tail

      | cons _ rest =>
        simp only [hpath0_drop, List.tail_cons] at h_in_drop_tail
        have h_not_in_drop := vertex_not_mem_drop_vertices spt.path0 A i idx0 hi hidx0_lt
        rw [hv_at_idx0] at h_not_in_drop
        rw [vertices_eq_scanl] at h_not_in_drop
        have h_in_scanl : (spt.path0.vertices A)[i]'(Nat.lt_trans hi hidx0_lt) ∈
            (spt.path0.drop idx0).scanl (fun p s => s.apply p) v := by
          rw [hpath0_drop]
          simp only [List.mem_cons]
          right
          exact h_in_drop_tail
        rw [← vertices_eq_scanl] at h_in_scanl
        exact h_not_in_drop h_in_scanl


  -- The findIdx on newPath0.vertices A equals idx0
  have h_findIdx_eq : (LatticePath.vertices newPath0 A).findIdx (fun v => decide (v ∈ LatticePath.vertices newPath1 A')) = idx0 := by
    apply findIdx_preserved_by_prefix (spt.path0.vertices A) (LatticePath.vertices newPath0 A)
        (LatticePath.vertices newPath1 A') idx0 hidx0_lt hidx0_lt'
    · intro i hi; exact h_prefix i hi
    · rw [hv_at_idx0]; exact hv_in_newPath1
    · exact h_not_in

  -- The value at idx0 in newPath0.vertices equals v
  have h_new_at_idx0 : (LatticePath.vertices newPath0 A)[idx0]'hidx0_lt' = v := by
    have := h_prefix idx0 (le_refl idx0)
    rw [this, hv_at_idx0]

  -- The ipatInvolution path0 is equal to newPath0
  -- Key: findIdx (· == v) on path0.vertices equals idx0 = firstIntersectionIdx
  have h_path0_eq : (ipatInvolution spt h).path0 = newPath0 := by
    unfold ipatInvolution
    simp only
    -- The LHS uses findIdx (· == v) for indices, we need to show these equal idx0 and idx1
    have h_idx0_eq := findIdx_beq_eq_firstIntersectionIdx spt h
    -- idx1 is defined as findIdx (· == v) on path1.vertices, so it's definitionally equal
    simp only [h_idx0_eq]
    -- Now both sides are spt.path0.take idx0 ++ spt.path1.drop idx1
    rfl
  have h_path1_eq : (ipatInvolution spt h).path1 = newPath1 := by
    unfold ipatInvolution
    simp only
    have h_idx0_eq := findIdx_beq_eq_firstIntersectionIdx spt h
    simp only [h_idx0_eq]
    rfl

  -- The firstIntersectionIdx for the involution equals idx0
  have h_idx_eq : firstIntersectionIdx (ipatInvolution spt h) h' = idx0 := by
    unfold firstIntersectionIdx
    rw [h_path0_eq, h_path1_eq]
    exact h_findIdx_eq

  -- Final calculation
  -- We need to show: firstIntersection (ipatInvolution spt h) h' = v
  -- By definition, firstIntersection = verts0[firstIntersectionIdx]
  -- We've shown: firstIntersectionIdx = idx0, and path0 = newPath0
  -- So we need: newPath0.vertices A)[idx0] = v, which is h_new_at_idx0
  show firstIntersection (ipatInvolution spt h) h' = v
  unfold firstIntersection
  -- The goal is: ((ipatInvolution spt h).path0.vertices A)[firstIntersectionIdx (ipatInvolution spt h) h'] = v
  -- Use simp to handle the dependent type issue
  simp only [h_path0_eq, h_idx_eq]
  exact h_new_at_idx0

/-- Extensionality for SignedPathTuple2 -/
private lemma SignedPathTuple2.ext' {A A' B B' : LatticePoint}
    {spt1 spt2 : SignedPathTuple2 A A' B B'}
    (h0 : spt1.path0 = spt2.path0) (h1 : spt1.path1 = spt2.path1) (hb : spt1.toBB' = spt2.toBB') :
    spt1 = spt2 := by
  cases spt1; cases spt2; simp only at h0 h1 hb; subst h0 h1 hb; rfl

/-- The involution is its own inverse.

    After applying the involution twice, we get back the original path tuple.
    The key insight is that:
    1. The first intersection point v is preserved after swapping tails (by firstIntersection_preserved)
    2. The indices idx0 and idx1 are also preserved
    3. Exchanging tails twice returns the original paths (take_append_drop)
    4. toBB' flips twice (!!b = b)

    **Proof strategy:**
    - Use `firstIntersection_preserved` to show v' = v
    - Use `findIdx_beq_eq_firstIntersectionIdx` and `findIdx_beq_newPath1_eq` to show idx0' = idx0 and idx1' = idx1
    - Apply List.take_append_drop to reconstruct the original paths -/
theorem ipatInvolution_involutive {A A' B B' : LatticePoint}
    (spt : SignedPathTuple2 A A' B B') (h : spt.isIntersecting) :
    let spt' := ipatInvolution spt h
    ∃ h' : spt'.isIntersecting, ipatInvolution spt' h' = spt := by
  -- First, show that the involution preserves being intersecting
  have h_isIntersecting : (ipatInvolution spt h).isIntersecting := ipatInvolution_isIntersecting spt h
  use h_isIntersecting
  -- Use the key lemma: firstIntersection is preserved
  have hv_preserved := firstIntersection_preserved spt h h_isIntersecting
  -- Define key values
  let v := firstIntersection spt h
  let idx0 := firstIntersectionIdx spt h
  let idx1 := (spt.path1.vertices A').findIdx (· == v)
  -- Key index bounds
  have hidx0_lt := firstIntersectionIdx_lt spt h
  have hidx1_lt : idx1 < (spt.path1.vertices A').length :=
    List.findIdx_lt_length_of_exists ⟨v, firstIntersection_mem_path1 spt h, by simp⟩
  have hidx0_le : idx0 ≤ spt.path0.length := by simp only [vertices_length] at hidx0_lt; omega
  have hidx1_le : idx1 ≤ spt.path1.length := by simp only [vertices_length] at hidx1_lt; omega
  -- The involution uses findIdx (· == v) which equals idx0 and idx1
  have h_idx0_eq := findIdx_beq_eq_firstIntersectionIdx spt h
  have h_idx1_eq := findIdx_beq_newPath1_eq spt h
  -- Length facts
  have hlen0 : (spt.path0.take idx0).length = idx0 := List.length_take_of_le hidx0_le
  have hlen1 : (spt.path1.take idx1).length = idx1 := List.length_take_of_le hidx1_le
  -- The key list manipulation lemmas
  have htake0 : (spt.path0.take idx0 ++ spt.path1.drop idx1).take idx0 = spt.path0.take idx0 := by
    rw [List.take_append_of_le_length (by simp [hlen0])]
    simp [List.take_take]
  have hdrop0 : (spt.path1.take idx1 ++ spt.path0.drop idx0).drop idx1 = spt.path0.drop idx0 := by
    have key : (spt.path1.take idx1).length = idx1 := hlen1
    calc (spt.path1.take idx1 ++ spt.path0.drop idx0).drop idx1
        = (spt.path1.take idx1 ++ spt.path0.drop idx0).drop (spt.path1.take idx1).length := by rw [key]
      _ = spt.path0.drop idx0 := List.drop_left
  have htake1 : (spt.path1.take idx1 ++ spt.path0.drop idx0).take idx1 = spt.path1.take idx1 := by
    rw [List.take_append_of_le_length (by simp [hlen1])]
    simp [List.take_take]
  have hdrop1 : (spt.path0.take idx0 ++ spt.path1.drop idx1).drop idx0 = spt.path1.drop idx1 := by
    have key : (spt.path0.take idx0).length = idx0 := hlen0
    calc (spt.path0.take idx0 ++ spt.path1.drop idx1).drop idx0
        = (spt.path0.take idx0 ++ spt.path1.drop idx1).drop (spt.path0.take idx0).length := by rw [key]
      _ = spt.path1.drop idx1 := List.drop_left
  -- The reconstruction lemmas
  have hpath0_eq : spt.path0.take idx0 ++ spt.path0.drop idx0 = spt.path0 := List.take_append_drop idx0 spt.path0
  have hpath1_eq : spt.path1.take idx1 ++ spt.path1.drop idx1 = spt.path1 := List.take_append_drop idx1 spt.path1

  -- Define the new paths after first involution
  let newPath0 := spt.path0.take idx0 ++ spt.path1.drop idx1
  let newPath1 := spt.path1.take idx1 ++ spt.path0.drop idx0

  -- The paths of the first involution
  have h_path0_eq' : (ipatInvolution spt h).path0 = newPath0 := by
    unfold ipatInvolution
    simp only [h_idx0_eq]
    rfl
  have h_path1_eq' : (ipatInvolution spt h).path1 = newPath1 := by
    unfold ipatInvolution
    simp only [h_idx0_eq]
    rfl

  -- The indices for the second involution
  -- v' = v (by hv_preserved)
  -- findIdx (· == v) on newPath0.vertices = idx0 (by findIdx_beq_newPath0_eq)
  -- findIdx (· == v) on newPath1.vertices = idx1 (by findIdx_beq_newPath1_eq)
  have h_idx0_eq' := findIdx_beq_newPath0_eq spt h
  have h_idx1_eq' := findIdx_beq_newPath1_eq spt h

  -- The second involution produces:
  -- path0'' = newPath0.take idx0 ++ newPath1.drop idx1 = path0.take idx0 ++ path0.drop idx0 = path0
  -- path1'' = newPath1.take idx1 ++ newPath0.drop idx0 = path1.take idx1 ++ path1.drop idx1 = path1
  -- toBB'' = !!spt.toBB' = spt.toBB'

  -- Compute the second involution's paths
  have h_second_path0 : (ipatInvolution (ipatInvolution spt h) h_isIntersecting).path0 = spt.path0 := by
    unfold ipatInvolution
    -- The first intersection of the involution is v (by hv_preserved)
    have hv' : firstIntersection (ipatInvolution spt h) h_isIntersecting = v := hv_preserved
    -- After unfolding, the goal involves the paths of (ipatInvolution spt h)
    -- which are newPath0 and newPath1
    -- The indices used are findIdx (· == v') on newPath0.vertices and newPath1.vertices
    -- Since v' = v, these equal idx0 and idx1 by h_idx0_eq' and h_idx1_eq'
    show (ipatInvolution spt h).path0.take ((((ipatInvolution spt h).path0).vertices A).findIdx (· == firstIntersection (ipatInvolution spt h) h_isIntersecting)) ++
         (ipatInvolution spt h).path1.drop ((((ipatInvolution spt h).path1).vertices A').findIdx (· == firstIntersection (ipatInvolution spt h) h_isIntersecting)) = spt.path0
    rw [hv', h_path0_eq', h_path1_eq', h_idx0_eq', h_idx1_eq']
    -- newPath0.take idx0 ++ newPath1.drop idx1 = path0.take idx0 ++ path0.drop idx0 = path0
    rw [htake0, hdrop0, hpath0_eq]

  have h_second_path1 : (ipatInvolution (ipatInvolution spt h) h_isIntersecting).path1 = spt.path1 := by
    unfold ipatInvolution
    have hv' : firstIntersection (ipatInvolution spt h) h_isIntersecting = v := hv_preserved
    show (ipatInvolution spt h).path1.take ((((ipatInvolution spt h).path1).vertices A').findIdx (· == firstIntersection (ipatInvolution spt h) h_isIntersecting)) ++
         (ipatInvolution spt h).path0.drop ((((ipatInvolution spt h).path0).vertices A).findIdx (· == firstIntersection (ipatInvolution spt h) h_isIntersecting)) = spt.path1
    rw [hv', h_path0_eq', h_path1_eq', h_idx0_eq', h_idx1_eq']
    -- newPath1.take idx1 ++ newPath0.drop idx0 = path1.take idx1 ++ path1.drop idx1 = path1
    rw [htake1, hdrop1, hpath1_eq]

  have h_second_toBB' : (ipatInvolution (ipatInvolution spt h) h_isIntersecting).toBB' = spt.toBB' := by
    unfold ipatInvolution
    simp only [Bool.not_not]

  -- Use extensionality to conclude
  exact SignedPathTuple2.ext' h_second_path0 h_second_path1 h_second_toBB'


/-- The set of signed path tuples is finite. -/
theorem signedPathTuples2_finite (A A' B B' : LatticePoint) :
    (signedPathTuples2 A A' B B').Finite := by
  let S0 := pathsFromTo A B ∪ pathsFromTo A B'
  let S1 := pathsFromTo A' B' ∪ pathsFromTo A' B
  have hS0_fin : S0.Finite := Set.Finite.union (pathsFromTo_finite A B) (pathsFromTo_finite A B')
  have hS1_fin : S1.Finite := Set.Finite.union (pathsFromTo_finite A' B') (pathsFromTo_finite A' B)
  let f : SignedPathTuple2 A A' B B' → LatticePath × LatticePath × Bool :=
    fun spt => (spt.path0, spt.path1, spt.toBB')
  have f_inj : Function.Injective f := by
    intro spt1 spt2 h
    simp only [f, Prod.mk.injEq] at h
    cases spt1; cases spt2; simp only at h
    obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; rfl
  have hrange : f '' signedPathTuples2 A A' B B' ⊆ S0 ×ˢ S1 ×ˢ (Set.univ : Set Bool) := by
    intro x hx
    obtain ⟨spt, _, rfl⟩ := hx
    simp only [Set.mem_prod, Set.mem_union, Set.mem_univ, and_true, f, S0, S1, pathsFromTo, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · cases hb : spt.toBB'
      · have := spt.valid0; simp only [hb, Bool.false_eq_true, ↓reduceIte] at this; right; exact this
      · have := spt.valid0; simp only [hb, ↓reduceIte] at this; left; exact this
    · cases hb : spt.toBB'
      · have := spt.valid1; simp only [hb, Bool.false_eq_true, ↓reduceIte] at this; right; exact this
      · have := spt.valid1; simp only [hb, ↓reduceIte] at this; left; exact this
  have hfin_target : (S0 ×ˢ S1 ×ˢ (Set.univ : Set Bool)).Finite :=
    Set.Finite.prod hS0_fin (Set.Finite.prod hS1_fin (Set.finite_univ (α := Bool)))
  have hfin_image : (f '' signedPathTuples2 A A' B B').Finite := hfin_target.subset hrange
  exact Set.Finite.of_finite_image hfin_image f_inj.injOn

/-- The set of non-intersecting signed path tuples is finite. -/
theorem signedNipats2_finite (A A' B B' : LatticePoint) :
    (signedNipats2 A A' B B').Finite :=
  (signedPathTuples2_finite A A' B B').subset (Set.subset_univ _)

/-- The set of intersecting signed path tuples is finite. -/
theorem signedIpats2_finite (A A' B B' : LatticePoint) :
    (signedIpats2 A A' B B').Finite :=
  (signedPathTuples2_finite A A' B B').subset (Set.subset_univ _)

/-- The sum over all signed path tuples equals the difference of path tuple counts. -/
theorem sum_signedPathTuples2 (A A' B B' : LatticePoint)
    (hfin : (signedPathTuples2 A A' B B').Finite) :
    ∑ spt ∈ hfin.toFinset, spt.sign =
      (numPaths A B : ℤ) * numPaths A' B' - (numPaths A B' : ℤ) * numPaths A' B := by
  -- Split the sum based on toBB'
  have h_split : ∑ spt ∈ hfin.toFinset, spt.sign =
      ∑ spt ∈ hfin.toFinset.filter (·.toBB' = true), spt.sign +
      ∑ spt ∈ hfin.toFinset.filter (·.toBB' = false), spt.sign := by
    rw [← Finset.sum_filter_add_sum_filter_not (p := fun spt => spt.toBB' = true)]
    congr 1
    apply Finset.sum_congr
    · ext x; simp only [Finset.mem_filter, and_congr_right_iff]
      intro _; cases x.toBB' <;> simp
    · intros; rfl
  rw [h_split]
  -- For toBB' = true, sign = 1
  have h_true : ∑ spt ∈ hfin.toFinset.filter (·.toBB' = true), spt.sign =
      (hfin.toFinset.filter (·.toBB' = true)).card := by
    rw [Finset.sum_eq_card_nsmul (b := (1 : ℤ))]
    · simp
    · intro spt hspt
      simp only [Finset.mem_filter] at hspt
      simp only [SignedPathTuple2.sign, hspt.2, ↓reduceIte]
  -- For toBB' = false, sign = -1
  have h_false : ∑ spt ∈ hfin.toFinset.filter (·.toBB' = false), spt.sign =
      -((hfin.toFinset.filter (·.toBB' = false)).card : ℤ) := by
    rw [Finset.sum_eq_card_nsmul (b := (-1 : ℤ))]
    · simp
    · intro spt hspt
      simp only [Finset.mem_filter] at hspt
      simp only [SignedPathTuple2.sign, hspt.2, Bool.false_eq_true, ↓reduceIte]
  rw [h_true, h_false]
  -- Now we need to relate the filter cardinalities to numPaths products
  have hfin_AB := pathsFromTo_finite A B
  have hfin_A'B' := pathsFromTo_finite A' B'
  have hfin_AB' := pathsFromTo_finite A B'
  have hfin_A'B := pathsFromTo_finite A' B
  -- Card of true filter = numPaths A B * numPaths A' B'
  have h_card_true : (hfin.toFinset.filter (·.toBB' = true)).card =
      numPaths A B * numPaths A' B' := by
    rw [numPaths_eq_card A B hfin_AB, numPaths_eq_card A' B' hfin_A'B']
    -- The filter is in bijection with the product
    -- Define the bijection
    let f : { spt : SignedPathTuple2 A A' B B' // spt ∈ hfin.toFinset.filter (·.toBB' = true) } →
            hfin_AB.toFinset × hfin_A'B'.toFinset := fun ⟨spt, hspt⟩ =>
      ⟨⟨spt.path0, by
        simp only [Set.Finite.mem_toFinset, pathsFromTo, Set.mem_setOf_eq]
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedPathTuples2,
                   Set.mem_univ, true_and] at hspt
        have h := spt.valid0
        simp only [hspt, ↓reduceIte] at h
        exact h⟩,
       ⟨spt.path1, by
        simp only [Set.Finite.mem_toFinset, pathsFromTo, Set.mem_setOf_eq]
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedPathTuples2,
                   Set.mem_univ, true_and] at hspt
        have h := spt.valid1
        simp only [hspt, ↓reduceIte] at h
        exact h⟩⟩
    let g : hfin_AB.toFinset × hfin_A'B'.toFinset →
            { spt : SignedPathTuple2 A A' B B' // spt ∈ hfin.toFinset.filter (·.toBB' = true) } :=
      fun ⟨⟨p0, hp0⟩, ⟨p1, hp1⟩⟩ =>
        ⟨⟨p0, p1, true, by
          simp only [Set.Finite.mem_toFinset, pathsFromTo, Set.mem_setOf_eq] at hp0
          simp only [↓reduceIte]
          exact hp0, by
          simp only [Set.Finite.mem_toFinset, pathsFromTo, Set.mem_setOf_eq] at hp1
          simp only [↓reduceIte]
          exact hp1⟩, by
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedPathTuples2,
                     Set.mem_univ, true_and]⟩
    have hfg : Function.LeftInverse g f := by
      intro ⟨spt, hspt⟩
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedPathTuples2,
                 Set.mem_univ, true_and] at hspt
      simp only [f, g, Subtype.mk.injEq]
      cases spt
      simp only at hspt ⊢
      subst hspt
      rfl
    have hgf : Function.RightInverse g f := fun ⟨⟨p0, hp0⟩, ⟨p1, hp1⟩⟩ => rfl
    have hbij' : Function.Bijective f := ⟨hfg.injective, hgf.surjective⟩
    have h1 := Fintype.card_of_bijective hbij'
    simp only [Fintype.card_prod, Fintype.card_coe] at h1
    exact h1
  -- Card of false filter = numPaths A B' * numPaths A' B
  have h_card_false : (hfin.toFinset.filter (·.toBB' = false)).card =
      numPaths A B' * numPaths A' B := by
    rw [numPaths_eq_card A B' hfin_AB', numPaths_eq_card A' B hfin_A'B]
    let f : { spt : SignedPathTuple2 A A' B B' // spt ∈ hfin.toFinset.filter (·.toBB' = false) } →
            hfin_AB'.toFinset × hfin_A'B.toFinset := fun ⟨spt, hspt⟩ =>
      ⟨⟨spt.path0, by
        simp only [Set.Finite.mem_toFinset, pathsFromTo, Set.mem_setOf_eq]
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedPathTuples2,
                   Set.mem_univ, true_and] at hspt
        have h := spt.valid0
        simp only [hspt, Bool.false_eq_true, ↓reduceIte] at h
        exact h⟩,
       ⟨spt.path1, by
        simp only [Set.Finite.mem_toFinset, pathsFromTo, Set.mem_setOf_eq]
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedPathTuples2,
                   Set.mem_univ, true_and] at hspt
        have h := spt.valid1
        simp only [hspt, Bool.false_eq_true, ↓reduceIte] at h
        exact h⟩⟩
    let g : hfin_AB'.toFinset × hfin_A'B.toFinset →
            { spt : SignedPathTuple2 A A' B B' // spt ∈ hfin.toFinset.filter (·.toBB' = false) } :=
      fun ⟨⟨p0, hp0⟩, ⟨p1, hp1⟩⟩ =>
        ⟨⟨p0, p1, false, by
          simp only [Set.Finite.mem_toFinset, pathsFromTo, Set.mem_setOf_eq] at hp0
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hp0, by
          simp only [Set.Finite.mem_toFinset, pathsFromTo, Set.mem_setOf_eq] at hp1
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hp1⟩, by
          simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedPathTuples2,
                     Set.mem_univ, true_and]⟩
    have hfg : Function.LeftInverse g f := by
      intro ⟨spt, hspt⟩
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedPathTuples2,
                 Set.mem_univ, true_and] at hspt
      simp only [f, g, Subtype.mk.injEq]
      cases spt
      simp only at hspt ⊢
      subst hspt
      rfl
    have hgf : Function.RightInverse g f := fun ⟨⟨p0, hp0⟩, ⟨p1, hp1⟩⟩ => rfl
    have hbij' : Function.Bijective f := ⟨hfg.injective, hgf.surjective⟩
    have h1 := Fintype.card_of_bijective hbij'
    simp only [Fintype.card_prod, Fintype.card_coe] at h1
    exact h1
  rw [h_card_true, h_card_false]
  push_cast
  ring

/-- The sum over intersecting path tuples is zero (by sign-reversing involution). -/
theorem sum_signedIpats2_eq_zero (A A' B B' : LatticePoint)
    (hfin : (signedIpats2 A A' B B').Finite) :
    ∑ spt ∈ hfin.toFinset, spt.sign = 0 := by
  -- Use Finset.sum_involution with ipatInvolution
  -- Define the involution function g on the finite set
  let g : ∀ spt ∈ hfin.toFinset, SignedPathTuple2 A A' B B' := fun spt hspt =>
    ipatInvolution spt (by
      simp only [Set.Finite.mem_toFinset, signedIpats2, Set.mem_setOf_eq] at hspt
      exact hspt)
  -- Prove that g maps elements back into the set
  have g_mem : ∀ spt hspt, g spt hspt ∈ hfin.toFinset := fun spt hspt => by
    simp only [Set.Finite.mem_toFinset, signedIpats2, Set.mem_setOf_eq] at hspt ⊢
    simp only [g]
    exact ipatInvolution_isIntersecting spt hspt
  -- Apply Finset.sum_involution
  refine Finset.sum_involution g ?hg₁ ?hg₃ g_mem ?hg₄
  case hg₁ => -- Signs sum to zero: spt.sign + (g spt).sign = 0
    intro spt hspt
    simp only [Set.Finite.mem_toFinset, signedIpats2, Set.mem_setOf_eq] at hspt
    simp only [g]
    have h := ipatInvolution_sign spt hspt
    omega
  case hg₃ => -- g is not the identity on non-zero elements
    intro spt hspt hne
    simp only [Set.Finite.mem_toFinset, signedIpats2, Set.mem_setOf_eq] at hspt
    simp only [g]
    intro heq
    have h := ipatInvolution_sign spt hspt
    rw [heq] at h
    simp only [SignedPathTuple2.sign] at h hne
    omega
  case hg₄ => -- g is an involution: g (g spt) = spt
    intro spt hspt
    simp only [Set.Finite.mem_toFinset, signedIpats2, Set.mem_setOf_eq] at hspt
    simp only [g]
    have h := ipatInvolution_involutive spt hspt
    obtain ⟨h', heq⟩ := h
    convert heq using 2

/-- Define the subset with toBB' = true -/
private def signedNipats2_true (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  { spt ∈ signedNipats2 A A' B B' | spt.toBB' = true }

/-- Define the subset with toBB' = false -/
private def signedNipats2_false (A A' B B' : LatticePoint) : Set (SignedPathTuple2 A A' B B') :=
  { spt ∈ signedNipats2 A A' B B' | spt.toBB' = false }

private lemma PathTuple.ext' {k : ℕ} {A B : kVertex k} {pt1 pt2 : PathTuple k A B}
    (h : pt1.paths = pt2.paths) : pt1 = pt2 := by
  cases pt1; cases pt2; simp only at h; subst h; rfl

/-- Key lemma: signedNipats2_true has the same ncard as nipatsFromTo ![A, A'] ![B, B'] -/
private lemma signedNipats2_true_ncard_eq (A A' B B' : LatticePoint) :
    (signedNipats2_true A A' B B').ncard = (nipatsFromTo (![A, A'] : kVertex 2) ![B, B']).ncard := by
  simp only [Set.ncard]
  congr 1
  apply Set.encard_congr
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  case toFun =>
    intro ⟨spt, hspt⟩
    have hni : ¬spt.isIntersecting := hspt.1
    have htoBB' : spt.toBB' = true := hspt.2
    refine ⟨⟨![spt.path0, spt.path1], ?_⟩, ?_⟩
    · intro i
      fin_cases i
      · convert spt.valid0 using 1; simp [htoBB']
      · convert spt.valid1 using 1; simp [htoBB']
    · simp only [nipatsFromTo, Set.mem_setOf_eq, PathTuple.isNonIntersecting]
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · rw [Set.disjoint_iff]
        intro v ⟨hv0, hv1⟩
        simp only [PathTuple.verticesOf, Set.mem_setOf_eq] at hv0 hv1
        exact hni ⟨v, hv0, hv1⟩
      · rw [Set.disjoint_iff]
        intro v ⟨hv1, hv0⟩
        simp only [PathTuple.verticesOf, Set.mem_setOf_eq] at hv0 hv1
        exact hni ⟨v, hv0, hv1⟩
      · exact (hij rfl).elim
  case invFun =>
    intro ⟨pt, hpt⟩
    simp only [nipatsFromTo, Set.mem_setOf_eq] at hpt
    refine ⟨⟨pt.paths 0, pt.paths 1, true, ?_, ?_⟩, ?_, rfl⟩
    · simp only [↓reduceIte]; exact pt.valid 0
    · simp only [↓reduceIte]; exact pt.valid 1
    · simp only [signedNipats2, Set.mem_setOf_eq, SignedPathTuple2.isIntersecting, not_exists, not_and]
      intro v hv0 hv1
      have hdisj := hpt 0 1 (by decide)
      simp only [PathTuple.verticesOf, Set.disjoint_iff] at hdisj
      exact hdisj ⟨hv0, hv1⟩
  case left_inv =>
    intro ⟨spt, hspt⟩
    simp only [Subtype.mk.injEq]
    exact SignedPathTuple2.ext' rfl rfl hspt.2.symm
  case right_inv =>
    intro ⟨pt, hpt⟩
    simp only [Subtype.mk.injEq]
    apply PathTuple.ext'
    funext i; fin_cases i <;> rfl

/-- Key lemma: signedNipats2_false has the same ncard as nipatsFromTo ![A, A'] ![B', B] -/
private lemma signedNipats2_false_ncard_eq (A A' B B' : LatticePoint) :
    (signedNipats2_false A A' B B').ncard = (nipatsFromTo (![A, A'] : kVertex 2) ![B', B]).ncard := by
  simp only [Set.ncard]
  congr 1
  apply Set.encard_congr
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  case toFun =>
    intro ⟨spt, hspt⟩
    have hni : ¬spt.isIntersecting := hspt.1
    have htoBB' : spt.toBB' = false := hspt.2
    refine ⟨⟨![spt.path0, spt.path1], ?_⟩, ?_⟩
    · intro i
      fin_cases i
      · convert spt.valid0 using 1; simp [htoBB']
      · convert spt.valid1 using 1; simp [htoBB']
    · simp only [nipatsFromTo, Set.mem_setOf_eq, PathTuple.isNonIntersecting]
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · rw [Set.disjoint_iff]
        intro v ⟨hv0, hv1⟩
        simp only [PathTuple.verticesOf, Set.mem_setOf_eq] at hv0 hv1
        exact hni ⟨v, hv0, hv1⟩
      · rw [Set.disjoint_iff]
        intro v ⟨hv1, hv0⟩
        simp only [PathTuple.verticesOf, Set.mem_setOf_eq] at hv0 hv1
        exact hni ⟨v, hv0, hv1⟩
      · exact (hij rfl).elim
  case invFun =>
    intro ⟨pt, hpt⟩
    simp only [nipatsFromTo, Set.mem_setOf_eq] at hpt
    refine ⟨⟨pt.paths 0, pt.paths 1, false, ?_, ?_⟩, ?_, rfl⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact pt.valid 0
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact pt.valid 1
    · simp only [signedNipats2, Set.mem_setOf_eq, SignedPathTuple2.isIntersecting, not_exists, not_and]
      intro v hv0 hv1
      have hdisj := hpt 0 1 (by decide)
      simp only [PathTuple.verticesOf, Set.disjoint_iff] at hdisj
      exact hdisj ⟨hv0, hv1⟩
  case left_inv =>
    intro ⟨spt, hspt⟩
    simp only [Subtype.mk.injEq]
    exact SignedPathTuple2.ext' rfl rfl hspt.2.symm
  case right_inv =>
    intro ⟨pt, hpt⟩
    simp only [Subtype.mk.injEq]
    apply PathTuple.ext'
    funext i; fin_cases i <;> rfl

/-- The sum over non-intersecting path tuples equals the difference of nipat counts. -/
theorem sum_signedNipats2 (A A' B B' : LatticePoint)
    (hfin : (signedNipats2 A A' B B').Finite) :
    ∑ spt ∈ hfin.toFinset, spt.sign =
      (numNipats2 A A' B B' : ℤ) - numNipats2 A A' B' B := by
  -- Split the sum based on toBB'
  have h_split : ∑ spt ∈ hfin.toFinset, spt.sign =
      ∑ spt ∈ hfin.toFinset.filter (·.toBB' = true), spt.sign +
      ∑ spt ∈ hfin.toFinset.filter (·.toBB' = false), spt.sign := by
    rw [← Finset.sum_filter_add_sum_filter_not (p := fun spt => spt.toBB' = true)]
    congr 1
    apply Finset.sum_congr
    · ext x; simp only [Finset.mem_filter, and_congr_right_iff]
      intro _; cases x.toBB' <;> simp
    · intros; rfl
  rw [h_split]
  -- For toBB' = true, sign = 1
  have h_true : ∑ spt ∈ hfin.toFinset.filter (·.toBB' = true), spt.sign =
      (hfin.toFinset.filter (·.toBB' = true)).card := by
    rw [Finset.sum_eq_card_nsmul (b := (1 : ℤ))]
    · simp
    · intro spt hspt
      simp only [Finset.mem_filter] at hspt
      simp only [SignedPathTuple2.sign, hspt.2, ↓reduceIte]
  -- For toBB' = false, sign = -1
  have h_false : ∑ spt ∈ hfin.toFinset.filter (·.toBB' = false), spt.sign =
      -((hfin.toFinset.filter (·.toBB' = false)).card : ℤ) := by
    rw [Finset.sum_eq_card_nsmul (b := (-1 : ℤ))]
    · simp
    · intro spt hspt
      simp only [Finset.mem_filter] at hspt
      simp only [SignedPathTuple2.sign, hspt.2, Bool.false_eq_true, ↓reduceIte]
  rw [h_true, h_false]
  ring_nf
  -- Relate the filters to signedNipats2_true/false
  have hfin_true : (signedNipats2_true A A' B B').Finite := hfin.subset fun x hx => hx.1
  have hfin_false : (signedNipats2_false A A' B B').Finite := hfin.subset fun x hx => hx.1
  have h_filter_true_eq : hfin.toFinset.filter (·.toBB' = true) = hfin_true.toFinset := by
    ext spt
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedNipats2, signedNipats2_true,
               Set.mem_setOf_eq]
  have h_filter_false_eq : hfin.toFinset.filter (·.toBB' = false) = hfin_false.toFinset := by
    ext spt
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedNipats2, signedNipats2_false,
               Set.mem_setOf_eq]
  rw [h_filter_true_eq, h_filter_false_eq]
  -- Use Set.ncard_eq_toFinset_card
  rw [← Set.ncard_eq_toFinset_card (signedNipats2_true A A' B B') hfin_true]
  rw [← Set.ncard_eq_toFinset_card (signedNipats2_false A A' B B') hfin_false]
  rw [signedNipats2_true_ncard_eq, signedNipats2_false_ncard_eq]
  simp only [numNipats2]

/-- signedPathTuples2 is the union of signedNipats2 and signedIpats2. -/
private lemma signedPathTuples2_eq_union (A A' B B' : LatticePoint) :
    signedPathTuples2 A A' B B' = signedNipats2 A A' B B' ∪ signedIpats2 A A' B B' := by
  ext spt
  simp only [signedPathTuples2, signedNipats2, signedIpats2, Set.mem_univ, Set.mem_union,
             Set.mem_setOf_eq, true_iff]
  tauto

/-- signedNipats2 and signedIpats2 are disjoint. -/
private lemma signedNipats2_disjoint_signedIpats2 (A A' B B' : LatticePoint) :
    Disjoint (signedNipats2 A A' B B') (signedIpats2 A A' B B') := by
  rw [Set.disjoint_iff]
  intro spt ⟨hni, hi⟩
  simp only [signedNipats2, signedIpats2, Set.mem_setOf_eq] at hni hi
  exact hni hi

/-- Sum over all = sum over nipats + sum over ipats.
    This is proved by showing the partition property at the Set.Finite level. -/
private lemma sum_partition (A A' B B' : LatticePoint) :
    let hfin_all := signedPathTuples2_finite A A' B B'
    let hfin_ni := signedNipats2_finite A A' B B'
    let hfin_i := signedIpats2_finite A A' B B'
    ∑ spt ∈ hfin_all.toFinset, spt.sign =
      ∑ spt ∈ hfin_ni.toFinset, spt.sign + ∑ spt ∈ hfin_i.toFinset, spt.sign := by
  classical
  intro hfin_all hfin_ni hfin_i
  -- Use Finset.sum_filter_add_sum_filter_not to split the sum
  have h_sum : ∑ spt ∈ hfin_all.toFinset, spt.sign =
      ∑ spt ∈ hfin_all.toFinset.filter (· ∈ hfin_ni.toFinset), spt.sign +
      ∑ spt ∈ hfin_all.toFinset.filter (· ∉ hfin_ni.toFinset), spt.sign := by
    rw [← Finset.sum_filter_add_sum_filter_not hfin_all.toFinset (· ∈ hfin_ni.toFinset)]
  rw [h_sum]
  congr 1
  · -- Show filter equals hfin_ni.toFinset
    apply Finset.sum_congr
    · ext spt
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedPathTuples2, Set.mem_univ,
                 true_and, signedNipats2, Set.mem_setOf_eq]
    · intros; rfl
  · -- Show filter of complement equals hfin_i.toFinset
    apply Finset.sum_congr
    · ext spt
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, signedPathTuples2, signedNipats2,
                 signedIpats2, Set.mem_univ, Set.mem_setOf_eq, true_and, not_not]
    · intros; rfl

/-- The LGV lemma for two paths.
    (Proposition prop.lgv.2paths.count)
    Label: prop.lgv.2paths.count

    The proof uses a sign-reversing involution on intersecting path tuples:
    1. Expand the determinant: det(M) = #paths(A→B)·#paths(A'→B') - #paths(A→B')·#paths(A'→B)
    2. By product rule, this equals #pathTuples(→(B,B')) - #pathTuples(→(B',B))
    3. Define signed path tuples with sign +1 for (B,B') and -1 for (B',B)
    4. The involution exchanges tails at the first intersection, flipping the sign
    5. By Lemma lem.sign.cancel2, ipats cancel, leaving only nipats -/
theorem lgv_two_paths (A A' B B' : LatticePoint) :
    (pathMatrix2 A A' B B').det =
      numNipats2 A A' B B' - numNipats2 A A' B' B := by
  -- Step 1: Expand the determinant
  rw [pathMatrix2_det]
  -- det = #paths(A→B) * #paths(A'→B') - #paths(A→B') * #paths(A'→B)

  -- Step 2: Get finiteness hypotheses
  have hfin_all := signedPathTuples2_finite A A' B B'
  have hfin_ni := signedNipats2_finite A A' B B'
  have hfin_i := signedIpats2_finite A A' B B'

  -- Step 3: Apply the key lemmas
  have h_all := sum_signedPathTuples2 A A' B B' hfin_all
  have h_ni := sum_signedNipats2 A A' B B' hfin_ni
  have h_i := sum_signedIpats2_eq_zero A A' B B' hfin_i
  have h_partition := sum_partition A A' B B'

  -- Step 4: Chain of equalities
  -- LHS = sum over all (by sum_signedPathTuples2)
  --     = sum over nipats + sum over ipats (by partition)
  --     = sum over nipats + 0 (by sum_signedIpats2_eq_zero)
  --     = RHS (by sum_signedNipats2)
  calc (numPaths A B : ℤ) * numPaths A' B' - (numPaths A B' : ℤ) * numPaths A' B
      = ∑ spt ∈ hfin_all.toFinset, spt.sign := h_all.symm
    _ = ∑ spt ∈ hfin_ni.toFinset, spt.sign + ∑ spt ∈ hfin_i.toFinset, spt.sign := h_partition
    _ = ∑ spt ∈ hfin_ni.toFinset, spt.sign + 0 := by rw [h_i]
    _ = ∑ spt ∈ hfin_ni.toFinset, spt.sign := by ring
    _ = (numNipats2 A A' B B' : ℤ) - numNipats2 A A' B' B := h_ni

/-!
## Baby Jordan Curve Theorem (Proposition prop.lgv.jordan-2)

If A' is weakly northwest of A, and B' is weakly northwest of B,
then any path from A to B' must intersect any path from A' to B.

This means:
- x(A') ≤ x(A) and y(A') ≥ y(A)
- x(B') ≤ x(B) and y(B') ≥ y(B)

Under these conditions, #nipats from (A,A') to (B',B) = 0.
-/

/-- Point p is weakly northwest of point q. -/
def isWeaklyNorthwestOf (p q : LatticePoint) : Prop :=
  p.x ≤ q.x ∧ p.y ≥ q.y

/-- Helper: If a path exists from a to b, then a.1 ≤ b.1 and a.2 ≤ b.2. -/
lemma path_coords_nondecreasing (path : LatticePath) (a b : LatticePoint)
    (h : path.isPathFromTo a b) : a.1 ≤ b.1 ∧ a.2 ≤ b.2 := by
  induction path generalizing a with
  | nil =>
    simp only [LatticePath.isPathFromTo, LatticePath.endpoint, List.foldl_nil] at h
    rw [h]; exact ⟨le_refl _, le_refl _⟩
  | cons s rest ih =>
    simp only [LatticePath.isPathFromTo, LatticePath.endpoint, List.foldl_cons] at h
    have ⟨hx, hy⟩ := ih (s.apply a) h
    cases s <;> simp only [LatticeStep.apply] at hx hy <;> constructor <;> omega

/-- Helper: Start vertex is in vertices. -/
lemma start_mem_vertices (path : LatticePath) (start : LatticePoint) :
    start ∈ path.vertices start := by
  unfold LatticePath.vertices
  cases path with
  | nil => simp only [List.scanl_nil, List.tail_cons, List.mem_cons, List.mem_nil_iff, or_false]
  | cons s rest => simp only [List.scanl_cons, List.tail_cons, List.mem_cons, true_or]

/-- Helper: Vertices of a cons path. -/
lemma mem_vertices_cons (s : LatticeStep) (rest : LatticePath) (start : LatticePoint)
    (v : LatticePoint) :
    v ∈ LatticePath.vertices (s :: rest) start ↔
    v = start ∨ v ∈ LatticePath.vertices rest (s.apply start) := by
  unfold LatticePath.vertices
  simp only [List.scanl_cons, List.tail_cons, List.mem_cons]

/-- Helper: Vertices of tail are contained in vertices of full path. -/
lemma vertices_cons_subset (s : LatticeStep) (rest : LatticePath) (start : LatticePoint)
    (v : LatticePoint) :
    v ∈ LatticePath.vertices rest (s.apply start) →
    v ∈ LatticePath.vertices (s :: rest) start := by
  intro hv; rw [mem_vertices_cons]; right; exact hv

/-- Baby Jordan curve theorem: Under NW conditions, paths must intersect.
    (Proposition prop.lgv.jordan-2)
    Label: prop.lgv.jordan-2

    **Proof strategy** (from tex source, Section sec.details.det.comb):

    The proof is by strong induction on ℓ(p) + ℓ(p'), the sum of path lengths.

    **Base case**: If ℓ(p) + ℓ(p') = 0, then both paths are empty, so A = B' and A' = B.
    From the NW conditions:
    - A'.x ≤ A.x = B'.x ≤ B.x = A'.x, so A'.x = A.x
    - A'.y ≥ A.y = B'.y ≥ B.y = A'.y, so A'.y = A.y
    Thus A = A', and A is a common vertex.

    **Induction step**: Assume the theorem holds for smaller path lengths.
    If A = A', then A is a common vertex and we're done.
    Otherwise, since A' is weakly NW of A and A ≠ A', we have either:
    - Case 1: A'.y > A.y (A' strictly north of A)
    - Case 2: A'.x < A.x (A' strictly west of A)

    In Case 1 (A'.y > A.y):
    - Let P be the next vertex after A on path p
    - If the first step of p is north, then P = (A.x, A.y + 1)
    - Since A'.y > A.y and integers, A'.y ≥ A.y + 1 = P.y
    - So A' is still weakly NW of P
    - The rest of p goes from P to B', and p' goes from A' to B
    - By IH (with smaller path length), these paths intersect
    - Any common vertex of (rest of p) and p' is also on p

    - If the first step of p is east, then P = (A.x + 1, A.y)
    - We need to look at the first step of p' and apply IH appropriately

    Case 2 (A'.x < A.x) is symmetric, looking at the first step of p' instead.

    The key insight is that the "river" created by path p from A to B' must be
    crossed by path p' from A' to B, since A' is northwest of A and B' is
    northwest of B.

    Reference: https://math.stackexchange.com/questions/2870640/ -/
theorem baby_jordan_curve (A A' B B' : LatticePoint)
    (hA : isWeaklyNorthwestOf A' A) (hB : isWeaklyNorthwestOf B' B)
    (p : LatticePath) (p' : LatticePath)
    (hp : p.isPathFromTo A B') (hp' : p'.isPathFromTo A' B) :
    ∃ v, v ∈ p.vertices A ∧ v ∈ p'.vertices A' := by
  -- If A = A', we're done immediately
  by_cases hAA' : A = A'
  · use A
    constructor
    · exact start_mem_vertices p A
    · rw [hAA']; exact start_mem_vertices p' A'
  -- Otherwise, A' is strictly NW of A in at least one coordinate
  unfold isWeaklyNorthwestOf LatticePoint.x LatticePoint.y at hA hB
  have hstrict : A'.2 > A.2 ∨ A'.1 < A.1 := by
    by_contra h
    push_neg at h
    have h1 : A'.1 = A.1 := le_antisymm hA.1 h.2
    have h2 : A'.2 = A.2 := le_antisymm h.1 hA.2
    exact hAA' (Prod.ext h1.symm h2.symm)
  cases hstrict with
  | inl hAy =>
    -- A'.y > A.y: A' is strictly north of A
    match hp_cases : p with
    | [] =>
      -- p is empty, so A = B'
      unfold LatticePath.isPathFromTo LatticePath.endpoint at hp
      simp only [List.foldl_nil] at hp
      have hp'_coords := path_coords_nondecreasing p' A' B hp'
      -- hB: B'.x ≤ B.x and B'.y ≥ B.y, with B' = A
      -- So A.x ≤ B.x and A.y ≥ B.y
      -- From path: A'.y ≤ B.y
      -- Combined: A'.y > A.y ≥ B.y ≥ A'.y, contradiction
      rw [← hp] at hB
      have : A'.2 ≤ B.2 := hp'_coords.2
      have : B.2 ≤ A.2 := hB.2
      omega
    | s :: rest =>
      -- First step of p
      match s with
      | .north =>
        let P := LatticeStep.north.apply A
        have hrest : LatticePath.isPathFromTo rest P B' := by
          unfold LatticePath.isPathFromTo LatticePath.endpoint at hp ⊢
          simp only [List.foldl_cons] at hp
          exact hp
        have hA'P : isWeaklyNorthwestOf A' P := by
          unfold isWeaklyNorthwestOf LatticePoint.x LatticePoint.y
          simp only [LatticeStep.apply, P]
          exact ⟨hA.1, by omega⟩
        have hBP : isWeaklyNorthwestOf B' B := by
          unfold isWeaklyNorthwestOf LatticePoint.x LatticePoint.y
          exact ⟨hB.1, hB.2⟩
        have := baby_jordan_curve P A' B B' hA'P hBP rest p' hrest hp'
        obtain ⟨v, hv1, hv2⟩ := this
        use v
        exact ⟨vertices_cons_subset LatticeStep.north rest A v hv1, hv2⟩
      | .east =>
        let P := LatticeStep.east.apply A
        have hA'P : isWeaklyNorthwestOf A' P := by
          unfold isWeaklyNorthwestOf LatticePoint.x LatticePoint.y
          simp only [LatticeStep.apply, P]
          exact ⟨by omega, by omega⟩
        have hrest : LatticePath.isPathFromTo rest P B' := by
          unfold LatticePath.isPathFromTo LatticePath.endpoint at hp ⊢
          simp only [List.foldl_cons] at hp
          exact hp
        have hBP : isWeaklyNorthwestOf B' B := by
          unfold isWeaklyNorthwestOf LatticePoint.x LatticePoint.y
          exact ⟨hB.1, hB.2⟩
        have := baby_jordan_curve P A' B B' hA'P hBP rest p' hrest hp'
        obtain ⟨v, hv1, hv2⟩ := this
        use v
        exact ⟨vertices_cons_subset LatticeStep.east rest A v hv1, hv2⟩
  | inr hAx =>
    -- A'.x < A.x: A' is strictly west of A
    match hp'_cases : p' with
    | [] =>
      -- p' is empty, so A' = B
      unfold LatticePath.isPathFromTo LatticePath.endpoint at hp'
      simp only [List.foldl_nil] at hp'
      have hp_coords := path_coords_nondecreasing p A B' hp
      -- hB: B'.x ≤ B.x and B'.y ≥ B.y, with B = A'
      -- So B'.x ≤ A'.x and B'.y ≥ A'.y
      -- From path: A.x ≤ B'.x
      -- Combined: A.x ≤ B'.x ≤ A'.x < A.x, contradiction
      rw [← hp'] at hB
      have : A.1 ≤ B'.1 := hp_coords.1
      have : B'.1 ≤ A'.1 := hB.1
      omega
    | s' :: rest' =>
      match s' with
      | .east =>
        let P' := LatticeStep.east.apply A'
        have hP'A : isWeaklyNorthwestOf P' A := by
          unfold isWeaklyNorthwestOf LatticePoint.x LatticePoint.y
          simp only [LatticeStep.apply, P']
          exact ⟨by omega, hA.2⟩
        have hrest' : LatticePath.isPathFromTo rest' P' B := by
          unfold LatticePath.isPathFromTo LatticePath.endpoint at hp' ⊢
          simp only [List.foldl_cons] at hp'
          exact hp'
        have hBP' : isWeaklyNorthwestOf B' B := by
          unfold isWeaklyNorthwestOf LatticePoint.x LatticePoint.y
          exact ⟨hB.1, hB.2⟩
        have := baby_jordan_curve A P' B B' hP'A hBP' p rest' hp hrest'
        obtain ⟨v, hv1, hv2⟩ := this
        use v
        exact ⟨hv1, vertices_cons_subset LatticeStep.east rest' A' v hv2⟩
      | .north =>
        let P' := LatticeStep.north.apply A'
        have hP'A : isWeaklyNorthwestOf P' A := by
          unfold isWeaklyNorthwestOf LatticePoint.x LatticePoint.y
          simp only [LatticeStep.apply, P']
          exact ⟨by omega, by omega⟩
        have hrest' : LatticePath.isPathFromTo rest' P' B := by
          unfold LatticePath.isPathFromTo LatticePath.endpoint at hp' ⊢
          simp only [List.foldl_cons] at hp'
          exact hp'
        have hBP' : isWeaklyNorthwestOf B' B := by
          unfold isWeaklyNorthwestOf LatticePoint.x LatticePoint.y
          exact ⟨hB.1, hB.2⟩
        have := baby_jordan_curve A P' B B' hP'A hBP' p rest' hp hrest'
        obtain ⟨v, hv1, hv2⟩ := this
        use v
        exact ⟨hv1, vertices_cons_subset LatticeStep.north rest' A' v hv2⟩
termination_by p.length + p'.length

/-- Under NW conditions, there are no nipats from (A,A') to (B',B).
    Label: prop.lgv.jordan-2 -/
theorem no_nipats_under_nw (A A' B B' : LatticePoint)
    (hA : isWeaklyNorthwestOf A' A) (hB : isWeaklyNorthwestOf B' B) :
    numNipats2 A A' B' B = 0 := by
  -- numNipats2 A A' B' B counts nipats from ![A, A'] to ![B', B]
  -- That means path 0: A → B', path 1: A' → B
  -- By baby_jordan_curve, these paths must intersect
  -- So there are no non-intersecting path tuples
  simp only [numNipats2]
  -- Show the set is empty, then use ncard_empty
  suffices h : nipatsFromTo ![A, A'] ![B', B] = ∅ by
    rw [h, Set.ncard_empty]
  ext pt
  simp only [nipatsFromTo, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hni
  -- pt is a path tuple from ![A, A'] to ![B', B]
  -- path 0 goes from A to B', path 1 goes from A' to B
  have h0 := pt.valid 0
  have h1 := pt.valid 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  -- By baby_jordan_curve, these paths intersect
  obtain ⟨v, hv0, hv1⟩ := baby_jordan_curve A A' B B' hA hB (pt.paths 0) (pt.paths 1) h0 h1
  -- But hni says the paths are disjoint
  have hdisj := hni 0 1 (by decide)
  rw [Set.disjoint_iff] at hdisj
  exact hdisj ⟨hv0, hv1⟩

/-!
## Log-Concavity of Binomial Coefficients (Corollary cor.lgv.binom-unimod)

As an application of the LGV lemma:
C(n,k)² ≥ C(n,k-1) · C(n,k+1)

This follows by choosing appropriate lattice points and applying
Propositions prop.lgv.2paths.count and prop.lgv.jordan-2.
-/

/-- Binomial coefficients are log-concave at positive indices.

    Proof sketch (algebraic): Using the recurrences
    - C(n, k+1) · (k+1) = C(n, k) · (n-k)
    - C(n, k) · k = C(n, k-1) · (n-k+1)
    we can show that C(n,k)² / (C(n,k-1) · C(n,k+1)) = (k+1)(n-k+1) / (k(n-k)).
    This ratio is ≥ 1 because (k+1)(n-k+1) - k(n-k) = n + 1 ≥ 0.

    Combinatorial proof (via LGV): Define lattice points A=(1,0), A'=(0,1),
    B=(k+1, n-k), B'=(k, n-k+1). Then det(path matrix) = #nipats ≥ 0. -/
theorem binom_log_concave_of_pos (n k : ℕ) (hk : 1 ≤ k) :
    n.choose k * n.choose k ≥ n.choose (k - 1) * n.choose (k + 1) := by
  by_cases hkn : n < k
  · -- k > n: C(n,k) = 0, so LHS = 0. Also C(n,k+1) = 0.
    have h1 : n.choose k = 0 := Nat.choose_eq_zero_of_lt hkn
    have h2 : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_add_right 1 hkn)
    simp [h1, h2]
  · push_neg at hkn
    -- Main case: 1 ≤ k ≤ n
    have hk_pos : 0 < k := hk

    -- Key recurrences from Mathlib:
    -- C(n, k+1) * (k+1) = C(n, k) * (n-k)
    have rec_up : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) :=
      Nat.choose_succ_right_eq n k
    -- C(n, k) * k = C(n, k-1) * (n - (k-1))
    have rec_down : n.choose k * k = n.choose (k - 1) * (n - (k - 1)) := by
      have h := Nat.choose_succ_right_eq n (k - 1)
      simp only [Nat.sub_add_cancel hk_pos] at h
      exact h

    -- Multiply both sides by k * (k+1) > 0, then show inequality
    suffices h : n.choose k * n.choose k * (k * (k + 1)) ≥
                 n.choose (k - 1) * n.choose (k + 1) * (k * (k + 1)) by
      have hpos : 0 < k * (k + 1) := Nat.mul_pos hk_pos (Nat.succ_pos k)
      exact Nat.le_of_mul_le_mul_right h hpos

    -- Rewrite LHS using rec_down
    have lhs_eq : n.choose k * n.choose k * (k * (k + 1)) =
                  n.choose (k - 1) * (n - (k - 1)) * n.choose k * (k + 1) := by
      calc n.choose k * n.choose k * (k * (k + 1))
          = (n.choose k * k) * (n.choose k * (k + 1)) := by ring
        _ = (n.choose (k - 1) * (n - (k - 1))) * (n.choose k * (k + 1)) := by rw [rec_down]
        _ = n.choose (k - 1) * (n - (k - 1)) * n.choose k * (k + 1) := by ring

    -- Rewrite RHS using rec_up
    have rhs_eq : n.choose (k - 1) * n.choose (k + 1) * (k * (k + 1)) =
                  n.choose (k - 1) * n.choose k * (n - k) * k := by
      calc n.choose (k - 1) * n.choose (k + 1) * (k * (k + 1))
          = n.choose (k - 1) * (n.choose (k + 1) * (k + 1)) * k := by ring
        _ = n.choose (k - 1) * (n.choose k * (n - k)) * k := by rw [rec_up]
        _ = n.choose (k - 1) * n.choose k * (n - k) * k := by ring

    rw [lhs_eq, rhs_eq]
    -- Now need: C(n,k-1) * (n-k+1) * C(n,k) * (k+1) ≥ C(n,k-1) * C(n,k) * (n-k) * k
    -- i.e., (n-k+1) * (k+1) ≥ (n-k) * k (when the common factor is nonzero)

    by_cases hzero : n.choose (k - 1) * n.choose k = 0
    · simp [hzero]
    · -- The key algebraic inequality: (n - (k-1)) * (k+1) ≥ (n - k) * k
      have key : (n - (k - 1)) * (k + 1) ≥ (n - k) * k := by
        have h1 : n - (k - 1) = n - k + 1 := by omega
        rw [h1]
        -- (n - k + 1) * (k + 1) ≥ (n - k) * k
        -- Expand: (n-k)(k+1) + (k+1) = (n-k)k + (n-k) + k + 1
        -- vs: (n-k)k
        -- Difference: n - k + k + 1 = n + 1 ≥ 0
        nlinarith
      -- Apply the key inequality
      have h1 : n.choose (k - 1) * (n - (k - 1)) * n.choose k * (k + 1) =
                n.choose (k - 1) * n.choose k * ((n - (k - 1)) * (k + 1)) := by ring
      have h2 : n.choose (k - 1) * n.choose k * (n - k) * k =
                n.choose (k - 1) * n.choose k * ((n - k) * k) := by ring
      rw [h1, h2]
      exact Nat.mul_le_mul_left (n.choose (k - 1) * n.choose k) key

/-- Binomial coefficients are log-concave.
    (Corollary cor.lgv.binom-unimod)
    Label: cor.lgv.binom-unimod

    The conditional implements the standard convention `C(n, -1) = 0`, which is
    needed at `k = 0` because subtraction on natural numbers is truncated. -/
theorem binom_log_concave (n k : ℕ) :
    n.choose k * n.choose k ≥
      (if k = 0 then 0 else n.choose (k - 1)) * n.choose (k + 1) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    exact binom_log_concave_of_pos n k (Nat.one_le_iff_ne_zero.mpr hk)

/-!
## The LGV Lemma for k Paths (Proposition prop.lgv.kpaths.count)

For k-vertices A = (A₁, ..., Aₖ) and B = (B₁, ..., Bₖ):

det(#paths from Aᵢ to Bⱼ)_{i,j} = ∑_{σ ∈ Sₖ} (-1)^σ · #nipats from A to σ(B)

The proof generalizes the k=2 case by using a sign-reversing involution
that picks the first pair of intersecting paths and exchanges their tails.
-/

/-! ### Helper lemmas for the product rule -/

/-- Product of ncards equals ncard of pi type.
    This is the key lemma for proving the product rule. -/
private lemma ncard_pi_eq_prod {α : Type*} [DecidableEq α] [Fintype α] {ι : α → Type*}
    [∀ i, DecidableEq (ι i)]
    {s : ∀ i : α, Set (ι i)} (hfin : ∀ i, (s i).Finite) :
    (Set.pi Set.univ s).ncard = ∏ i, (s i).ncard := by
  have hfin_pi : (Set.pi Set.univ s).Finite := Set.Finite.pi hfin
  rw [Set.ncard_eq_toFinset_card _ hfin_pi]
  haveI inst_i : ∀ i, Fintype (s i) := fun i => (hfin i).fintype
  haveI inst_set : Fintype (Set.pi Set.univ s) := hfin_pi.fintype
  have h1 : hfin_pi.toFinset.card = Fintype.card (Set.pi Set.univ s) := by
    rw [Set.toFinite_toFinset, Set.toFinset_card]
  rw [h1]
  rw [Fintype.card_congr (Equiv.Set.univPi s)]
  rw [Fintype.card_pi]
  congr 1
  funext i
  rw [Set.ncard_eq_toFinset_card _ (hfin i)]
  rw [Set.toFinite_toFinset, Set.toFinset_card]

/-- Equivalence between PathTuple and subtype of functions. -/
private def PathTuple.equivSubtype {k : ℕ} (A B : kVertex k) :
    PathTuple k A B ≃ { f : Fin k → LatticePath // ∀ i, f i ∈ pathsFromTo (A i) (B i) } where
  toFun pt := ⟨pt.paths, pt.valid⟩
  invFun sf := ⟨sf.val, sf.property⟩
  left_inv pt := by cases pt; rfl
  right_inv sf := by cases sf; rfl

/-- Helper: Nat.card of subtype equals ncard of set. -/
private lemma Nat.card_subtype_eq_ncard {α : Type*} (s : Set α) (hs : s.Finite) :
    Nat.card { x // x ∈ s } = s.ncard := by
  rw [Set.ncard_eq_toFinset_card _ hs]
  haveI : Fintype s := hs.fintype
  rw [Nat.card_eq_fintype_card]
  rw [Set.toFinite_toFinset]
  rw [← Set.toFinset_card]

/-- The ncard of pathTuplesFromTo equals the product of ncards of pathsFromTo.
    This is the "product rule" for path tuples. -/
theorem pathTuplesFromTo_ncard_eq_prod {k : ℕ} (A B : kVertex k) :
    (pathTuplesFromTo A B).ncard = ∏ i, (pathsFromTo (A i) (B i)).ncard := by
  -- Step 1: ncard(Set.univ) = Nat.card (PathTuple k A B) when finite
  have hfin := pathTuplesFromTo_finite A B
  have h1 : (pathTuplesFromTo A B).ncard = Nat.card (PathTuple k A B) := by
    rw [pathTuplesFromTo, Set.ncard_univ]
  rw [h1]

  -- Step 2: Use the equivalence to the subtype
  have h_equiv := PathTuple.equivSubtype A B
  have h2 : Nat.card (PathTuple k A B) =
            Nat.card { f : Fin k → LatticePath // ∀ i, f i ∈ pathsFromTo (A i) (B i) } :=
    Nat.card_congr h_equiv
  rw [h2]

  -- Step 3: The subtype { f // ∀ i, f i ∈ s i } equals the pi set
  have hset_eq : { f : Fin k → LatticePath | ∀ i, f i ∈ pathsFromTo (A i) (B i) } =
                 Set.pi Set.univ (fun i => pathsFromTo (A i) (B i)) := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]

  have hfin_pi : (Set.pi Set.univ (fun i => pathsFromTo (A i) (B i))).Finite :=
    Set.Finite.pi (fun i => pathsFromTo_finite (A i) (B i))

  -- Step 4: Nat.card of subtype = ncard of set
  have h3 : Nat.card { f : Fin k → LatticePath // ∀ i, f i ∈ pathsFromTo (A i) (B i) } =
            (Set.pi Set.univ (fun i => pathsFromTo (A i) (B i))).ncard := by
    rw [← hset_eq]
    have hfin_sub : { f : Fin k → LatticePath | ∀ i, f i ∈ pathsFromTo (A i) (B i) }.Finite := by
      rw [hset_eq]; exact hfin_pi
    exact Nat.card_subtype_eq_ncard _ hfin_sub
  rw [h3]

  -- Step 5: Apply ncard_pi_eq_prod
  exact ncard_pi_eq_prod (fun i => pathsFromTo_finite (A i) (B i))

/-- numPaths equals ncard of pathsFromTo. -/
private lemma numPaths_eq_ncard (a b : LatticePoint) :
    numPaths a b = (pathsFromTo a b).ncard := by
  have hfin := pathsFromTo_finite a b
  rw [numPaths_eq_card a b hfin]
  rw [Set.ncard_eq_toFinset_card _ hfin]

/-- The product of numPaths equals the ncard of pathTuplesFromTo. -/
theorem prod_numPaths_eq_pathTuples_ncard {k : ℕ} (A B : kVertex k) :
    ∏ i, numPaths (A i) (B i) = (pathTuplesFromTo A B).ncard := by
  rw [pathTuplesFromTo_ncard_eq_prod]
  congr 1
  funext i
  exact numPaths_eq_ncard (A i) (B i)

/-- The path count matrix for k source and target vertices. -/
def pathMatrixK {k : ℕ} (A B : kVertex k) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j => numPaths (A i) (B j)

/-- Number of nipats from A to σ(B).
    Defined as the cardinality of the set of non-intersecting path tuples. -/
noncomputable def numNipatsK {k : ℕ} (A B : kVertex k) (σ : Equiv.Perm (Fin k)) : ℕ :=
  (nipatsFromTo A (B.permute σ)).ncard

/-- Number of ipats from A to σ(B).
    Defined as the cardinality of the set of intersecting path tuples. -/
noncomputable def numIpatsK {k : ℕ} (A B : kVertex k) (σ : Equiv.Perm (Fin k)) : ℕ :=
  (ipatsFromTo A (B.permute σ)).ncard

/-!
### Bridge to LGV2.lean

We establish the connection between LGV1's path representation and LGV2's.
The key observation is that both represent the same mathematical objects.

The bridge uses the following chain of equivalences:
1. LGV1.LatticeStep ≃ LGV.LatticeStep' (both are {east, north})
2. LGV1.LatticePath ≃ LGV.LatticePath' (both are lists of steps)
3. LGV1.PathTuple k A B ≃ LGV.LatticePath'Tuple k A B (same structure)
4. LGV.LatticePath'Tuple k A B ≃ LGV.PathTuple integerLattice k A B (via latticePath'TupleEquiv)

The intersection property is preserved at each step, so:
- ipatsFromTo A B ≃ ipatSet integerLattice A B
- numIpatsK A B σ = (ipatFinset ... A (permuteKVertex σ B)).card
-/

/-- Equivalence between `LGV1.LatticeStep` and `LGV.LatticeStep'`.
    
    This is a definitional equivalence: both types have the same structure
    (two constructors `east` and `north`), so the equivalence is trivial.
    The equivalence preserves the `apply` function: `latticeStepEquiv_apply`. -/
def latticeStepEquiv : LatticeStep ≃ LGV.LatticeStep' where
  toFun s := match s with
    | LatticeStep.east => LGV.LatticeStep'.east
    | LatticeStep.north => LGV.LatticeStep'.north
  invFun s := match s with
    | LGV.LatticeStep'.east => LatticeStep.east
    | LGV.LatticeStep'.north => LatticeStep.north
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

/-- The step equivalence preserves the apply function -/
theorem latticeStepEquiv_apply (s : LatticeStep) (p : LatticePoint) :
    (latticeStepEquiv s).apply p = s.apply p := by
  cases s <;> rfl

/-- Map a LatticePath to a LatticePath' -/
def latticePathToLatticePath' (path : LatticePath) : LGV.LatticePath' :=
  path.map latticeStepEquiv

/-- Map a LatticePath' to a LatticePath -/
def latticePath'ToLatticePath (path : LGV.LatticePath') : LatticePath :=
  path.map latticeStepEquiv.symm

/-- The path mapping preserves endpoints -/
theorem latticePathToLatticePath'_endpoint (path : LatticePath) (start : LatticePoint) :
    LGV.LatticePath'.endpoint (latticePathToLatticePath' path) start = path.endpoint start := by
  induction path generalizing start with
  | nil => rfl
  | cons s rest ih =>
    simp only [latticePathToLatticePath', List.map, LatticePath.endpoint, LGV.LatticePath'.endpoint,
      List.foldl_cons, latticeStepEquiv_apply]
    exact ih (s.apply start)

/-- Helper: scanl with mapped function equals toVertices -/
private theorem map_scanl_eq_toVertices (path : LatticePath) (start : LatticePoint) :
    (path.map latticeStepEquiv).scanl (fun p s => s.apply p) start =
    LGV.LatticePath'.toVertices (path.map latticeStepEquiv) start := by
  induction path generalizing start with
  | nil =>
    simp only [List.map_nil, List.scanl_nil, LGV.LatticePath'.toVertices]
  | cons s rest ih =>
    simp only [List.map_cons, List.scanl_cons, LGV.LatticePath'.toVertices]
    congr 1
    exact ih ((latticeStepEquiv s).apply start)

/-- The path mapping preserves vertices -/
theorem latticePathToLatticePath'_toVertices (path : LatticePath) (start : LatticePoint) :
    LGV.LatticePath'.toVertices (latticePathToLatticePath' path) start = path.vertices start := by
  -- Both compute the same list of vertices, just with different implementations
  -- LGV1 uses scanl while LGV2 uses recursion, but they're equivalent
  unfold latticePathToLatticePath'
  rw [← map_scanl_eq_toVertices]
  rw [vertices_eq_scanl]
  -- Now show: (path.map latticeStepEquiv).scanl ... = path.scanl ...
  -- This follows from latticeStepEquiv preserving apply
  induction path generalizing start with
  | nil => simp [List.scanl_nil]
  | cons s rest ih =>
    simp only [List.map_cons, List.scanl_cons]
    rw [latticeStepEquiv_apply]
    congr 1
    exact ih (s.apply start)

/-- The permutation functions are equal -/
theorem permute_eq_permuteKVertex {k : ℕ} (B : kVertex k) (σ : Equiv.Perm (Fin k)) :
    B.permute σ = LGV.permuteKVertex σ B := rfl

/-- Convert a PathTuple to a LatticePath'Tuple.
    This is part of the key bridge lemma: numIpatsK equals ipatFinset.card.
    The chain of bijections is:
    - LGV1.PathTuple ≃ LGV.LatticePath'Tuple (via step equivalence)
    - LGV.LatticePath'Tuple ≃ LGV.PathTuple integerLattice (via latticePath'TupleEquiv)
    The intersection property is preserved at each step. -/
private def pathTupleToLatticePath'Tuple {k : ℕ} {A B : kVertex k} 
    (pt : PathTuple k A B) : LGV.LatticePath'Tuple k A B where
  paths := fun i => latticePathToLatticePath' (pt.paths i)
  valid := fun i => by
    simp only [latticePathToLatticePath'_endpoint]
    exact pt.valid i

/-- Helper: latticeStepEquiv.symm preserves apply -/
private theorem latticeStepEquiv_symm_apply (s : LGV.LatticeStep') (p : LatticePoint) :
    (latticeStepEquiv.symm s).apply p = s.apply p := by
  cases s <;> rfl

/-- Convert a LatticePath'Tuple to a PathTuple -/
private def latticePath'TupleToPathTuple {k : ℕ} {A B : kVertex k}
    (pt : LGV.LatticePath'Tuple k A B) : PathTuple k A B where
  paths := fun i => latticePath'ToLatticePath (pt.paths i)
  valid := fun i => by
    simp only [LatticePath.isPathFromTo]
    have h := pt.valid i
    simp only [latticePath'ToLatticePath, LatticePath.endpoint, LGV.LatticePath'.endpoint] at h ⊢
    -- Show that mapping through latticeStepEquiv.symm preserves the endpoint
    have key : ∀ (path : LGV.LatticePath') (start : LatticePoint),
        List.foldl (fun p s => s.apply p) start (path.map latticeStepEquiv.symm) = 
        List.foldl (fun p s => s.apply p) start path := by
      intro path start
      induction path generalizing start with
      | nil => rfl
      | cons s rest ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [latticeStepEquiv_symm_apply]
        exact ih (s.apply start)
    rw [key]
    exact h

/-- The two conversions are inverses -/
private theorem pathTuple_latticePath'Tuple_left_inv {k : ℕ} {A B : kVertex k}
    (pt : PathTuple k A B) : latticePath'TupleToPathTuple (pathTupleToLatticePath'Tuple pt) = pt := by
  cases pt
  unfold latticePath'TupleToPathTuple pathTupleToLatticePath'Tuple 
         latticePath'ToLatticePath latticePathToLatticePath'
  simp only [PathTuple.mk.injEq]
  funext i
  simp only [List.map_map]
  conv_lhs => rw [show (latticeStepEquiv.symm ∘ latticeStepEquiv) = id from funext (fun _ => Equiv.symm_apply_apply _ _)]
  simp only [List.map_id]

private theorem pathTuple_latticePath'Tuple_right_inv {k : ℕ} {A B : kVertex k}
    (pt : LGV.LatticePath'Tuple k A B) : pathTupleToLatticePath'Tuple (latticePath'TupleToPathTuple pt) = pt := by
  apply LGV.LatticePath'Tuple.ext
  intro i
  unfold pathTupleToLatticePath'Tuple latticePath'TupleToPathTuple
         latticePathToLatticePath' latticePath'ToLatticePath
  simp only [List.map_map]
  conv_lhs => rw [show (latticeStepEquiv ∘ latticeStepEquiv.symm) = id from funext (fun _ => Equiv.apply_symm_apply _ _)]
  simp only [List.map_id]

/-- Equivalence between LGV1.PathTuple and LGV.LatticePath'Tuple -/
private noncomputable def pathTupleEquivLatticePath'Tuple {k : ℕ} (A B : kVertex k) :
    PathTuple k A B ≃ LGV.LatticePath'Tuple k A B where
  toFun := pathTupleToLatticePath'Tuple
  invFun := latticePath'TupleToPathTuple
  left_inv := pathTuple_latticePath'Tuple_left_inv
  right_inv := pathTuple_latticePath'Tuple_right_inv

/-- The vertices of a PathTuple match those of the converted LatticePath'Tuple -/
private theorem pathTupleToLatticePath'Tuple_verticesOf {k : ℕ} {A B : kVertex k}
    (pt : PathTuple k A B) (i : Fin k) :
    (pathTupleToLatticePath'Tuple pt).verticesOf i = pt.verticesOf i := by
  ext v
  simp only [LGV.LatticePath'Tuple.verticesOf, PathTuple.verticesOf, Set.mem_setOf_eq]
  simp only [pathTupleToLatticePath'Tuple, latticePathToLatticePath'_toVertices]

/-- The intersection property is preserved by the equivalence -/
private theorem pathTuple_isIntersecting_iff_latticePath'Tuple {k : ℕ} {A B : kVertex k}
    (pt : PathTuple k A B) :
    pt.isIntersecting ↔ (pathTupleToLatticePath'Tuple pt).isIntersecting := by
  unfold PathTuple.isIntersecting PathTuple.isNonIntersecting
  unfold LGV.LatticePath'Tuple.isIntersecting LGV.LatticePath'Tuple.isNonIntersecting
  simp only [not_forall]
  constructor
  · intro ⟨i, j, hij, hnotdisj⟩
    use i, j, hij
    rw [pathTupleToLatticePath'Tuple_verticesOf, pathTupleToLatticePath'Tuple_verticesOf]
    exact hnotdisj
  · intro ⟨i, j, hij, hnotdisj⟩
    use i, j, hij
    rw [pathTupleToLatticePath'Tuple_verticesOf, pathTupleToLatticePath'Tuple_verticesOf] at hnotdisj
    exact hnotdisj

/-- Full equivalence between LGV1.PathTuple and LGV.PathTuple integerLattice -/
private noncomputable def pathTupleEquivLGVPathTuple {k : ℕ} (A B : kVertex k) :
    PathTuple k A B ≃ LGV.PathTuple LGV.integerLattice k A B :=
  (pathTupleEquivLatticePath'Tuple A B).trans (LGV.latticePath'TupleEquiv A B)

/-- The intersection property is preserved by the full equivalence -/
private theorem pathTuple_isIntersecting_iff_LGVPathTuple {k : ℕ} {A B : kVertex k}
    (pt : PathTuple k A B) :
    pt.isIntersecting ↔ (pathTupleEquivLGVPathTuple A B pt).isIntersecting := by
  rw [pathTuple_isIntersecting_iff_latticePath'Tuple]
  exact LGV.latticePath'Tuple_isIntersecting_iff _

theorem numIpatsK_eq_ipatFinset_card {k : ℕ} (A B : kVertex k) (σ : Equiv.Perm (Fin k)) :
    numIpatsK A B σ = (LGV.ipatFinset LGV.integerLattice_pathFinite A (LGV.permuteKVertex σ B)).card := by
  -- Unfold definitions
  unfold numIpatsK
  rw [← permute_eq_permuteKVertex]
  set B' := B.permute σ
  -- The key is to build a bijection between ipatsFromTo A B' and ipatFinset ... A B'
  -- ipatsFromTo A B' = { pt : PathTuple k A B' | pt.isIntersecting }
  -- ipatFinset ... A B' = (ipatSetFinite ...).toFinset where ipatSet = { pt | pt.isIntersecting }
  
  -- Build the equivalence between the intersecting sets
  let e := pathTupleEquivLGVPathTuple A B'
  have h_prop : ∀ pt, pt.isIntersecting ↔ (e pt).isIntersecting := 
    pathTuple_isIntersecting_iff_LGVPathTuple
  
  -- Build equivalence on subsets with isIntersecting property
  have h_equiv : ipatsFromTo A B' ≃ LGV.ipatSet (D := LGV.integerLattice) A B' := by
    refine Equiv.subtypeEquiv e ?_
    exact h_prop
  
  -- Now use that ncard equals card for equivalent finite sets
  have h_fin : (ipatsFromTo A B').Finite := ipatsFromTo_finite A B'
  rw [Set.ncard_eq_toFinset_card _ h_fin]
  
  -- ipatFinset is the toFinset of ipatSet
  have h_ipatFinset : LGV.ipatFinset LGV.integerLattice_pathFinite A B' = 
      (LGV.ipatSetFinite LGV.integerLattice_pathFinite A B').toFinset := rfl
  rw [h_ipatFinset]
  
  -- Both are finite sets with equivalent elements
  apply Finset.card_eq_of_equiv
  -- h_fin.toFinset ≃ ipatsFromTo A B' ≃ ipatSet ... ≃ ipatSetFinite.toFinset
  have h1 : h_fin.toFinset ≃ ipatsFromTo A B' := 
    Equiv.cast (congrArg (·) h_fin.coeSort_toFinset)
  have h2 : LGV.ipatSet (D := LGV.integerLattice) A B' ≃ 
      (LGV.ipatSetFinite LGV.integerLattice_pathFinite A B').toFinset :=
    Equiv.cast (congrArg (·) (LGV.ipatSetFinite LGV.integerLattice_pathFinite A B').coeSort_toFinset.symm)
  exact h1.trans (h_equiv.trans h2)

/-- Helper: the product in the determinant can be reindexed via σ⁻¹. -/
private lemma det_prod_reindex {k : ℕ} (A B : Fin k → LatticePoint) (σ : Equiv.Perm (Fin k)) :
    ∏ i, (numPaths (A (σ i)) (B i) : ℤ) = ∏ i, (numPaths (A i) (B (σ⁻¹ i)) : ℤ) := by
  conv_lhs => rw [← Equiv.prod_comp σ⁻¹]
  congr 1
  funext j
  congr 2
  exact congrArg A (Equiv.apply_symm_apply σ j)

/-- Helper: summing over σ equals summing over σ⁻¹. -/
private lemma sum_perm_inv {k : ℕ} (f : Equiv.Perm (Fin k) → ℤ) :
    ∑ σ : Equiv.Perm (Fin k), f σ = ∑ σ : Equiv.Perm (Fin k), f σ⁻¹ :=
  Finset.sum_equiv (Equiv.inv _) (by simp) (fun _ _ => rfl)

/-- Helper: sign is preserved under inverse. -/
private lemma sign_inv_eq {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (Equiv.Perm.sign σ⁻¹ : ℤ) = Equiv.Perm.sign σ := by
  simp only [Equiv.Perm.sign_inv]

/-- The determinant equals a sum over path tuples to σ(B).
    This rewrites det(M) = ∑ σ, sign(σ) * ∏ᵢ M(σ i, i) into
    det(M) = ∑ σ, sign(σ) * ∏ᵢ numPaths(A i, B(σ i)). -/
lemma det_eq_sum_path_tuples {k : ℕ} (A B : kVertex k) :
    (pathMatrixK A B).det =
      ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) * (∏ i, (numPaths (A i) (B (σ i)) : ℤ)) := by
  rw [Matrix.det_apply']
  simp only [pathMatrixK, Matrix.of_apply]
  conv_lhs => rw [sum_perm_inv]
  congr 1
  ext σ
  rw [sign_inv_eq]
  congr 1
  rw [det_prod_reindex]
  simp only [inv_inv]

/-- The key combinatorial lemma: intersecting path tuples cancel via sign-reversing involution.

    This encapsulates the main combinatorial content of the LGV lemma:
    1. ∏ᵢ numPaths(A i, B(σ i)) = #path tuples from A to σ(B) (product rule)
    2. Intersecting path tuples cancel via sign-reversing involution
    3. Only non-intersecting path tuples (nipats) survive

    The sign-reversing involution works by:
    - Finding the first crowded point v on the path with smallest index i
    - Finding the largest index j of a path containing v
    - Exchanging tails of paths pᵢ and pⱼ at v
    - Composing σ with the transposition (i,j) to flip the sign

    By Finset.sum_involution, the intersecting path tuples cancel.
    Label: pf.prop.lgv.kpaths.count.involution -/
lemma lgv_involution_cancellation {k : ℕ} (A B : kVertex k) :
    ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) * (∏ i, (numPaths (A i) (B (σ i)) : ℤ)) =
      ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) * (numNipatsK A B σ : ℤ) := by
  /-
  PROOF STRUCTURE:
  
  The proof reduces to two key lemmas:
  1. partition_lemma: ∏_i numPaths(A_i, B_{σ(i)}) = numNipatsK + numIpatsK
  2. ipat_cancellation: ∑_σ sign(σ) * numIpatsK = 0
  
  From these, the result follows by algebra:
    LHS = ∑_σ sign(σ) * (numNipatsK + numIpatsK)
        = ∑_σ sign(σ) * numNipatsK + ∑_σ sign(σ) * numIpatsK
        = ∑_σ sign(σ) * numNipatsK + 0
        = RHS
  
  PROOF OF partition_lemma:
  Step 1: ∏_i numPaths(A_i, B_{σ(i)}) = (pathTuplesFromTo A (B.permute σ)).ncard
    This is the "product rule": the product of path counts equals the count of path tuples.
    Uses numPaths_eq_card (proved) and the bijection between path tuples and products.
  
  Step 2: pathTuplesFromTo = nipatsFromTo ∪ ipatsFromTo (disjoint union)
    This follows from the definitions: every path tuple is either intersecting or not.
  
  Step 3: ncard of disjoint union = sum of ncards
    Uses Set.ncard_union_eq.
  
  PROOF OF ipat_cancellation:
  This uses a sign-reversing involution on pairs (σ, ipat).
  
  The involution f : (σ, ipat) ↦ (σ ∘ t_{i,j}, ipat') where:
  - i is the smallest index with a path containing a "crowded" point
  - v is the first crowded point on path i
  - j > i is the largest index with a path containing v
  - t_{i,j} is the transposition swapping i and j
  - ipat' has tails of paths i and j exchanged at v
  
  Key properties:
  - sign(σ ∘ t_{i,j}) = -sign(σ) (transposition flips sign)
  - f(f(σ, ipat)) = (σ, ipat) (involution)
  - f has no fixed points (every ipat has a crowded point)
  
  By Finset.sum_involution, the sum cancels to zero.
  
    DEPENDENCIES:
    - numPaths_eq_card: PROVED
    - pathTuplesFromTo_finite, nipatsFromTo_finite, ipatsFromTo_finite: PROVED
    - Product rule (bijection between path tuples and products): PROVED (prod_numPaths_eq_pathTuples_ncard)
    - partition_lemma: PROVED (uses product rule and partition)
    - Sign-reversing involution infrastructure: NOT FULLY FORMALIZED
      (requires "first crowded point" and "tail exchange" operations)
  -/
  -- Helper: pathTuples partition into nipats and ipats
  have pathTuples_partition : ∀ A' B' : kVertex k,
      pathTuplesFromTo A' B' = nipatsFromTo A' B' ∪ ipatsFromTo A' B' := by
    intro A' B'
    ext pt
    simp only [pathTuplesFromTo, nipatsFromTo, ipatsFromTo, Set.mem_univ, Set.mem_union,
               Set.mem_setOf_eq, true_iff]
    exact em pt.isNonIntersecting
  -- Helper: nipats and ipats are disjoint
  have nipats_ipats_disjoint : ∀ A' B' : kVertex k,
      Disjoint (nipatsFromTo A' B') (ipatsFromTo A' B') := by
    intro A' B'
    rw [Set.disjoint_iff]
    intro pt ⟨hni, hi⟩
    simp only [nipatsFromTo, ipatsFromTo, Set.mem_setOf_eq, PathTuple.isIntersecting] at hni hi
    exact hi hni
  -- Key lemma 1: product rule + partition
  -- ∏_i numPaths(A_i, B_{σ(i)}) = numNipatsK A B σ + numIpatsK A B σ
  have partition_lemma : ∀ σ : Equiv.Perm (Fin k),
      ∏ i, numPaths (A i) (B (σ i)) = numNipatsK A B σ + numIpatsK A B σ := by
    intro σ
    -- This requires the product rule and partition
    -- Product rule: ∏_i numPaths(A_i, B_{σ(i)}) = (pathTuplesFromTo A (B.permute σ)).ncard
    -- Partition: (pathTuplesFromTo).ncard = nipats.ncard + ipats.ncard
    have hpartition := pathTuples_partition A (B.permute σ)
    have hdisjoint := nipats_ipats_disjoint A (B.permute σ)
    have hfin_nipats := nipatsFromTo_finite A (B.permute σ)
    have hfin_ipats := ipatsFromTo_finite A (B.permute σ)
    have h_ncard_add : (pathTuplesFromTo A (B.permute σ)).ncard =
        (nipatsFromTo A (B.permute σ)).ncard + (ipatsFromTo A (B.permute σ)).ncard := by
      rw [hpartition]
      exact Set.ncard_union_eq hdisjoint hfin_nipats hfin_ipats
    -- The product rule: ∏_i numPaths(A_i, B_{σ(i)}) = (pathTuplesFromTo A (B.permute σ)).ncard
    -- Key insight: B (σ i) = (B.permute σ) i by definition of kVertex.permute
    simp only [numNipatsK, numIpatsK, ← h_ncard_add]
    -- Apply the product rule with B.permute σ
    exact prod_numPaths_eq_pathTuples_ncard A (B.permute σ)
  -- Key lemma 2: ipat cancellation via sign-reversing involution
  have ipat_cancellation :
      ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) * (numIpatsK A B σ : ℤ) = 0 := by
    /-
    PROOF: We use the sign-reversing involution from LGV2.lean.
    
    The key theorem `LGV.sum_signed_ipatFinset_card_eq_zero` proves:
      ∑ σ, sign(σ) * (ipatFinset A (permuteKVertex σ B)).card = 0
    
    We need to show that `numIpatsK A B σ` equals `(ipatFinset A (permuteKVertex σ B)).card`.
    
    This follows because:
    1. The types `LGV1.kVertex k` and `LGV.kVertex (ℤ × ℤ) k` are both `Fin k → ℤ × ℤ`
    2. The permutation functions are the same: `B.permute σ = LGV.permuteKVertex σ B`
    3. The path representations are equivalent via `latticePath'TupleEquiv`
    4. The intersection property is preserved by `latticePath'Tuple_isIntersecting_iff`
    
    The bijection between LGV1's `ipatsFromTo` and LGV2's `ipatFinset` preserves cardinality.
    -/
    -- Convert to LGV2's types and use sum_signed_ipatFinset_card_eq_zero
    -- Note: LGV1.kVertex k = Fin k → LatticePoint = Fin k → ℤ × ℤ = LGV.kVertex (ℤ × ℤ) k
    -- And: B.permute σ = LGV.permuteKVertex σ B (by definition)
    have h_eq : ∀ σ, (numIpatsK A B σ : ℤ) = 
        (LGV.ipatFinset LGV.integerLattice_pathFinite A (LGV.permuteKVertex σ B)).card := by
      intro σ
      rw [numIpatsK_eq_ipatFinset_card]
    simp_rw [h_eq]
    exact LGV.sum_signed_ipatFinset_card_eq_zero A B
  -- Main proof: use partition_lemma and ipat_cancellation
  have h : ∀ σ, (∏ i, (numPaths (A i) (B (σ i)) : ℤ)) =
      (numNipatsK A B σ : ℤ) + (numIpatsK A B σ : ℤ) := by
    intro σ
    have := partition_lemma σ
    simp only [← Nat.cast_prod, ← Nat.cast_add, this]
  simp_rw [h, mul_add, Finset.sum_add_distrib, ipat_cancellation, add_zero]

/-- The LGV lemma for k paths.
    (Proposition prop.lgv.kpaths.count)

    For k-vertices A = (A₁, ..., Aₖ) and B = (B₁, ..., Bₖ):
    det(#paths from Aᵢ to Bⱼ)_{i,j} = ∑_{σ ∈ Sₖ} (-1)^σ · #nipats from A to σ(B)

    The proof uses:
    1. The determinant formula: det(M) = ∑ σ, sign(σ) * ∏ᵢ M(σ i, i)
    2. Rewriting in terms of path tuples to σ(B)
    3. A sign-reversing involution that cancels intersecting path tuples

    Label: prop.lgv.kpaths.count -/
theorem lgv_k_paths {k : ℕ} (A B : kVertex k) :
    (pathMatrixK A B).det =
      ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) * (numNipatsK A B σ : ℤ) := by
  rw [det_eq_sum_path_tuples]
  exact lgv_involution_cancellation A B

/-!
## Sign-Reversing Involution (Proof Technique)

The proofs of the LGV lemmas use a sign-reversing involution on intersecting
path tuples. Given an ipat, we:

1. Find the first intersection point v (first crowded point on the path with smallest index)
2. Let i be the smallest index of a path containing v
3. Let j be the largest index of a path containing v (j > i since v is crowded)
4. Exchange the tails (parts after v) of paths pᵢ and pⱼ
5. Compose σ with the transposition (i j)

This involution:
- Maps ipats to ipats
- Reverses sign (since composing with a transposition changes parity)
- Has no fixed points
- Is its own inverse (applying twice returns the original)

By Lemma lem.sign.cancel2, the sum over ipats cancels, leaving only nipats.
-/

-- Note: The deterministic `firstIntersection` and `firstIntersectionIdx` are defined earlier
-- in this file (see `firstIntersectionIdx` and `firstIntersection`). They provide a
-- deterministic choice of intersection point that is essential for proving ipatInvolution_involutive.

end LGV1
