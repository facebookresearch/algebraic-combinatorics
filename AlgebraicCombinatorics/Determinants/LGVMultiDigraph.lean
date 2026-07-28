/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import AlgebraicCombinatorics.Determinants.LGV2

/-!
# The weighted LGV lemma for directed multigraphs

`LGV2` proves the weighted Lindström--Gessel--Viennot lemma for a digraph whose
arcs are propositions, and hence cannot distinguish parallel arcs.  This file
gives the version stated in Theorem `thm.lgv.kpaths.wt-dg` of the source, where
the digraph need not be simple.

We use the standard incidence-subdivision representation.  A directed
multigraph with vertex type `V` and arc type `E` is replaced by the simple
digraph on `V ⊕ E`, with

```
source(e) → e → target(e).
```

Thus parallel arcs become distinct intermediate vertices.  Paths whose
endpoints are original vertices alternate between original vertices and arc
vertices, so they are precisely paths in the original multigraph.  Sharing an
arc vertex also forces sharing its source and target; consequently the
vertex-disjoint path tuples in the subdivision are exactly the vertex-disjoint
path tuples in the original multigraph.  Giving the first half of a subdivided
arc its original weight and the second half weight `1` preserves path weights.
-/

open Finset BigOperators Matrix

namespace LGV

universe u v

/-- A directed multigraph.  Unlike `SimpleDigraph`, its arcs form a type of
objects, so distinct arcs may have the same source and target. -/
structure MultiDigraph (V : Type u) where
  /-- The type of arcs. -/
  Arc : Type v
  /-- The source of an arc. -/
  source : Arc → V
  /-- The target of an arc. -/
  target : Arc → V

namespace MultiDigraph

variable {V : Type u} (D : MultiDigraph.{u, v} V)

/-- Vertices of the incidence subdivision: original vertices or arc vertices. -/
abbrev SubdivisionVertex := V ⊕ D.Arc

/-- The incidence subdivision of a directed multigraph.  Every original arc
`e : u → v` is represented by the two arcs `u → e` and `e → v`. -/
def subdivision : SimpleDigraph D.SubdivisionVertex where
  arc x y :=
    match x, y with
    | Sum.inl u, Sum.inr e => D.source e = u
    | Sum.inr e, Sum.inl v => D.target e = v
    | _, _ => False
  arc_irrefl := by
    intro x
    cases x <;> simp

/-- Embed an original vertex into the incidence subdivision. -/
def vertex (x : V) : D.SubdivisionVertex := Sum.inl x

@[simp] theorem vertex_injective : Function.Injective D.vertex :=
  Sum.inl_injective

/-- Embed a tuple of original vertices into the incidence subdivision. -/
def vertices {k : ℕ} (A : kVertex V k) : kVertex D.SubdivisionVertex k :=
  fun i => D.vertex (A i)

/-- Path-finiteness of a multigraph, expressed through its incidence
subdivision.  This counts parallel arcs as distinct path choices. -/
def IsPathFinite : Prop :=
  D.subdivision.IsPathFinite

/-- Acyclicity of a multigraph, expressed through its incidence subdivision. -/
def IsAcyclic : Prop :=
  D.subdivision.IsAcyclic

variable {K : Type*} [CommRing K]

/-- Turn weights of multigraph arcs into weights of subdivision arcs. -/
noncomputable def subdivisionArcWeight (w : D.Arc → K) :
    ArcWeight D.subdivision K :=
  fun x y h =>
    match x, y with
    | Sum.inl _, Sum.inr e => w e
    | Sum.inr _, Sum.inl _ => 1
    | Sum.inl _, Sum.inl _ => False.elim h
    | Sum.inr _, Sum.inr _ => False.elim h

/-- The matrix of sums of path weights between two tuples of multigraph
vertices.  Paths are represented in the incidence subdivision. -/
noncomputable def pathWeightMatrix (hpf : D.IsPathFinite) (w : D.Arc → K)
    {k : ℕ} (A B : kVertex V k) : Matrix (Fin k) (Fin k) K := by
  classical
  exact LGV.pathWeightMatrix hpf (D.subdivisionArcWeight w) (D.vertices A) (D.vertices B)

/-- The sum of the weights of non-intersecting path tuples in a directed
multigraph. -/
noncomputable def nipatWeightSum (hpf : D.IsPathFinite) (w : D.Arc → K)
    {k : ℕ} (A B : kVertex V k) (σ : Equiv.Perm (Fin k)) : K := by
  classical
  exact LGV.nipatWeightSum hpf (D.subdivisionArcWeight w) (D.vertices A) (D.vertices B) σ

/-- Weighted LGV for an arbitrary path-finite acyclic directed multigraph.

This is the full digraph generality of Theorem `thm.lgv.kpaths.wt-dg`.
Parallel arcs are retained as distinct vertices of the incidence subdivision. -/
theorem lgv_weighted_multidigraph (hpf : D.IsPathFinite) (hac : D.IsAcyclic)
    {k : ℕ} (w : D.Arc → K) (A B : kVertex V k) :
    (D.pathWeightMatrix hpf w A B).det =
      ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
        D.nipatWeightSum hpf w A (permuteKVertex σ B) σ := by
  classical
  simpa [pathWeightMatrix, nipatWeightSum, vertices, permuteKVertex] using
    (lgv_weighted_digraph hpf hac (D.subdivisionArcWeight w)
      (D.vertices A) (D.vertices B))

end MultiDigraph

end LGV
