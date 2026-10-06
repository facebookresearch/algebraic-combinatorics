/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.Details.DominoTilings
import AlgebraicCombinatorics.FPS.WeightedSets

/-!
# Bridge between Domino representations

This module provides equivalence functions between the two Domino representations
used in the project:

1. **WeightedSets.lean** (`DominoTilingsZ.Domino`): Inductive type with `horizontal`/`vertical`
   constructors, using ℤ coordinates, with `Set Domino` for tilings
2. **DominoTilings.lean** (`DominoTilings.Domino`): Structure with `cell1`/`cell2` fields,
   using ℕ coordinates, with `Finset Domino` for tilings

## Design Rationale

The two representations were designed for different purposes:
- **DominoTilingsZ** uses ℤ coordinates for generality in weighted set theory and generating
  function calculations. The inductive type makes pattern matching on orientation natural.
- **DominoTilings** uses ℕ coordinates for finite rectangle tilings and faultfree classification.
  The structure representation is more flexible for adjacency conditions.

For rectangles with positive coordinates (the typical case), the representations are equivalent.
This bridge enables theorem transfer between files when needed.

## Main Definitions

* `DominoBridge.toDominoZ`: Convert a DominoTilings.Domino to DominoTilingsZ.Domino
* `DominoBridge.toDominoN`: Convert a DominoTilingsZ.Domino with positive coordinates to
  DominoTilings.Domino
* `DominoBridge.hasPositiveCoords`: Predicate for DominoTilingsZ.Domino having positive coords
* `DominoBridge.cellsZ`: The cells covered by a DominoTilings.Domino (cast to ℤ coordinates)

## Main Results

* `DominoBridge.toDominoZ_hasPositiveCoords`: Converting from ℕ preserves positivity
* `DominoBridge.toDominoZ_cells`: Converting to ℤ preserves the set of cells
* `DominoBridge.toDominoN_cells`: Converting from ℤ preserves the set of cells

## References

* Source files: `FPS/WeightedSets.lean` (DominoTilingsZ), `Details/DominoTilings.lean` (DominoTilings)

## Tags

domino, tiling, bridge, equivalence
-/

open Finset BigOperators

namespace DominoBridge

/-! ## Coordinate conversion helpers -/

/-- The cells covered by a DominoTilings.Domino, cast to ℤ coordinates.
    This allows comparison with DominoTilingsZ.Domino.toShape. -/
def cellsZ (d : DominoTilings.Domino) : Set (ℤ × ℤ) :=
  {((d.cell1.1 : ℤ), (d.cell1.2 : ℤ)), ((d.cell2.1 : ℤ), (d.cell2.2 : ℤ))}

/-! ## Conversion from DominoTilings.Domino to DominoTilingsZ.Domino

Note: We use `DominoTilings.Domino.isHorizontal` and `DominoTilings.Domino.isVertical`
from DominoTilings.lean via dot notation (e.g., `d.isHorizontal`). -/

/-- Convert a DominoTilings.Domino to DominoTilingsZ.Domino.
    
    The conversion uses the minimum coordinate as the anchor point:
    - A horizontal domino becomes DominoTilingsZ.Domino.horizontal (min col) row
    - A vertical domino becomes DominoTilingsZ.Domino.vertical col (min row) -/
def toDominoZ (d : DominoTilings.Domino) : DominoTilingsZ.Domino :=
  if d.isHorizontal then
    -- Horizontal: cells differ in first coordinate
    let minCol := min d.cell1.1 d.cell2.1
    DominoTilingsZ.Domino.horizontal (minCol : ℤ) (d.cell1.2 : ℤ)
  else
    -- Vertical: cells differ in second coordinate
    let minRow := min d.cell1.2 d.cell2.2
    DominoTilingsZ.Domino.vertical (d.cell1.1 : ℤ) (minRow : ℤ)

/-! ## Conversion from DominoTilingsZ.Domino to DominoTilings.Domino -/

/-- A DominoTilingsZ.Domino has positive coordinates if all its cells have positive coordinates.
    This is the precondition for converting to DominoTilings.Domino (which uses ℕ coordinates). -/
def hasPositiveCoords : DominoTilingsZ.Domino → Prop
  | .horizontal i j => i ≥ 1 ∧ j ≥ 1
  | .vertical i j => i ≥ 1 ∧ j ≥ 1

instance : DecidablePred hasPositiveCoords := fun d =>
  match d with
  | .horizontal i j => inferInstanceAs (Decidable (i ≥ 1 ∧ j ≥ 1))
  | .vertical i j => inferInstanceAs (Decidable (i ≥ 1 ∧ j ≥ 1))

/-- Convert a DominoTilingsZ.Domino with positive coordinates to DominoTilings.Domino.
    
    The conversion preserves the cells covered by the domino:
    - A horizontal domino at (i, j) becomes a DominoTilings.Domino with cells (i, j) and (i+1, j)
    - A vertical domino at (i, j) becomes a DominoTilings.Domino with cells (i, j) and (i, j+1) -/
def toDominoN (d : DominoTilingsZ.Domino) (hpos : hasPositiveCoords d) : DominoTilings.Domino :=
  match d, hpos with
  | .horizontal i j, ⟨hi, hj⟩ =>
    { cell1 := (i.toNat, j.toNat)
      cell2 := ((i + 1).toNat, j.toNat)
      distinct := by
        simp only [ne_eq, Prod.mk.injEq, not_and]
        intro h
        omega
      adjacent := by
        right
        constructor
        · rfl
        · left; omega }
  | .vertical i j, ⟨hi, hj⟩ =>
    { cell1 := (i.toNat, j.toNat)
      cell2 := (i.toNat, (j + 1).toNat)
      distinct := by
        simp only [ne_eq, Prod.mk.injEq, not_and]
        intro _
        omega
      adjacent := by
        left
        constructor
        · rfl
        · left; omega }

/-! ## Round-trip properties -/

/-- Converting DominoTilings.Domino to DominoTilingsZ.Domino produces positive coordinates 
    when all cells are positive. -/
theorem toDominoZ_hasPositiveCoords (d : DominoTilings.Domino)
    (h1 : d.cell1.1 ≥ 1) (h2 : d.cell1.2 ≥ 1) 
    (h3 : d.cell2.1 ≥ 1) (h4 : d.cell2.2 ≥ 1) : hasPositiveCoords (toDominoZ d) := by
  simp only [toDominoZ]
  split_ifs with hH
  · -- Horizontal case
    simp only [hasPositiveCoords, ge_iff_le]
    constructor
    · have hmin : min d.cell1.1 d.cell2.1 ≥ 1 := by omega
      exact_mod_cast hmin
    · exact_mod_cast h2
  · -- Vertical case
    simp only [hasPositiveCoords, ge_iff_le]
    constructor
    · exact_mod_cast h1
    · have hmin : min d.cell1.2 d.cell2.2 ≥ 1 := by omega
      exact_mod_cast hmin

/-! ## Cell preservation theorems -/

/-- Converting DominoTilings.Domino to DominoTilingsZ.Domino preserves the set of cells (cast to ℤ).
    
    This is the key theorem for theorem transfer between the two representations.
    It shows that the cells covered by a domino are the same regardless of which
    representation is used. -/
theorem toDominoZ_cells (d : DominoTilings.Domino) : (toDominoZ d).toShape = cellsZ d := by
  simp only [toDominoZ, cellsZ]
  split_ifs with hH
  · -- Horizontal case: cells have same row (cell1.2 = cell2.2)
    simp only [DominoTilingsZ.Domino.toShape]
    -- In horizontal case, cells differ in first coordinate
    rcases d.adjacent with ⟨hcol, _⟩ | ⟨hrow, hadj⟩
    · -- Same column contradicts distinct
      exfalso
      have hdist := d.distinct
      have : d.cell1 = d.cell2 := Prod.ext hcol hH
      exact hdist this
    · -- Same row, adjacent columns
      rcases hadj with h1 | h2
      · -- cell1.1 + 1 = cell2.1
        have hmin : min d.cell1.1 d.cell2.1 = d.cell1.1 := by omega
        simp only [hmin, hrow]
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
        constructor
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · left; constructor <;> omega
          · right; constructor <;> omega
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · left; constructor <;> omega
          · right; constructor <;> omega
      · -- cell2.1 + 1 = cell1.1
        have hmin : min d.cell1.1 d.cell2.1 = d.cell2.1 := by omega
        simp only [hmin, hrow]
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
        constructor
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · right; constructor <;> omega
          · left; constructor <;> omega
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · right; constructor <;> omega
          · left; constructor <;> omega
  · -- Vertical case: cells have same column
    simp only [DominoTilingsZ.Domino.toShape]
    rcases d.adjacent with ⟨hcol, hadj⟩ | ⟨hrow, _⟩
    · -- Same column, adjacent rows
      rcases hadj with h1 | h2
      · -- cell1.2 + 1 = cell2.2
        have hmin : min d.cell1.2 d.cell2.2 = d.cell1.2 := by omega
        simp only [hmin, hcol]
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
        constructor
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · left; constructor <;> omega
          · right; constructor <;> omega
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · left; constructor <;> omega
          · right; constructor <;> omega
      · -- cell2.2 + 1 = cell1.2
        have hmin : min d.cell1.2 d.cell2.2 = d.cell2.2 := by omega
        simp only [hmin, hcol]
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
        constructor
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · right; constructor <;> omega
          · left; constructor <;> omega
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · right; constructor <;> omega
          · left; constructor <;> omega
    · -- Same row contradicts not horizontal
      exact absurd hrow hH

/-- Converting DominoTilingsZ.Domino to DominoTilings.Domino preserves the set of cells (cast to ℤ). -/
theorem toDominoN_cells (d : DominoTilingsZ.Domino) (hpos : hasPositiveCoords d) : 
    cellsZ (toDominoN d hpos) = d.toShape := by
  match d, hpos with
  | .horizontal i j, ⟨hi, hj⟩ =>
    simp only [toDominoN, cellsZ, DominoTilingsZ.Domino.toShape]
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    constructor
    · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
      · left; constructor <;> omega
      · right; constructor <;> omega
    · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
      · left; constructor <;> omega
      · right; constructor <;> omega
  | .vertical i j, ⟨hi, hj⟩ =>
    simp only [toDominoN, cellsZ, DominoTilingsZ.Domino.toShape]
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    constructor
    · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
      · left; constructor <;> omega
      · right; constructor <;> omega
    · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
      · left; constructor <;> omega
      · right; constructor <;> omega

/-! ## Canonical form for DominoTilings.Domino 

The DominoTilings.Domino type allows the two cells to be in either order. For a canonical
representation, we define a form where cell1 is always the "smaller" cell. -/

/-- A DominoTilings.Domino is in canonical form if cell1 is the "smaller" cell:
    - For horizontal dominos: cell1 has smaller column
    - For vertical dominos: cell1 has smaller row -/
def isCanonical (d : DominoTilings.Domino) : Prop :=
  if d.isHorizontal then d.cell1.1 < d.cell2.1
  else d.cell1.2 < d.cell2.2

/-- Swap the cells of a DominoTilings.Domino. -/
def swap (d : DominoTilings.Domino) : DominoTilings.Domino where
  cell1 := d.cell2
  cell2 := d.cell1
  distinct := d.distinct.symm
  adjacent := by
    rcases d.adjacent with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1.symm, h2.symm⟩
    · right; exact ⟨h1.symm, h2.symm⟩

/-- Convert a DominoTilings.Domino to canonical form. -/
def toCanonical (d : DominoTilings.Domino) : DominoTilings.Domino :=
  if d.isHorizontal then
    if d.cell1.1 < d.cell2.1 then d else swap d
  else
    if d.cell1.2 < d.cell2.2 then d else swap d

/-- The cells of a domino in canonical form are the same as the original. -/
theorem toCanonical_cells (d : DominoTilings.Domino) : 
    ({(toCanonical d).cell1, (toCanonical d).cell2} : Set (ℕ × ℕ)) = {d.cell1, d.cell2} := by
  simp only [toCanonical]
  split_ifs <;> simp [swap, Set.pair_comm]

/-! ## Rectangle correspondence

The two Rectangle definitions use different types:
- `DominoTilings.Rectangle n m : Finset (ℕ × ℕ)` - finite set of natural number pairs
- `DominoTilingsZ.Rectangle n m : Set (ℤ × ℤ)` - set of integer pairs

We establish that they correspond under the natural embedding ℕ → ℤ. -/

/-- Cast a cell from ℕ × ℕ to ℤ × ℤ. -/
def cellToZ (c : ℕ × ℕ) : ℤ × ℤ := (c.1, c.2)

/-- The image of DominoTilings.Rectangle under cellToZ equals DominoTilingsZ.Rectangle 
    as sets of ℤ × ℤ. -/
theorem rectangle_correspondence (n m : ℕ) :
    cellToZ '' (DominoTilings.Rectangle n m : Set (ℕ × ℕ)) = DominoTilingsZ.Rectangle n m := by
  ext ⟨x, y⟩
  simp only [Set.mem_image, Finset.mem_coe, DominoTilingsZ.mem_rectangle_iff]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, heq⟩
    simp only [cellToZ, Prod.mk.injEq] at heq
    rw [DominoTilings.mem_Rectangle] at hmem
    constructor <;> omega
  · intro ⟨hx1, hx2, hy1, hy2⟩
    refine ⟨(x.toNat, y.toNat), ?_, ?_⟩
    · rw [DominoTilings.mem_Rectangle]
      constructor <;> omega
    · simp only [cellToZ, Prod.mk.injEq]
      constructor <;> omega

/-! ## Documentation: Relationship between representations

### Key differences between the two Domino types:

| Aspect | DominoTilingsZ.Domino | DominoTilings.Domino |
|--------|------------------------|-------------------------|
| Coordinates | ℤ × ℤ | ℕ × ℕ |
| Representation | Inductive (horizontal/vertical) | Structure (cell1, cell2) |
| Anchor | Explicit position parameter | Implicit via cells |
| Orientation | Explicit in constructor | Derived from cell positions |

### When to use each representation:

- **DominoTilingsZ**: Use when working with generating functions, weighted sets, or when
  you need to pattern match on orientation. The ℤ coordinates allow for translations
  that may temporarily go negative.

- **DominoTilings**: Use when working with finite tilings of rectangles, especially when
  you need to reason about cell membership in finsets. The structure representation
  is more flexible for adjacency conditions.

### Bridging tilings:

To bridge between `DominoTilingsZ.Tiling S` and `DominoTilings.DominoTiling n m`, use:
1. `toDominoZ` / `toDominoN` for individual domino conversion
2. `toDominoZ_cells` / `toDominoN_cells` for cell preservation
3. `rectangle_correspondence` for shape correspondence
-/

/-! ## Tiling equivalence infrastructure

We develop the machinery to convert between `DominoTilings.DominoTiling n m` and
`DominoTilingsZ.Tiling (Rectangle n m)`. This requires:
1. Converting the set of dominos (Finset vs Set)
2. Preserving the disjointness property
3. Preserving the covering property
-/

section TilingEquivalence

variable {n m : ℕ}

/-! ### Converting a DominoTiling to a Tiling -/

/-- Convert a Finset of DominoTilings.Domino to a Set of DominoTilingsZ.Domino. -/
def dominoFinsetToSet (ds : Finset DominoTilings.Domino) : Set DominoTilingsZ.Domino :=
  {toDominoZ d | d ∈ ds}

/-- The dominos in a DominoTiling have positive coordinates (cell coords ≥ 1). -/
lemma DominoTiling_dominos_pos (T : DominoTilings.DominoTiling n m) (d : DominoTilings.Domino)
    (hd : d ∈ T.dominos) : d.cell1.1 ≥ 1 ∧ d.cell1.2 ≥ 1 ∧ d.cell2.1 ≥ 1 ∧ d.cell2.2 ≥ 1 := by
  have h := T.dominos_in_rect d hd
  have hc1 : d.cell1 ∈ DominoTilings.Rectangle n m := by
    apply h
    simp [DominoTilings.Domino.cells]
  have hc2 : d.cell2 ∈ DominoTilings.Rectangle n m := by
    apply h
    simp [DominoTilings.Domino.cells]
  rw [DominoTilings.mem_Rectangle] at hc1 hc2
  exact ⟨hc1.1, hc1.2.2.1, hc2.1, hc2.2.2.1⟩

/-- Converting a DominoTiling preserves pairwise disjointness. -/
lemma toDominoZ_pairwise_disjoint (T : DominoTilings.DominoTiling n m) :
    Set.PairwiseDisjoint (dominoFinsetToSet T.dominos) DominoTilingsZ.Domino.toShape := by
  intro dz1 hdz1 dz2 hdz2 hne
  simp only [dominoFinsetToSet, Set.mem_ofPred_eq] at hdz1 hdz2
  obtain ⟨d1, hd1, rfl⟩ := hdz1
  obtain ⟨d2, hd2, rfl⟩ := hdz2
  -- Use that d1 ≠ d2 (since the cells would overlap otherwise)
  have hd1d2 : d1 ≠ d2 := by
    intro heq
    subst heq
    exact hne rfl
  -- Get disjointness from the original tiling
  have hdisj := T.pairwise_disjoint d1 hd1 d2 hd2 hd1d2
  -- Convert to the Z representation using cell preservation
  simp only [Function.onFun, Set.disjoint_left]
  intro x hx1 hx2
  rw [toDominoZ_cells] at hx1
  rw [toDominoZ_cells] at hx2
  simp only [cellsZ, Set.mem_insert_iff, Set.mem_singleton_iff] at hx1 hx2
  -- x is in cellsZ d1 and cellsZ d2, which contradicts disjointness
  -- Case analysis on which cells x corresponds to
  rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
  rcases hx1 with hx1_c1 | hx1_c2
  · -- x corresponds to d1.cell1
    rcases hx2 with hx2_c1 | hx2_c2
    · -- x corresponds to d2.cell1
      simp only [Prod.ext_iff] at hx1_c1 hx2_c1
      have hcell : d1.cell1 = d2.cell1 := by ext <;> omega
      have hmem : d1.cell1 ∈ d1.cells ∩ d2.cells := by
        simp only [DominoTilings.Domino.cells, Finset.mem_inter]
        simp [hcell]
      simp [hdisj] at hmem
    · -- x corresponds to d2.cell2
      simp only [Prod.ext_iff] at hx1_c1 hx2_c2
      have hcell : d1.cell1 = d2.cell2 := by ext <;> omega
      have hmem : d1.cell1 ∈ d1.cells ∩ d2.cells := by
        simp only [DominoTilings.Domino.cells, Finset.mem_inter]
        simp [hcell]
      simp [hdisj] at hmem
  · -- x corresponds to d1.cell2
    rcases hx2 with hx2_c1 | hx2_c2
    · -- x corresponds to d2.cell1
      simp only [Prod.ext_iff] at hx1_c2 hx2_c1
      have hcell : d1.cell2 = d2.cell1 := by ext <;> omega
      have hmem : d1.cell2 ∈ d1.cells ∩ d2.cells := by
        simp only [DominoTilings.Domino.cells, Finset.mem_inter]
        simp [hcell]
      simp [hdisj] at hmem
    · -- x corresponds to d2.cell2
      simp only [Prod.ext_iff] at hx1_c2 hx2_c2
      have hcell : d1.cell2 = d2.cell2 := by ext <;> omega
      have hmem : d1.cell2 ∈ d1.cells ∩ d2.cells := by
        simp only [DominoTilings.Domino.cells, Finset.mem_inter]
        simp [hcell]
      simp [hdisj] at hmem

/-- Converting a DominoTiling preserves the covering property. -/
lemma toDominoZ_cover (T : DominoTilings.DominoTiling n m) :
    ⋃ d ∈ dominoFinsetToSet T.dominos, d.toShape = DominoTilingsZ.Rectangle n m := by
  ext ⟨x, y⟩
  simp only [Set.mem_iUnion, dominoFinsetToSet, Set.mem_ofPred_eq, 
             DominoTilingsZ.mem_rectangle_iff]
  constructor
  · rintro ⟨dz, ⟨d, hd, rfl⟩, hxy⟩
    rw [toDominoZ_cells] at hxy
    simp only [cellsZ, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff] at hxy
    have hcells := T.dominos_in_rect d hd
    rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hc1 : d.cell1 ∈ DominoTilings.Rectangle n m := by
        apply hcells
        simp [DominoTilings.Domino.cells]
      rw [DominoTilings.mem_Rectangle] at hc1
      constructor <;> omega
    · have hc2 : d.cell2 ∈ DominoTilings.Rectangle n m := by
        apply hcells
        simp [DominoTilings.Domino.cells]
      rw [DominoTilings.mem_Rectangle] at hc2
      constructor <;> omega
  · intro ⟨hx1, hx2, hy1, hy2⟩
    -- The cell (x, y) is in the ℕ rectangle
    have hmem : (x.toNat, y.toNat) ∈ DominoTilings.Rectangle n m := by
      rw [DominoTilings.mem_Rectangle]
      constructor <;> omega
    -- So it's covered by some domino in T
    have hcover := T.covers_all
    rw [Finset.ext_iff] at hcover
    have := (hcover (x.toNat, y.toNat)).mpr hmem
    simp only [Finset.mem_biUnion] at this
    obtain ⟨d, hd, hcell⟩ := this
    refine ⟨toDominoZ d, ⟨d, hd, rfl⟩, ?_⟩
    rw [toDominoZ_cells]
    simp only [cellsZ, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    simp only [DominoTilings.Domino.cells] at hcell
    simp at hcell
    rcases hcell with hc1 | hc2
    · left
      have h1 : x.toNat = d.cell1.1 := congrArg Prod.fst hc1
      have h2 : y.toNat = d.cell1.2 := congrArg Prod.snd hc1
      constructor <;> omega
    · right
      have h1 : x.toNat = d.cell2.1 := congrArg Prod.fst hc2
      have h2 : y.toNat = d.cell2.2 := congrArg Prod.snd hc2
      constructor <;> omega

/-- Convert a DominoTiling to a Tiling. -/
def toTilingZ (T : DominoTilings.DominoTiling n m) : 
    DominoTilingsZ.Tiling (DominoTilingsZ.Rectangle n m) where
  dominos := dominoFinsetToSet T.dominos
  pairwise_disjoint := toDominoZ_pairwise_disjoint T
  cover := toDominoZ_cover T

/-! ### Dominos in a Tiling of a rectangle have positive coordinates -/

/-- Dominos in a Tiling of a rectangle have positive coordinates. -/
lemma Tiling_dominos_pos (T : DominoTilingsZ.Tiling (DominoTilingsZ.Rectangle n m))
    (d : DominoTilingsZ.Domino) (hd : d ∈ T.dominos) : hasPositiveCoords d := by
  have hcover := T.cover
  have hsub : d.toShape ⊆ DominoTilingsZ.Rectangle n m := by
    rw [← hcover]
    exact Set.subset_biUnion_of_mem hd
  match d with
  | .horizontal i j =>
    simp only [hasPositiveCoords, ge_iff_le]
    have h1 : (i, j) ∈ DominoTilingsZ.Rectangle n m := by
      apply hsub
      simp [DominoTilingsZ.Domino.toShape]
    rw [DominoTilingsZ.mem_rectangle_iff] at h1
    exact ⟨h1.1, h1.2.2.1⟩
  | .vertical i j =>
    simp only [hasPositiveCoords, ge_iff_le]
    have h1 : (i, j) ∈ DominoTilingsZ.Rectangle n m := by
      apply hsub
      simp [DominoTilingsZ.Domino.toShape]
    rw [DominoTilingsZ.mem_rectangle_iff] at h1
    exact ⟨h1.1, h1.2.2.1⟩

/-- toDominoN is injective on dominos with positive coordinates. -/
lemma toDominoN_injective {d1 d2 : DominoTilingsZ.Domino} 
    (hpos1 : hasPositiveCoords d1) (hpos2 : hasPositiveCoords d2)
    (heq : toDominoN d1 hpos1 = toDominoN d2 hpos2) : d1 = d2 := by
  -- Use that toDominoN preserves cells
  have hcells1 := toDominoN_cells d1 hpos1
  have hcells2 := toDominoN_cells d2 hpos2
  -- From heq, we get cellsZ (toDominoN d1 hpos1) = cellsZ (toDominoN d2 hpos2)
  have hcellsZ : cellsZ (toDominoN d1 hpos1) = cellsZ (toDominoN d2 hpos2) := by rw [heq]
  rw [hcells1, hcells2] at hcellsZ
  -- Now d1.toShape = d2.toShape, so d1 = d2
  exact DominoTilingsZ.Domino.eq_of_toShape_eq hcellsZ

end TilingEquivalence

end DominoBridge
