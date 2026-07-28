/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/

/-!
# Algebraic Combinatorics

This is the root import file for the Algebraic Combinatorics library.
Importing this file provides access to all public-facing modules in the library.

## Namespace Convention

This library uses two top-level namespaces:
- `AlgebraicCombinatorics` — the primary namespace for most definitions and theorems
- `AlgComb` — a shorter alias used in some modules (determinants, symmetric functions)

Both namespaces are valid and coexist intentionally. When writing new code:
- Use `AlgebraicCombinatorics` for new files unless extending existing `AlgComb` modules
- Use `AlgComb` when adding to files that already use this namespace
- Cross-namespace references work via explicit qualification or `open` declarations

The two namespaces arose organically during development. `AlgComb` is shorter and convenient
for frequently-used definitions, while `AlgebraicCombinatorics` is more descriptive.

## Contents

The library is organized into the following major areas:

### Formal Power Series (FPS)
Basic definitions, operations, and properties of formal power series.

### Partitions
Integer partitions, q-binomial coefficients, and related combinatorics.

### Permutations
Permutation groups, inversions, signs, cycles, and Lehmer codes.

### Signed Counting
Inclusion-exclusion, alternating sums, and Möbius inversion.

### Symmetric Functions
Symmetric polynomials, monomial symmetric functions, Schur polynomials,
and the Littlewood-Richardson rule.

### Determinants
Basic properties, Cauchy-Binet formula, Desnanot-Jacobi identity,
and the Lindström-Gessel-Viennot lemma.
-/

-- ============================================================================
-- Formal Power Series (FPS)
-- ============================================================================

-- Core definitions and basic operations
import AlgebraicCombinatorics.FPSDefinition
import AlgebraicCombinatorics.FPS.CommutativeRings
import AlgebraicCombinatorics.FPS.NotationsExamples
import AlgebraicCombinatorics.FPS.Polynomials

-- Advanced operations
import AlgebraicCombinatorics.DividingFPS
import AlgebraicCombinatorics.FPS.Substitution
import AlgebraicCombinatorics.FPS.Derivatives
import AlgebraicCombinatorics.FPS.XnEquivalence

-- Exponentials, logarithms, and powers
import AlgebraicCombinatorics.FPS.ExpLog
import AlgebraicCombinatorics.FPS.NonIntegerPowers

-- Limits and convergence
import AlgebraicCombinatorics.FPS.Limits

-- Infinite products
import AlgebraicCombinatorics.FPS.InfiniteProducts
import AlgebraicCombinatorics.FPS.InfiniteProducts1
import AlgebraicCombinatorics.FPS.InfiniteProducts2

-- Multivariate and Laurent series
import AlgebraicCombinatorics.FPS.Multivariate
import AlgebraicCombinatorics.FPS.LaurentSeries
import AlgebraicCombinatorics.LaurentSeries

-- Applications
import AlgebraicCombinatorics.FPS.IntegerCompositions
import AlgebraicCombinatorics.FPS.WeightedSets

-- ============================================================================
-- Partitions
-- ============================================================================

import AlgebraicCombinatorics.Partitions.Basics
import AlgebraicCombinatorics.Partitions.QBinomialFormulas
import AlgebraicCombinatorics.QBinomialBasic
import AlgebraicCombinatorics.PentagonalJacobi

-- ============================================================================
-- Permutations
-- ============================================================================

import AlgebraicCombinatorics.Permutations.Basics
import AlgebraicCombinatorics.Permutations.Inversions1
import AlgebraicCombinatorics.Permutations.Inversions2
import AlgebraicCombinatorics.Permutations.Signs
import AlgebraicCombinatorics.Permutations.CycleDecomposition

-- ============================================================================
-- Signed Counting
-- ============================================================================

import AlgebraicCombinatorics.SignedCounting.AlternatingSums
import AlgebraicCombinatorics.SignedCounting.InclusionExclusion1
import AlgebraicCombinatorics.SignedCounting.BooleanMobiusInversion
import AlgebraicCombinatorics.SignedCounting.SubtractiveMethods

-- ============================================================================
-- Symmetric Functions
-- ============================================================================

import AlgebraicCombinatorics.SymmetricFunctions.Definitions
import AlgebraicCombinatorics.SymmetricFunctions.MonomialSymmetric
import AlgebraicCombinatorics.SymmetricFunctions.OmegaInvolution
import AlgebraicCombinatorics.SymmetricFunctions.SchurBasics
import AlgebraicCombinatorics.SymmetricFunctions.LittlewoodRichardson
import AlgebraicCombinatorics.SymmetricFunctions.PieriJacobiTrudi
import AlgebraicCombinatorics.SymmetricFunctions.NPartition
import AlgebraicCombinatorics.SymmetricFunctions.SSYTEquiv

-- ============================================================================
-- Determinants
-- ============================================================================

import AlgebraicCombinatorics.DeterminantsBasic
import AlgebraicCombinatorics.Determinants.PermFinset
import AlgebraicCombinatorics.CauchyBinet
import AlgebraicCombinatorics.DesnanotJacobi
import AlgebraicCombinatorics.Determinants.LGV1
import AlgebraicCombinatorics.Determinants.LGV2
import AlgebraicCombinatorics.Determinants.LGVMultiDigraph

-- ============================================================================
-- Fin Utilities
-- ============================================================================

import AlgebraicCombinatorics.Fin.SkipTwo

-- ============================================================================
-- Details (supporting proofs)
-- ============================================================================

import AlgebraicCombinatorics.Details.Limits
import AlgebraicCombinatorics.Details.DominoTilings
import AlgebraicCombinatorics.Details.DominoBridge
import AlgebraicCombinatorics.Details.InfiniteProducts2

-- ============================================================================
-- Extra (support utilities)
-- ============================================================================

import AlgebraicCombinatorics.Extra.Pfaffian
