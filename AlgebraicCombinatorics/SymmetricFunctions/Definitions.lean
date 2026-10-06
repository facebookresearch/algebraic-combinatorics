/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.Permutations.Basics

/-!
# Definitions and Examples of Symmetric Polynomials

This file formalizes the definitions and basic properties of symmetric polynomials,
following Section "Definitions and examples of symmetric polynomials" (sec.sf.sp) of the source.

## Main definitions

* We use Mathlib's `MvPolynomial.IsSymmetric` for the notion of symmetric polynomials.
* `MvPolynomial.symmetricSubalgebra σ R` is the ring of symmetric polynomials.
* `MvPolynomial.esymm σ R n` is the n-th elementary symmetric polynomial.
* `MvPolynomial.hsymm σ R n` is the n-th complete homogeneous symmetric polynomial.
* `MvPolynomial.psum σ R n` is the n-th power sum.

## Main results

* The symmetric group acts on polynomials by permuting variables (Proposition prop.sf.SN-acts)
* The action is by K-algebra automorphisms (Proposition prop.sf.SN-acts-by-alg-auts)
* The set of symmetric polynomials forms a K-subalgebra (Theorem thm.sf.S-subalg)
* For n > N, the n-th elementary symmetric polynomial is zero (Proposition prop.sf.en=0)
* Newton-Girard formulas relating e_n, h_n, and p_n (Theorem thm.sf.NG)
* Fundamental Theorem of Symmetric Polynomials (Theorem thm.sf.ftsf)
* A polynomial is symmetric iff it is invariant under simple transpositions (Lemma lem.sf.simples-enough)

## References

* Source: SymmetricFunctions/Definitions.tex, sec.sf.sp

## Implementation notes

Mathlib already provides extensive support for symmetric polynomials via `MvPolynomial.IsSymmetric`
and related definitions. This file connects the textbook presentation to Mathlib's API
and provides additional lemmas following the source material.

The symmetric group action on polynomials is given by `MvPolynomial.rename` in Mathlib.
For a permutation σ : Equiv.Perm (Fin N), the action σ · f is `MvPolynomial.rename σ f`.
-/

open scoped Polynomial
open MvPolynomial Finset

namespace AlgebraicCombinatorics

namespace SymmetricPolynomials

variable {K : Type*} [CommRing K]
variable {N : ℕ}

/-!
## Convention (Convention conv.sf.KN)

We fix a commutative ring K and a natural number N throughout.
The polynomial ring P = K[x₁, x₂, ..., x_N] is `MvPolynomial (Fin N) K` in Mathlib.
-/

/-- The polynomial ring in N variables over K.
    This corresponds to 𝒫 in the source (Definition def.sf.PS (a)).
    Label: def.sf.PS -/
abbrev P (K : Type*) [CommRing K] (N : ℕ) : Type _ := MvPolynomial (Fin N) K

/-!
## The Symmetric Group Action (Definition def.sf.PS (b))

The symmetric group S_N acts on P by permuting variables:
  σ · f = f[x_{σ(1)}, x_{σ(2)}, ..., x_{σ(N)}]

In Mathlib, this is given by `MvPolynomial.rename σ f` where σ : Equiv.Perm (Fin N).
-/

/-- The action of a permutation on a polynomial by renaming variables.
    This is σ · f = f[x_{σ(1)}, ..., x_{σ(N)}] in the source.
    Label: def.sf.PS -/
noncomputable def permAction (σ : Equiv.Perm (Fin N)) (f : P K N) : P K N :=
  rename σ f

/-- Notation: σ • f for the permutation action -/
scoped notation:70 σ " •ₚ " f:70 => permAction σ f

/-!
## Proposition prop.sf.SN-acts: The action is a well-defined group action

(a) id · f = f for every f ∈ P
(b) (στ) · f = σ · (τ · f) for every σ, τ ∈ S_N and f ∈ P
-/

/-- The identity permutation acts trivially (Proposition prop.sf.SN-acts (a)).
    Label: prop.sf.SN-acts -/
theorem permAction_id (f : P K N) : (1 : Equiv.Perm (Fin N)) •ₚ f = f := by
  simp only [permAction, Equiv.Perm.coe_one, rename_id]
  rfl

/-- Composition of permutation actions (Proposition prop.sf.SN-acts (b)).
    Label: prop.sf.SN-acts -/
theorem permAction_mul (σ τ : Equiv.Perm (Fin N)) (f : P K N) :
    (σ * τ) •ₚ f = σ •ₚ (τ •ₚ f) := by
  simp only [permAction, rename_rename]
  rfl

/-- The symmetric group action on polynomials is a well-defined MulAction.
    This formalizes Proposition prop.sf.SN-acts in the standard Mathlib form:
    - `one_smul` corresponds to part (a): id · f = f
    - `mul_smul` corresponds to part (b): (στ) · f = σ · (τ · f)
    Label: prop.sf.SN-acts -/
noncomputable instance permMulAction : MulAction (Equiv.Perm (Fin N)) (P K N) where
  smul := permAction
  one_smul := permAction_id
  mul_smul σ τ f := by
    show permAction (σ * τ) f = permAction σ (permAction τ f)
    exact permAction_mul σ τ f

/-- The Mathlib smul action agrees with our permAction notation.
    Label: prop.sf.SN-acts -/
@[simp]
theorem smul_eq_permAction (σ : Equiv.Perm (Fin N)) (f : P K N) :
    σ • f = σ •ₚ f := rfl

/-!
## Definition of Symmetric Polynomials (Definition def.sf.PS (c)(d))

A polynomial f ∈ P is symmetric if σ · f = f for all σ ∈ S_N.
The set S of all symmetric polynomials is `symmetricSubalgebra (Fin N) K` in Mathlib.
-/

/-- A polynomial is symmetric if it is invariant under all permutations.
    This is Definition def.sf.PS (c) in the source.
    Label: def.sf.PS -/
def IsSymm (f : P K N) : Prop := f.IsSymmetric

/-- The ring of symmetric polynomials in N variables over K.

    This is the K-subalgebra S of P consisting of all symmetric polynomials,
    i.e., polynomials f such that σ · f = f for all permutations σ ∈ S_N.

    The terminology "ring of symmetric polynomials" comes from the fact that
    this subalgebra is closed under addition, multiplication, and scalar
    multiplication by elements of K (Theorem thm.sf.S-subalg).

    Label: def.sf.ring-of-symm -/
abbrev S (K : Type*) [CommRing K] (N : ℕ) : Subalgebra K (P K N) :=
  symmetricSubalgebra (Fin N) K

/-- Alternative name: the ring of symmetric polynomials.
    This is the standard terminology for the subalgebra S.
    Label: def.sf.ring-of-symm -/
abbrev ringOfSymmetricPolynomials (K : Type*) [CommRing K] (N : ℕ) : Subalgebra K (P K N) :=
  S K N

/-- The ring of symmetric polynomials is indeed a ring (a K-subalgebra of P).
    This follows from Mathlib's `symmetricSubalgebra` being a `Subalgebra`.
    Label: def.sf.ring-of-symm -/
noncomputable example : Ring (S K N) := inferInstance

/-- The ring of symmetric polynomials is a commutative ring.
    Label: def.sf.ring-of-symm -/
noncomputable example : CommRing (S K N) := inferInstance

/-- The ring of symmetric polynomials is a K-algebra.
    Label: def.sf.ring-of-symm -/
noncomputable example : Algebra K (S K N) := inferInstance

/-!
## Additional API for Definition def.sf.PS

These lemmas provide useful characterizations of the definitions.
-/

/-- The definition of IsSymm unfolds to: f is symmetric iff rename σ f = f for all σ.
    Label: def.sf.PS -/
theorem isSymm_def (f : P K N) : IsSymm f ↔ ∀ σ : Equiv.Perm (Fin N), rename σ f = f := Iff.rfl

/-- Membership in S is equivalent to being symmetric.
    Label: def.sf.PS -/
theorem mem_S_iff (f : P K N) : f ∈ S K N ↔ IsSymm f := mem_symmetricSubalgebra f

/-- The permutation action definition: σ •ₚ f = rename σ f.
    Label: def.sf.PS -/
theorem permAction_eq_rename (σ : Equiv.Perm (Fin N)) (f : P K N) : σ •ₚ f = rename σ f := rfl

/-- A polynomial is symmetric iff the permutation action fixes it.
    Label: def.sf.PS -/
theorem isSymm_iff_permAction (f : P K N) : IsSymm f ↔ ∀ σ : Equiv.Perm (Fin N), σ •ₚ f = f := by
  simp only [IsSymm, MvPolynomial.IsSymmetric, permAction_eq_rename]

/-- Example: The sum ∑ xᵢ is symmetric (Example exa.sf.PS1 (a)).
    Label: exa.sf.PS1 -/
theorem isSymm_sum_X : IsSymm (∑ i : Fin N, X i : P K N) := by
  intro σ
  simp only [map_sum, rename_X]
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

/-- The polynomial ring P K N is a commutative K-algebra.
    Label: def.sf.PS -/
noncomputable instance P_isCommRing' : CommRing (P K N) := inferInstance

/-- The polynomial ring P K N is a K-algebra.
    Label: def.sf.PS -/
noncomputable instance P_isAlgebra' : Algebra K (P K N) := inferInstance

/-!
## Proposition prop.sf.SN-acts-by-alg-auts: The action is by K-algebra automorphisms

For each σ ∈ S_N, the map f ↦ σ · f is a K-algebra automorphism of P.
-/

/-- The permutation action preserves addition.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAction_add (σ : Equiv.Perm (Fin N)) (f g : P K N) :
    σ •ₚ (f + g) = σ •ₚ f + σ •ₚ g := by
  simp only [permAction, map_add]

/-- The permutation action preserves multiplication.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAction_mul' (σ : Equiv.Perm (Fin N)) (f g : P K N) :
    σ •ₚ (f * g) = (σ •ₚ f) * (σ •ₚ g) := by
  simp only [permAction, map_mul]

/-- The permutation action preserves scaling.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAction_smul (σ : Equiv.Perm (Fin N)) (c : K) (f : P K N) :
    σ •ₚ (c • f) = c • (σ •ₚ f) := by
  simp only [permAction, map_smul]

/-- The permutation action is invertible with inverse σ⁻¹.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAction_inv (σ : Equiv.Perm (Fin N)) (f : P K N) :
    σ⁻¹ •ₚ (σ •ₚ f) = f := by
  simp only [permAction, rename_rename, Equiv.Perm.inv_def, Equiv.symm_comp_self, rename_id]
  rfl

/-- The K-algebra automorphism of P induced by a permutation σ.
    This is the main object of Proposition prop.sf.SN-acts-by-alg-auts:
    for each σ ∈ S_N, the map f ↦ σ · f is a K-algebra automorphism.
    Label: prop.sf.SN-acts-by-alg-auts -/
noncomputable def permAutomorphism (σ : Equiv.Perm (Fin N)) : P K N ≃ₐ[K] P K N :=
  renameEquiv K σ

/-- The permutation action equals the automorphism applied to the polynomial.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAction_eq_permAutomorphism (σ : Equiv.Perm (Fin N)) (f : P K N) :
    σ •ₚ f = permAutomorphism σ f := rfl

/-- The permutation automorphism preserves zero.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_zero (σ : Equiv.Perm (Fin N)) :
    permAutomorphism σ (0 : P K N) = 0 :=
  map_zero (permAutomorphism σ)

/-- The permutation automorphism preserves one.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_one (σ : Equiv.Perm (Fin N)) :
    permAutomorphism σ (1 : P K N) = 1 :=
  map_one (permAutomorphism σ)

/-- The permutation automorphism preserves constants.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_C (σ : Equiv.Perm (Fin N)) (c : K) :
    permAutomorphism σ (C c : P K N) = C c :=
  rename_C σ c

/-- The identity permutation gives the identity automorphism.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_id :
    permAutomorphism (K := K) (N := N) (1 : Equiv.Perm (Fin N)) = AlgEquiv.refl :=
  renameEquiv_refl K

/-- Composition of permutation automorphisms: (σ * τ) acts as τ then σ.
    Note: In AlgEquiv, f * g = g.trans f (apply g first, then f).
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_mul_perm (σ τ : Equiv.Perm (Fin N)) :
    permAutomorphism (K := K) (σ * τ) = permAutomorphism σ * permAutomorphism τ := by
  ext f
  unfold permAutomorphism
  simp only [renameEquiv_apply, AlgEquiv.mul_apply, rename_rename]
  rfl

/-- The inverse automorphism is given by the inverse permutation.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_symm (σ : Equiv.Perm (Fin N)) :
    (permAutomorphism (K := K) σ).symm = permAutomorphism σ⁻¹ :=
  renameEquiv_symm K σ

/-- The permutation automorphism is bijective.
    Label: prop.sf.SN-acts-by-alg-auts -/
theorem permAutomorphism_bijective (σ : Equiv.Perm (Fin N)) :
    Function.Bijective (permAutomorphism (K := K) σ) :=
  AlgEquiv.bijective (permAutomorphism σ)

/-- The map from S_N to Aut_K(P) is a group homomorphism.
    This is the full content of Proposition prop.sf.SN-acts-by-alg-auts:
    S_N acts on P by K-algebra automorphisms.
    Label: prop.sf.SN-acts-by-alg-auts -/
noncomputable def permAutomorphismHom :
    Equiv.Perm (Fin N) →* (P K N ≃ₐ[K] P K N) where
  toFun σ := permAutomorphism σ
  map_one' := permAutomorphism_id
  map_mul' σ τ := permAutomorphism_mul_perm σ τ

/-!
## Theorem thm.sf.S-subalg: S is a K-subalgebra of P

The set of symmetric polynomials is closed under addition, multiplication, and scaling,
and contains 0 and 1.

From the source (AlgebraicCombinatorics/tex/SymmetricFunctions/Definitions.tex, Theorem thm.sf.S-subalg):

> The subset S is a K-subalgebra of P.

A K-subalgebra of P must satisfy:
1. S contains 0 and 1
2. S is closed under addition
3. S is closed under multiplication
4. S is closed under scalar multiplication by elements of K

This section proves all these properties both in terms of `IsSymm` (the predicate)
and `∈ S K N` (membership in the subalgebra).
-/

/-- **Theorem thm.sf.S-subalg**: The symmetric polynomials form a K-subalgebra of P.

    This is the main theorem stating that the set S of symmetric polynomials is
    a K-subalgebra of the polynomial ring P = K[x₁, x₂, ..., x_N].

    A K-subalgebra satisfies:
    - (a) S contains 0 and 1 (see `S_zero_mem`, `S_one_mem`)
    - (b) S is closed under addition (see `S_add_mem`)
    - (c) S is closed under multiplication (see `S_mul_mem`)
    - (d) S is closed under scalar multiplication by K (see `S_smul_mem`)

    The definition `S K N := symmetricSubalgebra (Fin N) K` directly provides
    the `Subalgebra K (P K N)` structure, which bundles all these properties.

    Label: thm.sf.S-subalg -/
def S_subalgebra : Subalgebra K (P K N) := S K N

/-!
### Part (a): S contains 0 and 1
-/

/-- Zero is in S (Theorem thm.sf.S-subalg, part (a)).
    Label: thm.sf.S-subalg -/
theorem S_zero_mem : (0 : P K N) ∈ S K N := Subalgebra.zero_mem _

/-- One is in S (Theorem thm.sf.S-subalg, part (a)).
    Label: thm.sf.S-subalg -/
theorem S_one_mem : (1 : P K N) ∈ S K N := Subalgebra.one_mem _

/-- Zero is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_zero : IsSymm (0 : P K N) := MvPolynomial.IsSymmetric.zero

/-- One is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_one : IsSymm (1 : P K N) := MvPolynomial.IsSymmetric.one

/-- Constants are in S (Theorem thm.sf.S-subalg, part (a) generalized).
    Label: thm.sf.S-subalg -/
theorem S_C_mem (c : K) : (C c : P K N) ∈ S K N := Subalgebra.algebraMap_mem _ c

/-- Constants are symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_C (c : K) : IsSymm (C c : P K N) := MvPolynomial.IsSymmetric.C c

/-!
### Part (b): S is closed under addition
-/

/-- S is closed under addition (Theorem thm.sf.S-subalg, part (b)).
    Label: thm.sf.S-subalg -/
theorem S_add_mem {f g : P K N} (hf : f ∈ S K N) (hg : g ∈ S K N) : f + g ∈ S K N :=
  Subalgebra.add_mem _ hf hg

/-- Sum of symmetric polynomials is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_add {f g : P K N} (hf : IsSymm f) (hg : IsSymm g) : IsSymm (f + g) :=
  MvPolynomial.IsSymmetric.add hf hg

/-!
### Part (c): S is closed under multiplication
-/

/-- S is closed under multiplication (Theorem thm.sf.S-subalg, part (c)).
    Label: thm.sf.S-subalg -/
theorem S_mul_mem {f g : P K N} (hf : f ∈ S K N) (hg : g ∈ S K N) : f * g ∈ S K N :=
  Subalgebra.mul_mem _ hf hg

/-- Product of symmetric polynomials is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_mul {f g : P K N} (hf : IsSymm f) (hg : IsSymm g) : IsSymm (f * g) :=
  MvPolynomial.IsSymmetric.mul hf hg

/-!
### Part (d): S is closed under scalar multiplication
-/

/-- S is closed under scalar multiplication (Theorem thm.sf.S-subalg, part (d)).
    Label: thm.sf.S-subalg -/
theorem S_smul_mem (c : K) {f : P K N} (hf : f ∈ S K N) : c • f ∈ S K N :=
  Subalgebra.smul_mem _ hf c

/-- Scalar multiple of a symmetric polynomial is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_smul (c : K) {f : P K N} (hf : IsSymm f) : IsSymm (c • f) :=
  MvPolynomial.IsSymmetric.smul c hf

/-!
### Additional closure properties (consequences of being a K-subalgebra)

These properties follow automatically from S being a K-subalgebra.
-/

/-- S is closed under negation.
    Label: thm.sf.S-subalg -/
theorem S_neg_mem {f : P K N} (hf : f ∈ S K N) : -f ∈ S K N :=
  Subalgebra.neg_mem _ hf

/-- Negation of a symmetric polynomial is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_neg {f : P K N} (hf : IsSymm f) : IsSymm (-f) :=
  MvPolynomial.IsSymmetric.neg hf

/-- S is closed under subtraction.
    Label: thm.sf.S-subalg -/
theorem S_sub_mem {f g : P K N} (hf : f ∈ S K N) (hg : g ∈ S K N) : f - g ∈ S K N :=
  Subalgebra.sub_mem _ hf hg

/-- Difference of symmetric polynomials is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_sub {f g : P K N} (hf : IsSymm f) (hg : IsSymm g) : IsSymm (f - g) :=
  MvPolynomial.IsSymmetric.sub hf hg

/-- S is closed under powers.
    Label: thm.sf.S-subalg -/
theorem S_pow_mem {f : P K N} (hf : f ∈ S K N) (n : ℕ) : f ^ n ∈ S K N :=
  Subalgebra.pow_mem _ hf n

/-- Power of a symmetric polynomial is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_pow {f : P K N} (hf : IsSymm f) (n : ℕ) : IsSymm (f ^ n) := by
  intro σ
  rw [map_pow]
  rw [hf σ]

/-- S is closed under finite sums.
    Label: thm.sf.S-subalg -/
theorem S_sum_mem {ι : Type*} {s : Finset ι} {f : ι → P K N}
    (hf : ∀ i ∈ s, f i ∈ S K N) : ∑ i ∈ s, f i ∈ S K N :=
  Subalgebra.sum_mem _ hf

/-- Finite sum of symmetric polynomials is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_sum {ι : Type*} {s : Finset ι} {f : ι → P K N}
    (hf : ∀ i ∈ s, IsSymm (f i)) : IsSymm (∑ i ∈ s, f i) := by
  intro σ
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i hi => hf i hi σ)

/-- S is closed under finite products.
    Label: thm.sf.S-subalg -/
theorem S_prod_mem {ι : Type*} {s : Finset ι} {f : ι → P K N}
    (hf : ∀ i ∈ s, f i ∈ S K N) : ∏ i ∈ s, f i ∈ S K N :=
  Subalgebra.prod_mem _ hf

/-- Finite product of symmetric polynomials is symmetric.
    Label: thm.sf.S-subalg -/
theorem isSymm_prod {ι : Type*} {s : Finset ι} {f : ι → P K N}
    (hf : ∀ i ∈ s, IsSymm (f i)) : IsSymm (∏ i ∈ s, f i) := by
  intro σ
  simp only [map_prod]
  exact Finset.prod_congr rfl (fun i hi => hf i hi σ)

/-!
## Definition of Monomials (Definition def.sf.monomial)

(a) A monomial is x₁^{a₁} x₂^{a₂} ⋯ x_N^{a_N} with a_i ∈ ℕ
(b) The degree of a monomial is a₁ + a₂ + ⋯ + a_N
(c) A monomial is squarefree if all a_i ∈ {0, 1}
(d) A monomial is primal if at most one a_i > 0
-/

/-- A monomial represented by its exponent vector.
    In the textbook, a monomial is x₁^{a₁} x₂^{a₂} ⋯ x_N^{a_N}.
    We represent it by the exponent vector (a₁, a₂, ..., a_N) ∈ ℕ^N.
    Label: def.sf.monomial -/
abbrev Monomial (N : ℕ) := Fin N →₀ ℕ

/-- Convert a monomial (exponent vector) to the corresponding polynomial x₁^{a₁} ⋯ x_N^{a_N}.
    Label: def.sf.monomial -/
noncomputable def Monomial.toPoly (m : Monomial N) : P K N :=
  monomial m 1

/-- The degree of a monomial is the sum of its exponents.
    Label: def.sf.monomial -/
def Monomial.degree (m : Monomial N) : ℕ := m.sum (fun _ a => a)

/-- Alternative characterization: degree equals the support sum.
    Label: def.sf.monomial -/
theorem Monomial.degree_eq_support_sum (m : Monomial N) :
    m.degree = m.support.sum m := by
  simp only [degree, Finsupp.sum]

/-- A monomial is squarefree if all exponents are 0 or 1.
    Label: def.sf.monomial -/
def Monomial.IsSquarefree (m : Monomial N) : Prop := ∀ i, m i ≤ 1

/-- A monomial is primal if at most one exponent is positive.
    This means the monomial is either 1 or a power of a single variable.
    Label: def.sf.monomial -/
def Monomial.IsPrimal (m : Monomial N) : Prop := m.support.card ≤ 1

/-- The degree of a monomial equals the total degree of its polynomial representation
    (when K is nontrivial).
    Label: def.sf.monomial -/
theorem Monomial.degree_eq_totalDegree [Nontrivial K] (m : Monomial N) :
    m.degree = (m.toPoly : P K N).totalDegree := by
  unfold degree toPoly
  rw [totalDegree_monomial _ (one_ne_zero)]

/-- The set of all monomials of a given degree n.
    Label: def.sf.monomial -/
def monomialsOfDegree (N n : ℕ) : Set (Monomial N) :=
  {m | m.degree = n}

/-- The set of all squarefree monomials of a given degree n.
    Label: def.sf.monomial -/
def squarefreeMonomials (N n : ℕ) : Set (Monomial N) :=
  {m | m.IsSquarefree ∧ m.degree = n}

/-- The set of all primal monomials of a given degree n.
    Label: def.sf.monomial -/
def primalMonomials (N n : ℕ) : Set (Monomial N) :=
  {m | m.IsPrimal ∧ m.degree = n}

/-- The zero monomial (all exponents zero) represents 1.
    Label: def.sf.monomial -/
@[simp]
theorem Monomial.toPoly_zero : (0 : Monomial N).toPoly = (1 : P K N) := by
  simp only [toPoly, monomial_zero']
  rfl

/-- The degree of the zero monomial is 0.
    Label: def.sf.monomial -/
@[simp]
theorem Monomial.degree_zero : (0 : Monomial N).degree = 0 := by
  simp only [degree, Finsupp.sum_zero_index]

/-- The zero monomial is squarefree.
    Label: def.sf.monomial -/
theorem Monomial.isSquarefree_zero : (0 : Monomial N).IsSquarefree := by
  intro i
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.zero_le]

/-- The zero monomial is primal.
    Label: def.sf.monomial -/
theorem Monomial.isPrimal_zero : (0 : Monomial N).IsPrimal := by
  simp only [IsPrimal, Finsupp.support_zero, card_empty, Nat.zero_le]

/-- A single variable x_i corresponds to the monomial with exponent 1 at position i.
    Label: def.sf.monomial -/
noncomputable def Monomial.single (i : Fin N) : Monomial N := Finsupp.single i 1

/-- The polynomial corresponding to Monomial.single i is X i.
    Label: def.sf.monomial -/
@[simp]
theorem Monomial.toPoly_single (i : Fin N) :
    (Monomial.single i).toPoly = (X i : P K N) := by
  simp only [single, toPoly, MvPolynomial.X]

/-- The degree of a single variable monomial is 1.
    Label: def.sf.monomial -/
@[simp]
theorem Monomial.degree_single (i : Fin N) : (Monomial.single i).degree = 1 := by
  simp only [single, degree, Finsupp.sum_single_index]

/-- A single variable monomial is squarefree.
    Label: def.sf.monomial -/
theorem Monomial.isSquarefree_single (i : Fin N) : (Monomial.single i).IsSquarefree := by
  intro j
  simp only [single, Finsupp.single_apply]
  split_ifs <;> omega

/-- A single variable monomial is primal.
    Label: def.sf.monomial -/
theorem Monomial.isPrimal_single (i : Fin N) : (Monomial.single i).IsPrimal := by
  unfold IsPrimal single
  rw [Finsupp.support_single _ (one_ne_zero), card_singleton]

/-- Multiplication of monomials corresponds to addition of exponent vectors.
    Label: def.sf.monomial -/
theorem Monomial.toPoly_add (m₁ m₂ : Monomial N) :
    (m₁ + m₂).toPoly = (m₁.toPoly : P K N) * m₂.toPoly := by
  simp only [toPoly, monomial_mul_monomial, one_mul]

/-- The degree of a product of monomials is the sum of degrees.
    Label: def.sf.monomial -/
theorem Monomial.degree_add (m₁ m₂ : Monomial N) :
    (m₁ + m₂).degree = m₁.degree + m₂.degree := by
  simp only [degree]
  rw [Finsupp.sum_add_index']
  · intro _; rfl
  · intro _ _ _; ring

/-- A squarefree monomial has degree at most N.
    Label: def.sf.monomial -/
theorem Monomial.degree_le_of_isSquarefree (m : Monomial N) (hm : m.IsSquarefree) :
    m.degree ≤ N := by
  calc m.degree = m.support.sum m := m.degree_eq_support_sum
    _ ≤ m.support.sum (fun _ => 1) := Finset.sum_le_sum (fun i _ => hm i)
    _ = m.support.card := by simp
    _ ≤ Fintype.card (Fin N) := Finset.card_le_card (Finset.subset_univ _)
    _ = N := Fintype.card_fin N

/-- A primal monomial has support of size at most 1.
    Label: def.sf.monomial -/
theorem Monomial.support_card_le_one_of_isPrimal (m : Monomial N) (hm : m.IsPrimal) :
    m.support.card ≤ 1 := hm

/-- Characterization: a monomial is primal iff it's 0 or a power of a single variable.
    Label: def.sf.monomial -/
theorem Monomial.isPrimal_iff (m : Monomial N) :
    m.IsPrimal ↔ m = 0 ∨ ∃ i k, m = Finsupp.single i k ∧ 0 < k := by
  constructor
  · intro hm
    cases' Nat.lt_or_eq_of_le hm with h h
    · -- support is empty
      left
      simp only [Nat.lt_one_iff, Finset.card_eq_zero] at h
      exact Finsupp.support_eq_empty.mp h
    · -- support has exactly one element
      right
      rw [Finset.card_eq_one] at h
      obtain ⟨i, hi⟩ := h
      refine ⟨i, m i, ?_, ?_⟩
      · ext j
        simp only [Finsupp.single_apply]
        split_ifs with hji
        · rw [hji]
        · have : j ∉ m.support := by rw [hi]; simp only [mem_singleton]; exact fun h => hji h.symm
          simp only [Finsupp.mem_support_iff, not_not] at this
          exact this
      · have : i ∈ m.support := by rw [hi]; simp
        simp only [Finsupp.mem_support_iff] at this
        omega
  · intro h
    cases h with
    | inl h => rw [h]; exact Monomial.isPrimal_zero
    | inr h =>
      obtain ⟨i, k, rfl, hk⟩ := h
      unfold IsPrimal
      rw [Finsupp.support_single _ (Nat.pos_iff_ne_zero.mp hk), card_singleton]

/-- The monomial corresponding to a subset S ⊆ [N] is ∏_{i ∈ S} x_i.
    This is the squarefree monomial with support S.
    Label: def.sf.monomial -/
noncomputable def Monomial.ofFinset (s : Finset (Fin N)) : Monomial N :=
  s.sum (Finsupp.single · 1)

/-- The polynomial corresponding to Monomial.ofFinset s is ∏_{i ∈ s} X i.
    Label: def.sf.monomial -/
theorem Monomial.toPoly_ofFinset (s : Finset (Fin N)) :
    (Monomial.ofFinset s).toPoly = (∏ i ∈ s, X i : P K N) := by
  unfold ofFinset toPoly
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty, monomial_zero']
    rfl
  | @insert a s' h_not_mem ih =>
    rw [Finset.sum_insert h_not_mem, Finset.prod_insert h_not_mem]
    show monomial (Finsupp.single a 1 + ∑ x ∈ s', Finsupp.single x 1) 1 = X a * ∏ x ∈ s', X x
    have eq1 : monomial (Finsupp.single a 1 + ∑ x ∈ s', Finsupp.single x 1) (1 : K) =
               monomial (Finsupp.single a 1) 1 * monomial (∑ x ∈ s', Finsupp.single x 1) 1 := by
      rw [monomial_mul_monomial, one_mul]
    rw [eq1, ih]
    rfl

/-- Monomial.ofFinset gives a squarefree monomial.
    Label: def.sf.monomial -/
theorem Monomial.isSquarefree_ofFinset (s : Finset (Fin N)) :
    (Monomial.ofFinset s).IsSquarefree := by
  intro i
  simp only [ofFinset]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' h_not_mem ih =>
    rw [Finset.sum_insert h_not_mem]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with h
    · -- i = a (the inserted element)
      subst h
      have : (Finset.sum s' (fun x => Finsupp.single x 1)) a = 0 := by
        simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
        apply Finset.sum_eq_zero
        intro j hj
        simp only [ite_eq_right_iff, one_ne_zero]
        intro hja
        subst hja
        exact h_not_mem hj
      omega
    · -- i ≠ a
      have : Finsupp.single a 1 i = 0 := by simp [h]
      omega

/-- The degree of Monomial.ofFinset s is the cardinality of s.
    Label: def.sf.monomial -/
@[simp]
theorem Monomial.degree_ofFinset (s : Finset (Fin N)) :
    (Monomial.ofFinset s).degree = s.card := by
  simp only [degree, ofFinset]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' h_not_mem ih =>
    rw [Finset.sum_insert h_not_mem]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
    simp only [Finsupp.sum_single_index]
    rw [Finset.card_insert_of_notMem h_not_mem]
    omega

/-- The support of Monomial.ofFinset s equals s.
    Label: def.sf.monomial -/
theorem Monomial.support_ofFinset (s : Finset (Fin N)) :
    (Monomial.ofFinset s).support = s := by
  ext i
  simp only [Finsupp.mem_support_iff, ofFinset]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' h_not_mem ih =>
    rw [Finset.sum_insert h_not_mem, Finset.mem_insert]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    constructor
    · intro h
      by_contra hni
      push Not at hni
      have h1 : (if a = i then 1 else 0) = 0 := by simp only [ite_eq_right_iff, one_ne_zero]; exact fun h => (hni.1 h.symm).elim
      have h2 : (Finset.sum s' (fun x => Finsupp.single x 1)) i = 0 := by
        simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
        apply Finset.sum_eq_zero
        intro j hj
        simp only [ite_eq_right_iff, one_ne_zero]
        intro hji
        rw [hji] at hj
        exact hni.2 hj
      omega
    · intro h
      cases h with
      | inl h => simp [h]
      | inr h =>
        have : (Finset.sum s' (fun x => Finsupp.single x 1)) i ≠ 0 := by
          rw [ih]
          exact h
        omega

/-!
## Elementary Symmetric Polynomials (Definition def.sf.ehp (a))

e_n = sum of all squarefree monomials of degree n
    = ∑_{i₁ < i₂ < ... < i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}

In Mathlib, this is `MvPolynomial.esymm (Fin N) K n`.
-/

/-- The n-th elementary symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev e (n : ℕ) : P K N := esymm (Fin N) K n

/-- Elementary symmetric polynomials are symmetric.
    Label: def.sf.ehp -/
theorem e_isSymm (n : ℕ) : IsSymm (e (K := K) (N := N) n) := esymm_isSymmetric (Fin N) K n

/-!
## Complete Homogeneous Symmetric Polynomials (Definition def.sf.ehp (b))

h_n = sum of all monomials of degree n
    = ∑_{i₁ ≤ i₂ ≤ ... ≤ i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}

In Mathlib, this is `MvPolynomial.hsymm (Fin N) K n`.
-/

section WithDecidableEq

variable [DecidableEq (Fin N)]

/-- The n-th complete homogeneous symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev h (n : ℕ) : P K N := hsymm (Fin N) K n

/-- Complete homogeneous symmetric polynomials are symmetric.
    Label: def.sf.ehp -/
theorem h_isSymm (n : ℕ) : IsSymm (h (K := K) (N := N) n) := hsymm_isSymmetric (Fin N) K n

/-- h_0 = 1 (Example exa.sf.ehp.1 (e)).
    Label: exa.sf.ehp.1 -/
theorem h_zero : h (K := K) (N := N) 0 = 1 := hsymm_zero (Fin N) K

/-- h_1 = ∑ x_i (Example exa.sf.ehp.1 (d)).
    Label: exa.sf.ehp.1 -/
theorem h_one : h (K := K) (N := N) 1 = ∑ i, X i := hsymm_one (Fin N) K

end WithDecidableEq

/-!
## Power Sums (Definition def.sf.ehp (c))

p_n = x₁^n + x₂^n + ... + x_N^n  (for n > 0)
p_0 = 1
p_n = 0  (for n < 0)

In Mathlib, this is `MvPolynomial.psum (Fin N) K n`.
Note: Mathlib's definition has p_0 = N (the number of variables), not 1.
-/

/-- The n-th power sum symmetric polynomial.
    Label: def.sf.ehp -/
noncomputable abbrev p (n : ℕ) : P K N := psum (Fin N) K n

/-- Power sums are symmetric.
    Label: def.sf.ehp -/
theorem p_isSymm (n : ℕ) : IsSymm (p (K := K) (N := N) n) := psum_isSymmetric (Fin N) K n

/-!
## Basic Values (Example exa.sf.ehp.1)

(d) e_1 = h_1 = p_1 = x_1 + x_2 + ... + x_N
(e) e_0 = h_0 = 1, p_0 = N
(f) e_n = h_n = p_n = 0 for n < 0 (vacuously true for ℕ)
-/

/-- e_0 = 1 (Example exa.sf.ehp.1 (e)).
    Label: exa.sf.ehp.1 -/
theorem e_zero : e (K := K) (N := N) 0 = 1 := esymm_zero (Fin N) K

/-- p_0 = N (number of variables).
    Note: The source defines p_0 = 1, but Mathlib defines p_0 = N.
    Label: exa.sf.ehp.1 -/
theorem p_zero : p (K := K) (N := N) 0 = Fintype.card (Fin N) := psum_zero (Fin N) K

/-- e_1 = ∑ x_i (Example exa.sf.ehp.1 (d)).
    Label: exa.sf.ehp.1 -/
theorem e_one : e (K := K) (N := N) 1 = ∑ i, X i := esymm_one (Fin N) K

/-- p_1 = ∑ x_i (Example exa.sf.ehp.1 (d)).
    Label: exa.sf.ehp.1 -/
theorem p_one : p (K := K) (N := N) 1 = ∑ i, X i := psum_one (Fin N) K

/-!
## Integer-indexed versions (Definition def.sf.ehp)

The source defines e_n, h_n, p_n for all integers n ∈ ℤ.
For negative n, they are all 0. This section provides integer-indexed versions
that match the textbook definitions exactly.
-/

/-- Integer-indexed elementary symmetric polynomial.
    For n ∈ ℤ: e_n = esymm n if n ≥ 0, e_n = 0 if n < 0.
    This matches Definition def.sf.ehp (a) in the source.
    Label: def.sf.ehp -/
noncomputable def eZ (n : ℤ) : P K N :=
  if 0 ≤ n then e n.toNat else 0

/-- Integer-indexed complete homogeneous symmetric polynomial.
    For n ∈ ℤ: h_n = hsymm n if n ≥ 0, h_n = 0 if n < 0.
    This matches Definition def.sf.ehp (b) in the source.
    Label: def.sf.ehp -/
noncomputable def hZ [DecidableEq (Fin N)] (n : ℤ) : P K N :=
  if 0 ≤ n then h n.toNat else 0

/-- Integer-indexed power sum (textbook convention).
    For n ∈ ℤ: p'_n = psum n if n > 0, p'_0 = 1, p'_n = 0 if n < 0.
    This matches Definition def.sf.ehp (c) in the source.

    Note: Mathlib's psum has p_0 = N (number of variables), but the textbook
    defines p_0 = 1. We follow the textbook convention here.
    Label: def.sf.ehp -/
noncomputable def pZ (n : ℤ) : P K N :=
  if n > 0 then p n.toNat
  else if n = 0 then 1
  else 0

/-- e_n = 0 for negative n (Definition def.sf.ehp (a)).
    Label: def.sf.ehp -/
theorem eZ_neg {n : ℤ} (hn : n < 0) : eZ (K := K) (N := N) n = 0 := by
  simp only [eZ, not_le.mpr hn, ↓reduceIte]

/-- eZ agrees with e for non-negative integers.
    Label: def.sf.ehp -/
theorem eZ_of_nonneg {n : ℤ} (hn : 0 ≤ n) : eZ (K := K) (N := N) n = e n.toNat := by
  simp only [eZ, hn, ↓reduceIte]

/-- eZ n is symmetric for all n ∈ ℤ.
    Label: def.sf.ehp -/
theorem eZ_isSymmetric (n : ℤ) : (eZ (K := K) (N := N) n).IsSymmetric := by
  by_cases hn : 0 ≤ n
  · rw [eZ_of_nonneg hn]
    exact esymm_isSymmetric (Fin N) K n.toNat
  · rw [eZ_neg (not_le.mp hn)]
    exact IsSymmetric.zero

/-- h_n = 0 for negative n (Definition def.sf.ehp (b)).
    Label: def.sf.ehp -/
theorem hZ_neg [DecidableEq (Fin N)] {n : ℤ} (hn : n < 0) : hZ (K := K) (N := N) n = 0 := by
  simp only [hZ, not_le.mpr hn, ↓reduceIte]

/-- hZ agrees with h for non-negative integers.
    Label: def.sf.ehp -/
theorem hZ_of_nonneg [DecidableEq (Fin N)] {n : ℤ} (hn : 0 ≤ n) :
    hZ (K := K) (N := N) n = h n.toNat := by
  simp only [hZ, hn, ↓reduceIte]

/-- hZ n is symmetric for all n ∈ ℤ.
    Label: def.sf.ehp -/
theorem hZ_isSymmetric [DecidableEq (Fin N)] (n : ℤ) : (hZ (K := K) (N := N) n).IsSymmetric := by
  by_cases hn : 0 ≤ n
  · rw [hZ_of_nonneg hn]
    exact hsymm_isSymmetric (Fin N) K n.toNat
  · rw [hZ_neg (not_le.mp hn)]
    exact IsSymmetric.zero

/-- p'_n = 0 for negative n (Definition def.sf.ehp (c)).
    Label: def.sf.ehp -/
theorem pZ_neg {n : ℤ} (hn : n < 0) : pZ (K := K) (N := N) n = 0 := by
  simp only [pZ, not_lt.mpr (le_of_lt hn), ↓reduceIte, ne_of_lt hn]

/-- p'_0 = 1 (Definition def.sf.ehp (c)).
    Label: def.sf.ehp -/
theorem pZ_zero : pZ (K := K) (N := N) 0 = 1 := by
  simp only [pZ, lt_irrefl, ↓reduceIte]

/-- pZ agrees with psum for positive integers.
    Label: def.sf.ehp -/
theorem pZ_of_pos {n : ℤ} (hn : 0 < n) : pZ (K := K) (N := N) n = p n.toNat := by
  simp only [pZ, hn, ↓reduceIte]

/-- pZ n is symmetric for all n ∈ ℤ.
    Label: def.sf.ehp -/
theorem pZ_isSymmetric (n : ℤ) : (pZ (K := K) (N := N) n).IsSymmetric := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · rw [pZ_neg hn]
    exact IsSymmetric.zero
  · rw [hn, pZ_zero]
    exact IsSymmetric.one
  · rw [pZ_of_pos hn]
    exact psum_isSymmetric (Fin N) K n.toNat

/-!
## Alternative characterizations (Definition def.sf.ehp)

The defining formulas for e_n, h_n, p_n as sums over tuples.
-/

/-- e_n is the sum over all n-element subsets of [N] of the product of variables.
    This is the defining formula in Definition def.sf.ehp (a):
    e_n = ∑_{i₁ < i₂ < ... < i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}
    Label: def.sf.ehp -/
theorem e_eq_sum_prod_subsets (n : ℕ) :
    e (K := K) (N := N) n = ∑ s ∈ powersetCard n (univ : Finset (Fin N)), ∏ i ∈ s, X i := by
  rfl

section WithDecidableEq'

variable [DecidableEq (Fin N)]

/-- h_n is the sum over all symmetric n-tuples (multisets) of [N] of the product of variables.
    This is the defining formula in Definition def.sf.ehp (b):
    h_n = ∑_{i₁ ≤ i₂ ≤ ... ≤ i_n} x_{i₁} x_{i₂} ⋯ x_{i_n}
    Label: def.sf.ehp -/
theorem h_eq_sum_prod_sym (n : ℕ) :
    h (K := K) (N := N) n = ∑ s : Sym (Fin N) n, (s.1.map X).prod := by
  rfl

end WithDecidableEq'

/-- p_n is the sum of n-th powers of all variables.
    This is the defining formula in Definition def.sf.ehp (c):
    p_n = x₁^n + x₂^n + ... + x_N^n
    Label: def.sf.ehp -/
theorem p_eq_sum_pow (n : ℕ) :
    p (K := K) (N := N) n = ∑ i : Fin N, X i ^ n := by
  rfl

/-!
## Proposition prop.sf.en=0: e_n = 0 for n > N

For n > N, there are no n distinct elements in [N], so e_n = 0.
-/

/-- e_n = 0 for n > N (Proposition prop.sf.en=0).
    Label: prop.sf.en=0 -/
theorem e_eq_zero_of_gt {n : ℕ} (hn : N < n) : e (K := K) (N := N) n = 0 := by
  simp only [e, esymm]
  apply Finset.sum_eq_zero
  intro s hs
  rw [mem_powersetCard] at hs
  have : #s ≤ Fintype.card (Fin N) := card_le_card hs.1
  simp only [Fintype.card_fin] at this
  omega

/-!
## Adding a Variable Recurrence

The elementary symmetric polynomial e_n(x₁,...,x_N,y) satisfies the recurrence:
  e_n(x₁,...,x_N,y) = e_n(x₁,...,x_N) + y * e_{n-1}(x₁,...,x_N)

This is fundamental for inductive proofs about symmetric polynomials.
-/

/-- Helper lemma: the image of a preimage under castSucc equals the original set
    when the set doesn't contain Fin.last N. -/
private lemma image_preimage_eq_of_not_mem_last {a : Finset (Fin (N + 1))} (hlast : Fin.last N ∉ a) :
    (a.preimage Fin.castSucc (Fin.castSucc_injective N).injOn).image Fin.castSucc = a := by
  ext x; simp only [mem_image, mem_preimage]
  constructor
  · intro ⟨y, hy, hyx⟩; rwa [← hyx]
  · intro hx
    have hne : x ≠ Fin.last N := fun h => hlast (h ▸ hx)
    exact ⟨x.castPred hne, by simp [Fin.castSucc_castPred]; exact hx, Fin.castSucc_castPred x hne⟩

/-- Helper lemma: the image of a preimage of an erased set under castSucc equals the erased set. -/
private lemma image_preimage_erase_eq {a : Finset (Fin (N + 1))} :
    ((a.erase (Fin.last N)).preimage Fin.castSucc (Fin.castSucc_injective N).injOn).image Fin.castSucc = a.erase (Fin.last N) := by
  ext x; simp only [mem_image, mem_preimage, mem_erase, ne_eq]
  constructor
  · intro ⟨y, hy, hyx⟩; rwa [← hyx]
  · intro ⟨hne, hx⟩
    refine ⟨x.castPred hne, ?_, Fin.castSucc_castPred x hne⟩
    simp only [Fin.castSucc_castPred]
    exact ⟨hne, hx⟩

/-- Adding a variable: e_{n+1}(x₁,...,x_N,y) = e_{n+1}(x₁,...,x_N) + y * e_n(x₁,...,x_N).
    This is the recurrence for computing elementary symmetric polynomials.
    Label: def.sf.ehp -/
theorem esymm_succ_add_var' (n : ℕ) :
    esymm (Fin (N + 1)) K (n + 1) = 
    rename Fin.castSucc (esymm (Fin N) K (n + 1)) + 
    X (Fin.last N) * rename Fin.castSucc (esymm (Fin N) K n) := by
  simp only [esymm, map_sum, map_prod, rename_X]
  have h_partition : (powersetCard (n + 1) (univ : Finset (Fin (N + 1)))) = 
      (powersetCard (n + 1) univ).filter (Fin.last N ∉ ·) ∪ 
      (powersetCard (n + 1) univ).filter (Fin.last N ∈ ·) := by
    ext s; simp only [mem_union, mem_filter]; tauto
  rw [h_partition, sum_union]
  · congr 1
    · -- First sum: subsets not containing Fin.last N
      refine Finset.sum_bij' 
        (fun a _ => a.preimage Fin.castSucc (Fin.castSucc_injective N).injOn)
        (fun a _ => a.image Fin.castSucc)
        ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha ⊢
        obtain ⟨hcard, hlast⟩ := ha
        calc #(a.preimage Fin.castSucc (Fin.castSucc_injective N).injOn) 
            = #((a.preimage Fin.castSucc (Fin.castSucc_injective N).injOn).image Fin.castSucc) := by
                rw [card_image_of_injective _ (Fin.castSucc_injective N)]
            _ = #a := by rw [image_preimage_eq_of_not_mem_last hlast]
            _ = n + 1 := hcard
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and, mem_image] at ha ⊢
        constructor
        · rw [card_image_of_injective _ (Fin.castSucc_injective N)]; exact ha
        · intro ⟨y, _, hy⟩; exact Fin.castSucc_ne_last y hy
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha
        exact image_preimage_eq_of_not_mem_last ha.2
      · intro a _; ext x
        simp only [mem_preimage, mem_image, Fin.castSucc_inj]
        exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha
        conv_lhs => rw [← image_preimage_eq_of_not_mem_last ha.2, prod_image (Fin.castSucc_injective N).injOn]
    · -- Second sum: subsets containing Fin.last N
      rw [mul_sum]
      refine Finset.sum_bij' 
        (fun a _ => (a.erase (Fin.last N)).preimage Fin.castSucc (Fin.castSucc_injective N).injOn)
        (fun a _ => insert (Fin.last N) (a.image Fin.castSucc))
        ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha ⊢
        obtain ⟨hcard, hlast⟩ := ha
        have h_erase_card : #(a.erase (Fin.last N)) = n := by rw [card_erase_of_mem hlast]; omega
        calc #((a.erase (Fin.last N)).preimage Fin.castSucc (Fin.castSucc_injective N).injOn)
            = #(((a.erase (Fin.last N)).preimage Fin.castSucc (Fin.castSucc_injective N).injOn).image Fin.castSucc) := by
                rw [card_image_of_injective _ (Fin.castSucc_injective N)]
            _ = #(a.erase (Fin.last N)) := by rw [image_preimage_erase_eq]
            _ = n := h_erase_card
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha ⊢
        constructor
        · rw [card_insert_of_notMem]
          · rw [card_image_of_injective _ (Fin.castSucc_injective N)]; omega
          · simp only [mem_image]; intro ⟨y, _, hy⟩; exact Fin.castSucc_ne_last y hy
        · exact mem_insert_self _ _
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha
        obtain ⟨_, hlast⟩ := ha
        ext x; simp only [mem_insert, mem_image, mem_preimage, mem_erase, ne_eq]
        constructor
        · intro h
          rcases h with rfl | ⟨y, hy, hyx⟩
          · exact hlast
          · rw [← hyx]; exact hy.2
        · intro hx
          by_cases hne : x = Fin.last N
          · left; exact hne
          · right
            refine ⟨x.castPred hne, ?_, Fin.castSucc_castPred x hne⟩
            simp only [Fin.castSucc_castPred]
            exact ⟨hne, hx⟩
      · intro a _
        have h_erase : (insert (Fin.last N) (a.image Fin.castSucc)).erase (Fin.last N) = a.image Fin.castSucc := by
          apply erase_insert
          simp only [mem_image]; intro ⟨y, _, hy⟩; exact Fin.castSucc_ne_last y hy
        simp only [h_erase]
        ext x; simp only [mem_preimage, mem_image, Fin.castSucc_inj]
        constructor
        · intro ⟨y, hy, hyx⟩; rw [← hyx]; exact hy
        · intro hx; exact ⟨x, hx, rfl⟩
      · intro a ha
        simp only [mem_filter, mem_powersetCard, subset_univ, true_and] at ha
        obtain ⟨_, hlast⟩ := ha
        conv_lhs => rw [← insert_erase hlast, prod_insert (notMem_erase _ _)]
        congr 1
        conv_lhs => rw [← image_preimage_erase_eq, prod_image (Fin.castSucc_injective N).injOn]
  · simp only [disjoint_filter]; intro s _ hs; simp [hs]

/-- Adding a variable: e_n(x₁,...,x_N,y) = e_n(x₁,...,x_N) + y * e_{n-1}(x₁,...,x_N).
    This is the recurrence for computing elementary symmetric polynomials.
    For n = 0, the second term vanishes since e_{-1} = 0 by convention (but Nat subtraction
    gives e_0 instead, so we use a conditional).
    Label: def.sf.ehp -/
theorem esymm_succ_add_var (n : ℕ) :
    esymm (Fin (N + 1)) K n = 
    rename Fin.castSucc (esymm (Fin N) K n) + 
    if n = 0 then 0 else X (Fin.last N) * rename Fin.castSucc (esymm (Fin N) K (n - 1)) := by
  cases n with
  | zero => simp only [esymm_zero, map_one, ↓reduceIte, add_zero]
  | succ n => simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]; exact esymm_succ_add_var' n

/-!
## Newton-Girard Formulas (Theorem thm.sf.NG)

For any positive integer n:
(eq.thm.sf.NG.eh) ∑_{j=0}^n (-1)^j e_j h_{n-j} = 0
(eq.thm.sf.NG.ep) ∑_{j=1}^n (-1)^{j-1} e_{n-j} p_j = n · e_n
(eq.thm.sf.NG.hp) ∑_{j=1}^n h_{n-j} p_j = n · h_n

These are implemented in Mathlib as `MvPolynomial.mul_esymm_eq_sum` and related theorems.
-/

/-- Newton-Girard formula: recurrence for elementary symmetric polynomials.
    k * e_k = (-1)^{k+1} * ∑_{a ∈ antidiagonal k, a.1 < k} (-1)^{a.1} * e_{a.1} * p_{a.2}
    (Theorem thm.sf.NG, equation eq.thm.sf.NG.ep).
    Label: thm.sf.NG -/
theorem newtonGirard_esymm (k : ℕ) :
    (k : P K N) * e k = (-1 : P K N) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1 : P K N) ^ a.1 * e a.1 * p a.2 :=
  mul_esymm_eq_sum (Fin N) K k

/-- Newton-Girard formula: recurrence for power sums.
    p_k = (-1)^{k+1} * k * e_k - ∑_{a ∈ antidiagonal k, 0 < a.1 < k} (-1)^{a.1} * e_{a.1} * p_{a.2}
    (Theorem thm.sf.NG, equation eq.thm.sf.NG.ep).
    Label: thm.sf.NG -/
theorem newtonGirard_psum (k : ℕ) (hk : 0 < k) :
    p (K := K) (N := N) k = (-1 : P K N) ^ (k + 1) * (k : P K N) * e k -
      ∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k, (-1 : P K N) ^ a.fst * e a.1 * p a.2 :=
  psum_eq_mul_esymm_sub_sum (Fin N) K k hk

section WithDecidableEq'

variable [DecidableEq (Fin N)]

omit [DecidableEq (Fin N)] in
/-- Coefficient of (1 - X * C(x_i)) in power series.
    Helper lemma for Newton-Girard formula.
    Note: This lemma doesn't actually use DecidableEq (Fin N). -/
private lemma coeff_one_sub_X_mul_C (i : Fin N) (a : ℕ) :
    PowerSeries.coeff a (1 - PowerSeries.X * PowerSeries.C (X i : P K N)) =
    if a = 0 then 1 else if a = 1 then -(X i) else 0 := by
  simp only [map_sub, PowerSeries.coeff_one]
  cases a with
  | zero => simp
  | succ a =>
    simp only [ite_eq_right (Nat.succ_ne_zero a)]
    cases a with
    | zero =>
      rw [PowerSeries.coeff_mul]
      simp only [PowerSeries.coeff_X, PowerSeries.coeff_C]
      rw [show antidiagonal 1 = {(0, 1), (1, 0)} by decide]
      simp only [Finset.sum_pair (by decide : (0, 1) ≠ (1, 0))]
      simp
    | succ a =>
      simp only [ite_eq_right (by omega : a + 1 + 1 ≠ 1)]
      rw [PowerSeries.coeff_mul]
      simp only [PowerSeries.coeff_X, PowerSeries.coeff_C]
      simp only [zero_sub, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro ⟨k, l⟩ hkl
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
      by_cases hk1 : k = 1
      · subst hk1
        simp only [ite_true, one_mul]
        have hl : l = a + 1 := by omega
        simp only [ite_eq_right (by omega : l ≠ 0)]
      · simp only [ite_eq_right hk1, zero_mul]

omit [DecidableEq (Fin N)] in
/-- Geometric series identity: (1 - t·x) * (∑_{k≥0} t^k x^k) = 1.
    This is the key lemma for the generating function proof of Newton-Girard. -/
lemma geom_series_mul_one_sub (i : Fin N) :
    (1 - PowerSeries.X * PowerSeries.C (X i : P K N)) *
    PowerSeries.mk (fun k => (X i : P K N) ^ k) = 1 := by
  ext n
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_one, PowerSeries.coeff_mk]
  cases n with
  | zero =>
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, pow_zero, mul_one]
    simp [coeff_one_sub_X_mul_C]
  | succ n =>
    simp only [ite_eq_right (Nat.succ_ne_zero n)]
    simp_rw [coeff_one_sub_X_mul_C]
    have h0 : (0, n + 1) ∈ antidiagonal (n + 1) := by simp [Finset.HasAntidiagonal.mem_antidiagonal]
    have h1 : (1, n) ∈ antidiagonal (n + 1) := by simp [Finset.HasAntidiagonal.mem_antidiagonal]; omega
    rw [← Finset.sum_filter_add_sum_filter_not (antidiagonal (n + 1)) (fun x => x.1 = 0)]
    have hfilt0 : Finset.filter (fun x => x.1 = 0) (antidiagonal (n + 1)) = {(0, n + 1)} := by
      ext x
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton,
        Prod.ext_iff]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
      · intro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
    rw [hfilt0, Finset.sum_singleton]
    simp only [ite_true, one_mul]
    rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.filter (fun x => ¬x.1 = 0) (antidiagonal (n + 1))) (fun x => x.1 = 1)]
    have hfilt1 : Finset.filter (fun x => x.1 = 1)
        (Finset.filter (fun x => ¬x.1 = 0) (antidiagonal (n + 1))) = {(1, n)} := by
      ext x
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton,
        Prod.ext_iff]
      constructor
      · intro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, by omega⟩
      · intro ⟨h1, h2⟩; exact ⟨⟨by omega, by omega⟩, h1⟩
    rw [hfilt1, Finset.sum_singleton]
    simp only [ite_eq_right (by decide : (1 : ℕ) ≠ 0), ite_true, neg_mul]
    have hrest : ∑ x ∈ Finset.filter (fun x => ¬x.1 = 1)
        (Finset.filter (fun x => ¬x.1 = 0) (antidiagonal (n + 1))),
        (if x.1 = 0 then 1 else if x.1 = 1 then -(X i : P K N) else 0) * (X i) ^ x.2 = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hx
      simp [hx.1.2, hx.2]
    rw [hrest, add_zero]
    ring_nf

omit [DecidableEq (Fin N)] in
/-- Product of geometric series equals 1 when multiplied by ∏(1 - t·x_i).
    This is the generating function identity E(t) * H(t) = 1. -/
lemma prod_geom_series_mul_prod_one_sub :
    (∏ i : Fin N, (1 - PowerSeries.X * PowerSeries.C (X i : P K N))) *
    (∏ i : Fin N, PowerSeries.mk (fun k => (X i : P K N) ^ k)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  simp only [geom_series_mul_one_sub, Finset.prod_const_one]

omit [DecidableEq (Fin N)] in
/-- Helper: (-1)^j as a polynomial equals C((-1)^j).
    Used in coefficient extraction for Newton-Girard formula. -/
private lemma neg_one_pow_poly_eq_C (j : ℕ) :
    ((-1 : Polynomial (P K N)) ^ j) = Polynomial.C ((-1 : P K N) ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Polynomial.C_mul, Polynomial.C_neg, Polynomial.C_1]

omit [DecidableEq (Fin N)] in
/-- E(t) as PowerSeries equals E(t) as Polynomial coerced.
    This connects the polynomial generating function to power series. -/
private lemma E_powerseries_eq_poly_coe :
    (∏ i : Fin N, (1 - PowerSeries.X * PowerSeries.C (X i : P K N) : PowerSeries (P K N))) =
    ((∏ i : Fin N, ((1 - Polynomial.X * Polynomial.C (X i)) : Polynomial (P K N))) : PowerSeries (P K N)) := by
  simp_rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C]

/-- Helper for esymm_genfunc: product of negations. -/
private lemma prod_neg_eq' {α R : Type*} [DecidableEq α] [CommRing R] (s : Finset α) (f : α → R) :
    ∏ i ∈ s, (-f i) = (-1 : R) ^ #s * ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp [prod_empty, pow_zero]
  | insert x s ha ih =>
    simp only [prod_insert ha, card_insert_eq_ite, ite_eq_right ha, pow_succ]
    rw [ih]
    ring

/-- Generating function for elementary symmetric polynomials (Proposition prop.sf.e-h-FPS (a)).
    ∏_{i=1}^N (1 - t·x_i) = ∑_{n=0}^N (-1)^n t^n e_n
    This is placed here so it can be used in newtonGirard_eh.
    Label: prop.sf.e-h-FPS -/
theorem esymm_genfunc :
    ∏ i : Fin N, (1 - Polynomial.X * Polynomial.C (X i : P K N)) =
    ∑ n ∈ range (N + 1),
      (-1 : Polynomial (P K N)) ^ n * Polynomial.X ^ n * Polynomial.C (e (K := K) (N := N) n) := by
  -- Rewrite using prod_one_add with f i = -X * C(x_i)
  conv_lhs =>
    arg 2
    ext i
    rw [show (1 : Polynomial (P K N)) - Polynomial.X * Polynomial.C (X i : P K N) =
            (1 : Polynomial (P K N)) + (-(Polynomial.X * Polynomial.C (X i : P K N))) by ring]
  rw [prod_one_add]
  -- Now we have: ∑ t ∈ powerset univ, ∏ i ∈ t, (-(X * C(x_i)))
  -- Use powerset_card_biUnion to group by cardinality
  rw [powerset_card_biUnion, sum_biUnion]
  · -- Now: ∑ k ∈ range (card univ + 1), ∑ t ∈ powersetCard k univ, ∏ i ∈ t, (-(X * C(x_i)))
    rw [show #(univ : Finset (Fin N)) = N by simp]
    apply sum_congr rfl
    intro k hk
    -- For each k, simplify the product
    have h1 : ∀ t ∈ powersetCard k (univ : Finset (Fin N)),
        ∏ i ∈ t, (-(Polynomial.X * Polynomial.C (X i : P K N))) =
        (-1 : Polynomial (P K N)) ^ k * Polynomial.X ^ k * Polynomial.C (∏ i ∈ t, X i) := by
      intro t ht
      rw [mem_powersetCard] at ht
      rw [prod_neg_eq', ht.2]
      rw [prod_mul_distrib]
      rw [prod_const, ht.2]
      rw [map_prod]
      ring
    rw [sum_congr rfl h1]
    -- Factor out the constant terms
    simp_rw [← mul_sum]
    congr 1
    rw [← map_sum]
    -- Now we need: ∑ t ∈ powersetCard k univ, ∏ i ∈ t, x_i = e_k
    simp only [e, esymm]
  · -- Show the powersetCard sets are pairwise disjoint
    exact (pairwise_disjoint_powersetCard (univ : Finset (Fin N))).set_pairwise _

/-- Helper: product of powers equals multiset product.
    For s : Sym (Fin N) n, ∏ i, X_i^(count i s) = (s.1.map X).prod -/
private lemma prod_pow_count_eq_map_prod (n : ℕ) (s : Sym (Fin N) n) :
    ∏ i : Fin N, (X i : P K N) ^ (s : Multiset (Fin N)).count i = (s.1.map X).prod := by
  rw [prod_multiset_map_count]
  symm
  apply prod_subset
  · exact fun i _ => mem_univ i
  · intro i _ hi
    rw [Multiset.mem_toFinset] at hi
    rw [Multiset.count_eq_zero.mpr hi, pow_zero]

/-- Newton-Girard formula relating e and h: ∑_{j=0}^n (-1)^j e_j h_{n-j} = 0 for n > 0.
    (Theorem thm.sf.NG, equation eq.thm.sf.NG.eh).

    The proof uses the generating function identity:
    E(t) * H(t) = 1, where E(t) = ∏_i (1 - t·x_i) and H(t) = ∑_n t^n h_n.

    Since E(t) = ∑_n (-1)^n t^n e_n, the coefficient of t^n in E(t) * H(t) is:
    ∑_{j=0}^n (-1)^j e_j h_{n-j}

    For n > 0, this coefficient must be 0 (since E(t) * H(t) = 1).

    Label: thm.sf.NG -/
theorem newtonGirard_eh (n : ℕ) (hn : 0 < n) :
    ∑ j ∈ range (n + 1), (-1 : P K N) ^ j * e (K := K) (N := N) j * h (n - j) = 0 := by
  -- The proof follows from the generating function identity E(t) * H(t) = 1.
  -- We have shown prod_geom_series_mul_prod_one_sub, which establishes this identity.
  -- The coefficient extraction argument shows that for n > 0:
  -- ∑_{j=0}^n (-1)^j e_j h_{n-j} = coeff n (E(t) * H(t)) = coeff n 1 = 0

  -- Helper: coefficient of t^j in E(t) = ∏_i (1 - t·x_i) is (-1)^j * e_j for j ≤ N, 0 otherwise
  have coeff_E : ∀ j : ℕ,
      PowerSeries.coeff j (∏ i : Fin N, (1 - PowerSeries.X * PowerSeries.C (X i : P K N))) =
      if j ≤ N then (-1 : P K N) ^ j * e (K := K) (N := N) j else 0 := by
    intro j
    -- Step 1: Convert PowerSeries product to Polynomial product
    let E_ps := ∏ i : Fin N, (1 - PowerSeries.X * PowerSeries.C (X i : P K N))
    let E_poly := ∏ i : Fin N, ((1 : Polynomial (P K N)) - Polynomial.X * Polynomial.C (X i))
    have h_eq : E_ps = (E_poly : PowerSeries (P K N)) := by
      simp only [E_ps, E_poly]
      conv_lhs =>
        arg 2
        ext i
        rw [← Polynomial.coe_one, ← Polynomial.coe_X, ← Polynomial.coe_C (X i),
            ← Polynomial.coe_mul, ← Polynomial.coe_sub]
      simp only [← Polynomial.coeToPowerSeries.ringHom_apply]
      rw [map_prod]
    change PowerSeries.coeff j E_ps = _
    rw [h_eq, Polynomial.coeff_coe]
    -- Step 2: Prove E_poly = ∑ k, (-1)^k * X^k * C(e_k) inline
    -- This is the content of esymm_genfunc
    have h_genfunc : E_poly = ∑ k ∈ range (N + 1),
        (-1 : Polynomial (P K N)) ^ k * Polynomial.X ^ k * Polynomial.C (e (K := K) (N := N) k) := by
      simp only [E_poly]
      -- Rewrite using prod_one_add with f i = -X * C(x_i)
      conv_lhs =>
        arg 2
        ext i
        rw [show (1 : Polynomial (P K N)) - Polynomial.X * Polynomial.C (X i : P K N) =
                (1 : Polynomial (P K N)) + (-(Polynomial.X * Polynomial.C (X i : P K N))) by ring]
      rw [prod_one_add]
      -- Use powerset_card_biUnion to group by cardinality
      rw [powerset_card_biUnion, sum_biUnion]
      · rw [show #(univ : Finset (Fin N)) = N by simp]
        apply sum_congr rfl
        intro k _
        have h1 : ∀ t ∈ powersetCard k (univ : Finset (Fin N)),
            ∏ i ∈ t, (-(Polynomial.X * Polynomial.C (X i : P K N))) =
            (-1 : Polynomial (P K N)) ^ k * Polynomial.X ^ k * Polynomial.C (∏ i ∈ t, X i) := by
          intro t ht
          rw [mem_powersetCard] at ht
          have hprod_neg : ∀ (s : Finset (Fin N)), ∏ i ∈ s, (-(Polynomial.X * Polynomial.C (X i : P K N))) =
              (-1 : Polynomial (P K N)) ^ #s * ∏ i ∈ s, (Polynomial.X * Polynomial.C (X i)) := by
            intro s
            induction s using Finset.induction_on with
            | empty => simp [prod_empty, pow_zero]
            | insert x s' ha ih =>
              simp only [prod_insert ha, card_insert_eq_ite, ite_eq_right ha, pow_succ]
              rw [ih]
              ring
          rw [hprod_neg t, ht.2]
          rw [prod_mul_distrib]
          rw [prod_const, ht.2]
          rw [map_prod]
          ring
        rw [sum_congr rfl h1]
        simp_rw [← mul_sum]
        congr 1
        rw [← map_sum]
        simp only [e, esymm]
      · exact (pairwise_disjoint_powersetCard (univ : Finset (Fin N))).set_pairwise _
    show E_poly.coeff j = _
    rw [h_genfunc]
    -- Step 3: Extract coefficient from the sum
    rw [Polynomial.finsetSum_coeff]
    simp_rw [neg_one_pow_poly_eq_C]
    -- Step 4: Rearrange and extract coefficients
    conv_lhs =>
      arg 2
      ext n
      rw [show Polynomial.C ((-1 : P K N) ^ n) * Polynomial.X ^ n * Polynomial.C (e (K := K) (N := N) n) =
              Polynomial.X ^ n * Polynomial.C ((-1 : P K N) ^ n * e (K := K) (N := N) n) by
        rw [mul_comm (Polynomial.C _) (Polynomial.X ^ n), mul_assoc, ← Polynomial.C_mul]]
    simp only [Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]
    -- Step 5: Split based on whether j ≤ N
    split_ifs with h
    · -- j ≤ N: exactly one term contributes (n = j)
      rw [Finset.sum_eq_single j]
      · simp only [le_refl, ite_true, Nat.sub_self, ite_true]
      · intro k hk hkj
        simp only [Finset.mem_range] at hk
        by_cases hle : k ≤ j
        · simp only [hle, ite_true]
          have hne : j - k ≠ 0 := by omega
          simp [hne]
        · simp [hle]
      · intro hj
        simp only [Finset.mem_range] at hj
        omega
    · -- j > N: no terms contribute
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_range] at hk
      by_cases hle : k ≤ j
      · simp only [hle, ite_true]
        by_cases hkj : k = j
        · subst hkj; omega
        · have hne : j - k ≠ 0 := by omega
          simp [hne]
      · simp [hle]


  -- Helper: coefficient of t^n in H_raw(t) = ∏_i (∑_k t^k x_i^k) is h_n
  have coeff_H : ∀ m : ℕ,
      PowerSeries.coeff m (∏ i : Fin N, PowerSeries.mk (fun k => (X i : P K N) ^ k)) =
      h (K := K) (N := N) m := by
    intro m
    -- Use the multinomial expansion via PowerSeries.coeff_prod
    rw [PowerSeries.coeff_prod]
    simp only [PowerSeries.coeff_mk]
    simp only [h, hsymm]
    -- Now: ∑ f ∈ finsuppAntidiag univ m, ∏ i, (X i)^(f i) = ∑ s : Sym (Fin N) m, (s.1.map X).prod
    -- Use Finset.sum_bij' with the bijection via Sym.equivNatSum
    refine Finset.sum_bij'
      -- Forward: f ↦ (Sym.equivNatSum).symm f
      (fun f hf => (Sym.equivNatSum (Fin N) m).symm ⟨f, by
        rw [Finset.mem_finsuppAntidiag'] at hf
        exact hf.1⟩)
      -- Backward: s ↦ (Sym.equivNatSum s).1
      (fun s _ => (Sym.equivNatSum (Fin N) m s).1)
      -- Forward lands in Finset.univ
      (fun f hf => Finset.mem_univ _)
      -- Backward lands in finsuppAntidiag
      (fun s _ => by
        rw [Finset.mem_finsuppAntidiag']
        constructor
        · exact (Sym.equivNatSum (Fin N) m s).2
        · exact Finset.subset_univ _)
      -- Round-trip 1
      (fun f hf => by simp)
      -- Round-trip 2
      (fun s hs => by simp)
      -- Values match
      (fun f hf => by
        have hf' : f.sum (fun _ => id) = m := by
          rw [Finset.mem_finsuppAntidiag'] at hf
          exact hf.1
        let s := (Sym.equivNatSum (Fin N) m).symm ⟨f, hf'⟩
        -- Show f i = (s : Multiset).count i
        have heq : ∀ i, f i = (s : Multiset (Fin N)).count i := by
          intro i
          simp only [s]
          rw [Sym.coe_equivNatSum_symm_apply]
          exact (Finsupp.count_toMultiset f i).symm
        simp_rw [heq]
        -- Use prod_pow_count_eq_map_prod
        exact prod_pow_count_eq_map_prod m s)

  -- Extract coefficient n from E * H = 1
  have h_prod := prod_geom_series_mul_prod_one_sub (K := K) (N := N)
  have h_coeff : PowerSeries.coeff n
      ((∏ i : Fin N, (1 - PowerSeries.X * PowerSeries.C (X i : P K N))) *
       (∏ i : Fin N, PowerSeries.mk (fun k => (X i : P K N) ^ k))) =
      PowerSeries.coeff n (1 : PowerSeries (P K N)) := by rw [h_prod]
  simp only [PowerSeries.coeff_one, ite_eq_right (ne_of_gt hn)] at h_coeff

  -- Use convolution formula
  rw [PowerSeries.coeff_mul] at h_coeff

  -- Substitute coefficient identities
  conv at h_coeff =>
    lhs
    arg 2
    ext p
    rw [coeff_E p.1, coeff_H p.2]

  -- Simplify: for j > N, e_j = 0, so we can drop the condition
  have h_simp : ∀ p ∈ antidiagonal n,
      (if p.1 ≤ N then (-1 : P K N) ^ p.1 * e (K := K) (N := N) p.1 else 0) * h (K := K) (N := N) p.2 =
      (-1 : P K N) ^ p.1 * e (K := K) (N := N) p.1 * h (K := K) (N := N) p.2 := by
    intro p _
    split_ifs with hle
    · ring
    · push Not at hle
      have he0 : e (K := K) (N := N) p.1 = 0 := e_eq_zero_of_gt hle
      simp [he0]
  rw [Finset.sum_congr rfl h_simp] at h_coeff

  -- Convert antidiagonal sum to range sum
  have h_eq : ∑ j ∈ range (n + 1), (-1 : P K N) ^ j * e (K := K) (N := N) j * h (K := K) (N := N) (n - j) =
      ∑ x ∈ antidiagonal n, (-1 : P K N) ^ x.1 * e (K := K) (N := N) x.1 * h (K := K) (N := N) x.2 := by
    rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (-1 : P K N) ^ i * e (K := K) (N := N) i * h (K := K) (N := N) j)]
  rw [h_eq, h_coeff]

/-- Key lemma: For any multiset s of size m, the sum of counts over all elements equals m.
    This is used in the proof of the Newton-Girard formula for h and p.
    Label: thm.sf.NG -/
theorem sum_count_eq_card (m : ℕ) (s : Sym (Fin N) m) : ∑ i : Fin N, s.1.count i = m := by
  have h1 : s.1.card = m := s.2
  calc ∑ i : Fin N, s.1.count i
      = ∑ i ∈ s.1.toFinset, s.1.count i + ∑ i ∈ s.1.toFinsetᶜ, s.1.count i := by
        rw [Finset.sum_add_sum_compl]
    _ = ∑ i ∈ s.1.toFinset, s.1.count i + 0 := by
        congr 1
        apply Finset.sum_eq_zero
        intro i hi
        simp only [Finset.mem_compl, Multiset.mem_toFinset] at hi
        exact Multiset.count_eq_zero.mpr hi
    _ = s.1.card := by rw [add_zero]; exact Multiset.toFinset_sum_count_eq s.1
    _ = m := h1

/-! ### Helper lemmas for the bijection in Newton-Girard hp formula -/

/-- Helper: replicate n a ≤ s iff n ≤ count a s. -/
private lemma replicate_le_iff_count {α : Type*} [DecidableEq α] (a : α) (m : ℕ) (s : Multiset α) :
    Multiset.replicate m a ≤ s ↔ m ≤ s.count a := by
  constructor
  · intro h
    calc m = (Multiset.replicate m a).count a := by simp
      _ ≤ s.count a := Multiset.count_le_of_le a h
  · intro h
    rw [Multiset.le_iff_count]
    intro b
    simp only [Multiset.count_replicate]
    split_ifs with heq
    · subst heq; exact h
    · exact Nat.zero_le _

/-- Cardinality of s - replicate (k+1) i when k < count i s. -/
private lemma sub_replicate_card (m k : ℕ) (s : Sym (Fin N) m) (i : Fin N) (hk : k < s.1.count i) :
    (s.1 - Multiset.replicate (k + 1) i).card = m - 1 - k := by
  have hle : Multiset.replicate (k + 1) i ≤ s.1 := by
    rw [replicate_le_iff_count]; omega
  rw [Multiset.card_sub hle, s.2, Multiset.card_replicate]
  omega

omit [DecidableEq (Fin N)] in
/-- Cardinality of t + replicate (j+1) i when j < n. -/
private lemma add_replicate_card (m j : ℕ) (hj : j < m) (t : Sym (Fin N) (m - 1 - j)) (i : Fin N) :
    (t.1 + Multiset.replicate (j + 1) i).card = m := by
  rw [Multiset.card_add, t.2, Multiset.card_replicate]
  omega

/-- Add replicate (j+1) i to a Sym (n-1-j) to get a Sym n. -/
private def addReplicate (m j : ℕ) (hj : j < m) (t : Sym (Fin N) (m - 1 - j)) (i : Fin N) :
    Sym (Fin N) m :=
  ⟨t.1 + Multiset.replicate (j + 1) i, add_replicate_card m j hj t i⟩

/-- Subtract replicate (k+1) i from a Sym n to get a Sym (n-1-k). -/
private def subReplicate (m k : ℕ) (s : Sym (Fin N) m) (i : Fin N) (hk : k < s.1.count i) :
    Sym (Fin N) (m - 1 - k) :=
  ⟨s.1 - Multiset.replicate (k + 1) i, sub_replicate_card m k s i hk⟩

/-- Key property: j < count i (addReplicate t i). -/
private lemma j_lt_count_addReplicate (m j : ℕ) (hj : j < m) (t : Sym (Fin N) (m - 1 - j))
    (i : Fin N) : j < (addReplicate m j hj t i).1.count i := by
  simp only [addReplicate, Multiset.count_add, Multiset.count_replicate_self]
  omega

/-- Round-trip: subReplicate (addReplicate t i) = t. -/
private lemma sub_add_replicate (m j : ℕ) (hj : j < m) (t : Sym (Fin N) (m - 1 - j)) (i : Fin N) :
    subReplicate m j (addReplicate m j hj t i) i (j_lt_count_addReplicate m j hj t i) = t := by
  apply Subtype.ext
  simp only [subReplicate, addReplicate]
  exact @Multiset.add_sub_cancel_right (Fin N) _ t.1 (Multiset.replicate (j + 1) i)

/-- Bound: k < count i s implies k < n. -/
private lemma count_lt_card_of_lt (m k : ℕ) (s : Sym (Fin N) m) (i : Fin N) (hk : k < s.1.count i) :
    k < m := by
  have hle := Multiset.count_le_card i s.1
  rw [s.2] at hle
  omega

/-- Round-trip: addReplicate (subReplicate s i) = s. -/
private lemma add_sub_replicate (m k : ℕ) (s : Sym (Fin N) m) (i : Fin N) (hk : k < s.1.count i) :
    addReplicate m k (count_lt_card_of_lt m k s i hk) (subReplicate m k s i hk) i = s := by
  apply Subtype.ext
  simp only [addReplicate, subReplicate]
  have hle : Multiset.replicate (k + 1) i ≤ s.1 := by
    rw [replicate_le_iff_count]; omega
  exact Multiset.sub_add_cancel hle

/-- Newton-Girard formula relating h and p: ∑_{j=1}^n h_{n-j} p_j = n · h_n.
    (Theorem thm.sf.NG, equation eq.thm.sf.NG.hp).

    **Proof strategy**: The proof is by a counting argument on monomials.
    Each monomial in h_n corresponds to a multiset s : Sym (Fin N) n.

    On the LHS, each such monomial appears exactly n times:
    once for each way to decompose s = t + replicate (j+1) i where
    j ∈ {0, ..., n-1}, t : Sym (n-1-j), and i : Fin N.

    The key bijection is:
    - LHS: { (j, t, i) | j < n, t : Sym (n-1-j), i : Fin N }
    - RHS: { (s, i, k) | s : Sym n, i : Fin N, k < count i s }
    where (j, t, i) ↦ (t.1 + replicate (j+1) i, i, j).

    For each s : Sym n, the monomial (s.1.map X).prod appears:
    - On LHS: #{(j, t, i) | t.1 + replicate (j+1) i = s.1} = ∑_i count(i,s) = n times
    - On RHS: with coefficient ∑_i count(i,s) = n

    Label: thm.sf.NG -/
theorem newtonGirard_hp (n : ℕ) (_hn : 0 < n) :
    ∑ j ∈ range n, h (K := K) (N := N) (n - 1 - j) * p (j + 1) = (n : P K N) * h n := by
  simp only [h, hsymm, p, psum]
  -- Transform LHS using the identity: (t.1.map X).prod * X_i^j = ((t.1 + replicate j i).map X).prod
  have hprod : ∀ (k : ℕ) (t : Sym (Fin N) k) (i : Fin N) (j : ℕ),
      (t.1.map (MvPolynomial.X : Fin N → P K N)).prod * (MvPolynomial.X i : P K N) ^ j =
      ((t.1 + Multiset.replicate j i).map (MvPolynomial.X : Fin N → P K N)).prod := by
    intro k t i j
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]
  conv_lhs =>
    arg 2
    ext j
    rw [sum_mul_sum]
    arg 2
    ext t
    arg 2
    ext i
    rw [hprod]
  -- Transform RHS using sum_count_eq_card
  rw [mul_sum]
  have hrhs : ∀ s : Sym (Fin N) n,
      (n : P K N) * (s.1.map MvPolynomial.X).prod =
      ∑ i : Fin N, (s.1.count i : P K N) * (s.1.map MvPolynomial.X).prod := by
    intro s
    rw [← Finset.sum_mul]
    congr 1
    simp only [← Nat.cast_sum]
    congr 1
    exact (sum_count_eq_card n s).symm
  conv_rhs =>
    arg 2
    ext s
    rw [hrhs s]
  -- Both sides now sum over the same monomials with the same coefficients.
  rw [Finset.sum_comm]
  -- Swap sums on LHS to get ∑ i : Fin N, ∑ j ∈ range n, ∑ t : Sym (n-1-j), ...
  have lhs_eq : ∑ j ∈ range n, ∑ t : Sym (Fin N) (n - 1 - j), ∑ i : Fin N,
      ((t.1 + Multiset.replicate (j + 1) i).map (MvPolynomial.X : Fin N → P K N)).prod =
      ∑ i : Fin N, ∑ j ∈ range n, ∑ t : Sym (Fin N) (n - 1 - j),
      ((t.1 + Multiset.replicate (j + 1) i).map (MvPolynomial.X : Fin N → P K N)).prod := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [lhs_eq]

  -- Now both sides are ∑ i : Fin N, (inner sum)
  apply Finset.sum_congr rfl
  intro i _

  -- Key helper lemma: multiplying a natural number by a polynomial equals summing over range
  have nat_mul_eq_sum_range : ∀ (c : ℕ) (x : MvPolynomial (Fin N) K),
      (c : MvPolynomial (Fin N) K) * x = ∑ _k ∈ range c, x := by
    intro c x
    induction c with
    | zero => simp
    | succ c ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ih, range_add_one, sum_insert (by simp)]
      ring

  -- Use nat_mul_eq_sum_range to expand the count
  conv_rhs =>
    arg 2
    ext s
    rw [nat_mul_eq_sum_range]

  -- Flatten both sides using sum_sigma'
  rw [Finset.sum_sigma', Finset.sum_sigma']

  -- Apply Finset.sum_bij' with the bijection (j, t) ↔ (addReplicate t i, j)
  refine Finset.sum_bij'
    -- Forward function: (j, t) ↦ (addReplicate t i, j)
    (fun jt hjt => ⟨addReplicate n jt.1 (Finset.mem_range.mp (Finset.mem_sigma.mp hjt).1) jt.2 i, jt.1⟩)
    -- Backward function: (s, k) ↦ (k, subReplicate s i)
    (fun sk hsk => ⟨sk.2, subReplicate n sk.2 sk.1 i (Finset.mem_range.mp (Finset.mem_sigma.mp hsk).2)⟩)
    -- Forward lands in RHS domain
    (fun jt hjt => by
      rw [Finset.mem_sigma] at hjt ⊢
      constructor
      · exact Finset.mem_univ _
      · rw [Finset.mem_range]
        exact j_lt_count_addReplicate n jt.1 (Finset.mem_range.mp hjt.1) jt.2 i)
    -- Backward lands in LHS domain
    (fun sk hsk => by
      rw [Finset.mem_sigma] at hsk ⊢
      constructor
      · rw [Finset.mem_range]
        exact count_lt_card_of_lt n sk.2 sk.1 i (Finset.mem_range.mp hsk.2)
      · exact Finset.mem_univ _)
    -- Round-trip 1: backward ∘ forward = id
    (fun jt hjt => by
      rw [Finset.mem_sigma] at hjt
      refine Sigma.ext rfl ?_
      exact heq_of_eq (sub_add_replicate n jt.1 (Finset.mem_range.mp hjt.1) jt.2 i))
    -- Round-trip 2: forward ∘ backward = id
    (fun sk hsk => by
      rw [Finset.mem_sigma] at hsk
      refine Sigma.ext ?_ (heq_of_eq rfl)
      exact add_sub_replicate n sk.2 sk.1 i (Finset.mem_range.mp hsk.2))
    -- Values match: addReplicate gives the same monomial
    ?_
  -- Values match: we need to show the function values are equal
  intro jt hjt
  rfl

end WithDecidableEq'

/-!
## Generating Function Identities (Proposition prop.sf.e-h-FPS)

These identities express the elementary and complete homogeneous symmetric polynomials
as coefficients in certain generating functions.

(a) In P[t]: ∏_{i=1}^N (1 - t·x_i) = ∑_{n≥0} (-1)^n t^n e_n
(b) In P[u,v]: ∏_{i=1}^N (u - v·x_i) = ∑_{n=0}^N (-1)^n u^{N-n} v^n e_n
(c) In P[[t]]: ∏_{i=1}^N 1/(1 - t·x_i) = ∑_{n≥0} t^n h_n
-/

/-- Helper lemma for the product expansion in esymm_genfunc_two_var. -/
private lemma prod_neg_mul_eq (t : Finset (Fin N)) :
    ∏ i ∈ univ \ t, (-(MvPolynomial.X (1 : Fin 2) * MvPolynomial.C (X i : P K N)) :
        MvPolynomial (Fin 2) (P K N)) =
    (-1 : MvPolynomial (Fin 2) (P K N)) ^ #(univ \ t) * MvPolynomial.X 1 ^ #(univ \ t) *
      MvPolynomial.C (∏ i ∈ univ \ t, X i) := by
  have h1 : ∀ i : Fin N, (-(MvPolynomial.X (1 : Fin 2) * MvPolynomial.C (X i : P K N)) :
        MvPolynomial (Fin 2) (P K N)) =
      (-1 : MvPolynomial (Fin 2) (P K N)) * (MvPolynomial.X 1 * MvPolynomial.C (X i)) := by
    intro i; ring
  simp_rw [h1, prod_mul_distrib, prod_const, ← map_prod]
  ring

/-- Helper lemma for cardinality of complement in esymm_genfunc_two_var. -/
private lemma card_sdiff_univ (t : Finset (Fin N)) (ht : t ⊆ univ) :
    #(univ \ t) = N - #t := by
  have h : #t + #(univ \ t) = N := by
    rw [← card_union_of_disjoint disjoint_sdiff,
        union_sdiff_of_subset ht, card_univ, Fintype.card_fin]
  omega

/-- Sum over powersetCard j univ of products over complements equals e_{N-j}. -/
private lemma sum_powersetCard_prod_sdiff (j : ℕ) (hj : j ≤ N) :
    ∑ t ∈ powersetCard j (@univ (Fin N) _), ∏ i ∈ univ \ t, (X i : P K N) =
    e (K := K) (N := N) (N - j) := by
  simp only [e, esymm]
  refine Finset.sum_bij' (fun t _ => univ \ t) (fun s _ => univ \ s) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [mem_powersetCard] at ht ⊢
    refine ⟨sdiff_subset, ?_⟩
    rw [card_sdiff_univ t ht.1, ht.2]
  · intro s hs
    rw [mem_powersetCard] at hs ⊢
    refine ⟨sdiff_subset, ?_⟩
    rw [card_sdiff_univ s hs.1, hs.2]
    omega
  · intro t ht
    exact Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp ht).1
  · intro s hs
    exact Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp hs).1
  · intro t _
    rfl

/-- Generating function for elementary symmetric polynomials, two-variable version
    (Proposition prop.sf.e-h-FPS (b)).
    ∏_{i=1}^N (u - v·x_i) = ∑_{n=0}^N (-1)^n u^{N-n} v^n e_n
    Label: prop.sf.e-h-FPS -/
theorem esymm_genfunc_two_var :
    ∏ i : Fin N, (MvPolynomial.X (0 : Fin 2) -
      MvPolynomial.X (1 : Fin 2) * MvPolynomial.C (X i : P K N) :
        MvPolynomial (Fin 2) (P K N)) =
    ∑ n ∈ range (N + 1),
      (-1 : MvPolynomial (Fin 2) (P K N)) ^ n *
      MvPolynomial.X 0 ^ (N - n) * MvPolynomial.X 1 ^ n *
      MvPolynomial.C (e (K := K) (N := N) n) := by
  simp only [sub_eq_add_neg]
  rw [Finset.prod_add]
  simp_rw [prod_const, prod_neg_mul_eq]
  -- Rearrange the product
  have h1 : ∑ t ∈ univ.powerset,
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) (P K N)) ^ #t *
      ((-1 : MvPolynomial (Fin 2) (P K N)) ^ #(univ \ t) * MvPolynomial.X 1 ^ #(univ \ t) *
        MvPolynomial.C (∏ i ∈ univ \ t, X i)) =
      ∑ t ∈ univ.powerset,
        (-1 : MvPolynomial (Fin 2) (P K N)) ^ #(univ \ t) * MvPolynomial.X 0 ^ #t *
          MvPolynomial.X 1 ^ #(univ \ t) * MvPolynomial.C (∏ i ∈ univ \ t, X i) := by
    apply Finset.sum_congr rfl
    intros t _
    ring
  rw [h1]
  -- Group by cardinality of t
  rw [Finset.sum_powerset]
  simp only [card_univ, Fintype.card_fin]
  -- Simplify each inner sum
  have h2 : ∀ j ∈ range (N + 1),
      ∑ t ∈ powersetCard j (@univ (Fin N) _),
        (-1 : MvPolynomial (Fin 2) (P K N)) ^ #(univ \ t) * MvPolynomial.X 0 ^ #t *
          MvPolynomial.X 1 ^ #(univ \ t) * MvPolynomial.C (∏ i ∈ univ \ t, X i) =
      (-1 : MvPolynomial (Fin 2) (P K N)) ^ (N - j) * MvPolynomial.X 0 ^ j *
        MvPolynomial.X 1 ^ (N - j) * MvPolynomial.C (e (K := K) (N := N) (N - j)) := by
    intro j hj
    rw [mem_range] at hj
    have hj' : j ≤ N := by omega
    have h_card : ∀ t ∈ powersetCard j (@univ (Fin N) _), #(univ \ t) = N - j := by
      intro t ht
      rw [mem_powersetCard] at ht
      rw [card_sdiff_univ t ht.1, ht.2]
    have h_card_t : ∀ t ∈ powersetCard j (@univ (Fin N) _), #t = j := by
      intro t ht
      exact (mem_powersetCard.mp ht).2
    calc ∑ t ∈ powersetCard j (@univ (Fin N) _),
          (-1 : MvPolynomial (Fin 2) (P K N)) ^ #(univ \ t) * MvPolynomial.X 0 ^ #t *
            MvPolynomial.X 1 ^ #(univ \ t) * MvPolynomial.C (∏ i ∈ univ \ t, X i)
        = ∑ t ∈ powersetCard j (@univ (Fin N) _),
            (-1 : MvPolynomial (Fin 2) (P K N)) ^ (N - j) * MvPolynomial.X 0 ^ j *
              MvPolynomial.X 1 ^ (N - j) * MvPolynomial.C (∏ i ∈ univ \ t, X i) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [h_card t ht, h_card_t t ht]
        _ = (-1 : MvPolynomial (Fin 2) (P K N)) ^ (N - j) * MvPolynomial.X 0 ^ j *
            MvPolynomial.X 1 ^ (N - j) *
            ∑ t ∈ powersetCard j (@univ (Fin N) _), MvPolynomial.C (∏ i ∈ univ \ t, X i) := by
          rw [mul_sum]
        _ = (-1 : MvPolynomial (Fin 2) (P K N)) ^ (N - j) * MvPolynomial.X 0 ^ j *
            MvPolynomial.X 1 ^ (N - j) *
            MvPolynomial.C (∑ t ∈ powersetCard j (@univ (Fin N) _), ∏ i ∈ univ \ t, X i) := by
          rw [map_sum]
        _ = (-1 : MvPolynomial (Fin 2) (P K N)) ^ (N - j) * MvPolynomial.X 0 ^ j *
            MvPolynomial.X 1 ^ (N - j) * MvPolynomial.C (e (K := K) (N := N) (N - j)) := by
          rw [sum_powersetCard_prod_sdiff j hj']
  rw [Finset.sum_congr rfl h2]
  -- Reindex the sum: j ↦ N - j
  conv_rhs => rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have h_sub : N + 1 - 1 - j = N - j := by omega
  rw [h_sub]
  have h_sub2 : N - (N - j) = j := by omega
  rw [h_sub2]

/-- Generating function for complete homogeneous symmetric polynomials
    (Proposition prop.sf.e-h-FPS (c)).
    In the ring of formal power series, ∏_{i=1}^N 1/(1 - t·x_i) = ∑_{n≥0} t^n h_n.
    We state this as: (∑ t^n h_n) * ∏(1 - t·x_i) = 1.
    Label: prop.sf.e-h-FPS -/
theorem hsymm_genfunc [DecidableEq (Fin N)] :
    let E : Polynomial (P K N) := ∏ i : Fin N, (1 - Polynomial.X * Polynomial.C (X i : P K N))
    PowerSeries.mk (fun n => h (K := K) (N := N) n) * (E : PowerSeries (P K N)) = 1 := by
  intro E
  -- Helper lemma for (-1)^n in polynomials
  have neg_one_pow_eq_C : ∀ n : ℕ,
      (-1 : Polynomial (P K N)) ^ n = Polynomial.C ((-1 : P K N) ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, ih]
      simp only [mul_neg, mul_one, Polynomial.C_neg]
      ring
  -- Helper: coefficient of E
  have E_coeff : ∀ j : ℕ, Polynomial.coeff E j =
      if j ≤ N then (-1 : P K N) ^ j * e (K := K) (N := N) j else 0 := by
    intro j
    have hE : E = ∑ n ∈ range (N + 1),
        (-1 : Polynomial (P K N)) ^ n * Polynomial.X ^ n * Polynomial.C (e (K := K) (N := N) n) :=
      esymm_genfunc
    rw [hE]
    simp only [Polynomial.finsetSum_coeff]
    have h1 : ∀ n ∈ range (N + 1),
        Polynomial.coeff ((-1 : Polynomial (P K N)) ^ n * Polynomial.X ^ n *
          Polynomial.C (e (K := K) (N := N) n)) j =
        if j = n then (-1 : P K N) ^ n * e (K := K) (N := N) n else 0 := by
      intro n _
      rw [neg_one_pow_eq_C]
      have heq : Polynomial.C ((-1 : P K N) ^ n) * Polynomial.X ^ n *
          Polynomial.C (e (K := K) (N := N) n) =
          Polynomial.C ((-1 : P K N) ^ n * e (K := K) (N := N) n) * Polynomial.X ^ n := by
        rw [Polynomial.C_mul]; ring
      rw [heq, Polynomial.coeff_C_mul_X_pow]
    rw [sum_congr rfl h1]
    split_ifs with hj
    · have hj' : j ∈ range (N + 1) := by simp; omega
      rw [sum_eq_single j]
      · simp
      · intro b _ hbj; simp [hbj.symm]
      · intro hj''; exact absurd hj' hj''
    · apply sum_eq_zero
      intro n hn
      simp only [mem_range] at hn
      have : j ≠ n := by omega
      simp [this]
  -- Main proof
  rw [PowerSeries.ext_iff]
  intro n
  simp only [PowerSeries.coeff_one]
  rw [PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk, Polynomial.coeff_coe]
  conv_lhs =>
    arg 2
    ext p
    rw [E_coeff p.2]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- Case n = 0
    subst hn
    simp only [Finset.Nat.antidiagonal_zero, sum_singleton, Nat.zero_le, ite_true, pow_zero,
      one_mul]
    rw [h_zero, e_zero]; ring
  · -- Case n > 0
    simp only [ite_false, hn.ne']
    have hsum : ∑ p ∈ antidiagonal n, h (K := K) (N := N) p.1 *
        (if p.2 ≤ N then (-1 : P K N) ^ p.2 * e (K := K) (N := N) p.2 else 0) =
        ∑ p ∈ antidiagonal n, (if p.2 ≤ N then h (K := K) (N := N) p.1 *
          (-1 : P K N) ^ p.2 * e (K := K) (N := N) p.2 else 0) := by
      apply sum_congr rfl
      intro p _
      split_ifs with h <;> ring
    rw [hsum]
    have hdrop : ∑ p ∈ antidiagonal n, (if p.2 ≤ N then h (K := K) (N := N) p.1 *
        (-1 : P K N) ^ p.2 * e (K := K) (N := N) p.2 else 0) =
        ∑ p ∈ antidiagonal n, h (K := K) (N := N) p.1 *
          (-1 : P K N) ^ p.2 * e (K := K) (N := N) p.2 := by
      apply sum_congr rfl
      intro p _
      split_ifs with hle
      · rfl
      · push Not at hle
        rw [e_eq_zero_of_gt hle]; ring
    rw [hdrop]
    rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun k j => h (K := K) (N := N) k *
      (-1 : P K N) ^ j * e (K := K) (N := N) j)]
    rw [← sum_range_reflect (fun k => h (K := K) (N := N) k *
      (-1 : P K N) ^ (n - k) * e (K := K) (N := N) (n - k))]
    have hsub : ∀ k ∈ range (n + 1), n + 1 - 1 - k = n - k := fun k hk => by
      simp only [mem_range] at hk; omega
    have hsub2 : ∀ k ∈ range (n + 1), n - (n - k) = k := fun k hk => by
      simp only [mem_range] at hk; omega
    have hreindex : ∀ k ∈ range (n + 1),
        h (K := K) (N := N) (n + 1 - 1 - k) * (-1 : P K N) ^ (n - (n + 1 - 1 - k)) *
          e (K := K) (N := N) (n - (n + 1 - 1 - k)) =
        h (K := K) (N := N) (n - k) * (-1 : P K N) ^ k * e (K := K) (N := N) k := by
      intro k hk
      rw [hsub k hk, hsub2 k hk]
    rw [sum_congr rfl hreindex]
    have hcomm : ∑ k ∈ range (n + 1), h (K := K) (N := N) (n - k) *
        (-1 : P K N) ^ k * e (K := K) (N := N) k =
        ∑ k ∈ range (n + 1), (-1 : P K N) ^ k * e (K := K) (N := N) k *
          h (K := K) (N := N) (n - k) := by
      apply sum_congr rfl
      intro k _
      ring
    rw [hcomm, newtonGirard_eh n hn]

/-!
## Fundamental Theorem of Symmetric Polynomials (Theorem thm.sf.ftsf)

(a) e_1, e_2, ..., e_N are algebraically independent and generate S.
(b) h_1, h_2, ..., h_N are algebraically independent and generate S.
(c) If K is a ℚ-algebra, then p_1, p_2, ..., p_N are algebraically independent and generate S.

These are implemented in Mathlib via `MvPolynomial.esymmAlgEquiv`.

### Part (a): Elementary Symmetric Polynomials

The elementary symmetric polynomials e_1, e_2, ..., e_N are algebraically independent
over K and generate the K-algebra S of symmetric polynomials. This means:
1. The only polynomial relation P(e_1, ..., e_N) = 0 is P = 0 (algebraic independence)
2. Every symmetric polynomial can be written uniquely as a polynomial in e_1, ..., e_N (generation)

Equivalently, the map K[y_1, ..., y_N] → S given by g ↦ g(e_1, ..., e_N) is a K-algebra isomorphism.
-/

/-- The elementary symmetric polynomials e_1, ..., e_N generate the symmetric subalgebra
    and the map g ↦ g[e_1, ..., e_N] is a K-algebra isomorphism.
    (Theorem thm.sf.ftsf (a)).
    Label: thm.sf.ftsf -/
noncomputable def esymmAlgEquiv' : MvPolynomial (Fin N) K ≃ₐ[K] S K N :=
  esymmAlgEquiv (Fin N) K (Fintype.card_fin N)

/-- The map sending g to g[e_1, ..., e_N] is injective.
    This is equivalent to saying the elementary symmetric polynomials are algebraically independent.
    Label: thm.sf.ftsf -/
theorem esymmAlgHom_injective' :
    Function.Injective (esymmAlgHom (Fin N) K N) := by
  apply esymmAlgHom_injective K
  simp only [Fintype.card_fin, le_refl]

/-- The map sending g to g[e_1, ..., e_N] is surjective.
    This is equivalent to saying the elementary symmetric polynomials generate S.
    Label: thm.sf.ftsf -/
theorem esymmAlgHom_surjective' :
    Function.Surjective (esymmAlgHom (Fin N) K N) := by
  apply esymmAlgHom_surjective K
  simp only [Fintype.card_fin, le_refl]

/-- The esymmAlgEquiv' equals esymmAlgHom as a function.
    Label: thm.sf.ftsf -/
lemma esymmAlgEquiv'_eq_esymmAlgHom (g : MvPolynomial (Fin N) K) :
    esymmAlgEquiv' (K := K) (N := N) g = esymmAlgHom (Fin N) K N g := by
  simp only [esymmAlgEquiv', esymmAlgEquiv]
  rfl

/-- The key lemma: esymmAlgHom is aeval composed with the inclusion.
    Label: thm.sf.ftsf -/
lemma esymmAlgHom_eq_aeval (r : MvPolynomial (Fin N) K) :
    (esymmAlgHom (Fin N) K N r : P K N) =
    aeval (fun i : Fin N => (esymm (Fin N) K (i + 1) : P K N)) r := by
  simp only [esymmAlgHom, aeval_def]
  induction r using MvPolynomial.induction_on with
  | C a =>
    simp only [eval₂_C, algebraMap_eq]
    rfl
  | add p q hp hq =>
    simp only [eval₂_add, Subalgebra.coe_add]
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [eval₂_mul, eval₂_X, Subalgebra.coe_mul]
    rw [hp]

/-- The elementary symmetric polynomials e_1, ..., e_N are algebraically independent.
    This means: if P(e_1, ..., e_N) = 0 for some polynomial P ∈ K[y_1, ..., y_N], then P = 0.
    (Theorem thm.sf.ftsf (a), algebraic independence part).
    Label: thm.sf.ftsf -/
theorem esymm_algebraicIndependent :
    AlgebraicIndependent K (fun i : Fin N => (esymm (Fin N) K (i + 1) : P K N)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  intro p q hpq
  have h := esymmAlgHom_injective' (K := K) (N := N)
  rw [← esymmAlgHom_eq_aeval, ← esymmAlgHom_eq_aeval] at hpq
  exact h (Subtype.ext hpq)

/-- Every symmetric polynomial can be uniquely written as a polynomial in e_1, ..., e_N.
    (Theorem thm.sf.ftsf (a), generation part).
    Label: thm.sf.ftsf -/
theorem esymm_generates_symmetric (f : S K N) :
    ∃! g : MvPolynomial (Fin N) K, esymmAlgHom (Fin N) K N g = f := by
  use (esymmAlgEquiv' (K := K) (N := N)).symm f
  refine ⟨?_, ?_⟩
  · -- Need to show esymmAlgHom (esymmAlgEquiv'.symm f) = f
    show esymmAlgHom (Fin N) K N ((esymmAlgEquiv' (K := K) (N := N)).symm f) = f
    rw [← esymmAlgEquiv'_eq_esymmAlgHom]
    exact AlgEquiv.apply_symm_apply (esymmAlgEquiv' (K := K) (N := N)) f
  · intro g hg
    -- We have esymmAlgHom g = f, need to show g = esymmAlgEquiv'.symm f
    have hg' : esymmAlgEquiv' (K := K) (N := N) g = f := by
      rw [esymmAlgEquiv'_eq_esymmAlgHom]; exact hg
    calc g = (esymmAlgEquiv' (K := K) (N := N)).symm (esymmAlgEquiv' (K := K) (N := N) g) :=
             (AlgEquiv.symm_apply_apply (esymmAlgEquiv' (K := K) (N := N)) g).symm
         _ = (esymmAlgEquiv' (K := K) (N := N)).symm f := by rw [hg']

/-!
### Part (b): Complete Homogeneous Symmetric Polynomials

The complete homogeneous symmetric polynomials h_1, h_2, ..., h_N are also algebraically
independent and generate S. This is a consequence of the Newton-Girard relations which
express each h_k as a polynomial in e_1, ..., e_k and vice versa.
-/

section PartB

variable [DecidableEq (Fin N)]

/-- The complete homogeneous symmetric polynomials h_1, ..., h_N are algebraically independent.
    (Theorem thm.sf.ftsf (b), algebraic independence part).

    The proof uses the Newton-Girard relations to show that the map sending polynomials
    to their evaluation at h_1, ..., h_N factors through the symmetric subalgebra S,
    and this factored map is bijective.

    Key steps:
    1. The map aeval hsymm lands in S K N (since hsymm is symmetric)
    2. Factor aeval hsymm as: MvPolynomial → S K N → P K N
    3. The composition esymmAlgEquiv'.symm ∘ (factored map) : MvPolynomial → MvPolynomial is surjective
       (because X_i = esymmAlgEquiv'.symm (esymm (i+1)) and esymm is in the range by Newton-Girard)
    4. A surjective algebra endomorphism of K[X_1, ..., X_n] is bijective
    5. Therefore the factored map is bijective, hence aeval hsymm is injective

    Label: thm.sf.ftsf -/
theorem hsymm_algebraicIndependent [IsDomain K] :
    AlgebraicIndependent K (fun i : Fin N => (hsymm (Fin N) K (i + 1) : P K N)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  -- Define the aeval map inline
  let hsymmAeval' : MvPolynomial (Fin N) K →ₐ[K] P K N :=
    aeval (fun i : Fin N => hsymm (Fin N) K (i + 1))
  -- Step 1: hsymmAeval' lands in S K N
  have h_symm : ∀ p, (hsymmAeval' p).IsSymmetric := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c => simp only [hsymmAeval', aeval_C]; exact IsSymmetric.C c
    | add p q hp hq => simp only [hsymmAeval', map_add]; exact hp.add hq
    | mul_X p i hp => simp only [hsymmAeval', map_mul, aeval_X]; exact hp.mul (hsymm_isSymmetric (Fin N) K (i + 1))
  -- Step 2: Define the factored map hsymmToS
  let hsymmToS : MvPolynomial (Fin N) K →ₐ[K] S K N := {
    toFun := fun p => ⟨hsymmAeval' p, h_symm p⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
    commutes' := fun r => Subtype.ext (by simp [hsymmAeval', algebraMap_eq])
  }
  -- Step 3: The composition φ = esymmAlgEquiv'.symm ∘ hsymmToS
  let φ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K :=
    esymmAlgEquiv'.symm.toAlgHom.comp hsymmToS
  -- Step 4: φ is bijective
  -- The proof constructs an inverse ψ to φ using Newton-Girard.
  -- For each i, Newton-Girard gives P_i such that hsymmAeval'(P_i) = e_{i+1}.
  -- Define ψ(X_i) = P_i. Then:
  -- (a) φ ∘ ψ = id (since φ(P_i) = X_i by definition of esymmAlgEquiv')
  -- (b) ψ ∘ φ = id (by the symmetric structure of Newton-Girard relations)

  -- Newton-Girard hypothesis: for each i, esymm(i+1) is in the range of hsymmAeval'
  -- This follows from Newton-Girard: e_n can be expressed in terms of e_0, ..., e_{n-1} and h_1, ..., h_n.
  -- We prove by strong induction that esymm k is in the range for k ≤ N.
  have h_NG_aux : ∀ k : ℕ, k ≤ N → ∃ P : MvPolynomial (Fin N) K, hsymmAeval' P = esymm (Fin N) K k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero =>
        use 1
        simp only [hsymmAeval', map_one, esymm_zero]
      | succ k =>
        -- Use Newton-Girard: ∑_{j=0}^{k+1} (-1)^j e_j h_{k+1-j} = 0
        -- Rearrange: e_{k+1} = (-1)^{k+1} * (- ∑_{j=0}^k (-1)^j e_j h_{k+1-j})
        have ng := newtonGirard_eh (K := K) (N := N) (k + 1) (Nat.succ_pos k)
        -- Split off the last term from the sum
        have hrange : range (k + 1 + 1) = insert (k + 1) (range (k + 1)) := by
          rw [range_add_one]
        have hnotmem : k + 1 ∉ range (k + 1) := by simp
        rw [hrange, sum_insert hnotmem] at ng
        -- Simplify h_0 = 1
        have h0 : h (K := K) (N := N) ((k + 1) - (k + 1)) = 1 := by simp [hsymm_zero]
        simp only [h0, mul_one] at ng
        -- ng says: (-1)^{k+1} * e_{k+1} + ∑_{j=0}^k (-1)^j e_j h_{k+1-j} = 0
        -- Rearrange to get: (-1)^{k+1} * e_{k+1} = - ∑_{j=0}^k (-1)^j e_j h_{k+1-j}
        have h1 : (-1 : P K N) ^ (k + 1) * esymm (Fin N) K (k + 1) =
            - ∑ j ∈ range (k + 1), (-1 : P K N) ^ j * e (K := K) (N := N) j * h (k + 1 - j) := by
          have hzero : (-1 : P K N) ^ (k + 1) * e (k + 1) +
              ∑ x ∈ range (k + 1), (-1 : P K N) ^ x * e x * h (k + 1 - x) = 0 := ng
          calc (-1 : P K N) ^ (k + 1) * e (k + 1)
              = (-1 : P K N) ^ (k + 1) * e (k + 1) +
                  ∑ x ∈ range (k + 1), (-1 : P K N) ^ x * e x * h (k + 1 - x) -
                  ∑ x ∈ range (k + 1), (-1 : P K N) ^ x * e x * h (k + 1 - x) := by ring
            _ = 0 - ∑ x ∈ range (k + 1), (-1 : P K N) ^ x * e x * h (k + 1 - x) := by rw [hzero]
            _ = - ∑ x ∈ range (k + 1), (-1 : P K N) ^ x * e x * h (k + 1 - x) := by ring
        -- Now: e_{k+1} = (-1)^{k+1} * (- ∑ ...) since (-1)^{k+1} * (-1)^{k+1} = 1
        have h2 : (-1 : P K N) ^ (k + 1) * (-1 : P K N) ^ (k + 1) = 1 := by
          rw [← pow_add, ← two_mul]
          simp [pow_mul]
        have heq : esymm (Fin N) K (k + 1) =
            (-1 : P K N) ^ (k + 1) * (- ∑ j ∈ range (k + 1), (-1 : P K N) ^ j * e (K := K) (N := N) j * h (k + 1 - j)) := by
          calc esymm (Fin N) K (k + 1)
              = 1 * esymm (Fin N) K (k + 1) := by ring
            _ = ((-1 : P K N) ^ (k + 1) * (-1 : P K N) ^ (k + 1)) * esymm (Fin N) K (k + 1) := by rw [h2]
            _ = (-1 : P K N) ^ (k + 1) * ((-1 : P K N) ^ (k + 1) * esymm (Fin N) K (k + 1)) := by ring
            _ = (-1 : P K N) ^ (k + 1) * (- ∑ j ∈ range (k + 1), (-1 : P K N) ^ j * e (K := K) (N := N) j * h (k + 1 - j)) := by rw [h1]
        -- Now show the RHS is in the range of hsymmAeval'
        -- The range of hsymmAeval' is a subalgebra, so it's closed under *, -, ∑
        -- We need: (-1)^{k+1} and each term (-1)^j * e_j * h_{k+1-j} is in the range
        -- By IH, e_j is in the range for j < k+1
        -- h_{k+1-j} = hsymmAeval'(X_{k-j}) for 0 < k+1-j ≤ N
        -- Define the range subalgebra
        let R : Subalgebra K (P K N) := hsymmAeval'.range
        -- Show esymm (k+1) is in R using heq
        have h_neg1_in_R : (-1 : P K N) ∈ R := by
          have h1_in : (1 : P K N) ∈ R := Subalgebra.one_mem _
          exact Subalgebra.neg_mem _ h1_in
        have h_neg1_pow_in_R : ∀ n : ℕ, (-1 : P K N) ^ n ∈ R := fun n =>
          Subalgebra.pow_mem _ h_neg1_in_R n
        have h_ej_in_R : ∀ j, j < k + 1 → esymm (Fin N) K j ∈ R := by
          intro j hj
          exact ih j hj (by omega)
        have h_hkj_in_R : ∀ j, j < k + 1 → hsymm (Fin N) K (k + 1 - j) ∈ R := by
          intro j hj
          have hpos : 0 < k + 1 - j := by omega
          have hle : k + 1 - j ≤ N := by omega
          have hlt : k + 1 - j - 1 < N := by omega
          use X ⟨k + 1 - j - 1, hlt⟩
          show hsymmAeval' (X ⟨k + 1 - j - 1, hlt⟩) = hsymm (Fin N) K (k + 1 - j)
          simp only [hsymmAeval', aeval_X]
          congr 1
          omega
        have h_sum_in_R : ∑ j ∈ range (k + 1), (-1 : P K N) ^ j * e (K := K) (N := N) j * h (k + 1 - j) ∈ R := by
          apply Subalgebra.sum_mem
          intro j hj
          rw [mem_range] at hj
          apply Subalgebra.mul_mem
          · apply Subalgebra.mul_mem
            · exact h_neg1_pow_in_R j
            · exact h_ej_in_R j hj
          · exact h_hkj_in_R j hj
        have h_esymm_in_R : esymm (Fin N) K (k + 1) ∈ R := by
          rw [heq]
          apply Subalgebra.mul_mem
          · exact h_neg1_pow_in_R (k + 1)
          · exact Subalgebra.neg_mem _ h_sum_in_R
        exact h_esymm_in_R
  have h_NG : ∀ i : Fin N, ∃ P : MvPolynomial (Fin N) K, hsymmAeval' P = esymm (Fin N) K (i + 1) := by
    intro i
    exact h_NG_aux (i + 1) (Nat.add_one_le_iff.mpr i.isLt)

  -- Define ψ using the witnesses from h_NG
  let ψ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K :=
    aeval (fun i => Classical.choose (h_NG i))
  
  -- Key lemma: φ(P) = X_i when hsymmAeval'(P) = esymm(i+1)
  have h_φ_eq_X : ∀ (P : MvPolynomial (Fin N) K) (i : Fin N),
      hsymmAeval' P = esymm (Fin N) K (i + 1) → φ P = X i := by
    intro P i hP
    simp only [φ, AlgHom.comp_apply, AlgHom.coe_ofClass]
    have heq : hsymmToS P = ⟨esymm (Fin N) K (i + 1), esymm_isSymmetric _ _ _⟩ := by
      apply Subtype.ext
      simp only [hsymmToS, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      exact hP
    rw [heq]
    exact esymmAlgEquiv_symm_apply (R := K) (Fintype.card_fin N) i
  
  -- φ ∘ ψ = id on generators
  have h_φψ : ∀ i : Fin N, φ (ψ (X i)) = X i := fun i => by
    simp only [ψ, aeval_X]
    exact h_φ_eq_X _ i (Classical.choose_spec (h_NG i))
  
  -- φ ∘ ψ = id as algebra homomorphisms
  have h_φψ_id : φ.comp ψ = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    exact h_φψ i

  -- ψ ∘ φ = id
  -- The proof uses a transcendence degree argument:
  -- 1. φ ∘ ψ = id implies φ is surjective
  -- 2. φ surjective means φ ∘ X generates MvPolynomial (Fin N) K
  -- 3. MvPolynomial (Fin N) K has transcendence degree N over K
  -- 4. N generators of an algebra of trdeg N are algebraically independent
  --    (use Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite)
  -- 5. Therefore φ is injective (since aeval (φ ∘ X) = φ and algebraic independence = injectivity)
  -- 6. ψ ∘ φ = id follows from φ ∘ ψ = id and injectivity of φ
  --
  -- NOTE: This argument requires IsDomain K for the transcendence degree machinery.
  -- For general CommRing K, a different approach is needed (possibly using the
  -- Newton-Girard relations more directly to show hsymmAeval' is injective).
  have h_ψφ_id : ψ.comp φ = AlgHom.id K _ := by
    -- Step 1: φ is surjective (has a right inverse ψ)
    have h_φ_surj : Function.Surjective φ := by
      intro y
      use ψ y
      calc φ (ψ y) = (φ.comp ψ) y := rfl
        _ = AlgHom.id K _ y := by rw [h_φψ_id]
        _ = y := rfl
    
    -- Step 2: φ is injective (by transcendence degree argument)
    have h_φ_mem_adjoin : ∀ q : MvPolynomial (Fin N) K,
        φ q ∈ Algebra.adjoin K (Set.range (φ ∘ MvPolynomial.X)) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C c => rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ c
      | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
      | mul_X p i hp => rw [map_mul]; apply Subalgebra.mul_mem _ hp; apply Algebra.subset_adjoin; simp [Function.comp]
    
    have h_adjoin_top : Algebra.adjoin K (Set.range (φ ∘ MvPolynomial.X)) = ⊤ := by
      rw [eq_top_iff]; intro p _; obtain ⟨q, hq⟩ := h_φ_surj p; rw [← hq]; exact h_φ_mem_adjoin q
    
    haveI h_alg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (φ ∘ MvPolynomial.X))) (MvPolynomial (Fin N) K) := by
      rw [h_adjoin_top]; constructor; intro x
      use Polynomial.X - Polynomial.C ⟨x, trivial⟩
      constructor
      · intro h
        have := Polynomial.leadingCoeff_eq_zero.mpr h
        simp only [Polynomial.leadingCoeff_X_sub_C] at this
        exact one_ne_zero this
      · simp only [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero]
        rfl
    
    have h_basis : IsTranscendenceBasis K (φ ∘ MvPolynomial.X) := by
      apply Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite K
      simp [MvPolynomial.trdeg_of_isDomain]
    
    have h_indep : AlgebraicIndependent K (φ ∘ MvPolynomial.X) := h_basis.1
    rw [algebraicIndependent_iff_injective_aeval] at h_indep
    have h_aeval_eq_φ : MvPolynomial.aeval (φ ∘ MvPolynomial.X) = φ := by
      apply MvPolynomial.algHom_ext; intro i; simp
    rw [h_aeval_eq_φ] at h_indep
    
    -- Step 3: φ injective + φ ∘ ψ = id implies ψ ∘ φ = id
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    apply h_indep
    calc φ (ψ (φ (X i))) = (φ.comp ψ) (φ (X i)) := rfl
      _ = AlgHom.id K _ (φ (X i)) := by rw [h_φψ_id]
      _ = φ (X i) := rfl

  have h_φ_bij : Function.Bijective φ := by
    constructor
    · -- Injectivity: follows from ψ ∘ φ = id
      intro p q hpq
      have : ψ (φ p) = ψ (φ q) := by rw [hpq]
      simp only [← AlgHom.comp_apply, h_ψφ_id, AlgHom.id_apply] at this
      exact this
    · -- Surjectivity: follows from φ ∘ ψ = id
      intro q
      use ψ q
      simp only [← AlgHom.comp_apply, h_φψ_id, AlgHom.id_apply]
  -- Step 5: Conclude that aeval hsymm is injective
  intro p q hpq
  have h : hsymmToS p = hsymmToS q := Subtype.ext hpq
  have h' : φ p = φ q := by
    simp only [φ, AlgHom.comp_apply, AlgHom.coe_ofClass]
    rw [h]
  exact h_φ_bij.injective h'

/-- The aeval map sending X_i to h_{i+1}.
    Label: thm.sf.ftsf -/
private noncomputable def hsymmAeval : MvPolynomial (Fin N) K →ₐ[K] P K N :=
  aeval (fun i : Fin N => hsymm (Fin N) K (i + 1))

/-- The range of hsymmAeval is a subalgebra.
    Label: thm.sf.ftsf -/
private noncomputable def hsymmRange : Subalgebra K (P K N) := hsymmAeval.range

/-- hsymm k is in the range for 0 < k ≤ N.
    Label: thm.sf.ftsf -/
private lemma hsymm_mem_hsymmRange (k : ℕ) (hk : 0 < k) (hk' : k ≤ N) :
    hsymm (Fin N) K k ∈ hsymmRange := by
  have hlt : k - 1 < N := by omega
  refine ⟨X ⟨k - 1, hlt⟩, ?_⟩
  unfold hsymmAeval
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  congr 1
  omega

/-- Key lemma: esymm k is in hsymmRange.
    This follows from Newton-Girard: e_n can be expressed in terms of e_0, ..., e_{n-1} and h_1, ..., h_n.
    Label: thm.sf.ftsf -/
private lemma esymm_mem_hsymmRange (k : ℕ) (hk : k ≤ N) : esymm (Fin N) K k ∈ hsymmRange := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      simp only [esymm_zero]
      exact Subalgebra.one_mem _
    | succ k =>
      -- Use Newton-Girard: ∑_{j=0}^{k+1} (-1)^j e_j h_{k+1-j} = 0
      -- The last term is (-1)^{k+1} * e_{k+1} * h_0 = (-1)^{k+1} * e_{k+1}
      -- So: (-1)^{k+1} * e_{k+1} = - ∑_{j=0}^k (-1)^j e_j h_{k+1-j}
      have ng := newtonGirard_eh (K := K) (N := N) (k + 1) (Nat.succ_pos k)
      -- Split off the last term from the sum
      have hrange : range (k + 1 + 1) = insert (k + 1) (range (k + 1)) := by
        rw [range_add_one]
      have hnotmem : k + 1 ∉ range (k + 1) := by simp
      rw [hrange, sum_insert hnotmem] at ng
      -- Simplify h_0 = 1
      have h0 : h (K := K) (N := N) ((k + 1) - (k + 1)) = 1 := by simp [hsymm_zero]
      simp only [h0, mul_one] at ng
      -- ng says: (-1)^{k+1} * e_{k+1} + ∑_{j=0}^k (-1)^j e_j h_{k+1-j} = 0
      -- Rearrange to get: (-1)^{k+1} * e_{k+1} = - ∑_{j=0}^k (-1)^j e_j h_{k+1-j}
      have h1 : (-1 : P K N) ^ (k + 1) * esymm (Fin N) K (k + 1) =
          - ∑ j ∈ range (k + 1), (-1 : P K N) ^ j * e (K := K) (N := N) j * h (k + 1 - j) := by
        have hzero : (-1 : P K N) ^ (k + 1) * e (k + 1) +
            ∑ x ∈ range (k + 1), (-1 : P K N) ^ x * e x * h (k + 1 - x) = 0 := ng
        calc (-1 : P K N) ^ (k + 1) * e (k + 1)
            = (-1 : P K N) ^ (k + 1) * e (k + 1) +
                ∑ x ∈ range (k + 1), (-1 : P K N) ^ x * e x * h (k + 1 - x) -
                ∑ x ∈ range (k + 1), (-1 : P K N) ^ x * e x * h (k + 1 - x) := by ring
          _ = 0 - ∑ x ∈ range (k + 1), (-1 : P K N) ^ x * e x * h (k + 1 - x) := by rw [hzero]
          _ = - ∑ x ∈ range (k + 1), (-1 : P K N) ^ x * e x * h (k + 1 - x) := by ring
      -- Now: e_{k+1} = (-1)^{k+1} * (- ∑ ...) since (-1)^{k+1} * (-1)^{k+1} = 1
      have h2 : (-1 : P K N) ^ (k + 1) * (-1 : P K N) ^ (k + 1) = 1 := by
        rw [← pow_add, ← two_mul]
        simp [pow_mul]
      have heq : esymm (Fin N) K (k + 1) =
          (-1 : P K N) ^ (k + 1) * (- ∑ j ∈ range (k + 1), (-1 : P K N) ^ j * e (K := K) (N := N) j * h (k + 1 - j)) := by
        calc esymm (Fin N) K (k + 1)
            = 1 * esymm (Fin N) K (k + 1) := by ring
          _ = ((-1 : P K N) ^ (k + 1) * (-1 : P K N) ^ (k + 1)) * esymm (Fin N) K (k + 1) := by rw [h2]
          _ = (-1 : P K N) ^ (k + 1) * ((-1 : P K N) ^ (k + 1) * esymm (Fin N) K (k + 1)) := by ring
          _ = (-1 : P K N) ^ (k + 1) * (- ∑ j ∈ range (k + 1), (-1 : P K N) ^ j * e (K := K) (N := N) j * h (k + 1 - j)) := by rw [h1]
      rw [heq]
      -- Now show the RHS is in hsymmRange
      apply Subalgebra.mul_mem
      · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _
      · apply Subalgebra.neg_mem
        apply Subalgebra.sum_mem
        intro j hj
        rw [mem_range] at hj
        apply Subalgebra.mul_mem
        · apply Subalgebra.mul_mem
          · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _
          · exact ih j hj (by omega)  -- e_j ∈ hsymmRange by IH
        · -- h_{k+1-j} ∈ hsymmRange since 0 < k+1-j ≤ N
          have hpos : 0 < k + 1 - j := by omega
          have hle : k + 1 - j ≤ N := by omega
          exact hsymm_mem_hsymmRange (k + 1 - j) hpos hle

/-- aeval of esymm's is in hsymmRange.
    Label: thm.sf.ftsf -/
private lemma aeval_esymm_mem_hsymmRange (g : MvPolynomial (Fin N) K) :
    aeval (fun i : Fin N => esymm (Fin N) K (i + 1)) g ∈ hsymmRange := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C]
    exact Subalgebra.algebraMap_mem hsymmRange c
  | add p q hp hq =>
    simp only [map_add]
    exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
    simp only [map_mul, aeval_X]
    apply Subalgebra.mul_mem _ hp
    have hi : (i : ℕ) + 1 ≤ N := Nat.add_one_le_iff.mpr i.isLt
    exact esymm_mem_hsymmRange (i + 1) hi

/-- Every symmetric polynomial can be uniquely written as a polynomial in h_1, ..., h_N.
    (Theorem thm.sf.ftsf (b), generation part).
    Label: thm.sf.ftsf -/
theorem hsymm_generates_symmetric [IsDomain K] (f : S K N) :
    ∃! g : MvPolynomial (Fin N) K,
      aeval (fun i : Fin N => (hsymm (Fin N) K (i + 1) : P K N)) g = (f : P K N) := by
  -- Injectivity follows from algebraic independence
  have h_inj : Function.Injective (hsymmAeval (K := K) (N := N)) := by
    have := hsymm_algebraicIndependent (K := K) (N := N)
    rw [algebraicIndependent_iff_injective_aeval] at this
    exact this
  -- Existence: f is in the range of hsymmAeval via esymmAlgHom
  have h_card : Fintype.card (Fin N) = N := Fintype.card_fin N
  obtain ⟨g_esymm, hg_esymm⟩ := esymmAlgHom_surjective K h_card.le f
  -- The range of hsymmAeval contains all symmetric polynomials
  have h_f_in_range : (f : P K N) ∈ (hsymmRange (K := K) (N := N)) := by
    rw [← hg_esymm, esymmAlgHom_apply]
    exact aeval_esymm_mem_hsymmRange g_esymm
  -- Now we can conclude
  obtain ⟨g, hg⟩ := h_f_in_range
  refine ⟨g, hg, ?_⟩
  intro y hy
  exact h_inj (hy.trans hg.symm)

end PartB

/-!
### Part (c): Power Sums (over ℚ-algebras)

When K is a ℚ-algebra (e.g., K = ℚ, ℝ, ℂ, or any field of characteristic 0),
the power sums p_1, p_2, ..., p_N are also algebraically independent and generate S.

Note: This fails in positive characteristic. For example, over 𝔽_p, we have
p_p = x_1^p + ... + x_N^p = (x_1 + ... + x_N)^p = p_1^p by the Frobenius endomorphism.
-/

section PartC

variable [Algebra ℚ K] [IsDomain K]

/-! ### Weight argument infrastructure for power sum algebraic independence

The key insight for proving the triangular structure of ψ(X_i) is a weight argument:
- Define weight(X_k) = k+1 for variables X_k in MvPolynomial (Fin N) K
- The map psumAeval' sends X_k to psum(k+1), which is homogeneous of degree k+1
- Therefore psumAeval' maps polynomials of weighted degree w to polynomials of total degree w
- Since esymm(i+1) has total degree i+1, any polynomial P with psumAeval'(P) = esymm(i+1)
  must have all monomials with weighted degree i+1
- This constrains which variables can appear in P with which exponents
-/

/-- The weight function for power sum analysis: X_k has weight k+1 -/
private def psumWeight' : Fin N → ℕ := fun k => k.val + 1

omit [Algebra ℚ K] [IsDomain K] in
/-- psum(n) is homogeneous of degree n -/
private lemma psum_isHomogeneous (n : ℕ) : (psum (Fin N) K n).IsHomogeneous n := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_X_pow i n

omit [Algebra ℚ K] in
/-- psum(n) ≠ 0 when N > 0 and n > 0 -/
private lemma psum_ne_zero (hN : 0 < N) (n : ℕ) (hn : n > 0) : psum (Fin N) K n ≠ 0 := by
  rw [psum]
  have i₀ : Fin N := ⟨0, hN⟩
  apply ne_zero_iff.mpr
  use Finsupp.single i₀ n
  rw [coeff_sum]
  have heq : (∑ x : Fin N, (X x ^ n).coeff (Finsupp.single i₀ n)) = (1 : K) := by
    rw [Fintype.sum_eq_single i₀]
    · rw [coeff_X_pow, ite_eq_left rfl]
    · intro j hj
      rw [coeff_X_pow, ite_eq_right]
      intro heq
      rw [Finsupp.single_eq_single_iff] at heq
      cases heq with
      | inl h => exact hj h.1
      | inr h => exact hn.ne' h.2
  intro h
  rw [heq] at h
  exact one_ne_zero h

omit [Algebra ℚ K] [IsDomain K] in
/-- Key lemma: psumAeval' maps weighted homogeneous polynomials to homogeneous polynomials -/
private lemma psumAeval_preserves_homogeneous (P : MvPolynomial (Fin N) K) (w : ℕ)
    (hP : P.IsWeightedHomogeneous psumWeight' w) :
    (aeval (fun i : Fin N => psum (Fin N) K (i.val + 1)) P).IsHomogeneous w := by
  rw [as_sum P, map_sum]
  apply IsHomogeneous.sum
  intro d hd
  rw [monomial_eq, map_mul]
  have hC : (aeval (fun i : Fin N => psum (Fin N) K (i.val + 1))) (C (P.coeff d)) = C (P.coeff d) := by
    simp [algebraMap_eq]
  rw [hC]
  have h1 : (C (P.coeff d) : MvPolynomial (Fin N) K).IsHomogeneous 0 := isHomogeneous_C _ _
  have h2 : ((aeval (fun i : Fin N => psum (Fin N) K (i.val + 1))) (d.prod fun i n => (X i : MvPolynomial (Fin N) K) ^ n)).IsHomogeneous
      (Finsupp.weight psumWeight' d) := by
    rw [Finsupp.prod, map_prod]
    have h3 : ∀ i ∈ d.support, ((aeval (fun i : Fin N => psum (Fin N) K (i.val + 1))) ((X i : MvPolynomial (Fin N) K) ^ d i)).IsHomogeneous
        ((i.val + 1) * d i) := by
      intro i _
      simp only [map_pow, aeval_X]
      exact (psum_isHomogeneous (i.val + 1)).pow (d i)
    have h4 : (∏ x ∈ d.support, (aeval (fun i : Fin N => psum (Fin N) K (i.val + 1))) ((X x : MvPolynomial (Fin N) K) ^ d x)).IsHomogeneous
        (∑ x ∈ d.support, (x.val + 1) * d x) := by
      apply IsHomogeneous.prod
      intro i hi
      exact h3 i hi
    convert h4 using 1
    rw [Finsupp.weight_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro x _
    simp [psumWeight', mul_comm]
  have hw : Finsupp.weight psumWeight' d = w := by
    apply hP
    rw [mem_support_iff] at hd
    exact hd
  rw [hw] at h2
  simpa using h1.mul h2

/-- Weight bound: if d has a variable X_j with j ≥ i in its support, then weight(d) ≥ i+1 -/
private lemma weight_bound (d : Fin N →₀ ℕ) (i : Fin N) 
    (hj : ∃ j : Fin N, j ≥ i ∧ j ∈ d.support) :
    Finsupp.weight psumWeight' d ≥ i.val + 1 := by
  obtain ⟨j, hj_ge, hj_supp⟩ := hj
  rw [Finsupp.weight_apply, Finsupp.sum]
  have h1 : d j * (j.val + 1) ≤ ∑ a ∈ d.support, d a * (a.val + 1) := by
    apply Finset.single_le_sum (f := fun a => d a * (a.val + 1))
    · intro k _; exact Nat.zero_le _
    · exact hj_supp
  have h2 : i.val + 1 ≤ d j * (j.val + 1) := by
    have hd_pos : d j ≥ 1 := Finsupp.mem_support_iff.mp hj_supp |> Nat.one_le_iff_ne_zero.mpr
    calc i.val + 1 ≤ j.val + 1 := by omega
      _ = 1 * (j.val + 1) := by ring
      _ ≤ d j * (j.val + 1) := by apply Nat.mul_le_mul_right; exact hd_pos
  calc i.val + 1 ≤ d j * (j.val + 1) := h2
    _ ≤ ∑ a ∈ d.support, d a * (a.val + 1) := h1
    _ = ∑ a ∈ d.support, d a • (a.val + 1) := by simp [smul_eq_mul]

/-- If a monomial has weighted degree i+1 and contains variable X_i, then it must be exactly X_i.
    This is because X_i has weight i+1, so any other variable or higher power would exceed the weight.
    
    This is a key lemma for the triangular structure of ψ(X_i) in the algebraic independence proof. -/
private lemma monomial_with_var_i_is_single (i : Fin N) (d : Fin N →₀ ℕ) 
    (hd : Finsupp.weight psumWeight' d = i.val + 1)
    (hi : i ∈ d.support) : d = Finsupp.single i 1 := by
  ext j
  by_cases hj : j = i
  · -- j = i case: d i must equal 1
    subst hj
    have h1 : d j ≥ 1 := Finsupp.mem_support_iff.mp hi |> Nat.one_le_iff_ne_zero.mpr
    have h2 : d j * (j.val + 1) ≤ Finsupp.weight psumWeight' d := by
      rw [Finsupp.weight_apply, Finsupp.sum]
      have hconv : ∀ a, d a • psumWeight' a = d a * (a.val + 1) := fun a => by 
        simp [psumWeight', smul_eq_mul]
      simp_rw [hconv]
      have hle : (fun x : Fin N => d x * (x.val + 1)) j ≤ ∑ x ∈ d.support, (fun x : Fin N => d x * (x.val + 1)) x :=
        Finset.single_le_sum (f := fun x : Fin N => d x * (x.val + 1)) (fun k _ => Nat.zero_le _) hi
      exact hle
    have h3 : d j * (j.val + 1) ≤ j.val + 1 := by rw [hd] at h2; exact h2
    have h4 : d j ≤ 1 := by
      by_contra h
      push Not at h
      have : d j * (j.val + 1) ≥ 2 * (j.val + 1) := by nlinarith
      omega
    simp only [Finsupp.single_eq_same]
    omega
  · -- j ≠ i case: d j must equal 0
    simp only [ne_eq, hj, not_false_eq_true, Finsupp.single_eq_of_ne]
    by_contra hj'
    have hj_supp : j ∈ d.support := Finsupp.mem_support_iff.mpr hj'
    have h1 : d j ≥ 1 := Nat.one_le_iff_ne_zero.mpr hj'
    have h2 : d i ≥ 1 := Finsupp.mem_support_iff.mp hi |> Nat.one_le_iff_ne_zero.mpr
    have h3 : Finsupp.weight psumWeight' d ≥ d j * (j.val + 1) + d i * (i.val + 1) := by
      rw [Finsupp.weight_apply, Finsupp.sum]
      have hne : j ≠ i := hj
      have hconv : ∀ a, d a • psumWeight' a = d a * (a.val + 1) := fun a => by 
        simp [psumWeight', smul_eq_mul]
      simp_rw [hconv]
      calc ∑ a ∈ d.support, d a * (a.val + 1) 
          ≥ ∑ a ∈ ({j, i} : Finset (Fin N)), d a * (a.val + 1) := by
            apply Finset.sum_le_sum_of_subset
            intro x hx
            simp only [mem_insert, mem_singleton] at hx
            cases hx with
            | inl h => subst h; exact hj_supp
            | inr h => subst h; exact hi
        _ = d j * (j.val + 1) + d i * (i.val + 1) := by
            rw [sum_insert (by simp [hne]), sum_singleton]
    have h4 : d j * (j.val + 1) + d i * (i.val + 1) ≥ 1 + (i.val + 1) := by
      calc d j * (j.val + 1) + d i * (i.val + 1) 
          ≥ 1 * 1 + 1 * (i.val + 1) := by nlinarith
        _ = 1 + (i.val + 1) := by ring
    have h5 : Finsupp.weight psumWeight' d ≥ i.val + 2 := by omega
    omega

omit [Algebra ℚ K] [IsDomain K] in
/-- esymm(n) is homogeneous of degree n -/
private lemma esymm_isHomogeneous' (n : ℕ) : (esymm (Fin N) K n).IsHomogeneous n := by
  rw [esymm]
  apply IsHomogeneous.sum
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  have : (∏ i ∈ t, X i : MvPolynomial (Fin N) K).IsHomogeneous t.card := by
    rw [show t.card = ∑ _ ∈ t, 1 by simp]
    apply IsHomogeneous.prod
    intro i _
    exact isHomogeneous_X K i
  rw [ht.2] at this
  exact this

omit [Algebra ℚ K] [IsDomain K] in
/-- Key lemma: homogeneousComponent commutes with psumAeval' in the sense that
    homogeneousComponent w (psumAeval'(P)) = psumAeval'(weightedHomogeneousComponent w P).
    
    This follows from the fact that psumAeval' maps weighted degree to total degree:
    each monomial in P with weighted degree w' maps to a homogeneous polynomial of degree w'.
    Therefore, taking the homogeneous component of degree w extracts exactly the image of
    the weighted homogeneous component of degree w. -/
private lemma homogeneousComponent_psumAeval_eq (P : MvPolynomial (Fin N) K) (w : ℕ) :
    homogeneousComponent w (aeval (fun k : Fin N => psum (Fin N) K (k.val + 1)) P) = 
    aeval (fun k : Fin N => psum (Fin N) K (k.val + 1)) (weightedHomogeneousComponent psumWeight' w P) := by
  conv_lhs => rw [as_sum P, map_sum]
  conv_rhs => rw [weightedHomogeneousComponent_apply, map_sum]
  rw [map_sum]  -- homogeneousComponent is a linear map
  rw [sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have h_hom : (aeval (fun k : Fin N => psum (Fin N) K (k.val + 1)) (monomial d (P.coeff d))).IsHomogeneous
      (Finsupp.weight psumWeight' d) := by
    apply psumAeval_preserves_homogeneous
    exact isWeightedHomogeneous_monomial psumWeight' d (P.coeff d) rfl
  have h_mem : aeval (fun k : Fin N => psum (Fin N) K (k.val + 1)) (monomial d (P.coeff d)) ∈
      homogeneousSubmodule (Fin N) K (Finsupp.weight psumWeight' d) := by
    rw [mem_homogeneousSubmodule]; exact h_hom
  rw [homogeneousComponent_of_mem h_mem]
  split_ifs with h_eq h_eq'
  · rfl
  · omega
  · omega
  · rfl


/-- Helper lemma: The polynomial P such that psumAeval'(P) = esymm(k+1) has a triangular form.
    Specifically, P = c_k * X_k + q where c_k = (-1)^k / (k+1) and q only involves X_j for j < k.
    
    This is used to prove that ψ(X_i) has the triangular structure needed for the 
    algebraic independence proof of power sums.
    
    The proof uses Newton's identity and strong induction on k. The key insight is that
    Newton's identity expresses e_{k+1} as a linear combination where the term with
    coefficient (-1)^k / (k+1) involves p_{k+1} = psumAeval'(X_k), and all other terms
    involve e_j for j < k+1 (which by induction only use X_m for m < j-1 < k). -/
private lemma esymm_triangular_poly_aux (psumAeval' : MvPolynomial (Fin N) K →ₐ[K] P K N)
    (h_psumAeval' : psumAeval' = aeval (fun i : Fin N => psum (Fin N) K (i + 1)))
    (k : ℕ) (hk : k ≤ N) :
    ∃ Q : MvPolynomial (Fin N) K, 
      psumAeval' Q = esymm (Fin N) K k ∧ 
      (k = 0 → Q = 1) ∧
      (∀ (hk_pos : 0 < k), ∃ q : MvPolynomial (Fin N) K,
          (∀ j ∈ q.vars, (j : ℕ) < k - 1) ∧
          Q = C (algebraMap ℚ K ((-1 : ℚ)^(k-1) / k)) * X ⟨k - 1, Nat.sub_lt hk_pos Nat.one_pos |>.trans_le hk⟩ + q) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      use 1
      refine ⟨?_, ?_, ?_⟩
      · simp only [esymm_zero, map_one]
      · intro _; rfl
      · intro h; omega
    | succ k =>
      -- The proof uses Newton's identity and strong induction
      -- Newton: (k+1) * e_{k+1} = (-1)^{k+2} * Σ_{a < k+1} (-1)^a * e_a * p_{k+1-a}
      -- This gives e_{k+1} = (-1)^k/(k+1) * p_{k+1} + (lower terms)
      -- The lower terms involve e_a for a > 0, which by IH only use X_j for j < a-1 < k
      -- Therefore e_{k+1} = (-1)^k/(k+1) * psumAeval'(X_k) + psumAeval'(q) where q.vars < k
      
      -- Newton's identity: (k+1) * esymm(k+1) = (-1)^(k+2) * ∑_{a.1 < k+1} (-1)^a.1 * esymm(a.1) * psum(a.2)
      have newton := mul_esymm_eq_sum (Fin N) K (k + 1)
      
      -- (k+1) is invertible in K since K is a ℚ-algebra
      have h_inv : IsUnit ((k + 1 : ℕ) : K) := by
        have h : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
        have hunit : IsUnit ((k + 1 : ℕ) : ℚ) := isUnit_iff_ne_zero.mpr h
        have := hunit.map (algebraMap ℚ K)
        simp only [map_natCast] at this
        exact this
      obtain ⟨u, hu⟩ := h_inv
      
      -- The antidiagonal set and its split
      let S := (antidiagonal (k + 1)).filter (fun a => a.1 < k + 1)
      let S' := S.filter (fun a => 0 < a.1)
      
      have h_mem_0 : (0, k + 1) ∈ S := by simp [S, Finset.HasAntidiagonal.mem_antidiagonal]
      have h_nmem_0 : (0, k + 1) ∉ S' := by simp [S', S, Finset.HasAntidiagonal.mem_antidiagonal]
      have h_S_eq : S = insert (0, k + 1) S' := by
        ext a
        simp only [S, S', mem_insert, mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
        constructor
        · intro ⟨ha, hlt⟩
          by_cases h0 : a.1 = 0
          · left; ext <;> omega
          · right; exact ⟨⟨ha, hlt⟩, Nat.pos_of_ne_zero h0⟩
        · intro h
          cases h with
          | inl heq => simp only [heq]; omega
          | inr hright => exact ⟨hright.1.1, hright.1.2⟩
      
      -- By IH, for each m < k+1 with m ≤ N, there exists Q_m with psumAeval'(Q_m) = esymm(m)
      -- and var bounds when m > 0
      have h_ih_exists_full : ∀ m, m < k + 1 → m ≤ N → 
          ∃ Q_m : MvPolynomial (Fin N) K, psumAeval' Q_m = esymm (Fin N) K m ∧ 
            (∀ j ∈ Q_m.vars, (j : ℕ) < m) := by
        intro m hm hm_le
        obtain ⟨Q_m, hQ_m_eval, hQ_m_zero, hQ_m_struct⟩ := ih m hm hm_le
        refine ⟨Q_m, hQ_m_eval, ?_⟩
        intro j hj
        by_cases hm_pos : m = 0
        · -- If m = 0, then Q_m = 1, so Q_m.vars = ∅
          have hQ_m_eq_1 := hQ_m_zero hm_pos
          rw [hQ_m_eq_1] at hj
          simp at hj
        · -- If m > 0, use the triangular structure
          have hm_pos' : 0 < m := Nat.pos_of_ne_zero hm_pos
          obtain ⟨q_m, hq_m_vars, hQ_m_eq⟩ := hQ_m_struct hm_pos'
          rw [hQ_m_eq] at hj
          have h_idx : m - 1 < N := Nat.sub_lt hm_pos' Nat.one_pos |>.trans_le hm_le
          have h_vars_add : (C (algebraMap ℚ K ((-1 : ℚ)^(m-1) / m)) * X (⟨m - 1, h_idx⟩ : Fin N) + q_m).vars ⊆ 
              (C (algebraMap ℚ K ((-1 : ℚ)^(m-1) / m)) * X (⟨m - 1, h_idx⟩ : Fin N)).vars ∪ q_m.vars := vars_add_subset _ _
          have hj' := h_vars_add hj
          simp only [mem_union] at hj'
          rcases hj' with hj_CX | hj_q
          · have h_vars_CX : (C (algebraMap ℚ K ((-1 : ℚ)^(m-1) / m)) * X (⟨m - 1, h_idx⟩ : Fin N) : MvPolynomial (Fin N) K).vars ⊆ 
                (C (algebraMap ℚ K ((-1 : ℚ)^(m-1) / m))).vars ∪ (X (⟨m - 1, h_idx⟩ : Fin N)).vars := vars_mul _ _
            have hj'' := h_vars_CX hj_CX
            simp only [vars_C, empty_union, vars_X, mem_singleton] at hj''
            simp only [hj'']; omega
          · have hj_lt := hq_m_vars j hj_q; omega
      
      have h_S'_bound : ∀ a ∈ S', a.1 < k + 1 ∧ a.1 ≤ N ∧ 0 < a.2 ∧ a.2 ≤ N := by
        intro a ha
        simp only [S', S, mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        omega
      
      have h_ih_S'_full : ∀ a ∈ S', ∃ Q_a : MvPolynomial (Fin N) K, 
          psumAeval' Q_a = esymm (Fin N) K a.1 ∧ (∀ j ∈ Q_a.vars, (j : ℕ) < a.1) := by
        intro a ha
        have ⟨hlt, hle, _, _⟩ := h_S'_bound a ha
        exact h_ih_exists_full a.1 hlt hle
      
      choose Q_a hQ_a_spec using h_ih_S'_full
      
      have hQ_a : ∀ a (ha : a ∈ S'), psumAeval' (Q_a a ha) = esymm (Fin N) K a.1 := 
        fun a ha => (hQ_a_spec a ha).1
      
      have hQ_a_vars : ∀ a (ha : a ∈ S'), ∀ j ∈ (Q_a a ha).vars, (j : ℕ) < a.1 := 
        fun a ha => (hQ_a_spec a ha).2
      
      -- For psum(a.2), define Q_p directly as X_{a.2-1}
      let Q_p : (a : ℕ × ℕ) → a ∈ S' → MvPolynomial (Fin N) K := 
        fun a ha => X ⟨a.2 - 1, by have := h_S'_bound a ha; omega⟩
      
      have hQ_p : ∀ a (ha : a ∈ S'), psumAeval' (Q_p a ha) = psum (Fin N) K a.2 := by
        intro a ha
        simp only [Q_p, h_psumAeval', aeval_X]
        congr 1
        have ⟨_, _, hpos, _⟩ := h_S'_bound a ha
        omega
      
      -- Construct Q_sum = ∑_{a ∈ S'} (-1)^a.1 * Q_a * Q_p
      let Q_sum : MvPolynomial (Fin N) K := ∑ a ∈ S'.attach, (-1 : MvPolynomial (Fin N) K) ^ a.val.1 * Q_a a.val a.prop * Q_p a.val a.prop
      
      -- psumAeval'(Q_sum) = ∑_{a ∈ S'} (-1)^a.1 * esymm(a.1) * psum(a.2)
      have hQ_sum_eval : psumAeval' Q_sum = ∑ a ∈ S', (-1 : P K N) ^ a.1 * esymm (Fin N) K a.1 * psum (Fin N) K a.2 := by
        simp only [Q_sum, map_sum, map_mul, map_pow, map_neg, map_one]
        conv_rhs => rw [← sum_attach]
        apply sum_congr rfl
        intro ⟨a, ha⟩ _
        simp only [hQ_a a ha, hQ_p a ha]
      
      -- psum(k+1) = psumAeval'(X_k)
      have h_psum_k1 : k < N := by omega
      have h_psum_aeval_k1 : psumAeval' (X ⟨k, h_psum_k1⟩) = psum (Fin N) K (k + 1) := by
        rw [h_psumAeval']
        simp only [aeval_X]
      
      -- Coefficient c = (-1)^k / (k+1)
      let c : ℚ := (-1 : ℚ)^k / (k + 1)
      
      -- Construct Q = C(c) * X_k + C(c) * Q_sum
      let Q : MvPolynomial (Fin N) K := C (algebraMap ℚ K c) * X ⟨k, h_psum_k1⟩ + C (algebraMap ℚ K c) * Q_sum
      
      -- The key algebraic identity: psumAeval'(Q) = esymm(k+1)
      -- This follows from Newton's identity after dividing by (k+1)
      have hQ_eval : psumAeval' Q = esymm (Fin N) K (k + 1) := by
        -- Step 1: Compute psumAeval' Q
        -- psumAeval' (C r) = C r since AlgHoms preserve constants
        have h_aeval_C : psumAeval' (C (algebraMap ℚ K c)) = C (algebraMap ℚ K c) := by
          have : C (algebraMap ℚ K c) = algebraMap K (MvPolynomial (Fin N) K) (algebraMap ℚ K c) := rfl
          rw [this]
          exact psumAeval'.commutes (algebraMap ℚ K c)
        have h_eval : psumAeval' Q = C (algebraMap ℚ K c) * psum (Fin N) K (k + 1) + 
            C (algebraMap ℚ K c) * ∑ a ∈ S', (-1 : P K N) ^ a.1 * esymm (Fin N) K a.1 * psum (Fin N) K a.2 := by
          simp only [Q, map_add, map_mul, h_aeval_C, h_psum_aeval_k1, hQ_sum_eval]
        rw [h_eval]
        -- Step 2: Apply Newton formula to show this equals esymm(k+1)
        -- Newton: (k+1) * esymm(k+1) = (-1)^(k+2) * Σ_S ...
        -- After splitting S = {(0,k+1)} ∪ S' and using (-1)^(k+2) = (-1)^k:
        -- (k+1) * esymm(k+1) = (-1)^k * (psum(k+1) + Σ_{S'} ...)
        -- Multiplying by (k+1)⁻¹ gives the result
        have hne_Q : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
        have h_sum_split : ∑ a ∈ S, (-1 : P K N)^a.1 * esymm (Fin N) K a.1 * psum (Fin N) K a.2 = 
          psum (Fin N) K (k + 1) + ∑ a ∈ S', (-1 : P K N)^a.1 * esymm (Fin N) K a.1 * psum (Fin N) K a.2 := by
          conv_lhs => rw [h_S_eq, sum_insert h_nmem_0]
          simp only [pow_zero, esymm_zero, one_mul]
        have h_pow : (-1 : P K N)^(k + 1 + 1) = (-1 : P K N)^k := by
          rw [show k + 1 + 1 = k + 2 by ring, pow_add]
          simp [sq]
        have newton' := newton
        rw [h_sum_split, h_pow] at newton'
        have h_inv_cancel : C (algebraMap ℚ K ((k + 1 : ℕ) : ℚ)⁻¹) * ((k + 1 : ℕ) : P K N) = 1 := by
          have h1 : ((k + 1 : ℕ) : P K N) = C (algebraMap ℚ K ((k + 1 : ℕ) : ℚ)) := by simp
          rw [h1, ← map_mul, ← map_mul (algebraMap ℚ K), inv_mul_cancel₀ hne_Q, map_one, map_one]
        have h_coeff : (-1 : P K N)^k * C (algebraMap ℚ K ((k + 1 : ℕ) : ℚ)⁻¹) = C (algebraMap ℚ K c) := by
          have h1 : c = (-1 : ℚ)^k * ((k + 1 : ℕ) : ℚ)⁻¹ := by 
            simp only [c]
            have : (↑k + 1 : ℚ) = ((k + 1 : ℕ) : ℚ) := by simp
            rw [this, div_eq_mul_inv]
          rw [h1]
          simp only [map_mul, map_pow, map_neg, map_one]
        let sum'' := ∑ a ∈ S', (-1 : P K N)^a.1 * esymm (Fin N) K a.1 * psum (Fin N) K a.2
        symm
        calc esymm (Fin N) K (k + 1) 
            = C (algebraMap ℚ K ((k + 1 : ℕ) : ℚ)⁻¹) * ((k + 1 : ℕ) : P K N) * esymm (Fin N) K (k + 1) := by
              rw [h_inv_cancel, one_mul]
          _ = C (algebraMap ℚ K ((k + 1 : ℕ) : ℚ)⁻¹) * (((k + 1 : ℕ) : P K N) * esymm (Fin N) K (k + 1)) := by ring
          _ = C (algebraMap ℚ K ((k + 1 : ℕ) : ℚ)⁻¹) * ((-1 : P K N)^k * (psum (Fin N) K (k + 1) + sum'')) := by
              rw [newton']
          _ = (-1 : P K N)^k * C (algebraMap ℚ K ((k + 1 : ℕ) : ℚ)⁻¹) * (psum (Fin N) K (k + 1) + sum'') := by ring
          _ = C (algebraMap ℚ K c) * (psum (Fin N) K (k + 1) + sum'') := by rw [h_coeff]
          _ = C (algebraMap ℚ K c) * psum (Fin N) K (k + 1) + C (algebraMap ℚ K c) * sum'' := by ring
      
      use Q
      refine ⟨hQ_eval, ?_, ?_⟩
      · intro h; omega
      · intro hk_pos
        use C (algebraMap ℚ K c) * Q_sum
        constructor
        · -- vars of C c * Q_sum are < k
          -- This follows because:
          -- - vars of Q_a are < a.1 (by IH)
          -- - vars of Q_p are < a.2 (since Q_p = X_{a.2-1})
          -- - For a ∈ S', a.1 + a.2 = k+1 and 0 < a.1 < k+1
          -- - So max(a.1 - 1, a.2 - 1) < k
          intro j hj
          have h_vars_C_mul : (C (algebraMap ℚ K c) * Q_sum).vars ⊆ Q_sum.vars := by
            calc (C (algebraMap ℚ K c) * Q_sum).vars 
                ⊆ (C (algebraMap ℚ K c)).vars ∪ Q_sum.vars := vars_mul _ _
              _ = ∅ ∪ Q_sum.vars := by rw [vars_C]
              _ = Q_sum.vars := empty_union _
          have hj' := h_vars_C_mul hj
          -- The bound j < k follows from tracking vars through the sum
          -- Each term in Q_sum has vars bounded by max(a.1-1, a.2-1) < k
          
          -- Use vars_sum_subset
          have h_sum_vars : Q_sum.vars ⊆ S'.attach.biUnion (fun a => 
              ((-1 : MvPolynomial (Fin N) K)^a.val.1 * Q_a a.val a.prop * Q_p a.val a.prop).vars) :=
            vars_sum_subset _ _
          have hj'' := h_sum_vars hj'
          simp only [mem_biUnion, mem_attach, true_and, Subtype.exists] at hj''
          obtain ⟨a, ha, hj_in_term⟩ := hj''
          
          -- vars((-1)^a.1) = ∅
          have h_neg1_vars : ((-1 : MvPolynomial (Fin N) K)^a.1).vars = ∅ := by
            have h : (-1 : MvPolynomial (Fin N) K) = C (-1 : K) := by simp
            rw [h, ← C_pow]; exact vars_C
          
          -- vars((-1)^a.1 * Q_a * Q_p) ⊆ vars(Q_a) ∪ vars(Q_p)
          have h_term_vars : ((-1 : MvPolynomial (Fin N) K)^a.1 * Q_a a ha * Q_p a ha).vars ⊆ 
              (Q_a a ha).vars ∪ (Q_p a ha).vars := by
            calc ((-1 : MvPolynomial (Fin N) K)^a.1 * Q_a a ha * Q_p a ha).vars
                ⊆ ((-1 : MvPolynomial (Fin N) K)^a.1 * Q_a a ha).vars ∪ (Q_p a ha).vars := vars_mul _ _
              _ ⊆ (((-1 : MvPolynomial (Fin N) K)^a.1).vars ∪ (Q_a a ha).vars) ∪ (Q_p a ha).vars := by
                  apply Finset.union_subset_union_left; exact vars_mul _ _
              _ = (∅ ∪ (Q_a a ha).vars) ∪ (Q_p a ha).vars := by rw [h_neg1_vars]
              _ = (Q_a a ha).vars ∪ (Q_p a ha).vars := by rw [empty_union]
          
          have hj''' := h_term_vars hj_in_term
          simp only [mem_union] at hj'''
          
          -- Get bounds on a from S'
          have h_a_bound : a.1 + a.2 = k + 1 ∧ 0 < a.1 ∧ a.1 < k + 1 := by
            simp only [S', S, mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
            exact ⟨ha.1.1, ha.2, ha.1.2⟩
          
          rcases hj''' with hj_Qa | hj_Qp
          · -- j ∈ vars(Q_a), so j.val < a.1 ≤ k
            have hj_lt_a1 := hQ_a_vars a ha j hj_Qa
            omega
          · -- j ∈ vars(Q_p) = {a.2 - 1}
            -- Q_p a ha = X ⟨a.2 - 1, _⟩ by construction
            have h_Qp_def : Q_p a ha = X ⟨a.2 - 1, by have := h_S'_bound a ha; omega⟩ := rfl
            rw [h_Qp_def] at hj_Qp
            have h_idx : a.2 - 1 < N := by have := h_S'_bound a ha; omega
            have h_vars_X : (X ⟨a.2 - 1, h_idx⟩ : MvPolynomial (Fin N) K).vars = {⟨a.2 - 1, h_idx⟩} := vars_X
            rw [h_vars_X, mem_singleton] at hj_Qp
            simp only [hj_Qp]
            -- a.2 - 1 < k because a.1 > 0 and a.1 + a.2 = k + 1
            omega
        · -- Q = C c * X_k + C c * Q_sum
          simp only [Q]
          -- Need to show the coefficient and index match
          have h_c_eq : algebraMap ℚ K c = algebraMap ℚ K ((-1 : ℚ)^((k + 1) - 1) / (k + 1)) := by
            simp only [c, Nat.add_sub_cancel]
          have h_idx_eq : (⟨k, h_psum_k1⟩ : Fin N) = ⟨(k + 1) - 1, Nat.sub_lt (Nat.succ_pos k) Nat.one_pos |>.trans_le hk⟩ := by
            simp only [Nat.add_sub_cancel]
          rw [h_c_eq, h_idx_eq]
          -- The denominators (↑k + 1) and ↑(k + 1) are equal
          congr 2
          simp only [Nat.cast_add, Nat.cast_one]


/-- The power sums p_1, ..., p_N are algebraically independent over a ℚ-algebra.
    (Theorem thm.sf.ftsf (c), algebraic independence part).

    The proof follows the same strategy as for hsymm_algebraicIndependent:
    1. The map aeval psum lands in S K N (since psum is symmetric)
    2. Factor aeval psum as: MvPolynomial → S K N → P K N
    3. The composition esymmAlgEquiv'.symm ∘ (factored map) : MvPolynomial → MvPolynomial is surjective
       (because X_i = esymmAlgEquiv'.symm (esymm (i+1)) and esymm is in the range by Newton's identities)
    4. A surjective algebra endomorphism of K[X_1, ..., X_n] is bijective (transcendence degree argument)
    5. Therefore the factored map is bijective, hence aeval psum is injective

    Label: thm.sf.ftsf -/
theorem psum_algebraicIndependent :
    AlgebraicIndependent K (fun i : Fin N => (psum (Fin N) K (i + 1) : P K N)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  -- Define the aeval map inline
  let psumAeval' : MvPolynomial (Fin N) K →ₐ[K] P K N :=
    aeval (fun i : Fin N => psum (Fin N) K (i + 1))
  -- Step 1: psumAeval' lands in S K N
  have h_symm : ∀ p, (psumAeval' p).IsSymmetric := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c => simp only [psumAeval', aeval_C]; exact IsSymmetric.C c
    | add p q hp hq => simp only [psumAeval', map_add]; exact hp.add hq
    | mul_X p i hp =>
      simp only [psumAeval', map_mul, aeval_X]
      exact hp.mul (psum_isSymmetric (Fin N) K (i + 1))
  -- Step 2: Define the factored map psumToS
  let psumToS : MvPolynomial (Fin N) K →ₐ[K] S K N := {
    toFun := fun p => ⟨psumAeval' p, h_symm p⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
    commutes' := fun r => Subtype.ext (by simp [psumAeval', algebraMap_eq])
  }
  -- Step 3: The composition φ = esymmAlgEquiv'.symm ∘ psumToS
  let φ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K :=
    esymmAlgEquiv'.symm.toAlgHom.comp psumToS
  -- Step 4: φ is bijective
  -- This follows from:
  -- (a) φ is surjective (from Newton's identities: X_i is in the range because
  --     esymm (i+1) is in psumRange, so X_i = esymmAlgEquiv'.symm(esymm(i+1)) is in φ's range)
  -- (b) Surjective algebra endomorphisms of polynomial rings over fields are bijective
  --     (this uses the transcendence degree argument: trdeg is preserved by surjections,
  --      and if f is surjective but not injective, the image of the X variables would be
  --      algebraically dependent, contradicting that they generate an algebra of full trdeg)
  have h_φ_bij : Function.Bijective φ := by
    -- Step 4a: Show that for each i, esymm(i+1) is in the range of psumAeval'
    -- This uses Newton's identities (mul_esymm_eq_sum) and the fact that K is a ℚ-algebra
    have h_psum_range : ∀ k, 0 < k → k ≤ N → ∃ P, psumAeval' P = psum (Fin N) K k := by
      intro k hk hk'
      have h : k - 1 < N := by omega
      use X ⟨k - 1, h⟩
      simp only [psumAeval', aeval_X]
      congr 1; omega
    have h_esymm_range : ∀ k : ℕ, k ≤ N → ∃ P, psumAeval' P = esymm (Fin N) K k := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk
        cases k with
        | zero => use 1; simp only [esymm_zero, map_one]
        | succ k =>
          have newton := mul_esymm_eq_sum (Fin N) K (k + 1)
          let S := (antidiagonal (k + 1)).filter (fun a => a.1 < k + 1)
          have h_term : ∀ a ∈ S, ∃ Q : MvPolynomial (Fin N) K, 
              psumAeval' Q = (-1 : P K N) ^ a.1 * esymm (Fin N) K a.1 * psum (Fin N) K a.2 := by
            intro a ha
            rw [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
            obtain ⟨P_e, hP_e⟩ := ih a.1 ha.2 (by omega)
            obtain ⟨P_p, hP_p⟩ := h_psum_range a.2 (by have := ha.1; omega) (by have := ha.1; omega)
            use (-1) ^ a.1 * P_e * P_p
            simp only [map_mul, map_pow, map_neg, map_one, hP_e, hP_p]
          choose f hf using h_term
          have h_Q_sum : ∃ Q_sum, psumAeval' Q_sum = 
              ∑ a ∈ S, (-1 : P K N) ^ a.1 * esymm (Fin N) K a.1 * psum (Fin N) K a.2 := by
            use ∑ a : S, f a.val a.prop
            rw [map_sum]; conv_rhs => rw [← sum_attach]
            exact sum_congr rfl (fun ⟨a, ha⟩ _ => hf a ha)
          obtain ⟨Q_sum, hQ_sum⟩ := h_Q_sum
          let Q_rhs := (-1 : MvPolynomial (Fin N) K) ^ (k + 1 + 1) * Q_sum
          have hQ_rhs : psumAeval' Q_rhs = (-1 : P K N) ^ (k + 1 + 1) *
              ∑ a ∈ S, (-1) ^ a.1 * esymm (Fin N) K a.1 * psum (Fin N) K a.2 := by
            simp only [Q_rhs, map_mul, map_pow, map_neg, map_one, hQ_sum]
          have h_inv : IsUnit ((k + 1 : ℕ) : K) := by
            have h : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
            have hunit : IsUnit ((k + 1 : ℕ) : ℚ) := isUnit_iff_ne_zero.mpr h
            have := hunit.map (algebraMap ℚ K); simp only [map_natCast] at this; exact this
          obtain ⟨u, hu⟩ := h_inv
          use (C (↑u⁻¹ : K)) * Q_rhs
          simp only [map_mul]
          have hC : psumAeval' (C (↑u⁻¹ : K)) = C (↑u⁻¹ : K) := by
            have := psumAeval'.commutes (↑u⁻¹ : K); simp only [psumAeval', algebraMap_eq] at this; exact this
          rw [hC, hQ_rhs]
          -- newton says: (k+1) * esymm = RHS, so RHS = (k+1) * esymm
          -- We want: C u⁻¹ * RHS = esymm
          -- So: C u⁻¹ * (k+1) * esymm = esymm
          rw [newton.symm, ← mul_assoc]
          have h_cancel : C (↑u⁻¹ : K) * (↑(k + 1) : P K N) = 1 := by
            rw [← C_eq_coe_nat, ← C_mul]
            have h_eq : (↑u⁻¹ : K) * (k + 1 : ℕ) = 1 := by rw [← hu]; simp only [Units.inv_mul]
            rw [h_eq, C_1]
          rw [h_cancel, one_mul]
    -- Step 4b: For each i, get P_i such that psumAeval'(P_i) = esymm(i+1) with triangular structure
    -- Use esymm_triangular_poly_aux to get explicit polynomials with triangular structure
    have h_triangular_polys : ∀ i : Fin N, ∃ Q : MvPolynomial (Fin N) K,
        psumAeval' Q = esymm (Fin N) K (i + 1) ∧
        (∃ q : MvPolynomial (Fin N) K, (∀ j ∈ q.vars, (j : ℕ) < i.val) ∧
          Q = C (algebraMap ℚ K ((-1 : ℚ)^i.val / (i.val + 1))) * X i + q) := by
      intro i
      have h_tri := esymm_triangular_poly_aux psumAeval' rfl (i.val + 1) (Nat.add_one_le_iff.mpr i.isLt)
      obtain ⟨Q, hQ_eval, _, hQ_struct⟩ := h_tri
      use Q
      constructor
      · exact hQ_eval
      · have hi_pos : 0 < i.val + 1 := Nat.succ_pos i.val
        obtain ⟨q_lower, hq_vars, hQ_eq⟩ := hQ_struct hi_pos
        use q_lower
        constructor
        · intro j hj
          have hj_bound := hq_vars j hj
          simp at hj_bound
          exact hj_bound
        · have h_idx : (⟨(i.val + 1) - 1, Nat.sub_lt hi_pos Nat.one_pos |>.trans_le (Nat.add_one_le_iff.mpr i.isLt)⟩ : Fin N) = i := by
            simp only [Nat.add_sub_cancel]
          rw [hQ_eq, h_idx]
          congr 1
          congr 1
          simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    -- Define ψ using the explicit triangular polynomials
    let Q_i : Fin N → MvPolynomial (Fin N) K := fun i => Classical.choose (h_triangular_polys i)
    have hQ_spec : ∀ i : Fin N, psumAeval' (Q_i i) = esymm (Fin N) K (i + 1) ∧
        (∃ q : MvPolynomial (Fin N) K, (∀ j ∈ q.vars, (j : ℕ) < i.val) ∧
          Q_i i = C (algebraMap ℚ K ((-1 : ℚ)^i.val / (i.val + 1))) * X i + q) := 
      fun i => Classical.choose_spec (h_triangular_polys i)
    let ψ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K := aeval Q_i
    -- Also keep h_NG for compatibility
    have h_NG : ∀ i : Fin N, ∃ P : MvPolynomial (Fin N) K, psumAeval' P = esymm (Fin N) K (i + 1) := by
      intro i; use Q_i i; exact (hQ_spec i).1
    -- Key lemma: φ(P) = X_i when psumAeval'(P) = esymm(i+1)
    have h_φ_eq_X : ∀ (P : MvPolynomial (Fin N) K) (i : Fin N),
        psumAeval' P = esymm (Fin N) K (i + 1) → φ P = X i := by
      intro P i hP
      simp only [φ, AlgHom.comp_apply, AlgHom.coe_ofClass]
      have heq : psumToS P = ⟨esymm (Fin N) K (i + 1), esymm_isSymmetric _ _ _⟩ := by
        apply Subtype.ext
        simp only [psumToS, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
        exact hP
      rw [heq]
      exact esymmAlgEquiv_symm_apply (R := K) (Fintype.card_fin N) i
    -- φ ∘ ψ = id on generators
    have h_φψ : ∀ i : Fin N, φ (ψ (X i)) = X i := fun i => by
      simp only [ψ, aeval_X]
      exact h_φ_eq_X _ i (hQ_spec i).1
    -- φ ∘ ψ = id as algebra homomorphisms
    have h_φψ_id : φ.comp ψ = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro i; simp only [AlgHom.comp_apply, AlgHom.id_apply]; exact h_φψ i
    -- For bijectivity, we use transcendence degree:
    -- Step 1: ψ(X_i) are algebraically independent (since ψ is injective from φ ∘ ψ = id)
    have h_ψX_indep : AlgebraicIndependent K (fun i => ψ (X i)) := by
      have h_aeval_eq : aeval (fun i => ψ (X i)) = ψ := by ext i; simp [ψ]
      rw [algebraicIndependent_iff_injective_aeval, h_aeval_eq]
      intro x y hxy
      have : φ (ψ x) = φ (ψ y) := by rw [hxy]
      simp only [← AlgHom.comp_apply, h_φψ_id, AlgHom.id_apply] at this
      exact this
    -- Step 2: N algebraically independent elements form a transcendence basis (trdeg = N)
    have h_tb : IsTranscendenceBasis K (fun i => ψ (X i)) := by
      apply AlgebraicIndependent.isTranscendenceBasis_of_lift_trdeg_le_of_finite h_ψX_indep
      rw [MvPolynomial.trdeg_of_isDomain]
      simp only [Cardinal.lift_natCast, Cardinal.lift_id', Cardinal.mk_fin, le_refl]
    -- Step 3: Get the algebra equivalence
    have h_equiv : MvPolynomial (Fin N) K ≃ₐ[K] Algebra.adjoin K (Set.range (fun i => ψ (X i))) :=
      h_ψX_indep.aevalEquiv
    have h_aeval_eq : aeval (fun i => ψ (X i)) = ψ := by ext i; simp [ψ]
    -- Step 4: ψ.range = adjoin
    have h_range_eq_adjoin : ψ.range = Algebra.adjoin K (Set.range (fun i => ψ (X i))) := by
      have h1 : Algebra.adjoin K (Set.range (fun i => ψ (X i))) = (aeval (fun i => ψ (X i))).range :=
        Algebra.adjoin_range_eq_range_aeval K (fun i => ψ (X i))
      rw [h1, h_aeval_eq]
    -- Step 5: adjoin = ⊤ (transcendence basis spans the whole algebra)
    -- This follows from the triangular structure of ψ(X_i) from Newton's identities
    have h_adjoin_eq_top : Algebra.adjoin K (Set.range (fun i => ψ (X i))) = ⊤ := by
      -- The key insight: ψ(X_i) has a triangular structure from Newton's identities.
      -- ψ(X_i) = c_i * X_i + q_i where c_i is a unit and q_i only involves X_j for j < i.
      -- This triangular structure implies that each X_i is in the adjoin, hence adjoin = ⊤.
      
      -- First, show φ is surjective
      have h_φ_surj : Function.Surjective φ := by
        intro y
        use ψ y
        have := congrFun (congrArg DFunLike.coe h_φψ_id) y
        simp only [AlgHom.comp_apply, AlgHom.id_apply] at this
        exact this
      
      -- Helper lemma: if q.vars ⊆ {j | j < i}, and X_j ∈ A for all j < i, then q ∈ A
      have h_mem_adjoin_of_vars_bounded : ∀ (q : MvPolynomial (Fin N) K) (i : Fin N)
          (A : Subalgebra K (MvPolynomial (Fin N) K)),
          (∀ j ∈ q.vars, j < i) → (∀ j : Fin N, j < i → X j ∈ A) → q ∈ A := by
        intro q i A hq_vars hX_mem
        rw [as_sum q]
        apply Subalgebra.sum_mem
        intro m hm
        have h_monomial : monomial m (q.coeff m) = C (q.coeff m) * m.prod (fun j n => X j ^ n) := by
          rw [monomial_eq]
        rw [h_monomial]
        apply Subalgebra.mul_mem
        · exact Subalgebra.algebraMap_mem A _
        · rw [Finsupp.prod]
          apply Subalgebra.prod_mem
          intro j hj
          apply Subalgebra.pow_mem
          apply hX_mem
          apply hq_vars
          rw [mem_vars_iff_mem_support]
          exact ⟨m, hm, hj⟩
      
      let A := Algebra.adjoin K (Set.range (fun i => ψ (X i)))
      
      -- Show all X_i are in A by strong induction using the triangular structure
      suffices h_all_X_in_A : ∀ i : Fin N, X i ∈ A by
        rw [eq_top_iff, ← adjoin_range_X]
        apply Algebra.adjoin_le
        intro y hy
        obtain ⟨i, rfl⟩ := hy
        exact h_all_X_in_A i
      
      -- Strong induction on i.val
      suffices h_ind : ∀ n : ℕ, ∀ i : Fin N, i.val = n → X i ∈ A by
        intro i; exact h_ind i.val i rfl
      
      intro n
      induction n using Nat.strong_induction_on with
          | _ n ih =>
            intro i hi
            -- ψ(X_i) ∈ A
            have hψX_mem : ψ (X i) ∈ A := Algebra.subset_adjoin ⟨i, rfl⟩
            -- The coefficient c_i = (-1)^i / (i+1) is a unit since K is a ℚ-algebra:
            have h_c_unit : IsUnit (algebraMap ℚ K ((-1 : ℚ) ^ i.val / (i.val + 1))) := by
              have h_ne : ((-1 : ℚ) ^ i.val / (i.val + 1)) ≠ 0 := by
                apply div_ne_zero
                · exact pow_ne_zero i.val (by norm_num)
                · positivity
              exact (isUnit_iff_ne_zero.mpr h_ne).map (algebraMap ℚ K)
            -- By IH, X j ∈ A for all j < i
            have hX_mem_lower : ∀ j : Fin N, j < i → X j ∈ A := by
              intro j hj
              apply ih j.val
              · omega
              · rfl
            -- Define c_i
            let c_i : K := algebraMap ℚ K ((-1 : ℚ) ^ i.val / (i.val + 1))
            -- For this proof, we use the explicit triangular structure from hQ_spec
            have h_triangular : ∃ q : MvPolynomial (Fin N) K,
                (∀ j ∈ q.vars, j < i) ∧ ψ (X i) = C c_i * X i + q := by
              -- ψ(X i) = Q_i i by definition of ψ
              have h_ψXi_eq : ψ (X i) = Q_i i := by simp only [ψ, aeval_X]
              -- Get the triangular structure from hQ_spec
              obtain ⟨q_lower, hq_vars, hQ_eq⟩ := (hQ_spec i).2
              use q_lower
              constructor
              · -- Show q_lower.vars ⊆ {j | j < i}
                intro j hj
                have hj_bound := hq_vars j hj
                exact Fin.lt_def.mpr hj_bound
              · -- Show ψ(X i) = C c_i * X i + q_lower
                rw [h_ψXi_eq, hQ_eq]
            obtain ⟨q, hq_vars, hψX_eq⟩ := h_triangular
            -- q ∈ A by h_mem_adjoin_of_vars_bounded
            have hq_mem : q ∈ A := h_mem_adjoin_of_vars_bounded q i A hq_vars hX_mem_lower
            -- C c_i * X i = ψ(X i) - q ∈ A
            have hcX_mem : C c_i * X i ∈ A := by
              have h : C c_i * X i = ψ (X i) - q := by rw [hψX_eq]; ring
              rw [h]
              exact A.sub_mem hψX_mem hq_mem
            -- Since c_i is a unit, X i ∈ A
            obtain ⟨u, hu⟩ := h_c_unit
            have h_X_eq : X i = C (↑u⁻¹ : K) * (C c_i * X i) := by
              rw [← mul_assoc, ← C_mul]
              have hu' : c_i = u := hu.symm
              rw [hu']
              simp only [Units.inv_mul, C_1, one_mul]
            rw [h_X_eq]
            exact A.mul_mem (A.algebraMap_mem _) hcX_mem
    -- Step 6: Conclude bijectivity
    have h_ψ_surj : Function.Surjective ψ := by
      rw [← AlgHom.range_eq_top, h_range_eq_adjoin, h_adjoin_eq_top]
    constructor
    · -- φ is injective: since ψ is surjective, for any x, y with φ x = φ y,
      -- we have x = ψ a, y = ψ b for some a, b
      -- Then φ (ψ a) = φ (ψ b), so a = b (since φ ∘ ψ = id)
      -- Therefore x = ψ a = ψ b = y
      intro x y hxy
      obtain ⟨a, ha⟩ := h_ψ_surj x
      obtain ⟨b, hb⟩ := h_ψ_surj y
      have : φ (ψ a) = φ (ψ b) := by rw [ha, hb, hxy]
      simp only [← AlgHom.comp_apply, h_φψ_id, AlgHom.id_apply] at this
      rw [← ha, ← hb, this]
    · -- φ is surjective (from φ ∘ ψ = id)
      intro y
      use ψ y
      have := congrFun (congrArg DFunLike.coe h_φψ_id) y
      simp only [AlgHom.comp_apply, AlgHom.id_apply] at this
      exact this
  -- Step 5: Conclude that aeval psum is injective
  intro p q hpq
  have h : psumToS p = psumToS q := Subtype.ext hpq
  have h' : φ p = φ q := by
    simp only [φ, AlgHom.comp_apply, AlgHom.coe_ofClass]
    rw [h]
  exact h_φ_bij.injective h'

/-- The aeval map sending X_i to p_{i+1}.
    Label: thm.sf.ftsf -/
private noncomputable def psumAeval : MvPolynomial (Fin N) K →ₐ[K] P K N :=
  aeval (fun i : Fin N => psum (Fin N) K (i + 1))

/-- The range of psumAeval is a subalgebra.
    Label: thm.sf.ftsf -/
private noncomputable def psumRange : Subalgebra K (P K N) := psumAeval.range

omit [Algebra ℚ K] [IsDomain K] in
/-- psum k is in the range for 0 < k ≤ N.
    Label: thm.sf.ftsf -/
private lemma psum_mem_psumRange (k : ℕ) (hk : 0 < k) (hk' : k ≤ N) :
    psum (Fin N) K k ∈ psumRange := by
  have h : k - 1 < N := by omega
  refine ⟨X ⟨k - 1, h⟩, ?_⟩
  unfold psumAeval
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  congr 1
  omega

omit [IsDomain K] in
/-- Key lemma: esymm k is in the range of psumAeval.
    This follows from Newton's identities which allow expressing e_k in terms of
    e_0, ..., e_{k-1} and p_1, ..., p_k. Over a ℚ-algebra, we can divide by k to solve for e_k.
    Label: thm.sf.ftsf -/
private lemma esymm_mem_psumRange (k : ℕ) (hk : k ≤ N) : esymm (Fin N) K k ∈ psumRange := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      simp only [esymm_zero]
      exact Subalgebra.one_mem _
    | succ k =>
      -- Newton's identity: (k+1) * e_{k+1} = (-1)^{k+2} * sum_{i<k+1} (-1)^i * e_i * p_{k+1-i}
      have newton := mul_esymm_eq_sum (Fin N) K (k + 1)
      -- The RHS is in psumRange
      have h_rhs_mem : (-1 : P K N) ^ (k + 1 + 1) *
          ∑ a ∈ antidiagonal (k + 1) with a.1 < k + 1,
            (-1) ^ a.1 * esymm (Fin N) K a.1 * psum (Fin N) K a.2 ∈ psumRange := by
        apply Subalgebra.mul_mem
        · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _
        · apply Subalgebra.sum_mem
          intro a ha
          rw [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
          apply Subalgebra.mul_mem
          · apply Subalgebra.mul_mem
            · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _
            · exact ih a.1 ha.2 (by have := ha.1; omega)
          · exact psum_mem_psumRange a.2 (by have := ha.1; omega) (by have := ha.1; omega)
      -- (k+1) is invertible in K (since K is a ℚ-algebra)
      have h_inv : IsUnit ((k + 1 : ℕ) : K) := by
        have h : ((k + 1 : ℕ) : ℚ) ≠ 0 := by
          simp only [ne_eq, Nat.cast_eq_zero]
          exact Nat.succ_ne_zero k
        have hunit : IsUnit ((k + 1 : ℕ) : ℚ) := isUnit_iff_ne_zero.mpr h
        have := hunit.map (algebraMap ℚ K)
        simp only [map_natCast] at this
        exact this
      -- Since (k+1) * e_{k+1} = RHS and RHS ∈ psumRange and (k+1) is a unit,
      -- we have e_{k+1} = (k+1)⁻¹ * RHS ∈ psumRange
      obtain ⟨u, hu⟩ := h_inv
      have h_esymm_eq : esymm (Fin N) K (k + 1) =
          (↑u⁻¹ : K) • ((-1 : P K N) ^ (k + 1 + 1) *
            ∑ a ∈ antidiagonal (k + 1) with a.1 < k + 1,
              (-1) ^ a.1 * esymm (Fin N) K a.1 * psum (Fin N) K a.2) := by
        have h1 : (u : K) • esymm (Fin N) K (k + 1) = (k + 1 : ℕ) • esymm (Fin N) K (k + 1) := by
          simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, MvPolynomial.C_eq_coe_nat, hu]
          rfl
        have h2 : (↑u⁻¹ : K) • ((u : K) • esymm (Fin N) K (k + 1)) = esymm (Fin N) K (k + 1) := by
          rw [← smul_assoc, smul_eq_mul, Units.inv_mul, one_smul]
        rw [← h2, h1, ← newton]
        simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
        rfl
      rw [h_esymm_eq]
      exact Subalgebra.smul_mem _ h_rhs_mem _

omit [IsDomain K] in
/-- aeval of esymm's is in psumRange.
    Label: thm.sf.ftsf -/
private lemma aeval_esymm_mem_psumRange (g : MvPolynomial (Fin N) K) :
    aeval (fun i : Fin N => esymm (Fin N) K (i + 1)) g ∈ psumRange := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C]
    exact Subalgebra.algebraMap_mem psumRange c
  | add p q hp hq =>
    simp only [map_add]
    exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
    simp only [map_mul, aeval_X]
    apply Subalgebra.mul_mem _ hp
    have hi : (i : ℕ) + 1 ≤ N := Nat.add_one_le_iff.mpr i.isLt
    exact esymm_mem_psumRange (i + 1) hi

/-- Over a ℚ-algebra, every symmetric polynomial can be uniquely written as a polynomial
    in p_1, ..., p_N.
    (Theorem thm.sf.ftsf (c), generation part).
    Label: thm.sf.ftsf -/
theorem psum_generates_symmetric (f : S K N) :
    ∃! g : MvPolynomial (Fin N) K,
      aeval (fun i : Fin N => (psum (Fin N) K (i + 1) : P K N)) g = (f : P K N) := by
  -- Injectivity follows from algebraic independence
  have h_inj : Function.Injective (psumAeval (K := K) (N := N)) := by
    have := psum_algebraicIndependent (K := K) (N := N)
    rw [algebraicIndependent_iff_injective_aeval] at this
    exact this
  -- Existence: f is in the range of psumAeval
  have h_card : Fintype.card (Fin N) = N := Fintype.card_fin N
  obtain ⟨g_esymm, hg_esymm⟩ := esymmAlgHom_surjective K h_card.le f
  -- The range of psumAeval contains all symmetric polynomials
  have h_f_in_range : (f : P K N) ∈ (psumRange (K := K) (N := N)) := by
    rw [← hg_esymm, esymmAlgHom_apply]
    exact aeval_esymm_mem_psumRange g_esymm
  -- Now we can conclude
  obtain ⟨g, hg⟩ := h_f_in_range
  refine ⟨g, hg, ?_⟩
  intro y hy
  exact h_inj (hy.trans hg.symm)

end PartC

/-!
## Lemma lem.sf.simples-enough: Simple transpositions suffice

A polynomial f ∈ P is symmetric if and only if s_k · f = f for each k ∈ [N-1],
where s_k is the simple transposition swapping k and k+1.
-/

/-- Simple transposition s_k swaps positions k and k+1.
    
    This is an alias for the canonical definition `AlgebraicCombinatorics.simpleTransposition`
    from `Permutations/Basics.lean`. The canonical definition uses `Fin (N - 1)` to encode
    the constraint that k + 1 < N.
    
    Label: lem.sf.simples-enough -/
abbrev simpleTransposition (k : Fin (N - 1)) : Equiv.Perm (Fin N) :=
  AlgebraicCombinatorics.simpleTransposition k

/-- Helper: invariance under simple transpositions implies rename equals f -/
private lemma rename_simpleTransposition_eq (f : P K N) (k : Fin (N - 1))
    (h : ∀ k : Fin (N - 1), simpleTransposition k •ₚ f = f) :
    rename (simpleTransposition k) f = f := by
  have := h k
  simp only [permAction] at this
  exact this

/-- Auxiliary lemma: induction on distance between indices -/
private lemma rename_swap_eq_aux (f : P K N) (i j : Fin N)
    (h : ∀ k : Fin (N - 1), simpleTransposition k •ₚ f = f)
    (hlt : i < j) (d : ℕ) (hd : j.val - i.val = d + 1) :
    rename (Equiv.swap i j) f = f := by
  induction d generalizing i j with
  | zero =>
    have hj : j.val = i.val + 1 := by omega
    have hi_lt : i.val < N - 1 := by have := j.isLt; omega
    have hk : i.val + 1 < N := by omega
    have heq : Equiv.swap i j = simpleTransposition ⟨i.val, hi_lt⟩ := by
      have hj' : j = ⟨i.val + 1, hk⟩ := by ext; exact hj
      rw [hj', ← AlgebraicCombinatorics.simpleTransposition_eq_swap_explicit i hk]
    rw [heq]
    exact rename_simpleTransposition_eq f ⟨i.val, hi_lt⟩ h
  | succ d ih =>
    have hi1_lt : i.val + 1 < N := by have := j.isLt; omega
    have hi_lt : i.val < N - 1 := by have := j.isLt; omega
    have hne1 : i ≠ ⟨i.val + 1, hi1_lt⟩ := by simp only [ne_eq, Fin.ext_iff]; omega
    have hne2 : i ≠ j := by intro heq; simp only [heq, lt_self_iff_false] at hlt
    have hne3 : (⟨i.val + 1, hi1_lt⟩ : Fin N) ≠ j := by simp only [ne_eq, Fin.ext_iff]; omega
    have hconj : Equiv.swap i j = Equiv.swap i ⟨i.val + 1, hi1_lt⟩ *
        Equiv.swap ⟨i.val + 1, hi1_lt⟩ j * Equiv.swap i ⟨i.val + 1, hi1_lt⟩ := by
      have h1 := Equiv.swap_mul_swap_mul_swap (x := j) (y := ⟨i.val + 1, hi1_lt⟩)
        (z := i) hne3.symm hne2.symm
      simp only [Equiv.swap_comm ⟨i.val + 1, hi1_lt⟩ i, Equiv.swap_comm j ⟨i.val + 1, hi1_lt⟩] at h1
      exact h1.symm
    rw [hconj]
    simp only [Equiv.Perm.coe_mul, ← rename_rename]
    have h1 : rename (Equiv.swap i ⟨i.val + 1, hi1_lt⟩) f = f := by
      have hsi : Equiv.swap i ⟨i.val + 1, hi1_lt⟩ = simpleTransposition ⟨i.val, hi_lt⟩ := by
        rw [← AlgebraicCombinatorics.simpleTransposition_eq_swap_explicit i hi1_lt]
      rw [hsi]
      exact rename_simpleTransposition_eq f ⟨i.val, hi_lt⟩ h
    have hi1_lt_j : (⟨i.val + 1, hi1_lt⟩ : Fin N) < j := by simp only [Fin.lt_def]; omega
    have hdist' : j.val - (⟨i.val + 1, hi1_lt⟩ : Fin N).val = d + 1 := by simp; omega
    have h2 : rename (Equiv.swap ⟨i.val + 1, hi1_lt⟩ j) f = f := ih ⟨i.val + 1, hi1_lt⟩ j hi1_lt_j hdist'
    rw [h1, h2, h1]

/-- Invariance under simple transpositions implies invariance under any swap -/
private lemma rename_swap_eq_of_invariant_simpleTranspositions (f : P K N) (i j : Fin N)
    (h : ∀ k : Fin (N - 1), simpleTransposition k •ₚ f = f) :
    rename (Equiv.swap i j) f = f := by
  by_cases hij : i = j
  · simp [hij, rename_id]
  wlog hlt : i < j generalizing i j with Hsymm
  · rw [Equiv.swap_comm]
    exact Hsymm j i (Ne.symm hij) (not_lt.mp hlt |>.lt_of_ne (Ne.symm hij))
  have hdist : j.val - i.val ≥ 1 := by omega
  exact rename_swap_eq_aux f i j h hlt (j.val - i.val - 1) (by omega)

/-- A polynomial is symmetric iff it is invariant under all simple transpositions.
    (Lemma lem.sf.simples-enough).
    Label: lem.sf.simples-enough -/
theorem isSymm_iff_simpleTranspositions (f : P K N) :
    IsSymm f ↔ ∀ k : Fin (N - 1), simpleTransposition k •ₚ f = f := by
  constructor
  · -- Forward direction: symmetric implies invariant under simple transpositions
    intro hf k
    simp only [permAction, IsSymm, MvPolynomial.IsSymmetric] at hf ⊢
    exact hf (simpleTransposition k)
  · -- Backward direction: invariant under simple transpositions implies symmetric
    intro h σ
    -- Use induction on permutations via swap_induction_on
    induction σ using Equiv.Perm.swap_induction_on with
    | one => simp [rename_id]
    | swap_mul σ' i j hij ih =>
      simp only [Equiv.Perm.coe_mul, ← rename_rename]
      rw [ih, rename_swap_eq_of_invariant_simpleTranspositions f i j h]

/-!
## Example: Antisymmetric Polynomials

A polynomial f is antisymmetric if σ · f = (-1)^σ · f for all σ ∈ S_N.
The square of an antisymmetric polynomial is symmetric.
-/

/-- A polynomial is antisymmetric if σ · f = sign(σ) · f for all permutations σ.
    Label: exa.sf.PS1 -/
def IsAntisymm (f : P K N) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), rename σ f = Equiv.Perm.sign σ • f

/-!
### Basic API lemmas for `IsAntisymm`

The following lemmas establish that antisymmetric polynomials form a K-submodule of P
(but not a subalgebra, since the product of two antisymmetric polynomials is symmetric, not antisymmetric).
-/

/-- The zero polynomial is antisymmetric.
    Label: exa.sf.PS1 -/
theorem isAntisymm_zero : IsAntisymm (0 : P K N) := by
  intro σ
  simp only [map_zero, smul_zero]

/-- If f is antisymmetric, then -f is antisymmetric.
    Label: exa.sf.PS1 -/
theorem isAntisymm_neg {f : P K N} (hf : IsAntisymm f) : IsAntisymm (-f) := by
  intro σ
  simp only [map_neg, hf σ, smul_neg]

/-- If f is antisymmetric, then c • f is antisymmetric for any scalar c.
    Label: exa.sf.PS1 -/
theorem isAntisymm_smul (c : K) {f : P K N} (hf : IsAntisymm f) : IsAntisymm (c • f) := by
  intro σ
  simp only [map_smul, hf σ, smul_comm c]

/-- If f and g are antisymmetric, then f + g is antisymmetric.
    Label: exa.sf.PS1 -/
theorem isAntisymm_add {f g : P K N} (hf : IsAntisymm f) (hg : IsAntisymm g) :
    IsAntisymm (f + g) := by
  intro σ
  simp only [map_add, hf σ, hg σ, smul_add]

/-- If f and g are antisymmetric, then f - g is antisymmetric.
    Label: exa.sf.PS1 -/
theorem isAntisymm_sub {f g : P K N} (hf : IsAntisymm f) (hg : IsAntisymm g) :
    IsAntisymm (f - g) := by
  intro σ
  simp only [map_sub, hf σ, hg σ, smul_sub]

/-- The square of an antisymmetric polynomial is symmetric.
    (Example exa.sf.PS1 (d)).
    Label: exa.sf.PS1 -/
theorem isSymm_sq_of_isAntisymm {f : P K N} (hf : IsAntisymm f) : IsSymm (f ^ 2) := by
  intro σ
  simp only [pow_two, map_mul, hf σ, smul_mul_smul]
  simp only [Int.units_mul_self, one_smul]

end SymmetricPolynomials

end AlgebraicCombinatorics
