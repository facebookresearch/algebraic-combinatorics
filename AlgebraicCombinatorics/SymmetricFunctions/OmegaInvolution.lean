/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import AlgebraicCombinatorics.SymmetricFunctions.Definitions

/-!
# The ω-involution on symmetric functions

The ω-involution is an algebra automorphism of the ring of symmetric functions
that swaps the elementary and complete homogeneous symmetric polynomials:
- ω(e_n) = h_n
- ω(h_n) = e_n
- ω(s_λ) = s_{λᵗ}

This file defines the ω-involution and proves its key properties.

## Main definitions

* `SymmetricFunctions.hsymmAlgHom`: The algebra homomorphism from `MvPolynomial (Fin n) R`
  to the symmetric subalgebra sending `X_i` to `h_{i+1}`.
* `SymmetricFunctions.omegaInvolution`: The ω-involution on symmetric polynomials.

## Main results

* `SymmetricFunctions.omegaInvolution_esymm_succ`: ω(e_{k+1}) = h_{k+1} for k < n
* `SymmetricFunctions.omegaInvolution_hsymm_succ`: ω(h_{k+1}) = e_{k+1} for k < n
* `SymmetricFunctions.omegaInvolution_involutive`: ω ∘ ω = id

## Implementation notes

The ω-involution is defined using the fundamental theorem of symmetric polynomials.
The elementary symmetric polynomials generate the symmetric subalgebra, so we can
define ω by specifying ω(e_k) = h_k and extending algebraically.

To prove that ω is an involution, we need to show that ω(h_k) = e_k. This requires
proving that the h_k also generate the symmetric subalgebra (which they do, by the
Newton-Girard relations and the fundamental theorem).

## References

* [Stanley, *Enumerative Combinatorics, Vol. 2*][Stanley-EC2], Section 7.8
* [Grinberg-Reiner, *Hopf algebras in combinatorics*][GriRei], Section 2.4

## Why this is needed

The ω-involution is essential for proving the second Jacobi-Trudi formula
(jacobiTrudi_e in PieriJacobiTrudi.lean). The standard proof proceeds as follows:

1. First Jacobi-Trudi: s_{λ/μ} = det(h_{λᵢ - μⱼ - i + j})
2. Apply ω: ω(s_{λ/μ}) = det(ω(h_{...})) = det(e_{...})
3. Since ω(s_{λ/μ}) = s_{λᵗ/μᵗ}: s_{λᵗ/μᵗ} = det(e_{λᵢ - μⱼ - i + j})
4. Substitute λ → λᵗ: s_{λ/μ} = det(e_{(λᵗ)ᵢ - (μᵗ)ⱼ - i + j})

This file provides the infrastructure for steps 2 and 3.
-/

open MvPolynomial Finset BigOperators AlgebraicCombinatorics.SymmetricPolynomials

namespace SymmetricFunctions

/-!
## Transfer lemmas for esymm and hsymm via rename

These lemmas allow us to transfer results about symmetric polynomials from one
finite type to another via the `rename` operation.
-/

/-- Transfer lemma: esymm is preserved under rename by an equivalence. -/
lemma rename_esymm_eq {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
    (e : σ ≃ τ) (R : Type*) [CommRing R] (k : ℕ) :
    rename e (esymm σ R k) = esymm τ R k := by
  simp only [esymm, map_sum, map_prod, rename_X]
  refine Finset.sum_bij' 
    (fun s _ => s.map e.toEmbedding) 
    (fun t _ => t.map e.symm.toEmbedding) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [mem_powersetCard] at hs ⊢
    exact ⟨subset_univ _, by rw [Finset.card_map]; exact hs.2⟩
  · intro t ht
    simp only [mem_powersetCard] at ht ⊢
    exact ⟨subset_univ _, by rw [Finset.card_map]; exact ht.2⟩
  · intro s _
    ext x
    simp only [mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨a, ⟨b, hb, hab⟩, hax⟩
      rw [← hax, ← hab, Equiv.symm_apply_apply]; exact hb
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, Equiv.symm_apply_apply e x⟩
  · intro t _
    ext x
    simp only [mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨a, ⟨b, hb, hab⟩, hax⟩
      rw [← hax, ← hab, Equiv.apply_symm_apply]; exact hb
    · intro hx
      exact ⟨e.symm x, ⟨x, hx, rfl⟩, Equiv.apply_symm_apply e x⟩
  · intro s _
    rw [Finset.prod_map]
    simp only [Equiv.toEmbedding_apply]

/-- Transfer lemma: hsymm is preserved under rename by an equivalence. -/
lemma rename_hsymm_eq {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]
    (e : σ ≃ τ) (R : Type*) [CommRing R] (k : ℕ) :
    rename e (hsymm σ R k) = hsymm τ R k := by
  simp only [hsymm, map_sum]
  refine Finset.sum_bij' 
    (fun s _ => Sym.map e s) 
    (fun t _ => Sym.map e.symm t) ?_ ?_ ?_ ?_ ?_
  · intro s _; exact mem_univ _
  · intro t _; exact mem_univ _
  · intro s _
    simp only [Sym.map_map, Equiv.symm_comp_self]
    exact Sym.map_id s
  · intro t _
    simp only [Sym.map_map, Equiv.self_comp_symm]
    exact Sym.map_id t
  · intro s _
    rw [map_multiset_prod]
    congr 1
    simp only [Multiset.map_map, Function.comp_apply, rename_X]
    show Multiset.map (fun x => X (e x)) ↑s = Multiset.map X ↑(Sym.map (⇑e) s)
    simp only [Sym.coe_map, Multiset.map_map, Function.comp_apply]

/-- Newton-Girard identity for arbitrary finite type σ.
    Transferred from `newtonGirard_eh` via rename. -/
theorem newtonGirard_eh_general {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] (n : ℕ) (hn : 0 < n) :
    ∑ j ∈ range (n + 1), (-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (n - j) = 0 := by
  -- Transfer from Fin (Fintype.card σ)
  let N := Fintype.card σ
  let f := (Fintype.equivFin σ).symm
  -- Apply rename f to newtonGirard_eh
  have h := newtonGirard_eh (K := R) (N := N) n hn
  -- h : ∑ j ∈ range (n + 1), (-1)^j * e j * h (n - j) = 0 in MvPolynomial (Fin N) R
  have h' : rename f (∑ j ∈ range (n + 1), (-1 : MvPolynomial (Fin N) R) ^ j * 
              esymm (Fin N) R j * hsymm (Fin N) R (n - j)) = 0 := by
    rw [h, map_zero]
  rw [map_sum] at h'
  simp only [map_mul, map_pow, map_neg, map_one] at h'
  convert h' using 2
  · ext j
    rw [rename_esymm_eq, rename_hsymm_eq]

/-- Helper lemma: sum of subalgebra elements coerces to sum of their values. -/
lemma symmetricSubalgebra_sum_val_nat {σ : Type*} {R : Type*} [CommRing R]
    (s : Finset ℕ) (f : ℕ → symmetricSubalgebra σ R) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val := by
  induction s using Finset.induction_on
  · simp
  · rename_i a s ha ih
    simp only [Finset.sum_insert ha, AddMemClass.coe_add, ih]

/-!
## The hsymm algebra homomorphism

Similar to `esymmAlgHom`, we define an algebra homomorphism that sends
`X_i` to the (i+1)-th complete homogeneous symmetric polynomial.
-/

/-- The `R`-algebra homomorphism from $R[x_1,\dots,x_n]$ to the symmetric subalgebra of
  $R[\{x_i \mid i ∈ σ\}]$ sending $x_i$ to the $(i+1)$-th complete homogeneous symmetric polynomial.
  
  This is analogous to `MvPolynomial.esymmAlgHom` which sends $x_i$ to $e_{i+1}$. -/
noncomputable def hsymmAlgHom (σ : Type*) [Fintype σ] [DecidableEq σ] 
    (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n) R →ₐ[R] symmetricSubalgebra σ R :=
  aeval (fun i ↦ ⟨hsymm σ R (i + 1), hsymm_isSymmetric σ R _⟩)

@[simp]
lemma hsymmAlgHom_X {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (i : Fin n) :
    (hsymmAlgHom σ R n (X i)).val = hsymm σ R (i + 1) := by
  simp [hsymmAlgHom]

lemma hsymmAlgHom_apply {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (p : MvPolynomial (Fin n) R) :
    (hsymmAlgHom σ R n p).val = aeval (fun i : Fin n ↦ hsymm σ R (i + 1)) p :=
  (Subalgebra.mvPolynomial_aeval_coe _ _ _).symm

/-!
## The ω-involution

The ω-involution is defined as the composition:
  ω = hsymmAlgHom ∘ esymmAlgEquiv.symm

This maps each e_k to h_k.
-/

/-- The ω-involution on symmetric polynomials.

This is an algebra endomorphism of the symmetric subalgebra that swaps
elementary and complete homogeneous symmetric polynomials:
- ω(e_n) = h_n
- ω(h_n) = e_n

The definition uses the fundamental theorem of symmetric polynomials:
since the e_k generate the symmetric subalgebra, we define ω by
specifying ω(e_k) = h_k and extending algebraically.

Note: For this definition to work, we need `Fintype.card σ = n`. -/
noncomputable def omegaInvolution {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n) :
    symmetricSubalgebra σ R →ₐ[R] symmetricSubalgebra σ R :=
  (hsymmAlgHom σ R n).comp (esymmAlgEquiv σ R hn).symm.toAlgHom

/-- The ω-involution maps e_k to h_k for 0 < k ≤ n. -/
theorem omegaInvolution_esymm_succ {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n) (k : ℕ) (hk : k < n) :
    (omegaInvolution hn ⟨esymm σ R (k + 1), esymm_isSymmetric σ R (k + 1)⟩ : 
      symmetricSubalgebra σ R).val = hsymm σ R (k + 1) := by
  simp only [omegaInvolution, AlgHom.comp_apply, AlgHom.coe_ofClass]
  have h : (esymmAlgEquiv σ R hn).symm ⟨esymm σ R (k + 1), esymm_isSymmetric σ R (k + 1)⟩ = X ⟨k, hk⟩ := 
    @esymmAlgEquiv_symm_apply σ R n _ _ hn ⟨k, hk⟩
  erw [h]
  simp [hsymmAlgHom]

/-- The ω-involution maps 1 to 1. -/
theorem omegaInvolution_one {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n) :
    omegaInvolution (R := R) hn 1 = 1 := by
  simp [omegaInvolution]

/-- The ω-involution preserves addition. -/
theorem omegaInvolution_add {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n)
    (p q : symmetricSubalgebra σ R) :
    omegaInvolution hn (p + q) = omegaInvolution hn p + omegaInvolution hn q :=
  map_add _ _ _

/-- The ω-involution preserves multiplication. -/
theorem omegaInvolution_mul {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n)
    (p q : symmetricSubalgebra σ R) :
    omegaInvolution hn (p * q) = omegaInvolution hn p * omegaInvolution hn q :=
  map_mul _ _ _

/-- The ω-involution commutes with scalar multiplication. -/
theorem omegaInvolution_smul {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n)
    (r : R) (p : symmetricSubalgebra σ R) :
    omegaInvolution hn (r • p) = r • omegaInvolution hn p :=
  map_smul _ _ _

/-!
## The ω-involution maps h_k to e_k

To show that ω(h_k) = e_k, we need to establish that the h_k generate the symmetric
subalgebra. This is proved in the Definitions.lean file as `hsymm_algebraicIndependent`.

Given this, we can define the "dual" ω-involution that maps h_k to e_k, and show
that it equals the original ω-involution composed with itself.
-/

/-- The symmetric Newton-Girard identity: ∑_{j=0}^n (-1)^j h_j e_{n-j} = 0 for n > 0.

This is the "symmetric" version of `newtonGirard_eh` (which gives ∑ (-1)^j e_j h_{n-j} = 0).
The proof follows from `newtonGirard_eh` by reindexing (j ↦ n-j) and using:
- Commutativity: h_j * e_{n-j} = e_{n-j} * h_j
- Sign identity: (-1)^{n-j} * (-1)^n = (-1)^j (since (n-j+n) mod 2 = j mod 2)

This identity is the key ingredient for proving `omegaInvolution_hsymm_succ`. -/
theorem newtonGirard_he {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] (n : ℕ) (hn : 0 < n) :
    ∑ j ∈ Finset.range (n + 1), (-1 : MvPolynomial σ R) ^ j * 
      hsymm σ R j * esymm σ R (n - j) = 0 := by
  -- Step 1: Reindex the sum using j ↦ n - j
  -- This transforms ∑_j (-1)^j h_j e_{n-j} to ∑_j (-1)^{n-j} h_{n-j} e_j
  have h_eq : ∑ j ∈ Finset.range (n + 1), (-1 : MvPolynomial σ R) ^ j * hsymm σ R j * esymm σ R (n - j) =
              ∑ j ∈ Finset.range (n + 1), (-1 : MvPolynomial σ R) ^ (n - j) * hsymm σ R (n - j) * esymm σ R j := by
    refine Finset.sum_bij' (fun j _ => n - j) (fun j _ => n - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
    · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      have h1 : j ≤ n := by omega
      exact Nat.sub_sub_self h1
    · intro j hj
      simp only [Finset.mem_range] at hj
      have h1 : j ≤ n := by omega
      exact Nat.sub_sub_self h1
    · intro j hj
      simp only [Finset.mem_range] at hj
      have h1 : j ≤ n := by omega
      simp only [Nat.sub_sub_self h1]
  rw [h_eq]
  
  -- Step 2: Transform (-1)^{n-j} h_{n-j} e_j to (-1)^n * ((-1)^j e_j h_{n-j})
  -- Key identity: (-1)^{n-j} * (-1)^j = (-1)^n
  have h_sign : ∀ j ∈ Finset.range (n + 1), 
      ((-1 : MvPolynomial σ R) ^ (n - j) * hsymm σ R (n - j) * esymm σ R j) = 
      ((-1 : MvPolynomial σ R) ^ n * ((-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (n - j))) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hle : j ≤ n := by omega
    have h : (n - j) + j = n := Nat.sub_add_cancel hle
    have h_neg1_sq : ((-1 : MvPolynomial σ R) ^ j) * ((-1 : MvPolynomial σ R) ^ j) = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨j, rfl⟩
    calc (-1 : MvPolynomial σ R) ^ (n - j) * hsymm σ R (n - j) * esymm σ R j 
        = (-1 : MvPolynomial σ R) ^ (n - j) * 1 * hsymm σ R (n - j) * esymm σ R j := by ring
      _ = (-1 : MvPolynomial σ R) ^ (n - j) * ((-1 : MvPolynomial σ R) ^ j * (-1 : MvPolynomial σ R) ^ j) * hsymm σ R (n - j) * esymm σ R j := by rw [h_neg1_sq]
      _ = (-1 : MvPolynomial σ R) ^ (n - j) * (-1 : MvPolynomial σ R) ^ j * (-1 : MvPolynomial σ R) ^ j * hsymm σ R (n - j) * esymm σ R j := by ring
      _ = (-1 : MvPolynomial σ R) ^ ((n - j) + j) * ((-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (n - j)) := by rw [pow_add]; ring
      _ = (-1 : MvPolynomial σ R) ^ n * ((-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (n - j)) := by rw [h]
  rw [Finset.sum_congr rfl h_sign]
  rw [← Finset.mul_sum]
  
  -- Step 3: Show the inner sum is 0 by the Newton-Girard identity
  -- ∑ j, (-1)^j * e_j * h_{n-j} = 0 follows from E(t) * H(t) = 1
  -- where E(t) = ∏_i (1 - t·x_i) and H(t) = ∏_i 1/(1 - t·x_i)
  suffices h : ∑ i ∈ Finset.range (n + 1), (-1 : MvPolynomial σ R) ^ i * esymm σ R i * hsymm σ R (n - i) = 0 by
    rw [h, mul_zero]
  -- Use the transferred Newton-Girard identity
  exact newtonGirard_eh_general n hn

/-- Recurrence for h_n from Newton-Girard: h_n = ∑_{j=1}^n (-1)^{j+1} e_j h_{n-j} for n > 0.

This follows from isolating the j=0 term in `newtonGirard_eh_general`:
∑_{j=0}^n (-1)^j e_j h_{n-j} = 0
⟹ e_0 h_n + ∑_{j=1}^n (-1)^j e_j h_{n-j} = 0  (since e_0 = 1)
⟹ h_n = -∑_{j=1}^n (-1)^j e_j h_{n-j} = ∑_{j=1}^n (-1)^{j+1} e_j h_{n-j} -/
theorem hsymm_recurrence_eh {σ : Type*} [Fintype σ] [DecidableEq σ]
    {R : Type*} [CommRing R] (n : ℕ) (hn : 0 < n) :
    hsymm σ R n = ∑ j ∈ Finset.Ico 1 (n + 1), (-1 : MvPolynomial σ R) ^ (j + 1) * 
      esymm σ R j * hsymm σ R (n - j) := by
  -- From Newton-Girard: ∑_{j=0}^n (-1)^j e_j h_{n-j} = 0
  have ng := newtonGirard_eh_general (σ := σ) (R := R) n hn
  -- Split off the j=0 term: h_n + ∑_{j>0} ... = 0
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_range.mpr (Nat.succ_pos n))] at ng
  simp only [pow_zero, one_mul, esymm_zero, Nat.sub_zero] at ng
  -- ng: ∑_{j>0} (-1)^j e_j h_{n-j} + h_n = 0, so ∑_{j>0} ... = -h_n
  -- Rearrange: h_n = -∑_{j>0} (-1)^j e_j h_{n-j}
  have h1 : hsymm σ R n = -∑ j ∈ Finset.range (n + 1) \ {0}, 
      (-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (n - j) := by
    have h := add_eq_zero_iff_eq_neg.mp ng
    rw [h, neg_neg]
  rw [h1]
  -- range(n+1) \ {0} = Ico 1 (n+1)
  have h2 : Finset.range (n + 1) \ {0} = Finset.Ico 1 (n + 1) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ico]
    omega
  rw [h2]
  -- -∑ (-1)^j = ∑ (-1)^{j+1}
  rw [neg_eq_iff_eq_neg, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Recurrence for e_n from symmetric Newton-Girard: e_n = ∑_{j=1}^n (-1)^{j+1} h_j e_{n-j} for n > 0.

This follows from isolating the j=0 term in `newtonGirard_he`:
∑_{j=0}^n (-1)^j h_j e_{n-j} = 0
⟹ h_0 e_n + ∑_{j=1}^n (-1)^j h_j e_{n-j} = 0  (since h_0 = 1)
⟹ e_n = -∑_{j=1}^n (-1)^j h_j e_{n-j} = ∑_{j=1}^n (-1)^{j+1} h_j e_{n-j} -/
theorem esymm_recurrence_he {σ : Type*} [Fintype σ] [DecidableEq σ]
    {R : Type*} [CommRing R] (n : ℕ) (hn : 0 < n) :
    esymm σ R n = ∑ j ∈ Finset.Ico 1 (n + 1), (-1 : MvPolynomial σ R) ^ (j + 1) * 
      hsymm σ R j * esymm σ R (n - j) := by
  -- From symmetric Newton-Girard: ∑_{j=0}^n (-1)^j h_j e_{n-j} = 0
  have ng := newtonGirard_he (σ := σ) (R := R) n hn
  -- Split off the j=0 term
  rw [Finset.sum_eq_sum_sdiff_singleton_add (Finset.mem_range.mpr (Nat.succ_pos n))] at ng
  simp only [pow_zero, one_mul, hsymm_zero, Nat.sub_zero] at ng
  -- ng: ∑_{j>0} (-1)^j h_j e_{n-j} + e_n = 0
  -- Rearrange: e_n = -∑_{j>0} (-1)^j h_j e_{n-j}
  have h1 : esymm σ R n = -∑ j ∈ Finset.range (n + 1) \ {0}, 
      (-1 : MvPolynomial σ R) ^ j * hsymm σ R j * esymm σ R (n - j) := by
    have h := add_eq_zero_iff_eq_neg.mp ng
    rw [h, neg_neg]
  rw [h1]
  -- range(n+1) \ {0} = Ico 1 (n+1)
  have h2 : Finset.range (n + 1) \ {0} = Finset.Ico 1 (n + 1) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ico]
    omega
  rw [h2]
  -- -∑ (-1)^j = ∑ (-1)^{j+1}
  rw [neg_eq_iff_eq_neg, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The ω-involution maps h_k to e_k for 0 < k ≤ n.

    **Proof sketch**: The h_k are algebraically independent and generate the symmetric
    subalgebra. Therefore, there exists a unique algebra homomorphism ω' that maps
    h_k to e_k. We show that ω' = ω by checking that ω(h_k) = e_k using the
    Newton-Girard relations.
    
    The Newton-Girard relations give:
      k * e_k = ∑_{i=1}^{k} (-1)^{i-1} e_{k-i} * p_i
      k * h_k = ∑_{i=1}^{k} h_{k-i} * p_i
    
    These can be used to express h_k in terms of e_k and p_k, and vice versa.
    Since ω(p_k) = (-1)^{k-1} p_k (which follows from the definition), we get
    ω(h_k) = e_k. -/
theorem omegaInvolution_hsymm_succ {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n) (k : ℕ) (hk : k < n) :
    (omegaInvolution hn ⟨hsymm σ R (k + 1), hsymm_isSymmetric σ R (k + 1)⟩ : 
      symmetricSubalgebra σ R).val = esymm σ R (k + 1) := by
  -- Proof by strong induction on k
  -- Base case: h_1 = e_1, so ω(h_1) = ω(e_1) = h_1 = e_1
  -- Inductive step: Use Newton-Girard to express h_{k+1} in terms of e_j and h_{k+1-j}
  --   Then apply ω and use the IH to get the symmetric Newton-Girard identity for e_{k+1}
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    cases k with
    | zero =>
      -- Base case: h_1 = e_1
      have h1 : hsymm σ R 1 = esymm σ R 1 := by simp [hsymm_one, esymm_one]
      have heq : (⟨hsymm σ R 1, hsymm_isSymmetric σ R 1⟩ : symmetricSubalgebra σ R) = 
                 ⟨esymm σ R 1, esymm_isSymmetric σ R 1⟩ := Subtype.ext h1
      rw [heq]
      rw [omegaInvolution_esymm_succ hn 0 hk]
      simp only [zero_add]
      exact h1
    | succ k' =>
      -- Inductive step: We show ω(h_{k'+2}) = e_{k'+2}
      -- Let m = k' + 2 = k + 1
      let m := k' + 2
      have hm_pos : 0 < m := Nat.succ_pos _
      have hk_eq : k' + 1 + 1 = m := rfl
      have hm_le_n : m ≤ n := by omega
      
      -- From newtonGirard_he: ∑_{j=0}^m (-1)^j h_j e_{m-j} = 0
      have ng_he : ∑ j ∈ Finset.range (m + 1), (-1 : MvPolynomial σ R) ^ j * 
          hsymm σ R j * esymm σ R (m - j) = 0 := newtonGirard_he m hm_pos
      
      -- Isolate the j=m term: (-1)^m h_m e_0 + ∑_{j<m} ... = 0
      -- Since e_0 = 1: (-1)^m h_m = -∑_{j<m} (-1)^j h_j e_{m-j}
      have h_sum_split : ∑ j ∈ Finset.range (m + 1), (-1 : MvPolynomial σ R) ^ j * 
          hsymm σ R j * esymm σ R (m - j) = 
          ∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * hsymm σ R j * esymm σ R (m - j) +
          (-1 : MvPolynomial σ R) ^ m * hsymm σ R m * esymm σ R 0 := by
        rw [Finset.sum_range_succ]
        simp only [Nat.sub_self]
      rw [h_sum_split, esymm_zero, mul_one] at ng_he
      
      have h_hm : (-1 : MvPolynomial σ R) ^ m * hsymm σ R m = 
          -∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * hsymm σ R j * esymm σ R (m - j) := by
        calc (-1 : MvPolynomial σ R) ^ m * hsymm σ R m 
            = 0 - ∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * 
                hsymm σ R j * esymm σ R (m - j) := by rw [← ng_he]; ring
          _ = -∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * 
                hsymm σ R j * esymm σ R (m - j) := by ring
      
      -- From newtonGirard_eh_general: ∑_{j=0}^m (-1)^j e_j h_{m-j} = 0
      have ng_eh : ∑ j ∈ Finset.range (m + 1), (-1 : MvPolynomial σ R) ^ j * 
          esymm σ R j * hsymm σ R (m - j) = 0 := newtonGirard_eh_general m hm_pos
      
      -- Similarly isolate j=m: (-1)^m e_m = -∑_{j<m} (-1)^j e_j h_{m-j}
      have e_sum_split : ∑ j ∈ Finset.range (m + 1), (-1 : MvPolynomial σ R) ^ j * 
          esymm σ R j * hsymm σ R (m - j) = 
          ∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (m - j) +
          (-1 : MvPolynomial σ R) ^ m * esymm σ R m * hsymm σ R 0 := by
        rw [Finset.sum_range_succ]
        simp only [Nat.sub_self]
      rw [e_sum_split, hsymm_zero, mul_one] at ng_eh
      
      have h_em : (-1 : MvPolynomial σ R) ^ m * esymm σ R m = 
          -∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (m - j) := by
        calc (-1 : MvPolynomial σ R) ^ m * esymm σ R m 
            = 0 - ∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * 
                esymm σ R j * hsymm σ R (m - j) := by rw [← ng_eh]; ring
          _ = -∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * 
                esymm σ R j * hsymm σ R (m - j) := by ring
      
      -- Key: (-1)^m * (-1)^m = 1
      have h_neg1_sq : ((-1 : MvPolynomial σ R) ^ m) * ((-1 : MvPolynomial σ R) ^ m) = 1 := by
        rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
      
      -- From h_hm and h_em, we have:
      -- (-1)^m h_m = -∑_{j<m} (-1)^j h_j e_{m-j}
      -- (-1)^m e_m = -∑_{j<m} (-1)^j e_j h_{m-j}
      
      -- We want to show ω(h_m).val = e_m
      -- Strategy: Show (-1)^m * ω(h_m).val = (-1)^m * e_m, then cancel (-1)^m
      
      -- First, compute ω applied to the sum expression
      -- ω(∑_{j<m} (-1)^j h_j e_{m-j}) = ∑_{j<m} (-1)^j ω(h_j) ω(e_{m-j})
      --                                = ∑_{j<m} (-1)^j e_j h_{m-j}  (using IH and ω(e_k) = h_k)
      
      -- We need to show: ω(h_m).val = e_m
      -- This is equivalent to: (-1)^m * ω(h_m).val = (-1)^m * e_m
      -- 
      -- From h_hm: h_m = (-1)^m * (-∑_{j<m} (-1)^j h_j e_{m-j})
      -- So: ω(h_m).val = (-1)^m * (-∑_{j<m} (-1)^j ω(h_j).val * ω(e_{m-j}).val)
      --               = (-1)^m * (-∑_{j<m} (-1)^j e_j h_{m-j})  (by IH and ω(e_k) = h_k)
      --               = (-1)^m * (-1)^m * e_m  (by h_em, multiplied by (-1)^m)
      --               = e_m
      
      -- Step 1: Lift the Newton-Girard sum to the subalgebra
      -- Define the sum as a subalgebra element
      let ng_sum_sub : symmetricSubalgebra σ R := 
        ∑ j ∈ Finset.range m, (-1 : symmetricSubalgebra σ R) ^ j * 
          ⟨hsymm σ R j, hsymm_isSymmetric σ R j⟩ * ⟨esymm σ R (m - j), esymm_isSymmetric σ R (m - j)⟩
      
      -- Step 2: Show that the subalgebra sum coerces to the MvPolynomial sum
      have ng_sum_sub_val : ng_sum_sub.val = 
          ∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * hsymm σ R j * esymm σ R (m - j) := by
        simp only [ng_sum_sub]
        rw [symmetricSubalgebra_sum_val_nat]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, NegMemClass.coe_neg, OneMemClass.coe_one]
      
      -- Step 3: From h_hm, express h_m in terms of the sum
      -- h_hm: (-1)^m * h_m = -ng_sum_sub.val
      -- So: h_m = (-1)^m * (-ng_sum_sub.val)
      have h_hm_lift : (⟨hsymm σ R m, hsymm_isSymmetric σ R m⟩ : symmetricSubalgebra σ R) = 
          (-1 : symmetricSubalgebra σ R) ^ m * (-ng_sum_sub) := by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, NegMemClass.coe_neg, 
          OneMemClass.coe_one, ng_sum_sub_val]
        -- From h_hm: (-1)^m * h_m = -∑...
        -- So h_m = (-1)^m * (-∑...)
        have h := h_hm
        calc hsymm σ R m 
            = 1 * hsymm σ R m := by ring
          _ = ((-1 : MvPolynomial σ R) ^ m * (-1 : MvPolynomial σ R) ^ m) * hsymm σ R m := by rw [h_neg1_sq]
          _ = (-1 : MvPolynomial σ R) ^ m * ((-1 : MvPolynomial σ R) ^ m * hsymm σ R m) := by ring
          _ = (-1 : MvPolynomial σ R) ^ m * 
              (-∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * hsymm σ R j * esymm σ R (m - j)) := by rw [h]
          _ = (-1) ^ m * -∑ j ∈ Finset.range m, (-1) ^ j * hsymm σ R j * esymm σ R (m - j) := by ring
      
      -- Step 4: Apply ω to h_m
      rw [h_hm_lift]
      simp only [map_mul, map_pow, map_neg, map_one]
      
      -- Step 5: Show that ω applied to the sum gives the other sum
      have omega_sum : (omegaInvolution hn ng_sum_sub).val = 
          ∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (m - j) := by
        simp only [ng_sum_sub]
        rw [map_sum]
        rw [symmetricSubalgebra_sum_val_nat]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        simp only [Finset.mem_range] at hj
        simp only [map_mul, map_pow, map_neg, map_one, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
          NegMemClass.coe_neg, OneMemClass.coe_one]
        -- Show ω(h_j).val = e_j
        have h_omega_h : (omegaInvolution hn ⟨hsymm σ R j, hsymm_isSymmetric σ R j⟩).val = esymm σ R j := by
          cases j with
          | zero =>
            have h1 : (⟨hsymm σ R 0, hsymm_isSymmetric σ R 0⟩ : symmetricSubalgebra σ R) = 1 := by
              apply Subtype.ext; simp [hsymm_zero]
            rw [h1, map_one]
            simp [esymm_zero]
          | succ j' =>
            have hj'_lt : j' < m - 1 := by omega
            have hj'_lt_n : j' < n := by omega
            exact ih j' (by omega) hj'_lt_n
        -- Show ω(e_{m-j}).val = h_{m-j}
        have h_omega_e : (omegaInvolution hn ⟨esymm σ R (m - j), esymm_isSymmetric σ R (m - j)⟩).val = 
            hsymm σ R (m - j) := by
          cases hm_j : m - j with
          | zero => omega
          | succ k =>
            have hk_lt_n : k < n := by omega
            exact omegaInvolution_esymm_succ hn k hk_lt_n
        rw [h_omega_h, h_omega_e]
      
      -- Step 6: Combine everything
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, NegMemClass.coe_neg, 
        OneMemClass.coe_one, omega_sum]
      -- Goal: (-1)^m * -∑... = e_m
      -- From h_em: (-1)^m * e_m = -∑...
      -- So: (-1)^m * -∑... = (-1)^m * ((-1)^m * e_m) = e_m
      calc (-1 : MvPolynomial σ R) ^ m * 
            -∑ j ∈ Finset.range m, (-1 : MvPolynomial σ R) ^ j * esymm σ R j * hsymm σ R (m - j)
          = (-1 : MvPolynomial σ R) ^ m * ((-1 : MvPolynomial σ R) ^ m * esymm σ R m) := by rw [h_em]
        _ = ((-1 : MvPolynomial σ R) ^ m * (-1 : MvPolynomial σ R) ^ m) * esymm σ R m := by ring
        _ = 1 * esymm σ R m := by rw [h_neg1_sq]
        _ = esymm σ R m := by ring

/-- The ω-involution is an involution: ω ∘ ω = id.

    This follows from ω(e_k) = h_k and ω(h_k) = e_k, since the e_k generate
    the symmetric subalgebra. -/
theorem omegaInvolution_involutive {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n) :
    (omegaInvolution hn).comp (omegaInvolution hn) = AlgHom.id R _ := by
  -- To show ω ∘ ω = id, we show they agree on all elements
  apply AlgHom.ext
  intro x
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  -- x is in the symmetric subalgebra, write x = esymmAlgEquiv p for some p
  obtain ⟨p, hp⟩ := (esymmAlgEquiv σ R hn).surjective x
  subst hp
  -- We use induction on p
  induction p using MvPolynomial.induction_on with
  | C r =>
    -- For constants, ω(ω(algebraMap r)) = algebraMap r since ω is an R-algebra homomorphism
    have h1 : (esymmAlgEquiv σ R hn) (C r) = algebraMap R _ r := by
      simp [esymmAlgEquiv, esymmAlgHom]
    rw [h1]
    simp only [AlgHom.commutes]
  | add p q ihp ihq =>
    -- ω preserves addition
    simp only [map_add, ihp, ihq]
  | mul_X p i ih =>
    -- ω preserves multiplication
    simp only [map_mul, ih]
    -- Need to show ω(ω(esymmAlgEquiv (X i))) = esymmAlgEquiv (X i)
    refine congrArg (HMul.hMul _) ?_
    -- esymmAlgEquiv (X i) = ⟨e_{i+1}, _⟩
    have h1 : (esymmAlgEquiv σ R hn) (X i) = ⟨esymm σ R (i + 1), esymm_isSymmetric σ R (i + 1)⟩ := by
      simp [esymmAlgEquiv, esymmAlgHom]
    rw [h1]
    -- ω(e_{i+1}) = h_{i+1} by omegaInvolution_esymm_succ
    have h2 : omegaInvolution hn ⟨esymm σ R (i + 1), esymm_isSymmetric σ R (i + 1)⟩ = 
              ⟨hsymm σ R (i + 1), hsymm_isSymmetric σ R (i + 1)⟩ := by
      apply Subtype.ext
      exact omegaInvolution_esymm_succ hn i.val i.isLt
    rw [h2]
    -- ω(h_{i+1}) = e_{i+1} by omegaInvolution_hsymm_succ
    have h3 : omegaInvolution hn ⟨hsymm σ R (i + 1), hsymm_isSymmetric σ R (i + 1)⟩ = 
              ⟨esymm σ R (i + 1), esymm_isSymmetric σ R (i + 1)⟩ := by
      apply Subtype.ext
      exact omegaInvolution_hsymm_succ hn i.val i.isLt
    rw [h3]

/-- The ω-involution is bijective. -/
theorem omegaInvolution_bijective {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n) :
    Function.Bijective (omegaInvolution (R := R) hn) := by
  constructor
  · -- Injectivity: ω ∘ ω = id implies ω is injective
    intro x y hxy
    have h := congr_arg (omegaInvolution hn) hxy
    simp only [← AlgHom.comp_apply, omegaInvolution_involutive hn, AlgHom.id_apply] at h
    exact h
  · -- Surjectivity: ω ∘ ω = id implies ω is surjective
    intro y
    use omegaInvolution hn y
    simp only [← AlgHom.comp_apply, omegaInvolution_involutive hn, AlgHom.id_apply]

/-- The ω-involution as an algebra equivalence. -/
noncomputable def omegaInvolutionEquiv {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n : ℕ} (hn : Fintype.card σ = n) :
    symmetricSubalgebra σ R ≃ₐ[R] symmetricSubalgebra σ R :=
  AlgEquiv.ofBijective (omegaInvolution hn) (omegaInvolution_bijective hn)

/-!
## Application to Jacobi-Trudi

The ω-involution is used to prove the second Jacobi-Trudi formula from the first.
The key insight is that applying ω to both sides of the first Jacobi-Trudi formula
transforms h_k entries to e_k entries, while transforming s_{λ/μ} to s_{λᵗ/μᵗ}.
-/

/-- The ω-involution applied to a determinant of h-entries gives a determinant of e-entries.
    
    This is a key step in the proof of the second Jacobi-Trudi formula:
    ω(det(h_{λᵢ - μⱼ - i + j})) = det(e_{λᵢ - μⱼ - i + j})
    
    Note: This requires showing that ω commutes with taking determinants,
    which follows from ω being an algebra homomorphism. -/
theorem omegaInvolution_det_hsymm {σ : Type*} [Fintype σ] [DecidableEq σ] 
    {R : Type*} [CommRing R] {n m : ℕ} (hn : Fintype.card σ = n)
    (M : Matrix (Fin m) (Fin m) (symmetricSubalgebra σ R)) :
    omegaInvolution hn M.det = (M.map (omegaInvolution hn)).det :=
  AlgHom.map_det (omegaInvolution hn) M

end SymmetricFunctions
