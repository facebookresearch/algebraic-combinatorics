/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# The Generating Function of a Weighted Set

This file formalizes the theory of weighted sets and their weight generating functions,
following Section sec.gf.weighted-set of the Algebraic Combinatorics notes.

A weighted set is a set equipped with a weight function to ℕ. When the set is "finite-type"
(only finitely many elements of each weight), we can define its weight generating function
as a formal power series.

## Main Definitions

* `WeightedSet`: A set with a weight function to ℕ
* `WeightedSet.IsFiniteType`: Predicate for finite-type weighted sets
* `WeightedSet.weightGenFun`: The weight generating function of a finite-type weighted set
* `WeightedSet.Isomorphism`: Weight-preserving bijections between weighted sets
* `WeightedSet.disjointUnion`: Disjoint union of weighted sets (A + B)
* `WeightedSet.prod`: Product of weighted sets (A × B) with additive weights
* `WeightedSet.pow`: Cartesian power of a weighted set
* `WeightedSet.tuples`: Infinite disjoint union W^0 + W^1 + W^2 + ... (Kleene star)

## Main Results

* `WeightedSet.weightGenFun_eq_of_isomorphic`: Isomorphic weighted sets have equal generating functions
* `WeightedSet.weightGenFun_disjointUnion`: ḡ(A + B) = ḡ(A) + ḡ(B)
* `WeightedSet.weightGenFun_prod`: ḡ(A × B) = ḡ(A) · ḡ(B)
* `WeightedSet.weightGenFun_pow`: ḡ(A^k) = ḡ(A)^k
* `DominoTilingsZ.tiling_decomposition_isomorphism`: D ≅ F^0 + F^1 + F^2 + ... (Lemma lem.gf.weighted-set.domino.fd)

## Applications

The file includes applications to:
* Counting compositions (recovering the formula for the generating function of compositions)
* Domino tilings of height-2 rectangles (connection to Fibonacci numbers)

Note: Height-3 domino tilings are handled in `Details/DominoTilings.lean`.

## References

* [Flajolet and Sedgewick, *Analytic Combinatorics*, Part A][FlaSed09]
* [Fink, *Enumerative Combinatorics*, §3.3-§3.4][Fink17]

## Tags

weighted set, generating function, combinatorial class, domino tiling
-/

open PowerSeries Finset BigOperators

noncomputable section

variable {R : Type*} [CommSemiring R]

/-! ### Weighted Sets -/

/-- A weighted set is a type equipped with a weight function to ℕ.
    (Definition \ref{def.gf-ws.weighted-sets}(a)) -/
structure WeightedSet (α : Type*) where
  /-- The weight function assigning a natural number to each element -/
  weight : α → ℕ

namespace WeightedSet

variable {α β γ : Type*}

/-- A weighted set is finite-type if for each n ∈ ℕ, there are only finitely many
    elements of weight n. (Definition \ref{def.gf-ws.weighted-sets}(b)) -/
def IsFiniteType (W : WeightedSet α) : Prop :=
  ∀ n : ℕ, Set.Finite {a : α | W.weight a = n}

/-- The set of elements of a given weight in a weighted set -/
def elementsOfWeight (W : WeightedSet α) (n : ℕ) : Set α :=
  {a : α | W.weight a = n}

/-- For a finite-type weighted set, the count of elements of weight n -/
def countOfWeight (W : WeightedSet α) (hft : W.IsFiniteType) (n : ℕ) : ℕ :=
  (hft n).toFinset.card

/-! ### Weight Generating Function -/

/-- The weight generating function of a finite-type weighted set is the FPS
    ∑_{n ∈ ℕ} (# of elements of weight n) · x^n.
    (Definition \ref{def.gf-ws.weighted-sets}(c)) -/
def weightGenFun (W : WeightedSet α) (hft : W.IsFiniteType) : R⟦X⟧ :=
  PowerSeries.mk fun n => (W.countOfWeight hft n : R)

/-- Alternative characterization: weightGenFun = ∑_{a ∈ A} x^{|a|} -/
theorem weightGenFun_eq_sum (W : WeightedSet α) (hft : W.IsFiniteType) :
    W.weightGenFun (R := R) hft = PowerSeries.mk fun n => ((hft n).toFinset.card : R) := by
  rfl

/-! ### Isomorphisms of Weighted Sets -/

/-- An isomorphism between weighted sets is a weight-preserving bijection.
    (Definition \ref{def.gf-ws.weighted-sets}(d)) -/
structure Isomorphism (W₁ : WeightedSet α) (W₂ : WeightedSet β) where
  /-- The underlying bijection -/
  toEquiv : α ≃ β
  /-- The bijection preserves weights -/
  weight_eq : ∀ a : α, W₂.weight (toEquiv a) = W₁.weight a

/-- Two weighted sets are isomorphic if there exists an isomorphism between them.
    (Definition \ref{def.gf-ws.weighted-sets}(e)) -/
def AreIsomorphic (W₁ : WeightedSet α) (W₂ : WeightedSet β) : Prop :=
  Nonempty (Isomorphism W₁ W₂)

notation W₁ " ≅ᵥ " W₂ => AreIsomorphic W₁ W₂

/-- Isomorphic finite-type weighted sets have equal weight generating functions.
    (Proposition \ref{prop.gf-ws.iso}) -/
theorem weightGenFun_eq_of_isomorphic (W₁ : WeightedSet α) (W₂ : WeightedSet β)
    (hft₁ : W₁.IsFiniteType) (hft₂ : W₂.IsFiniteType) (h : W₁ ≅ᵥ W₂) :
    W₁.weightGenFun (R := R) hft₁ = W₂.weightGenFun hft₂ := by
  obtain ⟨iso⟩ := h
  ext n
  simp only [weightGenFun, coeff_mk, countOfWeight]
  congr 1
  rw [← Nat.card_eq_card_finite_toFinset (hft₁ n), ← Nat.card_eq_card_finite_toFinset (hft₂ n)]
  apply Nat.card_congr
  refine Equiv.subtypeEquiv iso.toEquiv ?_
  intro a
  simp only [Set.mem_ofPred_eq]
  rw [iso.weight_eq]

/-! ### Disjoint Union of Weighted Sets -/

/-- The disjoint union of two weighted sets, with weights inherited from each component.
    (Definition \ref{def.gf-ws.djun}) -/
def disjointUnion (W₁ : WeightedSet α) (W₂ : WeightedSet β) : WeightedSet (α ⊕ β) where
  weight := Sum.elim W₁.weight W₂.weight

infixl:65 " +ᵥ " => disjointUnion

@[simp] lemma disjointUnion_weight_inl (W₁ : WeightedSet α) (W₂ : WeightedSet β) (a : α) :
    (W₁ +ᵥ W₂).weight (Sum.inl a) = W₁.weight a := rfl

@[simp] lemma disjointUnion_weight_inr (W₁ : WeightedSet α) (W₂ : WeightedSet β) (b : β) :
    (W₁ +ᵥ W₂).weight (Sum.inr b) = W₂.weight b := rfl

/-- The disjoint union of finite-type weighted sets is finite-type. -/
theorem disjointUnion_isFiniteType (W₁ : WeightedSet α) (W₂ : WeightedSet β)
    (hft₁ : W₁.IsFiniteType) (hft₂ : W₂.IsFiniteType) : (W₁ +ᵥ W₂).IsFiniteType := by
  intro n
  -- The set of elements of weight n in the disjoint union is the disjoint union
  -- of the sets of elements of weight n in each component
  have h1 : {a : α ⊕ β | (W₁ +ᵥ W₂).weight a = n} =
      Sum.inl '' {a : α | W₁.weight a = n} ∪ Sum.inr '' {b : β | W₂.weight b = n} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hx
      cases x with
      | inl a =>
        left
        exact ⟨a, hx, rfl⟩
      | inr b =>
        right
        exact ⟨b, hx, rfl⟩
    · intro hx
      rcases hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact ha
      · exact hb
  rw [h1]
  exact Set.Finite.union (Set.Finite.image _ (hft₁ n)) (Set.Finite.image _ (hft₂ n))

/-- The weight generating function of a disjoint union is the sum of the generating functions.
    (Proposition \ref{prop.gf-ws.djun}) -/
theorem weightGenFun_disjointUnion (W₁ : WeightedSet α) (W₂ : WeightedSet β)
    (hft₁ : W₁.IsFiniteType) (hft₂ : W₂.IsFiniteType) :
    (W₁ +ᵥ W₂).weightGenFun (R := R) (disjointUnion_isFiniteType W₁ W₂ hft₁ hft₂) =
      W₁.weightGenFun hft₁ + W₂.weightGenFun hft₂ := by
  ext n
  simp only [weightGenFun, PowerSeries.coeff_mk, map_add, countOfWeight]
  -- Use ncard which is independent of the proof of finiteness
  have h1 := hft₁ n
  have h2 := hft₂ n
  have hft_union := disjointUnion_isFiniteType W₁ W₂ hft₁ hft₂ n
  -- Convert to ncard
  have eq1 : (h1.toFinset.card : R) = ({a : α | W₁.weight a = n}.ncard : R) := by
    rw [Set.ncard_eq_toFinset_card _ h1]
  have eq2 : (h2.toFinset.card : R) = ({b : β | W₂.weight b = n}.ncard : R) := by
    rw [Set.ncard_eq_toFinset_card _ h2]
  have eq_union : (hft_union.toFinset.card : R) = ({x : α ⊕ β | (W₁ +ᵥ W₂).weight x = n}.ncard : R) := by
    rw [Set.ncard_eq_toFinset_card _ hft_union]
  rw [eq1, eq2, eq_union]
  -- Establish the set equality: elements of weight n in the disjoint union are
  -- either from W₁ or W₂
  have hset : {x : α ⊕ β | (W₁ +ᵥ W₂).weight x = n} =
              (Sum.inl (β := β)) '' {a : α | W₁.weight a = n} ∪ (Sum.inr (α := α)) '' {b : β | W₂.weight b = n} := by
    ext x
    simp only [disjointUnion, Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hx
      cases x with
      | inl a => left; exact ⟨a, hx, rfl⟩
      | inr b => right; exact ⟨b, hx, rfl⟩
    · intro hx
      rcases hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact ha
      · exact hb
  -- The two images are disjoint (Sum.inl and Sum.inr have disjoint ranges)
  have hdisj : Disjoint ((Sum.inl (β := β)) '' {a : α | W₁.weight a = n})
                        ((Sum.inr (α := α)) '' {b : β | W₂.weight b = n}) := by
    rw [Set.disjoint_iff]
    intro x ⟨⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
    cases ha
    simp at hb
  have h1' : ((Sum.inl (β := β)) '' {a : α | W₁.weight a = n}).Finite := h1.image Sum.inl
  have h2' : ((Sum.inr (α := α)) '' {b : β | W₂.weight b = n}).Finite := h2.image Sum.inr
  -- The ncard of a disjoint union is the sum of ncards
  have ncard_eq : {x : α ⊕ β | (W₁ +ᵥ W₂).weight x = n}.ncard =
                  {a : α | W₁.weight a = n}.ncard + {b : β | W₂.weight b = n}.ncard := by
    rw [hset, Set.ncard_union_eq hdisj h1' h2']
    rw [Set.ncard_image_of_injective _ Sum.inl_injective]
    rw [Set.ncard_image_of_injective _ Sum.inr_injective]
  simp only [ncard_eq, Nat.cast_add]

/-! ### Product of Weighted Sets -/

/-- The product of two weighted sets, with weight defined as the sum of component weights.
    (Definition \ref{def.gf-ws.prod}) -/
def prod (W₁ : WeightedSet α) (W₂ : WeightedSet β) : WeightedSet (α × β) where
  weight := fun ⟨a, b⟩ => W₁.weight a + W₂.weight b

infixl:70 " ×ᵥ " => prod

@[simp] lemma prod_weight (W₁ : WeightedSet α) (W₂ : WeightedSet β) (p : α × β) :
    (W₁ ×ᵥ W₂).weight p = W₁.weight p.1 + W₂.weight p.2 := rfl

/-- The product of finite-type weighted sets is finite-type.
    (Proof of first part of Proposition \ref{prop.gf-ws.prod}) -/
theorem prod_isFiniteType (W₁ : WeightedSet α) (W₂ : WeightedSet β)
    (hft₁ : W₁.IsFiniteType) (hft₂ : W₂.IsFiniteType) : (W₁ ×ᵥ W₂).IsFiniteType := by
  intro n
  -- The set of pairs with weight n is a subset of ⋃_{i ≤ n} {a | weight a = i} × {b | weight b = n - i}
  have h : {p : α × β | (W₁ ×ᵥ W₂).weight p = n} ⊆
      ⋃ i ∈ Finset.range (n + 1), {a | W₁.weight a = i} ×ˢ {b | W₂.weight b = n - i} := by
    intro ⟨a, b⟩ hab
    simp only [prod, Set.mem_ofPred_eq] at hab
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq, Finset.mem_range]
    refine ⟨W₁.weight a, ?_, rfl, ?_⟩
    · omega
    · omega
  apply Set.Finite.subset _ h
  apply Set.Finite.biUnion
  · exact (Finset.range (n + 1)).finite_toSet
  · intro i _
    exact Set.Finite.prod (hft₁ i) (hft₂ (n - i))

/-- The weight generating function of a product is the product of the generating functions.
    (Proposition \ref{prop.gf-ws.prod})

    This is the key theorem showing that the weight generating function respects
    Cartesian products: ḡ(A × B) = ḡ(A) · ḡ(B). The proof partitions the pairs of
    total weight n by the weight of the first component, showing this equals the
    convolution sum that defines multiplication of power series. -/
theorem weightGenFun_prod [DecidableEq α] [DecidableEq β] (W₁ : WeightedSet α) (W₂ : WeightedSet β)
    (hft₁ : W₁.IsFiniteType) (hft₂ : W₂.IsFiniteType) :
    (W₁ ×ᵥ W₂).weightGenFun (R := R) (prod_isFiniteType W₁ W₂ hft₁ hft₂) =
      W₁.weightGenFun hft₁ * W₂.weightGenFun hft₂ := by
  classical
  ext n
  rw [PowerSeries.coeff_mul]
  simp only [weightGenFun, PowerSeries.coeff_mk, countOfWeight]
  -- The count of weight n in product equals sum over (i,j) with i+j=n of products of counts
  have hft_prod := prod_isFiniteType W₁ W₂ hft₁ hft₂
  -- Show that the toFinset of the product weight set equals the biUnion of toFinsets
  have key : (hft_prod n).toFinset =
      (antidiagonal n).biUnion (fun ij => (hft₁ ij.1).toFinset ×ˢ (hft₂ ij.2).toFinset) := by
    ext ⟨a, b⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, mem_biUnion, mem_product,
      Finset.HasAntidiagonal.mem_antidiagonal, prod]
    constructor
    · intro h
      exact ⟨(W₁.weight a, W₂.weight b), h, rfl, rfl⟩
    · rintro ⟨⟨i, j⟩, hij, ha, hb⟩
      rw [ha, hb]
      exact hij
  rw [key]
  -- The biUnion is disjoint, so card equals sum of cards
  have hdisj : (antidiagonal n : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun ij => (hft₁ ij.1).toFinset ×ˢ (hft₂ ij.2).toFinset) := by
    intro ⟨i₁, j₁⟩ _ ⟨i₂, j₂⟩ _ hne
    simp only [Function.onFun, Finset.disjoint_iff_ne]
    intro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    simp only [mem_product, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hab hab'
    apply hne
    simp only [Prod.mk.injEq] at heq
    obtain ⟨ha_eq, hb_eq⟩ := heq
    rw [← hab.1, ← hab.2, ha_eq, hb_eq, hab'.1, hab'.2]
  rw [card_biUnion hdisj]
  simp only [card_product]
  -- Convert ↑(∑ ...) to ∑ ↑(...)
  push_cast
  rfl

/-! ### Cartesian Powers -/

/-- The k-th Cartesian power of a weighted set.
    Weight of (a₁, ..., aₖ) is |a₁| + ... + |aₖ|. -/
def pow (W : WeightedSet α) (k : ℕ) : WeightedSet (Fin k → α) where
  weight := fun f => ∑ i, W.weight (f i)

/-- The k-th power of a finite-type weighted set is finite-type. -/
theorem pow_isFiniteType (W : WeightedSet α) (hft : W.IsFiniteType) (k : ℕ) :
    (W.pow k).IsFiniteType := by
  intro n
  -- Show {a | W.weight a ≤ n} is finite (finite union of finite sets)
  have h_le_finite : Set.Finite {a : α | W.weight a ≤ n} := by
    have : {a : α | W.weight a ≤ n} = ⋃ m ≤ n, {a | W.weight a = m} := by
      ext a; simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      exact ⟨fun h => ⟨W.weight a, h, rfl⟩, fun ⟨_, hm, ha⟩ => ha ▸ hm⟩
    rw [this]
    exact Set.Finite.biUnion (Set.finite_le_nat n) fun m _ => hft m
  -- The set of f with weight n is a subset of f where each component has weight ≤ n
  apply Set.Finite.subset (Set.Finite.pi' fun _ => h_le_finite)
  intro f hf i
  simp only [Set.mem_ofPred_eq, pow] at hf ⊢
  exact (Finset.single_le_sum (by simp) (Finset.mem_univ i)).trans_eq hf

/-- Helper: pow (n+1) is isomorphic to W × pow n -/
def pow_succ_equiv (W : WeightedSet α) (n : ℕ) :
    Isomorphism (W.pow (n + 1)) (W ×ᵥ (W.pow n)) where
  toEquiv := (Fin.succFunEquiv α n).trans (Equiv.prodComm _ _)
  weight_eq := fun f => by
    simp only [pow, prod, Equiv.trans_apply, Equiv.prodComm_apply, Fin.succFunEquiv]
    rw [Fin.sum_univ_castSucc, add_comm]
    simp [Fin.last, Fin.natAdd, Fin.castSucc, Fin.castAdd]

/-- The weight generating function of A^k is (ḡ(A))^k.
    (Proposition \ref{prop.gf-ws.pow}) -/
theorem weightGenFun_pow (W : WeightedSet α) (hft : W.IsFiniteType) (k : ℕ) :
    (W.pow k).weightGenFun (R := R) (pow_isFiniteType W hft k) =
      (W.weightGenFun hft) ^ k := by
  classical
  induction k with
  | zero =>
    simp only [pow_zero]
    ext n
    simp only [weightGenFun, countOfWeight, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with hn
    · -- n = 0: Show that there's exactly one element of weight 0
      subst hn
      have heq : {f : Fin 0 → α | ∑ i : Fin 0, W.weight (f i) = 0} = Set.univ := by
        ext f
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        rfl
      have hFinset : (pow_isFiniteType W hft 0 0).toFinset = Finset.univ := by
        ext f
        simp only [Set.Finite.mem_toFinset, pow, heq, Set.mem_univ, Finset.mem_univ]
      rw [hFinset]
      haveI : Unique (Fin 0 → α) := Pi.uniqueOfIsEmpty fun _ => α
      simp
    · -- n ≠ 0: No function Fin 0 → α has weight n > 0
      have heq : {f : Fin 0 → α | ∑ i : Fin 0, W.weight (f i) = n} = ∅ := by
        ext f
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have : ∑ i : Fin 0, W.weight (f i) = 0 := rfl
        omega
      have hFinset : (pow_isFiniteType W hft 0 n).toFinset = ∅ := by
        ext f
        rw [Set.Finite.mem_toFinset]
        simp only [pow, heq, Set.mem_empty_iff_false]
        simp
      rw [hFinset]
      simp
  | succ n ih =>
    have hiso : (W.pow (n + 1)) ≅ᵥ (W ×ᵥ (W.pow n)) := ⟨pow_succ_equiv W n⟩
    calc (W.pow (n + 1)).weightGenFun (R := R) (pow_isFiniteType W hft (n + 1))
        = (W ×ᵥ (W.pow n)).weightGenFun (prod_isFiniteType W (W.pow n) hft (pow_isFiniteType W hft n)) := by
          exact weightGenFun_eq_of_isomorphic _ _ _ _ hiso
      _ = W.weightGenFun hft * (W.pow n).weightGenFun (pow_isFiniteType W hft n) := by
          exact weightGenFun_prod _ _ _ _
      _ = W.weightGenFun hft * (W.weightGenFun hft) ^ n := by rw [ih]
      _ = (W.weightGenFun hft) ^ (n + 1) := by ring

/-! ### Infinite Disjoint Union (Tuples) -/

/-- The infinite disjoint union W^0 + W^1 + W^2 + ... of all tuples of elements.
    This is the "Kleene star" construction on weighted sets.
    An element is a pair (k, f) where k ∈ ℕ and f : Fin k → α is a k-tuple.
    The weight of (k, f) is the sum of weights of the entries: ∑ᵢ |f(i)|. -/
def tuples (W : WeightedSet α) : WeightedSet (Σ n : ℕ, Fin n → α) where
  weight := fun ⟨n, f⟩ => ∑ i : Fin n, W.weight (f i)

/-- The weight in the tuples weighted set equals the weight in the corresponding power -/
theorem tuples_weight_eq_pow (W : WeightedSet α) (n : ℕ) (f : Fin n → α) :
    W.tuples.weight ⟨n, f⟩ = (W.pow n).weight f := by
  simp only [tuples, pow]

/-- A weighted set has positive weights if every element has weight ≥ 1 -/
def HasPositiveWeights (W : WeightedSet α) : Prop :=
  ∀ a : α, W.weight a ≥ 1

/-- The tuples weighted set is finite-type if the original is finite-type and has positive weights.
    
    Note: The hypothesis `hpos : W.HasPositiveWeights` is necessary. Without it, the theorem is false:
    if W has elements of weight 0, then for any weight m, there are infinitely many tuples of weight m
    (we can have arbitrarily many weight-0 elements in a tuple). For example, if W = ℕ with weight = id,
    then tuples of weight 2 include ⟨1, ![2]⟩, ⟨2, ![0, 2]⟩, ⟨3, ![0, 0, 2]⟩, etc.
    
    The key insight is that with positive weights, a tuple of length n has weight ≥ n, so for weight m,
    we only need to consider tuples of length ≤ m. -/
theorem tuples_isFiniteType (W : WeightedSet α) (hft : W.IsFiniteType)
    (hpos : W.HasPositiveWeights) : W.tuples.IsFiniteType := by
  intro m
  -- Key: if every element has weight ≥ 1, then a tuple of length n has weight ≥ n
  -- So for weight = m, we can only have tuples of length ≤ m
  have h : {p : Σ n : ℕ, Fin n → α | W.tuples.weight p = m} ⊆
      ⋃ n ∈ Finset.range (m + 1), Sigma.mk n '' {f : Fin n → α | (W.pow n).weight f = m} := by
    intro ⟨n, f⟩ hf
    simp only [tuples, Set.mem_ofPred_eq] at hf
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_range, pow, Set.mem_ofPred_eq]
    refine ⟨n, ?_, f, hf, rfl⟩
    -- Need to show n < m + 1, i.e., n ≤ m
    -- Since each element has weight ≥ 1, sum of n weights ≥ n
    have hge : ∑ i : Fin n, W.weight (f i) ≥ n := by
      calc ∑ i : Fin n, W.weight (f i) ≥ ∑ i : Fin n, 1 := 
        Finset.sum_le_sum (fun i _ => hpos (f i))
        _ = n := by simp
    omega
  apply Set.Finite.subset _ h
  apply Set.Finite.biUnion
  · exact (Finset.range (m + 1)).finite_toSet
  · intro n _
    -- {f : Fin n → α | (W.pow n).weight f = m} is finite by pow_isFiniteType
    exact Set.Finite.image _ (pow_isFiniteType W hft n m)

end WeightedSet

/-! ### Examples and Applications -/

namespace WeightedSetExamples

/-! #### Binary Strings (Example \ref{exa.ws.bin-string1}) -/

/-- Binary strings (finite tuples of 0s and 1s) with weight = length -/
def BinaryStrings : WeightedSet (List (Fin 2)) where
  weight := List.length

/-- The binary strings weighted set is finite-type -/
theorem binaryStrings_isFiniteType : BinaryStrings.IsFiniteType := fun n =>
  Set.finite_coe_iff.mp (Finite.of_fintype (List.Vector (Fin 2) n))

/-- Helper lemma: the count of binary strings of length n is 2^n -/
private lemma binaryStrings_countOfWeight (n : ℕ) :
    BinaryStrings.countOfWeight binaryStrings_isFiniteType n = 2 ^ n := by
  unfold WeightedSet.countOfWeight
  have h_eq : {a : List (Fin 2) | BinaryStrings.weight a = n} =
              Set.range (List.Vector.toList : List.Vector (Fin 2) n → List (Fin 2)) := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_range, BinaryStrings]
    constructor
    · intro hl; exact ⟨⟨l, hl⟩, rfl⟩
    · intro ⟨v, hv⟩; rw [← hv]; exact v.toList_length
  have h_inj : Function.Injective (List.Vector.toList : List.Vector (Fin 2) n → List (Fin 2)) := by
    intro v w h
    exact List.Vector.toList_injective h
  have h_finite := binaryStrings_isFiniteType n
  have h_card : h_finite.toFinset.card = {a : List (Fin 2) | BinaryStrings.weight a = n}.ncard := by
    rw [Set.ncard]
    simp only [h_finite.encard_eq_coe_toFinset_card, ENat.toNat_natCast]
  rw [h_card, h_eq]
  rw [Set.ncard_range_of_injective h_inj]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.ofEquiv_card (Equiv.vectorEquivFin (Fin 2) n).symm]
  simp [Fintype.card_fin]

/-- The generating function of binary strings is 1/(1-2x).
    Since (mk 1) represents 1 + x + x² + ... = 1/(1-x),
    we express 1/(1-2x) differently. -/
theorem weightGenFun_binaryStrings :
    BinaryStrings.weightGenFun (R := ℚ) binaryStrings_isFiniteType =
      PowerSeries.mk fun n => (2 ^ n : ℚ) := by
  ext n
  simp only [WeightedSet.weightGenFun, PowerSeries.coeff_mk]
  rw [binaryStrings_countOfWeight]
  simp

/-! #### Positive Integers -/

/-- The positive integers with weight = value -/
def PositiveIntegers : WeightedSet ℕ+ where
  weight := fun n => n.val

/-- Positive integers form a finite-type weighted set -/
theorem positiveIntegers_isFiniteType : PositiveIntegers.IsFiniteType := by
  intro n
  -- The set {a : ℕ+ | a.val = n} has at most one element
  apply Set.Subsingleton.finite
  intro x hx y hy
  simp only [Set.mem_ofPred_eq, PositiveIntegers] at hx hy
  exact PNat.eq (hx.trans hy.symm)

private lemma countOfWeight_zero : PositiveIntegers.countOfWeight positiveIntegers_isFiniteType 0 = 0 := by
  simp only [WeightedSet.countOfWeight]
  convert Finset.card_empty
  simp only [Set.Finite.toFinset_eq_empty]
  ext x
  simp only [PositiveIntegers, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact x.2.ne'

set_option backward.isDefEq.respectTransparency false in
private lemma countOfWeight_pos (n : ℕ) (hn : 0 < n) :
    PositiveIntegers.countOfWeight positiveIntegers_isFiniteType n = 1 := by
  simp only [WeightedSet.countOfWeight]
  have h : (positiveIntegers_isFiniteType n).toFinset = {⟨n, hn⟩} := by
    ext x
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton]
    constructor
    · intro h
      exact PNat.eq h
    · intro h
      simp [h, PositiveIntegers]
  rw [h]
  simp

/-- The generating function of positive integers is x + x² + x³ + ... = x/(1-x) -/
theorem weightGenFun_positiveIntegers :
    PositiveIntegers.weightGenFun (R := ℚ) positiveIntegers_isFiniteType =
      PowerSeries.X * (PowerSeries.invOneSubPow ℚ 1).val := by
  ext n
  simp only [WeightedSet.weightGenFun, coeff_mk]
  cases n with
  | zero =>
    simp [countOfWeight_zero, coeff_zero_X_mul]
  | succ n =>
    rw [coeff_succ_X_mul]
    rw [countOfWeight_pos (n + 1) (Nat.succ_pos n)]
    rw [show (1 : ℕ) = 0 + 1 from rfl, invOneSubPow_val_succ_eq_mk_add_choose]
    simp

/-! #### Compositions -/

/-- Compositions of length k are k-tuples of positive integers -/
def Compositions (k : ℕ) : WeightedSet (Fin k → ℕ+) :=
  PositiveIntegers.pow k

/-- Compositions form a finite-type weighted set -/
theorem compositions_isFiniteType (k : ℕ) : (Compositions k).IsFiniteType :=
  WeightedSet.pow_isFiniteType _ positiveIntegers_isFiniteType k

/-- The generating function of compositions of length k is (x/(1-x))^k -/
theorem weightGenFun_compositions (k : ℕ) :
    (Compositions k).weightGenFun (R := ℚ) (compositions_isFiniteType k) =
      (PowerSeries.X * (PowerSeries.invOneSubPow ℚ 1).val) ^ k := by
  -- Compositions k = PositiveIntegers.pow k by definition
  -- By weightGenFun_pow, the generating function of A^k is (ḡ(A))^k
  -- By weightGenFun_positiveIntegers, ḡ(PositiveIntegers) = X * (invOneSubPow ℚ 1).val
  simp only [Compositions]
  rw [WeightedSet.weightGenFun_pow PositiveIntegers positiveIntegers_isFiniteType k,
      weightGenFun_positiveIntegers]

end WeightedSetExamples

/-! ### Domino Tilings -/

namespace DominoTilingsZ

/-! #### Shapes and Dominos (Definition \ref{def.domino.shapes-and-tilings}) -/

/-- A shape is a subset of ℤ² (Definition \ref{def.domino.shapes-and-tilings}(a)) -/
abbrev Shape := Set (ℤ × ℤ)

/-- The n × m rectangle (Definition \ref{def.domino.shapes-and-tilings}(b)) -/
def Rectangle (n m : ℕ) : Shape :=
  {p : ℤ × ℤ | 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ m}

/-- Membership in a rectangle -/
theorem mem_rectangle_iff {n m : ℕ} {p : ℤ × ℤ} :
    p ∈ Rectangle n m ↔ 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ m := Iff.rfl

/-- The 0 × m rectangle is empty -/
@[simp]
theorem Rectangle_zero_left (m : ℕ) : Rectangle 0 m = ∅ := by
  ext p
  simp only [Rectangle, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  omega

/-- The n × 0 rectangle is empty -/
@[simp]
theorem Rectangle_zero_right (n : ℕ) : Rectangle n 0 = ∅ := by
  ext p
  simp only [Rectangle, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 _ h3
  omega

/-- The rectangle has n * m cells -/
theorem Rectangle_ncard (n m : ℕ) : (Rectangle n m).ncard = n * m := by
  have h : Rectangle n m = Set.Icc (1 : ℤ) n ×ˢ Set.Icc (1 : ℤ) m := by
    ext ⟨x, y⟩
    simp only [Rectangle, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc]
    tauto
  rw [h, Set.ncard_prod]
  simp [Set.ncard_eq_toFinset_card', Set.toFinset_Icc]

/-- A domino is either horizontal or vertical (Definition \ref{def.domino.shapes-and-tilings}(c)) -/
inductive Domino : Type
  | horizontal (i j : ℤ) : Domino  -- {(i,j), (i+1,j)}
  | vertical (i j : ℤ) : Domino    -- {(i,j), (i,j+1)}
  deriving DecidableEq

/-- The cells covered by a domino -/
def Domino.toShape : Domino → Shape
  | .horizontal i j => {(i, j), (i + 1, j)}
  | .vertical i j => {(i, j), (i, j + 1)}

/-- A domino covers exactly 2 cells -/
theorem Domino.toShape_ncard (d : Domino) : d.toShape.ncard = 2 := by
  cases d with
  | horizontal i j =>
    simp only [toShape]
    rw [Set.ncard_pair]
    simp only [Prod.mk.injEq, ne_eq, not_and]
    intro _
    omega
  | vertical i j =>
    simp only [toShape]
    rw [Set.ncard_pair]
    simp only [Prod.mk.injEq, ne_eq, not_and]
    intro _ _
    omega

/-- A horizontal domino covers the cells (i,j) and (i+1,j) -/
@[simp]
theorem Domino.horizontal_toShape (i j : ℤ) :
    (Domino.horizontal i j).toShape = {(i, j), (i + 1, j)} := rfl

/-- A vertical domino covers the cells (i,j) and (i,j+1) -/
@[simp]
theorem Domino.vertical_toShape (i j : ℤ) :
    (Domino.vertical i j).toShape = {(i, j), (i, j + 1)} := rfl

/-- The shape of a domino is nonempty -/
theorem Domino.toShape_nonempty (d : Domino) : d.toShape.Nonempty := by
  cases d with
  | horizontal i j => exact ⟨(i, j), Set.mem_insert _ _⟩
  | vertical i j => exact ⟨(i, j), Set.mem_insert _ _⟩

/-- The shape of a domino is finite -/
theorem Domino.toShape_finite (d : Domino) : d.toShape.Finite := by
  cases d <;> simp only [toShape, Set.finite_insert, Set.finite_singleton]

/-- Two dominos with the same shape are equal.
    This follows from the fact that a domino's shape uniquely determines its type and position. -/
theorem Domino.eq_of_toShape_eq {d1 d2 : Domino} (h : d1.toShape = d2.toShape) : d1 = d2 := by
  cases d1 with
  | horizontal i1 j1 =>
    cases d2 with
    | horizontal i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1 + 1, j1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> [omega; simp only [hi1, hj1]]
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega
    | vertical i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1 + 1, j1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩ <;>
      rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega
  | vertical i1 j1 =>
    cases d2 with
    | horizontal i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1, j1 + 1) ∈ ({(i2, j2), (i2 + 1, j2)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩ <;>
      rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega
    | vertical i2 j2 =>
      simp only [toShape] at h
      have h1 : (i1, j1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert _ _
      have h2 : (i1, j1 + 1) ∈ ({(i2, j2), (i2, j2 + 1)} : Set (ℤ × ℤ)) := by rw [← h]; exact Set.mem_insert_of_mem _ rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> [omega; simp only [hi1, hj1]]
      · rcases h2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩ <;> omega

/-- A domino tiling of a shape S is a set partition of S into dominos
    (Definition \ref{def.domino.shapes-and-tilings}(d)) -/
structure Tiling (S : Shape) where
  /-- The set of dominos in the tiling -/
  dominos : Set Domino
  /-- The dominos are pairwise disjoint -/
  pairwise_disjoint : Set.PairwiseDisjoint dominos Domino.toShape
  /-- The union of dominos equals the shape -/
  cover : ⋃ d ∈ dominos, d.toShape = S

/-- Two tilings are equal iff they have the same dominos -/
@[ext]
theorem Tiling.ext {S : Shape} (T1 T2 : Tiling S) (h : T1.dominos = T2.dominos) : T1 = T2 := by
  cases T1
  cases T2
  congr

/-- The empty tiling of an empty shape -/
def Tiling.empty : Tiling ∅ where
  dominos := ∅
  pairwise_disjoint := Set.pairwiseDisjoint_empty
  cover := by simp

/-- The empty shape has exactly one tiling (the empty tiling) -/
theorem Tiling.unique_empty (T : Tiling (∅ : Shape)) : T.dominos = ∅ := by
  by_contra h
  have hne : T.dominos.Nonempty := Set.nonempty_iff_ne_empty.mpr h
  obtain ⟨d, hd⟩ := hne
  have hsub : d.toShape ⊆ ∅ := by
    rw [← T.cover]
    exact Set.subset_biUnion_of_mem hd
  have hne' : d.toShape.Nonempty := Domino.toShape_nonempty d
  exact Set.not_nonempty_empty (hne'.mono hsub)

/-- The number of domino tilings of the n × m rectangle
    (Definition \ref{def.domino.shapes-and-tilings}(e))

    This is defined as the cardinality of the type of all tilings.
    Note: For this to be meaningful, the set of tilings must be finite,
    which holds for any finite rectangle. -/
def numTilings (n m : ℕ) : ℕ := Nat.card (Tiling (Rectangle n m))

notation "d_[" n "," m "]" => numTilings n m

/-! #### Height-2 Rectangle Tilings -/

/-- Domino tilings of height-2 rectangles, with weight = width of rectangle -/
def TilingsHeight2 : WeightedSet (Σ n : ℕ, Tiling (Rectangle n 2)) where
  weight := fun ⟨n, _⟩ => n

/-- TilingsHeight2 is a finite-type weighted set -/
theorem tilingsHeight2_isFiniteType : TilingsHeight2.IsFiniteType := by
  intro k
  -- The set of elements of weight k is exactly {(k, T) | T is a tiling of Rectangle k 2}
  have h : {a : (Σ n : ℕ, Tiling (Rectangle n 2)) | TilingsHeight2.weight a = k} =
           Sigma.mk k '' Set.univ := by
    ext ⟨n, T⟩
    simp only [TilingsHeight2, Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ, true_and]
    constructor
    · intro hn
      subst hn
      exact ⟨T, rfl⟩
    · intro ⟨T', hT'⟩
      simp only [Sigma.mk.injEq] at hT'
      exact hT'.1.symm
  rw [h]
  apply Set.Finite.image
  -- Prove that the set of tilings of Rectangle k 2 is finite
  -- A tiling is determined by its set of dominos, which is a subset of all possible dominos
  -- in the rectangle. Since the rectangle is finite, so is the set of possible dominos.
  let DominosIn : Set Domino := {d | d.toShape ⊆ Rectangle k 2}
  have hDominosIn_finite : Set.Finite DominosIn := by
    have h : DominosIn ⊆
        (Set.Icc (1 : ℤ) k ×ˢ Set.Icc (1 : ℤ) 2).image (fun p => Domino.horizontal p.1 p.2) ∪
        (Set.Icc (1 : ℤ) k ×ˢ Set.Icc (1 : ℤ) 2).image (fun p => Domino.vertical p.1 p.2) := by
      intro d hd
      cases d with
      | horizontal i j =>
        left
        simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
        use (i, j)
        simp only [DominosIn, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
        have h1 := hd (i, j) (by simp)
        simp only [Rectangle, Set.mem_ofPred_eq] at h1
        refine ⟨⟨⟨h1.1, ?_⟩, ⟨h1.2.2.1, h1.2.2.2⟩⟩, rfl⟩
        omega
      | vertical i j =>
        right
        simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
        use (i, j)
        simp only [DominosIn, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
        have h1 := hd (i, j) (by simp)
        simp only [Rectangle, Set.mem_ofPred_eq] at h1
        refine ⟨⟨⟨h1.1, h1.2.1⟩, ⟨h1.2.2.1, ?_⟩⟩, rfl⟩
        omega
    apply Set.Finite.subset _ h
    apply Set.Finite.union
    · apply Set.Finite.image
      apply Set.Finite.prod
      · exact Set.finite_Icc (1 : ℤ) k
      · exact Set.finite_Icc (1 : ℤ) 2
    · apply Set.Finite.image
      apply Set.Finite.prod
      · exact Set.finite_Icc (1 : ℤ) k
      · exact Set.finite_Icc (1 : ℤ) 2
  -- Now show tilings are finite
  let f : Tiling (Rectangle k 2) → Set Domino := fun T => T.dominos
  have hf : Function.Injective f := by
    intro T₁ T₂ h
    cases T₁; cases T₂
    simp only [f] at h
    congr
  have h_tiling_subset : ∀ T : Tiling (Rectangle k 2), T.dominos ⊆ DominosIn := by
    intro T d hd
    simp only [DominosIn, Set.mem_ofPred_eq]
    have h : d.toShape ⊆ ⋃ d' ∈ T.dominos, d'.toShape := by
      intro p hp
      simp only [Set.mem_iUnion]
      exact ⟨d, hd, hp⟩
    rw [T.cover] at h
    exact h
  have h_range : Set.range f ⊆ 𝒫 DominosIn := by
    intro s hs
    simp only [Set.mem_range, f] at hs
    obtain ⟨T, rfl⟩ := hs
    simp only [Set.mem_powerset_iff]
    exact h_tiling_subset T
  have h_powerset_finite : Set.Finite (𝒫 DominosIn) := hDominosIn_finite.powerset
  have h_range_finite : Set.Finite (Set.range f) := h_powerset_finite.subset h_range
  have h_univ_finite : Set.Finite (f ⁻¹' Set.range f) := by
    apply h_range_finite.preimage
    exact hf.injOn
  convert h_univ_finite
  ext x
  simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, exists_apply_eq_apply]

/-- A fault in a domino tiling is a vertical line that no domino straddles -/
def hasFault (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) : Prop :=
  k > 0 ∧ k < n ∧
  ∀ d ∈ T.dominos, match d with
    | .horizontal i _ => i < k ∨ i ≥ k + 1
    | .vertical _ _ => True

/-- hasFault only depends on the dominos set -/
theorem hasFault_eq_of_dominos_eq {n : ℕ} {T1 T2 : Tiling (Rectangle n 2)} 
    (h : T1.dominos = T2.dominos) (k : ℕ) : hasFault n T1 k ↔ hasFault n T2 k := by
  simp only [hasFault, h]

/-- A tiling is faultfree if it is nonempty and has no fault -/
def isFaultfree (n : ℕ) (T : Tiling (Rectangle n 2)) : Prop :=
  n > 0 ∧ ∀ k, ¬hasFault n T k

/-- isFaultfree only depends on the dominos set -/
theorem isFaultfree_eq_of_dominos_eq {n : ℕ} {T1 T2 : Tiling (Rectangle n 2)} 
    (h : T1.dominos = T2.dominos) : isFaultfree n T1 ↔ isFaultfree n T2 := by
  simp only [isFaultfree, hasFault_eq_of_dominos_eq h]

/-- Faultfree tilings of height-2 rectangles -/
def FaultfreeTilingsHeight2 : WeightedSet (Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T}) where
  weight := fun ⟨n, _⟩ => n

/-- FaultfreeTilingsHeight2 is finite-type -/
theorem faultfreeTilingsHeight2_isFiniteType : FaultfreeTilingsHeight2.IsFiniteType := by
  intro m
  have h := tilingsHeight2_isFiniteType m
  -- The faultfree tilings embed into all tilings
  let f : (Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T}) →
          (Σ n : ℕ, Tiling (Rectangle n 2)) := fun ⟨n, T, _⟩ => ⟨n, T⟩
  have hinj : Function.Injective f := by
    intro ⟨n₁, T₁, h₁⟩ ⟨n₂, T₂, h₂⟩ heq
    have heq' := Sigma.mk.inj_iff.mp heq
    obtain ⟨hn, hT⟩ := heq'
    subst hn
    simp only [heq_eq_eq] at hT
    subst hT
    rfl
  -- The image of the faultfree tilings under f is a subset of all tilings
  have himg : f '' {a | FaultfreeTilingsHeight2.weight a = m} ⊆
              {a | TilingsHeight2.weight a = m} := by
    intro ⟨n, T⟩ ⟨⟨n', T', hT'⟩, hmem, heq⟩
    simp only [Set.mem_ofPred_eq] at hmem ⊢
    obtain ⟨hn, hTeq⟩ := Sigma.mk.inj_iff.mp heq
    subst hn
    simp only [heq_eq_eq] at hTeq
    subst hTeq
    exact hmem
  -- Since the image is a subset of a finite set, it's finite
  have himg_fin : (f '' {a | FaultfreeTilingsHeight2.weight a = m}).Finite := h.subset himg
  -- Use Set.Finite.of_finite_image with InjOn
  have hinjOn : Set.InjOn f {a | FaultfreeTilingsHeight2.weight a = m} :=
    fun _ _ _ _ h => hinj h
  exact Set.Finite.of_finite_image himg_fin hinjOn

/-! ##### Helper lemmas for faultfree classification -/

private lemma domino_subset_rect (n : ℕ) (T : Tiling (Rectangle n 2)) (d : Domino) (hd : d ∈ T.dominos) :
    d.toShape ⊆ Rectangle n 2 := by
  intro x hx
  have : x ∈ ⋃ d ∈ T.dominos, d.toShape := by
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hx⟩
  rw [T.cover] at this
  exact this

private lemma cell_11_in_rect (n : ℕ) (hn : n ≥ 1) : (1, 1) ∈ Rectangle n 2 := by
  simp only [Rectangle, Set.mem_ofPred_eq]; omega

lemma exists_domino_covering_11 (n : ℕ) (hn : n ≥ 1) (T : Tiling (Rectangle n 2)) :
    ∃ d ∈ T.dominos, (1, 1) ∈ d.toShape := by
  have h11 : (1, 1) ∈ Rectangle n 2 := cell_11_in_rect n hn
  rw [← T.cover] at h11
  simp only [Set.mem_iUnion] at h11
  obtain ⟨d, hd, hmem⟩ := h11
  exact ⟨d, hd, hmem⟩

lemma domino_covering_11_valid (n : ℕ) (T : Tiling (Rectangle n 2))
    (d : Domino) (hd : d ∈ T.dominos) (h : (1, 1) ∈ d.toShape) :
    d = .vertical 1 1 ∨ d = .horizontal 1 1 := by
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · right; simp only [Domino.horizontal.injEq]; omega
    · exfalso
      have hcover : ((0 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        left; omega
      have := domino_subset_rect n T (Domino.horizontal i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · left; simp only [Domino.vertical.injEq]; omega
    · exfalso
      have hcover : ((1 : ℤ), (0 : ℤ)) ∈ (Domino.vertical i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        left; omega
      have := domino_subset_rect n T (Domino.vertical i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega

private lemma no_horizontal_at_1_if_vertical (n : ℕ) (T : Tiling (Rectangle n 2))
    (hv : Domino.vertical 1 1 ∈ T.dominos) (i j : ℤ)
    (hd : Domino.horizontal i j ∈ T.dominos) : i < 1 ∨ i ≥ 2 := by
  have hdisj := T.pairwise_disjoint hv hd
  by_contra h; push Not at h; obtain ⟨hi1, hi2⟩ := h
  have hi : i = 1 := by omega
  have hd' : Domino.horizontal 1 j ∈ T.dominos := by rwa [hi] at hd
  have hsub := domino_subset_rect n T (Domino.horizontal 1 j) hd'
  have h1j : ((1 : ℤ), j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
  simp only [Rectangle, Set.mem_ofPred_eq] at h1j
  have hj12 : j = 1 ∨ j = 2 := by omega
  have h_in_horiz : ((1 : ℤ), j) ∈ (Domino.horizontal 1 j).toShape := by simp [Domino.toShape]
  have h_in_vert : ((1 : ℤ), j) ∈ (Domino.vertical 1 1).toShape := by
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    rcases hj12 with rfl | rfl <;> simp
  have hne : Domino.vertical 1 1 ≠ Domino.horizontal i j := by simp
  have hdisj' : Disjoint (Domino.vertical 1 1).toShape (Domino.horizontal i j).toShape := hdisj hne
  rw [hi] at hdisj'
  exact Set.disjoint_iff.mp hdisj' ⟨h_in_vert, h_in_horiz⟩

lemma fault_at_1_if_vertical (n : ℕ) (hn : n ≥ 2) (T : Tiling (Rectangle n 2))
    (hv : Domino.vertical 1 1 ∈ T.dominos) : hasFault n T 1 := by
  refine ⟨by omega, by omega, ?_⟩
  intro d hd
  cases d with
  | horizontal i j =>
    have := no_horizontal_at_1_if_vertical n T hv i j hd
    rcases this with h | h
    · left; omega
    · right; omega
  | vertical i j => trivial

private lemma cell_12_in_rect (n : ℕ) (hn : n ≥ 1) : (1, 2) ∈ Rectangle n 2 := by
  simp only [Rectangle, Set.mem_ofPred_eq]; omega

private lemma exists_domino_covering_12 (n : ℕ) (hn : n ≥ 1) (T : Tiling (Rectangle n 2)) :
    ∃ d ∈ T.dominos, (1, 2) ∈ d.toShape := by
  have h12 : (1, 2) ∈ Rectangle n 2 := cell_12_in_rect n hn
  rw [← T.cover] at h12
  simp only [Set.mem_iUnion] at h12
  obtain ⟨d, hd, hmem⟩ := h12
  exact ⟨d, hd, hmem⟩

private lemma domino_covering_12_valid (n : ℕ) (T : Tiling (Rectangle n 2))
    (d : Domino) (hd : d ∈ T.dominos) (h : (1, 2) ∈ d.toShape) :
    d = .vertical 1 1 ∨ d = .horizontal 1 2 := by
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · right; simp only [Domino.horizontal.injEq]; omega
    · exfalso
      have hcover : ((0 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        left; omega
      have := domino_subset_rect n T (Domino.horizontal i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · exfalso
      have hcover : ((1 : ℤ), (3 : ℤ)) ∈ (Domino.vertical i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        right; omega
      have := domino_subset_rect n T (Domino.vertical i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega
    · left; simp only [Domino.vertical.injEq]; omega

lemma horizontal_12_if_horizontal_11 (n : ℕ) (hn : n ≥ 1) (T : Tiling (Rectangle n 2))
    (hh : Domino.horizontal 1 1 ∈ T.dominos) : Domino.horizontal 1 2 ∈ T.dominos := by
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering_12 n hn T
  have hcases := domino_covering_12_valid n T d hd hmem
  rcases hcases with rfl | rfl
  · exfalso
    have hdisj := T.pairwise_disjoint hd hh
    have hne : Domino.vertical 1 1 ≠ Domino.horizontal 1 1 := by simp
    have : Disjoint (Domino.vertical 1 1).toShape (Domino.horizontal 1 1).toShape := hdisj hne
    have h11_vert : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape := by simp [Domino.toShape]
    have h11_horiz : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
    exact Set.disjoint_iff.mp this ⟨h11_vert, h11_horiz⟩
  · exact hd

private lemma no_horizontal_at_2_if_horizontal_pair (n : ℕ) (T : Tiling (Rectangle n 2))
    (hh1 : Domino.horizontal 1 1 ∈ T.dominos) (hh2 : Domino.horizontal 1 2 ∈ T.dominos)
    (i j : ℤ) (hd : Domino.horizontal i j ∈ T.dominos) : i < 2 ∨ i ≥ 3 := by
  by_contra h; push Not at h; obtain ⟨hi1, hi2⟩ := h
  have hi : i = 2 := by omega
  have hsub := domino_subset_rect n T (Domino.horizontal i j) hd
  have hij : ((i : ℤ), j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
  simp only [Rectangle, Set.mem_ofPred_eq] at hij
  have hj12 : j = 1 ∨ j = 2 := by omega
  rcases hj12 with rfl | rfl
  · have hdisj := T.pairwise_disjoint hh1 hd
    have hne : Domino.horizontal 1 1 ≠ Domino.horizontal i 1 := by simp; omega
    have : Disjoint (Domino.horizontal 1 1).toShape (Domino.horizontal i 1).toShape := hdisj hne
    have h21_h11 : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
    have h21_hi1 : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal i 1).toShape := by simp [Domino.toShape, hi]
    exact Set.disjoint_iff.mp this ⟨h21_h11, h21_hi1⟩
  · have hdisj := T.pairwise_disjoint hh2 hd
    have hne : Domino.horizontal 1 2 ≠ Domino.horizontal i 2 := by simp; omega
    have : Disjoint (Domino.horizontal 1 2).toShape (Domino.horizontal i 2).toShape := hdisj hne
    have h22_h12 : ((2 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal 1 2).toShape := by simp [Domino.toShape]
    have h22_hi2 : ((2 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal i 2).toShape := by simp [Domino.toShape, hi]
    exact Set.disjoint_iff.mp this ⟨h22_h12, h22_hi2⟩

lemma fault_at_2_if_horizontal (n : ℕ) (hn : n ≥ 3) (T : Tiling (Rectangle n 2))
    (hh : Domino.horizontal 1 1 ∈ T.dominos) : hasFault n T 2 := by
  have hn1 : n ≥ 1 := by omega
  have hh2 := horizontal_12_if_horizontal_11 n hn1 T hh
  refine ⟨by omega, by omega, ?_⟩
  intro d hd
  cases d with
  | horizontal i j =>
    have := no_horizontal_at_2_if_horizontal_pair n T hh hh2 i j hd
    rcases this with h | h
    · left; omega
    · right; omega
  | vertical i j => trivial

/-- The only faultfree tilings of height-2 rectangles have width 1 or 2 -/
theorem faultfree_height2_classification (n : ℕ) (T : Tiling (Rectangle n 2))
    (hff : isFaultfree n T) : n = 1 ∨ n = 2 := by
  obtain ⟨hn_pos, hno_fault⟩ := hff
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  -- So n ≥ 3 (since n > 0, n ≠ 1, n ≠ 2)
  have hn3 : n ≥ 3 := by omega
  -- Get the domino covering (1,1)
  have hn1 : n ≥ 1 := by omega
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering_11 n hn1 T
  have hcases := domino_covering_11_valid n T d hd hmem
  rcases hcases with rfl | rfl
  · -- d = vertical 1 1: there's a fault at k=1
    have hfault := fault_at_1_if_vertical n (by omega) T hd
    exact hno_fault 1 hfault
  · -- d = horizontal 1 1: there's a fault at k=2
    have hfault := fault_at_2_if_horizontal n hn3 T hd
    exact hno_fault 2 hfault

/-- The unique tiling of the 1×2 rectangle (one vertical domino) -/
def tiling_1_2 : Tiling (Rectangle 1 2) where
  dominos := {Domino.vertical 1 1}
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_singleton_iff] at hd1 hd2
    subst hd1 hd2
    exact (hne rfl).elim
  cover := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, exists_eq_left,
               Domino.toShape, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact ⟨le_refl 1, le_refl 1, le_refl 1, by norm_num⟩
      · exact ⟨le_refl 1, le_refl 1, by norm_num, le_refl 2⟩
    · intro ⟨h1, h2, h3, h4⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      have hp1 : p.1 = 1 := by omega
      have hp2 : p.2 = 1 ∨ p.2 = 2 := by omega
      rcases hp2 with hp2eq | hp2eq
      · left; ext <;> omega
      · right; ext <;> omega

/-- The 1×2 tiling is faultfree -/
theorem tiling_1_2_faultfree : isFaultfree 1 tiling_1_2 := by
  constructor
  · omega
  · intro k ⟨hk1, hk2, _⟩
    omega

set_option backward.isDefEq.respectTransparency false in
/-- Every tiling of the 1×2 rectangle equals tiling_1_2 -/
theorem tiling_1_2_unique (T : Tiling (Rectangle 1 2)) : T = tiling_1_2 := by
  -- Prove equality by showing dominos are equal
  have hdom : T.dominos = tiling_1_2.dominos := by
    ext d
    constructor
    · intro hd
      have hsub : d.toShape ⊆ Rectangle 1 2 := by
        rw [← T.cover]
        exact Set.subset_biUnion_of_mem hd
      cases d with
      | horizontal i j =>
        simp only [Domino.toShape] at hsub
        have h1 : (i, j) ∈ Rectangle 1 2 := hsub (Set.mem_insert _ _)
        have h2 : (i + 1, j) ∈ Rectangle 1 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
        omega
      | vertical i j =>
        simp only [Domino.toShape] at hsub
        have h1 : (i, j) ∈ Rectangle 1 2 := hsub (Set.mem_insert _ _)
        have h2 : (i, j + 1) ∈ Rectangle 1 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
        have hi : i = 1 := by omega
        have hj : j = 1 := by omega
        subst hi hj
        exact Set.mem_singleton_iff.mpr rfl
    · intro hd
      simp only [tiling_1_2, Set.mem_singleton_iff] at hd
      subst hd
      have h11 : (1, 1) ∈ Rectangle 1 2 := by
        simp only [Rectangle, Set.mem_ofPred_eq]
        omega
      rw [← T.cover] at h11
      simp only [Set.mem_iUnion, exists_prop] at h11
      obtain ⟨d, hd, h11d⟩ := h11
      have hsub : d.toShape ⊆ Rectangle 1 2 := by
        rw [← T.cover]
        exact Set.subset_biUnion_of_mem hd
      cases d with
      | horizontal i j =>
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h11d
        rcases h11d with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · subst hi hj
          have h21 : @Prod.mk ℤ ℤ 2 1 ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
          have h21' : @Prod.mk ℤ ℤ 2 1 ∈ Rectangle 1 2 := hsub h21
          simp only [Rectangle, Set.mem_ofPred_eq] at h21'
          omega
        · have hi' : i = 0 := by omega
          subst hi' hj
          have h01 : @Prod.mk ℤ ℤ 0 1 ∈ (Domino.horizontal 0 1).toShape := by simp [Domino.toShape]
          have h01' : @Prod.mk ℤ ℤ 0 1 ∈ Rectangle 1 2 := hsub h01
          simp only [Rectangle, Set.mem_ofPred_eq] at h01'
          omega
      | vertical i j =>
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h11d
        rcases h11d with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · subst hi hj
          exact hd
        · have hj' : j = 0 := by omega
          subst hi hj'
          have h10 : @Prod.mk ℤ ℤ 1 0 ∈ (Domino.vertical 1 0).toShape := by simp [Domino.toShape]
          have h10' : @Prod.mk ℤ ℤ 1 0 ∈ Rectangle 1 2 := hsub h10
          simp only [Rectangle, Set.mem_ofPred_eq] at h10'
          omega
  -- Use the fact that tilings with equal dominos are equal
  cases T with | mk dom pd cov =>
  simp only [tiling_1_2, Tiling.mk.injEq]
  simp only [tiling_1_2] at hdom
  exact hdom

/-- The faultfree tiling of the 1×2 rectangle as a Subtype element -/
def faultfreeTiling_1_2 : {T : Tiling (Rectangle 1 2) // isFaultfree 1 T} :=
  ⟨tiling_1_2, tiling_1_2_faultfree⟩

/-- Every element of FaultfreeTilingsHeight2 with weight 1 equals faultfreeTiling_1_2 -/
theorem faultfreeTilingsHeight2_weight1_unique
    (x : Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T})
    (hx : FaultfreeTilingsHeight2.weight x = 1) :
    x = ⟨1, faultfreeTiling_1_2⟩ := by
  obtain ⟨n, T, hT⟩ := x
  simp only [FaultfreeTilingsHeight2] at hx
  subst hx
  congr 1
  -- Need to show ⟨T, hT⟩ = faultfreeTiling_1_2
  simp only [faultfreeTiling_1_2, Subtype.mk.injEq]
  exact tiling_1_2_unique T

/-- There is exactly one faultfree tiling of width 1 (one vertical domino) -/
theorem countOfWeight_faultfreeHeight2_one :
    FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType 1 = 1 := by
  unfold WeightedSet.countOfWeight
  have hset : {a | FaultfreeTilingsHeight2.weight a = 1} = {⟨1, faultfreeTiling_1_2⟩} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact faultfreeTilingsHeight2_weight1_unique x hx
    · intro hx
      subst hx
      rfl
  have hfin : ({⟨1, faultfreeTiling_1_2⟩} : Set (Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T})).Finite :=
    Set.finite_singleton _
  have heq : (faultfreeTilingsHeight2_isFiniteType 1).toFinset = hfin.toFinset := by
    apply Set.Finite.toFinset_inj.mpr
    exact hset
  rw [heq]
  simp only [Set.Finite.toFinset_singleton, card_singleton]

/-- The unique faultfree tiling of width 2: two horizontal dominos -/
def twoHorizontalDominos : Tiling (Rectangle 2 2) where
  dominos := {Domino.horizontal 1 1, Domino.horizontal 1 2}
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd1 hd2
    rcases hd1 with rfl | rfl <;> rcases hd2 with rfl | rfl
    · exact (hne rfl).elim
    · simp only [Set.disjoint_iff, Set.subset_empty_iff]; ext x
      simp only [Domino.toShape, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
                 Set.mem_empty_iff_false, iff_false, not_and]
      intro h1; rcases h1 with rfl | rfl <;> (intro h2; rcases h2 with h | h <;> simp_all)
    · simp only [Set.disjoint_iff, Set.subset_empty_iff]; ext x
      simp only [Domino.toShape, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
                 Set.mem_empty_iff_false, iff_false, not_and]
      intro h1; rcases h1 with rfl | rfl <;> (intro h2; rcases h2 with h | h <;> simp_all)
    · exact (hne rfl).elim
  cover := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop,
               Domino.toShape, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, hd, hp⟩
      rcases hd with rfl | rfl <;>
        (simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp; rcases hp with rfl | rfl <;> omega)
    · intro ⟨h1, h2, h3, h4⟩
      have hp1 : p.1 = 1 ∨ p.1 = 2 := by omega
      have hp2 : p.2 = 1 ∨ p.2 = 2 := by omega
      rcases hp2 with hp2' | hp2'
      · use Domino.horizontal 1 1, Or.inl rfl
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hp1 with hp1' | hp1' <;> [left; right] <;> ext <;> omega
      · use Domino.horizontal 1 2, Or.inr rfl
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hp1 with hp1' | hp1' <;> [left; right] <;> ext <;> omega

/-- The two horizontal dominos tiling is faultfree -/
theorem twoHorizontalDominos_isFaultfree : isFaultfree 2 twoHorizontalDominos := by
  constructor
  · omega
  · intro k hfault
    unfold hasFault at hfault
    obtain ⟨hk_pos, hk_lt, hdom⟩ := hfault
    have hk1 : k = 1 := by omega
    subst hk1
    have hcontra := hdom (Domino.horizontal 1 1) (by simp [twoHorizontalDominos])
    simp only at hcontra
    omega

/-- For a faultfree tiling of width 2, there must be a horizontal domino straddling position 1 -/
private lemma faultfree_width2_has_horizontal_at_1 (T : Tiling (Rectangle 2 2)) (hff : isFaultfree 2 T) :
    Domino.horizontal 1 1 ∈ T.dominos ∨ Domino.horizontal 1 2 ∈ T.dominos := by
  obtain ⟨_, hno_fault⟩ := hff
  by_contra h
  push Not at h
  obtain ⟨hnh1, hnh2⟩ := h
  have hfault : hasFault 2 T 1 := by
    refine ⟨by omega, by omega, ?_⟩
    intro d hd
    cases d with
    | horizontal i j =>
      have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
      have hij : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      have hij' : (i + 1, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq] at hij hij'
      have hi : i = 1 := by omega
      have hj : j = 1 ∨ j = 2 := by omega
      subst hi
      rcases hj with rfl | rfl
      · exact (hnh1 hd).elim
      · exact (hnh2 hd).elim
    | vertical _ _ => trivial
  exact hno_fault 1 hfault

private lemma exists_domino_covering' (n : ℕ) (T : Tiling (Rectangle n 2)) (i j : ℤ)
    (h : (i, j) ∈ Rectangle n 2) :
    ∃ d ∈ T.dominos, (i, j) ∈ d.toShape := by
  rw [← T.cover] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨d, hd, hmem⟩ := h
  exact ⟨d, hd, hmem⟩

/-- For a faultfree tiling of width 2, horizontal dominos at (1,1) and (1,2) must both be present -/
private lemma horizontal_11_implies_12' (T : Tiling (Rectangle 2 2))
    (hh : Domino.horizontal 1 1 ∈ T.dominos) : Domino.horizontal 1 2 ∈ T.dominos := by
  have h12 : (1, 2) ∈ Rectangle 2 2 := by simp only [Rectangle, Set.mem_ofPred_eq]; omega
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering' 2 T 1 2 h12
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · subst hi hj; exact hd
    · have hi' : i = 0 := by omega
      have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
      have h02 : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq, hi'] at h02
      omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hsub := domino_subset_rect 2 T (Domino.vertical i j) hd
      have h13 : (i, j + 1) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq, hi] at h13
      omega
    · have hi' : i = 1 := by omega
      have hj' : j = 1 := by omega
      subst hi' hj'
      have hdisj := T.pairwise_disjoint hh hd
      have hne : Domino.horizontal 1 1 ≠ Domino.vertical 1 1 := by intro h; cases h
      have hdisjoint : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 1 1).toShape := hdisj hne
      have h11_h : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := Set.mem_insert (1, 1) _
      have h11_v : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape := Set.mem_insert (1, 1) _
      exact False.elim (Set.not_disjoint_iff.mpr ⟨(1, 1), h11_h, h11_v⟩ hdisjoint)

private lemma horizontal_12_implies_11' (T : Tiling (Rectangle 2 2))
    (hh : Domino.horizontal 1 2 ∈ T.dominos) : Domino.horizontal 1 1 ∈ T.dominos := by
  have h11 : (1, 1) ∈ Rectangle 2 2 := by simp only [Rectangle, Set.mem_ofPred_eq]; omega
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering' 2 T 1 1 h11
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · subst hi hj; exact hd
    · have hi' : i = 0 := by omega
      have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
      have h01 : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq, hi'] at h01
      omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = 1 := by omega
      have hj' : j = 1 := by omega
      subst hi' hj'
      have hdisj := T.pairwise_disjoint hh hd
      have hne : Domino.horizontal 1 2 ≠ Domino.vertical 1 1 := by intro h; cases h
      have hdisjoint : Disjoint (Domino.horizontal 1 2).toShape (Domino.vertical 1 1).toShape := hdisj hne
      have h12_h : ((1 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal 1 2).toShape := Set.mem_insert (1, 2) _
      have h12_v : ((1 : ℤ), (2 : ℤ)) ∈ (Domino.vertical 1 1).toShape :=
        Set.mem_insert_of_mem _ (Set.mem_singleton _)
      exact False.elim (Set.not_disjoint_iff.mpr ⟨(1, 2), h12_h, h12_v⟩ hdisjoint)
    · have hj' : j = 0 := by omega
      have hsub := domino_subset_rect 2 T (Domino.vertical i j) hd
      have h10 : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq, hj'] at h10
      omega

/-- A faultfree tiling of width 2 has exactly horizontal 1 1 and horizontal 1 2 -/
private lemma faultfree_width2_dominos (T : Tiling (Rectangle 2 2)) (hff : isFaultfree 2 T) :
    Domino.horizontal 1 1 ∈ T.dominos ∧ Domino.horizontal 1 2 ∈ T.dominos := by
  have h := faultfree_width2_has_horizontal_at_1 T hff
  rcases h with hh1 | hh2
  · exact ⟨hh1, horizontal_11_implies_12' T hh1⟩
  · exact ⟨horizontal_12_implies_11' T hh2, hh2⟩

/-- The dominos of a faultfree tiling of width 2 are exactly {horizontal 1 1, horizontal 1 2} -/
private lemma faultfree_width2_dominos_eq (T : Tiling (Rectangle 2 2)) (hff : isFaultfree 2 T) :
    T.dominos = {Domino.horizontal 1 1, Domino.horizontal 1 2} := by
  have ⟨hh1, hh2⟩ := faultfree_width2_dominos T hff
  ext d
  constructor
  · intro hd
    have hsub := domino_subset_rect 2 T d hd
    cases d with
    | horizontal i j =>
      have hij : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      have hij' : (i + 1, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq] at hij hij'
      have hi : i = 1 := by omega
      have hj : j = 1 ∨ j = 2 := by omega
      subst hi
      rcases hj with rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    | vertical i j =>
      have hij : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      have hij' : (i, j + 1) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq] at hij hij'
      have hi : i = 1 ∨ i = 2 := by omega
      have hj : j = 1 := by omega
      subst hj
      rcases hi with rfl | rfl
      · have hdisj := T.pairwise_disjoint hh1 hd
        have hne : Domino.horizontal 1 1 ≠ Domino.vertical 1 1 := by intro h; cases h
        have hdisjoint : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 1 1).toShape := hdisj hne
        have h11_h : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := Set.mem_insert (1, 1) _
        have h11_v : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape := Set.mem_insert (1, 1) _
        exact False.elim (Set.not_disjoint_iff.mpr ⟨(1, 1), h11_h, h11_v⟩ hdisjoint)
      · have hdisj := T.pairwise_disjoint hh1 hd
        have hne : Domino.horizontal 1 1 ≠ Domino.vertical 2 1 := by intro h; cases h
        have hdisjoint : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 2 1).toShape := hdisj hne
        have h21_h : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape :=
          Set.mem_insert_of_mem _ (Set.mem_singleton _)
        have h21_v : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 2 1).toShape := Set.mem_insert (2, 1) _
        exact False.elim (Set.not_disjoint_iff.mpr ⟨(2, 1), h21_h, h21_v⟩ hdisjoint)
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl
    · exact hh1
    · exact hh2

set_option backward.isDefEq.respectTransparency false in
/-- Any faultfree tiling of Rectangle 2 2 equals twoHorizontalDominos -/
theorem faultfree_tiling_width2_unique (T : Tiling (Rectangle 2 2)) (hff : isFaultfree 2 T) :
    T = twoHorizontalDominos := by
  have hdom := faultfree_width2_dominos_eq T hff
  cases T with | mk dom pd cov =>
  simp only [twoHorizontalDominos, Tiling.mk.injEq]
  exact hdom

/-- There is exactly one faultfree tiling of width 2 (two horizontal dominos) -/
theorem countOfWeight_faultfreeHeight2_two :
    FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType 2 = 1 := by
  unfold WeightedSet.countOfWeight
  -- The set of faultfree tilings of weight 2 is a singleton
  have hsingleton : {a : Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T} |
      FaultfreeTilingsHeight2.weight a = 2} =
      {⟨2, twoHorizontalDominos, twoHorizontalDominos_isFaultfree⟩} := by
    ext ⟨n, T, hT⟩
    simp only [FaultfreeTilingsHeight2, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hn
      subst hn
      have heq := faultfree_tiling_width2_unique T hT
      subst heq
      rfl
    · intro heq
      simp only [Sigma.mk.inj_iff] at heq
      obtain ⟨hn, hTeq⟩ := heq
      simp only [hn]
  have hfin := faultfreeTilingsHeight2_isFiniteType 2
  have hfin' := Set.finite_singleton (⟨2, twoHorizontalDominos, twoHorizontalDominos_isFaultfree⟩ :
      Σ n : ℕ, {T : Tiling (Rectangle n 2) // isFaultfree n T})
  have heq_fin : hfin.toFinset = hfin'.toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      have : x ∈ {a | FaultfreeTilingsHeight2.weight a = 2} := hx
      rw [hsingleton] at this
      exact this
    · intro hx
      subst hx
      rfl
  rw [heq_fin]
  simp only [Set.Finite.toFinset_singleton, card_singleton]

/-- For n ≠ 1 and n ≠ 2, there are no faultfree tilings of width n -/
theorem countOfWeight_faultfreeHeight2_eq_zero (n : ℕ) (hn1 : n ≠ 1) (hn2 : n ≠ 2) :
    FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType n = 0 := by
  unfold WeightedSet.countOfWeight
  rw [Finset.card_eq_zero]
  ext ⟨m, T, hT⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · intro hm
    simp only [FaultfreeTilingsHeight2] at hm
    have := faultfree_height2_classification m T hT
    simp
    omega
  · simp

/-- The generating function of faultfree height-2 tilings is x + x² -/
theorem weightGenFun_faultfreeHeight2 :
    FaultfreeTilingsHeight2.weightGenFun (R := ℚ) faultfreeTilingsHeight2_isFiniteType =
      PowerSeries.X + PowerSeries.X ^ 2 := by
  ext n
  simp only [WeightedSet.weightGenFun, PowerSeries.coeff_mk, map_add, coeff_X, coeff_X_pow]
  rcases n with _ | _ | _ | n
  · -- n = 0
    have h0 : FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType 0 = 0 :=
      countOfWeight_faultfreeHeight2_eq_zero 0 (by omega) (by omega)
    simp [h0]
  · -- n = 1
    rw [countOfWeight_faultfreeHeight2_one]
    norm_num
  · -- n = 2
    rw [countOfWeight_faultfreeHeight2_two]
    norm_num
  · -- n ≥ 3
    have hn1 : n + 3 ≠ 1 := by omega
    have hn2 : n + 3 ≠ 2 := by omega
    have h3 : FaultfreeTilingsHeight2.countOfWeight faultfreeTilingsHeight2_isFiniteType (n + 3) = 0 :=
      countOfWeight_faultfreeHeight2_eq_zero (n + 3) hn1 hn2
    simp [h3, hn2]

/-! #### Decomposition Lemma (lem.gf.weighted-set.domino.fd) -/

/-! #### Helper definitions for tiling composition/decomposition -/

/-- Shift a domino horizontally by an offset -/
def Domino.shift (d : Domino) (offset : ℤ) : Domino :=
  match d with
  | .horizontal i j => .horizontal (i + offset) j
  | .vertical i j => .vertical (i + offset) j

/-- Shifting preserves the shape structure -/
theorem Domino.shift_toShape (d : Domino) (offset : ℤ) :
    (d.shift offset).toShape = d.toShape.image (fun p => (p.1 + offset, p.2)) := by
  cases d with
  | horizontal i j =>
    simp only [shift, toShape, Set.image_insert_eq, Set.image_singleton]
    ext ⟨x, y⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · left; omega
      · right; omega
    · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
      · left; omega
      · right; omega
  | vertical i j =>
    simp only [shift, toShape, Set.image_insert_eq, Set.image_singleton]

/-- Shift a set of dominos -/
def shiftDominos (ds : Set Domino) (offset : ℤ) : Set Domino :=
  ds.image (fun d => d.shift offset)

/-- Shifting is injective -/
theorem Domino.shift_injective (offset : ℤ) : Function.Injective (fun d : Domino => d.shift offset) := by
  intro d1 d2 h
  cases d1 <;> cases d2 <;> simp only [shift, Domino.horizontal.injEq, Domino.vertical.injEq] at h ⊢
  · omega
  · contradiction
  · contradiction
  · omega

/-- Shifting by 0 is the identity -/
@[simp]
theorem Domino.shift_zero (d : Domino) : d.shift 0 = d := by
  cases d <;> simp [shift]

/-- Shifting twice is the same as shifting by the sum -/
theorem Domino.shift_shift (d : Domino) (a b : ℤ) : (d.shift a).shift b = d.shift (a + b) := by
  cases d <;> simp [shift, add_assoc]

/-- Rectangle shift lemma -/
theorem Rectangle_shift (n m : ℕ) (offset : ℤ) :
    (Rectangle n m).image (fun p => (p.1 + offset, p.2)) = 
    {p : ℤ × ℤ | 1 + offset ≤ p.1 ∧ p.1 ≤ n + offset ∧ 1 ≤ p.2 ∧ p.2 ≤ m} := by
  ext ⟨x, y⟩
  simp only [Set.mem_image, Rectangle, Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x', y'⟩, ⟨h1, h2, h3, h4⟩, hx, hy⟩
    subst hx hy
    exact ⟨by omega, by omega, h3, h4⟩
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨(x - offset, y), ⟨by omega, by omega, h3, h4⟩, by omega, rfl⟩

/-- Shift a tiling to a new position -/
def Tiling.shift {n m : ℕ} (T : Tiling (Rectangle n m)) (offset : ℤ) :
    Tiling {p : ℤ × ℤ | 1 + offset ≤ p.1 ∧ p.1 ≤ n + offset ∧ 1 ≤ p.2 ∧ p.2 ≤ m} where
  dominos := shiftDominos T.dominos offset
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [shiftDominos, Set.mem_image] at hd1 hd2
    obtain ⟨d1', hd1', rfl⟩ := hd1
    obtain ⟨d2', hd2', rfl⟩ := hd2
    have hne' : d1' ≠ d2' := by
      intro heq; subst heq; exact hne rfl
    have hdisj := T.pairwise_disjoint hd1' hd2' hne'
    simp only [Function.onFun, Domino.shift_toShape]
    exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
      simp only [Prod.mk.injEq] at h
      ext <;> omega) hdisj
  cover := by
    have hcover := T.cover
    have heq : (Rectangle n m).image (fun p => (p.1 + offset, p.2)) = 
        {p : ℤ × ℤ | 1 + offset ≤ p.1 ∧ p.1 ≤ n + offset ∧ 1 ≤ p.2 ∧ p.2 ≤ m} := 
      Rectangle_shift n m offset
    rw [← heq]
    ext p
    simp only [Set.mem_iUnion, Set.mem_image, shiftDominos, exists_prop]
    constructor
    · rintro ⟨d, ⟨d', hd', rfl⟩, hp⟩
      rw [Domino.shift_toShape] at hp
      obtain ⟨p', hp', rfl⟩ := hp
      have hp'_rect : p' ∈ Rectangle n m := by
        rw [← hcover]
        exact Set.mem_biUnion hd' hp'
      exact ⟨p', hp'_rect, rfl⟩
    · rintro ⟨p', hp', rfl⟩
      rw [← hcover] at hp'
      simp only [Set.mem_iUnion, exists_prop] at hp'
      obtain ⟨d', hd', hp''⟩ := hp'
      refine ⟨d'.shift offset, ⟨d', hd', rfl⟩, ?_⟩
      rw [Domino.shift_toShape]
      exact ⟨p', hp'', rfl⟩

/-- The tiling of the empty rectangle (width 0) -/
def emptyTiling2 : Tiling (Rectangle 0 2) := by
  rw [Rectangle_zero_left]
  exact Tiling.empty

/-- Cast a tiling along rectangle equality -/
def Tiling.cast {S S' : Shape} (h : S = S') (T : Tiling S) : Tiling S' where
  dominos := T.dominos
  pairwise_disjoint := T.pairwise_disjoint
  cover := by rw [← h]; exact T.cover

/-- Casting a tiling preserves its dominos -/
@[simp]
theorem Tiling.cast_dominos {S S' : Shape} (h : S = S') (T : Tiling S) :
    (T.cast h).dominos = T.dominos := rfl

/-- Subst (▸) on a tiling preserves dominos -/
@[simp]
theorem Tiling.subst_dominos {n m : ℕ} (h : n = m) (T : Tiling (Rectangle n 2)) :
    (h ▸ T).dominos = T.dominos := by
  subst h
  rfl

/-! #### Composition: Concatenating faultfree tilings -/

/-- The partial sum of widths up to (but not including) index i -/
def partialWidthSum (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) : ℕ :=
  ∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1

/-- The partial width sum at index with val = 0 is always 0 -/
@[simp]
theorem partialWidthSum_zero (k : ℕ)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) (hi : i.val = 0) :
    partialWidthSum k ts i = 0 := by
  simp only [partialWidthSum]
  have hempty : (Finset.univ : Finset (Fin i.val)) = ∅ := by rw [hi]; rfl
  simp [hempty]

/-- Shift a domino by a natural number offset (for composition) -/
def Domino.shiftNat (d : Domino) (offset : ℕ) : Domino :=
  d.shift (offset : ℤ)

/-- Shifting by natural 0 is the identity -/
@[simp]
theorem Domino.shiftNat_zero (d : Domino) : d.shiftNat 0 = d := by
  simp [shiftNat, shift_zero]

/-- Shifting by natural number preserves shape structure -/
theorem Domino.shiftNat_toShape (d : Domino) (offset : ℕ) :
    (d.shiftNat offset).toShape = d.toShape.image (fun p => (p.1 + (offset : ℤ), p.2)) :=
  d.shift_toShape offset

/-- Shifting twice by natural numbers is the same as shifting by the sum -/
theorem Domino.shiftNat_shiftNat (d : Domino) (a b : ℕ) : 
    (d.shiftNat a).shiftNat b = d.shiftNat (a + b) := by
  simp only [shiftNat, shift_shift, Nat.cast_add]

/-- The set of dominos for the i-th component in the composition, shifted appropriately -/
def composeTilings_component_dominos (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) : Set Domino :=
  (ts i).2.val.dominos.image (fun d => d.shiftNat (partialWidthSum k ts i))

/-- The union of all shifted dominos for composition -/
def composeTilings_dominos (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) : Set Domino :=
  ⋃ i : Fin k, composeTilings_component_dominos k ts i

/-- X-coordinate bounds for a shifted domino from a component -/
private lemma shifted_domino_x_in_range' {n : ℕ} {T : Tiling (Rectangle n 2)} {d : Domino}
    (hd : d ∈ T.dominos) (offset : ℕ) (p : ℤ × ℤ) (hp : p ∈ (d.shiftNat offset).toShape) :
    1 + (offset : ℤ) ≤ p.1 ∧ p.1 ≤ n + (offset : ℤ) := by
  rw [Domino.shiftNat_toShape] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  have hsub := domino_subset_rect n T d hd hp'
  simp only [Rectangle, Set.mem_ofPred_eq] at hsub
  simp only
  constructor <;> linarith

/-- Helper lemma for finding which component a point belongs to based on its x-coordinate.
    Given k components with widths, finds the unique component containing position x. -/
private lemma find_component_index (k : ℕ) (widths : Fin k → ℕ) (x : ℕ) (hx : x < ∑ i, widths i) :
    ∃ i : Fin k, (∑ j : Fin i.val, widths ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) ≤ x ∧ 
                 x < (∑ j : Fin i.val, widths ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) + widths i := by
  induction k with
  | zero => 
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hx
    omega
  | succ k ih =>
    by_cases h : x < ∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    · have ih' := ih (fun i => widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) h
      obtain ⟨i, hi1, hi2⟩ := ih'
      exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi1, hi2⟩
    · push Not at h
      have hsum : ∑ i : Fin (k + 1), widths i = 
          (∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + widths ⟨k, Nat.lt_succ_self k⟩ := by
        rw [Fin.sum_univ_castSucc]
        rfl
      have hx' : x < (∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + widths ⟨k, Nat.lt_succ_self k⟩ := by
        calc x < ∑ i : Fin (k + 1), widths i := hx
          _ = _ := hsum
      exact ⟨⟨k, Nat.lt_succ_self k⟩, h, hx'⟩

/-- Key lemma: partial width sums are monotonic -/
private lemma partialWidthSum_add_le (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i1 i2 : Fin k) (h : i1 < i2) :
    partialWidthSum k ts i1 + (ts i1).1 ≤ partialWidthSum k ts i2 := by
  simp only [partialWidthSum]
  have hi : i1.val < i2.val := h
  have hle : i1.val + 1 ≤ i2.val := hi
  have hk : i1.val + 1 < k := Nat.lt_of_le_of_lt hi i2.isLt
  have hinj : Function.Injective (Fin.castLE hle) := Fin.castLE_injective hle
  have step1 : (∑ j : Fin i1.val, (ts ⟨j.val, Nat.lt_trans j.isLt i1.isLt⟩).1) + (ts i1).1 = 
               ∑ j : Fin (i1.val + 1), (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1 := by
    have heq := Fin.sum_univ_castSucc (fun j : Fin (i1.val + 1) => (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1)
    simp only [Fin.last, Fin.val_mk, Fin.val_castSucc] at heq
    linarith [heq]
  calc (∑ j : Fin i1.val, (ts ⟨j.val, Nat.lt_trans j.isLt i1.isLt⟩).1) + (ts i1).1
      = ∑ j : Fin (i1.val + 1), (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1 := step1
    _ = ∑ j : Fin (i1.val + 1), (ts ⟨(Fin.castLE hle j).val, Nat.lt_trans (Fin.castLE hle j).isLt i2.isLt⟩).1 := by
          apply Finset.sum_congr rfl; intro x _; simp [Fin.castLE]
    _ = ∑ j ∈ (Finset.univ : Finset (Fin (i1.val + 1))).map ⟨Fin.castLE hle, hinj⟩, 
          (ts ⟨j.val, Nat.lt_trans j.isLt i2.isLt⟩).1 := by
          rw [Finset.sum_map]; simp
    _ ≤ ∑ j : Fin i2.val, (ts ⟨j.val, Nat.lt_trans j.isLt i2.isLt⟩).1 := by
          apply Finset.sum_le_univ_sum_of_nonneg; intro _; exact Nat.zero_le _

/-- Helper: Dominos from different components have disjoint x-coordinate ranges -/
theorem composeTilings_component_dominos_disjoint (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i1 i2 : Fin k) (hi : i1 ≠ i2)
    (d1 : Domino) (hd1 : d1 ∈ composeTilings_component_dominos k ts i1)
    (d2 : Domino) (hd2 : d2 ∈ composeTilings_component_dominos k ts i2) :
    Disjoint d1.toShape d2.toShape := by
  -- Get the original dominos
  simp only [composeTilings_component_dominos, Set.mem_image] at hd1 hd2
  obtain ⟨d1', hd1', rfl⟩ := hd1
  obtain ⟨d2', hd2', rfl⟩ := hd2
  -- WLOG i1 < i2
  wlog h : i1 < i2 generalizing i1 i2 d1' d2' with H
  · have h' : i2 < i1 := (lt_or_gt_of_ne hi).resolve_left h
    exact (H i2 i1 (Ne.symm hi) d2' hd2' d1' hd1' h').symm
  -- Key: partialWidthSum i1 + (ts i1).1 ≤ partialWidthSum i2
  have key : partialWidthSum k ts i1 + (ts i1).1 ≤ partialWidthSum k ts i2 := 
    partialWidthSum_add_le k ts i1 i2 h
  -- Prove disjointness using x-coordinate separation
  rw [Set.disjoint_iff]
  intro p ⟨hp1, hp2⟩
  have hx1 := shifted_domino_x_in_range' hd1' (partialWidthSum k ts i1) p hp1
  have hx2 := shifted_domino_x_in_range' hd2' (partialWidthSum k ts i2) p hp2
  have h1 : p.1 ≤ (ts i1).1 + partialWidthSum k ts i1 := hx1.2
  have h2 : 1 + partialWidthSum k ts i2 ≤ p.1 := hx2.1
  have h3 : (ts i1).1 + partialWidthSum k ts i1 < 1 + partialWidthSum k ts i2 := by
    calc (ts i1).1 + partialWidthSum k ts i1 
        = partialWidthSum k ts i1 + (ts i1).1 := by ring
      _ ≤ partialWidthSum k ts i2 := key
      _ < 1 + partialWidthSum k ts i2 := by omega
  linarith

/-- The partial width sum at i plus width of component i gives the next partial sum -/
private lemma partialWidthSum_succ (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) (hi : i.val + 1 < k) :
    partialWidthSum k ts ⟨i.val + 1, hi⟩ = partialWidthSum k ts i + (ts i).1 := by
  simp only [partialWidthSum]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.last, Fin.val_mk, Fin.val_castSucc, add_comm]

/-- For any point p in the rectangle of total width, there exists a component i such that
    partialWidthSum k ts i < p.1 ≤ partialWidthSum k ts i + (ts i).1 -/
private lemma point_in_some_component (k : ℕ) (_hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (p : ℤ × ℤ) (hp : p ∈ Rectangle (∑ i : Fin k, (ts i).1) 2) :
    ∃ i : Fin k, (partialWidthSum k ts i : ℤ) < p.1 ∧ 
                  p.1 ≤ partialWidthSum k ts i + (ts i).1 := by
  simp only [Rectangle, Set.mem_ofPred_eq] at hp
  have hp1_pos : p.1 ≥ 1 := hp.1
  have hp1_le : p.1 ≤ ∑ i : Fin k, (ts i).1 := hp.2.1
  -- p.1 - 1 is in range [0, totalWidth - 1]
  have hp1_nat : (p.1 - 1).toNat < ∑ i : Fin k, (ts i).1 := by omega
  -- Find the component using find_component_index
  obtain ⟨i, hi_lo, hi_hi⟩ := find_component_index k (fun j => (ts j).1) (p.1 - 1).toNat hp1_nat
  refine ⟨i, ?_, ?_⟩
  · -- partialWidthSum k ts i < p.1
    simp only [partialWidthSum]
    have h : (∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1 : ℤ) ≤ (p.1 - 1).toNat := by
      exact_mod_cast hi_lo
    omega
  · -- p.1 ≤ partialWidthSum k ts i + (ts i).1
    simp only [partialWidthSum]
    have h : ((p.1 - 1).toNat : ℤ) < ∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1 + (ts i).1 := by
      exact_mod_cast hi_hi
    omega

set_option backward.isDefEq.respectTransparency false in
/-- The composition function: given a tuple of faultfree tilings, concatenate them
    horizontally to produce a single tiling.
    
    Each faultfree tiling is shifted by the cumulative width of the previous tilings,
    and the union of all shifted dominos forms the composed tiling.
    
    This is the inverse of decomposeTiling. -/
def composeTilings (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    Σ n : ℕ, Tiling (Rectangle n 2) :=
  let totalWidth := ∑ i : Fin k, (ts i).1
  ⟨totalWidth, {
    dominos := composeTilings_dominos k ts
    pairwise_disjoint := by
      intro d1 hd1 d2 hd2 hne
      simp only [composeTilings_dominos, Set.mem_iUnion] at hd1 hd2
      obtain ⟨i1, hi1⟩ := hd1
      obtain ⟨i2, hi2⟩ := hd2
      simp only [composeTilings_component_dominos, Set.mem_image] at hi1 hi2
      obtain ⟨d1', hd1', rfl⟩ := hi1
      obtain ⟨d2', hd2', rfl⟩ := hi2
      -- The shifted dominos are disjoint either because they come from the same component
      -- (and the original dominos are disjoint) or from different components (different x-ranges)
      by_cases heq : i1 = i2
      · -- Same component: use original pairwise disjointness
        subst heq
        have hne' : d1' ≠ d2' := by
          intro h
          subst h
          exact hne rfl
        have hdisj := (ts i1).2.val.pairwise_disjoint hd1' hd2' hne'
        simp only [Function.onFun, Domino.shiftNat_toShape]
        exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
          simp only [Prod.mk.injEq] at h
          ext <;> omega) hdisj
      · -- Different components: disjoint x-ranges
        simp only [Function.onFun]
        exact composeTilings_component_dominos_disjoint k ts i1 i2 heq 
          (d1'.shiftNat (partialWidthSum k ts i1)) 
          (Set.mem_image_of_mem _ hd1')
          (d2'.shiftNat (partialWidthSum k ts i2)) 
          (Set.mem_image_of_mem _ hd2')
    cover := by
        -- The union of shifted dominos covers the rectangle of total width
        -- This follows from each component covering its portion of the rectangle
        ext ⟨x, y⟩
        simp only [Set.mem_iUnion, Rectangle, Set.mem_ofPred_eq]
        constructor
        · -- ⊆ direction: any point in a shifted domino is in the total rectangle
          rintro ⟨d, hd, hp⟩
          simp only [composeTilings_dominos, Set.mem_iUnion] at hd
          obtain ⟨i, hi⟩ := hd
          simp only [composeTilings_component_dominos, Set.mem_image] at hi
          obtain ⟨d', hd', rfl⟩ := hi
          -- Get x-coordinate bounds from shifted_domino_x_in_range'
          have hx := shifted_domino_x_in_range' hd' (partialWidthSum k ts i) (x, y) hp
          -- Get y-coordinate bounds from the original domino
          rw [Domino.shiftNat_toShape] at hp
          obtain ⟨⟨x', y'⟩, hp', heq⟩ := hp
          simp only [Prod.mk.injEq] at heq
          have hd'_rect := domino_subset_rect (ts i).1 (ts i).2.val d' hd' hp'
          simp only [Rectangle, Set.mem_ofPred_eq] at hd'_rect
          -- Bound for x: need partialWidthSum + (ts i).1 ≤ totalWidth
          have hbound : partialWidthSum k ts i + (ts i).1 ≤ ∑ j : Fin k, (ts j).1 := by
            simp only [partialWidthSum]
            have hsub : Finset.univ.map (Fin.castLEEmb i.isLt) ⊆ Finset.univ := 
              fun x _ => Finset.mem_univ x
            have h3 := Finset.sum_le_sum_of_subset (f := fun j => (ts j).1) hsub
            have h4 : ∑ j ∈ Finset.univ.map (Fin.castLEEmb i.isLt), (ts j).1 = 
                      ∑ j : Fin (i.val + 1), (ts ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.isLt⟩).1 := by
              rw [Finset.sum_map]
              apply Finset.sum_congr rfl
              intro j _
              rfl
            have h5 : (∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1) + (ts i).1 = 
                      ∑ j : Fin (i.val + 1), (ts ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.isLt⟩).1 := by
              rw [Fin.sum_univ_castSucc]
              simp only [Fin.val_castSucc, Fin.val_last]
            calc (∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1) + (ts i).1
                = ∑ j : Fin (i.val + 1), (ts ⟨j.val, Nat.lt_of_lt_of_le j.isLt i.isLt⟩).1 := h5
              _ = ∑ j ∈ Finset.univ.map (Fin.castLEEmb i.isLt), (ts j).1 := h4.symm
              _ ≤ ∑ j : Fin k, (ts j).1 := h3
          constructor
          · -- 1 ≤ x
            have : 1 + (partialWidthSum k ts i : ℤ) ≤ x := hx.1
            omega
          constructor
          · -- x ≤ totalWidth
            have : x ≤ (ts i).1 + (partialWidthSum k ts i : ℤ) := hx.2
            have : (partialWidthSum k ts i : ℤ) + (ts i).1 ≤ ∑ j : Fin k, (ts j).1 := by
              exact_mod_cast hbound
            omega
          constructor
          · -- 1 ≤ y
            have hy_eq : y = y' := heq.2.symm
            omega
          · -- y ≤ 2
            have hy_eq : y = y' := heq.2.symm
            omega
        · -- ⊇ direction: any point in the rectangle is covered by some shifted domino
          intro ⟨hx1, hx2, hy1, hy2⟩
          -- Handle k = 0 case: rectangle is empty
          by_cases hk : k = 0
          · subst hk
            simp at hx2
            omega
          · -- k ≥ 1: use point_in_some_component
            have hk' : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
            have hp_rect : (x, y) ∈ Rectangle (∑ i : Fin k, (ts i).1) 2 := by
              simp only [Rectangle, Set.mem_ofPred_eq]
              exact ⟨hx1, hx2, hy1, hy2⟩
            obtain ⟨i, hi_lo, hi_hi⟩ := point_in_some_component k hk' ts (x, y) hp_rect
            -- The unshifted point (x - partialWidthSum, y) is in component i's rectangle
            have hp'_rect : (x - partialWidthSum k ts i, y) ∈ Rectangle (ts i).1 2 := by
              simp only [Rectangle, Set.mem_ofPred_eq]
              constructor
              · omega
              constructor
              · omega
              exact ⟨hy1, hy2⟩
            -- By component's cover property, this point is covered by some domino d'
            rw [← (ts i).2.val.cover] at hp'_rect
            simp only [Set.mem_iUnion] at hp'_rect
            obtain ⟨d', hd', hp'⟩ := hp'_rect
            -- The shifted domino d'.shiftNat (partialWidthSum k ts i) covers (x, y)
            refine ⟨d'.shiftNat (partialWidthSum k ts i), ?_, ?_⟩
            · -- Show the shifted domino is in composeTilings_dominos
              simp only [composeTilings_dominos, composeTilings_component_dominos, 
                         Set.mem_iUnion, Set.mem_image]
              exact ⟨i, d', hd', rfl⟩
            · rw [Domino.shiftNat_toShape]
              refine ⟨(x - partialWidthSum k ts i, y), hp', ?_⟩
              simp only [Prod.mk.injEq]
              constructor
              · omega
              · trivial
    }⟩

/-- For k = 1, the composed dominos equal the original dominos (shifted by 0) -/
theorem composeTilings_dominos_one 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    composeTilings_dominos 1 ts = (ts 0).2.val.dominos := by
  simp only [composeTilings_dominos, composeTilings_component_dominos]
  -- Union over Fin 1 is just the single element
  ext d
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨i, d', hd', rfl⟩
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    have h0 : (0 : Fin 1).val = 0 := rfl
    simp only [partialWidthSum_zero 1 ts 0 h0, Domino.shiftNat_zero]
    exact hd'
  · intro hd
    refine ⟨0, d, hd, ?_⟩
    have h0 : (0 : Fin 1).val = 0 := rfl
    simp only [partialWidthSum_zero 1 ts 0 h0, Domino.shiftNat_zero]

/-- For k = 1, the composed tiling has the same dominos as the original -/
theorem composeTilings_one_dominos 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings 1 ts).2.dominos = (ts 0).2.val.dominos := by
  simp only [composeTilings]
  exact composeTilings_dominos_one ts

/-- For k = 1, the width of the composed tiling equals the width of the single component -/
theorem composeTilings_one_width 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings 1 ts).1 = (ts 0).1 := by
  simp only [composeTilings, Finset.univ_unique, Finset.sum_singleton]
  rfl

/-- For k = 1, the composed tiling equals the single component (as Tilings) -/
theorem composeTilings_one_tiling 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings 1 ts).2 = (ts 0).2.val := by
  apply Tiling.ext
  exact composeTilings_one_dominos ts

/-- For k = 1, the composed tiling is faultfree -/
theorem composeTilings_one_isFaultfree 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    isFaultfree (composeTilings 1 ts).1 (composeTilings 1 ts).2 := by
  have h := (ts 0).2.property
  -- The width is (ts 0).1 and the tiling has the same dominos as (ts 0).2.val
  -- Since (ts 0).2.val is faultfree, so is the composed tiling
  constructor
  · -- Positive width
    have hpos : (ts 0).1 > 0 := h.1
    simp only [composeTilings, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
    exact hpos
  · -- No faults
    intro k hfault
    have hno_fault := h.2 k
    apply hno_fault
    rw [hasFault_eq_of_dominos_eq (composeTilings_one_dominos ts).symm]
    simp only [composeTilings] at hfault ⊢
    exact hfault

set_option backward.isDefEq.respectTransparency false in
/-- Helper lemma: The width of composeTilings with a prepended element equals
    the first width plus the sum of the remaining widths.
    This is used in proving composeTilings_decomposeTiling. -/
theorem composeTilings_prepend_width (m : ℕ) (first_width : ℕ)
    (first : {T' : Tiling (Rectangle first_width 2) // isFaultfree first_width T'})
    (rest : Fin m → (Σ w : ℕ, {T' : Tiling (Rectangle w 2) // isFaultfree w T'}))
    (ts : Fin (m + 1) → (Σ w : ℕ, {T' : Tiling (Rectangle w 2) // isFaultfree w T'}))
    (hts : ts = fun i => if hi : i.val = 0 then ⟨first_width, first⟩ else rest ⟨i.val - 1, by omega⟩) :
    (composeTilings (m + 1) ts).1 = first_width + ∑ j : Fin m, (rest j).1 := by
  simp only [composeTilings, hts]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, dite_true, Fin.val_succ, Nat.add_one_ne_zero, dite_false,
             Nat.add_sub_cancel]
/-- Helper lemma: When we compose with a prepended element, if the rest composes to 
    a specific width and tiling, then the total width equals first_width + rest_width. -/
theorem composeTilings_prepend_width' (m : ℕ) (first_width rest_width : ℕ)
    (first : {T' : Tiling (Rectangle first_width 2) // isFaultfree first_width T'})
    (rest : Fin m → (Σ w : ℕ, {T' : Tiling (Rectangle w 2) // isFaultfree w T'}))
    (hrest : (composeTilings m rest).1 = rest_width)
    (ts : Fin (m + 1) → (Σ w : ℕ, {T' : Tiling (Rectangle w 2) // isFaultfree w T'}))
    (hts : ts = fun i => if hi : i.val = 0 then ⟨first_width, first⟩ else rest ⟨i.val - 1, by omega⟩) :
    (composeTilings (m + 1) ts).1 = first_width + rest_width := by
  rw [composeTilings_prepend_width m first_width first rest ts hts]
  simp only [composeTilings] at hrest
  rw [hrest]

/-! #### Decomposition: Cutting at faults -/

/-! ##### Infrastructure for restricting tilings at faults -/

/-- Shift a domino by a negative offset (for decomposition) -/
def Domino.shiftNeg (d : Domino) (offset : ℕ) : Domino :=
  d.shift (-(offset : ℤ))

/-- Shifting by negative offset preserves shape structure -/
theorem Domino.shiftNeg_toShape (d : Domino) (offset : ℕ) :
    (d.shiftNeg offset).toShape = d.toShape.image (fun p => (p.1 - (offset : ℤ), p.2)) := by
  simp only [shiftNeg, shift_toShape]
  ext ⟨x, y⟩
  simp only [Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x', y'⟩, hp, hx, hy⟩
    exact ⟨⟨x', y'⟩, hp, by omega, hy⟩
  · rintro ⟨⟨x', y'⟩, hp, hx, hy⟩
    exact ⟨⟨x', y'⟩, hp, by omega, hy⟩

/-- Shifting by k then by -k returns the original domino -/
theorem Domino.shiftNeg_shiftNat (d : Domino) (k : ℕ) : (d.shiftNat k).shiftNeg k = d := by
  cases d <;> simp [shiftNat, shiftNeg, shift]

/-- Shifting by -k then by k returns the original domino -/
theorem Domino.shiftNat_shiftNeg (d : Domino) (k : ℕ) : (d.shiftNeg k).shiftNat k = d := by
  cases d <;> simp [shiftNat, shiftNeg, shift]

/-- A domino is in the left part (all x-coordinates ≤ k) -/
def Domino.inLeftPart (d : Domino) (k : ℕ) : Prop :=
  ∀ p ∈ d.toShape, p.1 ≤ k

/-- A domino is in the right part (all x-coordinates ≥ k+1) -/
def Domino.inRightPart (d : Domino) (k : ℕ) : Prop :=
  ∀ p ∈ d.toShape, p.1 ≥ k + 1

/-- At a fault, each domino is either entirely left or entirely right -/
theorem domino_left_or_right_at_fault {n : ℕ} {T : Tiling (Rectangle n 2)} {k : ℕ}
    (hk : hasFault n T k) (d : Domino) (hd : d ∈ T.dominos) :
    d.inLeftPart k ∨ d.inRightPart k := by
  cases d with
  | horizontal i j =>
    have hfault := hk.2.2 (Domino.horizontal i j) hd
    simp only [Domino.inLeftPart, Domino.inRightPart, Domino.toShape]
    rcases hfault with hlt | hge
    · left
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega
    · right
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega
  | vertical i j =>
    simp only [Domino.inLeftPart, Domino.inRightPart, Domino.toShape]
    -- Get x-coordinate bound from the domino being in the tiling
    have hsub := domino_subset_rect n T (Domino.vertical i j) hd
    have h1 : (i, j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
    simp only [Rectangle, Set.mem_ofPred_eq] at h1
    by_cases hi : i ≤ k
    · left
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega
    · right
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp <;> omega

/-- Restrict a tiling to the left part at a fault position -/
def restrictTilingLeft (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) : Tiling (Rectangle k 2) where
  dominos := {d ∈ T.dominos | d.inLeftPart k}
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_sep_iff] at hd1 hd2
    exact T.pairwise_disjoint hd1.1 hd2.1 hne
  cover := by
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, ⟨hd, hleft⟩, hp⟩
      have hdomain := T.cover ▸ Set.mem_biUnion hd hp
      simp only [Rectangle, Set.mem_ofPred_eq] at hdomain
      exact ⟨hdomain.1, hleft (x, y) hp, hdomain.2.2.1, hdomain.2.2.2⟩
    · intro ⟨h1, h2, h3, h4⟩
      have hk_lt_n : (k : ℤ) < n := by exact_mod_cast hk.2.1
      have hxy : (x, y) ∈ Rectangle n 2 := by
        simp only [Rectangle, Set.mem_ofPred_eq]
        exact ⟨h1, by omega, h3, h4⟩
      rw [← T.cover] at hxy
      simp only [Set.mem_iUnion] at hxy
      obtain ⟨d, hd, hp⟩ := hxy
      have hlr := domino_left_or_right_at_fault hk d hd
      rcases hlr with hleft | hright
      · exact ⟨d, ⟨hd, hleft⟩, hp⟩
      · -- Contradiction: d is in right part but covers (x, y) with x ≤ k
        exfalso
        have hge := hright (x, y) hp
        omega

/-- Restrict a tiling to the right part at a fault position, shifted to origin -/
def restrictTilingRight (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) : Tiling (Rectangle (n - k) 2) where
  dominos := ({d ∈ T.dominos | d.inRightPart k}).image (fun d => d.shiftNeg k)
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_image, Set.mem_sep_iff] at hd1 hd2
    obtain ⟨d1', ⟨hd1'_mem, _⟩, rfl⟩ := hd1
    obtain ⟨d2', ⟨hd2'_mem, _⟩, rfl⟩ := hd2
    have hne' : d1' ≠ d2' := by intro heq; subst heq; exact hne rfl
    have hdisj := T.pairwise_disjoint hd1'_mem hd2'_mem hne'
    simp only [Function.onFun, Domino.shiftNeg_toShape]
    exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
      simp only [Prod.mk.injEq] at h; ext <;> omega) hdisj
  cover := by
      ext ⟨x, y⟩
      simp only [Set.mem_iUnion, Set.mem_image, Rectangle, Set.mem_ofPred_eq]
      constructor
      · intro ⟨d, hd_img, hp⟩
        obtain ⟨d', ⟨hd', hright⟩, hd_eq⟩ := hd_img
        rw [← hd_eq, Domino.shiftNeg_toShape] at hp
        obtain ⟨p', hp', hp_eq⟩ := hp
        simp only [Prod.mk.injEq] at hp_eq
        have hdomain := T.cover ▸ Set.mem_biUnion hd' hp'
        simp only [Rectangle, Set.mem_ofPred_eq] at hdomain
        have hx : p'.1 ≥ k + 1 := hright p' hp'
        have hy : y = p'.2 := hp_eq.2.symm
        constructor
        · omega
        constructor
        · have hk_le_n : (k : ℤ) ≤ n := by exact_mod_cast Nat.le_of_lt hk.2.1
          omega
        constructor
        · rw [hy]; exact hdomain.2.2.1
        · rw [hy]; exact hdomain.2.2.2
      · intro ⟨h1, h2, h3, h4⟩
        have hk_lt_n : (k : ℤ) < n := by exact_mod_cast hk.2.1
        have hxy : ((x + k : ℤ), y) ∈ Rectangle n 2 := by
          simp only [Rectangle, Set.mem_ofPred_eq]
          exact ⟨by omega, by omega, h3, h4⟩
        rw [← T.cover] at hxy
        simp only [Set.mem_iUnion] at hxy
        obtain ⟨d, hd, hp⟩ := hxy
        have hlr := domino_left_or_right_at_fault hk d hd
        rcases hlr with hleft | hright
        · -- Contradiction: d is in left part but covers (x + k, y) with x ≥ 1
          exfalso
          have hle := hleft ((x + k : ℤ), y) hp
          omega
        · refine ⟨d.shiftNeg k, ⟨d, ⟨hd, hright⟩, rfl⟩, ?_⟩
          rw [Domino.shiftNeg_toShape]
          refine ⟨((x + k : ℤ), y), hp, ?_⟩
          simp only [add_sub_cancel_right]

/-- `restrictTilingLeft` does not depend on the proof of `hasFault` -/
@[simp]
theorem restrictTilingLeft_proof_irrel (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk1 hk2 : hasFault n T k) : 
    restrictTilingLeft n T k hk1 = restrictTilingLeft n T k hk2 := rfl

/-- `restrictTilingRight` does not depend on the proof of `hasFault` -/
@[simp]
theorem restrictTilingRight_proof_irrel (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk1 hk2 : hasFault n T k) : 
    restrictTilingRight n T k hk1 = restrictTilingRight n T k hk2 := rfl

/-- The left restriction at a fault is faultfree if k is the smallest fault -/
theorem restrictTilingLeft_isFaultfree (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) (hmin : ∀ j, j < k → ¬hasFault n T j) : 
    isFaultfree k (restrictTilingLeft n T k hk) := by
  constructor
  · exact hk.1
  · intro j hfault_restr
    -- We need to show False (i.e., no fault at j in the restricted tiling)
    -- A fault at j in the restricted tiling would imply a fault at j in T
    -- But j < k and hmin says there's no fault at j in T
    have hj_lt : j < k := hfault_restr.2.1
    have hj_lt_n : j < n := Nat.lt_trans hj_lt hk.2.1
    have hfault_T : hasFault n T j := by
      refine ⟨hfault_restr.1, hj_lt_n, ?_⟩
      intro d hd
      cases d with
      | horizontal i jj =>
        -- If d is in T.dominos, it's either in left part or right part
        have hlr := domino_left_or_right_at_fault hk (Domino.horizontal i jj) hd
        rcases hlr with hleft | hright
        · -- d is in left part, so it's in the restricted tiling
          have hd_restr : Domino.horizontal i jj ∈ (restrictTilingLeft n T k hk).dominos := by
            simp only [restrictTilingLeft, Set.mem_sep_iff]
            exact ⟨hd, hleft⟩
          exact hfault_restr.2.2 (Domino.horizontal i jj) hd_restr
        · -- d is in right part (x ≥ k+1), so i ≥ k+1 > j, hence i ≥ j+1
          simp only [Domino.inRightPart, Domino.toShape] at hright
          have hi := hright (i, jj) (by simp)
          have hj_lt_k : (j : ℤ) < k := by exact_mod_cast hj_lt
          right
          -- Need to show i ≥ j + 1
          -- We have hi : i ≥ k + 1 and hj_lt : j < k
          -- So i ≥ k + 1 > k > j, hence i ≥ j + 1
          omega
      | vertical _ _ => trivial
    exact hmin j hj_lt hfault_T

/-- At a fault position, the tiling's dominos split into left and right parts -/
theorem dominos_eq_leftPart_union_rightPart (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) : 
    T.dominos = {d ∈ T.dominos | d.inLeftPart k} ∪ {d ∈ T.dominos | d.inRightPart k} := by
  ext d
  simp only [Set.mem_union, Set.mem_sep_iff]
  constructor
  · intro hd
    rcases domino_left_or_right_at_fault hk d hd with hleft | hright
    · left; exact ⟨hd, hleft⟩
    · right; exact ⟨hd, hright⟩
  · intro hd
    rcases hd with ⟨hd, _⟩ | ⟨hd, _⟩ <;> exact hd

/-- The original dominos equal the union of left part and shifted right part -/
theorem dominos_eq_left_union_shifted_right (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) : 
    T.dominos = (restrictTilingLeft n T k hk).dominos ∪ 
                ((restrictTilingRight n T k hk).dominos.image (fun d => d.shiftNat k)) := by
  ext d
  simp only [Set.mem_union, Set.mem_image]
  simp only [restrictTilingLeft, restrictTilingRight, Set.mem_sep_iff, Set.mem_image]
  constructor
  · intro hd
    rcases domino_left_or_right_at_fault hk d hd with hleft | hright
    · left; exact ⟨hd, hleft⟩
    · right
      -- d is in right part, so d.shiftNeg k is in restrictTilingRight
      -- and (d.shiftNeg k).shiftNat k = d
      refine ⟨d.shiftNeg k, ⟨d, ⟨hd, hright⟩, rfl⟩, ?_⟩
      exact d.shiftNat_shiftNeg k
  · intro hd
    rcases hd with ⟨hd, _⟩ | ⟨d', ⟨d'', ⟨hd'', _⟩, hd'_eq⟩, hd_eq⟩
    · exact hd
    · -- d = d'.shiftNat k where d' = d''.shiftNeg k and d'' ∈ T.dominos
      subst hd'_eq hd_eq
      rw [Domino.shiftNat_shiftNeg]
      exact hd''

/-- The set of fault positions in a tiling -/
def faultPositions (n : ℕ) (T : Tiling (Rectangle n 2)) : Set ℕ :=
  {k | hasFault n T k}

/-- The fault positions form a finite set (bounded by n) -/
theorem faultPositions_finite (n : ℕ) (T : Tiling (Rectangle n 2)) : 
    (faultPositions n T).Finite := by
  apply Set.Finite.subset (Set.finite_Icc 0 n)
  intro k hk
  simp only [faultPositions, Set.mem_ofPred_eq] at hk
  simp only [Set.mem_Icc]
  exact ⟨Nat.zero_le k, Nat.le_of_lt hk.2.1⟩

/-- The minimum fault position in a tiling (when faults exist) -/
noncomputable def minFault (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hne : (faultPositions n T).Nonempty) : ℕ :=
  (faultPositions_finite n T).toFinset.min' (by
    rw [Set.Finite.toFinset_nonempty]
    exact hne)

/-- The minimum fault is indeed a fault -/
theorem minFault_mem (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hne : (faultPositions n T).Nonempty) : minFault n T hne ∈ faultPositions n T := by
  unfold minFault
  have := (faultPositions_finite n T).toFinset.min'_mem (by
    rw [Set.Finite.toFinset_nonempty]; exact hne)
  simp only [Set.Finite.mem_toFinset] at this
  exact this

/-- The minimum fault is a hasFault -/
theorem minFault_hasFault (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hne : (faultPositions n T).Nonempty) : hasFault n T (minFault n T hne) :=
  minFault_mem n T hne

/-- The minimum fault is less than or equal to any other fault -/
theorem minFault_le (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hne : (faultPositions n T).Nonempty) (j : ℕ) (hj : j ∈ faultPositions n T) :
    minFault n T hne ≤ j := by
  unfold minFault
  apply (faultPositions_finite n T).toFinset.min'_le
  simp only [Set.Finite.mem_toFinset]
  exact hj

/-- Decidability instance for faultPositions.Nonempty -/
noncomputable instance faultPositions_nonempty_decidable (n : ℕ) (T : Tiling (Rectangle n 2)) : 
    Decidable (faultPositions n T).Nonempty := by
  have h := (faultPositions_finite n T).toFinset.decidableNonempty
  rw [Set.Finite.toFinset_nonempty] at h
  exact h

/-- A faultfree tiling has no faults, so faultPositions is empty -/
theorem faultPositions_empty_of_isFaultfree (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hff : isFaultfree n T) : faultPositions n T = ∅ := by
  ext k
  simp only [faultPositions, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact hff.2 k

/-- A faultfree tiling has non-nonempty faultPositions -/
theorem faultPositions_not_nonempty_of_isFaultfree (n : ℕ) (T : Tiling (Rectangle n 2)) 
    (hff : isFaultfree n T) : ¬(faultPositions n T).Nonempty := by
  rw [faultPositions_empty_of_isFaultfree n T hff]
  exact Set.not_nonempty_empty

/-! ##### Helper lemmas for k >= 2 case of decomposeTiling_composeTilings -/

/-- The partial width sum at index 1 equals the width of the first component -/
theorem partialWidthSum_one (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    partialWidthSum k ts ⟨1, by omega⟩ = (ts ⟨0, by omega⟩).1 := by
  simp only [partialWidthSum, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero, Fin.val_zero]

/-- For k >= 2, the composed tiling has a fault at position (ts 0).1 -/
theorem composeTilings_hasFault_at_boundary (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1 := by
  -- Need to show: (ts 0).1 > 0, (ts 0).1 < total width, and no horizontal domino crosses position (ts 0).1
  set w0 := (ts ⟨0, by omega⟩).1 with hw0_def
  have hpos : w0 > 0 := (ts ⟨0, by omega⟩).2.property.1
  -- Total width is sum of all component widths
  have htotal : (composeTilings k ts).1 = ∑ i : Fin k, (ts i).1 := rfl
  -- Since k >= 2, there's at least one more component with positive width
  have hlt : w0 < (composeTilings k ts).1 := by
    rw [htotal]
    have h1 : (ts ⟨1, by omega⟩).1 > 0 := (ts ⟨1, by omega⟩).2.property.1
    have hdiff : (⟨0, by omega⟩ : Fin k) ≠ (⟨1, by omega⟩ : Fin k) := by simp
    have hsum : w0 + (ts ⟨1, by omega⟩).1 ≤ ∑ i : Fin k, (ts i).1 := by
      have := Finset.sum_pair hdiff (f := fun i => (ts i).1)
      calc w0 + (ts ⟨1, by omega⟩).1 
          = ∑ i ∈ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin k)), (ts i).1 := by rw [this]
        _ ≤ ∑ i : Fin k, (ts i).1 := by
          apply Finset.sum_le_sum_of_subset
          intro i _
          exact Finset.mem_univ i
    omega
  constructor
  · exact hpos
  constructor
  · exact hlt
  · -- Show no horizontal domino crosses position w0
    intro d hd
    simp only [composeTilings, composeTilings_dominos, Set.mem_iUnion] at hd
    obtain ⟨j, hj⟩ := hd
    simp only [composeTilings_component_dominos, Set.mem_image] at hj
    obtain ⟨d', hd', rfl⟩ := hj
    -- d' is a domino from component j, shifted by partialWidthSum k ts j
    cases d' with
    | horizontal i jj =>
      -- Horizontal domino at position i in component j
      -- After shifting, position is i + partialWidthSum k ts j
      simp only [Domino.shiftNat, Domino.shift]
      -- Case split on j
      by_cases hj0 : j.val = 0
      · -- j = 0: domino from first component
        left
        have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
        have hpws : partialWidthSum k ts j = 0 := by
          rw [hj_eq]
          exact partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
        simp only [hpws, Nat.cast_zero, add_zero]
        -- d' = horizontal i jj is in (ts j).2.val.dominos
        -- Since ts j is faultfree with width (ts j).1, we have i < (ts j).1
        have hd'_in : Domino.horizontal i jj ∈ (ts j).2.val.dominos := hd'
        have hsub := domino_subset_rect (ts j).1 (ts j).2.val (Domino.horizontal i jj) hd'_in
        -- The domino's rightmost point (i+1, jj) is in Rectangle (ts j).1 2
        have hright : (i + 1, jj) ∈ (Domino.horizontal i jj).toShape := by simp [Domino.toShape]
        have hright_rect := hsub hright
        simp only [Rectangle, Set.mem_ofPred_eq] at hright_rect
        -- hright_rect : 1 ≤ i + 1 ∧ i + 1 ≤ (ts j).1 ∧ 1 ≤ jj ∧ jj ≤ 2
        -- We need i < w0, i.e., i < (ts ⟨0, _⟩).1
        -- Since j = ⟨0, _⟩, we have (ts j).1 = w0
        have hw0_eq : (ts j).1 = w0 := by rw [hj_eq]
        have hi_bound : i + 1 ≤ w0 := by rw [← hw0_eq]; exact hright_rect.2.1
        linarith
      · -- j >= 1: domino from later component
        right
        have hj_pos : j.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hj0
        have hj1 : (⟨0, by omega⟩ : Fin k) < j := by simp [Fin.lt_def]; omega
        have hpws_ge : partialWidthSum k ts j ≥ w0 := by
          have := partialWidthSum_add_le k ts ⟨0, by omega⟩ j hj1
          simp only [hw0_def] at this ⊢
          omega
        -- The shifted position is i + partialWidthSum k ts j >= 1 + w0 = w0 + 1
        have hi_pos : i ≥ 1 := by
          have hd'_in : Domino.horizontal i jj ∈ (ts j).2.val.dominos := hd'
          have hsub := domino_subset_rect (ts j).1 (ts j).2.val (Domino.horizontal i jj) hd'_in
          have hleft : (i, jj) ∈ (Domino.horizontal i jj).toShape := by simp [Domino.toShape]
          have hleft_rect := hsub hleft
          simp only [Rectangle, Set.mem_ofPred_eq] at hleft_rect
          omega
        calc (i : ℤ) + (partialWidthSum k ts j : ℤ) 
            ≥ 1 + (w0 : ℤ) := by omega
          _ = (w0 : ℤ) + 1 := by ring
    | vertical i jj =>
      -- Vertical dominos don't affect faults
      trivial

/-- For k >= 1, there are no faults at positions less than (ts 0).1 in the composed tiling -/
theorem composeTilings_no_fault_before_boundary (k : ℕ) (hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (p : ℕ) (hp : p < (ts ⟨0, hk⟩).1) : ¬hasFault (composeTilings k ts).1 (composeTilings k ts).2 p := by
  intro hfault
  -- If there's a fault at p < (ts 0).1, then the first component would have a fault at p
  -- But the first component is faultfree, contradiction
  have hff := (ts ⟨0, hk⟩).2.property
  have hno_fault := hff.2 p
  apply hno_fault
  -- Show hasFault (ts 0).1 (ts 0).2.val p
  have hpos : p > 0 := hfault.1
  have hlt : p < (ts ⟨0, hk⟩).1 := hp
  constructor
  · exact hpos
  constructor
  · exact hlt
  · -- Show no horizontal domino in (ts 0).2.val crosses position p
    intro d hd
    -- d is in (ts 0).2.val.dominos
    -- The shifted version d.shiftNat 0 = d is in composeTilings_dominos
    have hd_shifted : d.shiftNat (partialWidthSum k ts ⟨0, hk⟩) ∈ (composeTilings k ts).2.dominos := by
      simp only [composeTilings, composeTilings_dominos, Set.mem_iUnion]
      refine ⟨⟨0, hk⟩, ?_⟩
      simp only [composeTilings_component_dominos, Set.mem_image]
      exact ⟨d, hd, rfl⟩
    have hpws0 : partialWidthSum k ts ⟨0, hk⟩ = 0 := partialWidthSum_zero k ts ⟨0, hk⟩ rfl
    simp only [hpws0, Domino.shiftNat_zero] at hd_shifted
    -- Use the fault condition at p in the composed tiling
    have hcross := hfault.2.2 d hd_shifted
    exact hcross

/-- The minimum fault in a composed tiling with k >= 2 components is at (ts 0).1 -/
theorem composeTilings_minFault_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) 
    (hne : (faultPositions (composeTilings k ts).1 (composeTilings k ts).2).Nonempty) :
    minFault (composeTilings k ts).1 (composeTilings k ts).2 hne = (ts ⟨0, by omega⟩).1 := by
  -- The minimum fault is (ts 0).1 because:
  -- 1. There's a fault at (ts 0).1 (by composeTilings_hasFault_at_boundary)
  -- 2. There are no faults at positions < (ts 0).1 (by composeTilings_no_fault_before_boundary)
  have hfault := composeTilings_hasFault_at_boundary k hk ts
  have hmin := minFault_hasFault (composeTilings k ts).1 (composeTilings k ts).2 hne
  have hle := minFault_le (composeTilings k ts).1 (composeTilings k ts).2 hne (ts ⟨0, by omega⟩).1 hfault
  -- Show minFault >= (ts 0).1 by contradiction
  by_contra hne'
  push Not at hne'
  have hlt : minFault (composeTilings k ts).1 (composeTilings k ts).2 hne < (ts ⟨0, by omega⟩).1 := by
    omega
  have hno := composeTilings_no_fault_before_boundary k (by omega : k ≥ 1) ts 
    (minFault (composeTilings k ts).1 (composeTilings k ts).2 hne) hlt
  exact hno hmin

/-! ##### Lemmas relating restrictTiling to composeTilings -/

/-- The tail of a tuple of faultfree tilings -/
def faultfreeTilingsTail (k : ℕ) (hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    Fin (k - 1) → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}) :=
  fun i => ts ⟨i.val + 1, by omega⟩

/-- The width of composing the tail equals the total width minus the first component width -/
theorem composeTilings_tail_width (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).1 = 
    (composeTilings k ts).1 - (ts ⟨0, by omega⟩).1 := by
  simp only [composeTilings, faultfreeTilingsTail]
  -- Sum over tail = total sum - first element
  have hsplit : ∑ i : Fin k, (ts i).1 = (ts ⟨0, by omega⟩).1 + 
                ∑ i : Fin (k - 1), (ts ⟨i.val + 1, by omega⟩).1 := by
    induction k with
    | zero => omega
    | succ n ih =>
      cases n with
      | zero => omega
      | succ m =>
        rw [Fin.sum_univ_succ]
        rfl
  omega

/-- Dominos from component 0 are in the left part at position (ts 0).1 -/
theorem composeTilings_component0_inLeftPart (k : ℕ) (hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (d : Domino) (hd : d ∈ (ts ⟨0, hk⟩).2.val.dominos) :
    d.inLeftPart (ts ⟨0, hk⟩).1 := by
  intro p hp
  have hsub := domino_subset_rect (ts ⟨0, hk⟩).1 (ts ⟨0, hk⟩).2.val d hd
  have hp_rect := hsub hp
  simp only [Rectangle, Set.mem_ofPred_eq] at hp_rect
  exact hp_rect.2.1

/-- Dominos from component i >= 1 are in the right part at position (ts 0).1 -/
theorem composeTilings_componentPos_inRightPart (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) (hi : i.val ≥ 1) (d : Domino) (hd : d ∈ (ts i).2.val.dominos) :
    (d.shiftNat (partialWidthSum k ts i)).inRightPart (ts ⟨0, by omega⟩).1 := by
  intro p hp
  -- The shifted domino has x-coordinates >= partialWidthSum k ts i + 1
  -- Since i >= 1, partialWidthSum k ts i >= (ts 0).1
  have hpws_ge : partialWidthSum k ts i ≥ (ts ⟨0, by omega⟩).1 := by
    have h0 : (⟨0, by omega⟩ : Fin k) < i := by simp [Fin.lt_def]; omega
    have := partialWidthSum_add_le k ts ⟨0, by omega⟩ i h0
    omega
  -- The original domino d has x-coords in [1, (ts i).1]
  have hd_x := domino_subset_rect (ts i).1 (ts i).2.val d hd
  -- After shifting, x-coords are in [1 + pws, (ts i).1 + pws]
  rw [Domino.shiftNat_toShape, Set.mem_image] at hp
  obtain ⟨p', hp', hp_eq⟩ := hp
  rw [Prod.ext_iff] at hp_eq
  have hp'_rect := hd_x hp'
  simp only [Rectangle, Set.mem_ofPred_eq] at hp'_rect
  have hx' : p'.1 ≥ 1 := hp'_rect.1
  calc p.1 = p'.1 + partialWidthSum k ts i := by omega
    _ ≥ 1 + (ts ⟨0, by omega⟩).1 := by omega
    _ = (ts ⟨0, by omega⟩).1 + 1 := by ring

/-- The left restriction of a composed tiling at the first boundary has the same dominos 
    as the first component -/
theorem restrictTilingLeft_composeTilings_dominos (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) 
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    (restrictTilingLeft (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault).dominos = (ts ⟨0, by omega⟩).2.val.dominos := by
  ext d
  simp only [restrictTilingLeft, composeTilings, composeTilings_dominos,
             Set.mem_iUnion, composeTilings_component_dominos, Set.mem_image]
  constructor
  · -- If d is in the left restriction, it came from component 0
    intro ⟨⟨i, d', hd', hd_eq⟩, hleft⟩
    -- d = d'.shiftNat (partialWidthSum k ts i)
    subst hd_eq
    -- If i = 0, then partialWidthSum = 0 and d' is in (ts 0).2.val.dominos
    -- If i >= 1, then d is in right part, contradiction with hleft
    by_cases hi : i.val = 0
    · -- i = 0
      have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [hi_eq] at hd' ⊢
      have hpws : partialWidthSum k ts ⟨0, by omega⟩ = 0 := 
        partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
      rw [hpws, Domino.shiftNat_zero]
      exact hd'
    · -- i >= 1, contradiction
      exfalso
      have hi_pos : i.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
      have hright := composeTilings_componentPos_inRightPart k hk ts i hi_pos d' hd'
      -- d'.shiftNat ... is in right part, but hleft says it's in left part
      have hcontra := hleft
      simp only [Domino.inLeftPart] at hcontra
      simp only [Domino.inRightPart] at hright
      -- Get a point in d'.shiftNat ...
      have hne := Domino.toShape_nonempty (d'.shiftNat (partialWidthSum k ts i))
      obtain ⟨p, hp⟩ := hne
      have h1 := hcontra p hp
      have h2 := hright p hp
      omega
  · -- If d is in (ts 0).2.val.dominos, it's in the composed tiling and in left part
    intro hd
    constructor
    · -- d is in composeTilings_dominos
      refine ⟨⟨0, by omega⟩, d, hd, ?_⟩
      have hpws : partialWidthSum k ts ⟨0, by omega⟩ = 0 := 
        partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
      rw [hpws, Domino.shiftNat_zero]
    · -- d is in left part
      exact composeTilings_component0_inLeftPart k (by omega) ts d hd

/-- The left restriction of a composed tiling equals the first component's tiling.
    This follows from `restrictTilingLeft_composeTilings_dominos` via `Tiling.ext`. -/
theorem restrictTilingLeft_composeTilings_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    restrictTilingLeft (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault = (ts ⟨0, by omega⟩).2.val := by
  apply Tiling.ext
  exact restrictTilingLeft_composeTilings_dominos k hk ts hfault

/-- Dominos from component i shifted and then unshifted by k gives back the original -/
theorem composeTilings_componentPos_dominos_unshift (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) (hi : i.val ≥ 1) (d : Domino) (hd : d ∈ (ts i).2.val.dominos) :
    (d.shiftNat (partialWidthSum k ts i)).shiftNeg (ts ⟨0, by omega⟩).1 = 
    d.shiftNat (partialWidthSum k ts i - (ts ⟨0, by omega⟩).1) := by
  -- partialWidthSum k ts i >= (ts 0).1 for i >= 1
  have hpws_ge : partialWidthSum k ts i ≥ (ts ⟨0, by omega⟩).1 := by
    have h0 : (⟨0, by omega⟩ : Fin k) < i := by simp [Fin.lt_def]; omega
    have := partialWidthSum_add_le k ts ⟨0, by omega⟩ i h0
    omega
  cases d with
  | horizontal x y =>
    simp only [Domino.shiftNat, Domino.shiftNeg, Domino.shift]
    congr 1
    omega
  | vertical x y =>
    simp only [Domino.shiftNat, Domino.shiftNeg, Domino.shift]
    congr 1
    omega

/-- The partial width sum for the tail equals the original minus (ts 0).1 -/
theorem partialWidthSum_tail (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (j : Fin (k - 1)) :
    partialWidthSum (k - 1) (faultfreeTilingsTail k (by omega) ts) j = 
    partialWidthSum k ts ⟨j.val + 1, by omega⟩ - (ts ⟨0, by omega⟩).1 := by
  simp only [partialWidthSum, faultfreeTilingsTail]
  -- LHS: ∑ i : Fin j.val, (ts ⟨i.val + 1, ...⟩).1
  -- RHS: ∑ i : Fin (j.val + 1), (ts ⟨i.val, ...⟩).1 - (ts ⟨0, ...⟩).1
  -- Use Fin.sum_univ_succ on RHS
  have hrhs : ∑ i : Fin (j.val + 1), (ts ⟨i.val, by omega⟩).1 = 
              (ts ⟨0, by omega⟩).1 + ∑ i : Fin j.val, (ts ⟨i.succ.val, by omega⟩).1 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero]
  conv_rhs => rw [hrhs]
  -- Now goal: ∑ i : Fin j.val, (ts ⟨i.val + 1, ...⟩).1 = 
  --           (ts ⟨0, ...⟩).1 + ∑ i : Fin j.val, (ts ⟨i.succ.val, ...⟩).1 - (ts ⟨0, ...⟩).1
  -- Note: i.succ.val = i.val + 1
  have heq : ∑ i : Fin j.val, (ts ⟨i.succ.val, by omega⟩).1 = 
             ∑ i : Fin j.val, (ts ⟨i.val + 1, by omega⟩).1 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_succ]
  rw [heq]
  omega

/-- The right restriction of a composed tiling at the first boundary has the same dominos 
    as the composition of the tail -/
theorem restrictTilingRight_composeTilings_dominos (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) 
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    (restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault).dominos = 
    (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2.dominos := by
  -- The proof shows that:
  -- 1. Dominos in right restriction come from components i >= 1
  -- 2. After unshifting by (ts 0).1, they match the tail composition
  ext d
  simp only [restrictTilingRight, Set.mem_image, composeTilings, 
             composeTilings_dominos, Set.mem_iUnion, composeTilings_component_dominos]
  constructor
  · -- Forward direction: d is in restrictTilingRight → d is in composeTilings of tail
    intro ⟨d', ⟨⟨i, d'', hd'', hd'_eq⟩, hright⟩, hd_eq⟩
    -- d' = d''.shiftNat (partialWidthSum k ts i) is in right part
    -- d = d'.shiftNeg w0 = (d''.shiftNat (pws k ts i)).shiftNeg w0
    subst hd'_eq hd_eq
    -- If i = 0, then d' would be in left part (contradiction)
    -- So i >= 1
    by_cases hi : i.val = 0
    · -- i = 0: contradiction
      exfalso
      have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [hi_eq] at hd'' hright
      have hpws : partialWidthSum k ts ⟨0, by omega⟩ = 0 := partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
      rw [hpws, Domino.shiftNat_zero] at hright
      have hleft := composeTilings_component0_inLeftPart k (by omega : k ≥ 1) ts d'' hd''
      -- d'' is in left part but hright says it's in right part
      have hne := Domino.toShape_nonempty d''
      obtain ⟨p, hp⟩ := hne
      have h1 := hleft p hp
      have h2 := hright p hp
      omega
    · -- i >= 1: d comes from component i
      have hi_pos : i.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
      -- The index in the tail is i - 1
      -- Need to show d'' is in (faultfreeTilingsTail k _ ts ⟨i.val - 1, _⟩).2.val.dominos
      have hd''_tail : d'' ∈ (faultfreeTilingsTail k (by omega) ts ⟨i.val - 1, by omega⟩).2.val.dominos := by
        simp only [faultfreeTilingsTail]
        have hi_eq' : i.val - 1 + 1 = i.val := by omega
        have hfin_eq : (⟨i.val - 1 + 1, by omega⟩ : Fin k) = i := Fin.ext hi_eq'
        rw [hfin_eq]
        exact hd''
      refine ⟨⟨i.val - 1, by omega⟩, d'', hd''_tail, ?_⟩
      -- Need: (d''.shiftNat (pws k ts i)).shiftNeg w0 = d''.shiftNat (pws (k-1) (tail) (i-1))
      -- Use composeTilings_componentPos_dominos_unshift and partialWidthSum_tail
      have hunshift := composeTilings_componentPos_dominos_unshift k hk ts i hi_pos d'' hd''
      rw [hunshift]
      congr 1
      have htail := partialWidthSum_tail k hk ts ⟨i.val - 1, by omega⟩
      -- htail says: pws (k-1) (tail ts) ⟨i.val - 1, _⟩ = pws k ts ⟨i.val - 1 + 1, _⟩ - w0
      -- We need: pws k ts i - w0 = pws (k-1) (tail ts) ⟨i.val - 1, _⟩
      have hi_eq' : i.val - 1 + 1 = i.val := by omega
      have hfin_eq : (⟨i.val - 1 + 1, by omega⟩ : Fin k) = i := Fin.ext hi_eq'
      rw [htail, hfin_eq]
  · -- Backward direction: d is in composeTilings of tail → d is in restrictTilingRight
    intro ⟨j, d', hd', hd_eq⟩
    -- j : Fin (k - 1), d' is in (tail ts j).2.val.dominos
    -- d = d'.shiftNat (pws (k-1) (tail ts) j)
    subst hd_eq
    -- The original index is j + 1
    let i : Fin k := ⟨j.val + 1, by omega⟩
    -- d' is in (ts i).2.val.dominos (since tail ts j = ts (j+1))
    have hd'_ts : d' ∈ (ts i).2.val.dominos := by
      simp only [faultfreeTilingsTail] at hd'
      exact hd'
    -- The shifted domino in composeTilings is d'.shiftNat (pws k ts i)
    have hi_pos : i.val ≥ 1 := by simp only [i, Nat.add_one_le_iff, Nat.zero_lt_succ]
    -- Show that d'.shiftNat (pws k ts i) is in right part
    have hright := composeTilings_componentPos_inRightPart k hk ts i hi_pos d' hd'_ts
    -- The unshifted version
    have hunshift := composeTilings_componentPos_dominos_unshift k hk ts i hi_pos d' hd'_ts
    -- pws (k-1) (tail ts) j = pws k ts i - w0
    have htail := partialWidthSum_tail k hk ts j
    -- So d'.shiftNat (pws (k-1) (tail ts) j) = (d'.shiftNat (pws k ts i)).shiftNeg w0
    refine ⟨d'.shiftNat (partialWidthSum k ts i), ⟨⟨i, d', hd'_ts, rfl⟩, hright⟩, ?_⟩
    rw [hunshift, htail]

/-- The right restriction of a composed tiling has the same dominos as the composition of the tail.
    Note: The tilings have different types (different width parameters), so we state this 
    as a domino equality rather than a tiling equality. Use `Tiling.ext` with the width 
    equality `composeTilings_tail_width` to convert to tiling equality when needed. -/
theorem restrictTilingRight_composeTilings_dominos_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    (restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault).dominos = 
    (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2.dominos :=
  restrictTilingRight_composeTilings_dominos k hk ts hfault

/-- The right restriction of a composed tiling equals the composition of the tail.
    This combines the width equality `composeTilings_tail_width` with the domino equality
    `restrictTilingRight_composeTilings_dominos_eq` to give a full tiling equality.
    
    Note: The two tilings have the same type because:
    - restrictTilingRight has width (composeTilings k ts).1 - (ts 0).1
    - composeTilings (k-1) (tail ts) has width (composeTilings k ts).1 - (ts 0).1 (by composeTilings_tail_width) -/
theorem restrictTilingRight_composeTilings_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault = 
    (composeTilings_tail_width k hk ts) ▸ (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2 := by
  -- The dominos are equal by restrictTilingRight_composeTilings_dominos_eq
  have hdominos := restrictTilingRight_composeTilings_dominos_eq k hk ts hfault
  -- Apply Tiling.ext after casting
  apply Tiling.ext
  rw [hdominos]
  -- The cast doesn't change dominos
  rw [Tiling.subst_dominos]

/-- The decomposition function: given a tiling of a height-2 rectangle, produce a tuple
    of faultfree tilings by cutting along all faults.
    
    For example, a tiling with faults at positions k₁ < k₂ < ... < kₘ decomposes into
    m+1 faultfree tilings of widths k₁, k₂-k₁, ..., n-kₘ.
    
    The empty tiling (n=0) decomposes into the empty tuple (k=0). 
    
    Implementation: We recursively find the minimum fault position, cut the tiling there,
    and decompose the right part. The left part at a minimum fault is always faultfree.
    If no faults exist, the entire tiling is faultfree and returned as a singleton. -/
noncomputable def decomposeTiling : (n : ℕ) → (T : Tiling (Rectangle n 2)) → 
    Σ k : ℕ, Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})
  | 0, _ => ⟨0, Fin.elim0⟩
  | n + 1, T => 
    if hne : (faultPositions (n + 1) T).Nonempty then
      -- Has faults: cut at minimum fault
      let k := minFault (n + 1) T hne
      have hk : hasFault (n + 1) T k := minFault_hasFault (n + 1) T hne
      have hk_min : ∀ j, j < k → ¬hasFault (n + 1) T j := by
        intro j hj hfault
        have hle := minFault_le (n + 1) T hne j hfault
        omega
      let left := restrictTilingLeft (n + 1) T k hk
      let left_ff := restrictTilingLeft_isFaultfree (n + 1) T k hk hk_min
      let right := restrictTilingRight (n + 1) T k hk
      have hk_pos : k > 0 := hk.1
      have hk_lt : k < n + 1 := hk.2.1
      have hdec : n + 1 - k < n + 1 := by omega
      let ⟨m, ts⟩ := decomposeTiling (n + 1 - k) right
      ⟨m + 1, fun i => 
        if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ 
        else ts ⟨i.val - 1, by omega⟩⟩
    else
      -- No faults: T is faultfree
      have hff : isFaultfree (n + 1) T := by
        constructor
        · omega
        · intro k hfault
          exact hne ⟨k, hfault⟩
      ⟨1, fun _ => ⟨n + 1, ⟨T, hff⟩⟩⟩
termination_by n => n

/-- Decomposing a tiling with faults at the minimum fault position.
    This characterizes the structure of decomposeTiling when faults exist. -/
theorem decomposeTiling_hasFault (n : ℕ) (T : Tiling (Rectangle (n + 1) 2))
    (hne : (faultPositions (n + 1) T).Nonempty) :
    let k := minFault (n + 1) T hne
    let hk := minFault_hasFault (n + 1) T hne
    let hk_min : ∀ j, j < k → ¬hasFault (n + 1) T j := fun j hj hfault => 
      absurd (minFault_le (n + 1) T hne j hfault) (not_le.mpr hj)
    let left := restrictTilingLeft (n + 1) T k hk
    let left_ff := restrictTilingLeft_isFaultfree (n + 1) T k hk hk_min
    let right := restrictTilingRight (n + 1) T k hk
    let ⟨m, ts⟩ := decomposeTiling (n + 1 - k) right
    decomposeTiling (n + 1) T = 
      ⟨m + 1, fun i => if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ 
                       else ts ⟨i.val - 1, by omega⟩⟩ := by
  simp only [decomposeTiling, dite_eq_left hne]

/-- The width of decomposeTiling when faults exist equals m+1 where m is the count from
    decomposing the right part. This is useful for proving composeTilings_decomposeTiling. -/
theorem decomposeTiling_hasFault_fst (n : ℕ) (T : Tiling (Rectangle (n + 1) 2))
    (hne : (faultPositions (n + 1) T).Nonempty) :
    let k := minFault (n + 1) T hne
    let hk := minFault_hasFault (n + 1) T hne
    let right := restrictTilingRight (n + 1) T k hk
    (decomposeTiling (n + 1) T).1 = (decomposeTiling (n + 1 - k) right).1 + 1 := by
  simp only [decomposeTiling, dite_eq_left hne]

set_option backward.isDefEq.respectTransparency false in
/-- Decomposition followed by composition gives back the original tiling -/
theorem composeTilings_decomposeTiling (n : ℕ) (T : Tiling (Rectangle n 2)) :
    let ⟨k, ts⟩ := decomposeTiling n T
    composeTilings k ts = ⟨n, T⟩ := by
  simp only
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      -- n = 0 case: decomposeTiling returns ⟨0, Fin.elim0⟩
      have heq : decomposeTiling 0 T = ⟨0, Fin.elim0⟩ := by unfold decomposeTiling; rfl
      rw [heq]
      simp only [composeTilings, Sigma.mk.injEq]
      refine ⟨rfl, ?_⟩
      cases T with
      | mk dominos pairwise_disjoint cover =>
        congr 1
        show composeTilings_dominos _ _ = dominos
        have hT_empty : dominos = ∅ := by
          have heq : Rectangle 0 2 = ∅ := Rectangle_zero_left 2
          have hcover' : ⋃ d ∈ dominos, d.toShape = ∅ := by rw [cover]; exact heq
          by_contra hne
          have hne' : dominos.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
          obtain ⟨d, hd⟩ := hne'
          have hsub : d.toShape ⊆ ∅ := by
            calc d.toShape ⊆ ⋃ d' ∈ dominos, d'.toShape := Set.subset_biUnion_of_mem hd
            _ = ∅ := hcover'
          have hdne : d.toShape.Nonempty := Domino.toShape_nonempty d
          exact Set.not_nonempty_empty (hdne.mono hsub)
        rw [hT_empty]
        ext x
        simp only [composeTilings_dominos, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        intro ⟨i, _⟩
        exact i.elim0
    | n' + 1 =>
      -- n = n' + 1 case
      -- decomposeTiling (n' + 1) T branches on whether faults exist
      -- Case split on whether faults exist
      by_cases hne : (faultPositions (n' + 1) T).Nonempty
      · -- Has faults: cut at minimum fault
        -- Get the minimum fault position and related data
        set k := minFault (n' + 1) T hne with hk_def
        have hk : hasFault (n' + 1) T k := minFault_hasFault (n' + 1) T hne
        have hk_min : ∀ j, j < k → ¬hasFault (n' + 1) T j := by
          intro j hj hfault
          have hle := minFault_le (n' + 1) T hne j hfault
          omega
        have hk_pos : k > 0 := hk.1
        have hk_lt : k < n' + 1 := hk.2.1
        have hdec : n' + 1 - k < n' + 1 := by omega
        
        -- Set up the left and right parts
        set left := restrictTilingLeft (n' + 1) T k hk with hleft_def
        set right := restrictTilingRight (n' + 1) T k hk with hright_def
        have left_ff := restrictTilingLeft_isFaultfree (n' + 1) T k hk hk_min
        
        -- Get the decomposition of the right part (keeping definitional equality)
        set dec_right := decomposeTiling (n' + 1 - k) right with hdec_right_def
        
        -- Apply induction hypothesis to the right part
        have ih_right := ih (n' + 1 - k) hdec right
        -- ih_right : composeTilings dec_right.1 dec_right.2 = ⟨n' + 1 - k, right⟩
        
        -- Rewrite using decomposeTiling_hasFault to get the concrete form
        have hdecomp := decomposeTiling_hasFault n' T hne
        simp only at hdecomp
        rw [hdecomp]
        
        -- The goal is now in terms of the concrete decomposition
        -- We need to show that composing gives back ⟨n' + 1, T⟩
        
        -- Key facts we'll use:
        -- 1. ih_right tells us composeTilings on the right part gives back right
        -- 2. dominos_eq_left_union_shifted_right tells us T.dominos = left ∪ shifted(right)
        
        -- The proof strategy is to show both components are equal
        -- For this, we use the fact that Sigma types are equal iff both components are equal
        
        -- Define abbreviations for clarity
        let m := (decomposeTiling (n' + 1 - k) right).1
        let ts_rest := (decomposeTiling (n' + 1 - k) right).2
        
        -- Show the width equality first
        have hwidth : (composeTilings (m + 1) (fun i => 
            if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ else ts_rest ⟨i.val - 1, by omega⟩)).1 = n' + 1 := by
          simp only [composeTilings]
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, dite_true, Fin.val_succ, Nat.add_one_ne_zero, dite_false,
                     Nat.add_sub_cancel]
          have h := congrArg Sigma.fst ih_right
          simp only [composeTilings] at h
          rw [h]
          omega
        
        -- For the tiling part, we need to show the dominos are equal
        -- This requires showing that the union of shifted components equals T.dominos
        -- 
        -- The proof involves showing:
        -- 1. Component 0 (left) contributes left.dominos (shifted by 0)
        -- 2. Components 1..m contribute the shifted composition of ts_rest
        -- 3. By IH, composeTilings m ts_rest = right
        -- 4. By dominos_eq_left_union_shifted_right, T.dominos = left ∪ shifted(right)
        
        -- Define the function ts' for clarity
        let ts' : Fin (m + 1) → (Σ w : ℕ, {T' : Tiling (Rectangle w 2) // isFaultfree w T'}) := 
          fun i => if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ else ts_rest ⟨i.val - 1, by omega⟩
        
        -- Show the dominos equality
        -- composeTilings_dominos (m + 1) ts' = T.dominos
        -- By dominos_eq_left_union_shifted_right:
        -- T.dominos = left.dominos ∪ right.dominos.image (shiftNat k)
        
        have hT_dominos := dominos_eq_left_union_shifted_right (n' + 1) T k hk
        
        -- Show that the composed dominos equal left ∪ shifted(right)
        have hdominos_eq : (composeTilings (m + 1) ts').2.dominos = T.dominos := by
          -- Step 1: composeTilings dominos = composeTilings_dominos
          simp only [composeTilings]
          
          -- Step 2: Split the union into component 0 and components 1..m
          have hsplit : composeTilings_dominos (m + 1) ts' = 
              composeTilings_component_dominos (m + 1) ts' 0 ∪ 
              ⋃ j : Fin m, composeTilings_component_dominos (m + 1) ts' j.succ := by
            ext d
            simp only [composeTilings_dominos, Set.mem_iUnion, Set.mem_union]
            constructor
            · intro ⟨i, hi⟩
              rcases i.eq_zero_or_eq_succ with rfl | ⟨j, rfl⟩
              · left; exact hi
              · right; exact ⟨j, hi⟩
            · intro h
              rcases h with h | ⟨j, hj⟩
              · exact ⟨0, h⟩
              · exact ⟨j.succ, hj⟩
          rw [hsplit]
          
          -- Step 3: Component 0 is left.dominos (since partialWidthSum = 0)
          have hcomp0 : composeTilings_component_dominos (m + 1) ts' 0 = left.dominos := by
            simp only [composeTilings_component_dominos]
            have hpws0 : partialWidthSum (m + 1) ts' 0 = 0 := 
              partialWidthSum_zero (m + 1) ts' 0 rfl
            rw [hpws0]
            simp only [Domino.shiftNat_zero, Set.image_id']
            -- ts' 0 = ⟨k, ⟨left, left_ff⟩⟩
            have hts'0 : ts' 0 = ⟨k, ⟨left, left_ff⟩⟩ := by
              simp only [ts']
              simp only [Fin.val_zero, dite_true]
            rw [hts'0]
          rw [hcomp0]
          
          -- Step 4: Show components 1..m equal right.dominos.image (shiftNat k)
          -- First, show the relationship between ts' j.succ and ts_rest j
          have hts'_succ : ∀ j : Fin m, ts' j.succ = ts_rest j := by
            intro j
            simp only [ts']
            simp only [Fin.val_succ, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
            rfl
          
          -- Key: partialWidthSum (m+1) ts' j.succ = k + partialWidthSum m ts_rest j
          have hpws_succ : ∀ j : Fin m, 
              partialWidthSum (m + 1) ts' j.succ = k + partialWidthSum m ts_rest j := by
            intro j
            simp only [partialWidthSum]
            -- The sum over Fin j.succ.val needs to be rewritten
            -- j.succ.val = j.val + 1
            -- We need: ∑ i : Fin (j.val + 1), (ts' ⟨i, ...⟩).1 = k + ∑ i : Fin j.val, (ts_rest ⟨i, ...⟩).1
            
            -- Define a simpler function for the sum
            let f : Fin j.succ.val → ℕ := fun i => (ts' ⟨i.val, Nat.lt_trans i.isLt j.succ.isLt⟩).1
            let g : Fin j.val → ℕ := fun i => (ts_rest ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩).1
            
            -- j.succ.val = j.val + 1 ≥ 1, so Fin j.succ.val has a 0 element
            have hpos : j.succ.val > 0 := by simp only [Fin.val_succ]; omega
            let zero_idx : Fin j.succ.val := ⟨0, hpos⟩
            
            -- Show f zero_idx = k
            have hf0 : f zero_idx = k := by
              simp only [f, zero_idx, ts']
              simp only [dite_true]
            
            -- Show f i.succ = g i for i : Fin j.val
            have hf_succ : ∀ i : Fin j.val, f i.succ = g i := by
              intro i
              simp only [f, g, ts']
              simp only [Fin.val_succ, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
            
            -- Now use Fin.sum_univ_succ on f
            have h_sum : ∑ i : Fin j.succ.val, f i = f zero_idx + ∑ i : Fin j.val, f i.succ := by
              have h := Fin.sum_univ_succ f
              convert h using 2; rfl
            
            calc ∑ i : Fin j.succ.val, (ts' ⟨i.val, Nat.lt_trans i.isLt j.succ.isLt⟩).1
                = ∑ i : Fin j.succ.val, f i := rfl
              _ = f zero_idx + ∑ i : Fin j.val, f i.succ := h_sum
              _ = k + ∑ i : Fin j.val, f i.succ := by rw [hf0]
              _ = k + ∑ i : Fin j.val, g i := by simp only [hf_succ]
              _ = k + ∑ i : Fin j.val, (ts_rest ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩).1 := rfl
          
          -- Now show ⋃ j : Fin m, composeTilings_component_dominos (m+1) ts' j.succ
          --         = (composeTilings_dominos m ts_rest).image (shiftNat k)
          have hrest : ⋃ j : Fin m, composeTilings_component_dominos (m + 1) ts' j.succ = 
              (composeTilings_dominos m ts_rest).image (fun d => d.shiftNat k) := by
            ext d
            simp only [Set.mem_iUnion, composeTilings_component_dominos, Set.mem_image,
                       composeTilings_dominos]
            constructor
            · -- Forward: d is in component j.succ of ts'
              intro ⟨j, hj⟩
              obtain ⟨d', hd', hd_eq⟩ := hj
              use d'.shiftNat (partialWidthSum m ts_rest j)
              constructor
              · -- d'.shiftNat (partialWidthSum m ts_rest j) is in composeTilings_dominos m ts_rest
                refine ⟨j, d', ?_, rfl⟩
                rw [hts'_succ] at hd'
                exact hd'
              · -- d = (d'.shiftNat ...).shiftNat k
                rw [← hd_eq, hpws_succ, Nat.add_comm, Domino.shiftNat_shiftNat]
            · -- Backward: d is in (composeTilings_dominos m ts_rest).image (shiftNat k)
              intro ⟨d'', hd''_mem, hd_eq⟩
              obtain ⟨j, d', hd', hd''_eq⟩ := hd''_mem
              refine ⟨j, ?_⟩
              refine ⟨d', ?_, ?_⟩
              · rw [hts'_succ]; exact hd'
              · rw [← hd_eq, ← hd''_eq, hpws_succ, Nat.add_comm, Domino.shiftNat_shiftNat]
          rw [hrest]
          
          -- Step 5: Use IH to relate composeTilings_dominos m ts_rest to right.dominos
          have hih_dominos : (composeTilings m ts_rest).2.dominos = right.dominos := by
            have h := congrArg (fun σ => σ.2.dominos) ih_right
            exact h
          
          -- composeTilings_dominos m ts_rest = (composeTilings m ts_rest).2.dominos
          have hcomp_dominos : composeTilings_dominos m ts_rest = (composeTilings m ts_rest).2.dominos := by
            simp only [composeTilings]
          
          rw [hcomp_dominos, hih_dominos]
          
          -- Step 6: Apply dominos_eq_left_union_shifted_right
          exact hT_dominos.symm
        
        -- Now use the dominos equality to prove the full equality
        -- We need: composeTilings (m + 1) ts' = ⟨n' + 1, T⟩
        -- We have: hwidth for the first component
        -- We have: hdominos_eq for the second component
        
        -- Since the dominos are equal and the widths are equal, the tilings are equal
        -- The key is to use Sigma.ext_iff
        
        -- First, we need to show the tilings are equal after casting
        have htiling_eq : hwidth ▸ (composeTilings (m + 1) ts').2 = T := by
          apply Tiling.ext
          rw [Tiling.subst_dominos]
          exact hdominos_eq
        
        -- The goal uses raw decomposeTiling expressions instead of m and ts'
        -- We need to convert using the definitional equalities
        show composeTilings (m + 1) ts' = ⟨n' + 1, T⟩
        
        -- Use Sigma.ext_iff to construct the equality
        rw [Sigma.ext_iff]
        refine ⟨hwidth, ?_⟩
        -- Now need to show HEq (composeTilings (m + 1) ts').2 T
        -- We have: hwidth ▸ (composeTilings (m + 1) ts').2 = T
        -- Use eqRec_heq_iff: (h ▸ a ≍ b) ↔ (a ≍ b)
        exact eqRec_heq_iff.mp (heq_of_eq htiling_eq)
      · -- No faults: T is faultfree
        have hff : isFaultfree (n' + 1) T := by
          constructor
          · omega
          · intro k hfault
            exact hne ⟨k, hfault⟩
        -- Show that decomposeTiling returns a singleton
        have hne' : ¬(faultPositions (n' + 1) T).Nonempty := hne
        have hdecomp : decomposeTiling (n' + 1) T = 
          ⟨1, fun _ => ⟨n' + 1, ⟨T, hff⟩⟩⟩ := by
          simp only [decomposeTiling, dite_eq_right hne']
        rw [hdecomp]
        
        -- composeTilings 1 ts = ⟨(ts 0).1, (ts 0).2.val⟩ = ⟨n' + 1, T⟩
        have hwidth := composeTilings_one_width (fun _ => ⟨n' + 1, ⟨T, hff⟩⟩)
        have htiling := composeTilings_one_tiling (fun _ => ⟨n' + 1, ⟨T, hff⟩⟩)
        -- Use Sigma.ext to prove equality of sigma types
        apply Sigma.ext
        · -- Width equality
          simp only [composeTilings, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
        · -- Tiling equality (as HEq)
          simp only [heq_eq_eq]
          apply Tiling.ext
          rw [composeTilings_one_dominos]



/-- Decomposing a faultfree tiling returns a singleton tuple containing the original tiling.
    This is a key helper for proving `decomposeTiling_composeTilings`. -/
theorem decomposeTiling_faultfree (n : ℕ) (T : Tiling (Rectangle (n + 1) 2))
    (hff : isFaultfree (n + 1) T) :
    decomposeTiling (n + 1) T = ⟨1, fun _ => ⟨n + 1, ⟨T, hff⟩⟩⟩ := by
  unfold decomposeTiling
  -- Since T is faultfree, faultPositions is empty, so Nonempty is false
  have hne : ¬(faultPositions (n + 1) T).Nonempty := 
    faultPositions_not_nonempty_of_isFaultfree (n + 1) T hff
  simp only [dite_eq_right hne]

/-- Decomposition is invariant under type cast (subst).
    This is key for handling dependent types in the inverse proofs. -/
theorem decomposeTiling_subst {n m : ℕ} (h : n = m) (T : Tiling (Rectangle n 2)) :
    decomposeTiling n T = decomposeTiling m (h ▸ T) := by
  subst h
  rfl

/-- Decomposition depends only on width and dominos.
    If two tilings have the same width and dominos, their decompositions are equal. -/
theorem decomposeTiling_eq_of_dominos_eq {n m : ℕ} (h : n = m) 
    (T1 : Tiling (Rectangle n 2)) (T2 : Tiling (Rectangle m 2))
    (hdom : T1.dominos = T2.dominos) :
    decomposeTiling n T1 = decomposeTiling m T2 := by
  subst h
  have hT_eq : T1 = T2 := Tiling.ext T1 T2 hdom
  rw [hT_eq]

/-- The left restriction of a subst'd tiling equals the left restriction of the original. -/
theorem restrictTilingLeft_subst {n m : ℕ} (h : n = m) (T : Tiling (Rectangle n 2)) (k : ℕ)
    (hk : hasFault n T k) :
    restrictTilingLeft m (h ▸ T) k (by subst h; exact hk) = 
    restrictTilingLeft n T k hk := by
  subst h
  rfl

/-- The right restriction of a subst'd tiling has the same dominos as the original. -/
theorem restrictTilingRight_subst_dominos {n m : ℕ} (h : n = m) (T : Tiling (Rectangle n 2)) (k : ℕ)
    (hk : hasFault n T k) :
    (restrictTilingRight m (h ▸ T) k (by subst h; exact hk)).dominos = 
    (restrictTilingRight n T k hk).dominos := by
  subst h
  rfl

/-- Helper lemma for proving equality of sigma types with Fin-indexed functions.
    This is used to prove decomposeTiling_composeTilings in the k ≥ 2 case. -/
private lemma sigma_fin_fun_ext {α : Type*} (n m : ℕ) (h : n = m) 
    (f : Fin n → α) (g : Fin m → α)
    (hfg : ∀ i : Fin m, f ⟨i.val, by omega⟩ = g i) :
    (⟨n, f⟩ : Σ k, Fin k → α) = ⟨m, g⟩ := by
  apply Sigma.ext h
  simp only
  apply Function.hfunext (by simp only [h])
  intro i j hij
  have hi_eq : i.val = j.val := by
    have : HEq i j := hij
    cases h
    exact (Fin.heq_ext_iff rfl).mp this
  rw [heq_eq_eq]
  have hj_eq : (⟨i.val, by omega⟩ : Fin m) = j := Fin.ext hi_eq
  rw [← hj_eq]
  have hi_eq' : (⟨i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
  conv_lhs => rw [← hi_eq']
  exact hfg ⟨i.val, by omega⟩

set_option backward.isDefEq.respectTransparency false in
/-- Composition followed by decomposition gives back the original tuple.
    
    This theorem proves that composing faultfree tilings and then decomposing 
    recovers the original tuple of tilings.
    
    The proof handles two cases:
    1. If k = 0 (empty tuple), the composed tiling is empty (width 0), and 
       decomposeTiling returns the empty tuple by definition.
    2. If k > 0, the composed tiling has positive width, and we need to show that
       the faults in the composed tiling occur exactly at the partial width sums,
       so decomposing at those faults recovers the original pieces. -/
theorem decomposeTiling_composeTilings (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    decomposeTiling (composeTilings k ts).1 (composeTilings k ts).2 = ⟨k, ts⟩ := by
  -- Use strong induction on k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
      -- k = 0: empty tuple, composed tiling has width 0
      show decomposeTiling 0 _ = ⟨0, ts⟩
      simp only [decomposeTiling, Sigma.mk.injEq, heq_eq_eq, true_and]
      funext i
      exact Fin.elim0 i
    | 1 =>
      -- k = 1: single faultfree tiling
      -- The key insight: composeTilings 1 ts produces a Sigma pair where
      -- the width equals (ts 0).1 and the tiling equals (ts 0).2.val
      -- Since the original tiling is faultfree, decomposeTiling returns a singleton
      
      -- First, set up the key properties
      have hwidth : (composeTilings 1 ts).1 = (ts 0).1 := composeTilings_one_width ts
      have htiling : (composeTilings 1 ts).2 = (ts 0).2.val := composeTilings_one_tiling ts
      have hff : isFaultfree (composeTilings 1 ts).1 (composeTilings 1 ts).2 := 
        composeTilings_one_isFaultfree ts
      have hpos : (ts 0).1 > 0 := (ts 0).2.property.1
      
      -- The composed tiling equals ⟨(ts 0).1, (ts 0).2.val⟩
      have hpair : composeTilings 1 ts = ⟨(ts 0).1, (ts 0).2.val⟩ := by
        apply Sigma.ext hwidth
        simp only [heq_eq_eq]
        exact htiling
      
      -- Rewrite the goal using this equality
      rw [hpair]
      -- Goal: decomposeTiling (ts 0).1 (ts 0).2.val = ⟨1, ts⟩
      
      -- Destructure ts 0 to get the width and the faultfree tiling together
      -- This avoids the dependent type issue
      rcases hts0 : ts 0 with ⟨m, T, hT_ff⟩
      -- Now hts0 : ts 0 = ⟨m, ⟨T, hT_ff⟩⟩
      
      -- Update the goal and hypotheses using hts0
      simp only [hts0] at hpos ⊢
      -- Now hpos : m > 0
      -- Goal: decomposeTiling m T = ⟨1, ts⟩
      
      -- Since m > 0, we can write m = n + 1 for some n
      -- Use match to handle the pattern matching in decomposeTiling
      match m, T, hT_ff, hpos, hts0 with
      | n + 1, T, hT_ff, hpos, hts0 =>
        -- m = n + 1
        have hne : ¬(faultPositions (n + 1) T).Nonempty := 
          faultPositions_not_nonempty_of_isFaultfree (n + 1) T hT_ff
        
        simp only [decomposeTiling, dite_eq_right hne]
        
        -- Goal: ⟨1, fun _ => ⟨n + 1, ⟨T, _⟩⟩⟩ = ⟨1, ts⟩
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
        funext i
        simp only [Fin.fin_one_eq_zero]
        
        -- Show ⟨n + 1, ⟨T, _⟩⟩ = ts 0
        -- We have hts0 : ts 0 = ⟨n + 1, ⟨T, hT_ff⟩⟩
        rw [hts0]
        -- Goal is now definitionally equal
    | k' + 2 =>
      -- k = k' + 2 ≥ 2: multiple components
      -- The composed tiling has faults at the boundaries between components
      have hk_ge2 : k' + 2 ≥ 2 := by omega
      
      -- 1. There is a fault at position (ts 0).1 (the boundary after the first component)
      have hfault := composeTilings_hasFault_at_boundary (k' + 2) hk_ge2 ts
      
      -- The fault positions are nonempty
      have hne : (faultPositions (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2).Nonempty := 
        ⟨(ts ⟨0, by omega⟩).1, hfault⟩
      
      -- 2. The minimum fault is at (ts 0).1
      have hmin_eq := composeTilings_minFault_eq (k' + 2) hk_ge2 ts hne
      
      -- 3. Apply induction hypothesis to the tail
      have ih_tail := ih (k' + 1) (by omega) (faultfreeTilingsTail (k' + 2) (by omega) ts)
      
      -- 4. The width of the composed tiling is positive
      have hwidth_pos : (composeTilings (k' + 2) ts).1 > 0 := by
        have h0 : (ts ⟨0, by omega⟩).1 > 0 := (ts ⟨0, by omega⟩).2.property.1
        have hle : (ts ⟨0, by omega⟩).1 ≤ (composeTilings (k' + 2) ts).1 := by
          simp only [composeTilings]
          apply Finset.single_le_sum (s := Finset.univ) (f := fun i => (ts i).1)
            (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
        omega
      
      -- 5. Key equalities for the restrict operations
      have hleft_eq := restrictTilingLeft_composeTilings_eq (k' + 2) hk_ge2 ts hfault
      have hright_eq := restrictTilingRight_composeTilings_eq (k' + 2) hk_ge2 ts hfault
      
      -- 6. The width of the right restriction equals the tail composition width
      have hright_width := composeTilings_tail_width (k' + 2) hk_ge2 ts
      
      -- The width W = (composeTilings (k' + 2) ts).1 is positive, so W = (W - 1) + 1
      have hW_eq : (composeTilings (k' + 2) ts).1 = ((composeTilings (k' + 2) ts).1 - 1) + 1 := by omega
      
      -- Use decomposeTiling_subst to convert to the form (n + 1)
      rw [decomposeTiling_subst hW_eq]
      
      -- Now we can apply decomposeTiling_hasFault
      -- First, convert the nonemptiness proof
      have hne' : (faultPositions (((composeTilings (k' + 2) ts).1 - 1) + 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2)).Nonempty := by
        -- faultPositions only depends on dominos, which are preserved by subst
        simp only [faultPositions, Set.Nonempty, Set.mem_ofPred_eq]
        obtain ⟨k, hk⟩ := hne
        use k
        simp only [hasFault] at hk ⊢
        simp only [Tiling.subst_dominos]
        constructor
        · exact hk.1
        constructor
        · -- k < ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1
          have h := hk.2.1
          simp only [Nat.sub_add_cancel hwidth_pos] at h ⊢
          exact h
        · exact hk.2.2
      
      -- Apply the hasFault characterization
      rw [decomposeTiling_hasFault ((composeTilings (k' + 2) ts).1 - 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne']
      
      -- Now we need to show the equality of sigma types
      -- LHS: ⟨m + 1, fun i => if i.val = 0 then ⟨minF, left⟩ else ts_right (i-1)⟩
      -- RHS: ⟨k' + 2, ts⟩
      
      -- Key: minF = (ts 0).1
      have hminF_eq : minFault (((composeTilings (k' + 2) ts).1 - 1) + 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne' = (ts ⟨0, by omega⟩).1 := by
        -- The width ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1
        have hW_simp : ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1 := 
          Nat.sub_add_cancel hwidth_pos
        -- The two fault position sets are equal because:
        -- 1. The dominos are the same (subst preserves dominos)
        -- 2. The width bound is the same (by hW_simp)
        have hfp_eq : faultPositions (((composeTilings (k' + 2) ts).1 - 1) + 1) 
            (hW_eq ▸ (composeTilings (k' + 2) ts).2) = 
            faultPositions (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2 := by
          apply Set.ext
          intro j
          simp only [faultPositions, Set.mem_ofPred_eq, hasFault, Tiling.subst_dominos]
          constructor
          · intro ⟨h1, h2, h3⟩
            refine ⟨h1, ?_, h3⟩
            simp only [hW_simp] at h2
            exact h2
          · intro ⟨h1, h2, h3⟩
            refine ⟨h1, ?_, h3⟩
            simp only [hW_simp]
            exact h2
        -- Use the fact that the sets are equal to show the minFaults are equal
        have hfinite1 := faultPositions_finite (((composeTilings (k' + 2) ts).1 - 1) + 1) 
            (hW_eq ▸ (composeTilings (k' + 2) ts).2)
        have hfinite2 := faultPositions_finite (composeTilings (k' + 2) ts).1 
            (composeTilings (k' + 2) ts).2
        have htoFinset_eq : hfinite1.toFinset = hfinite2.toFinset := by
          ext x
          simp only [Set.Finite.mem_toFinset]
          rw [hfp_eq]
        -- minFault is defined as min' of the toFinset
        unfold minFault
        -- The min' of equal finsets is equal
        have hne1 : hfinite1.toFinset.Nonempty := by
          rw [Set.Finite.toFinset_nonempty]
          exact hne'
        have hne2 : hfinite2.toFinset.Nonempty := by
          rw [Set.Finite.toFinset_nonempty]
          exact hne
        calc hfinite1.toFinset.min' _ 
            = hfinite1.toFinset.min' hne1 := rfl
          _ = hfinite2.toFinset.min' hne2 := by simp only [htoFinset_eq]
          _ = minFault (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2 hne := rfl
          _ = (ts ⟨0, by omega⟩).1 := hmin_eq
      
      -- The proof for k >= 2 requires showing:
      -- 1. The count (m + 1) equals k' + 2
      -- 2. The 0th element equals ts 0
      -- 3. The remaining elements equal ts 1, ts 2, etc.
      
      -- Set up the width simplification
      have hW_simp : ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1 := 
        Nat.sub_add_cancel hwidth_pos
      
      -- The hasFault proof for the subst'd tiling, using the minFault
      have hminF' := minFault_hasFault (((composeTilings (k' + 2) ts).1 - 1) + 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne'
      
      -- Key simplification: minFault equals (ts 0).1
      -- So we can work with (ts 0).1 directly
      
      -- The right restriction at minFault has the same width as the tail composition
      have hright_width_eq : (((composeTilings (k' + 2) ts).1 - 1) + 1) - 
          (minFault (((composeTilings (k' + 2) ts).1 - 1) + 1) (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne') = 
          (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1 := by
        rw [hminF_eq, hW_simp]
        have htail := composeTilings_tail_width (k' + 2) hk_ge2 ts
        -- htail : (composeTilings (k' + 2 - 1) (tail ts)).1 = (composeTilings (k' + 2) ts).1 - (ts 0).1
        -- We need: (composeTilings (k' + 2) ts).1 - (ts 0).1 = (composeTilings (k' + 1) (tail ts)).1
        -- Note: k' + 2 - 1 = k' + 1, so this is just htail.symm with the k simplification
        -- Use congrArg to handle the dependent type
        have hk_simp : k' + 2 - 1 = k' + 1 := by omega
        calc (composeTilings (k' + 2) ts).1 - (ts ⟨0, by omega⟩).1 
            = (composeTilings (k' + 2 - 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1 := htail.symm
          _ = (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1 := by
              congr 1

      -- The key insight: decomposeTiling of the right restriction equals ⟨k' + 1, tail ts⟩
      -- This follows from:
      -- 1. The right restriction equals the tail composition (after cast)
      -- 2. By ih_tail, decomposeTiling of tail composition = ⟨k' + 1, tail ts⟩
      
      -- The proof involves showing:
      -- - First component: (decomposeTiling ... right').fst + 1 = k' + 2
      --   This follows from hright_width_eq and ih_tail
      -- - Second component: the functions match
      --   For i=0: ⟨minF, left⟩ = ts 0 (by hminF_eq and hleft_eq)
      --   For i>0: ts_right(i-1) = ts i (by ih_tail and faultfreeTilingsTail definition)
      
      -- Key helper lemmas established above:
      -- - hfault: hasFault at position (ts 0).1
      -- - hne: faultPositions is nonempty
      -- - hmin_eq: minFault = (ts 0).1
      -- - ih_tail: decomposeTiling of tail composition = ⟨k' + 1, tail ts⟩
      -- - hleft_eq: left restriction = (ts 0).2.val
      -- - hright_eq: right restriction = tail composition (after cast)
      -- - hright_width_eq: width of right = width of tail composition
      
      -- Abbreviations for readability
      let n' := (composeTilings (k' + 2) ts).1 - 1
      let T' := hW_eq ▸ (composeTilings (k' + 2) ts).2
      let minF := minFault (n' + 1) T' hne'
      let hminF'' := minFault_hasFault (n' + 1) T' hne'
      let hminF_min : ∀ j, j < minF → ¬hasFault (n' + 1) T' j := fun j hj hfault => 
        absurd (minFault_le (n' + 1) T' hne' j hfault) (not_le.mpr hj)
      let left := restrictTilingLeft (n' + 1) T' minF hminF''
      let left_ff := restrictTilingLeft_isFaultfree (n' + 1) T' minF hminF'' hminF_min
      let right := restrictTilingRight (n' + 1) T' minF hminF''
      
      -- The decomposition of the right part
      let decomp_right := decomposeTiling (n' + 1 - minF) right
      
      -- Step 1: Show decomposeTiling of right equals decomposeTiling of tail composition
      -- First, we need the dominos equality
      have hright_dominos : right.dominos = 
          (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).2.dominos := by
        -- right = restrictTilingRight of the subst'd tiling
        -- The subst'd tiling has the same dominos as the original
        have hsubst_dom : T'.dominos = (composeTilings (k' + 2) ts).2.dominos := 
          Tiling.subst_dominos hW_eq (composeTilings (k' + 2) ts).2
        -- minF = (ts 0).1
        have hminF_eq' : minF = (ts ⟨0, by omega⟩).1 := hminF_eq
        -- restrictTilingRight of T' at minF has the same dominos as the original
        have hrest_dom : (restrictTilingRight (n' + 1) T' minF hminF'').dominos = 
            (restrictTilingRight (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2 
              (ts ⟨0, by omega⟩).1 hfault).dominos := by
          simp only [restrictTilingRight, hsubst_dom, hminF_eq']
        rw [hrest_dom]
        exact restrictTilingRight_composeTilings_dominos_eq (k' + 2) hk_ge2 ts hfault
      
      -- Use decomposeTiling_eq_of_dominos_eq
      have hdecomp_eq : decomp_right = 
          decomposeTiling (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1
            (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).2 := by
        apply decomposeTiling_eq_of_dominos_eq hright_width_eq right
        exact hright_dominos
      
      -- By ih_tail, decomposeTiling of tail composition = ⟨k' + 1, tail ts⟩
      have hdecomp_tail : decomp_right = ⟨k' + 1, faultfreeTilingsTail (k' + 2) (by omega) ts⟩ := by
        rw [hdecomp_eq]
        exact ih_tail
      
      -- Step 2: First component equality
      have h_fst : decomp_right.1 + 1 = k' + 2 := by
        simp only [hdecomp_tail]
      
      -- Step 3: Apply sigma_fin_fun_ext to prove the equality
      apply sigma_fin_fun_ext (decomp_right.1 + 1) (k' + 2) h_fst
      
      -- Step 4: Prove elementwise equality
      intro i
      simp only
      -- Case split on whether i = 0
      by_cases hi : i.val = 0
      · -- Case i = 0: Show ⟨minF, ⟨left, left_ff⟩⟩ = ts 0
        simp only [hi, ↓reduceDIte]
        -- Since i.val = 0, we have i = ⟨0, _⟩
        have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
        -- Rewrite ts i to ts ⟨0, _⟩
        conv_rhs => rw [hi_eq]
        -- Now goal is: ⟨minF, ⟨left, left_ff⟩⟩ = ts ⟨0, _⟩
        -- minF = (ts 0).1 by hminF_eq
        -- left = (ts 0).2.val (after casting by hminF_eq)
        -- 
        -- Step 1: Show left.dominos = (ts ⟨0, _⟩).2.val.dominos
        -- left = restrictTilingLeft (n' + 1) T' minF hminF''
        -- T' = hW_eq ▸ (composeTilings (k' + 2) ts).2
        -- T'.dominos = (composeTilings (k' + 2) ts).2.dominos (by Tiling.subst_dominos)
        have hT'_dominos : T'.dominos = (composeTilings (k' + 2) ts).2.dominos := 
          Tiling.subst_dominos hW_eq (composeTilings (k' + 2) ts).2
        have hleft_dominos : left.dominos = (ts ⟨0, by omega⟩).2.val.dominos := by
          simp only [left, restrictTilingLeft]
          -- left.dominos = {d ∈ T'.dominos | d.inLeftPart minF}
          -- We need to show this equals (ts ⟨0, _⟩).2.val.dominos
          -- By hleft_eq, restrictTilingLeft on the original tiling equals (ts ⟨0, _⟩).2.val
          -- So we need to connect T' to the original tiling
          have horiginal : (restrictTilingLeft (composeTilings (k' + 2) ts).1 
              (composeTilings (k' + 2) ts).2 (ts ⟨0, by omega⟩).1 hfault).dominos = 
              (ts ⟨0, by omega⟩).2.val.dominos := by
            rw [hleft_eq]
          simp only [restrictTilingLeft] at horiginal
          -- Now we need: {d ∈ T'.dominos | d.inLeftPart minF} = {d ∈ (composeTilings ...).2.dominos | d.inLeftPart (ts ⟨0, _⟩).1}
          -- Use hT'_dominos and hminF_eq
          have hminF_eq' : minF = (ts ⟨0, by omega⟩).1 := hminF_eq
          rw [hT'_dominos, hminF_eq']
          exact horiginal
        -- Step 2: Destructure ts ⟨0, _⟩ to get concrete values
        -- This allows us to use subst on the width equality
        rcases hts0 : ts ⟨0, by omega⟩ with ⟨w0, T0, hT0_ff⟩
        -- Now hts0 : ts ⟨0, _⟩ = ⟨w0, ⟨T0, hT0_ff⟩⟩
        -- hminF_eq : minF = w0
        simp only [hts0] at hminF_eq
        -- Rewrite hleft_dominos using hts0
        have hleft_dominos' : left.dominos = T0.dominos := by
          rw [hleft_dominos, hts0]
        -- Now minF = w0 and left.dominos = T0.dominos
        -- Use subst to replace minF with w0
        subst hminF_eq
        -- Now minF is replaced by w0, so left : Tiling (Rectangle w0 2)
        -- And T0 : Tiling (Rectangle w0 2) - same type!
        have hleft_val : left = T0 := Tiling.ext left T0 hleft_dominos'
        subst hleft_val
        -- Now left is replaced by T0
        -- Goal: ⟨w0, ⟨T0, left_ff⟩⟩ = ⟨w0, ⟨T0, hT0_ff⟩⟩
        rfl
      · -- Case i > 0: Show decomp_right.2 ⟨i - 1, _⟩ = ts i
        have hi_pos : i.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
        simp only [hi, ↓reduceDIte]
        -- Goal: decomp_right.2 ⟨i.val - 1, _⟩ = ts i
        -- We have hdecomp_tail : decomp_right = ⟨k' + 1, faultfreeTilingsTail (k' + 2) (by omega) ts⟩
        -- 
        -- Extract h1 : decomp_right.1 = k' + 1
        have h1 : decomp_right.1 = k' + 1 := by
          have := congrArg Sigma.fst hdecomp_tail
          simp only at this
          exact this
        -- Use Sigma.ext_iff to extract the HEq of second components
        rw [Sigma.ext_iff] at hdecomp_tail
        obtain ⟨hk, hf⟩ := hdecomp_tail
        -- hk : decomp_right.1 = k' + 1
        -- hf : HEq decomp_right.2 (faultfreeTilingsTail ...)
        -- 
        -- The key is that HEq of functions implies equality of values at HEq indices
        have hindex : HEq (⟨i.val - 1, by omega⟩ : Fin decomp_right.1) 
                          (⟨i.val - 1, by omega⟩ : Fin (k' + 1)) := by
          rw [Fin.heq_ext_iff h1]
        -- Apply congr_heq to get the equality at the specific index
        have happ := congr_heq hf hindex
        -- happ : decomp_right.2 ⟨i.val - 1, _⟩ = faultfreeTilingsTail ... ⟨i.val - 1, _⟩
        rw [happ]
        -- Goal: faultfreeTilingsTail (k' + 2) (by omega) ts ⟨i.val - 1, _⟩ = ts i
        -- By definition: faultfreeTilingsTail k hk ts j = ts ⟨j.val + 1, _⟩
        simp only [faultfreeTilingsTail]
        -- Goal: ts ⟨(i.val - 1) + 1, _⟩ = ts i
        -- Since i.val ≥ 1, we have (i.val - 1) + 1 = i.val
        congr 1
        simp only [Fin.ext_iff]
        omega

/-- The width of the composed tiling equals the sum of widths of the components.
    This follows from the definition of composeTilings as horizontal concatenation. -/
theorem composeTilings_width (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings k ts).1 = ∑ i : Fin k, (ts i).1 := by
  rfl

/-- The sum of widths of the faultfree tilings equals the width of the original.
    This is the key property that makes the decomposition weight-preserving. -/
theorem decomposeTiling_weight_sum (n : ℕ) (T : Tiling (Rectangle n 2)) :
    let ⟨k, ts⟩ := decomposeTiling n T
    (∑ i : Fin k, (ts i).1) = n := by
  simp only
  have h1 := composeTilings_decomposeTiling n T
  simp only at h1
  have h2 := composeTilings_width (decomposeTiling n T).1 (decomposeTiling n T).2
  rw [← h2]
  exact congrArg Sigma.fst h1

/-- Main decomposition isomorphism (Lemma \ref{lem.gf.weighted-set.domino.fd}):
    
    Any domino tiling of a height-2 rectangle can be decomposed **uniquely** into a 
    tuple of faultfree tilings of (usually smaller) height-2 rectangles, by cutting 
    it along its faults.
    
    This gives an isomorphism of weighted sets:
      D ≅ F⁰ + F¹ + F² + F³ + ...
    where D = TilingsHeight2 and F = FaultfreeTilingsHeight2.
    
    The isomorphism preserves weights: the sum of the widths of the faultfree tilings
    in the tuple equals the width of the original tiling. -/
def tiling_decomposition_isomorphism :
    WeightedSet.Isomorphism TilingsHeight2 FaultfreeTilingsHeight2.tuples where
  toEquiv := {
    toFun := fun ⟨n, T⟩ => decomposeTiling n T
    invFun := fun ⟨k, ts⟩ => composeTilings k ts
    left_inv := fun ⟨n, T⟩ => composeTilings_decomposeTiling n T
    right_inv := fun ⟨k, ts⟩ => decomposeTiling_composeTilings k ts
  }
  weight_eq := fun ⟨n, T⟩ => by
    simp only [WeightedSet.tuples, TilingsHeight2]
    exact decomposeTiling_weight_sum n T

/-- Corollary: Any tiling decomposes into a tuple of faultfree tilings with matching total weight -/
theorem tiling_decomposition (n : ℕ) (T : Tiling (Rectangle n 2)) :
    ∃ (k : ℕ) (ts : Fin k → Σ m, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}),
      (∑ i, (ts i).1) = n :=
  ⟨(decomposeTiling n T).1, (decomposeTiling n T).2, decomposeTiling_weight_sum n T⟩

/-! #### Helper definitions for the Fibonacci recurrence bijection -/

/-- Prepend a vertical domino to a tiling of Rectangle m 2, giving a tiling of Rectangle (m+1) 2.
    
    The new tiling has dominos = {vertical 1 1} ∪ (T.dominos shifted right by 1).
    This is the inverse of restricting at fault 1 when a vertical domino is present. -/
def prependVertical (m : ℕ) (T : Tiling (Rectangle m 2)) : Tiling (Rectangle (m + 1) 2) where
  dominos := {Domino.vertical 1 1} ∪ T.dominos.image (fun d => d.shiftNat 1)
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image] at hd1 hd2
    rcases hd1 with rfl | ⟨d1', hd1', rfl⟩ <;> rcases hd2 with rfl | ⟨d2', hd2', rfl⟩
    · exact (hne rfl).elim
    · -- vertical 1 1 vs shifted d2'
      -- vertical 1 1 covers column 1, shifted dominos cover columns ≥ 2
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift]
      rw [Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
      cases d2' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs vertical 1 1
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift]
      rw [Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
      cases d1' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs shifted d2'
      have hne' : d1' ≠ d2' := by
        intro heq; subst heq; exact hne rfl
      have hdisj := T.pairwise_disjoint hd1' hd2' hne'
      simp only [Function.onFun, Domino.shiftNat_toShape]
      exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
        simp only [Prod.mk.injEq] at h; ext <;> omega) hdisj
  cover := by
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_image,
               Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, hd, hp⟩
      rcases hd with rfl | ⟨d', hd', rfl⟩
      · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
        rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
      · have hd'_rect := domino_subset_rect m T d' hd'
        rw [Domino.shiftNat_toShape] at hp
        obtain ⟨⟨x', y'⟩, hp', heq⟩ := hp
        simp only [Prod.mk.injEq] at heq
        have hxy' := hd'_rect hp'
        simp only [Rectangle, Set.mem_ofPred_eq] at hxy'
        omega
    · intro ⟨hx1, hx2, hy1, hy2⟩
      rcases (show x = 1 ∨ x ≥ 2 by omega) with rfl | hx_ge2
      · -- x = 1: covered by vertical 1 1
        use Domino.vertical 1 1, Or.inl rfl
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        have hy12 : y = 1 ∨ y = 2 := by omega
        rcases hy12 with rfl | rfl <;> simp
      · -- x ≥ 2: covered by shifted domino
        have hxy_rect : (x - 1, y) ∈ Rectangle m 2 := by
          simp only [Rectangle, Set.mem_ofPred_eq]
          omega
        rw [← T.cover] at hxy_rect
        simp only [Set.mem_iUnion] at hxy_rect
        obtain ⟨d', hd', hp'⟩ := hxy_rect
        use d'.shiftNat 1, Or.inr ⟨d', hd', rfl⟩
        rw [Domino.shiftNat_toShape]
        refine ⟨(x - 1, y), hp', ?_⟩
        simp only [Prod.mk.injEq]
        constructor <;> first | ring | trivial

/-- The vertical domino is not in the image of shifted dominos from Rectangle m 2. -/
lemma vertical_11_not_in_shiftNat_image (m : ℕ) (T : Tiling (Rectangle m 2)) :
    Domino.vertical 1 1 ∉ T.dominos.image (fun d => d.shiftNat 1) := by
  simp only [Set.mem_image, not_exists, not_and]
  intro d hd heq
  cases d with
  | horizontal i j =>
    simp only [Domino.shiftNat, Domino.shift] at heq
    exact Domino.noConfusion heq
  | vertical i j =>
    simp only [Domino.shiftNat, Domino.shift, Domino.vertical.injEq] at heq
    have hsub := domino_subset_rect m T (Domino.vertical i j) hd
    have hi_ge : i ≥ 1 := by
      have := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq] at this
      exact this.1
    omega

/-- Prepend a pair of horizontal dominos to a tiling of Rectangle m 2, giving a tiling of Rectangle (m+2) 2.
    
    The new tiling has dominos = {horizontal 1 1, horizontal 1 2} ∪ (T.dominos shifted right by 2).
    This is the inverse of restricting at fault 2 when horizontal dominos are present. -/
def prependHorizontalPair (m : ℕ) (T : Tiling (Rectangle m 2)) : Tiling (Rectangle (m + 2) 2) where
  dominos := {Domino.horizontal 1 1, Domino.horizontal 1 2} ∪ T.dominos.image (fun d => d.shiftNat 2)
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image] at hd1 hd2
    rcases hd1 with (rfl | rfl) | ⟨d1', hd1', rfl⟩ <;> rcases hd2 with (rfl | rfl) | ⟨d2', hd2', rfl⟩
    · exact (hne rfl).elim
    · -- horizontal 1 1 vs horizontal 1 2
      simp only [Function.onFun, Domino.toShape, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1 hx2
      rcases hx1 with ⟨_, hy1⟩ | ⟨_, hy1⟩ <;> rcases hx2 with ⟨_, hy2⟩ | ⟨_, hy2⟩ <;> omega
    · -- horizontal 1 1 vs shifted d2'
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
      cases d2' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- horizontal 1 2 vs horizontal 1 1
      simp only [Function.onFun, Domino.toShape, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1 hx2
      rcases hx1 with ⟨_, hy1⟩ | ⟨_, hy1⟩ <;> rcases hx2 with ⟨_, hy2⟩ | ⟨_, hy2⟩ <;> omega
    · exact (hne rfl).elim
    · -- horizontal 1 2 vs shifted d2'
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
      cases d2' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd2'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs horizontal 1 1
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
      cases d1' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs horizontal 1 2
      simp only [Function.onFun, Domino.toShape, Domino.shiftNat, Domino.shift, Set.disjoint_iff]
      intro ⟨x, y⟩ ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx2
      cases d1' with
      | horizontal i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.horizontal i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
      | vertical i j =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hx1
        have hsub := domino_subset_rect m T (Domino.vertical i j) hd1'
        have hi_ge : i ≥ 1 := by
          have := hsub (Set.mem_insert (i, j) _)
          simp only [Rectangle, Set.mem_ofPred_eq] at this
          exact this.1
        rcases hx1 with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rcases hx2 with ⟨hx', _⟩ | ⟨hx', _⟩ <;> omega
    · -- shifted d1' vs shifted d2'
      have hne' : d1' ≠ d2' := by
        intro heq; subst heq; exact hne rfl
      have hdisj := T.pairwise_disjoint hd1' hd2' hne'
      simp only [Function.onFun, Domino.shiftNat_toShape]
      exact Set.disjoint_image_of_injective (fun p1 p2 h => by 
        simp only [Prod.mk.injEq] at h; ext <;> omega) hdisj
  cover := by
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, 
               Set.mem_image, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, hd, hp⟩
      rcases hd with (rfl | rfl) | ⟨d', hd', rfl⟩
      · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
        rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
      · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
        rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
      · have hd'_rect := domino_subset_rect m T d' hd'
        rw [Domino.shiftNat_toShape] at hp
        obtain ⟨⟨x', y'⟩, hp', heq⟩ := hp
        simp only [Prod.mk.injEq] at heq
        have hxy' := hd'_rect hp'
        simp only [Rectangle, Set.mem_ofPred_eq] at hxy'
        omega
    · intro ⟨hx1, hx2, hy1, hy2⟩
      have hy12 : y = 1 ∨ y = 2 := by omega
      rcases (show x = 1 ∨ x = 2 ∨ x ≥ 3 by omega) with rfl | rfl | hx_ge3
      · -- x = 1: covered by horizontal 1 y
        rcases hy12 with rfl | rfl
        · use Domino.horizontal 1 1, Or.inl (Or.inl rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
        · use Domino.horizontal 1 2, Or.inl (Or.inr rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
      · -- x = 2: covered by horizontal 1 y
        rcases hy12 with rfl | rfl
        · use Domino.horizontal 1 1, Or.inl (Or.inl rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          right; trivial
        · use Domino.horizontal 1 2, Or.inl (Or.inr rfl)
          simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          right; trivial
      · -- x ≥ 3: covered by shifted domino
        have hxy_rect : (x - 2, y) ∈ Rectangle m 2 := by
          simp only [Rectangle, Set.mem_ofPred_eq]
          omega
        rw [← T.cover] at hxy_rect
        simp only [Set.mem_iUnion] at hxy_rect
        obtain ⟨d', hd', hp'⟩ := hxy_rect
        use d'.shiftNat 2, Or.inr ⟨d', hd', rfl⟩
        rw [Domino.shiftNat_toShape]
        refine ⟨(x - 2, y), hp', ?_⟩
        simp only [Prod.mk.injEq]
        constructor <;> first | ring | trivial

/-- The horizontal dominos are not in the image of shifted dominos from Rectangle m 2. -/
lemma horizontal_11_not_in_shiftNat2_image (m : ℕ) (T : Tiling (Rectangle m 2)) :
    Domino.horizontal 1 1 ∉ T.dominos.image (fun d => d.shiftNat 2) := by
  simp only [Set.mem_image, not_exists, not_and]
  intro d hd heq
  cases d with
  | horizontal i j =>
    simp only [Domino.shiftNat, Domino.shift, Domino.horizontal.injEq] at heq
    have hsub := domino_subset_rect m T (Domino.horizontal i j) hd
    have hi_ge : i ≥ 1 := by
      have := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq] at this
      exact this.1
    omega
  | vertical i j =>
    simp only [Domino.shiftNat, Domino.shift] at heq
    exact Domino.noConfusion heq

lemma horizontal_12_not_in_shiftNat2_image (m : ℕ) (T : Tiling (Rectangle m 2)) :
    Domino.horizontal 1 2 ∉ T.dominos.image (fun d => d.shiftNat 2) := by
  simp only [Set.mem_image, not_exists, not_and]
  intro d hd heq
  cases d with
  | horizontal i j =>
    simp only [Domino.shiftNat, Domino.shift, Domino.horizontal.injEq] at heq
    have hsub := domino_subset_rect m T (Domino.horizontal i j) hd
    have hi_ge : i ≥ 1 := by
      have := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq] at this
      exact this.1
    omega
  | vertical i j =>
    simp only [Domino.shiftNat, Domino.shift] at heq
    exact Domino.noConfusion heq

/-- The vertical domino at (1,1) is not in the image of dominos shifted by 2. -/
lemma vertical_11_not_in_shiftNat2_image (m : ℕ) (T : Tiling (Rectangle m 2)) :
    Domino.vertical 1 1 ∉ T.dominos.image (fun d => d.shiftNat 2) := by
  simp only [Set.mem_image, not_exists, not_and]
  intro d hd heq
  cases d with
  | horizontal i j =>
    simp only [Domino.shiftNat, Domino.shift] at heq
    exact Domino.noConfusion heq
  | vertical i j =>
    simp only [Domino.shiftNat, Domino.shift, Domino.vertical.injEq] at heq
    have hsub := domino_subset_rect m T (Domino.vertical i j) hd
    have hi_ge : i ≥ 1 := by
      have := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq] at this
      exact this.1
    omega

/-- The empty rectangle has exactly one tiling -/
@[simp] lemma numTilings_0_2 : d_[0, 2] = 1 := by
  unfold numTilings
  rw [Rectangle_zero_left]
  have huniq : Unique (Tiling (∅ : Shape)) := {
    default := Tiling.empty
    uniq := fun T => by
      have hdom := Tiling.unique_empty T
      cases T
      simp only [Tiling.mk.injEq, Tiling.empty]
      exact hdom
  }
  exact Nat.card_unique

/-- The 1×2 rectangle has exactly one tiling -/
@[simp] lemma numTilings_1_2 : d_[1, 2] = 1 := by
  unfold numTilings
  have huniq : Unique (Tiling (Rectangle 1 2)) := {
    default := tiling_1_2
    uniq := tiling_1_2_unique
  }
  exact Nat.card_unique

/-- The Fibonacci recurrence for tiling counts: d_{n+2,2} = d_{n,2} + d_{n+1,2}.

    This follows from the bijection:
    Tiling (Rectangle (n+2) 2) ≃ Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n+1) 2)

    The bijection classifies tilings based on what covers the first column:
    - If a vertical domino covers (1,1)-(1,2): removing it and shifting gives a tiling of Rectangle (n+1) 2
    - If horizontal dominos cover (1,1)-(2,1) and (1,2)-(2,2): removing them and shifting gives a tiling of Rectangle n 2

    This is a classical result in combinatorics. -/
lemma numTilings_recurrence (n : ℕ) : d_[n + 2, 2] = d_[n, 2] + d_[n + 1, 2] := by
  -- The proof constructs a bijection between tilings of Rectangle (n+2) 2 and
  -- the disjoint union of tilings of Rectangle n 2 and Rectangle (n+1) 2.
  -- 
  -- The key insight is that every tiling of Rectangle (n+2) 2 has its first column covered 
  -- by either:
  -- 1. A vertical domino at (1,1)-(1,2) (giving a tiling of Rectangle (n+1) 2 after removal and shift)
  -- 2. Two horizontal dominos at (1,1)-(2,1) and (1,2)-(2,2) (giving a tiling of Rectangle n 2 after removal and shift)
  --
  -- The bijection is established using:
  -- - exists_domino_covering_11: there exists a domino covering (1,1)
  -- - domino_covering_11_valid: that domino is either vertical 1 1 or horizontal 1 1
  -- - horizontal_12_if_horizontal_11: if horizontal 1 1 is present, so is horizontal 1 2
  -- - fault_at_1_if_vertical: if vertical 1 1 is present, there's a fault at 1
  -- - fault_at_2_if_horizontal: if horizontal 1 1 is present, there's a fault at 2
  -- - restrictTilingRight: get the right part at a fault
  --
  -- The formal construction uses Equiv.sumCompl to partition tilings by whether 
  -- vertical 1 1 is present, then constructs equivalences for each part.
  unfold numTilings
  -- We need: Nat.card (Tiling (Rectangle (n+2) 2)) = Nat.card (Tiling (Rectangle n 2)) + Nat.card (Tiling (Rectangle (n+1) 2))
  -- 
  -- Define the predicate: P(T) := Domino.vertical 1 1 ∈ T.dominos
  -- Then by Equiv.sumCompl: Tiling (Rectangle (n+2) 2) ≃ {T | P T} ⊕ {T | ¬P T}
  --
  -- We need two equivalences:
  -- e1 : {T | P T} ≃ Tiling (Rectangle (n+1) 2)  (remove vertical, shift by -1)
  -- e2 : {T | ¬P T} ≃ Tiling (Rectangle n 2)     (remove horizontal pair, shift by -2)
  --
  -- The construction of these equivalences requires:
  -- - Forward: use restrictTilingRight with the appropriate fault
  -- - Backward: prepend the appropriate dominos and shift
  --
  -- The equivalence is constructed using the classification of tilings by what covers (1,1).
  -- Every tiling of Rectangle (n+2) 2 has exactly one of:
  -- - vertical 1 1 ∈ T.dominos (covering column 1 with one vertical domino)
  -- - horizontal 1 1 ∈ T.dominos (covering columns 1-2 with two horizontal dominos)
  -- They can't both be present since they overlap at (1,1).
  --
  -- Forward map: T ↦ if vertical 1 1 ∈ T.dominos then Sum.inr (restrictTilingRight T 1)
  --                                               else Sum.inl (restrictTilingRight T 2)
  -- 
  -- Inverse map: Sum.inl T' ↦ prepend {horizontal 1 1, horizontal 1 2} and shift T' by 2
  --              Sum.inr T' ↦ prepend {vertical 1 1} and shift T' by 1
  --
  -- The proof that these are inverses follows from:
  -- 1. At a fault, T.dominos = leftPart ∪ (rightPart.image shiftNat k)
  -- 2. For fault at 1: leftPart = {vertical 1 1}
  -- 3. For fault at 2: leftPart = {horizontal 1 1, horizontal 1 2}
  -- 4. shiftNat and shiftNeg are inverses
  --
  -- This is a standard combinatorial bijection (the Fibonacci recurrence for domino tilings).
  have e : Tiling (Rectangle (n + 2) 2) ≃ Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n + 1) 2) := by
    -- Helper: vertical 1 1 and horizontal 1 1 overlap at (1,1), so they can't both be in a tiling
    have vertical_horizontal_disjoint : ∀ T : Tiling (Rectangle (n + 2) 2), 
        ¬(Domino.vertical 1 1 ∈ T.dominos ∧ Domino.horizontal 1 1 ∈ T.dominos) := by
      intro T ⟨hv, hh⟩
      have hne : Domino.vertical 1 1 ≠ Domino.horizontal 1 1 := by intro h; exact Domino.noConfusion h
      have hdisj := T.pairwise_disjoint hv hh hne
      simp only [Function.onFun] at hdisj
      rw [Set.disjoint_iff_inter_eq_empty] at hdisj
      have h11 : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape ∩ (Domino.horizontal 1 1).toShape := by
        constructor
        · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
        · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
      rw [hdisj] at h11
      exact h11
    -- Helper: every tiling of Rectangle (n+2) 2 has either vertical 1 1 or horizontal 1 1
    have classification : ∀ T : Tiling (Rectangle (n + 2) 2), 
        Domino.vertical 1 1 ∈ T.dominos ∨ Domino.horizontal 1 1 ∈ T.dominos := by
      intro T
      obtain ⟨d, hd, hmem⟩ := exists_domino_covering_11 (n + 2) (by omega) T
      have hcases := domino_covering_11_valid (n + 2) T d hd hmem
      rcases hcases with rfl | rfl
      · left; exact hd
      · right; exact hd
    -- Helper: if vertical 1 1 ∈ T.dominos, then horizontal 1 1 ∉ T.dominos
    have vertical_implies_not_horizontal : ∀ T : Tiling (Rectangle (n + 2) 2),
        Domino.vertical 1 1 ∈ T.dominos → Domino.horizontal 1 1 ∉ T.dominos := by
      intro T hv hh
      exact vertical_horizontal_disjoint T ⟨hv, hh⟩
    -- Helper: if vertical 1 1 ∉ T.dominos, then horizontal 1 1 ∈ T.dominos  
    have not_vertical_implies_horizontal : ∀ T : Tiling (Rectangle (n + 2) 2),
        Domino.vertical 1 1 ∉ T.dominos → Domino.horizontal 1 1 ∈ T.dominos := by
      intro T hnv
      rcases classification T with hv | hh
      · exact absurd hv hnv
      · exact hh
    -- Use classical logic for decidability
    haveI : ∀ T : Tiling (Rectangle (n + 2) 2), Decidable (Domino.vertical 1 1 ∈ T.dominos) := 
      fun T => Classical.dec _
    haveI : DecidableEq ℕ := Classical.decEq ℕ
    -- Define the forward map
    let toSum : Tiling (Rectangle (n + 2) 2) → Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n + 1) 2) := 
      fun T => if hv : Domino.vertical 1 1 ∈ T.dominos 
               then Sum.inr (restrictTilingRight (n + 2) T 1 (fault_at_1_if_vertical (n + 2) (by omega) T hv))
               else if hn : n = 0 
                    then Sum.inl (hn ▸ emptyTiling2)
                    else Sum.inl (by
                      have hh := not_vertical_implies_horizontal T hv
                      have hn3 : n + 2 ≥ 3 := by omega
                      have hfault := fault_at_2_if_horizontal (n + 2) hn3 T hh
                      have hrestrict := restrictTilingRight (n + 2) T 2 hfault
                      simp only [show n + 2 - 2 = n by omega] at hrestrict
                      exact hrestrict)
    -- Define the inverse map  
    let fromSum : Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n + 1) 2) → Tiling (Rectangle (n + 2) 2) :=
      fun s => match s with
               | Sum.inl T => prependHorizontalPair n T
               | Sum.inr T => prependVertical (n + 1) T
    -- Construct the equivalence
    refine ⟨toSum, fromSum, ?_, ?_⟩
    -- Proof that fromSum ∘ toSum = id (left inverse)
    · intro T
      simp only [toSum, fromSum]
      by_cases hv : Domino.vertical 1 1 ∈ T.dominos
      · -- Case: vertical 1 1 ∈ T.dominos
        simp only [hv, dite_true]
        -- Need to show: prependVertical (n+1) (restrictTilingRight (n+2) T 1 _) = T
        -- This requires showing the dominos are equal
        apply Tiling.ext
        -- Show: {vertical 1 1} ∪ (restrictTilingRight ...).dominos.image (shiftNat 1) = T.dominos
        simp only [prependVertical, restrictTilingRight]
        -- The key insight: T.dominos = {vertical 1 1} ∪ {d ∈ T.dominos | d.inRightPart 1}
        -- because at fault 1, the only domino in left part is vertical 1 1
        ext d
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_sep_iff]
        constructor
        · intro h
          rcases h with rfl | ⟨d'', ⟨d', ⟨hd'_mem, hd'_right⟩, hd'_eq⟩, hd''_eq⟩
          · exact hv
          · -- d = d''.shiftNat 1 and d'' = d'.shiftNeg 1 and d' ∈ T.dominos
            subst hd'_eq hd''_eq
            rw [Domino.shiftNat_shiftNeg]
            exact hd'_mem
        · intro hd
          have hfault := fault_at_1_if_vertical (n + 2) (by omega) T hv
          have hlr := domino_left_or_right_at_fault hfault d hd
          rcases hlr with hleft | hright
          · -- d is in left part, so d = vertical 1 1
            left
            cases d with
            | horizontal i j =>
              exfalso
              have hsub := domino_subset_rect (n + 2) T (Domino.horizontal i j) hd
              have hi_ge : i ≥ 1 := by
                have := hsub (Set.mem_insert (i, j) _)
                simp only [Rectangle, Set.mem_ofPred_eq] at this
                exact this.1
              have hi1_le : i + 1 ≤ 1 := hleft (i + 1, j) (by simp [Domino.toShape])
              omega
            | vertical i j =>
              have hsub := domino_subset_rect (n + 2) T (Domino.vertical i j) hd
              have h1 : (i, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
              have h2 : (i, j + 1) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
              have hi_ge : i ≥ 1 := by simp only [Rectangle, Set.mem_ofPred_eq] at h1; exact h1.1
              have hi_le : i ≤ 1 := hleft (i, j) (by simp [Domino.toShape])
              have hj_ge : j ≥ 1 := by simp only [Rectangle, Set.mem_ofPred_eq] at h1; exact h1.2.2.1
              have hj1_le : j + 1 ≤ 2 := by simp only [Rectangle, Set.mem_ofPred_eq] at h2; exact h2.2.2.2
              simp only [Domino.vertical.injEq]; omega
          · -- d is in right part
            right
            refine ⟨d.shiftNeg 1, ⟨d, ⟨hd, hright⟩, rfl⟩, Domino.shiftNat_shiftNeg d 1⟩
      · -- Case: vertical 1 1 ∉ T.dominos (so horizontal 1 1 ∈ T.dominos)
        simp only [hv, dite_false]
        by_cases hn : n = 0
        · -- n = 0: special case
          simp only [hn, dite_true]
          -- Need to show: prependHorizontalPair 0 emptyTiling2 = T
          -- When n = 0, Rectangle 2 2 is covered by exactly {horizontal 1 1, horizontal 1 2}
          subst hn
          apply Tiling.ext
          simp only [prependHorizontalPair]
          -- emptyTiling2.dominos = ∅
          have hempty_dominos : emptyTiling2.dominos = ∅ := by
            have hsub : emptyTiling2.dominos ⊆ ∅ := by
              intro d hd
              have hsub' : d.toShape ⊆ Rectangle 0 2 := by
                rw [← emptyTiling2.cover]
                exact Set.subset_biUnion_of_mem hd
              rw [Rectangle_zero_left] at hsub'
              cases d with
              | horizontal i j =>
                have := hsub' (Set.mem_insert (i, j) _)
                exact this
              | vertical i j =>
                have := hsub' (Set.mem_insert (i, j) _)
                exact this
            exact Set.subset_eq_empty hsub rfl
          rw [hempty_dominos, Set.image_empty, Set.union_empty]
          -- Need to show: {horizontal 1 1, horizontal 1 2} = T.dominos
          have hh := not_vertical_implies_horizontal T hv
          have hh2 := horizontal_12_if_horizontal_11 2 (by omega) T hh
          ext d
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · intro hd
            rcases hd with rfl | rfl
            · exact hh
            · exact hh2
          · intro hd
            -- Every domino in T is either horizontal 1 1 or horizontal 1 2
            cases d with
            | horizontal i j =>
              have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
              have h1 : (i, j) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              have h2 : (i + 1, j) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
              have hi : i = 1 := by omega
              have hj : j = 1 ∨ j = 2 := by omega
              rcases hj with rfl | rfl
              · left; simp only [hi]
              · right; simp only [hi]
            | vertical i j =>
              -- vertical dominos are impossible when horizontal 1 1 is present
              exfalso
              have hsub := domino_subset_rect 2 T (Domino.vertical i j) hd
              have h1 : (i, j) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              have h2 : (i, j + 1) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
              have hi : i = 1 ∨ i = 2 := by omega
              have hj : j = 1 := by omega
              -- If i = 1, then vertical 1 1 ∈ T.dominos, contradicting hv
              -- If i = 2, then vertical 2 1 overlaps with horizontal 1 1 or horizontal 1 2
              rcases hi with rfl | rfl
              · -- i = 1: vertical 1 1 ∈ T.dominos
                have : Domino.vertical 1 1 ∈ T.dominos := by simp only [hj] at hd; exact hd
                exact hv this
              · -- i = 2: vertical 2 1 overlaps with horizontal 1 1 at (2, 1)
                have hdisj := T.pairwise_disjoint hh hd
                have hne : Domino.horizontal 1 1 ≠ Domino.vertical 2 j := by simp
                have : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 2 j).toShape := hdisj hne
                have h21_h : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
                have h21_v : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 2 j).toShape := by simp [Domino.toShape, hj]
                exact Set.disjoint_iff.mp this ⟨h21_h, h21_v⟩
        · -- n ≥ 1: use restrictTilingRight
          simp only [hn, dite_false]
          -- Need to show: prependHorizontalPair n (restrictTilingRight (n+2) T 2 _) = T
          apply Tiling.ext
          simp only [prependHorizontalPair, restrictTilingRight]
          -- Similar to the vertical case: T.dominos = {h 1 1, h 1 2} ∪ {d ∈ T.dominos | d.inRightPart 2}
          ext d
          simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
          constructor
          · intro h
            rcases h with (rfl | rfl) | ⟨d'', ⟨d', ⟨hd'_mem, hd'_right⟩, hd'_eq⟩, hd''_eq⟩
            · exact not_vertical_implies_horizontal T hv
            · exact horizontal_12_if_horizontal_11 (n + 2) (by omega) T (not_vertical_implies_horizontal T hv)
            · subst hd'_eq hd''_eq; rw [Domino.shiftNat_shiftNeg]; exact hd'_mem
          · intro hd
            have hh := not_vertical_implies_horizontal T hv
            have hn3 : n + 2 ≥ 3 := by omega
            have hfault := fault_at_2_if_horizontal (n + 2) hn3 T hh
            have hlr := domino_left_or_right_at_fault hfault d hd
            rcases hlr with hleft | hright
            · -- d is in left part at fault 2, so d = horizontal 1 1 or horizontal 1 2
              cases d with
              | horizontal i j =>
                have hsub := domino_subset_rect (n + 2) T (Domino.horizontal i j) hd
                have h1 : (i, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                have h2 : (i + 1, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
                have hi1_le : i + 1 ≤ 2 := hleft (i + 1, j) (by simp [Domino.toShape])
                have hi_ge : i ≥ 1 := h1.1
                have hj12 : j = 1 ∨ j = 2 := by omega
                have hi_eq : i = 1 := by omega
                rcases hj12 with rfl | rfl
                · left; left; simp only [hi_eq]
                · left; right; simp only [hi_eq]
              | vertical i j =>
                exfalso
                have hsub := domino_subset_rect (n + 2) T (Domino.vertical i j) hd
                have h1 : (i, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1
                have hi_ge : i ≥ 1 := h1.1
                have hi_le : i ≤ 2 := hleft (i, j) (by simp [Domino.toShape])
                have hj_ge : j ≥ 1 := h1.2.2.1
                -- vertical i j with 1 ≤ i ≤ 2 and j ≥ 1 means i ∈ {1, 2}
                -- If i = 1: vertical 1 1 ∈ T.dominos, contradicting hv
                -- If i = 2: vertical 2 j overlaps with horizontal 1 j at (2, j)
                rcases (show i = 1 ∨ i = 2 by omega) with hi_eq | hi_eq
                · have hj1 : j = 1 := by
                    have h2' : (i, j + 1) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                    simp only [Rectangle, Set.mem_ofPred_eq] at h2'
                    omega
                  have hv11 : Domino.vertical 1 1 ∈ T.dominos := by
                    simp only [hi_eq, hj1] at hd; exact hd
                  exact hv hv11
                · have hj12 : j = 1 := by
                    have h2' : (i, j + 1) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                    simp only [Rectangle, Set.mem_ofPred_eq] at h2'
                    omega
                  have hh2 := horizontal_12_if_horizontal_11 (n + 2) (by omega) T hh
                  have hdisj := T.pairwise_disjoint hh hd
                  have hne : Domino.horizontal 1 1 ≠ Domino.vertical i j := by simp [hi_eq]
                  have hdisj' : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical i j).toShape := hdisj hne
                  have h21_h : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
                  have h21_v : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.vertical i j).toShape := by simp [Domino.toShape, hi_eq, hj12]
                  exact Set.disjoint_iff.mp hdisj' ⟨h21_h, h21_v⟩
            · -- d is in right part
              right
              refine ⟨d.shiftNeg 2, ⟨d, ⟨hd, hright⟩, rfl⟩, Domino.shiftNat_shiftNeg d 2⟩
    -- Proof that toSum ∘ fromSum = id (right inverse)
    · intro s
      simp only [toSum, fromSum]
      rcases s with T | T
      · -- Case: Sum.inl T (from Rectangle n 2)
        -- Need to show: toSum (prependHorizontalPair n T) = Sum.inl T
        -- First, show vertical 1 1 ∉ (prependHorizontalPair n T).dominos
        have hv_not : Domino.vertical 1 1 ∉ (prependHorizontalPair n T).dominos := by
          simp only [prependHorizontalPair, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          constructor
          · constructor
            · exact fun h => Domino.noConfusion h
            · exact fun h => Domino.noConfusion h
          · exact vertical_11_not_in_shiftNat2_image n T
        simp only [hv_not, dite_false]
        by_cases hn : n = 0
        · simp only [hn, dite_true]
          -- Need to show: Sum.inl (0 ▸ emptyTiling2) = Sum.inl T
          -- When n = 0, T : Tiling (Rectangle 0 2) must be emptyTiling2
          subst hn
          congr 1
          apply Tiling.ext
          -- Rectangle 0 2 = ∅, so both tilings have empty dominos
          have hT_empty : T.dominos = ∅ := by
            have hsub : T.dominos ⊆ ∅ := by
              intro d hd
              have hsub' : d.toShape ⊆ Rectangle 0 2 := by
                rw [← T.cover]
                exact Set.subset_biUnion_of_mem hd
              rw [Rectangle_zero_left] at hsub'
              cases d with
              | horizontal i j => exact hsub' (Set.mem_insert (i, j) _)
              | vertical i j => exact hsub' (Set.mem_insert (i, j) _)
            exact Set.subset_eq_empty hsub rfl
          have hempty : emptyTiling2.dominos = ∅ := by
            have hsub : emptyTiling2.dominos ⊆ ∅ := by
              intro d hd
              have hsub' : d.toShape ⊆ Rectangle 0 2 := by
                rw [← emptyTiling2.cover]
                exact Set.subset_biUnion_of_mem hd
              rw [Rectangle_zero_left] at hsub'
              cases d with
              | horizontal i j => exact hsub' (Set.mem_insert (i, j) _)
              | vertical i j => exact hsub' (Set.mem_insert (i, j) _)
            exact Set.subset_eq_empty hsub rfl
          rw [hT_empty, hempty]
        · simp only [hn, dite_false]
          -- Need to show: Sum.inl (restrictTilingRight ...) = Sum.inl T
          -- This means restrictTilingRight (prependHorizontalPair n T) = T
          congr 1
          apply Tiling.ext
          simp only [restrictTilingRight, prependHorizontalPair]
          -- Similar to the vertical case
          ext d
          simp only [Set.mem_image, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · intro ⟨d', ⟨hd'_mem, hd'_right⟩, hd_eq⟩
            cases hd'_mem with
            | inl heq =>
              rcases heq with rfl | rfl
              · -- d' = horizontal 1 1, which is in left part at fault 2
                exfalso
                have h : (2 : ℤ) ≥ 2 + 1 := hd'_right (2, 1) (by simp [Domino.toShape])
                omega
              · -- d' = horizontal 1 2, which is in left part at fault 2
                exfalso
                have h : (2 : ℤ) ≥ 2 + 1 := hd'_right (2, 2) (by simp [Domino.toShape])
                omega
            | inr hex =>
              obtain ⟨d'', hd''_mem, hd''_eq⟩ := hex
              subst hd''_eq hd_eq
              simp only [Domino.shiftNeg_shiftNat]
              exact hd''_mem
          · intro hd
            use d.shiftNat 2
            constructor
            · constructor
              · right; exact ⟨d, hd, rfl⟩
              · simp only [Domino.inRightPart, Domino.shiftNat_toShape]
                intro p hp
                simp only [Set.mem_image] at hp
                obtain ⟨⟨x, y⟩, hxy, rfl, rfl⟩ := hp
                have hsub := domino_subset_rect n T d hd
                cases d with
                | horizontal i j =>
                  have h1 : (i, j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
                  simp only [Rectangle, Set.mem_ofPred_eq] at h1
                  simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
                | vertical i j =>
                  have h1 : (i, j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
                  simp only [Rectangle, Set.mem_ofPred_eq] at h1
                  simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
            · exact Domino.shiftNeg_shiftNat d 2
      · -- Case: Sum.inr T (from Rectangle (n+1) 2)
        -- Need to show: toSum (prependVertical (n+1) T) = Sum.inr T
        -- First, show vertical 1 1 ∈ (prependVertical (n+1) T).dominos
        have hv : Domino.vertical 1 1 ∈ (prependVertical (n + 1) T).dominos := by
          simp only [prependVertical, Set.mem_union, Set.mem_singleton_iff, true_or]
        simp only [hv, dite_true]
        -- Need to show: Sum.inr (restrictTilingRight ...) = Sum.inr T
        -- This means restrictTilingRight (prependVertical (n+1) T) = T
        congr 1
        apply Tiling.ext
        simp only [restrictTilingRight, prependVertical]
        -- The right part of prependVertical T at fault 1 is exactly T.dominos.image (shiftNat 1)
        -- And restricting shifts back by 1, so we get T.dominos
        ext d
        simp only [Set.mem_image, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · intro ⟨d', ⟨hd'_mem, hd'_right⟩, hd_eq⟩
          cases hd'_mem with
          | inl heq =>
            -- d' = vertical 1 1, which is in left part, not right part
            exfalso
            subst heq
            have h : (1 : ℤ) ≥ 1 + 1 := hd'_right (1, 1) (by simp [Domino.toShape])
            omega
          | inr hex =>
            -- d' is in the shifted part
            obtain ⟨d'', hd''_mem, hd''_eq⟩ := hex
            subst hd''_eq hd_eq
            simp only [Domino.shiftNeg_shiftNat]
            exact hd''_mem
        · intro hd
          use d.shiftNat 1
          constructor
          · constructor
            · right; exact ⟨d, hd, rfl⟩
            · simp only [Domino.inRightPart, Domino.shiftNat_toShape]
              intro p hp
              simp only [Set.mem_image] at hp
              obtain ⟨⟨x, y⟩, hxy, rfl, rfl⟩ := hp
              have hsub := domino_subset_rect (n + 1) T d hd
              cases d with
              | horizontal i j =>
                have h1 : (i, j) ∈ Rectangle (n + 1) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1
                simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
              | vertical i j =>
                have h1 : (i, j) ∈ Rectangle (n + 1) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1
                simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
          · exact Domino.shiftNeg_shiftNat d 1
  -- Provide Finite instances by extracting from tilingsHeight2_isFiniteType
  -- tilingsHeight2_isFiniteType k says {a : Σ n, Tiling (Rectangle n 2) | weight a = k} is finite
  -- This implies Tiling (Rectangle k 2) is finite
  have hfin_n : Set.Finite (Set.univ : Set (Tiling (Rectangle n 2))) := by
    have h := tilingsHeight2_isFiniteType n
    let f : Tiling (Rectangle n 2) → Σ m : ℕ, Tiling (Rectangle m 2) := fun T => ⟨n, T⟩
    have hf : Function.Injective f := by
      intro T1 T2 heq
      simp only [f, Sigma.mk.injEq] at heq
      exact eq_of_heq heq.2
    have hrange : Set.range f ⊆ {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n} := by
      intro x hx
      simp only [Set.mem_range, f] at hx
      obtain ⟨T, rfl⟩ := hx
      simp only [TilingsHeight2, Set.mem_ofPred_eq]
    have hrange_fin : Set.Finite (Set.range f) := h.subset hrange
    convert hrange_fin.preimage hf.injOn
    ext T
    simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, true_iff]
    exact ⟨T, rfl⟩
  have hfin_n1 : Set.Finite (Set.univ : Set (Tiling (Rectangle (n + 1) 2))) := by
    have h := tilingsHeight2_isFiniteType (n + 1)
    let f : Tiling (Rectangle (n + 1) 2) → Σ m : ℕ, Tiling (Rectangle m 2) := fun T => ⟨n + 1, T⟩
    have hf : Function.Injective f := by
      intro T1 T2 heq
      simp only [f, Sigma.mk.injEq] at heq
      exact eq_of_heq heq.2
    have hrange : Set.range f ⊆ {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n + 1} := by
      intro x hx
      simp only [Set.mem_range, f] at hx
      obtain ⟨T, rfl⟩ := hx
      simp only [TilingsHeight2, Set.mem_ofPred_eq]
    have hrange_fin : Set.Finite (Set.range f) := h.subset hrange
    convert hrange_fin.preimage hf.injOn
    ext T
    simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, true_iff]
    exact ⟨T, rfl⟩
  haveI : Finite (Tiling (Rectangle n 2)) := Set.finite_univ_iff.mp hfin_n
  haveI : Finite (Tiling (Rectangle (n + 1) 2)) := Set.finite_univ_iff.mp hfin_n1
  rw [Nat.card_congr e, Nat.card_sum, add_comm]

/-- The number of domino tilings of a 2×n rectangle equals the (n+1)-th Fibonacci number -/
theorem numTilings_2_n (n : ℕ) : d_[n, 2] = Nat.fib (n + 1) := by
  -- The proof uses strong induction with the Fibonacci recurrence.
  -- Base cases: d_[0, 2] = 1 = fib(1), d_[1, 2] = 1 = fib(2)
  -- Inductive step: d_[n+2, 2] = d_[n, 2] + d_[n+1, 2] by numTilings_recurrence
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · -- n = 0
      rw [numTilings_0_2]
      rfl
    · -- n = 1
      rw [numTilings_1_2]
      rfl
    · -- n + 2: use the Fibonacci recurrence
      -- By IH: d_[n, 2] = Nat.fib (n + 1) and d_[n+1, 2] = Nat.fib (n + 2)
      have h1 := ih n (by omega)
      have h2 := ih (n + 1) (by omega)
      simp only [show n + 2 + 1 = n + 3 by ring]
      simp only [show n + 1 + 1 = n + 2 by ring] at h2
      -- By Fibonacci recurrence: Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2)
      have hfib := @Nat.fib_add_two (n + 1)
      simp only [show n + 1 + 1 = n + 2 by ring, show n + 1 + 2 = n + 3 by ring] at hfib
      rw [hfib, ← h1, ← h2]
      -- Apply the recurrence lemma
      exact numTilings_recurrence n

/-- The count of tilings at weight n equals the number of tilings of R_{n,2} -/
lemma countOfWeight_tilingsHeight2_eq (n : ℕ) :
    TilingsHeight2.countOfWeight tilingsHeight2_isFiniteType n = d_[n, 2] := by
  -- This follows from the definition: elements of weight n are exactly tilings of R_{n,2}
  unfold WeightedSet.countOfWeight numTilings
  -- Show the set of elements of weight n is in bijection with tilings of Rectangle n 2
  have h_eq : {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n} =
              Set.range (fun T : Tiling (Rectangle n 2) => (⟨n, T⟩ : Σ m : ℕ, Tiling (Rectangle m 2))) := by
    ext ⟨m, T⟩
    simp only [TilingsHeight2, Set.mem_ofPred_eq, Set.mem_range, Sigma.mk.injEq]
    constructor
    · intro hm
      use hm.symm ▸ T
      exact ⟨hm.symm, by simp⟩
    · intro ⟨T', hm, hT⟩
      exact hm.symm
  have h_finite := tilingsHeight2_isFiniteType n
  have h_card : h_finite.toFinset.card = {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n}.ncard := by
    rw [Set.ncard]
    simp only [h_finite.encard_eq_coe_toFinset_card, ENat.toNat_natCast]
  rw [h_card, h_eq]
  have h_inj : Function.Injective (fun T : Tiling (Rectangle n 2) => (⟨n, T⟩ : Σ m : ℕ, Tiling (Rectangle m 2))) := by
    intro T1 T2 heq
    exact Sigma.mk.inj heq |>.2 |> eq_of_heq
  rw [Set.ncard_range_of_injective h_inj]

/-- The generating function of height-2 tilings equals 1/(1-x-x²),
    which is the Fibonacci generating function -/
theorem weightGenFun_tilingsHeight2 :
    TilingsHeight2.weightGenFun (R := ℚ) tilingsHeight2_isFiniteType =
      PowerSeries.mk fun n => (Nat.fib (n + 1) : ℚ) := by
  -- The n-th coefficient of the LHS is countOfWeight n
  -- which equals numTilings n 2 by countOfWeight_tilingsHeight2_eq
  -- which equals Nat.fib (n + 1) by numTilings_2_n
  ext n
  simp only [WeightedSet.weightGenFun, PowerSeries.coeff_mk]
  rw [countOfWeight_tilingsHeight2_eq, numTilings_2_n]

/-! #### Height-3 Rectangle Tilings -/

/-- The set of dominos that fit within a rectangle -/
def DominosInRectangle (n m : ℕ) : Set Domino :=
  {d | d.toShape ⊆ Rectangle n m}

/-- The set of dominos in a rectangle is finite -/
lemma dominosInRectangle_finite (n m : ℕ) : Set.Finite (DominosInRectangle n m) := by
  have h : DominosInRectangle n m ⊆
      (Set.Icc (1 : ℤ) n ×ˢ Set.Icc (1 : ℤ) m).image (fun p => Domino.horizontal p.1 p.2) ∪
      (Set.Icc (1 : ℤ) n ×ˢ Set.Icc (1 : ℤ) m).image (fun p => Domino.vertical p.1 p.2) := by
    intro d hd
    cases d with
    | horizontal i j =>
      left
      simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
      use (i, j)
      simp only [DominosInRectangle, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
      have h1 := hd (i, j) (by simp)
      simp only [Rectangle, Set.mem_ofPred_eq] at h1
      refine ⟨⟨⟨h1.1, ?_⟩, ⟨h1.2.2.1, h1.2.2.2⟩⟩, rfl⟩
      omega
    | vertical i j =>
      right
      simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
      use (i, j)
      simp only [DominosInRectangle, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
      have h1 := hd (i, j) (by simp)
      simp only [Rectangle, Set.mem_ofPred_eq] at h1
      refine ⟨⟨⟨h1.1, h1.2.1⟩, ⟨h1.2.2.1, ?_⟩⟩, rfl⟩
      omega
  apply Set.Finite.subset _ h
  apply Set.Finite.union
  · apply Set.Finite.image
    apply Set.Finite.prod
    · exact Set.finite_Icc (1 : ℤ) n
    · exact Set.finite_Icc (1 : ℤ) m
  · apply Set.Finite.image
    apply Set.Finite.prod
    · exact Set.finite_Icc (1 : ℤ) n
    · exact Set.finite_Icc (1 : ℤ) m

/-- A tiling's dominos are contained in DominosInRectangle -/
lemma tiling_dominos_subset (n m : ℕ) (T : Tiling (Rectangle n m)) :
    T.dominos ⊆ DominosInRectangle n m := by
  intro d hd
  simp only [DominosInRectangle, Set.mem_ofPred_eq]
  have h : d.toShape ⊆ ⋃ d' ∈ T.dominos, d'.toShape := by
    intro p hp
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hp⟩
  rw [T.cover] at h
  exact h

/-- The set of tilings of a rectangle is finite -/
lemma tilings_finite (n m : ℕ) : Set.Finite (Set.univ : Set (Tiling (Rectangle n m))) := by
  let f : Tiling (Rectangle n m) → Set Domino := fun T => T.dominos
  have hf : Function.Injective f := by
    intro T₁ T₂ h
    cases T₁; cases T₂
    simp only [f] at h
    congr
  have h_range : Set.range f ⊆ 𝒫 (DominosInRectangle n m) := by
    intro s hs
    simp only [Set.mem_range, f] at hs
    obtain ⟨T, rfl⟩ := hs
    simp only [Set.mem_powerset_iff]
    exact tiling_dominos_subset n m T
  have h_powerset_finite : Set.Finite (𝒫 (DominosInRectangle n m)) := by
    exact (dominosInRectangle_finite n m).powerset
  have h_range_finite : Set.Finite (Set.range f) := by
    exact h_powerset_finite.subset h_range
  have h_univ_finite : Set.Finite (f ⁻¹' Set.range f) := by
    apply h_range_finite.preimage
    exact hf.injOn
  convert h_univ_finite
  ext x
  simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, exists_apply_eq_apply]

end DominoTilingsZ
