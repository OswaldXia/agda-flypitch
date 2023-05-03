{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary
open BinaryRelation
module CubicalExt.Logic.Zorn {u r} {U : Type u} {_≤_ : Rel U U r} (isPropValued≤ : isPropValued _≤_) where

open import CubicalExt.Axiom.ExcludedMiddle
open import CubicalExt.Foundations.Powerset* using (𝒫; _∈_; _⊆_)
open import Cubical.Foundations.Function using (_$_)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ2)
open import Cubical.Functions.Logic using (∥_∥ₚ; inl; inr) renaming (_⊔′_ to infixr 3 _∨_)
open import Cubical.Data.Sigma using (∃-syntax; _×_)
open import Cubical.HITs.PropositionalTruncation using (squash₁; elim; elim2)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

private variable
  ℓ : Level
  x y : U
  A : 𝒫 U ℓ

--------------------------------------------------
-- Definition

isChain : 𝒫 U ℓ → Type _
isChain A = ∀ x y → x ∈ A → y ∈ A → x ≤ y ∨ y ≤ x

upperBound : 𝒫 U ℓ → U → Type _
upperBound A ub = ∀ x → x ∈ A → x ≤ ub

EveryChainHasUpperBound = ∀ {ℓ} (A : 𝒫 U ℓ) → Σ[ ub ∈ U ] upperBound A ub

premaximum : U → Type _
premaximum m = ∀ x → m ≤ x → x ≤ m

-- Given preorder (U, ≤), if every chain A ⊆ U has an upper bound, then (U, ≤) merely has a premaximum.
Zorn = isRefl _≤_ → isTrans _≤_ → EveryChainHasUpperBound → ∃[ m ∈ U ] premaximum m

--------------------------------------------------
-- Proof

instance
  isPropImplicitValued≤ : isPropImplicit (x ≤ y)
  isPropImplicitValued≤ = isPropValued≤ _ _ _ _

Successive = ∀ x → Σ[ y ∈ U ] x ≤ y × (¬ x ≡ y) × ∀ z → x ≤ z → z ≤ y → z ≡ x ∨ z ≡ y

-- least upper bound
supremum : 𝒫 U ℓ → U → Type _
supremum A sup = upperBound A sup × ∀ ub → upperBound A ub → sup ≤ ub

EveryChainHasSupremum = ∀ {ℓ} (A : 𝒫 U ℓ) → isChain A → Σ[ sup ∈ U ] supremum A sup

module _ ⦃ em : ∀ {ℓ} → EM ℓ ⦄ (hasSuc : Successive) (hasSup : EveryChainHasSupremum) where
  open import CubicalExt.Logic.Classical

  data Tower (ℓ : Level) : U → Type (ℓ-max (ℓ-max u r) (ℓ-suc ℓ)) where
    includeSuc : (x : U) → Tower ℓ x → Tower ℓ (hasSuc x .fst)
    includeSup : (A : 𝒫 U ℓ) → (∀ x → x ∈ A → Tower ℓ x) → (isChainA : isChain A) →
      Tower ℓ (hasSup A isChainA .fst)

  TowerSet : (ℓ : Level) → 𝒫 U _
  TowerSet ℓ x = ∥ Tower ℓ x ∥ₚ

  isChainTowerSet : isChain (TowerSet ℓ)
  isChainTowerSet x y = elim2 (λ _ _ → squash₁) (isChainTower x y) where
    isChainTower : ∀ x y → Tower ℓ x → Tower ℓ y → x ≤ y ∨ y ≤ x
    isChainTower x .(hasSuc y .fst) x∈ (includeSuc y y∈) = {!   !}
    isChainTower x .(hasSup A isChainA .fst) x∈ (includeSup A A⊆ isChainA) with em {P = upperBound A x}
    ... | yes p = inr $ hasSup A isChainA .snd .snd x p
    ... | no ¬p = inl $ elim (λ _ → isPropValued≤ _ _) {!   !} (¬∀→∃¬ ¬p)
