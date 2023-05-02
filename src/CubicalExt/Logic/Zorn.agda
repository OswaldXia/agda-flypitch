{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary
module CubicalExt.Logic.Zorn {ℓ ℓ'} {U : Type ℓ} (_≤_ : Rel U U ℓ') where

open import CubicalExt.Foundations.Powerset* using (𝒫; _∈_; _⊆_)
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Sigma using (∃-syntax; _×_)
open import Cubical.Data.Sum using () renaming (_⊎_ to infixr 3 _⊎_)
open import Cubical.Relation.Nullary using (¬_)
open BinaryRelation

--------------------------------------------------
-- Definition

isChain : 𝒫 U ℓ → Type _
isChain A = ∀ x y → x ∈ A → y ∈ A → x ≤ y ⊎ y ≤ x

upperBound : 𝒫 U ℓ → U → Type _
upperBound A ub = ∀ x → x ∈ A → x ≤ ub

EveryChainHasUpperBound = ∀ A → isChain A → Σ[ ub ∈ U ] upperBound A ub

premaximum : U → Type _
premaximum m = ∀ x → m ≤ x → x ≤ m

-- Given preorder (U, ≤), if every chain A ⊆ U has an upper bound, then (U, ≤) merely has a premaximum.
Zorn = isRefl _≤_ → isTrans _≤_ → EveryChainHasUpperBound → ∃[ m ∈ U ] premaximum m

--------------------------------------------------
-- Proof

Successive = ∀ x → Σ[ y ∈ U ] x ≤ y × (¬ x ≡ y) × ∀ z → x ≤ z → z ≤ y → z ≡ x ⊎ z ≡ y

-- least upper bound
supremum : 𝒫 U ℓ → U → Type _
supremum A sup = upperBound A sup × ∀ ub → upperBound A ub → sup ≤ ub

EveryChainHasSupremum = ∀ A → isChain A → Σ[ sup ∈ U ] supremum A sup

module _ (hasSuc : Successive) (hasSup : EveryChainHasSupremum) where

  data Tower : U → Type (ℓ-max (ℓ-suc ℓ) ℓ') where
    isSetTower : (x : U) → isProp (Tower x)
    includeSuc : let TowerSet = λ x → Tower x , isSetTower x in
      (x : U) → x ∈ TowerSet → hasSuc x .fst ∈ TowerSet
    includeSup : let TowerSet = λ x → Tower x , isSetTower x in
      (A : 𝒫 U ℓ) → A ⊆ TowerSet → (isChainA : isChain A) →
      hasSup A isChainA .fst ∈ TowerSet
