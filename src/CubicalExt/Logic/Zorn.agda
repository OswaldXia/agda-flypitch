{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary
module CubicalExt.Logic.Zorn {ℓ ℓ'} {U : Type ℓ} {_≤_ : Rel U U ℓ'} where

open import CubicalExt.Foundations.Powerset* using (𝒫; _∈_; _⊆_)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infix 3 _×_)
open import Cubical.Data.Sum renaming (_⊎_ to infix 3 _⊎_)
open BinaryRelation

--------------------------------------------------
-- Definition

isPreorder : Rel U U ℓ' → Type _
isPreorder _≤_ = isRefl _≤_ × isTrans _≤_

isChain : 𝒫 U ℓ → Type _
isChain A = ∀ x y → x ∈ A → y ∈ A → x ≤ y ⊎ y ≤ x

upperBound : 𝒫 U ℓ → U → Type _
upperBound A ub = ∀ x → x ∈ A → x ≤ ub

EveryChainHasUpperBound = ∀ A → isChain A → ∃[ ub ∈ U ] upperBound A ub

preMaximum : U → Type _
preMaximum m = ∀ x → m ≤ x → x ≤ m

HasPreMaximum = ∃[ m ∈ U ] preMaximum m

Zorn = isPreorder _≤_ → EveryChainHasUpperBound → HasPreMaximum

--------------------------------------------------
-- Proof

-- least upper bound
supremum : 𝒫 U ℓ → U → Type _
supremum A sup = upperBound A sup × ∀ ub → upperBound A ub → sup ≤ ub

EveryChainHasSupremum = ∀ A → isChain A → ∃[ sup ∈ U ] supremum A sup
