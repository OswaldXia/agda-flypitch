{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary
open BinaryRelation
module CubicalExt.Logic.Zorn {ℓ ℓ'} {U : Type ℓ} {_≤_ : Rel U U ℓ'} (isTrans≤ : isTrans _≤_) where

open import CubicalExt.Foundations.Powerset* using (𝒫; _∈_)
open import Cubical.Data.Sigma using (∃-syntax)
open import Cubical.Data.Sum renaming (_⊎_ to infix 3 _⊎_)

--------------------------------------------------
-- Definition

isChain : 𝒫 U ℓ → Type _
isChain A = ∀ x y → x ∈ A → y ∈ A → x ≤ y ⊎ y ≤ x

EveryChianHasAnUpperNound = ∀ A → isChain A → ∃[ ub ∈ U ] ∀ x → x ∈ A → x ≤ ub

HasMaximum = ∃[ m ∈ U ] ∀ x → m ≤ x → x ≤ m

Zorn = EveryChianHasAnUpperNound → HasMaximum

--------------------------------------------------
-- Proof


