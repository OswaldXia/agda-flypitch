{-# OPTIONS --cubical --safe #-}

module CubicalExt.Axiom.ExcludedMiddle where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude using (isProp)
open import Cubical.Relation.Nullary using (Dec)

ExcludedMiddle : (ℓ : Level) → Type (ℓ-suc ℓ)
ExcludedMiddle ℓ = {P : Type ℓ} → isProp P → Dec P
