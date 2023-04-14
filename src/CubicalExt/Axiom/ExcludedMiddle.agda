{-# OPTIONS --cubical --safe #-}

module CubicalExt.Axiom.ExcludedMiddle where

open import Cubical.Core.Primitives
open import Cubical.Relation.Nullary using (Dec)

isPropImplicit : ∀ {ℓ} → Type ℓ → Type ℓ
isPropImplicit A = {x y : A} → x ≡ y

ExcludedMiddle : Typeω
ExcludedMiddle = ∀ {ℓ} {A : Type ℓ} → ⦃ isPropImplicit A ⦄ → Dec A
