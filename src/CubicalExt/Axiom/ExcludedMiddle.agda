{-# OPTIONS --cubical --safe #-}

module CubicalExt.Axiom.ExcludedMiddle where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary using (Dec)

isPropImplicit : ∀ {ℓ} → Type ℓ → Type ℓ
isPropImplicit A = {x y : A} → x ≡ y

EM : Typeω
EM = ∀ {ℓ} {A : Type ℓ} → ⦃ isPropImplicit A ⦄ → Dec A
