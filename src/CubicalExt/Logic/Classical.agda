{-# OPTIONS --cubical --safe #-}

open import CubicalExt.Axiom.ExcludedMiddle
module CubicalExt.Logic.Classical ⦃ em : ∀ {ℓ} → EM ℓ ⦄ where

open import Cubical.Foundations.Prelude
open import CubicalExt.Foundations.Function using (_∘_; _$--)
open import Cubical.Data.Empty
open import CubicalExt.Relation.Nullary

private variable
  ℓ ℓ' : Level
  A : Type ℓ

module _ {A : Type ℓ} ⦃ Aprop : isPropImplicit A ⦄ where

  byContra : (¬ A → ⊥) → A
  byContra ¬A⇒⊥ with em ⦃ Aprop ⦄
  ... | yes p = p
  ... | no ¬p = rec (¬A⇒⊥ ¬p)

  byContra* : (¬ A → ⊥* {ℓ'}) → A
  byContra* ¬A⇒⊥ with em ⦃ Aprop ⦄
  ... | yes p = p
  ... | no ¬p = rec* (¬A⇒⊥ ¬p)

isSet→Discrete : isSet A → Discrete A
isSet→Discrete Aset x y = em ⦃ Aset x y $-- ⦄

isSet→DiscreteEq : isSet A → DiscreteEq A
isSet→DiscreteEq = Discrete→DiscreteEq ∘ isSet→Discrete
