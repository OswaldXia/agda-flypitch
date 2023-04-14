{-# OPTIONS --cubical --safe #-}

open import CubicalExt.Axiom.ExcludedMiddle
module CubicalExt.Classical ⦃ classical : ExcludedMiddle ⦄ where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import CubicalExt.Foundations.Function using (_$--)
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

private variable
  ℓ ℓ' : Level
  A : Type ℓ

module _ {A : Type ℓ} ⦃ Aprop : isPropImplicit A ⦄ where

  byContra : (¬ A → ⊥) → A
  byContra ¬A⇒⊥ with classical ⦃ Aprop ⦄
  ... | yes p = p
  ... | no ¬p = rec (¬A⇒⊥ ¬p)

  byContra* : (¬ A → ⊥* {ℓ'}) → A
  byContra* ¬A⇒⊥ with classical ⦃ Aprop ⦄
  ... | yes p = p
  ... | no ¬p = rec* (¬A⇒⊥ ¬p)

isSet→Discrete : isSet A → Discrete A
isSet→Discrete Aset x y = classical ⦃ Aset x y $-- ⦄
