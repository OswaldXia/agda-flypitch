{-# OPTIONS --cubical #-}

module CubicalExt.Classical where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary
open import CubicalExt.Axiom.ExcludedMiddle

private variable
  ℓ ℓ' : Level

postulate
  classical : ExcludedMiddle ℓ

module _ {A : Type ℓ} (Aprop : isProp A) where

  byContra : (¬ A → ⊥) → A
  byContra ¬A⇒⊥ with classical Aprop
  ... | yes p = p
  ... | no ¬p = rec (¬A⇒⊥ ¬p)

  byContra* : (¬ A → ⊥* {ℓ'}) → A
  byContra* ¬A⇒⊥ with classical Aprop
  ... | yes p = p
  ... | no ¬p = rec* (¬A⇒⊥ ¬p)
