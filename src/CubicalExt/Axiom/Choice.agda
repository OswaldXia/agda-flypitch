{-# OPTIONS --cubical --safe #-}

module CubicalExt.Axiom.Choice where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (∃-syntax)

private variable
  ℓ ℓ' : Level
  X : Type ℓ

AC : (A : X → Type ℓ) (P : ∀ x → A x → Type ℓ') → Type _
AC A P = (∀ x → ∃[ a ∈ A x ] P x a) → ∃[ f ∈ (∀ x → A x) ] ∀ x → P x (f x)
