{-# OPTIONS --cubical --safe #-}

module CubicalExt.Axiom.Choice where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (∃-syntax)

AC : (ℓ ℓ' ℓ'' : Level) → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ''))
AC ℓ ℓ' ℓ'' = (A : Type ℓ) (B : A → Type ℓ') (P : ∀ x → B x → Type ℓ'') →
  (∀ x → ∃[ a ∈ B x ] P x a) → ∃[ f ∈ (∀ x → B x) ] ∀ x → P x (f x)
