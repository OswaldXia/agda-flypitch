{-# OPTIONS --cubical --safe #-}

module CubicalExt.Foundations.Powerset where

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels using (hProp)
--open import Cubical.Foundations.Powerset public
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)

private variable
  a b ℓ : Level
  A : Type a
  B : Type b
  --P Q : ℙ A
  x : A
  f : A → B

ℙ : Type a → (ℓ : Level) → Type (ℓ-max a (ℓ-suc ℓ))
ℙ A ℓ = A → hProp ℓ

--_⟦_⟧ : {A : Type a} {B : Type a} (f : A → B) (P : ℙ A) → ℙ B
--f ⟦ P ⟧ = λ y → {! ∃[ x ∈ _ ] x ∈ P × y ≡ f x  !} , {!   !} --λ y → ∃[ x ] x ∈ P × y ≡ f x
