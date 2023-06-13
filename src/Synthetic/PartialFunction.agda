{-# OPTIONS --cubical --safe #-}

module Synthetic.PartialFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import CubicalExt.Logic.ConstructiveEpsilon

private variable
  ℓ : Level
  A : Type ℓ

record part (A : Type) : Type where
  field
    f : ℕ → Maybe A
    deterministic : ∀ n m a b → f n ≡ just a → f m ≡ just b → a ≡ b
  _▻_ : A → Type
  _▻_ a = ∃ _ λ k → f k ≡ just a

open part using (_▻_) public

totalise : (aₚ : part A) → ∃ _ (aₚ ▻_) → Σ _ (aₚ ▻_)
totalise aₚ = let H = {!   !} in {!  !}
