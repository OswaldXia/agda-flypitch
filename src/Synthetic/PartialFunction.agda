{-# OPTIONS --cubical --safe #-}

module Synthetic.PartialFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import CubicalExt.Logic.ConstructiveEpsilon

private variable
  ℓ : Level
  A B : Type ℓ

record part (A : Type) : Type where
  field
    f : ℕ → Maybe A
    proper : ∀ {n m a b} → f n ≡ just a → f m ≡ just b → a ≡ b

  eval : A → Type
  eval a = ∃ _ λ k → f k ≡ just a

  functional : isSet A → ∀ {a b} → eval a → eval b → a ≡ b
  functional Aset = rec2 (Aset _ _)
    (λ { (_ , Hn) (_ , Hm) → proper Hn Hm })

  totalise : ∃ _ eval → Σ _ eval
  totalise aₚ = {!   !}

_▻_ : part A → A → Type
aᵖ ▻ a = part.eval aᵖ a

total : (f : A → part B) → Type _
total f = ∀ x → ∃ _ (f x ▻_)

totalise : (f : A → part B) → total f → A → B
totalise f H x = part.totalise (f x) (H x) .fst

partialise : (A → B) → A → part B
partialise f x = record { f = λ _ → just (f x) ; proper = λ p q → just-inj _ _ ((sym p) ∙ q) }
