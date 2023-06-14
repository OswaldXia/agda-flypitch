{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Synthetic.Church
module Synthetic.Halting ((Θ , Θ-universal) : EPFᴮ) where

open import Synthetic.PartialFunction
open import Synthetic.Definitions

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation
open import CubicalExt.Functions.Logic.Iff

-- halting problem by self-reference
Kᶿ : ℕ → Type
Kᶿ c = ∃ _ (Θ c c ≐_)

Kᶿ-diverging : ∀ f → f partialDecides Kᶿ → ∃ _ λ c → diverging (f c)
Kᶿ-diverging f = {!   !}

Kᶿ-¬dec : ¬ decidable Kᶿ
Kᶿ-¬dec dec = {!   !} where
  fₚ : ℕ → part Bool
  fₚ n = rec→Set {!   !}
    (λ { (fᵈ , Hᵈ) → record { f = λ n → just (fᵈ n) ; proper = {!   !} } })
    {!   !}
    dec
