{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Synthetic.Church
module Synthetic.Halting ((Θ , Θ-universal) : EPFᴮ) where

open import Synthetic.PartialFunction

open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

-- halting problem by self-reference
Kᶿ : ℕ → Type
Kᶿ c = ∃ _ (Θ c c ≐_)

--Kᶿ-diverge : (f : ℕ → part Bool) → 
