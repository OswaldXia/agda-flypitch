{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Synthetic.Church
module Synthetic.Halting ((Θ , Θ-universal) : EPFᴮ) where

open import Synthetic.PartialFunction
open import Synthetic.Definitions
open import Synthetic.Properties

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

-- halting problem by self-reference
Kᶿ : ℕ → Type
Kᶿ c = ∃ _ (Θ c c ≐_)

Kᶿ-divergent : ∀ fₚ → fₚ partialDecides Kᶿ → ∃ _ λ c → divergent (fₚ c)
Kᶿ-divergent fₚ Hₚ = {!   !}
  where
  eval : ℕ → ℕ → Maybe Bool
  eval n m with fₚ n .part.eval m
  ... | just true = nothing
  ... | just false = just true
  ... | nothing = nothing
  proper : ∀ n → deterministic (eval n)
  proper n {m₁} {m₂} p q with fₚ n .part.eval m₁ | fₚ n .part.eval m₂
  ... | just true  | just true  = {!   !}
  ... | just false | just false = {!   !}
  ... | just true  | just false = {!   !}
  ... | just false | just true  = {!   !}
  ... | nothing    | just _     = {!   !}
  ... | just _     | nothing    = {!   !}
  ... | nothing    | nothing    = {!   !}
  gₚ : ℕ → part Bool
  gₚ n = mkPart (eval n) (proper n)

Kᶿ-¬dec : ¬ decidable Kᶿ
Kᶿ-¬dec = ∥₁.rec isProp⊥ λ dec@(fᵈ , _) → let (fₚ , Hₚ) = dec→pDec (λ _ → squash₁) dec in
  ∥₁.rec isProp⊥ (λ (c , div) → div (fᵈ c) ∣ 0 , refl ∣₁) (Kᶿ-divergent fₚ Hₚ)
