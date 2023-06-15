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

Kᶿ-diverging : ∀ fₚ → fₚ partialDecides Kᶿ → ∃ _ λ c → diverging (fₚ c)
Kᶿ-diverging fₚ Hₚ = {!   !}
  where
  gₚ : ℕ → part Bool
  gₚ n = mkPart (λ m → {! fₚ n  !}) {!   !}

Kᶿ-¬dec : ¬ decidable Kᶿ
Kᶿ-¬dec = ∥₁.rec isProp⊥ λ dec@(fᵈ , _) → let (fₚ , Hₚ) = dec→pDec (λ _ → squash₁) dec in
  ∥₁.rec isProp⊥ (λ (c , div) → div (fᵈ c) ∣ 0 , refl ∣₁) (Kᶿ-diverging fₚ Hₚ)
