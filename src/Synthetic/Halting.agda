{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Synthetic.Axiom.Base
module Synthetic.Halting ((Θ , Θ-universal) : EPFᴮ) where

open import Synthetic.PartialFunction
open import Synthetic.Definitions.Base
open import Synthetic.Definitions.Properties

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Equality using (eqToPath)
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

-- halting problem by self-reference
Kᶿ : ℕ → Type
Kᶿ c = ∃ _ (Θ c c ≐_)

Kᶿ-divergent : ∀ fₚ → fₚ decidesₚ Kᶿ → ∃ _ λ c → undefined (fₚ c)
Kᶿ-divergent fₚ Hₚ = flip map (Θ-universal gₚ) λ { (c , Hc) → c ,
  λ { true fₚc≐T → {!   !}
    ; false fₚc≐F → {!   !}
    } }
  where
  gₚ : ℕ → part Bool
  gₚ = {!   !}
