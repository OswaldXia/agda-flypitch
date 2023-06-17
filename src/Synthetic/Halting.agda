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
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

-- halting problem by self-reference
Kᶿ : ℕ → Type
Kᶿ c = ∃ _ (Θ c c ≐_)

Kᶿ-divergent : ∀ fₚ → fₚ partialDecides Kᶿ → ∃ _ λ c → divergent (fₚ c)
Kᶿ-divergent fₚ Hₚ = flip map (Θ-universal gₚ) λ { (c , Hc) → c ,
  λ b → ∥₁.rec isProp⊥ (λ (n , H) → {!   !}) }
  where
  eval : ℕ → ℕ → Maybe Bool
  eval n m with fₚ n .part.eval m
  ... | just true = nothing
  ... | just false = just true
  ... | nothing = nothing
  proper : ∀ n → deterministic (eval n)
  proper n {m₁} {m₂} p q with fₚ n .part.eval m₁ | fₚ n .part.eval m₂
  ... | just true  | just true  = just-inj _ _ $ (sym p) ∙ q
  ... | just false | just false = just-inj _ _ $ (sym p) ∙ q
  ... | just true  | just false = ⊥.rec $ ¬nothing≡just p
  ... | just false | just true  = ⊥.rec $ ¬nothing≡just q
  ... | nothing    | _          = ⊥.rec $ ¬nothing≡just p
  ... | _          | nothing    = ⊥.rec $ ¬nothing≡just q
  gₚ : ℕ → part Bool
  gₚ n = mkPart (eval n) (proper n)

Kᶿ-¬dec : ¬ decidable Kᶿ
Kᶿ-¬dec dec@(fᵈ , _) = let (fₚ , Hₚ) = dec→pDec (λ _ → squash₁) dec in
  ∥₁.rec isProp⊥ (λ (c , conv) → conv (fᵈ c) ∣ 0 , refl ∣₁) (Kᶿ-divergent fₚ Hₚ)
