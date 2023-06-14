{-# OPTIONS --cubical --safe #-}

module Synthetic.WeeklyIncompleteness where
open import Synthetic.Definitions
open import Synthetic.Properties
open import Synthetic.PartialFunction
open import Synthetic.FormalSystem

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Equality using (eqToPath)
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ : Level
  Sentence : Type ℓ
  ¬_ : Sentence → Sentence

module _ (S : FormalSystem Sentence ¬_) where
  open FormalSystem S

  ⊢¬-semiDec : semiDecidable (⊢_ ∘ ¬_)
  ⊢¬-semiDec = semiDecReduction ∣ ¬_ , (λ _ → ↔-refl) ∣₁ ⊢-semiDec

  ⊢-⊢¬-sep : separatable (⊢_) (⊢_ ∘ ¬_)
  ⊢-⊢¬-sep = semiDec→sep ⊢-isPred (λ _ → ⊢-isPred _)
    consistent ⊢-semiDec ⊢¬-semiDec

  complete→⊢-dec : complete S → decidable (⊢_)
  complete→⊢-dec compl = flip ∥₁.map ⊢-⊢¬-sep
    λ { (fₚ , Hₚ) → let open Lemma fₚ Hₚ in f , H } where
    module Lemma (fₚ : Sentence → part Bool) (Hₚ : fₚ separates ⊢_ and (⊢_ ∘ ¬_)) where
      fₚ-total : total fₚ
      fₚ-total φ = ∥₁.map (aux φ) (compl φ) where
        aux : ∀ φ → (⊢ φ) ⊎ (⊢ ¬ φ) → Σ _ (fₚ φ ▻_)
        aux φ (inl ⊢φ)  = true  , Hₚ .fst φ .to ⊢φ
        aux φ (inr ⊢¬φ) = false , Hₚ .snd φ .to ⊢¬φ
      f : Sentence → Bool
      f = fst ∘ totalise fₚ fₚ-total isSetBool
      fₚ▻ : (φ : Sentence) → fₚ φ ▻ f φ
      fₚ▻ = snd ∘ totalise fₚ fₚ-total isSetBool
      H : f decides ⊢_
      H φ with f φ in α
      ... | true  = →: (λ _ → refl)
                    ←: (λ _ → Hₚ .fst φ .from ▻true)
        where
        ▻true : fₚ φ ▻ true
        ▻true = subst (fₚ φ ▻_) (eqToPath α) (fₚ▻ φ)
      ... | false = →: (λ ⊢φ → part.functional (fₚ φ) isSetBool ▻false (▻true ⊢φ))
                    ←: (λ H → ⊥.rec $ false≢true H)
        where
        ▻true : ⊢ φ → fₚ φ ▻ true
        ▻true = Hₚ .fst φ .to
        ▻false : fₚ φ ▻ false
        ▻false = subst (fₚ φ ▻_) (eqToPath α) (fₚ▻ φ)
