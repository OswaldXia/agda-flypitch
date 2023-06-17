{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module Synthetic.FormalSystem {ℓ} where
open import Synthetic.PartialFunction
open import Synthetic.Definitions.Base
open import Synthetic.Definitions.Properties
open import Synthetic.Definitions.Prophood

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Equality using (eqToPath)
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

record FormalSystem (Sentence : Type ℓ) (¬_ : Sentence → Sentence) : Type (ℓ-suc ℓ) where
  field
    ⊢_ : Sentence → Type
    ⊢-isPred : isPredicate ⊢_
    ⊢-semiDec : semiDecidable ⊢_
    consistent : ∀ φ → ⊢ φ → ⊢ (¬ φ) → ⊥

  ⊬_ : Sentence → Type
  ⊬_ φ = ⊢ φ → ⊥

  complete : Type _
  complete = ∀ φ → ∥ (⊢ φ) ⊎ (⊢ ¬ φ) ∥₁

  independent : Type _
  independent = ∀ φ → (⊬ φ) × (⊬ ¬ φ)

  ⊢¬-semiDec : semiDecidable (⊢_ ∘ ¬_)
  ⊢¬-semiDec = semiDecReduction ∣ ¬_ , (λ _ → ↔-refl) ∣₁ ⊢-semiDec

  ⊢-⊢¬-sep : separatable (⊢_) (⊢_ ∘ ¬_)
  ⊢-⊢¬-sep = semiDec→sep ⊢-isPred (λ _ → ⊢-isPred _)
    consistent ⊢-semiDec ⊢¬-semiDec

  complete→⊢-dec : complete → decidable (⊢_)
  complete→⊢-dec compl = ∥₁.rec (isPropDecidable ⊢-isPred)
    (λ { (fₚ , Hₚ) → let open Lemma fₚ Hₚ in f , H }) ⊢-⊢¬-sep
    where
    module Lemma (fₚ : Sentence → part Bool) (Hₚ : fₚ separates ⊢_ and (⊢_ ∘ ¬_)) where
      fₚ-total : total fₚ
      fₚ-total φ = ∥₁.map (aux φ) (compl φ) where
        aux : ∀ φ → (⊢ φ) ⊎ (⊢ ¬ φ) → Σ _ (fₚ φ ≐_)
        aux φ (inl ⊢φ)  = true  , Hₚ .fst φ .to ⊢φ
        aux φ (inr ⊢¬φ) = false , Hₚ .snd φ .to ⊢¬φ
      f : Sentence → Bool
      f = fst ∘ totalise fₚ fₚ-total isSetBool
      fₚ≐ : (φ : Sentence) → fₚ φ ≐ f φ
      fₚ≐ = snd ∘ totalise fₚ fₚ-total isSetBool
      H : f decides ⊢_
      H φ with f φ in α
      ... | true  = →: (λ _ → refl)
                    ←: (λ _ → Hₚ .fst φ .from ≐true)
        where
        ≐true : fₚ φ ≐ true
        ≐true = subst (fₚ φ ≐_) (eqToPath α) (fₚ≐ φ)
      ... | false = →: (λ ⊢φ → part.functional (fₚ φ) isSetBool ≐false (≐true ⊢φ))
                    ←: (λ H → ⊥.rec $ false≢true H)
        where
        ≐true : ⊢ φ → fₚ φ ≐ true
        ≐true = Hₚ .fst φ .to
        ≐false : fₚ φ ≐ false
        ≐false = subst (fₚ φ ≐_) (eqToPath α) (fₚ≐ φ)

open FormalSystem using (complete; independent; complete→⊢-dec) public

private variable
  Sentence : Type ℓ
  ¬_ : Sentence → Sentence

_⊢_ : FormalSystem Sentence ¬_ → Sentence → Type
S ⊢ φ = ⊢ φ where open FormalSystem S

_⊬_ : FormalSystem Sentence ¬_ → Sentence → Type
S ⊬ φ = ⊬_ φ where open FormalSystem S

_⊑_ : FormalSystem Sentence ¬_ → FormalSystem Sentence ¬_ → Type _
S₁ ⊑ S₂ = ∀ φ → S₁ ⊢ φ → S₂ ⊢ φ

_represents_by_ : FormalSystem Sentence ¬_ → (ℕ → Type ℓ) → (ℕ → Sentence) → Type _
S represents N by fᵣ = fᵣ reducts N to (S ⊢_)

_represents_ : FormalSystem Sentence ¬_ → (ℕ → Type ℓ) → Type _
S represents N = N ⪯ (S ⊢_)

_soundFor_by_ : FormalSystem Sentence ¬_ → (ℕ → Type ℓ) → (ℕ → Sentence) → Type _
S soundFor N by fᵣ = ∀ n → S ⊢ (fᵣ n) → N n

_soundFor_ : FormalSystem Sentence ¬_ → (ℕ → Type ℓ) → Type _
S soundFor N = ∃ (ℕ → _) λ fᵣ → S soundFor N by fᵣ

private variable
  S S₁ S₂ : FormalSystem Sentence ¬_
  N : ℕ → Type ℓ

represent→sound : S represents N → S soundFor N
represent→sound = ∥₁.map λ (fᵣ , H) → fᵣ , λ n → H n .from

⊢-dec→repN→decN : S₁ ⊑ S₂ → decidable (S₂ ⊢_) → isPredicate N →
  (∃ (ℕ → _) λ fᵣ → S₁ represents N by fᵣ × S₂ soundFor N by fᵣ) → decidable N
⊢-dec→repN→decN ext (fᵈ , Hᵈ) pred =
  ∥₁.rec (isPropDecidable pred) λ { (fᵣ , H₁ , H₂) → fᵈ ∘ fᵣ , λ n →
    →: (λ H → Hᵈ _ .to $ ext _ $ H₁ _ .to H)
    ←: λ H → H₂ n $ Hᵈ _ .from H }

com→repN→decN : S₁ ⊑ S₂ → complete S₂ → isPredicate N →
  (∃ (ℕ → _) λ fᵣ → S₁ represents N by fᵣ × S₂ soundFor N by fᵣ) → decidable N
com→repN→decN {S₂ = S₂} ext compl pred =
  ⊢-dec→repN→decN ext (complete→⊢-dec S₂ compl) pred
