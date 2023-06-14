{-# OPTIONS --cubical --safe #-}

module Synthetic.FormalSystem where
open import Synthetic.Definitions

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ : Level
  Sentence : Type ℓ
  ¬_ : Sentence → Sentence

record FormalSystem (Sentence : Type ℓ) (¬_ : Sentence → Sentence) : Type (ℓ-suc ℓ) where
  field
    ⊢_ : Sentence → Type
    ⊢-isPred : isPredicate ⊢_
    ⊢-semiDec : semiDecidable ⊢_
    consistent : ∀ φ → ⊢ φ → ⊢ (¬ φ) → ⊥
  ⊬_ : Sentence → Type
  ⊬_ φ = ⊢ φ → ⊥

_⊢_ : FormalSystem Sentence ¬_ → Sentence → Type
S ⊢ φ = ⊢ φ where open FormalSystem S

_⊬_ : FormalSystem Sentence ¬_ → Sentence → Type
S ⊬ φ = ⊬_ φ where open FormalSystem S

_⊑_ : FormalSystem Sentence ¬_ → FormalSystem Sentence ¬_ → Type _
S₁ ⊑ S₂ = ∀ φ → S₁ ⊢ φ → S₂ ⊢ φ

complete : FormalSystem Sentence ¬_ → Type _
complete {¬_ = ¬_} S = ∀ φ → ∥ (S ⊢ φ) ⊎ (S ⊢ (¬ φ)) ∥₁

independent : FormalSystem Sentence ¬_ → Type _
independent {¬_ = ¬_} S = ∀ φ → (S ⊬ φ) × (S ⊬ (¬ φ))

_represents_by_ : FormalSystem Sentence ¬_ → (ℕ → Type) → (ℕ → Sentence) → Type _
S represents P by fᵣ = fᵣ reducts P to (S ⊢_)

_represents_ : FormalSystem Sentence ¬_ → (ℕ → Type) → Type _
S represents P = P ⪯ (S ⊢_)

_soundFor_by_ : FormalSystem Sentence ¬_ → (ℕ → Type) → (ℕ → Sentence) → Type _
S soundFor P by fᵣ = ∀ n → S ⊢ (fᵣ n) → P n

_soundFor_ : FormalSystem Sentence ¬_ → (ℕ → Type) → Type _
S soundFor P = ∃ (ℕ → _) λ fᵣ → S soundFor P by fᵣ

private variable
  S : FormalSystem Sentence ¬_
  P : ℕ → Type ℓ

represent→sound : S represents P → S soundFor P
represent→sound = ∥₁.map λ (fᵣ , H) → fᵣ , λ n → H n .from
