{-# OPTIONS --cubical --safe #-}

module Synthetic.FormalSystem where
open import Synthetic.Definitions

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation

infix 22 ¬_
infix 21 _⊢_

private variable
  ℓ : Level
  Sentence : Type ℓ
  ¬_ : Sentence → Sentence

record FormalSystem (Sentence : Type ℓ) (¬_ : Sentence → Sentence) : Type (ℓ-suc ℓ) where
  field
    ⊢_ : Sentence → Type
    ⊢-isPred : isPredicate ⊢_
    ⊢-semiDec : semiDecidable ⊢_
    consistent : ∀ φ → ⊢ φ → ⊢ ¬ φ → ⊥

_⊢_ : FormalSystem Sentence ¬_ → Sentence → Type
S ⊢ φ = ⊢ φ where open FormalSystem S

_⊬_ : FormalSystem Sentence ¬_ → Sentence → Type
S ⊬ φ = ⊢ φ → ⊥ where open FormalSystem S

_⊑_ : FormalSystem Sentence ¬_ → FormalSystem Sentence ¬_ → Type _
S₁ ⊑ S₂ = ∀ φ → S₁ ⊢ φ → S₂ ⊢ φ

module _ (S : FormalSystem Sentence ¬_) where

  complete : Type _
  complete = ∀ φ → ∥ S ⊢ φ ⊎ S ⊢ ¬ φ ∥₁

  independent : Type _
  independent = ∀ φ → S ⊬ φ × S ⊬ ¬ φ
