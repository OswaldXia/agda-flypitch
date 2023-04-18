{-# OPTIONS --cubical --safe #-}

module FOL.Language.Homomorphism.Base {u} where
open import FOL.Language hiding (u)

open import Cubical.Foundations.Prelude using (Type)
open import Data.Nat using (ℕ)
open import Function using () renaming (id to ⟨id⟩; _∘_ to _⟨∘⟩_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

private variable
  ℒ₁ ℒ₂ ℒ₃ ℒ₄ : Language

record _⟶_ (ℒ₁ : Language) (ℒ₂ : Language) : Type u where
  constructor ⟪_,_⟫
  open Language {u}
  field
    funMorph : ∀ {n} → ℒ₁ .𝔉 n → ℒ₂ .𝔉 n
    relMorph : ∀ {n} → ℒ₁ .ℜ n → ℒ₂ .ℜ n

id : ℒ ⟶ ℒ
id = ⟪ ⟨id⟩ , ⟨id⟩ ⟫

_∘_ : ℒ₂ ⟶ ℒ₃ → ℒ₁ ⟶ ℒ₂ → ℒ₁ ⟶ ℒ₃
F ∘ G = ⟪ F .funMorph ⟨∘⟩ G .funMorph , F .relMorph ⟨∘⟩ G .relMorph ⟫ where open _⟶_

open _⟶_

homExt : {F G : ℒ₁ ⟶ ℒ₂} → (λ {n} → funMorph F {n}) ≡ funMorph G → (λ {n} → relMorph F {n}) ≡ relMorph G → F ≡ G
homExt funMorphEq relMorphEq = cong₂ ⟪_,_⟫ funMorphEq relMorphEq

funMorph-∘ : (G : ℒ₂ ⟶ ℒ₃) (F : ℒ₁ ⟶ ℒ₂) (n : ℕ) → funMorph (G ∘ F) {n} ≡ funMorph G ⟨∘⟩ funMorph F
funMorph-∘ G F n = refl

relMorph-∘ : (G : ℒ₂ ⟶ ℒ₃) (F : ℒ₁ ⟶ ℒ₂) (n : ℕ) → relMorph (G ∘ F) {n} ≡ relMorph G ⟨∘⟩ relMorph F
relMorph-∘ G F n = refl
