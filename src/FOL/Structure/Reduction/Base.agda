{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Language.Homomorphism using (_⟶_)
module FOL.Structure.Reduction.Base {ℒ₁ ℒ₂ : Language {u}} (F : ℒ₁ ⟶ ℒ₂) where
open import FOL.Structure.Base {u}
open _⟶_ F

open import Function using (_∘_; id)

⟦_⟧ : ∀ {v} → Structure ℒ₂ {v} → Structure ℒ₁
⟦ 𝒮 ⟧ = record
  { Domain = Domain
  ; isSetDomain = isSetDomain
  ; funMap = funMap ∘ funMorph
  ; relMap = relMap ∘ relMorph
  } where open Structure ℒ₂ 𝒮

reductId : ∀ {v} (𝒮 : Structure ℒ₂ {v}) → Structure.Domain 𝒮 → Structure.Domain ⟦ 𝒮 ⟧
reductId _ = id
