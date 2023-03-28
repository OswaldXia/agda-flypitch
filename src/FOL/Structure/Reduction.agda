{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Language.Homomorphism using (_⟶_)
module FOL.Structure.Reduction {ℒ₁ ℒ₂ : Language {u}} (F : ℒ₁ ⟶ ℒ₂) where
open import FOL.Structure.Base {u}

open import Function using (_∘_; id)

reduct : ∀ {v} → Structure ℒ₂ {v} → Structure ℒ₁
reduct 𝒮 = record
  { Domain = Domain
  ; isSetDomain = isSetDomain
  ; funMap = funMap ∘ funMorph
  ; relMap = relMap ∘ relMorph
  } where open Structure ℒ₂ 𝒮
          open _⟶_ F

open Structure

reductId : ∀ {v} {𝒮 : Structure ℒ₂ {v}} → Domain 𝒮 → Domain (reduct 𝒮)
reductId = id
