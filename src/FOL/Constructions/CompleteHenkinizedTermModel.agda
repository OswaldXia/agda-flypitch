{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
open import FOL.Bounded.Syntactics using (Theory)
module FOL.Constructions.CompleteHenkinizedTermModel ⦃ _ : ∀ {ℓ} → EM ℓ ⦄ {ℒ : Language {u}} (T : Theory ℒ) where

open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Constructions.Henkin.TheoryChain u
open import FOL.Constructions.Henkin.Properties ℒ
open import FOL.Constructions.TermModel.Base (∞-theory T)

open import FOL.Structure.Base ℒ using (Structure)
open import FOL.Structure.Reduction.Base (henkinization ℒ)
open import FOL.Structure.Reduction.Properties (henkinization ℒ) termModel

open import FOL.Bounded.Semantics ℒ
module _ {ℒ : Language {u}} where
  open import FOL.PropertiesOfTheory.Base ℒ public

open import Function using (_$_)

theModel : Structure
theModel = ⟦ termModel ⟧

modelNonempty : Structure.nonempty theModel
modelNonempty = reductNonempty $ TermModel.nonempty $ ∞-theory-hasEnoughConstants T

modelComplete : Con T → theModel ⊨ᵀ T
modelComplete con = reduct⊨ᵀ T λ φ φ∈T' → termModelWellDefined φ {!   !}
  where H₁ : complete (∞-theory T)
        H₁ = {!   !}
        H₂ = ∞-theory-hasEnoughConstants T
        open import FOL.Constructions.TermModel.Properties H₁ H₂
