{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module FOL.Constructions.Henkin.Witness u where
open import FOL.Constructions.Henkin.Base
open import FOL.Constructions.Henkin.LanguageChain u
  using (obj; languageStep; languageMorph; ∞-language; languageCanonicalMorph)
open import FOL.Constructions.Henkin.FormulaChain u
  using (formulaChain; formulaComparison; formulaComparisonFiber)
open import FOL.Bounded.Base using (Formula; Sentence)
open import FOL.Language hiding (u)
open Language {u}

import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_)
open LHom._⟶_ using (funMorph)

open import Tools.DirectedDiagram using (DirectedDiagram; Cocone)
open DirectedDiagram using (Colimit; Coproduct)

open import Cubical.Core.Primitives
open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (refl)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
import Cubical.Data.Sum as ⊎
open import Cubical.Functions.Logic using (inl; inr)
open import Cubical.HITs.SetQuotients using ([_])
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim)
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂)

open import StdlibExt.Data.Nat hiding (_/_)
open import Function using (_$_)

witnessOf : ∥ Formula ℒ 1 ∥₂ → Constant $ languageStep ℒ
witnessOf = witness

witnessStatement : Formula ℒ 1 → ∥ Sentence $ languageStep ℒ ∥₂
witnessStatement {ℒ} φ = ∣ [ witnessOf ∣ φ ∣₂ witnessing formulaMorph φ ] ∣₂
  where open LHom.Bounded (languageMorph {ℒ}) using (formulaMorph)
        open import FOL.Bounded.PropertiesOfTheory (languageStep ℒ) using ([_witnessing_])

∞-witness : ∀ {i} → ∥ Formula (obj ℒ i) 1 ∥₂ → Constant (∞-language ℒ)
∞-witness {_} {i} φ = languageCanonicalMorph (suc i) .funMorph (witnessOf φ)

∞-Witnessing : (φ : Formula (∞-language ℒ) 1) → Type u
∞-Witnessing {ℒ} φ =
  ∃[ c ∈ Constant $ ∞-language ℒ ]
  Σ[ φ∞ ∈ Colimit (formulaChain ℒ 1 0) ]
  Σ[ φₚ@(i , φᵢ) ∈ Coproduct (formulaChain ℒ 1 0) ]
    [ φₚ ] ≡ φ∞
  × formulaComparison φ∞ ≡ ∣ φ ∣₂
  × c ≡ languageCanonicalMorph (suc i) .funMorph (witnessOf φᵢ)

∞-witnessing : (φ : Formula (∞-language ℒ) 1) → ∞-Witnessing φ
∞-witnessing {ℒ} φ = let (φ∞ , Hφ∞) = formulaComparisonFiber φ in
  elim {P = λ _ → ∞-Witnessing φ}
    (λ _ → squash₁)
    (λ { (φₚ@(i , φᵢ) , Hi) →
      ∣ ∞-witness φᵢ , φ∞ , φₚ , Hi , Hφ∞ , refl ∣₁
    })
    (representative φ∞)
  where open DirectedDiagram (formulaChain ℒ 1 0) using (representative)
