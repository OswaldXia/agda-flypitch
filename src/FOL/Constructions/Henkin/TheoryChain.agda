{-# OPTIONS --cubical --safe #-}

module FOL.Constructions.Henkin.TheoryChain u where
open import FOL.Constructions.Henkin.Base
open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Constructions.Henkin.FormulaChain u as Φ
  using (formulaChain; formulaComparison; formulaComparisonFiber)
open import FOL.Bounded.Base using (Formula; Sentence; Theory)
open import FOL.Language hiding (u)
open Language {u}

import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_)
open LHom._⟶_ using (funMorph)

open import Tools.DirectedDiagram using (DirectedDiagram)
open DirectedDiagram using (Colimit; Coproduct)
open import FOL.Language.DirectedDiagram using (DirectedDiagramLanguage)

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude using (refl)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.SetQuotients using ([_]; eq/; squash/)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim)
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; squash₂; rec)

open import StdlibExt.Data.Nat hiding (_/_)
open import Function using (_∘_; _$_)
open import StdlibExt.Relation.Unary using (_∪_; _⟦_⟧; ⋃_; replacement-syntax)

witnessOf : ∥ Formula ℒ 1 ∥₂ → Constant $ languageStep ℒ
witnessOf = witness

[_witnessing_] : Constant ℒ → Formula ℒ 1 → Sentence ℒ
[_witnessing_] {ℒ} c φ = (∃' φ) ⇒ φ [ const c / 0 ] where
  open import FOL.Bounded.Base ℒ using (∃'_; _⇒_; const)
  open import FOL.Bounded.Substitution ℒ

theoryStep : Theory ℒ → Theory $ languageStep ℒ
theoryStep {ℒ} Γ = theoryMorph Γ ∪ ｛ [ witnessOf ∣ φ ∣₂ witnessing formulaMorph φ ] ∣ φ ∈ Formula ℒ 1 ｝
  where open LHom.Bounded languageMorph

[_]-theory : ∀ n → Theory ℒ → Theory $ [ n ]-language ℒ
[ zero ]-theory T = T
[ suc n ]-theory T = theoryStep $ [ n ]-theory T

[_]-∞-theory : ∀ n → Theory ℒ → Theory $ ∞-language ℒ
[ n ]-∞-theory T = sentenceMorph ⟦ [ n ]-theory T ⟧
  where open LHom.Bounded (languageCanonicalMorph n)

∞-theory : Theory ℒ → Theory $ ∞-language ℒ
∞-theory T = ⋃ (λ n → [ n ]-∞-theory T)

∞-witness : {T : Theory ℒ} (φ : Formula (∞-language ℒ) 1) →
  ∃[ c ∈ Constant $ ∞-language ℒ ]
  Σ[ φ∞ ∈ Colimit (formulaChain ℒ 1 0) ]
  Σ[ φₚ@(i , φᵢ) ∈ Coproduct (formulaChain ℒ 1 0) ]
    [ φₚ ] ≡ φ∞
  × formulaComparison φ∞ ≡ ∣ φ ∣₂
  × c ≡ languageCanonicalMorph (suc i) .funMorph (witnessOf φᵢ)
∞-witness {ℒ} φ = let (φ∞ , Hφ∞) = formulaComparisonFiber φ in
  elim {P = λ _ →
      ∃[ c ∈ Constant $ ∞-language ℒ ]
      Σ[ φ∞ ∈ Colimit (formulaChain ℒ 1 0) ]
      Σ[ φₚ@(i , φᵢ) ∈ Coproduct (formulaChain ℒ 1 0) ]
        [ φₚ ] ≡ φ∞
      × formulaComparison φ∞ ≡ ∣ φ ∣₂
      × c ≡ languageCanonicalMorph (suc i) .funMorph (witnessOf φᵢ)}
    (λ _ → squash₁)
    (λ (φₚ@(i , φᵢ) , Hi) →
      ∣ languageCanonicalMorph (suc i) .funMorph (witnessOf φᵢ)
      , φ∞ , φₚ , Hi , Hφ∞ , refl
      ∣₁)
    (representative φ∞)
  where open DirectedDiagram (formulaChain ℒ 1 0) using (representative)
