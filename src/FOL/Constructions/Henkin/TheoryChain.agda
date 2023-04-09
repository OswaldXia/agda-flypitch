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

open import Cubical.Core.Primitives renaming (_≡_ to _≡ₚ_)
open import Cubical.Foundations.Prelude using (step-≡; _≡⟨⟩_; _∎)
open import Cubical.Foundations.HLevels using (isSet→isGroupoid)
open import Cubical.Data.Sigma using () renaming (_×_ to infixr 3 _×_)
open import Cubical.Data.Equality using (eqToPath; pathToEq; reflPath; symPath; compPath; congPath)
open import Cubical.HITs.SetQuotients using ([_]; eq/; squash/)
open import Cubical.HITs.PropositionalTruncation
  using (∣_∣₁; squash₁; elim→Set) renaming (elim to elim₁)
open import Cubical.HITs.SetTruncation
  using (∥_∥₂; ∣_∣₂; squash₂; rec; map) renaming (elim to elim₂)

open import StdlibExt.Data.Nat hiding (_/_)
open import Function using (_∘_; _$_)
open import StdlibExt.Relation.Unary using (_∪_; _⟦_⟧; ⋃_; replacement-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

abstract
  morph-witnessOf-comm : ∀ {ℒ i j} .{i~j : i ≤₃ j} (φ : Φ.obj {ℒ} {1} {0} i) →
    morph (s≤₃s i~j) .funMorph (witnessOf φ) ≡ₚ witnessOf (Φ.morph i~j φ)
  morph-witnessOf-comm = elim₂ (λ _ → isSet→isGroupoid (isSetHekinFunctions _) _ _) (λ _ → {!   !})

∞-witness : {T : Theory ℒ} (φ : Formula (∞-language ℒ) 1) → Constant $ ∞-language ℒ
∞-witness {ℒ} {T} φ = let (φ∞ , _) = formulaComparisonFiber φ in
  elim→Set (λ _ → squash/)
    (λ ((i , φᵢ) , _) → languageCanonicalMorph (suc i) .funMorph (witnessOf φᵢ))
    (λ ((i , φᵢ) , Hi) ((j , φⱼ) , Hj) → eq/ _ _ $
      elim₁ {P = λ _ → (suc i , witnessOf φᵢ) ≃ (suc j , witnessOf φⱼ)}
        (λ _ → squash₁)
        (λ (k , φₖ , i~k , j~k , H₁ , H₂) →
          ∣ suc k , witnessOf φₖ , s≤₃s i~k , s≤₃s j~k
          , (pathToEq $
              morph (s≤₃s i~k) .funMorph (witnessOf φᵢ) ≡⟨ morph-witnessOf-comm _ ⟩
              witnessOf (Φ.morph i~k φᵢ)                ≡⟨ congPath witnessOf (eqToPath H₁) ⟩
              witnessOf φₖ                              ∎)
          , (pathToEq $
              morph (s≤₃s j~k) .funMorph (witnessOf φⱼ) ≡⟨ morph-witnessOf-comm _ ⟩
              witnessOf (Φ.morph j~k φⱼ)                ≡⟨ congPath witnessOf (eqToPath H₂) ⟩
              witnessOf φₖ                              ∎)
          ∣₁)
        (effective $ compPath Hi $ symPath Hj))
    (representative φ∞)
  where open DirectedDiagram (formulaChain ℒ 1 0) using (representative; effective)
        open DirectedDiagramLanguage (languageChain ℒ) using (functionsᴰ)
        open DirectedDiagram (functionsᴰ 0) using (_≃_)
