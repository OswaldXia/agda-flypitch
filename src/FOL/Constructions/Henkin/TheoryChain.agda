{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module FOL.Constructions.Henkin.TheoryChain u where
open import FOL.Constructions.Henkin.Base
open import FOL.Constructions.Henkin.LanguageChain u
  using (obj; languageStep; languageMorph; [_]-language; ∞-language; languageCanonicalMorph)
open import FOL.Constructions.Henkin.FormulaChain u
  using (formulaChain; coconeOfFormulaChain; formulaComparison; formulaComparisonFiber)
open import FOL.Bounded.Base using (Formula; Sentence; Theory)
open import FOL.Language hiding (u)
open Language {u}

import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_)
open LHom._⟶_ using (funMorph)

open import Tools.DirectedDiagram using (DirectedDiagram; Cocone)
open DirectedDiagram using (Colimit; Coproduct)
open import FOL.Language.DirectedDiagram using (DirectedDiagramLanguage)

open import Cubical.Core.Primitives
open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (refl)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
import Cubical.Data.Sum as ⊎
open import Cubical.Functions.Logic using (inl; inr)
open import Cubical.HITs.SetQuotients using ([_]; eq/; squash/)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim)
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; squash₂; rec)

open import StdlibExt.Data.Nat hiding (_/_)
open import Function using (_∘_; _∘₂_; _$_)
open import CubicalExt.Foundations.Powerset* using (_∈_; ∈-isProp; _∪_; ⋃_; _⟦_⟧; replacement-syntax)

module _ {ℒ : Language} where
  open LHom.Bounded (languageMorph {ℒ})

  witnessOf : ∥ Formula ℒ 1 ∥₂ → Constant $ languageStep ℒ
  witnessOf = witness

  witnessStatement : Formula ℒ 1 → ∥ Sentence $ languageStep ℒ ∥₂
  witnessStatement φ = ∣ [ witnessOf ∣ φ ∣₂ witnessing formulaMorph φ ] ∣₂
    where open import FOL.Bounded.PropertiesOfTheory (languageStep ℒ) using ([_witnessing_])

  theoryStep : Theory ℒ → Theory $ languageStep ℒ
  theoryStep Γ = theoryMorph Γ ∪ ｛ witnessStatement φ ∣ φ ∈ Formula ℒ 1 ｝

[_]-theory : ∀ n → Theory ℒ → Theory $ [ n ]-language ℒ
[ zero ]-theory T = T
[ suc n ]-theory T = theoryStep $ [ n ]-theory T

[_]→∞-theory : ℕ → Theory ℒ → Theory $ ∞-language ℒ
[ n ]→∞-theory T = theoryMorph ([ n ]-theory T)
  where open LHom.Bounded (languageCanonicalMorph n)

∞-theory : Theory ℒ → Theory $ ∞-language ℒ
∞-theory T = ⋃ (λ n → [ n ]→∞-theory T)

module _ {ℒ} where
  open Cocone (coconeOfFormulaChain ℒ 0 0) using (map)

  ∈-∞-theory : ∀ {T : Theory ℒ} (i : ℕ) (φ : ∥ Sentence $ obj ℒ $ suc i ∥₂) →
    φ ∈ [ suc i ]-theory T → map (suc i) φ ∈ [ suc i ]→∞-theory T
  ∈-∞-theory {ℒ} i φ = elim (λ _ → ∈-isProp _ _)
    λ { (⊎.inl ∈) → ∣ φ , inl ∈ , reflId ∣₁
      ; (⊎.inr ∈) → ∣ φ , inr ∈ , reflId ∣₁ }

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
