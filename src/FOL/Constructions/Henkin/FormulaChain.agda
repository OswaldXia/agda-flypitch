{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module FOL.Constructions.Henkin.FormulaChain u where
open import FOL.Constructions.Henkin.LanguageChain u
  renaming (obj to langObj ; morph to langMorph; functorial to langFunctorial)
open import FOL.Constructions.Henkin.TermChain u using (termComparisonFiber)
open import FOL.Language using (Language)
open import FOL.Bounded.Base using (Formulaₗ)
open Formulaₗ

import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_) renaming (_∘_ to _◯_)
open LHom.Bounded using (formulaMorph)
open LHom.BoundedProperties

open import Tools.DirectedDiagram using (ℕᴰ; DirectedDiagram; Cocone)
open Cocone using (universalMap)
open import FOL.Language.DirectedDiagram using (DirectedDiagramLanguage; CoconeLanguage)
open CoconeLanguage using (compat)

open import Cubical.Core.Primitives renaming (_≡_ to _≡ₚ_)
open import Cubical.Foundations.Prelude
  using (cong₂; isProp; isSet; isProp→isSet; toPathP; step-≡; _≡⟨⟩_; _∎; _≡$_)
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.HLevels using (isSetΣ; isSet→isGroupoid)
open import Cubical.Data.Equality
  using (eqToPath; pathToEq; reflPath; symPath; compPath; congPath; substPath)
open import Cubical.Data.Sigma using (ΣPathP) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.SetQuotients
  using ([_]; eq/; squash/)
open import Cubical.HITs.PropositionalTruncation
  using (∣_∣₁; squash₁; elim; elim→Set; elim2→Set)
open import CubicalExt.HITs.SetTruncation
  using (∥_∥₂; ∣_∣₂; squash₂; rec; rec2; elim2; recComp2; map; map2; map-functorial)

open import StdlibExt.Data.Nat
open import Data.Nat.Properties
open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong)

abstract
  map-$-formulaMorph-functorial : ∀ {ℒ₁ ℒ₂ ℒ₃ : Language {u}} {n l : ℕ}
    {F₁ : ℒ₁ ⟶ ℒ₂} {F₂ : ℒ₂ ⟶ ℒ₃} {F₃ : ℒ₁ ⟶ ℒ₃} → F₃ ≡ F₂ ◯ F₁ →
    (map $ formulaMorph F₃ {n} {l}) ≡ (map $ formulaMorph F₂) ∘ (map $ formulaMorph F₁)
  map-$-formulaMorph-functorial H = trans (cong (map ∘ λ t → formulaMorph t) H)
    $ trans (cong map $ formulaMorphComp _ _)
    $ pathToEq $ map-functorial _ _

formulaChain : ∀ ℒ n l → DirectedDiagram ℕᴰ
formulaChain ℒ n l = record
  { obj = λ k → ∥ Formulaₗ ([ k ]-language ℒ) n l ∥₂
  ; morph = λ i≤j → map $ formulaMorph $ langMorph i≤j
  ; functorial = map-$-formulaMorph-functorial langFunctorial
  }

coconeOfFormulaChain : ∀ ℒ n l → Cocone (formulaChain ℒ n l)
coconeOfFormulaChain ℒ n l = record
  { Vertex = ∥ Formulaₗ (∞-language ℒ ) n l ∥₂
  ; isSetVertex = squash₂
  ; map = λ i → map $ formulaMorph $ languageCanonicalMorph i
  ; compat = λ i~j → map-$-formulaMorph-functorial (coconeOfLanguageChain .compat i~j)
  }

module _ {ℒ n l} where
  open DirectedDiagram (formulaChain ℒ n l) using (obj; morph; functorial; Colimit) public

  formulaComparison : Colimit → ∥ Formulaₗ (∞-language ℒ) n l ∥₂
  formulaComparison = universalMap (coconeOfFormulaChain ℒ n l)

  _ : ∀ {i} (φ : obj i) → formulaComparison [ i , φ ] ≡ₚ map (formulaMorph $ languageCanonicalMorph i) φ
  _ = λ _ → reflPath

abstract
  isSetFiber : ∀ {ℒ n l} {φ : Formulaₗ (∞-language ℒ) n l} → isSet (fiber formulaComparison ∣ φ ∣₂)
  isSetFiber = isSetΣ squash/ $ λ _ → isProp→isSet $ squash₂ _ _

  formulaComparisonFiber : ∀ {ℒ n l} (φ : Formulaₗ (∞-language ℒ) n l) → fiber formulaComparison ∣ φ ∣₂
  formulaComparisonFiber φ = {!   !}
