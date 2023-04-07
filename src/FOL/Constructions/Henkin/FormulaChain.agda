{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module FOL.Constructions.Henkin.FormulaChain u where
open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Constructions.Henkin.TermChain u using (termComparisonFiber)
open import FOL.Language using (Language)
open import FOL.Bounded.Base using (Formulaₗ)
open Formulaₗ

import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_) renaming (_∘_ to _◯_)
open LHom.Bounded using (formulaMorph)
open LHom.BoundedProperties

open import Tools.DirectedDiagram using (ℕᴰ; DirectedDiagram; Cocone)
open DirectedDiagram using (Coproduct; Colimit)
open Cocone using (universalMap)
open import FOL.Language.DirectedDiagram using (DirectedDiagramLanguage; CoconeLanguage)
open CoconeLanguage using (compat)

open import Cubical.Core.Primitives renaming (_≡_ to _≡ₚ_)
open import Cubical.Data.Equality using (pathToEq)
open import CubicalExt.HITs.SetTruncation using (∥_∥₂; squash₂; map; map-functorial)

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
  ; morph = λ i≤j → map $ formulaMorph $ morph i≤j
  ; functorial = map-$-formulaMorph-functorial functorial
  }

coconeOfFormulaChain : ∀ ℒ n l → Cocone (formulaChain ℒ n l)
coconeOfFormulaChain ℒ n l = record
  { Vertex = ∥ Formulaₗ (∞-language ℒ ) n l ∥₂
  ; isSetVertex = squash₂
  ; map = λ i → map $ formulaMorph $ languageCanonicalMorph i
  ; compat = λ i~j → map-$-formulaMorph-functorial (coconeOfLanguageChain .compat i~j)
  }

formulaComparison : ∀ {ℒ n l} → Colimit (formulaChain ℒ n l) → ∥ Formulaₗ (∞-language ℒ ) n l ∥₂
formulaComparison {ℒ} {n} {l} = universalMap (coconeOfFormulaChain ℒ n l)
