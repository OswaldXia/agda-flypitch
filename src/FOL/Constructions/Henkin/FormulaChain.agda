{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module FOL.Constructions.Henkin.FormulaChain u where
open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Constructions.Henkin.TheoryChain u
open import FOL.Bounded.Base using (Formulaₗ)

import FOL.Language.Homomorphism as LHom
open LHom.BoundedProperties

open import Tools.DirectedDiagram using (ℕᴰ; DirectedDiagram; Cocone)
open DirectedDiagram using (Coproduct; Colimit)
open Cocone using (universalMap)
open import FOL.Language.DirectedDiagram using (CoconeLanguage)

open import Cubical.Data.Equality using (pathToEq)
open import CubicalExt.HITs.SetTruncation using (∥_∥₂; squash₂; map; map-functorial)
open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong)

formulaChain : ∀ ℒ n l → DirectedDiagram ℕᴰ
formulaChain ℒ n l = record
  { obj = λ k → ∥ Formulaₗ ([ k ]-language ℒ) n l ∥₂
  ; morph = λ i≤j → map $ formulaMorph $ morph i≤j
  ; functorial = trans (cong (map ∘ λ φ → formulaMorph φ) functorial)
               $ trans (cong map $ formulaMorphComp _ _)
               $ pathToEq $ map-functorial _ _
  } where open LHom.Bounded using (formulaMorph)

coconeOfFormulaChain : ∀ ℒ n l → Cocone (formulaChain ℒ n l)
coconeOfFormulaChain ℒ n l = record
  { Vertex = ∥ Formulaₗ (∞-language ℒ ) n l ∥₂
  ; isSetVertex = squash₂
  ; map = λ i → map $ formulaMorph $ languageCanonicalMorph i
  ; compat = λ i~j → trans (cong (map ∘ λ φ → formulaMorph φ) (coconeOfLanguageChain .compat i~j))
                   $ trans (cong map $ formulaMorphComp _ _)
                   $ pathToEq $ map-functorial _ _
  } where open LHom.Bounded using (formulaMorph)
          open CoconeLanguage using (compat)

formulaComparison : ∀ {ℒ n l} → Colimit (formulaChain ℒ n l) → ∥ Formulaₗ (∞-language ℒ ) n l ∥₂
formulaComparison {ℒ} {n} {l} = universalMap (coconeOfFormulaChain ℒ n l)
