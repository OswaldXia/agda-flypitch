{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Constructions.Henkin.Properties (ℒ : Language {u}) where
open import FOL.Constructions.Henkin.LanguageChain u using (∞-language; languageCanonicalMorph)
open import FOL.Constructions.Henkin.FormulaChain u using (coconeOfFormulaChain)
open import FOL.Constructions.Henkin.TheoryChain u

open import FOL.Base (∞-language ℒ) using (axiom)
open import FOL.Bounded.Base (∞-language ℒ)
open import FOL.Bounded.Substitution (∞-language ℒ)
open import FOL.Bounded.PropertiesOfTheory (∞-language ℒ)
  using (hasEnoughConstants; [_witnessing_])
open Language (∞-language ℒ) using (Constant)

import FOL.Language.Homomorphism as LHom
open LHom.Bounded using (formulaMorph)

open import Tools.DirectedDiagram using (Cocone)
open Cocone (coconeOfFormulaChain ℒ 0 0) renaming (map to coconeMap)

open import Cubical.Core.Primitives
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim)
open import Cubical.HITs.SetTruncation using (map)
open import CubicalExt.Foundations.Powerset* using (_∈_)

open import Data.Nat using (ℕ; suc)
open import Function using (_∘_; _∘₂_; _$_)

∞-theory-hasEnoughConstants : ∀ T → hasEnoughConstants $ ∞-theory T
∞-theory-hasEnoughConstants T φ = elim
  {P = λ _ → ∃[ c ∈ Constant ] (∞-theory T) ⊢ [ c witnessing φ ]}
  (λ _ → squash₁)
  (λ { (c , φ∞ , φₚ@(i , φᵢ) , [φₚ]≡φ∞ , fCφ∞≡∣φ∣₂ , c≡) → (∣_∣₁ ∘₂ _,_) c $ axiom $ ∣_∣₁ $
      coconeMap (suc i) (map witnessStatement φᵢ)
    , {!   !}
    , {!   !}
  })
  (∞-witness φ)
