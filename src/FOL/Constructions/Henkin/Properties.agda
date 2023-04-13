{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

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
open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (isProp→isSet)
open import Cubical.Functions.Logic using (inl; inr)
open import Cubical.Data.Unit using (tt*)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁) renaming (elim to elim₁)
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; map) renaming (elim to elim₂)
open import CubicalExt.Foundations.Powerset* using (_∈_; ∈-isProp)

open import Data.Nat using (ℕ; suc)
open import Function using (_$_)

∞-theory-hasEnoughConstants : ∀ T → hasEnoughConstants $ ∞-theory T
∞-theory-hasEnoughConstants T φ =
  let Goal = ∃[ c ∈ Constant ] (∞-theory T) ⊢ [ c witnessing φ ] in
  elim₁ {P = λ _ → Goal} (λ _ → squash₁)
    (λ { (c , φ∞ , φₚ@(i , φᵢ) , [φₚ]≡φ∞ , fCφ∞≡∣φ∣₂ , c≡) →
      elim₂ {B = λ _ → Goal} (λ _ → isProp→isSet squash₁)
        (λ ψ → ∣_∣₁ $ c ,_ $ axiom $
          ∣ coconeMap (suc i) (witnessStatement ψ)
          , ∣ suc i , ∈-→∞-theory i (witnessStatement ψ) (inr ∣ ψ , tt* , reflId ∣₁) ∣₁
          , {!   !}
          ∣₁)
        φᵢ
    })
    (∞-witness φ)
