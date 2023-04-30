{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Properties.Completeness ⦃ _ : EM ⦄ (ℒ : Language {u}) where

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.PropertiesOfTheory ℒ
open import FOL.Properties.Soundness ℒ

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; map)
open import CubicalExt.Classical
open import Function using (_$_)

private variable
  v : Level
  φ : Sentence
  T : Theory

module InconsistencyConsequence {v} where
  open Implication v

  ¬Con→Soundness : ¬Con T → T ⊦ φ → T ⊨ φ
  ¬Con→Soundness _ = soundness

  ¬Con→Completeness : ¬Con T → T ⊨ φ → T ⊦ φ
  ¬Con→Completeness T⊢⊥ _ = map exfalso T⊢⊥

Model→Con : Model {v} T → Con T
Model→Con (ℳ , a , ℳ⊨T) T⊢⊥ = [ ℳ ]⊭⊥ $ soundness ∣ T⊢⊥ ∣₁ ℳ a ℳ⊨T

Con→Model : Con T → Model T
Con→Model {T} con = theModel , modelNonempty , modelComplete con
  where open import FOL.Constructions.CompleteHenkinizedTermModel T

module _ {v} where
  open Implication v
  Completeness : Type (ℓ-max (ℓ-suc u) (ℓ-suc v))
  Completeness = ∀ {T φ} → T ⊨ φ → T ⊢ φ
