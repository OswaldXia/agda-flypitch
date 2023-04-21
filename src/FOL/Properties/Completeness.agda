{-# OPTIONS --cubical #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Properties.Completeness ⦃ _ : EM ⦄ (ℒ : Language {u}) where

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.Bounded.PropertiesOfTheory ℒ
open import FOL.Properties.Soundness ℒ
open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Constructions.Henkin.TheoryChain u
open import FOL.Constructions.Henkin.Properties ℒ
open import FOL.Structure.Base using (Structure)

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim; map)
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
Con→Model {T} T⊭⊥ =
    reduct termModel
  , elim {P = λ _ → Structure.nonempty (reduct termModel)} (λ _ → squash₁)
      (λ x → ∣ (reductId {𝒮 = termModel} x) ∣₁)
      (TermModel.nonempty $ ∞-theory-hasEnoughConstants T)
  , {!   !}
  where open import FOL.Structure.Reduction (henkinization ℒ)
        open import FOL.Constructions.TermModel.Base (∞-theory T)

module _ {v} where
  open Implication v
  Completeness : Type (ℓ-max (ℓ-suc u) (ℓ-suc v))
  Completeness = ∀ {T φ} → T ⊨ φ → T ⊢ φ
