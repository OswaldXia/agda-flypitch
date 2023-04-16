{-# OPTIONS --cubical #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
open import FOL.Bounded.Syntactics using (Theory)
module FOL.Properties.Completeness ⦃ _ : EM ⦄ {ℒ : Language {u}} (T : Theory ℒ) where

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.Bounded.PropertiesOfTheory ℒ
open import FOL.Properties.Soundness ℒ
open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Constructions.Henkin.TheoryChain u

open import Cubical.Core.Primitives
open import Cubical.Data.Sigma using (_×_)
open import CubicalExt.Classical
open import Function using (_$_)

private variable
  φ : Sentence

¬Con→Soundness : ¬Con T → T ⊢ φ → T ⊨ φ
¬Con→Soundness _ = soundness

¬Con→Completeness : ¬Con T → T ⊨ φ → T ⊢ φ
¬Con→Completeness T⊢⊥ _ = exfalso T⊢⊥

existsModel→Con : existsModel T → Con T
existsModel→Con (ℳ , x , ℳ⊨T) T⊢⊥ = [ ℳ ]⊭⊥ (soundness T⊢⊥ ℳ x ℳ⊨T)

Con→existsModel : Con T → existsModel T
Con→existsModel T⊭⊥ =
    reduct termModel
  , reductId {!   !} --(nonemptyDomain {!   !})
  , {!   !}
  where open import FOL.Structure.Reduction (henkinization ℒ)
        open import FOL.Constructions.TermModel (∞-theory T)
