{-# OPTIONS --cubical #-}

open import FOL.Language
open import FOL.Bounded.Base using (Theory)
module FOL.Properties.Completeness {ℒ : Language {u}} (T : Theory ℒ) where

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Interpretation ℒ
open import FOL.Bounded.PropertiesOfTheory ℒ
open import FOL.Properties.Soundness ℒ
open import FOL.Constructions.Henkin

open import CubicalExt.Classical
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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
  , reductId (nonemptyDomain {!   !})
  , {!   !}
  where open import FOL.Structure.Reduction (henkinization ℒ)
        open import FOL.Constructions.TermModel (∞-theory T)
