{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Bounded.Syntactics using (Theory)
open import FOL.Bounded.PropertiesOfTheory using (complete; hasEnoughConstants)
module FOL.Constructions.TermModel.Properties {ℒ : Language {u}}
  (T : Theory ℒ) (H₁ : complete ℒ T) (H₂ : hasEnoughConstants ℒ T) where
open import FOL.Constructions.TermModel.Base using (termModel)

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.CountQuantifiers ℒ

open import Data.Nat
open import Data.Vec using (Vec; []; _∷_)
open import StdlibExt.Relation.Binary.PropositionalEquivalence u

termModelReflects : {n : ℕ} (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  count∀ (unbound φ) < n → T ⊢ appsᵣ φ xs ↔ termModel T ⊨ˢ appsᵣ φ xs
termModelReflects {_} {zero} _ _ ()
termModelReflects {0} {suc n} ⊥           xs < = {!   !}
termModelReflects {l} {suc n} (rel R)     xs < = {!   !}
termModelReflects {l} {suc n} (appᵣ φ t)  xs < = {!   !}
termModelReflects {0} {suc n} (t₁ ≈ t₂)   xs < = {!   !}
termModelReflects {0} {suc n} (φ ⇒ φ₁)    xs < = {!   !}
termModelReflects {0} {suc n} (∀' φ)      xs < = {!   !}
