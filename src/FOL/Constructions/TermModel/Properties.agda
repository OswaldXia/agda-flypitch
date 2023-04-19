{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

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

open import CubicalExt.Foundations.Powerset* using (_∈_)

open import Data.Nat
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec using (Vec; []; _∷_)
open import StdlibExt.Relation.Binary.PropositionalEquivalence u

termModelReflectsN∀ : {n : ℕ} (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  count∀ (unbound φ) < n → T ⊢ appsᵣ φ xs ↔ termModel T ⊨ˢ appsᵣ φ xs
termModelReflectsN∀ {_} {zero} _ _ ()
termModelReflectsN∀ {0} {suc n} ⊥           xs < = mk↔ {!   !} {!   !}
termModelReflectsN∀ {l} {suc n} (rel R)     xs < = {!   !}
termModelReflectsN∀ {l} {suc n} (appᵣ φ t)  xs < = {!   !}
termModelReflectsN∀ {0} {suc n} (t₁ ≈ t₂)   xs < = {!   !}
termModelReflectsN∀ {0} {suc n} (φ ⇒ φ₁)    xs < = {!   !}
termModelReflectsN∀ {0} {suc n} (∀' φ)      xs < = {!   !}

termModelReflects : (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  T ⊢ appsᵣ φ xs ↔ termModel T ⊨ˢ appsᵣ φ xs
termModelReflects φ xs = termModelReflectsN∀ φ xs  (s≤s ≤-refl)

termModel⊨ : termModel T ⊨ᵀ T
termModel⊨ φ φ∈T = to (termModelReflects φ []) ⟨$⟩ axiom φ∈T

-- completeness for complete theories with enough constants
completeness : (φ : Sentence) → T ⊨ φ → T ⊢ φ
completeness φ T⊨φ = from (termModelReflects φ []) ⟨$⟩ {! termModel T    !}
