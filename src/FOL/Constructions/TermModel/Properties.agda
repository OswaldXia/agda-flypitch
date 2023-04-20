{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import FOL.Bounded.Syntactics using (Theory)
open import FOL.Bounded.PropertiesOfTheory using (complete; hasEnoughConstants)
module FOL.Constructions.TermModel.Properties {ℒ : Language {u}} {T : Theory ℒ}
  (H₁ : complete ℒ T) (H₂ : hasEnoughConstants ℒ T) where
open import FOL.Constructions.TermModel.Base using (nonempty; termModel)

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.CountQuantifiers ℒ

open import Cubical.Foundations.Prelude
open import CubicalExt.Foundations.Powerset* using (_∈_)

open import Data.Nat
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_$_)

termModelSound : {n : ℕ} (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  count∀ (unbound φ) < n → T ⊢ appsᵣ φ xs → termModel T ⊨ˢ appsᵣ φ xs
termModelSound {_} {zero} _ _ ()
termModelSound {0} {suc n} ⊥           xs < = {!   !}
termModelSound {l} {suc n} (rel R)     xs < = {!   !}
termModelSound {l} {suc n} (appᵣ φ t)  xs < = {!   !}
termModelSound {0} {suc n} (t₁ ≈ t₂)   xs < = {!   !}
termModelSound {0} {suc n} (φ ⇒ φ₁)    xs < = {!   !}
termModelSound {0} {suc n} (∀' φ)      xs < = {!   !}

termModelComplete : {n : ℕ} (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  count∀ (unbound φ) < n → termModel T ⊨ˢ appsᵣ φ xs → T ⊢ appsᵣ φ xs
termModelComplete φ xs < = {!   !}

termModelWellDefined : termModel T ⊨ᵀ T
termModelWellDefined φ φ∈T = termModelSound φ [] (s≤s ≤-refl) (axiom φ∈T)

-- completeness for complete theories with enough constants
open Implication (ℓ-suc u) using (_⊨_)
completeness : (φ : Sentence) → T ⊨ φ → T ⊢ φ
completeness φ T⊨φ = termModelComplete φ [] (s≤s ≤-refl) $
  T⊨φ (termModel T) (nonempty T H₂) termModelWellDefined
