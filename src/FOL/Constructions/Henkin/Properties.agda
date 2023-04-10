{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Constructions.Henkin.Properties (ℒ : Language {u}) where
open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Constructions.Henkin.TheoryChain u

open import FOL.Base (∞-language ℒ) using (axiom)
open import FOL.Bounded.Base (∞-language ℒ)
open import FOL.Bounded.Substitution (∞-language ℒ)
open import FOL.Bounded.PropertiesOfTheory (∞-language ℒ) using (hasEnoughConstants)
open Language (∞-language ℒ) using (Constant)

import FOL.Language.Homomorphism as LHom
open LHom.Bounded using (formulaMorph)

open import Cubical.Core.Primitives
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim)
--open import Cubical.HITs.SetTruncation using (∣_∣₂)

open import Data.Nat using (ℕ; suc)
open import Function using (_∘₂_; _$_)
open import StdlibExt.Relation.Unary using (_∈_; _⟦_⟧)

∞-theory-hasEnoughConstants : ∀ T → hasEnoughConstants $ ∞-theory T
∞-theory-hasEnoughConstants T φ = elim
  {P = λ _ → ∃[ c ∈ Constant ] (∞-theory T) ⊢ ∃' φ ⇒ φ [ const c / 0 ]}
  (λ _ → squash₁)
  (λ (c , φ∞ , φₚ@(i , φᵢ) , [φₚ]≡φ∞ , fCφ∞≡∣φ∣₂ , c≡) → (∣_∣₁ ∘₂ _,_) c $ axiom $
    formulaMorph (languageCanonicalMorph (suc i))
      [ witnessOf φᵢ witnessing formulaMorph languageMorph {!   !} ]
  , (suc i , {!   !})
  , {!   !}
  )
  (∞-witness φ)
