{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Bounded.Lemmas.QuantifierCounting (ℒ : Language {u}) where

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Manipulations.Substitution.Closed ℒ
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

private variable
  n : ℕ

-- currently not used
count∀OfRel : (φ : Formulaₗ n (suc l)) → count∀ φ ≡ 0
count∀OfRel (rel R)     = refl
count∀OfRel (appᵣ φ t)  = refl

count∀OfSubst : (φ : Formulaₗ (suc n) l) (s : ClosedTerm) → count∀ (φ [≔ s ]) ≡ count∀ φ
count∀OfSubst ⊥           s = refl
count∀OfSubst (rel R)     s = refl
count∀OfSubst (appᵣ φ t)  s = refl
count∀OfSubst (t₁ ≈ t₂)   s = refl
count∀OfSubst (φ₁ ⇒ φ₂)   s = cong₂ _+_ (count∀OfSubst φ₁ s) (count∀OfSubst φ₂ s)
count∀OfSubst (∀' φ)      s = cong suc (count∀OfSubst φ s)
