{-# OPTIONS --cubical --safe #-}
{- currently not used -}

open import FOL.Language
module FOL.Lemmas.QuantifierCounting (ℒ : Language {u}) where

open import FOL.Base ℒ
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

count∀OfRel : (φ : Formulaₗ (suc l)) → count∀ φ ≡ 0
count∀OfRel (rel R)     = refl
count∀OfRel (appᵣ φ t)  = refl

count∀OfSubst : (φ : Formulaₗ l) (n : ℕ) (s : Term) → count∀ (φ [ n ≔ s ]) ≡ count∀ φ
count∀OfSubst ⊥           n s = refl
count∀OfSubst (rel R)     n s = refl
count∀OfSubst (appᵣ φ t)  n s = refl
count∀OfSubst (t₁ ≈ t₂)   n s = refl
count∀OfSubst (φ₁ ⇒ φ₂)   n s = cong₂ _+_ (count∀OfSubst φ₁ n s) (count∀OfSubst φ₂ n s)
count∀OfSubst (∀' φ)      n s = cong suc (count∀OfSubst φ (suc n) s)
