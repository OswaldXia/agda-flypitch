{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Lemmas.QuantifierCount (ℒ : Language {u}) where

open import FOL.Base ℒ
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

count∀OfRel : (r : Formulaₗ (suc l)) → count∀ r ≡ 0
count∀OfRel (rel R) = refl
count∀OfRel (appᵣ r t) = refl

count∀OfSubst : (φ : Formulaₗ l) (s : Term) (n : ℕ) → count∀ (φ [ s / n ]) ≡ count∀ φ
count∀OfSubst ⊥ s n = refl
count∀OfSubst (rel R) s n = refl
count∀OfSubst (appᵣ φ t) s n = refl
count∀OfSubst (t₁ ≈ t₂) s n = refl
count∀OfSubst (φ₁ ⇒ φ₂) s n = cong₂ _+_ (count∀OfSubst φ₁ s n) (count∀OfSubst φ₂ s n)
count∀OfSubst (∀' φ) s n = cong suc (count∀OfSubst φ s (suc n))
