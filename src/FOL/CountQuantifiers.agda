{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.CountQuantifiers (ℒ : Language {u}) where

open import FOL.Base ℒ
open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

count∀ : Formulaₗ l → ℕ
count∀ ⊥ = 0
count∀ (rel R) = 0
count∀ (appᵣ φ t) = 0
count∀ (t₁ ≈ t₂) = 0
count∀ (φ₁ ⇒ φ₂) = count∀ φ₁ + count∀ φ₂
count∀ (∀' φ) = suc (count∀ φ)

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
