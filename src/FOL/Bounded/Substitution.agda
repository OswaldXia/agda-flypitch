{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Bounded.Substitution ⦃ em : EM ⦄ (ℒ : Language {u}) where
import FOL.Base ⦃ em ⦄ ℒ as Free
open import FOL.Bounded.Base ⦃ em ⦄ ℒ
open import FOL.Bounded.Casting ⦃ em ⦄ ℒ
open import FOL.Bounded.Lifting ⦃ em ⦄ ℒ

open import Data.Fin using (Fin; toℕ; fromℕ<; reduce≥)
open import StdlibExt.Data.Fin.Properties using (toℕ-fromℕ<; toℕ-reduce≥)
open import Data.Nat using (ℕ; suc; _+_; s≤s; z≤n; _≤_)
open import Data.Nat.Properties
open import Function using (_$_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong) renaming (subst to ≡-subst)

private variable
  n m : ℕ

substₜ : (t : Termₗ (suc n + m) l) (s : Term m) → Termₗ (n + m) l
substₜ {n} {m} (var k) s with <-cmp (toℕ k) n
... | tri< k<n _ _  = var $ fromℕ< $ ≤-trans k<n (m≤m+n _ _)
... | tri≈ _ _ _    = castₜ (≡-subst (_≤ n + m) (+-comm n _) ≤-refl) (s ↑ n)
... | tri> _ _ n<k  = var (reduce≥ k (≤-trans (s≤s z≤n) n<k))
substₜ (func f) s = func f
substₜ (app t₁ t₂) s = app (substₜ t₁ s) (substₜ t₂ s)

syntax substₜ {n} t s = t [ s / n ]ₜ

subst : (φ : Formulaₗ (suc n + m) l) (s : Term m) → Formulaₗ (n + m) l
subst ⊥ s = ⊥
subst (rel R) s = rel R
subst (appᵣ φ t) s = appᵣ (subst φ s) (substₜ t s)
subst (t₁ ≈ t₂) s = substₜ t₁ s ≈ substₜ t₂ s
subst (φ₁ ⇒ φ₂) s = subst φ₁ s ⇒ subst φ₂ s
subst (∀' φ) s = ∀' subst φ s

syntax subst {n} φ s = φ [ s / n ]

unbound-substₜ : (t : Termₗ (suc n + m) l) (s : Term m) →
  unboundₜ (t [ s / n ]ₜ) ≡ unboundₜ t Free.[ unboundₜ s / n ]ₜ
unbound-substₜ {n} (var k) s with <-cmp (toℕ k) n
... | tri< k<n _ _  = cong Free.var (toℕ-fromℕ< _)
... | tri≈ _ _ _    = {!   !}
... | tri> _ _ n<k  = cong Free.var (toℕ-reduce≥ k (≤-trans (s≤s z≤n) n<k))
unbound-substₜ (func f) s   = refl
unbound-substₜ (app t t₁) s = {!   !}

unbound-subst : (φ : Formulaₗ (suc n + m) l) (s : Term m) →
  unbound (φ [ s / n ]) ≡ unbound φ Free.[ unboundₜ s / n ]
unbound-subst ⊥ s           = refl
unbound-subst (rel R) s     = refl
unbound-subst (appᵣ φ t) s  = {!   !}
unbound-subst (t₁ ≈ t₂) s   = {!   !}
unbound-subst (φ ⇒ φ₁) s    = {!   !}
unbound-subst (∀' φ) s      = {!   !}
