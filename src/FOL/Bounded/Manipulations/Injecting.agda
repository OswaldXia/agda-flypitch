{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Bounded.Manipulations.Injecting (ℒ : Language {u}) where
import FOL.Base ℒ as Free
open import FOL.Bounded.Base ℒ

open import Data.Fin using (Fin; inject≤)
open import Data.Fin.Properties using (toℕ-inject≤)
open import Data.Nat using (ℕ; suc; _≤_; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

private variable
  m n : ℕ

injectₜ : m ≤ n → Termₗ m l → Termₗ n l
injectₜ m≤n (var k)     = var (inject≤ k m≤n)
injectₜ m≤n (func f)    = func f
injectₜ m≤n (app t₁ t₂) = app (injectₜ m≤n t₁) (injectₜ m≤n t₂)

inject : m ≤ n → Formulaₗ m l → Formulaₗ n l
inject m≤n ⊥          = ⊥
inject m≤n (rel R)    = rel R
inject m≤n (appᵣ φ t) = appᵣ (inject m≤n φ) (injectₜ m≤n t)
inject m≤n (t₁ ≈ t₂)  = injectₜ m≤n t₁ ≈ injectₜ m≤n t₂
inject m≤n (φ₁ ⇒ φ₂)  = inject m≤n φ₁ ⇒ inject m≤n φ₂
inject m≤n (∀' φ)     = ∀' inject (s≤s m≤n) φ

unbound-injectₜ : (m≤n : m ≤ n) (t : Termₗ m l) → unboundₜ (injectₜ m≤n t) ≡ unboundₜ t
unbound-injectₜ m≤n (var k)     = cong Free.var (toℕ-inject≤ k m≤n)
unbound-injectₜ m≤n (func f)    = refl
unbound-injectₜ m≤n (app t₁ t₂) = cong₂ Free.app (unbound-injectₜ m≤n t₁) (unbound-injectₜ m≤n t₂)

unbound-inject : (m≤n : m ≤ n) (φ : Formulaₗ m l) → unbound (inject m≤n φ) ≡ unbound φ
unbound-inject m≤n ⊥          = refl
unbound-inject m≤n (rel R)    = refl
unbound-inject m≤n (appᵣ φ t) = cong₂ Free.appᵣ (unbound-inject m≤n φ) (unbound-injectₜ m≤n t)
unbound-inject m≤n (t₁ ≈ t₂)  = cong₂ Free._≈_ (unbound-injectₜ m≤n t₁) (unbound-injectₜ m≤n t₂)
unbound-inject m≤n (φ₁ ⇒ φ₂)  = cong₂ Free._⇒_ (unbound-inject m≤n φ₁) (unbound-inject m≤n φ₂)
unbound-inject m≤n (∀' φ)     = cong Free.∀'_ (unbound-inject (s≤s m≤n) φ)
