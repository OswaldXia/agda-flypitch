{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Bounded.Casting ⦃ em : EM ⦄ (ℒ : Language {u}) where
import FOL.Base ⦃ em ⦄ ℒ as Free
open import FOL.Bounded.Base ⦃ em ⦄ ℒ

open import Data.Fin using (Fin; inject≤)
open import Data.Fin.Properties using (toℕ-inject≤)
open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

private variable
  m n : ℕ

castₜ : m ≤ n → Termₗ m l → Termₗ n l
castₜ m≤n (var k)     = var (inject≤ k m≤n)
castₜ m≤n (func f)    = func f
castₜ m≤n (app t₁ t₂) = app (castₜ m≤n t₁) (castₜ m≤n t₂)

unbound-castₜ : (m≤n : m ≤ n) (t : Termₗ m l) → unboundₜ (castₜ m≤n t) ≡ unboundₜ t
unbound-castₜ m≤n (var k)     = cong Free.var (toℕ-inject≤ k m≤n)
unbound-castₜ m≤n (func f)    = refl
unbound-castₜ m≤n (app t₁ t₂) = cong₂ Free.app (unbound-castₜ m≤n t₁) (unbound-castₜ m≤n t₂)
