{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Bounded.Casting ⦃ em : EM ⦄ (ℒ : Language {u}) where
open import FOL.Bounded.Base ⦃ em ⦄ ℒ

open import Data.Fin using (Fin; inject≤)
open import Data.Nat using (ℕ; _≤_)

private variable
  m n : ℕ

castₜ : m ≤ n → Termₗ m l → Termₗ n l
castₜ m≤n (var k)     = var (inject≤ k m≤n)
castₜ m≤n (func f)    = func f
castₜ m≤n (app t₁ t₂) = app (castₜ m≤n t₁) (castₜ m≤n t₂)
