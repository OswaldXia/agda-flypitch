{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Synthetic.Axiom.Base where
open import Synthetic.PartialFunction

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ : Level
  A : Type ℓ

universal : (ℕ → ℕ → part A) → Type
universal {A} Θ = (f : ℕ → part A) → ∃ _ λ c → ∀ x y → f x ≐ y ↔ Θ c x ≐ y

EPFᴺ : Type
EPFᴺ = Σ (ℕ → ℕ → part ℕ) universal

EPFᴮ : Type
EPFᴮ = Σ (ℕ → ℕ → part Bool) universal
