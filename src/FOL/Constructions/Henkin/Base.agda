{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Constructions.Henkin.Base (ℒ : Language {u}) where
open import FOL.Bounded.Base ℒ using (Formula)
open Language ℒ

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude using (isSet)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.HITs.SetTruncation using (∥_∥₂)

data HekinFunctions : ℕ → Type u where
  include  : ∀ {n} → 𝔉 n → HekinFunctions n
  witness : ∥ Formula 1 ∥₂ → HekinFunctions 0
  isSetHekinFunctions : ∀ n → isSet (HekinFunctions n)
