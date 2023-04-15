{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Constructions.Henkin.Base ⦃ em : EM ⦄ (ℒ : Language {u}) where
open import FOL.Bounded.Base ⦃ em ⦄ ℒ using (Formula)
open Language ℒ

open import Agda.Builtin.Equality using (_≡_; refl)
open import Cubical.Foundations.Prelude using (Type; isSet)
open import Cubical.Data.Nat using (ℕ)
open import CubicalExt.Relation.Nullary using (yes; no; DiscreteEq; DiscreteEq→isSet)

private variable
  n : ℕ

data HekinFunctions : ℕ → Type u where
  include  : ∀ {n} → 𝔉 n → HekinFunctions n
  witness : Formula 1 → HekinFunctions 0

discreteHekinFunctions : DiscreteEq (HekinFunctions n)
discreteHekinFunctions (include _) (witness _) = {!   !}
discreteHekinFunctions (witness _) (include _) = {!   !}
discreteHekinFunctions (include f₁) (include f₂) = {!   !}
discreteHekinFunctions (witness φ₁) (witness φ₂) = {!   !}

isSetHekinFunctions : isSet (HekinFunctions n)
isSetHekinFunctions = DiscreteEq→isSet discreteHekinFunctions
