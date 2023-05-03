{-# OPTIONS --cubical --safe #-}

module CubicalExt.Axiom.ExcludedMiddle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Relation.Nullary using (Dec)

private variable
  ℓ : Level
  A : Type ℓ
  B : A → Type ℓ

isPropImplicit : {ℓ : Level} → Type ℓ → Type ℓ
isPropImplicit A = {x y : A} → x ≡ y

EM : (ℓ : Level) → Type (ℓ-suc ℓ)
EM ℓ = {P : Type ℓ} → ⦃ isPropImplicit P ⦄ → Dec P

instance
  isPropImplicitΠIteration : ⦃ H : {x : A} → isPropImplicit (B x) ⦄ → isPropImplicit ((x : A) → B x)
  isPropImplicitΠIteration ⦃ H ⦄ = isPropΠ (λ _ _ _ → H) _ _
