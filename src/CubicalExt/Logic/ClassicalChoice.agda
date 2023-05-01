{-# OPTIONS --cubical --safe #-}

open import CubicalExt.Axiom.Choice
module CubicalExt.Logic.ClassicalChoice (ac : ∀ {ℓ ℓ'} → AC ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import CubicalExt.Axiom.ExcludedMiddle
open import CubicalExt.Logic.Diaconescu using (Diaconescu)
open import Function using (it)

private variable
  ℓ ℓ' ℓ'' : Level

acDep : ACDep ℓ ℓ' ℓ''
acDep = AC→ACDep ac

acRel : ACRel ℓ ℓ' ℓ''
acRel = AC→ACRel ac

surjectionHasRightInverse : SurjectionHasRightInverse ℓ ℓ'
surjectionHasRightInverse Aset Bset sur = acRel Bset Aset (λ _ _ → Bset _ _) sur

em : EM ℓ
em = Diaconescu (λ _ _ → it) surjectionHasRightInverse
