{-# OPTIONS --cubical --safe #-}

open import CubicalExt.Axiom.Choice
module CubicalExt.Logic.ClassicalChoice (ac : ∀ {ℓ ℓ'} → AC ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

private variable
  ℓ ℓ' ℓ'' : Level
  A B : Type ℓ
  f : A → B

acDep : ACDep ℓ ℓ' ℓ''
acDep = AC→ACDep ac

acRel : ACRel ℓ ℓ' ℓ''
acRel = AC→ACRel ac

isSurjection→section : isSet A → isSet B → isSurjection f → ∃[ g ∈ (B → A) ] section f g
isSurjection→section Aset Bset sur = acRel Bset Aset (λ _ _ → Bset _ _) sur
