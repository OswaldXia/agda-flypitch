{-# OPTIONS --cubical --safe #-}

open import CubicalExt.Axiom.Choice
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
module CubicalExt.Logic.Diaconescu (ac : ∀ {ℓ ℓ' ℓ''} → AC ℓ ℓ' ℓ'') {ℓ} (P : hProp ℓ) where

open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import CubicalExt.Axiom.ExcludedMiddle


