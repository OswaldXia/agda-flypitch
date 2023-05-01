{-# OPTIONS --cubical --safe #-}

open import CubicalExt.Axiom.Choice
module CubicalExt.Logic.ClassicalChoice (ac : ∀ {ℓ ℓ' ℓ''} → AC ℓ ℓ' ℓ'') where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (∃-syntax)
