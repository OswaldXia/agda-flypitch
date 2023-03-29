{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Constructions.Henkin.Properties (ℒ : Language {u}) where

open import FOL.Constructions.Henkin using (∞-language; ∞-theory)
open import FOL.Bounded.PropertiesOfTheory (∞-language ℒ) using (hasEnoughConstants)

open import Function using (_$_)
open import Data.Product using (_,_)

∞-theory-hasEnoughConstants : ∀ T → hasEnoughConstants $ ∞-theory T
∞-theory-hasEnoughConstants T φ = {!   !}
