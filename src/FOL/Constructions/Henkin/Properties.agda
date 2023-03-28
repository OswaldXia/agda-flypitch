{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Constructions.Henkin.Properties (ℒ : Language {u}) where

open import FOL.Constructions.Henkin using (∞-language; ∞-theory)
open import FOL.Bounded.PropertiesOfTheory (∞-language ℒ) using (maximal)

open import Function using (_$_)

∞-theory-maximal : ∀ T → maximal $ ∞-theory T
∞-theory-maximal T = {!   !}
