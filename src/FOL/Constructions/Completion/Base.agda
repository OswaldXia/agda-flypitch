{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Constructions.Completion.Base (ℒ : Language {u}) where

open import FOL.Bounded.Syntactics ℒ
open import FOL.PropertiesOfTheory.Base ℒ

open import Cubical.Foundations.Prelude
open import CubicalExt.Foundations.Powerset*
open import Cubical.Data.Sigma using () renaming (_×_ to infixr 3 _×_)

ConsistentExtension : Theory → Type (ℓ-suc u)
ConsistentExtension T = Σ[ T' ∈ Theory ] Con T' × T ⊆ T'
