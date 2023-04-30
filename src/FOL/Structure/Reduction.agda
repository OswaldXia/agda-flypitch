{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Language.Homomorphism as LHom using (_⟶_)
module FOL.Structure.Reduction {ℒ₁ ℒ₂ : Language {u}} (F : ℒ₁ ⟶ ℒ₂) where

open import FOL.Structure.Reduction.Base F public
open import FOL.Structure.Reduction.Properties F public
