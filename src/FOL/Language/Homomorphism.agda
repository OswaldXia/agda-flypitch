{-# OPTIONS --cubical --safe #-}

module FOL.Language.Homomorphism {u} where

open import FOL.Language using (Language)
open import FOL.Language.Homomorphism.Base {u} public

private variable
  ℒ₁ ℒ₂ : Language

open import FOL.Language.Homomorphism.OnBounded.Base {u}
module OnBounded (F : ℒ₁ ⟶ ℒ₂) where
  open Definitions F public
open Definitions public
open import FOL.Language.Homomorphism.OnBounded.Properties {u} public
