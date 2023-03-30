{-# OPTIONS --cubical --safe #-}

module CubicalExt.Functions.Logic where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude using (isPropIsProp)
open import Cubical.Foundations.Function using (_$_)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Functions.Logic public
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.HITs.PropositionalTruncation using (isPropPropTrunc; map)

private variable
  ℓ : Level
  A B : Type ℓ

iffToPath : (A → B) → (B → A) → ∥ A ∥ₚ ≡ ∥ B ∥ₚ
iffToPath to from = Σ≡Prop (λ _ → isPropIsProp) $ ua $ isoToEquiv $ iso
  (map to) (map from) (λ x → isPropPropTrunc _ x) (λ x → isPropPropTrunc _ x)
