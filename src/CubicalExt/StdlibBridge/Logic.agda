{-# OPTIONS --cubical --safe #-}

module CubicalExt.StdlibBridge.Logic where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude using (isPropIsProp)
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Functions.Logic public
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.HITs.PropositionalTruncation using (squash₁; map)

open import Function using (_$_)
open import StdlibExt.Relation.Binary.PropositionalEquivalence ℓ-zero as Iff hiding (map)

private variable
  ℓ : Level
  A B : Type ℓ
  P Q : hProp ℓ

propTruncExt : A ↔ B → ∥ A ∥ₚ ≡ ∥ B ∥ₚ
propTruncExt iff = Σ≡Prop (λ _ → isPropIsProp) $ ua $ isoToEquiv $ iso
  (map $ to iff ⟨$⟩_) (map $ from iff ⟨$⟩_) (λ x → squash₁ _ x) (λ x → squash₁ _ x)

hPropExt : ⟨ P ⟩ ↔ ⟨ Q ⟩ → P ≡ Q
hPropExt iff = ⇒∶ to iff ⟨$⟩_ ⇐∶ from iff ⟨$⟩_