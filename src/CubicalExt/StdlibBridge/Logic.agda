{-# OPTIONS --cubical --safe #-}

module CubicalExt.StdlibBridge.Logic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Functions.Logic public
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.HITs.PropositionalTruncation using (squash₁; map)

open import Function using (_$_)
open import StdlibExt.Relation.Binary.PropositionalEquivalence ℓ-zero as Iff hiding (map; sym)

private variable
  ℓ : Level
  A B : Type ℓ
  P Q : hProp ℓ

propTruncExt : A ↔ B → ∥ A ∥ₚ ≡ ∥ B ∥ₚ
propTruncExt iff = Σ≡Prop (λ _ → isPropIsProp) $ ua $ isoToEquiv $ iso
  (map $ to iff ⟨$⟩_) (map $ from iff ⟨$⟩_) (λ x → squash₁ _ x) (λ x → squash₁ _ x)

hPropExt : ⟨ P ⟩ ↔ ⟨ Q ⟩ → P ≡ Q
hPropExt iff = ⇒∶ to iff ⟨$⟩_ ⇐∶ from iff ⟨$⟩_

path↔path : ∀ {a b c d : A} → a ≡ b → c ≡ d → (a ≡ c) ↔ (b ≡ d)
path↔path a≡b c≡d = mk↔
  (λ a≡c → sym a≡b ∙ a≡c ∙ c≡d)
  (λ b≡d → a≡b ∙ b≡d ∙ sym c≡d)
