{-# OPTIONS --cubical --safe #-}

module CubicalExt.HITs.SetTruncation where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_; _$_)
open import Cubical.Foundations.HLevels using (isSetΠ)
open import Cubical.HITs.SetTruncation public

private variable
  ℓ : Level
  A B C : Type ℓ

rec2' : isSet C → (A → B → C) → ∥ A ∥₂ → ∥ B ∥₂ → C
rec2' Cset f = rec (isSetΠ λ _ → Cset) λ x → rec Cset (f x)

map2 : (A → B → C) → ∥ A ∥₂ → ∥ B ∥₂ → ∥ C ∥₂
map2 f = rec2' squash₂ (λ x y → ∣ f x y ∣₂)

map-functorial : (f : A → B) (g : B → C) → map (g ∘ f) ≡ map g ∘ map f
map-functorial f g = funExt $ λ x → elim {B = λ x → map (g ∘ f) x ≡ (map g ∘ map f) x}
  (λ _ → isProp→isSet $ squash₂ _ _) (λ _ → refl) x
