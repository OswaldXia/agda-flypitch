{-# OPTIONS --cubical --safe #-}

module CubicalExt.HITs.SetTruncation where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_; _$_)
open import Cubical.HITs.SetTruncation public

private variable
  ℓ : Level
  A B C : Type ℓ

map-functorial : (f : A → B) (g : B → C) → map (g ∘ f) ≡ map g ∘ map f
map-functorial f g = funExt $ λ x → elim {B = λ x → map (g ∘ f) x ≡ (map g ∘ map f) x}
  (λ _ → isProp→isSet $ isSetSetTrunc _ _) (λ _ → refl) x
