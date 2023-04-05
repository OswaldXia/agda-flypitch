{-# OPTIONS --cubical --safe #-}

module CubicalExt.HITs.SetTruncation where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSet→isGroupoid)
open import Cubical.Foundations.Function using (_∘_; _$_)
open import Cubical.HITs.SetTruncation public
open import Function using (_∘₂_)

private variable
  ℓ : Level
  A B C D : Type ℓ

recComp : (f : A → B) (g : B → C) (a : ∥ A ∥₂) →
  rec squash₂ (∣_∣₂ ∘ g) (rec squash₂ (∣_∣₂ ∘ f) a) ≡ rec squash₂ (∣_∣₂ ∘ g ∘ f) a
recComp f g = elim (λ _ → isSet→isGroupoid squash₂ _ _) λ _ → refl

recComp2 : (f : A → B → C) (g : C → D) (a : ∥ A ∥₂) (b : ∥ B ∥₂) →
  rec squash₂ (∣_∣₂ ∘ g) (rec2 squash₂ (∣_∣₂ ∘₂ f) a b) ≡ rec2 squash₂ (∣_∣₂ ∘₂ g ∘₂ f) a b
recComp2 f g = elim2 (λ _ _ → isSet→isGroupoid squash₂ _ _) (λ _ _ → refl)

map2 : (A → B → C) → ∥ A ∥₂ → ∥ B ∥₂ → ∥ C ∥₂
map2 f = rec2 squash₂ (λ x y → ∣ f x y ∣₂)

map-functorial : (f : A → B) (g : B → C) → map (g ∘ f) ≡ map g ∘ map f
map-functorial f g = funExt $ λ x → elim {B = λ x → map (g ∘ f) x ≡ (map g ∘ map f) x}
  (λ _ → isProp→isSet $ squash₂ _ _) (λ _ → refl) x
