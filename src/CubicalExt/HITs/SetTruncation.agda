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

recComp : (f : A → B) (g : B → C) → rec squash₂ (∣_∣₂ ∘ g) ∘ rec squash₂ (∣_∣₂ ∘ f) ≡ rec squash₂ (∣_∣₂ ∘ g ∘ f)
recComp f g = funExt $ elim (λ _ → isSet→isGroupoid squash₂ _ _) λ _ → refl

recComp2 : (f : A → B → C) (g : C → D) →
  rec squash₂ (∣_∣₂ ∘ g) ∘₂ rec2 squash₂ (∣_∣₂ ∘₂ f) ≡ rec2 squash₂ (∣_∣₂ ∘₂ g ∘₂ f)
recComp2 f g = funExt λ a → funExt λ b → elim2
  {C = λ a b → (rec squash₂ (∣_∣₂ ∘ g) ∘₂ rec2 squash₂ (∣_∣₂ ∘₂ f)) a b ≡ rec2 squash₂ (∣_∣₂ ∘₂ g ∘₂ f) a b}
  (λ _ _ → isSet→isGroupoid squash₂ _ _) (λ _ _ → refl) a b

map2 : (A → B → C) → ∥ A ∥₂ → ∥ B ∥₂ → ∥ C ∥₂
map2 f = rec2 squash₂ (λ x y → ∣ f x y ∣₂)

map-functorial : (f : A → B) (g : B → C) → map (g ∘ f) ≡ map g ∘ map f
map-functorial f g = funExt $ λ x → elim {B = λ x → map (g ∘ f) x ≡ (map g ∘ map f) x}
  (λ _ → isProp→isSet $ squash₂ _ _) (λ _ → refl) x
