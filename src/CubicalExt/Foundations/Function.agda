
{-# OPTIONS --cubical --safe #-}

module CubicalExt.Foundations.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function public

private variable
  ℓ ℓ' ℓ'' : Level

_$- : ∀ {A : Type ℓ} {B : A → Type ℓ'} → ((x : A) → B x) → ({x : A} → B x)
f $- = f _
{-# INLINE _$- #-}

_$-- : ∀ {A : Type ℓ} {B : Type ℓ'} {C : A → B → Type ℓ''} →
  ((x : A) → (y : B) → C x y) → ({x : A} → {y : B} → C x y)
f $-- = f _ _
{-# INLINE _$- #-}
