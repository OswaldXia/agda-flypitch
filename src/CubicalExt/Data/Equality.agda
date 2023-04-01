{-# OPTIONS --cubical --safe #-}

module CubicalExt.Data.Equality where

open import Cubical.Core.Primitives hiding (_≡_)
open import Cubical.Data.Equality renaming (implicitFunExt to implicitFunExtPath) public

private variable
  ℓ : Level
  A : Type ℓ
  B : A → Type ℓ

implicitFunExt : {B : A → Type ℓ} {f g : {x : A} → B x} → ({x : A} → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g
implicitFunExt p = pathToEq λ i → eqToPath p i
