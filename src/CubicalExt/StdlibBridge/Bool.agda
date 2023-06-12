{-# OPTIONS --cubical --safe #-}

module CubicalExt.StdlibBridge.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToPath)

open import Data.Bool as Stdlib
open import Cubical.Data.Bool as Cubical

Cubical→Stdlib : Cubical.Bool → Stdlib.Bool
Cubical→Stdlib true = true
Cubical→Stdlib false = false

Stblib→Cubical : Stdlib.Bool → Cubical.Bool
Stblib→Cubical true = true
Stblib→Cubical false = false

Cubical→Stdlib→Cubical : ∀ b → Cubical→Stdlib (Stblib→Cubical b) ≡ b
Cubical→Stdlib→Cubical true = refl
Cubical→Stdlib→Cubical false = refl

Stblib→Cubical→Stblib : ∀ b → Stblib→Cubical (Cubical→Stdlib b) ≡ b
Stblib→Cubical→Stblib true = refl
Stblib→Cubical→Stblib false = refl

CubicalIsoStdlib : Iso Cubical.Bool Stdlib.Bool
CubicalIsoStdlib = iso Cubical→Stdlib Stblib→Cubical Cubical→Stdlib→Cubical Stblib→Cubical→Stblib

boolBridge : Cubical.Bool ≡ Stdlib.Bool
boolBridge = isoToPath CubicalIsoStdlib
