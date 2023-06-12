{-# OPTIONS --cubical --safe #-}

module CubicalExt.StdlibBridge.Vec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToPath)
open import Cubical.Data.Nat using (ℕ)

open import Data.Vec as Stdlib
open import Cubical.Data.Vec as Cubical

private variable
  ℓ : Level
  A : Type ℓ

Cubical→Stdlib : {n : ℕ} → Cubical.Vec A n → Stdlib.Vec A n
Cubical→Stdlib [] = []
Cubical→Stdlib (x ∷ xs) = x ∷ Cubical→Stdlib xs

Stblib→Cubical : {n : ℕ} → Stdlib.Vec A n → Cubical.Vec A n
Stblib→Cubical [] = []
Stblib→Cubical (x ∷ xs) = x ∷ Stblib→Cubical xs

Cubical→Stdlib→Cubical : {n : ℕ} → (xs : Cubical.Vec A n) → Stblib→Cubical (Cubical→Stdlib xs) ≡ xs
Cubical→Stdlib→Cubical [] = refl
Cubical→Stdlib→Cubical (x ∷ xs) = cong (x ∷_) (Cubical→Stdlib→Cubical xs)

Stdlib→Cubical→Stdlib : {n : ℕ} → (xs : Stdlib.Vec A n) → Cubical→Stdlib (Stblib→Cubical xs) ≡ xs
Stdlib→Cubical→Stdlib [] = refl
Stdlib→Cubical→Stdlib (x ∷ xs) = cong (x ∷_) (Stdlib→Cubical→Stdlib xs)

CubicalIsoStdlib : (n : ℕ) → Iso (Cubical.Vec A n) (Stdlib.Vec A n)
CubicalIsoStdlib n = iso Cubical→Stdlib Stblib→Cubical Stdlib→Cubical→Stdlib Cubical→Stdlib→Cubical

vecBridge : (n : ℕ) → Cubical.Vec A n ≡ Stdlib.Vec A n
vecBridge n = isoToPath (CubicalIsoStdlib n)
