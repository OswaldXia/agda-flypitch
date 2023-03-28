{-# OPTIONS --cubical --safe #-}

module CubicalExt.StdlibBridge.Vec where

open import Data.Nat using (ℕ)
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude using (refl; cong)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
open import Cubical.Foundations.Univalence using (ua)

open import Data.Vec as Stdlib
open import CubicalExt.Data.Vec as Cubical

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

Cubical≃Stdlib : (n : ℕ) → Cubical.Vec A n ≃ Stdlib.Vec A n
Cubical≃Stdlib n = isoToEquiv (CubicalIsoStdlib n)

vecBridge : (n : ℕ) → Cubical.Vec A n ≡ Stdlib.Vec A n
vecBridge n = ua (Cubical≃Stdlib n)
