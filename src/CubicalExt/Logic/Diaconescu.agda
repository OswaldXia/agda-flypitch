{-# OPTIONS --cubical --safe #-}

open import CubicalExt.Axiom.Choice
open import Cubical.Foundations.HLevels
module CubicalExt.Logic.Diaconescu (ac : ∀ {ℓ ℓ'} → AC ℓ ℓ') {ℓ} (P : hProp ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.HITs.SetQuotients
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary
open import CubicalExt.Axiom.ExcludedMiddle

_~_ : Rel Bool Bool ℓ
true ~ false = fst P
false ~ true = fst P
_ ~ _ = ¬ fst P

Nice = Bool
Naughty = Bool / _~_

∀ x → ∃[ y ∈ Naughty ] [ x ] ≡ y
(∀ x → ∃[ y ∈ B ] P x y) → ∃[ f ∈ (A → B) ] ∀ x → P x (f x)

∃[ f ∈ (Nice → Naughty) ] ∀ x → f x ≡ x
