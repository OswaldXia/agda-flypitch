{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Relation.Binary.PropositionalEquality where

open import Relation.Binary.PropositionalEquality public

funExt⁻ : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} {x : A} → f ≡ g → f x ≡ g x
funExt⁻ refl = refl
