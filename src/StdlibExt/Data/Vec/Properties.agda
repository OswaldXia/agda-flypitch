{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Data.Vec.Properties where

open import Level
open import Data.Nat
open import Data.Vec
open import Data.Vec.Properties public
open import Function using (_$_; _∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; sym; trans)

private variable
  a : Level
  n : ℕ
  A B : Set a

map-∘-id : ∀ (f : B → A) (g : A → B) → f ∘ g ≗ id → map f ∘ map g ≗ id {A = Vec A n}
map-∘-id f g fg≗id xs = trans (sym $ map-∘ f g xs) (trans (map-cong fg≗id xs) (map-id xs))
