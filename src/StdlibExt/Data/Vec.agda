{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Data.Vec where

open import Level using (Level)
open import Data.Fin
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Vec public
open import Data.Vec.Properties public
open import Function using (_$_; _∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; refl; sym; trans)

private variable
  a : Level
  n : ℕ
  A B : Set a

[]-refl : (xs : Vec A 0) → [] ≡ xs
[]-refl [] = refl

map-∘-id : ∀ (f : B → A) (g : A → B) → f ∘ g ≗ id → map f ∘ map g ≗ id {A = Vec A n}
map-∘-id f g fg≗id xs = trans (sym $ map-∘ f g xs) (trans (map-cong fg≗id xs) (map-id xs))

lookup∷ʳ-< : (xs : Vec A n) {a : A} (k : Fin (suc n)) (k<n : toℕ k ℕ.< n) →
  lookup (xs ∷ʳ a) k ≡ lookup xs (fromℕ< k<n)
lookup∷ʳ-< (x ∷ xs) zero z<s = refl
lookup∷ʳ-< (x ∷ xs) (suc k) (s<s k<n) = lookup∷ʳ-< xs k k<n

lookup∷ʳ-≡ : (xs : Vec A n) {a : A} (k : Fin (suc n)) (k≡n : toℕ k ≡ n) →
  lookup (xs ∷ʳ a) k ≡ a
lookup∷ʳ-≡ [] zero k≡n = refl
lookup∷ʳ-≡ (x ∷ xs) (suc k) = lookup∷ʳ-≡ xs k ∘ suc-injective
