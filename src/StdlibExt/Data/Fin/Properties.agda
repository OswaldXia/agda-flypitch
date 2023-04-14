{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Data.Fin.Properties where

open import Data.Nat.Base as ℕ using (ℕ; zero; suc; s≤s)
open import Data.Fin.Base
open import Data.Fin.Properties public
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
  m n : ℕ

toℕ-reduce≥ : (i : Fin (m ℕ.+ n)) (i≥m : toℕ i ℕ.≥ m) → toℕ (reduce≥ i i≥m) ≡ toℕ i ℕ.∸ m
toℕ-reduce≥ {zero} i i≥m = refl
toℕ-reduce≥ {suc m} (suc i) (s≤s i≥m) = toℕ-reduce≥ i i≥m
