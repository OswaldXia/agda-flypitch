{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Data.Fin where

open import Data.Nat.Base as ℕ using (ℕ; zero; suc; s≤s)
open import Data.Nat.Properties using (+-suc; +-comm; +-identityʳ)
open import Data.Fin.Base public
open import Data.Fin.Properties public
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

private variable
  m n : ℕ

toℕ-reduce≥ : (i : Fin (m ℕ.+ n)) (i≥m : toℕ i ℕ.≥ m) → toℕ (reduce≥ i i≥m) ≡ toℕ i ℕ.∸ m
toℕ-reduce≥ {zero} i i≥m = refl
toℕ-reduce≥ {suc m} (suc i) (s≤s i≥m) = toℕ-reduce≥ i i≥m

toℕ-cast-↑ʳ : (i : Fin m) → toℕ (cast (+-comm n m) (n ↑ʳ i)) ≡ toℕ i ℕ.+ n
toℕ-cast-↑ʳ {_} {zero} i = trans (toℕ-cast (sym $ +-identityʳ _) i) (sym $ +-identityʳ _)
toℕ-cast-↑ʳ {suc m} {suc n} i rewrite +-suc m n = trans (cong suc (toℕ-cast-↑ʳ i)) (sym $ +-suc _ _)
