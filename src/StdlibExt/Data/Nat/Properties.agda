{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Data.Nat.Properties where

open import StdlibExt.Data.Nat
open import Data.Nat.Properties public
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; sym; trans)
open ≤-Reasoning

private variable
  n m : ℕ

n<n+1 : ∀ {n} → n < n + 1
n<n+1 {n} = m<m+n n (s≤s z≤n)

n≡1+n∸1 : m < n → n ≡ suc (n ∸ 1)
n≡1+n∸1 m<n = sym $ trans (+-comm 1 _) (m∸n+n≡m $ ≤-trans (s≤s z≤n) m<n)

≤₃-refl : ∀ {n} → n ≤₃ n
≤₃-refl = ≤⇒≤₃ ≤-refl

m≤₃m+n : ∀ {m n} → m ≤₃ m + n
m≤₃m+n = ≤⇒≤₃ (m≤m+n _ _)

m≤₃n+m : ∀ {m n} → m ≤₃ n + m
m≤₃n+m = ≤⇒≤₃ (m≤n+m _ _)
