{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Data.Nat where

open import Data.Nat public
open import Data.Nat.Properties public
open import Data.Empty
open import Data.Unit
open import Data.Sum using (inj₁; inj₂)
open import Function using (_$_)
open import Relation.Binary using (tri<; tri≈; tri>; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

private variable
  n m : ℕ

infix 4 _≤₃_
_≤₃_ : ℕ → ℕ → Set
m ≤₃ n with <-cmp m n
... | tri< _ _ _ = ⊤
... | tri≈ _ _ _ = ⊤
... | tri> _ _ _ = ⊥

≤₃⇒≤ : _≤₃_ ⇒ _≤_
≤₃⇒≤ {m} {n} x≤₃y with <-cmp m n
... | tri< (s≤s x≤y-1) _ _ = ≤-trans x≤y-1 (n≤1+n _)
... | tri≈ _ refl _ = ≤-refl

≤⇒≤₃ : _≤_ ⇒ _≤₃_
≤⇒≤₃ {m} {n} x≤y with <-cmp m n
... | tri< _ _ _ = tt
... | tri≈ _ _ _ = tt
... | tri> x≮y x≢y _ with m≤n⇒m<n∨m≡n x≤y
... | inj₁ m<n = x≮y m<n
... | inj₂ x≡y = x≢y x≡y

s≤₃s : ∀ {m n} → m ≤₃ n → suc m ≤₃ suc n
s≤₃s x≤₃y = ≤⇒≤₃ (s≤s (≤₃⇒≤ x≤₃y))

≤₃-refl : ∀ {n} → n ≤₃ n
≤₃-refl = ≤⇒≤₃ ≤-refl

m≤₃m+n : ∀ {m n} → m ≤₃ m + n
m≤₃m+n = ≤⇒≤₃ (m≤m+n _ _)

m≤₃n+m : ∀ {m n} → m ≤₃ n + m
m≤₃n+m = ≤⇒≤₃ (m≤n+m _ _)

n<n+1 : ∀ {n} → n < n + 1
n<n+1 {n} = m<m+n n (s≤s z≤n)

n≡1+n∸1 : m < n → n ≡ suc (n ∸ 1)
n≡1+n∸1 m<n = sym $ trans (+-comm 1 _) (m∸n+n≡m $ ≤-trans (s≤s z≤n) m<n)

m+n≤n+m : (m n : ℕ) → m + n ≤ n + m
m+n≤n+m m n = subst (_≤ n + m) (+-comm n _) ≤-refl
