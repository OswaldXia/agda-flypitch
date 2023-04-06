{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Data.Nat where

open import Data.Nat public
open import Data.Nat.Properties
open import Data.Empty
open import Data.Unit
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (tri<; tri≈; tri>; _⇒_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infix 4 _≤₃_

_≤₃_ : ℕ → ℕ → Set
x ≤₃ y with <-cmp x y
... | tri< _ _ _ = ⊤
... | tri≈ _ _ _ = ⊤
... | tri> _ _ _ = ⊥

≤₃⇒≤ : _≤₃_ ⇒ _≤_
≤₃⇒≤ {x} {y} x≤₃y with <-cmp x y
... | tri< (s≤s x≤y-1) _ _ = ≤-trans x≤y-1 (n≤1+n _)
... | tri≈ _ refl _ = ≤-refl

≤⇒≤₃ : _≤_ ⇒ _≤₃_
≤⇒≤₃ {x} {y} x≤y with <-cmp x y
... | tri< _ _ _ = tt
... | tri≈ _ _ _ = tt
... | tri> x≮y x≢y _ with m≤n⇒m<n∨m≡n x≤y
... | inj₁ x<y = x≮y x<y
... | inj₂ x≡y = x≢y x≡y
