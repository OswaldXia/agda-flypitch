---
title: Agda综合哥德尔不完备 (2) 邱奇论题
---

# Agda综合哥德尔不完备 (2) 邱奇论题

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Synthetic.Axiom.Base where
open import Synthetic.PartialFunction

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ : Level
  A : Type ℓ
```

## 邱奇论题 (CT)

```agda
module _ (φ : ℕ → ℕ → ℕ → Maybe ℕ) where

  --Kleene’s computation predicate
  halts : ℕ → ℕ → ℕ → Type _
  halts c x n = ∀ m → m ≥ n → φ c x m ≡ φ c x n

  CTᵩ : Type _
  CTᵩ = (f : ℕ → ℕ) → ∃ _ λ c → ∀ x → Σ _ λ n → halts c x n × (φ c x n ≡ just (f x))

CT = Σ _ CTᵩ
```

## 偏函数可枚举公理 (EPF)

```agda
_[_]-reflects_ : ℕ → (ℕ → ℕ → part A) → (ℕ → part A) → Type _
c [ Θ ]-reflects f = ∀ x y → Θ c x ≐ y ↔ f x ≐ y

universal : (ℕ → ℕ → part A) → Type _
universal {A} Θ = (f : ℕ → part A) → ∃ ℕ (_[ Θ ]-reflects f)

EPFᴺ : Type _
EPFᴺ = Σ (ℕ → ℕ → part ℕ) universal

EPFᴮ : Type _
EPFᴮ = Σ (ℕ → ℕ → part Bool) universal
```
