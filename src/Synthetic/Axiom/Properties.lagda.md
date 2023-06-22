---
title: Agda综合哥德尔不完备 (3) CT ↔ EPF
---

# Agda综合哥德尔不完备 (3) CT ↔ EPF

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Synthetic.Axiom.Properties where
open import Synthetic.Axiom.Base
open import Synthetic.PartialFunction

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Logic using (∥_∥ₚ)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff
```

```agda
CT→EPFᴺ : CT → EPFᴺ
CT→EPFᴺ (φ , ct) = θ , H where
  P : ℕ → ℕ → Type
  P c x = Σ _ λ n → Σ _ λ y → halts φ c x n × (φ c x n ≡ just y)
  θ : ℕ → ℕ → Part ℕ
  θ c x = ∥ P c x ∥ₚ , rec→Set isSetℕ (fst ∘ snd)
    λ { (n₁ , y₁ , H₁ , eq₁) (n₂ , y₂ , H₂ , eq₂) → {!   !} }
  H : universal θ
  H f = {!   !}
```
