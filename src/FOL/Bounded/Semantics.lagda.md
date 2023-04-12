---
title: Agda一阶逻辑(?) 语义 (束缚项)
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(?) 语义 (束缚项)

> 交流Q群: 893531731  
> 本文源码: [Semantics.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Bounded/Semantics.lagda.md)  
> 高亮渲染: [Semantics.html](https://choukh.github.io/agda-flypitch/FOL.Bounded.Semantics.html)  

## 前言

```agda
{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Bounded.Semantics (ℒ : Language {u}) where
open import FOL.Bounded.Base ℒ
open import FOL.Structure.Base ℒ
```

### 标准库依赖

```agda
open import Agda.Builtin.Equality
open import Cubical.Core.Primitives hiding (_≡_)
open import Cubical.Foundations.Prelude using (isProp; subst)
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2; isPropΠ3)
open import Cubical.Data.Equality using (PathPathEq)
open import Cubical.Data.Empty using (⊥*; isProp⊥*)
open import CubicalExt.HITs.SetTruncation using (∣_∣₂)
open import CubicalExt.Foundations.Powerset* using (_∈_)

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Function using (_$_)
open import Relation.Nullary using (¬_)
```

## 实现

```agda
module PreRealizer (𝒮 : Structure {v}) where
  open Structure 𝒮
  open Termₗ
  open Formulaₗ
  private variable
    n : ℕ

  realizeₜ : (𝓋 : Vec Domain n) (t : Termₗ n l) (xs : Vec Domain l) → Domain
  realizeₜ 𝓋 (var k)      xs = lookup 𝓋 k
  realizeₜ 𝓋 (func f)     xs = funMap f xs
  realizeₜ 𝓋 (app t₁ t₂)  xs = realizeₜ 𝓋 t₁ ((realizeₜ 𝓋 t₂ []) ∷ xs)

  realize : (𝓋 : Vec Domain n) (φ : Formulaₗ n l) (xs : Vec Domain l) → Type v
  realize 𝓋 ⊥          xs = ⊥*
  realize 𝓋 (rel R)    xs = relMap R xs .fst
  realize 𝓋 (appᵣ φ t) xs = realize 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  realize 𝓋 (t₁ ≈ t₂)  xs = realizeₜ 𝓋 t₁ xs ≡ realizeₜ 𝓋 t₂ xs
  realize 𝓋 (φ₁ ⇒ φ₂)  xs = realize 𝓋 φ₁ xs → realize 𝓋 φ₂ xs
  realize 𝓋 (∀' φ)     xs = ∀ x → realize (x ∷ 𝓋) φ xs

  isPropRealization : (𝓋 : Vec Domain n) (φ : Formulaₗ n l) (xs : Vec Domain l) → isProp (realize 𝓋 φ xs)
  isPropRealization 𝓋 ⊥          xs = isProp⊥*
  isPropRealization 𝓋 (rel R)    xs = relMap R xs .snd
  isPropRealization 𝓋 (appᵣ φ t) xs = isPropRealization 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  isPropRealization 𝓋 (t₁ ≈ t₂)  xs = subst (λ x → isProp x) PathPathEq (isSetDomain (realizeₜ 𝓋 t₁ xs) (realizeₜ 𝓋 t₂ xs))
  isPropRealization 𝓋 (φ₁ ⇒ φ₂)  xs = isPropΠ $ λ _ → isPropRealization 𝓋 φ₂ xs
  isPropRealization 𝓋 (∀' φ)     xs = isPropΠ λ x → isPropRealization (x ∷ 𝓋) φ xs
```

```agda
open Structure
module OpenedRealizer (𝒮 : Structure {v}) {n} (𝓋 : Vec (Domain 𝒮) n) where
  module Pre = PreRealizer 𝒮

  realizeₜ : Term n → Domain 𝒮
  realizeₜ t = Pre.realizeₜ 𝓋 t []

  realize : Formula n → Type v
  realize φ = Pre.realize 𝓋 φ []

  isPropRealization : (φ : Formula n) → isProp (realize φ)
  isPropRealization φ = Pre.isPropRealization 𝓋 φ []
```

```agda
module ClosedRealizer (𝒮 : Structure {v}) where
  open OpenedRealizer 𝒮 [] public
```

## 语义蕴含

```agda
open ClosedRealizer
infix 6 _⊨ˢ_ _⊨ᵀ_ _⊨_

_⊨ˢ_ : Structure {v} → Sentence → Type v
𝒮 ⊨ˢ φ = realize 𝒮 φ

_⊨ᵀ_ : Structure {v} → Theory → Type (ℓ-max u v)
𝒮 ⊨ᵀ Γ = ∀ φ → ∣ φ ∣₂ ∈ Γ → 𝒮 ⊨ˢ φ

_⊨_ : Theory → Sentence → Type (ℓ-suc u)
Γ ⊨ φ = ∀ 𝒮 → Domain 𝒮 → 𝒮 ⊨ᵀ Γ → 𝒮 ⊨ˢ φ
```

```agda
isProp-⊨ˢ : (𝒮 : Structure {v}) (φ : Sentence) → isProp {v} (𝒮 ⊨ˢ φ)
isProp-⊨ˢ 𝒮 φ = isPropRealization 𝒮 φ

isProp-⊨ᵀ : (𝒮 : Structure {v}) (Γ : Theory) → isProp (𝒮 ⊨ᵀ Γ)
isProp-⊨ᵀ 𝒮 _ = isPropΠ2 (λ φ _ → isProp-⊨ˢ 𝒮 φ)

isProp-⊨ : (Γ : Theory) (φ : Sentence) → isProp (Γ ⊨ φ)
isProp-⊨ _ φ = isPropΠ3 (λ 𝒮 _ _ → isProp-⊨ˢ 𝒮 φ)
```

```agda
[_]⊭⊥ : (𝒮 : Structure {v}) → ¬ (𝒮 ⊨ˢ ⊥)
[ _ ]⊭⊥ ()
```
