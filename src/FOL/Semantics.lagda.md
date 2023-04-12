---
title: Agda一阶逻辑(?) 语义
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(?) 语义

> 交流Q群: 893531731  
> 本文源码: [Semantics.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Semantics.lagda.md)  
> 高亮渲染: [Semantics.html](https://choukh.github.io/agda-flypitch/FOL.Semantics.html)  

## 前言

```agda
{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Semantics (ℒ : Language {u}) where
open import FOL.Base ℒ hiding (subst)
open import FOL.Structure.Base ℒ
open Language ℒ
```

### 标准库依赖

```agda
open import Agda.Builtin.Equality
open import Cubical.Core.Primitives hiding (_≡_)
open import Cubical.Foundations.Prelude using (isProp; isSet; subst)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ; isPropΠ2; isPropΠ3)
open import Cubical.Data.Equality using (PathPathEq)
open import Cubical.Data.Empty using (⊥*; isProp⊥*)
open import CubicalExt.HITs.SetTruncation using (∣_∣₂)
open import CubicalExt.Foundations.Powerset* using (_∈_)

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_$_)
```

## 实现

```agda
module PreRealizer (𝒮 : Structure {v}) where
  open Structure 𝒮
  open Termₗ
  open Formulaₗ

  realizeₜ : (𝓋 : ℕ → Domain) (t : Termₗ l) (xs : Vec Domain l) → Domain
  realizeₜ 𝓋 (var k)     xs = 𝓋 k
  realizeₜ 𝓋 (func f)    xs = funMap f xs
  realizeₜ 𝓋 (app t₁ t₂) xs = realizeₜ 𝓋 t₁ ((realizeₜ 𝓋 t₂ []) ∷ xs)

  realize : (𝓋 : ℕ → Domain) (φ : Formulaₗ l) (xs : Vec Domain l) → Type v
  realize 𝓋 ⊥          xs = ⊥*
  realize 𝓋 (rel R)    xs = relMap R xs .fst
  realize 𝓋 (appᵣ φ t) xs = realize 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  realize 𝓋 (t₁ ≈ t₂)  xs = realizeₜ 𝓋 t₁ xs ≡ realizeₜ 𝓋 t₂ xs
  realize 𝓋 (φ₁ ⇒ φ₂)  xs = realize 𝓋 φ₁ xs → realize 𝓋 φ₂ xs
  realize 𝓋 (∀' φ)     xs = ∀ x → realize (𝓋 [ x / 0 ]ᵥ) φ xs

  isPropRealization : (𝓋 : ℕ → Domain) (φ : Formulaₗ l) (xs : Vec Domain l) → isProp (realize 𝓋 φ xs)
  isPropRealization 𝓋 ⊥           xs = isProp⊥*
  isPropRealization 𝓋 (rel R)     xs = relMap R xs .snd
  isPropRealization 𝓋 (appᵣ φ t)  xs = isPropRealization 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  isPropRealization 𝓋 (t₁ ≈ t₂)   xs = subst (λ x → isProp x) PathPathEq (isSetDomain (realizeₜ 𝓋 t₁ xs) (realizeₜ 𝓋 t₂ xs))
  isPropRealization 𝓋 (φ₁ ⇒ φ₂)   xs = isPropΠ $ λ _ → isPropRealization 𝓋 φ₂ xs
  isPropRealization 𝓋 (∀' φ)      xs = isPropΠ $ λ x → isPropRealization (𝓋 [ x / 0 ]ᵥ) φ xs
```

```agda
open Structure
module Realizer (𝒮 : Structure {v}) (𝓋 : ℕ → Domain 𝒮) where
  module Pre = PreRealizer 𝒮

  realizeₜ : Term → Domain 𝒮
  realizeₜ t = Pre.realizeₜ 𝓋 t []

  realize : Formula → Type v
  realize φ = Pre.realize 𝓋 φ []

  isPropRealization : ∀ φ → isProp (realize φ)
  isPropRealization φ = Pre.isPropRealization 𝓋 φ []
```

## 语义蕴含

```agda
open Realizer
infix 4 _⊨[_]_ _⊨_

_⊨[_]_ : (𝒮 : Structure {v}) (𝓋 : ℕ → Domain 𝒮) → Theory → Type (ℓ-max u v)
𝒮 ⊨[ 𝓋 ] Γ = ∀ φ → ∣ φ ∣₂ ∈ Γ → realize 𝒮 𝓋 φ

_⊨_ : Theory → Formula → Type (ℓ-suc u)
Γ ⊨ φ = ∀ 𝒮 𝓋 → 𝒮 ⊨[ 𝓋 ] Γ → realize 𝒮 𝓋 φ
```

```agda
isProp-⊨[] : (𝒮 : Structure {v}) (𝓋 : ℕ → Domain 𝒮) (Γ : Theory) → isProp (𝒮 ⊨[ 𝓋 ] Γ)
isProp-⊨[] 𝒮 𝓋 _ = isPropΠ2 λ φ _ → isPropRealization 𝒮 𝓋 φ

isProp-⊨ : (Γ : Theory) (φ : Formula) → isProp (Γ ⊨ φ)
isProp-⊨ Γ φ = isPropΠ3 λ 𝒮 𝓋 _ → isPropRealization 𝒮 𝓋 φ
```
