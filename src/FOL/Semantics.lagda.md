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
open import Cubical.Foundations.HLevels using (hProp; isSetHProp; isPropΠ; isPropΠ2; isPropΠ3)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Equality using (PathPathEq)
open import Cubical.Data.Empty using (⊥*; isProp⊥*)
open import CubicalExt.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; elim)
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

  realizeType : (𝓋 : ℕ → Domain) (φ : Formulaₗ l) (xs : Vec Domain l) → Type v
  realizeType 𝓋 ⊥          xs = ⊥*
  realizeType 𝓋 (rel R)    xs = relMap R xs .fst
  realizeType 𝓋 (appᵣ φ t) xs = realizeType 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  realizeType 𝓋 (t₁ ≈ t₂)  xs = realizeₜ 𝓋 t₁ xs ≡ realizeₜ 𝓋 t₂ xs
  realizeType 𝓋 (φ₁ ⇒ φ₂)  xs = realizeType 𝓋 φ₁ xs → realizeType 𝓋 φ₂ xs
  realizeType 𝓋 (∀' φ)     xs = ∀ x → realizeType (𝓋 [ x / 0 ]ᵥ) φ xs

  isPropRealize : (𝓋 : ℕ → Domain) (φ : Formulaₗ l) (xs : Vec Domain l) → isProp (realizeType 𝓋 φ xs)
  isPropRealize 𝓋 ⊥           xs = isProp⊥*
  isPropRealize 𝓋 (rel R)     xs = relMap R xs .snd
  isPropRealize 𝓋 (appᵣ φ t)  xs = isPropRealize 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  isPropRealize 𝓋 (t₁ ≈ t₂)   xs = subst (λ x → isProp x) PathPathEq (isSetDomain (realizeₜ 𝓋 t₁ xs) (realizeₜ 𝓋 t₂ xs))
  isPropRealize 𝓋 (φ₁ ⇒ φ₂)   xs = isPropΠ $ λ _ → isPropRealize 𝓋 φ₂ xs
  isPropRealize 𝓋 (∀' φ)      xs = isPropΠ $ λ x → isPropRealize (𝓋 [ x / 0 ]ᵥ) φ xs

  realize : (𝓋 : ℕ → Domain) (φ : Formulaₗ l) (xs : Vec Domain l) → hProp v
  realize 𝓋 φ xs = realizeType 𝓋 φ xs , isPropRealize 𝓋 φ xs
```

```agda
open Structure
module Realizer (𝒮 : Structure {v}) (𝓋 : ℕ → Domain 𝒮) where
  module Pre = PreRealizer 𝒮

  realizeₜ : Term → Domain 𝒮
  realizeₜ t = Pre.realizeₜ 𝓋 t []

  realize : Formula → hProp v
  realize φ = Pre.realize 𝓋 φ []
```

## 语义蕴含

```agda
open Realizer
infix 4 _⊨[_]_ _⊨_

_⊨[_]_ : (𝒮 : Structure {v}) (𝓋 : ℕ → Domain 𝒮) → Theory → hProp (ℓ-max u v)
𝒮 ⊨[ 𝓋 ] Γ = (∀ φ → φ ∈ Γ → ⟨ realize 𝒮 𝓋 φ ⟩)
  , isPropΠ2 λ φ _ → realize 𝒮 𝓋 φ .snd

_⊨_ : Theory → ∥ Formula ∥₂ → hProp (ℓ-suc u)
Γ ⊨ φ = (∀ 𝒮 𝓋 → ⟨ 𝒮 ⊨[ 𝓋 ] Γ ⟩ → ⟨ realize 𝒮 𝓋 φ ⟩)
  , isPropΠ3 λ 𝒮 𝓋 _ → realize 𝒮 𝓋 φ .snd
```
