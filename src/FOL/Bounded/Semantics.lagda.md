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
open import Cubical.Foundations.HLevels using (hProp; isSetHProp; isPropΠ; isPropΠ2; isPropΠ3)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Equality using (PathPathEq)
open import Cubical.Data.Empty using (⊥*; isProp⊥*)
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; elim)
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

  realizeType : (𝓋 : Vec Domain n) (φ : Formulaₗ n l) (xs : Vec Domain l) → Type v
  realizeType 𝓋 ⊥          xs = ⊥*
  realizeType 𝓋 (rel R)    xs = relMap R xs .fst
  realizeType 𝓋 (appᵣ φ t) xs = realizeType 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  realizeType 𝓋 (t₁ ≈ t₂)  xs = realizeₜ 𝓋 t₁ xs ≡ realizeₜ 𝓋 t₂ xs
  realizeType 𝓋 (φ₁ ⇒ φ₂)  xs = realizeType 𝓋 φ₁ xs → realizeType 𝓋 φ₂ xs
  realizeType 𝓋 (∀' φ)     xs = ∀ x → realizeType (x ∷ 𝓋) φ xs

  isPropRealize : (𝓋 : Vec Domain n) (φ : Formulaₗ n l) (xs : Vec Domain l) → isProp (realizeType 𝓋 φ xs)
  isPropRealize 𝓋 ⊥          xs = isProp⊥*
  isPropRealize 𝓋 (rel R)    xs = relMap R xs .snd
  isPropRealize 𝓋 (appᵣ φ t) xs = isPropRealize 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  isPropRealize 𝓋 (t₁ ≈ t₂)  xs = subst (λ x → isProp x) PathPathEq (isSetDomain (realizeₜ 𝓋 t₁ xs) (realizeₜ 𝓋 t₂ xs))
  isPropRealize 𝓋 (φ₁ ⇒ φ₂)  xs = isPropΠ $ λ _ → isPropRealize 𝓋 φ₂ xs
  isPropRealize 𝓋 (∀' φ)     xs = isPropΠ λ x → isPropRealize (x ∷ 𝓋) φ xs

  realize : (𝓋 : Vec Domain n) (φ : ∥ Formulaₗ n l ∥₂) (xs : Vec Domain l) → hProp v
  realize 𝓋 φ xs = elim (λ _ → isSetHProp) (λ φ → realizeType 𝓋 φ xs , isPropRealize 𝓋 φ xs) φ
```

```agda
open Structure
module OpenedRealizer (𝒮 : Structure {v}) {n} (𝓋 : Vec (Domain 𝒮) n) where
  module Pre = PreRealizer 𝒮

  realizeₜ : Term n → Domain 𝒮
  realizeₜ t = Pre.realizeₜ 𝓋 t []

  realize : ∥ Formula n ∥₂ → hProp v
  realize φ = Pre.realize 𝓋 φ []
```

```agda
module ClosedRealizer (𝒮 : Structure {v}) where
  open OpenedRealizer 𝒮 [] public
```

## 语义蕴含

```agda
open ClosedRealizer
infix 6 _⊨ˢ_ --_⊨ᵀ_ _⊨_

_⊨ˢ_ : Structure {v} → ∥ Sentence ∥₂ → hProp v
𝒮 ⊨ˢ φ = realize 𝒮 φ

_⊨ᵀ_ : Structure {v} → Theory → hProp (ℓ-max u v)
𝒮 ⊨ᵀ Γ = (∀ φ → φ ∈ Γ → ⟨ 𝒮 ⊨ˢ φ ⟩) , (isPropΠ2 $ λ φ _ → (𝒮 ⊨ˢ φ) .snd)

_⊨_ : Theory → ∥ Sentence ∥₂ → hProp (ℓ-suc u)
Γ ⊨ φ = (∀ 𝒮 → Domain 𝒮 → ⟨ 𝒮 ⊨ᵀ Γ ⟩ → ⟨ 𝒮 ⊨ˢ φ ⟩) , (isPropΠ3 $ λ 𝒮 _ _ → (𝒮 ⊨ˢ φ) .snd)
```
