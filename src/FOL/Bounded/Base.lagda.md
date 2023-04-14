---
title: Agda一阶逻辑(?) 束缚
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(?) 束缚

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Bounded/Base.lagda.md)  
> 高亮渲染: [Base.html](https://choukh.github.io/agda-flypitch/FOL.Bounded.Base.html)  

## 前言

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Bounded.Base ⦃ em : EM ⦄ (ℒ : Language {u}) where
import FOL.Base ⦃ em ⦄ ℒ as Free
open Language ℒ
open Free using (l) public
open Free.Termₗ
open Free.Formulaₗ
```

### 标准库依赖

```agda
open import Agda.Builtin.Equality
open import Cubical.Core.Primitives using (Type)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_$_)
open import Relation.Nullary using (¬_)
```

### 符号优先级

```agda
infix 100 ~_
infix 9 _≈_
infix 8 _⇔_
infix 7 _⇒_
infixr 6 _∧_
infixr 5 _∨_
```

## 束缚项

```agda
data Termₗ (n : ℕ) : ℕ → Type u where
  var  : (k : Fin n) → Termₗ n 0
  func : (f : 𝔉 l) → Termₗ n l
  app  : (t₁ : Termₗ n (suc l)) (t₂ : Termₗ n 0) → Termₗ n l

Term : ℕ → Type u
Term n = Termₗ n 0
```

### 常量

```agda
private variable
  n : ℕ

const : Constant → Term n
const = func
```

### 多元函数应用

```agda
apps : (t : Termₗ n l) (ts : Vec (Term n) l) → Term n
apps t [] = t
apps f (t ∷ ts) = apps (app f t) ts
```

### 闭项

```agda
ClosedTermₗ : ℕ → Type u
ClosedTermₗ l = Termₗ 0 l

ClosedTerm : Type u
ClosedTerm = ClosedTermₗ 0
```

## 束缚公式

```agda
data Formulaₗ (n : ℕ) : ℕ → Type u where
  ⊥     : Formulaₗ n 0
  rel   : (R : ℜ l) → Formulaₗ n l
  appᵣ  : (φ : Formulaₗ n (suc l)) (t : Term n) → Formulaₗ n l
  _≈_   : (t₁ t₂ : Term n) → Formulaₗ n 0
  _⇒_   : (φ₁ φ₂ : Formulaₗ n 0) → Formulaₗ n 0
  ∀'_   : (φ : Formulaₗ (suc n) 0) → Formulaₗ n 0

Formula : ℕ → Type u
Formula n = Formulaₗ n 0
```

### 多元关系应用

```agda
appsᵣ : (φ : Formulaₗ n l) (ts : Vec (Term n) l) → Formula n
appsᵣ φ [] = φ
appsᵣ φ (t ∷ ts) = appsᵣ (appᵣ φ t) ts
```

### 句子 (闭公式)

```agda
Sentenceₗ : ℕ → Type u
Sentenceₗ l = Formulaₗ 0 l

Sentence : Type u
Sentence = Sentenceₗ 0
```

### 导出符号

```agda
~_ : Formula n → Formula n
~ φ = φ ⇒ ⊥

⊤ : Formula n
⊤ = ~ ⊥

_∧_ : Formula n → Formula n → Formula n
φ₁ ∧ φ₂ = ~ (φ₁ ⇒ ~ φ₂)

_∨_ : Formula n → Formula n → Formula n
φ₁ ∨ φ₂ = ~ φ₁ ⇒ φ₂

_⇔_ : Formula n → Formula n → Formula n
φ₁ ⇔ φ₂ = φ₁ ⇒ φ₂ ∧ φ₂ ⇒ φ₁

∃'_ : Formula (suc n) → Formula n
∃' φ = ~ (∀' ~ φ)
```

## 解束缚

```agda
unboundₜ : Termₗ n l → Free.Termₗ l
unboundₜ (var k)     = var $ toℕ k
unboundₜ (func f)    = func f
unboundₜ (app t₁ t₂) = app (unboundₜ t₁) (unboundₜ t₂)
```

```agda
unbound : Formulaₗ n l → Free.Formulaₗ l
unbound ⊥           = ⊥
unbound (rel R)     = rel R
unbound (appᵣ φ t)  = appᵣ (unbound φ) (unboundₜ t)
unbound (t₁ ≈ t₂)   = unboundₜ t₁ ≈ unboundₜ t₂
unbound (φ₁ ⇒ φ₂)   = unbound φ₁ ⇒ unbound φ₂
unbound (∀' φ)      = ∀' (unbound φ)
```
