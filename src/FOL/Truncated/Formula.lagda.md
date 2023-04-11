---
title: Agda一阶逻辑(3) 公式集
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(3) 公式集

> 交流Q群: 893531731  
> 本文源码: [Formula.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Truncated/Formula.lagda.md)  
> 高亮渲染: [Formula.html](https://choukh.github.io/agda-flypitch/FOL.Truncated.Formula.html)  

```agda
{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Truncated.Formula (ℒ : Language {u}) where
import FOL.Base ℒ as Untruncated
open Untruncated using (l; Term)
open Language ℒ

open import Cubical.Core.Primitives using (Type; ℓ-suc)
open import Cubical.Foundations.Prelude using (isSet)
open import CubicalExt.Foundations.Powerset* as 𝒫 using (𝒫; isSet𝒫; _∈_; _⟦_⟧)
open import CubicalExt.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; squash₂; map; map2)

open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_)
```

```agda
infix 100 ~_
infix 9 _≈_
infix 8 _⇔_
infix 7 _⇒_
infixr 6 _∧_
infixr 5 _∨_
```

## 公式集

公式集是 `Formula` 的 2-截断.

```agda
Formulaₗ : ℕ → Type u
Formulaₗ l = ∥ Untruncated.Formulaₗ l ∥₂

Formula = Formulaₗ 0
```

公式构造子的截断版本:

```agda
⊥ : Formula
⊥ = ∣ Untruncated.⊥ ∣₂

rel : relations l → Formulaₗ l
rel R = ∣ Untruncated.rel R ∣₂

appᵣ : Formulaₗ (suc l) → Term → Formulaₗ l
appᵣ φ t = map (λ φ → Untruncated.appᵣ φ t) φ

appsᵣ : (φ : Formulaₗ l) (ts : Vec Term l) → Formula
appsᵣ φ ts = map (λ φ → Untruncated.appsᵣ φ ts) φ

_≈_ : Term → Term → Formula
t₁ ≈ t₂ = ∣ t₁ Untruncated.≈ t₂ ∣₂

_⇒_ : Formula → Formula → Formula
φ₁ ⇒ φ₂ = map2 Untruncated._⇒_ φ₁ φ₂

∀'_ : Formula → Formula
∀' φ = map Untruncated.∀'_ φ
```

其他导出符号的截断版本:

```agda
~_ : Formula → Formula
~ φ = φ ⇒ ⊥

⊤ : Formula
⊤ = ~ ⊥
```

```agda
_∧_ : Formula → Formula → Formula
φ₁ ∧ φ₂ = ~ (φ₁ ⇒ ~ φ₂)

_∨_ : Formula → Formula → Formula
φ₁ ∨ φ₂ = ~ φ₁ ⇒ φ₂

_⇔_ : Formula → Formula → Formula
φ₁ ⇔ φ₂ = φ₁ ⇒ φ₂ ∧ φ₂ ⇒ φ₁

∃'_ : Formula → Formula
∃' φ = ~ (∀' ~ φ)
```

变量提升与替换的截断版本:

```agda
_↥[_]_ : (φ : Formulaₗ l) (m n : ℕ) → Formulaₗ l
φ ↥[ m ] n = map (Untruncated._↥[ m ] n) φ

_↥_ : (φ : Formulaₗ l) (n : ℕ) → Formulaₗ l
φ ↥ n = φ ↥[ 0 ] n

_[_/_] : (φ : Formulaₗ l) (s : Term) (n : ℕ) → Formulaₗ l
φ [ s / n ] = map (Untruncated._[ s / n ]) φ
```

## 理论

公式集的子集叫做**理论 (theory)**. 如有违和感, 那么可能是因为这种定义是对朴素意义的理论的一种过度一般化, 这时只需认为理论就是"公式集的子集"的别名即可.

```agda
Theory : Type (ℓ-suc u)
Theory = 𝒫 Formula u

isSetTheory : isSet Theory
isSetTheory = isSet𝒫

open 𝒫.SetBased {X = Formula} squash₂ renaming (_⨭_ to _,_)
```

理论 `Γ` 在函数 `_↥ n` 之下的像叫做理论 `Γ` 的 `n` 提升, 记作 `Γ ⇑ n`.

```agda
_⇑_ : Theory → ℕ → Theory
Γ ⇑ n = (_↥ n) ⟦ Γ ⟧
```
