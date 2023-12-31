---
title: Agda一阶逻辑(1) 语言
zhihu-tags: Agda, 数理逻辑
zhihu-url: https://zhuanlan.zhihu.com/p/604316553
---

# Agda一阶逻辑(1) 语言

> 交流Q群: 893531731  
> 本文源码: [Language.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Language.lagda.md)  
> 高亮渲染: [Language.html](https://choukh.github.io/agda-flypitch/FOL.Language.html)  

本系列文章采用立方类型论 (cubical type theory, 简称 CuTT) 作为元语言, 讨论一阶逻辑及其性质.

```agda
{-# OPTIONS --cubical --safe #-}
```

一阶逻辑是一种形式语言, 其语句由一些原始符号按一定的语法组合而成. 符号又分为逻辑符号和非逻辑符号. 本篇先讲非逻辑符号.

非逻辑符号分为函数符号和关系符号, 且它们都带有一个称为元数 (arity) 的属性. 例如, 元数为 2 的函数符号即用于表示二元函数. 特别地, 元数为零的函数又称为常量.

较传统的处理方式是给出所有可能的函数符号和关系符号. 即对任意元数 $n$, 都有自然数多个函数符号

$$f^n_0,\ f^n_1,\ f^n_2,\ f^n_3,\ ...$$

以及自然数多个关系符号

$$R^n_0,\ R^n_1,\ R^n_2,\ R^n_3,\ ...$$

在这种处理下, 只有唯一一种一阶逻辑语言.

较现代的方式是根据最终要实现的一阶理论来指定该理论所需的非逻辑符号. 这些特定的符号以及它们的元数所组成的资料叫做理论的**签名 (signature)**. 在这种处理下, 每种签名都对应一种一阶逻辑语言, 因此签名又叫做**语言 (language)**, 语言的实例按惯例记作 ℒ. 由于一阶逻辑的其他部分都是参数化到语言的, 我们把它单独作为一个模块.

```agda
module FOL.Language where

open import Cubical.Foundations.Prelude using (Type; Level; ℓ-suc; isSet)
open import Cubical.Data.Nat using (ℕ)
open import CubicalExt.Relation.Nullary using (DiscreteEq; DiscreteEq→isSet)
```

**定义 (语言)** 由按元数分类的函数符号集族 `𝔉 : ℕ → Type u` 以及按元数分类的关系符号集族 `ℜ : ℕ → Type u` 组成的资料叫做一阶逻辑的语言. 特别地, 常量集是元数为 0 的函数集. 我们约定 `u` 是语言专用的宇宙多态参数, 语言比符号集高一个宇宙.

```agda
variable
  u : Level

record Language : Type (ℓ-suc u) where
  field
    𝔉 : ℕ → Type u
    ℜ : ℕ → Type u
    discrete𝔉 : ∀ {n} → DiscreteEq (𝔉 n)
    discreteℜ : ∀ {n} → DiscreteEq (ℜ n)
  Constant = 𝔉 0
```

在经典语境下集合一定是离散的, 但在直觉主义 CuTT 中, 离散是强于"是集合"的. 尽管我们最终将假设排中律, 但我们希望尽可能推迟它的引入, 因此以上定义中我们直接要求符号集是离散的. 下面补上"是集合"的证明.

```agda
  isSet𝔉 : ∀ {n} → isSet (𝔉 n)
  isSet𝔉 = DiscreteEq→isSet discrete𝔉

  isSetℜ : ∀ {n} → isSet (ℜ n)
  isSetℜ = DiscreteEq→isSet discreteℜ
```

**例** 下面给出了语言的一个实例 `ℒ`, 它可以作为皮亚诺算术 (一种一阶理论) 的语言. 注意符号的元数被编码到了类型里面. 例如, 常量 `O` 的类型是 `func 0`, 后继函数 `S` 的类型是 `func 1`, 加法 `+` 以及乘法 `*` 的类型是 `func 2`, 小于关系 `<` 的类型是 `rel 2`.

```agda
private module ExampleLanguagePA where
  open import Agda.Builtin.Equality using (refl)
  open import CubicalExt.Relation.Nullary using (yes; no)

  data func : ℕ → Type where
    O : func 0
    S : func 1
    + : func 2
    * : func 2

  data rel : ℕ → Type where
    < : rel 2
```

通过模式匹配不难证明归纳定义的 `func` 和 `rel` 是离散的.

```agda
  discreteFunc : ∀ {n} → DiscreteEq (func n)
  discreteFunc {0} O O = yes refl
  discreteFunc {1} S S = yes refl
  discreteFunc {2} + + = yes refl
  discreteFunc {2} * * = yes refl
  discreteFunc {2} + * = no λ ()
  discreteFunc {2} * + = no λ ()

  discreteRel : ∀ {n} → DiscreteEq (rel n)
  discreteRel {2} < < = yes refl
```

于是它们可以构成语言.

```agda
  ℒ : Language
  ℒ = record
    { 𝔉 = func
    ; ℜ = rel
    ; discrete𝔉 = discreteFunc
    ; discreteℜ = discreteRel
    }
```

今后我们约定 `ℒ` 作为语言的实例的记号.

```
variable
  ℒ : Language
```
