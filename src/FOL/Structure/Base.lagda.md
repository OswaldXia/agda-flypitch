---
title: Agda一阶逻辑(?) 结构
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(?) 结构

> 交流Q群: 893531731  
> 本文源码: [Structure.Base.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Structure/Base.lagda.md)  
> 高亮渲染: [Structure.Base.html](https://choukh.github.io/agda-flypitch/FOL.Structure.Base.html)  

```agda
{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Structure.Base (ℒ : Language {u}) where
open Language ℒ

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Data.Vec using (Vec; []; _∷_)
```

函数符号和关系符号的一套实际所指就构成了一阶逻辑的一种解释, 从解释所得到的实际产物的角度来看又叫做结构. 它由一个集合 `Domain` 以及两个映射 `funMap` 和 `relMap` 组成. 其中 `funMap` 用于映射函数符号到函数, `relMap` 用于映射关系符号到 (hProp) 关系. 注意函数和关系的n元参数编码为n维向量.

```agda
variable
  v : Level

record Structure : Type (ℓ-max u (ℓ-suc v)) where
  field
    Domain : Type v
    isSetDomain : isSet Domain
    funMap : ∀ {n} → 𝔉 n → Vec Domain n → Domain
    relMap : ∀ {n} → ℜ n → Vec Domain n → hProp v
```
