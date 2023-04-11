---
title: Agda一阶逻辑(2) 项与公式
zhihu-tags: Agda, 数理逻辑
zhihu-url: https://zhuanlan.zhihu.com/p/604316612
---

# Agda一阶逻辑(2) 项与公式

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Base.lagda.md)  
> 高亮渲染: [Base.html](https://choukh.github.io/agda-flypitch/FOL.Base.html)  

## 前言

本篇定义一阶逻辑的项与公式. 粗略类比, 如果说符号相当于字, 那么**项 (term)** 和**公式 (formula)** 则相当于词和句. 更准确地说, 项由变量与函数符号构成; 公式则由关系符号, 等号, 量化符号与连接符号等构成. 如上一篇所说, 本篇的所有内容都是参数化到语言的.

```agda
{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Base (ℒ : Language {u}) where
open Language ℒ
```

### 标准库依赖

```agda
open import Agda.Builtin.Equality
open import Cubical.Core.Primitives using (Type)

open import Data.Nat using (ℕ; suc; _+_; _∸_; _<?_)
open import Data.Nat.Properties using (<-cmp)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (tri<; tri≈; tri>)
```

### 符号优先级

```agda
infix 100 ~_
infix 10 _↑[_]_ _↑_ _↥[_]_ _↥_ _[_/_]
infix 9 _≈_
infix 8 _⇔_
infix 7 _⇒_
infixr 6 _∧_
infixr 5 _∨_
```

## 项

与语言的处理类似地，我们把函数的元数编码进项的类型里：变量和常量是 **0-项**，n元函数是 **n-项**。此外，变量采用 [De Brujin编码](https://en.wikipedia.org/wiki/De_Bruijn_index)，即把任意自然数当作变量。

**定义** 归纳定义 l-项:

- 对任意自然数 `n`，变量 `var n` 是 `0`-项.
- 对任意 `l` 元函数符号 `f`，函数 `func f` 是 `l`-项.
- 对任意 `suc l`-项 `t₁` 和任意 `0`-项 `t₂`，函数应用 `app t₁ t₂` 是 `l`-项.

特别地，`0`-项简称项。

其中 `l` 可以看作是参数表的长度. 我们始终保留字母 l 来表示它.

```agda
variable
  l : ℕ

data Termₗ : ℕ → Type u where
  var  : (k : ℕ) → Termₗ 0
  func : (f : functions l) → Termₗ l
  app  : (t₁ : Termₗ (suc l)) (t₂ : Termₗ 0) → Termₗ l

Term = Termₗ 0
```

由构造子的单射性立即有

```agda
var-injective : ∀ {k₁ k₂} → var k₁ ≡ var k₂ → k₁ ≡ k₂
var-injective refl = refl
```

这意味着对任意两个变量如果它们相等, 那么它们所使用的自然数相等. 类似地有

```agda
app-injectiveˡ : {t₁ t₂ : Termₗ (suc l)} {t₃ t₄ : Term}
  → app t₁ t₃ ≡ app t₂ t₄ → t₁ ≡ t₂
app-injectiveˡ refl = refl

app-injectiveʳ : {t₁ t₂ : Termₗ (suc l)} {t₃ t₄ : Term}
  → app t₁ t₃ ≡ app t₂ t₄ → t₃ ≡ t₄
app-injectiveʳ refl = refl
```

有时候我们希望把多元函数的参数全部应用上, 这时候可以用 `apps` 函数来实现.

```agda
apps : (t : Termₗ l) (ts : Vec Term l) → Term
apps t [] = t
apps f (t ∷ ts) = apps (app f t) ts
```

## 公式

n元关系在公式中的处理与n元函数在项中的处理类似, 我们把关系的元数编码进公式的类型里: n元关系是 **n-公式**.

至此, 非逻辑符号处理完毕. 接下来处理[逻辑符号](https://zh.wikipedia.org/wiki/%E4%B8%80%E9%98%B6%E9%80%BB%E8%BE%91#%E9%82%8F%E8%BC%AF%E7%AC%A6%E8%99%9F). 它们通常包括:

1. 等号: = (≈)
2. 量化符号:
  - 全称量化: ∀ (∀')
  - 存在量化: ∃ (∃')
3. 连接符号:
  - 否定: ¬ (~)
  - 蕴含: → (⇒)
  - 等价: ↔ (⇔)
  - 且: ∧
  - 或: ∨

括号中是为了避免与Agda元语言符号冲突而在本文中使用的符号.

这些符号不是独立的, 只需选取其中一些作为原始符号, 剩下的可以由它们推导出来. 不同的书根据不同的理由做出了不同的选取, 但得到的一阶逻辑系统基本是一样的. 我们根据Agda形式化的简便性 (具体会在后文逐渐体现), 选取等号 ≈, 蕴含 ⇒ , 全称量化 ∀' 和恒假 ⊥ 作为原始符号.

**定义** 归纳定义 l-公式:

- 恒假 `⊥` 是 `0`-公式.
- 对任意 `l` 元关系符号 `r`，关系 `rel R` 是 `l`-公式.
- 对任意 `suc l`-公式 `φ` 和任意项 `t`，关系应用 `appᵣ φ t` 是 `l`-公式.
- 对任意项 `t₁` 和 `t₂`，等式 `t₁ ≈ t₂` 是 `0`-公式.
- 对任意 `0`-公式 `φ₁` 和任意 `0`-公式 `φ₂`，蕴含式 `φ₁ ⇒ φ₂` 是 `0`-公式.
- 对任意 `0`-公式 `φ`，全称量化式 `∀' φ` 是 `0`-公式.

特别地, `0`-公式简称公式.

```agda
data Formulaₗ : ℕ → Type u where
  ⊥     : Formulaₗ 0
  rel   : (R : relations l) → Formulaₗ l
  appᵣ  : (φ : Formulaₗ (suc l)) (t : Term) → Formulaₗ l
  _≈_   : (t₁ t₂ : Term) → Formulaₗ 0
  _⇒_   : (φ₁ φ₂ : Formulaₗ 0) → Formulaₗ 0
  ∀'_   : (φ : Formulaₗ 0) → Formulaₗ 0

Formula = Formulaₗ 0
```

有时候我们希望把多元关系的参数全部应用上, 这时候可以用 `appsᵣ` 函数来实现.

```agda
appsᵣ : (φ : Formulaₗ l) (ts : Vec Term l) → Formula
appsᵣ φ [] = φ
appsᵣ φ (t ∷ ts) = appsᵣ (appᵣ φ t) ts
```

**注意** 我们将元数编码进类型里是为了省去所谓的[合式公式 (well-formed formula，WFF)](https://zh.wikipedia.org/wiki/%E5%90%88%E5%BC%8F%E5%85%AC%E5%BC%8F) 谓词. 任意 `φ : Formula` 都是合式公式, 类型正确性保证了 `φ` 的合式性.


## 导出符号

仿照类型论的处理, φ 的否定定义为 φ 蕴含恒假. 而恒真则是恒假的否定. 由于我们的对象逻辑是经典逻辑, 所以可以这样方便地处理.

```agda
~_ : Formula → Formula
~ φ = φ ⇒ ⊥

⊤ : Formula
⊤ = ~ ⊥
```

其他逻辑符号的定义也是同样地利用了经典逻辑的特性. 它们都可以在加了排中律的 Agda 中"证"出来.

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

## 变量提升

变量提升属于[De Brujin编码](https://en.wikipedia.org/wiki/De_Bruijn_index)方案的一部分, 用于处理量词的绑定, 具体会在后文中体现.

简单来说, 变量提升就是把变量符号表 `var : ℕ → Term` 的某一段去掉, 以剩下的变量符号来重新表达原来的项和公式. 例如, 对项 `t`, 从 `var m` 开始, 去掉 `n` 个符号, 就叫做将 `t` 从 `m` 提升 `n`, 记作 `t ↑[ m ] n`.

如果项 `t` 使用了变量 `var 0`, `var 1`, `var 2`, `var 3`, 那么 `t ↑[ 1 ] 2` 则会使用变量 `var 0`, `var 3`, `var 4`, `var 5`.

特别地, 如果 `m = 0`, 就叫做将 `t` 提升 `n`, 记作 `t ↑ n`.

```agda
_↑[_]_ : (t : Termₗ l) (m n : ℕ) → Termₗ l
var k     ↑[ m ] n with k <? m
... | yes _ = var k
... | no  _ = var (k + n)
func f    ↑[ m ] n = func f
app t₁ t₂ ↑[ m ] n = app (t₁ ↑[ m ] n) (t₂ ↑[ m ] n)

_↑_ : (t : Termₗ l) (n : ℕ) → Termₗ l
t ↑ n = t ↑[ 0 ] n
```

对公式的变量提升基本上就是对其中的项进行变量提升, 或者是对公式中的公式递归地提升. 只是对于量词构造的公式, 保留一位变量不提升, 以作为量词的绑定变量.

```agda
_↥[_]_ : (φ : Formulaₗ l) (m n : ℕ) → Formulaₗ l
⊥         ↥[ m ] n = ⊥
rel R     ↥[ m ] n = rel R
appᵣ φ t  ↥[ m ] n = appᵣ (φ ↥[ m ] n) (t ↑[ m ] n)
(t₁ ≈ t₂) ↥[ m ] n = t₁ ↑[ m ] n ≈ t₂ ↑[ m ] n
(φ₁ ⇒ φ₂) ↥[ m ] n = φ₁ ↥[ m ] n ⇒ φ₂ ↥[ m ] n
∀' φ      ↥[ m ] n = ∀' (φ ↥[ suc m ] n)

_↥_ : (φ : Formulaₗ l) (n : ℕ) → Formulaₗ l
φ ↥ n = φ ↥[ 0 ] n
```

## 变量替换

变量替换用于处理量词绑定变量的替换和等量的替换. 首先我们需要一个帮助函数, 往序列 `𝓋 : ℕ → A` 中插入指定的项 `s` 于指定的位置 `n`. 例如, 如果 `v` 是序列

`t₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ ...`

那么 `insert s into 𝓋 at 4` 就是序列

`t₀ t₁ t₂ t₃ s t₄ t₅ t₆ t₇ ...`

```agda
insert_into_at_ : ∀ {u} {A : Type u} (s : A) (𝓋 : ℕ → A) (n : ℕ) → (ℕ → A)
(insert s into 𝓋 at n) k with <-cmp k n
... | tri< _ _ _ = 𝓋 k
... | tri≈ _ _ _ = s
... | tri> _ _ _ = 𝓋 (k ∸ 1)
```

将项 `t` 中的变量 `var n` (如果存在) 替换为项 `s` 后得到的项记作 `t [ s /ₜ n ]`. 如果项是变量 `var k`, 那么将变量符号表 `var` 改造成 `insert (s ↑ n) into var at n`, 再取其中的第 `k` 个. 如果项是函数应用, 那么递归地替换其中的项.

其中, `insert (s ↑ n) into var at n` 的意思是往 `var` 中插入 `s ↑ n` 于 `n` 处. 将 `s` 提升 `n` 是为了保证 `s` 中的变量不会与 `t` 中的变量冲突.

```agda
_[_/_]ᵥ : ∀ {u} {A : Type u} (𝓋 : ℕ → A) (s : A) (n : ℕ) → (ℕ → A)
𝓋 [ s / n ]ᵥ = insert s into 𝓋 at n

_[_/_]ₜ : (t : Termₗ l) (s : Term) (n : ℕ) → Termₗ l
var k     [ s / n ]ₜ = var [ (s ↑ n) / n ]ᵥ $ k
func f    [ s / n ]ₜ = func f
app t₁ t₂ [ s / n ]ₜ = app (t₁ [ s / n ]ₜ) (t₂ [ s / n ]ₜ)
```

对公式的变量替换基本上就是对其中的项进行变量替换, 或者是对公式中的公式递归地替换. 只是对于量词构造的公式, 将替换的位置顺延一位, 因为首位是量词的绑定变量.

```agda
_[_/_] : (φ : Formulaₗ l) (s : Term) (n : ℕ) → Formulaₗ l
⊥         [ s / n ] = ⊥
rel R     [ s / n ] = rel R
appᵣ φ t  [ s / n ] = appᵣ (φ [ s / n ]) (t [ s / n ]ₜ)
(t₁ ≈ t₂) [ s / n ] = t₁ [ s / n ]ₜ ≈ t₂ [ s / n ]ₜ
(φ₁ ⇒ φ₂) [ s / n ] = φ₁ [ s / n ] ⇒ φ₂ [ s / n ]
∀' φ      [ s / n ] = ∀' (φ [ s / suc n ])
```
