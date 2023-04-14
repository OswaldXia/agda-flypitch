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
module FOL.Bounded.Base (ℒ : Language {u}) where
import FOL.Base ℒ as Free
open Language ℒ
open Free using (l) public
open Free.Termₗ
open Free.Formulaₗ
open Free._⊢_
```

### 标准库依赖

```agda
open import Agda.Builtin.Equality
open import Cubical.Core.Primitives using (Type; ℓ-suc; _,_)
open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (isSet)
open import Cubical.Functions.Logic using (inl; inr)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import CubicalExt.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; squash₂; map)
open import CubicalExt.Foundations.Powerset* as 𝒫 using (𝒫; isSet𝒫; _∈_; _⊆_; _⟦_⟧; ⟦⟧⊆⟦⟧)

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
infixl 6 _+_
infixr 6 _∧_
infixr 5 _∨_
infix 4 _⊢_
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

### 理论

```agda
Theory : Type (ℓ-suc u)
Theory = 𝒫 ∥ Sentence ∥₂ u

isSetTheory : isSet Theory
isSetTheory = isSet𝒫
```

```agda
open 𝒫.SetBased {X = ∥ Sentence ∥₂} squash₂
open 𝒫.SetBased2 {X = ∥ Sentence ∥₂} {Y = ∥ Free.Formula ∥₂} squash₂ squash₂

_+_ : Theory → Sentence → Theory
Γ + φ = Γ ⨭ ∣ φ ∣₂
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

## 证明

```agda
_⊢_ : Theory → Sentence → Type (ℓ-suc u)
Γ ⊢ φ = map unbound ⟦ Γ ⟧ Free.⊢ unbound φ
```

```agda
weakening : ∀ {Γ Δ} {φ} → Γ ⊆ Δ → Γ ⊢ φ → Δ ⊢ φ
weakening Γ⊆Δ Γ⊢φ = Free.weakening (⟦⟧⊆⟦⟧ Γ⊆Δ) Γ⊢φ

weakening1 : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₂ → Γ + φ₁ ⊢ φ₂
weakening1 = weakening ⊆⨭

weakening2 : ∀ {Γ : Theory} {φ₁ φ₂ φ₃} → Γ + φ₁ ⊢ φ₂ → Γ + φ₃ + φ₁ ⊢ φ₂
weakening2 = weakening (⨭⊆⨭ ⊆⨭)
```

```agda
axiom1 : ∀ {Γ : Theory} {φ} → Γ + φ ⊢ φ
axiom1 = axiom ∣ _ , inr reflId , reflId ∣₁

axiom2 : ∀ {Γ : Theory} {φ₁ φ₂} → Γ + φ₁ + φ₂ ⊢ φ₁
axiom2 = axiom ∣ _ , inl (inr reflId) , reflId ∣₁
```

## 导出规则

```agda
bound⊢ : ∀ {Γ : Theory} {φ₁ φ₂} → Γ + φ₂ ⊢ φ₁ → map unbound ⟦ Γ ⟧ Free.+ unbound φ₂ Free.⊢ unbound φ₁
bound⊢ = Free.weakening ⟦⨭⟧⊆
```

### `⇒` 的补充规则

`⇒-intro` 在有些书中称为[**演绎定理 (deduction theorem)**](https://zh.wikipedia.org/wiki/%E4%B8%80%E9%98%B6%E9%80%BB%E8%BE%91#%E6%BC%94%E7%B9%B9%E5%85%83%E5%AE%9A%E7%90%86). 我们这里直接指定为规则. 以下是它的逆命题. 两者结合表明了 `Γ , φ₁ ⊢ φ₂` 与 `Γ ⊢ φ₁ ⇒ φ₂` 的等价性.

```agda
⇒-elim-to-axiom : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇒ φ₂ → Γ + φ₁ ⊢ φ₂
⇒-elim-to-axiom Γ⊢⇒ = ⇒-elim (weakening1 Γ⊢⇒) axiom1
```

以下可以认为是 `⇒-elim` 的逆命题, 但要注意 `→` 的两边都要对理论做全称量化. 此外, 满足 `∀ Γ → Γ ⊢ φ` 的 `φ` 又称为**恒真式 (tautology)**. 所以以下命题又称为恒真式的引入规则.

```agda
⇒-intro-tauto : ∀ {φ₁ φ₂} → (∀ {Γ} → Γ ⊢ φ₁ → Γ ⊢ φ₂) → ∀ {Δ} → Δ ⊢ φ₁ ⇒ φ₂
⇒-intro-tauto {φ₁} ⊢ = ⇒-intro $ bound⊢ $ weakening inr $ ⊢ $ axiom $ ⊆⟦｛｝⟧ reflId
```

以下规则我们直接列出名称而不再加以说明.

### 爆炸律

```agda
exfalso : ∀ {Γ φ} → Γ ⊢ ⊥ → Γ ⊢ φ
exfalso = Free.exfalso

tauto-exfalso : ∀ {Γ φ} → Γ ⊢ ⊥ ⇒ φ
tauto-exfalso = Free.tauto-exfalso
```

### `∧` 的引入引出规则

```agda
∧-intro : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ → Γ ⊢ φ₂ → Γ ⊢ φ₁ ∧ φ₂
∧-intro = Free.∧-intro

∧-elimₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ∧ φ₂ → Γ ⊢ φ₁
∧-elimₗ = Free.∧-elimₗ

∧-elimᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ∧ φ₂ → Γ ⊢ φ₂
∧-elimᵣ = Free.∧-elimᵣ
```

### `∨` 的引入引出规则

```agda
∨-introₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ → Γ ⊢ φ₁ ∨ φ₂
∨-introₗ = Free.∨-introₗ

∨-introᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₂ → Γ ⊢ φ₁ ∨ φ₂
∨-introᵣ = Free.∨-introᵣ

∨-elim : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⊢ φ₁ ∨ φ₂ → Γ + φ₁ ⊢ φ₃ → Γ + φ₂ ⊢ φ₃ → Γ ⊢ φ₃
∨-elim Γ⊢∨ ⊢₁ ⊢₂ = Free.∨-elim Γ⊢∨ (bound⊢ ⊢₁) (bound⊢ ⊢₂)

∨-comm : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ∨ φ₂ → Γ ⊢ φ₂ ∨ φ₁
∨-comm = Free.∨-comm
```

### 排中律

```agda
LEM : ∀ {Γ φ} → Γ ⊢ φ ∨ ~ φ
LEM = Free.LEM

DNE : ∀ {Γ φ} → Γ ⊢ ~ ~ φ ⇒ φ
DNE = Free.DNE
```

### 矛盾律

```agda
no-contra : ∀ {Γ φ} → Γ ⊢ φ ∧ ~ φ → Γ ⊢ ⊥
no-contra = Free.no-contra

tauto-no-contra : ∀ {Γ φ} → Γ ⊢ ~ (φ ∧ ~ φ)
tauto-no-contra = Free.tauto-no-contra
```

### `⇔` 的引入引出规则

```agda
⇔-intro : ∀ {Γ φ₁ φ₂} → Γ + φ₁ ⊢ φ₂ → Γ + φ₂ ⊢ φ₁ → Γ ⊢ φ₁ ⇔ φ₂
⇔-intro ⊢₁ ⊢₂ = Free.⇔-intro (bound⊢ ⊢₁) (bound⊢ ⊢₂)

⇔-elimₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ + φ₁ ⊢ φ₂
⇔-elimₗ ⊢⇔ = ⇒-elim-to-axiom (∧-elimₗ ⊢⇔)

⇔-elimᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ + φ₂ ⊢ φ₁
⇔-elimᵣ ⊢⇔ = ⇒-elim-to-axiom (∧-elimᵣ ⊢⇔)
```

### `⇔` 的自反性、对称性和传递性

```agda
⇔-refl : ∀ {Γ φ} → Γ ⊢ φ ⇔ φ
⇔-refl = Free.⇔-refl

⇔-sym : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⊢ φ₂ ⇔ φ₁
⇔-sym = Free.⇔-sym

⇒-trans : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⊢ φ₁ ⇒ φ₂ → Γ ⊢ φ₂ ⇒ φ₃ → Γ ⊢ φ₁ ⇒ φ₃
⇒-trans = Free.⇒-trans

⇔-trans : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⊢ φ₂ ⇔ φ₃ → Γ ⊢ φ₁ ⇔ φ₃
⇔-trans = Free.⇔-trans
```
