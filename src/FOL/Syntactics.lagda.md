---
title: Agda一阶逻辑(3) 理论与证明
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(3) 理论与证明

> 交流Q群: 893531731  
> 本文源码: [Syntactics.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Syntactics.lagda.md)  
> 高亮渲染: [Syntactics.html](https://choukh.github.io/agda-flypitch/FOL.Syntactics.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
module FOL.Syntactics (ℒ : Language {u}) where
open import FOL.Base ℒ
open import FOL.Lemmas.Sethood ℒ
```

### 标准库依赖

```agda
open import Agda.Builtin.Equality
open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (Type; ℓ-suc; isSet)
open import Cubical.Functions.Logic using (inl; inr)
open import CubicalExt.Foundations.Powerset* as 𝒫 using (𝒫; isSet𝒫; _∈_; _⊆_; _⟦_⟧; ⟦⟧⊆⟦⟧)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)

open import Data.Nat as ℕ using (ℕ)
open import Function using (_$_)
```

## 理论

公式集的子集叫做**理论 (theory)**, 其元素也叫做公理.

```agda
Theory : Type (ℓ-suc u)
Theory = 𝒫 Formula u

isSetTheory : isSet Theory
isSetTheory = isSet𝒫

open 𝒫.SetBased {X = Formula} isSetFormula
open 𝒫.SetBased2 {X = Formula} {Y = Formula} isSetFormula isSetFormula
```

理论可以通过添加新的公式来扩展. 我们用 `Γ ⨭ φ` 来表示将公式 `φ` 加入到理论 `Γ` 中.

理论 `Γ` 在函数 `_↥ n` 之下的像叫做理论 `Γ` 的 `n` 提升, 记作 `Γ ⇑ n`.

```agda
_⇑_ : Theory → ℕ → Theory
Γ ⇑ n = (_↥ n) ⟦ Γ ⟧
```

## 证明

有了理论和公式的定义, 我们终于可以定义什么叫证明. 我们采用所谓[**自然演绎 (natural deduction)**](https://zh.m.wikipedia.org/zh/%E8%87%AA%E7%84%B6%E6%BC%94%E7%BB%8E)的方案.

**定义** 我们说理论 `Γ` 可以证明公式 `φ` (记作 `Γ ⊢ φ`) 当且仅当以下任意一种情况成立:

- `φ` 是理论 `Γ` 的公理, 即 `φ` 是公式集 `Γ` 的元素.
- `Γ` 加上 `~ φ` 可以证明假. **("假"的消去规则)**
- `φ` 是某项 `t` 构造的等式 `t ≈ t`. **(等式的消去规则)**
- `φ` 是某公式 `φ₁` 和 `φ₂` 构造的蕴含式 `φ₁ ⇒ φ₂`, 且 `Γ` 加上 `φ₁` 可以证明 `φ₂`. **(蕴含式的引入规则)**
- 已知 `Γ` 可以证明 `φ₁ ⇒ φ`, 且 `Γ` 可以证明 `φ₁`. **(蕴含式的消去规则)**
- `φ` 是某公式 `φ₁` 构造的全称量化式 `∀' φ₁`, 且 `Γ ⇑ 1` 可以证明 `φ₁`. **(全称量化式的引入规则)**
- `φ` 是将某公式 `φ₁` 的变量 `var 0` 替换成某项 `t` 而得到的公式 `φ₁ [ 0 ≔ t ]`, 且 `Γ` 可以证明 `∀' φ₁`. **(全称量化式的消去规则)**
- `φ` 是某替换式 `φ₁ [ 0 ≔ t ]`, 且 `Γ` 可以证明 `φ₁ [ 0 ≔ s ]`, 且 `Γ` 可以证明 `t` 和 `s` 相等. **(替换规则)**

```agda
infix 4 _⊢_
data _⊢_ : Theory → Formula → Type (ℓ-suc u) where
  axiom   : ∀ {Γ φ} → φ ∈ Γ → Γ ⊢ φ
  ⊥-elim  : ∀ {Γ φ} → Γ ⨭ ~ φ ⊢ ⊥ → Γ ⊢ φ
  ≈-refl  : ∀ {Γ t} → Γ ⊢ t ≈ t
  ⇒-intro : ∀ {Γ φ₁ φ₂} → Γ ⨭ φ₁ ⊢ φ₂ → Γ ⊢ φ₁ ⇒ φ₂
  ⇒-elim  : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇒ φ₂ → Γ ⊢ φ₁ → Γ ⊢ φ₂
  ∀-intro : ∀ {Γ φ} → Γ ⇑ 1 ⊢ φ → Γ ⊢ ∀' φ
  ∀-elim  : ∀ {Γ φ t} → Γ ⊢ ∀' φ → Γ ⊢ φ [ 0 ≔ t ]
  subst   : ∀ {Γ s t φ} → Γ ⊢ s ≈ t → Γ ⊢ φ [ 0 ≔ s ] → Γ ⊢ φ [ 0 ≔ t ]
```

以上规则大部分都符合直观, 我们只讲全称量词相关的两条规则 `∀-intro` 和 `∀-elim`. 首先这两条可以合并看作一条: `Γ ⇑ 1 ⊢ φ → Γ ⊢ φ [ 0 ≔ t ]`. 它说如果不使用变量 `var 0` 而表达的理论 `Γ ⇑ 1` 能证明 `φ`, 那么可以将 `φ` 中的 `var 0` 换成任意项, 所得到的 `φ [ 0 ≔ t ]` 能被恢复使用 `var 0` 的理论 `Γ` 所证明. 这就是从指定 `var 0` 为全称量化专用变量, 到将它替换为其他项并撤销该指定的自然过程, 而 `∀' φ` 只是这一过程的中间状态表示.

以下 `subst` 规则的变体在某些情况下更方便使用.

```agda
≈-≡-subst : ∀ {Γ t₁ t₂} (φ₁ : Formula) {φ₂ : Formula}
  → Γ ⊢ t₁ ≈ t₂ → Γ ⊢ φ₁ [ 0 ≔ t₁ ] → φ₁ [ 0 ≔ t₂ ] ≡ φ₂ → Γ ⊢ φ₂
≈-≡-subst φ₁ H₁ H₂ refl = subst H₁ H₂
```

我们用更短的 `⊦` 表示 `⊢` 的命题截断.

```agda
infix 4 _⊦_
_⊦_ : Theory → Formula → Type (ℓ-suc u)
Γ ⊦ φ = ∥ Γ ⊢ φ ∥₁
```

虽然我们最终只关心 `⊦`, 例如一阶逻辑的完备性将使用 `⊦` 来表达, 但在此之前需要先证明一系列关于 `⊢` 的引理.

## 理论的弱化

我们将补完导出符号 `∧` 等的相关规则. 为此需要先证明一个重要引理.

**引理 (弱化)** 对于任意理论 `Γ` 和 `Δ`, 如果 `Δ` 包含了 `Γ`, 那么 `Γ` 可以证明的任意 `φ` 都可以被 `Δ` 证明.

证明: 简单的集合论事实配合归纳法即可. ∎

```agda
weakening : ∀ {Γ Δ φ} → Γ ⊆ Δ → Γ ⊢ φ → Δ ⊢ φ
weakening Γ⊆Δ (axiom φ∈Γ)     = axiom   (Γ⊆Δ φ∈Γ)
weakening Γ⊆Δ (⊥-elim ⊢)      = ⊥-elim  (weakening (⨭⊆⨭ Γ⊆Δ) ⊢)
weakening Γ⊆Δ ≈-refl          = ≈-refl
weakening Γ⊆Δ (⇒-intro ⊢)     = ⇒-intro (weakening (⨭⊆⨭ Γ⊆Δ) ⊢)
weakening Γ⊆Δ (⇒-elim ⊢₁ ⊢₂)  = ⇒-elim  (weakening Γ⊆Δ ⊢₁) (weakening Γ⊆Δ ⊢₂)
weakening Γ⊆Δ (∀-intro ⊢)     = ∀-intro (weakening (⟦⟧⊆⟦⟧ Γ⊆Δ) ⊢)
weakening Γ⊆Δ (∀-elim ⊢)      = ∀-elim  (weakening Γ⊆Δ ⊢)
weakening Γ⊆Δ (subst ⊢₁ ⊢₂)   = subst   (weakening Γ⊆Δ ⊢₁) (weakening Γ⊆Δ ⊢₂)
```

以下是两个简单的变化形式, 它们会经常用到.

```agda
weakening1 : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₂ → Γ ⨭ φ₁ ⊢ φ₂
weakening1 = weakening ⊆⨭

weakening2 : ∀ {Γ : Theory} {φ₁ φ₂ φ₃} → Γ ⨭ φ₁ ⊢ φ₂ → Γ ⨭ φ₃ ⨭ φ₁ ⊢ φ₂
weakening2 = weakening (⨭⊆⨭ ⊆⨭)
```

与之类似地是 `axiom` 规则的两个变化形式.

```agda
axiom1 : ∀ {Γ : Theory} {φ} → Γ ⨭ φ ⊢ φ
axiom1 = axiom (inr reflId)

axiom2 : ∀ {Γ : Theory} {φ₁ φ₂} → Γ ⨭ φ₁ ⨭ φ₂ ⊢ φ₁
axiom2 = axiom (inl (inr reflId))
```

## 导出规则

### `⇒` 的补充规则

`⇒-intro` 在有些书中称为[**演绎定理 (deduction theorem)**](https://zh.wikipedia.org/wiki/%E4%B8%80%E9%98%B6%E9%80%BB%E8%BE%91#%E6%BC%94%E7%B9%B9%E5%85%83%E5%AE%9A%E7%90%86). 我们这里直接指定为规则. 以下是它的逆命题. 两者结合表明了 `Γ ⨭ φ₁ ⊢ φ₂` 与 `Γ ⊢ φ₁ ⇒ φ₂` 的等价性.

```agda
⇒-elim-to-axiom : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇒ φ₂ → Γ ⨭ φ₁ ⊢ φ₂
⇒-elim-to-axiom Γ⊢⇒ = ⇒-elim (weakening1 Γ⊢⇒) axiom1
```

以下可以认为是 `⇒-elim` 的逆命题, 但要注意 `→` 的两边都要对理论做全称量化. 此外, 满足 `∀ Γ → Γ ⊢ φ` 的 `φ` 又称为**恒真式 (tautology)**. 所以以下命题又称为恒真式的引入规则.

```agda
⇒-intro-tauto : ∀ {φ₁ φ₂} → (∀ {Γ} → Γ ⊢ φ₁ → Γ ⊢ φ₂) → ∀ {Δ} → Δ ⊢ φ₁ ⇒ φ₂
⇒-intro-tauto {φ₁} ⊢ = ⇒-intro $ weakening {Γ = ｛ φ₁ ｝} inr $ ⊢ $ axiom reflId
```

以下规则我们直接列出名称而不再加以说明.

### 爆炸律

```agda
exfalso : ∀ {Γ φ} → Γ ⊢ ⊥ → Γ ⊢ φ
exfalso Γ⊢⊥ = ⊥-elim (weakening1 Γ⊢⊥)

tauto-exfalso : ∀ {Γ φ} → Γ ⊢ ⊥ ⇒ φ
tauto-exfalso = ⇒-intro-tauto exfalso
```

### `∧` 的引入与消去规则

```agda
∧-intro : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ → Γ ⊢ φ₂ → Γ ⊢ φ₁ ∧ φ₂
∧-intro Γ⊢φ₁ Γ⊢φ₂ = ⇒-intro $ ⇒-elim (⇒-elim axiom1 (weakening1 Γ⊢φ₁)) (weakening1 Γ⊢φ₂)

∧-elimₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ∧ φ₂ → Γ ⊢ φ₁
∧-elimₗ ⊢∧ = ⊥-elim $ ⇒-elim (weakening1 ⊢∧) (⇒-intro $ exfalso $ ⇒-elim axiom2 axiom1)

∧-elimᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ∧ φ₂ → Γ ⊢ φ₂
∧-elimᵣ ⊢∧ = ⊥-elim $ ⇒-elim (weakening1 ⊢∧) (⇒-intro axiom2)
```

### `∨` 的引入与消去规则

```agda
∨-introₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ → Γ ⊢ φ₁ ∨ φ₂
∨-introₗ Γ⊢φ₁ = ⇒-intro $ exfalso $ ⇒-elim axiom1 (weakening1 Γ⊢φ₁)

∨-introᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₂ → Γ ⊢ φ₁ ∨ φ₂
∨-introᵣ Γ⊢φ₂ = ⇒-intro $ weakening1 Γ⊢φ₂

∨-elim : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⊢ φ₁ ∨ φ₂ → Γ ⨭ φ₁ ⊢ φ₃ → Γ ⨭ φ₂ ⊢ φ₃ → Γ ⊢ φ₃
∨-elim Γ⊢∨ ⊢₁ ⊢₂ = ⊥-elim $ ⇒-elim axiom1 Γ,φ₃⇒⊥⊢φ₃ where
  Γ,φ₃⇒⊥⊢φ₃ = ⇒-elim (⇒-intro $ weakening2 ⊢₂) Γ,φ₃⇒⊥⊢φ₂ where
    Γ,φ₃⇒⊥⊢φ₂ = ⇒-elim (weakening1 Γ⊢∨) (⇒-intro $ ⇒-elim axiom2 (weakening2 ⊢₁))

∨-comm : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ∨ φ₂ → Γ ⊢ φ₂ ∨ φ₁
∨-comm ⊢∨ = ∨-elim ⊢∨ (∨-introᵣ axiom1) (∨-introₗ axiom1)
```

### 排中律

```agda
LEM : ∀ {Γ φ} → Γ ⊢ φ ∨ ~ φ
LEM = ⇒-intro axiom1

DNE : ∀ {Γ φ} → Γ ⊢ ~ ~ φ ⇒ φ
DNE = ∨-comm LEM
```

### 矛盾律

```agda
no-contra : ∀ {Γ φ} → Γ ⊢ φ ∧ ~ φ → Γ ⊢ ⊥
no-contra ⊢ = ⇒-elim (∧-elimᵣ ⊢) (∧-elimₗ ⊢)

tauto-no-contra : ∀ {Γ φ} → Γ ⊢ ~ (φ ∧ ~ φ)
tauto-no-contra = ⇒-intro-tauto no-contra
```

### `⇔` 的引入与消去规则

```agda
⇔-intro : ∀ {Γ φ₁ φ₂} → Γ ⨭ φ₁ ⊢ φ₂ → Γ ⨭ φ₂ ⊢ φ₁ → Γ ⊢ φ₁ ⇔ φ₂
⇔-intro ⊢₁ ⊢₂ = ∧-intro (⇒-intro ⊢₁) (⇒-intro ⊢₂)

⇔-elimₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⨭ φ₁ ⊢ φ₂
⇔-elimₗ ⊢⇔ = ⇒-elim-to-axiom (∧-elimₗ ⊢⇔)

⇔-elimᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⨭ φ₂ ⊢ φ₁
⇔-elimᵣ ⊢⇔ = ⇒-elim-to-axiom (∧-elimᵣ ⊢⇔)
```

### `⇔` 的自反性、对称性和传递性

```agda
⇔-refl : ∀ {Γ φ} → Γ ⊢ φ ⇔ φ
⇔-refl = ⇔-intro axiom1 axiom1

⇔-sym : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⊢ φ₂ ⇔ φ₁
⇔-sym ⊢ = ⇔-intro (⇔-elimᵣ ⊢) (⇔-elimₗ ⊢)

⇒-trans : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⊢ φ₁ ⇒ φ₂ → Γ ⊢ φ₂ ⇒ φ₃ → Γ ⊢ φ₁ ⇒ φ₃
⇒-trans ⊢₁ ⊢₂ = ⇒-intro $ ⇒-elim (weakening1 ⊢₂) (⇒-elim (weakening1 ⊢₁) axiom1)

⇔-trans : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⊢ φ₂ ⇔ φ₃ → Γ ⊢ φ₁ ⇔ φ₃
⇔-trans ⊢₁ ⊢₂ = ∧-intro
  (⇒-trans (∧-elimₗ ⊢₁) (∧-elimₗ ⊢₂))
  (⇒-trans (∧-elimᵣ ⊢₂) (∧-elimᵣ ⊢₁))
```

### `∃` 的引入与消去规则

```agda
∃-intro : ∀ {Γ φ} (t : Term) → Γ ⊢ φ [ 0 ≔ t ] → Γ ⊢ ∃' φ
∃-intro t ⊢ = ⇒-intro $ ⇒-elim (∀-elim axiom1) (weakening1 ⊢)

∃-elim : ∀ {Γ φ₁ φ₂} → Γ ⊢ ∃' φ₁ → Γ ⇑ 1 ⨭ φ₁ ⊢ φ₂ ↥ 1 → Γ ⊢ φ₂
∃-elim {Γ} {φ₁} {φ₂} ⊢∃ ⊢ = ⊥-elim $ ⇒-elim (weakening1 ⊢∃)
  -- Goal : Γ , ~ φ₂ ⊢ ∀' ~ φ₁
  (∀-intro $ ⇒-intro $ ⇒-elim
    -- Goal : (Γ , ~ φ₂) ⇑ 1 , φ₁ ⊢ ~ φ₂ ↥ 1
    (weakening1 $ weakening (⊆⟦⨭⟧ {f = _↥ 1} {A = Γ} {x = ~ φ₂}) axiom1)
    -- Goal : (Γ , ~ φ₂) ⇑ 1 , φ₁ ⊢ φ₂ ↥ 1
    (weakening (⨭⊆⨭ $ ⟦⟧⊆⟦⟧ $ ⊆⨭ {A = Γ}) ⊢)
  )
```
