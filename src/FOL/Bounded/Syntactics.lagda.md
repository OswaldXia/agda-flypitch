---
title: Agda一阶逻辑(?) 理论与证明 (束缚)
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(?) 理论与证明 (束缚)

> 交流Q群: 893531731  
> 本文源码: [Syntactics.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Bounded/Syntactics.lagda.md)  
> 高亮渲染: [Syntactics.html](https://choukh.github.io/agda-flypitch/FOL.Bounded.Syntactics.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
module FOL.Bounded.Syntactics (ℒ : Language {u}) where
open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Sethood ℒ

private module Free where
  open import FOL.Base ℒ public
  open import FOL.Sethood ℒ public
  open import FOL.Syntactics ℒ public
open Free._⊢_ hiding (axiom)

open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (Type; ℓ-suc; _,_; isSet)
open import Cubical.Functions.Logic using (inl; inr)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁)
open import CubicalExt.Foundations.Powerset* as 𝒫 using (𝒫; isSet𝒫; _∈_; _⊆_; _⟦_⟧; ⟦⟧⊆⟦⟧)

open import Function using (_$_)
```

## 理论

```agda
Theory : Type (ℓ-suc u)
Theory = 𝒫 Sentence u

isSetTheory : isSet Theory
isSetTheory = isSet𝒫
```

```agda
open 𝒫.SetBased {X = Sentence} isSetFormula
open 𝒫.SetBased2 {X = Sentence} {Y = Free.Formula} isSetFormula Free.isSetFormula
open 𝒫.SetBased {X = Free.Formula} Free.isSetFormula using () renaming (_⨭_ to _Free⨭_)
```

## 证明

```agda
infix 4 _⊢_
_⊢_ : Theory → Sentence → Type (ℓ-suc u)
Γ ⊢ φ = unbound ⟦ Γ ⟧ Free.⊢ unbound φ
```

我们用更短的 `⊦` 表示 `⊢` 的命题截断.

```agda
infix 4 _⊦_
_⊦_ : Theory → Sentence → Type (ℓ-suc u)
Γ ⊦ φ = ∥ Γ ⊢ φ ∥₁
```

虽然我们最终只关心 `⊦`, 例如一阶逻辑的完备性将使用 `⊦` 来表达, 但在此之前需要先证明一系列关于 `⊢` 的引理.

```agda
weakening : ∀ {Γ Δ} {φ} → Γ ⊆ Δ → Γ ⊢ φ → Δ ⊢ φ
weakening Γ⊆Δ Γ⊢φ = Free.weakening (⟦⟧⊆⟦⟧ Γ⊆Δ) Γ⊢φ

weakening1 : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₂ → Γ ⨭ φ₁ ⊢ φ₂
weakening1 = weakening ⊆⨭

weakening2 : ∀ {Γ : Theory} {φ₁ φ₂ φ₃} → Γ ⨭ φ₁ ⊢ φ₂ → Γ ⨭ φ₃ ⨭ φ₁ ⊢ φ₂
weakening2 = weakening (⨭⊆⨭ ⊆⨭)
```

```agda
axiom : ∀ {Γ : Theory} {φ} → φ ∈ Γ → Γ ⊢ φ
axiom φ∈Γ = Free.axiom ∣ _ , φ∈Γ , reflId ∣₁

axiom1 : ∀ {Γ : Theory} {φ} → Γ ⨭ φ ⊢ φ
axiom1 = axiom $ inr reflId

axiom2 : ∀ {Γ : Theory} {φ₁ φ₂} → Γ ⨭ φ₁ ⨭ φ₂ ⊢ φ₁
axiom2 = axiom $ inl $ inr reflId
```

## 导出规则

```agda
bound⊢ : ∀ {Γ : Theory} {φ₁ φ₂} → Γ ⨭ φ₂ ⊢ φ₁ → unbound ⟦ Γ ⟧ Free⨭ unbound φ₂ Free.⊢ unbound φ₁
bound⊢ = Free.weakening ⟦⨭⟧⊆
```

### `⇒` 的补充规则

`⇒-intro` 在有些书中称为[**演绎定理 (deduction theorem)**](https://zh.wikipedia.org/wiki/%E4%B8%80%E9%98%B6%E9%80%BB%E8%BE%91#%E6%BC%94%E7%B9%B9%E5%85%83%E5%AE%9A%E7%90%86). 我们这里直接指定为规则. 以下是它的逆命题. 两者结合表明了 `Γ , φ₁ ⊢ φ₂` 与 `Γ ⊢ φ₁ ⇒ φ₂` 的等价性.

```agda
⇒-elim-to-axiom : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇒ φ₂ → Γ ⨭ φ₁ ⊢ φ₂
⇒-elim-to-axiom Γ⊢⇒ = ⇒-elim (weakening1 Γ⊢⇒) axiom1
```

以下可以认为是 `⇒-elim` 的逆命题, 但要注意 `→` 的两边都要对理论做全称量化. 此外, 满足 `∀ Γ → Γ ⊢ φ` 的 `φ` 又称为**恒真式 (tautology)**. 所以以下命题又称为恒真式的引入规则.

```agda
⇒-intro-tauto : ∀ {φ₁ φ₂} → (∀ {Γ} → Γ ⊢ φ₁ → Γ ⊢ φ₂) → ∀ {Δ} → Δ ⊢ φ₁ ⇒ φ₂
⇒-intro-tauto {φ₁} ⊢ = ⇒-intro $ bound⊢ $ weakening {Γ = ｛ φ₁ ｝} inr $ ⊢ $ axiom reflId
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

∨-elim : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⊢ φ₁ ∨ φ₂ → Γ ⨭ φ₁ ⊢ φ₃ → Γ ⨭ φ₂ ⊢ φ₃ → Γ ⊢ φ₃
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
⇔-intro : ∀ {Γ φ₁ φ₂} → Γ ⨭ φ₁ ⊢ φ₂ → Γ ⨭ φ₂ ⊢ φ₁ → Γ ⊢ φ₁ ⇔ φ₂
⇔-intro ⊢₁ ⊢₂ = Free.⇔-intro (bound⊢ ⊢₁) (bound⊢ ⊢₂)

⇔-elimₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⨭ φ₁ ⊢ φ₂
⇔-elimₗ ⊢⇔ = ⇒-elim-to-axiom (∧-elimₗ ⊢⇔)

⇔-elimᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⨭ φ₂ ⊢ φ₁
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
  