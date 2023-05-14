---
title: Agda佐恩引理
zhihu-tags: Agda, 数理逻辑
---

# Agda佐恩引理

> 交流Q群: 893531731  
> 本文源码: [Zorn.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/CubicalExt/Logic/Zorn.lagda.md)  
> 高亮渲染: [Zorn.html](https://choukh.github.io/agda-flypitch/CubicalExt.Logic.Zorn.html)  
> 改编自: Coq [ZornsLemma.v](https://github.com/coq-community/zorns-lemma/blob/master/ZornsLemma.v)  

## 前言

佐恩引理是经典数学中最基础的定理之一. 然而, 作为直觉主义数学的前沿之一, 同伦类型论 (HoTT) 在经典领域的扩展并未获得太多研究关注. 本文旨在填补这一空白, 我们将在同伦类型论的框架下展示对佐恩引理这一经典定理的证明. 尽管本文的内容可以被视为 Agda 代码的注释, 我们仍然力求使其内容对于不熟悉 Agda 语言的读者也能理解其中的主要思路, 但前提是读者需要了解同伦类型论的基本概念.

我们工作在无公理的 cubical 环境中, 而选择公理将作为参数引入. 这里说的 cubical 指立方类型论 (cubical type theory), 它是同伦类型论的一种实现.

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module CubicalExt.Logic.Zorn where
```

首先, 我们需要导入 Cubical 标准库模块. 同伦类型论 (乃至其立方类型论实现) 以其对"相等"这一基础概念的复杂诠释而广为人知. 在某些情况下 (如单集的定义中), 我们将使用立方类型论的 `Id` 类型, 因其可以便捷地进行模式匹配. 然而, 在大部分情况下, 我们更倾向于使用路径 `Path` 类型.

```agda
open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Empty as ⊥ using (⊥; isProp⊥)
open import Cubical.Data.Sigma using (∃-syntax; ΣPathP; PathPΣ)
import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁; rec; rec2; map)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import Cubical.Relation.Binary
open BinaryRelation
```

本文在很大程度上依赖于 **命题截断 (propositional truncation)** 这一概念, 因此需要读者能对此有较为深入的理解. 我们 TODO

以下是我们按照标准库风格额外编写的前置模块. 这些模块主要涉及经典逻辑和集合论的基本概念. 我们预设读者对这些概念有深入的理解, 因此不会再逐一进行解释.

```agda
open import CubicalExt.Axiom.Choice
open import CubicalExt.Axiom.ExcludedMiddle
open import CubicalExt.Foundations.Powerset* hiding (U)
open import CubicalExt.Foundations.Function using (_∘_; _$_; it)
open import CubicalExt.Functions.Logic using (∥_∥ₚ; _∧_; _∨_; inl; inr; ∨-elimˡ; ∨-elimʳ)
```

如果在后续的内容中出现了以下列出的变量, 但没有提前进行声明, 请理解为它们已作为隐式参数被引入，并具备以下规定的类型.

```agda
private variable
  ℓ u r : Level
  U : Type ℓ
  A : 𝒫 U ℓ
```

其中 `Level` 是宇宙等级, `𝒫 U ℓ` 表示 `U` 的位于 `ℓ` 宇宙的幂集. 在后文中我们将假设排中律, 这将导致命题宇宙坍塌到一层. 从而幂集将不再有宇宙等级的区分, 使其更接近于传统意义上的幂集.

## 序理论

佐恩引理的表述需要序理论的基本概念. 我们将在本节中对这些概念进行简要的回顾. 给定类型 `U` 及其上的二元关系 `R`.

```agda
module Order {U : Type u} (R : Rel U U r) where
```

### 偏序

如果 `R` 取值到命题, 并且满足自反, 反对称和传递性, 则称 `R` 是偏序 (partial order).

```agda
  isPo : Type _
  isPo = isPropValued R ∧ isRefl R ∧ isAntisym R ∧ isTrans R
```

如果 `R` 是偏序且 `U` 是集合, 则称 `U` 为偏序集.

```agda
  isPoset : Type _
  isPoset = isSet U ∧ isPo
```

### 无界

我们又用中缀符号 `≤` 表示 `R` 关系.

```agda
  private _≤_ = R
```

我们说 `U` 在 `R` 关系下是无界的, 当且仅当从任意 `x : U` 都能得到一个 `y : U` 严格大于 `x`.

```agda
  unbound : Type _
  unbound = ∀ x → Σ[ y ∈ U ] x ≤ y ∧ ¬ x ≡ y
```

我们说 `U` 在 `R` 关系下是后继的, 当且仅当它是无界的, 且见证无界的那个 `y` 刚好比 `x` 大, 也就是说它们之间没有其他元素.

```agda
  successive : Type _
  successive = ∀ x → Σ[ y ∈ U ] x ≤ y ∧ (¬ x ≡ y) ∧ ∀ z → x ≤ z → z ≤ y → z ≡ x ∨ z ≡ y
```

### 最大元

对任意大于等于 `m` 的元素, 如果它其实都等于 `m`, 那么称 `m` 是 `U` 的最大元.

```agda
  maximum : U → Type _
  maximum m = ∀ x → m ≤ x → m ≡ x
```

注意无界与存在最大元是不相容的.

### 链

现在, 考虑 `U` 的子集 `A`, 如果其中的任意两个元素都可以比较大小, 我们就说 `A` 是链, 也叫 `U` 的全序子集.

```agda
  isChain : 𝒫 U ℓ → Type _
  isChain A = ∀ x y → x ∈ A → y ∈ A → x ≤ y ∨ y ≤ x
```

注意 `∨` 是和类型 `⊎` 的命题截断, 从而保证了"某某是链"是一个命题. 后面要用到这一性质.

```agda
  isPropIsChain : isProp (isChain A)
  isPropIsChain = isPropΠ2 λ _ _ → isPropΠ2 λ _ _ → squash₁
```

### 上界

给定 `A` 和 `ub : U`, 如果 `ub` 比 `A` 的任意元素都要大, 则称 `ub` 是 `A` 的上界. 注意上界不一定在 `A` 中.

```agda
  upperBound : 𝒫 U ℓ → U → Type _
  upperBound A ub = ∀ x → x ∈ A → x ≤ ub
```

由以上定义, "所有链都可以找到上界"表述如下.

```agda
  allChainHasUb = ∀ {ℓ} (A : 𝒫 U ℓ) → isChain A → Σ[ ub ∈ U ] upperBound A ub
```

### 上确界

给定 `A` 和 `sup : U`, 如果 `sup` 是 `A` 的最小上界, 则称 `sup` 是 `A` 的上确界. 注意上确界也不一定在 `A` 中.

```agda
  supremum : 𝒫 U ℓ → U → Type _
  supremum A sup = upperBound A sup ∧ ∀ ub → upperBound A ub → sup ≤ ub
```

由以上定义, "所有链都可以找到上确界"表述如下.

```agda
  allChainHasSup = ∀ {ℓ} (A : 𝒫 U ℓ) → isChain A → Σ[ sup ∈ U ] supremum A sup
```

### 佐恩引理的表述

经过以上的概念铺垫, 我们现在可以正式阐述佐恩引理. 佐恩引理是说: 对任意偏序集 `U`, 如果 `U` 中所有的链都能**找到**上界, 那么 `U` 中**存在**一个最大元.

```agda
  Zorn = isPoset → allChainHasUb → ∃[ m ∈ U ] maximum m
```

需要注意的是, 我们仅将 `Σ` 的命题截断 `∃` 称为*存在*, 而对于 `Σ`, 我们会用诸如*找到*, *取到*, *得到*等表述. 我们尽量避免使用 *有* 这种模糊的说法.

当然, 佐恩引理的表述可以进一步强化为"对任意偏序集 `U`, 如果 `U` 中所有的链都**存在**上确界, 那么 `U` 中**存在**一个最大元". 只需要用命题截断的 `rec`, 就可以证明前者蕴含后者. 然而, 我们习惯避免在前提中使用截断, 等到需要时再用 `rec` 得到截断版本.

佐恩引理的证明思路中反直觉的地方是我们并非直接考虑链本身, 而是考虑由所有链构成的集合在包含关系下构成的链.

## 链集的链

现在, 假设排中律, 并给定偏序 `≤`.

```agda
module Chain ⦃ em : ∀ {ℓ} → EM ℓ ⦄ {U : Type u} (_≤_ : Rel U U r) where
  open import CubicalExt.Logic.Classical
  open module ≤ = Order _≤_
```

我们把 `U` 的子集 `A` 配备上链条件所得到的类型 `Chain` 叫做链集.

```agda
  Chain : Type _
  Chain = Σ[ A ∈ 𝒫 U ℓ-zero ] ≤.isChain A
```

可以证明 `Chain` 是集合.

```agda
  _ : isSet Chain
  _ = isSetΣ (isSetΠ λ _ → isSetHProp) λ _ → isProp→isSet isPropIsChain
```

### 偏序

定义链集上的二元关系 `⪯` 为链之间的包含关系.

```agda
  _⪯_ : Rel Chain Chain u
  a ⪯ b = a .fst ⊆ b .fst
```

由于集合的包含关系是偏序, 所以 `⪯` 也是偏序.

```agda
  ⪯-prop : isPropValued _⪯_
  ⪯-prop _ _ = ⊆-isProp _ _

  ⪯-refl : isRefl _⪯_
  ⪯-refl = ⊆-refl ∘ fst

  ⪯-antisym : isAntisym _⪯_
  ⪯-antisym _ _ H₁ H₂ = ΣPathP $ ⊆-antisym _ _ H₁ H₂ , toPathP (≤.isPropIsChain _ _)

  ⪯-trans : isTrans _⪯_
  ⪯-trans _ _ _ H₁ H₂ x∈ = H₂ $ H₁ x∈

  open module ⪯ = Order _⪯_

  ⪯-po : ⪯.isPo
  ⪯-po = ⪯-prop , ⪯-refl , ⪯-antisym , ⪯-trans
```

现在我们有了两个偏序, 一个是 `U` 上的 `≤`, 一个是链集上的 `⪯`. 为避免混淆, 接下来我们会对相关概念加上 `≤` 或 `⪯` 前缀, 来指明该概念所涉及的偏序.

### 上确界

现在考虑链集的链. 注意, 尽管链集中的每个元素都是 ≤-链, 但这里我们说的是由链集中的元素组成的 ⪯-链.

对任意 ⪯-链 `A`, 我们可以找到其上确界, 只需取 `A` 中所有 ≤-链的并. 也就是说, 并作为一个集合, 其中的任意 `x`, 都需要存在一条 ≤-链 `a₁` 容纳它, 且 `a₁` 作为链集的一个元素 `a`, 必须在 `A` 中.

需要注意的是, `Chain` 的定义仅接受 `U` 的位于最低宇宙的子集, 为了使我们这里定义的并确实具有 `Chain` 类型, 需要将上述并 `Resize` 到最低宇宙. 由于我们假设了排中律, 这是可以做到的. 关于具体的方法, 读者可以点击代码中的 `Resize` 查看其定义.

```agda
  sup : (A : 𝒫 Chain ℓ) → ⪯.isChain A → Chain
  sup A isChainA = Resize ∘ (λ x → (∃[ a@(a₁ , _ ) ∈ Chain ] x ∈ a₁ ∧ a ∈ A) , squash₁) ,
```

为了保证并具有 `Chain` 类型, 我们还需要说明它是一个 ≤-链. 根据定义, 并中的任意元素都在某个 ≤-链中, 且该 ≤-链又在 `A` 中. 由于 `A` 是 ⪯-链, 并中的任意两个元素都可以找到一个共同的 ≤-链容纳它, 因此它们可以比较大小, 这也就说明了并同样是 ≤-链.

```agda
    λ x y x∈ y∈ → rec2 squash₁
      (λ{ (a , x∈a , a∈A) (b , y∈b , b∈A) → rec squash₁
        (λ{ (⊎.inl a⪯b) → b .snd x y (a⪯b x∈a) y∈b
          ; (⊎.inr b⪯a) → a .snd x y x∈a (b⪯a y∈b) })
        (isChainA a b a∈A b∈A)})
      (unresize x∈) (unresize y∈)
```

下面的代码证明上面说的并确实是上确界. 由集合论知识, 集族的并显然是 ⊆-序的上确界. 这里不再赘述.

```agda
  suphood : (A : 𝒫 Chain ℓ) (isChainA : ⪯.isChain A) → ⪯.supremum A (sup A isChainA)
  suphood A isChainA = (λ { a a∈A x∈a₁ → resize ∣ a , x∈a₁ , a∈A ∣₁ }) ,
    λ ub ubhood x∈sup → rec (∈-isProp (ub .fst) _)
      (λ{ (a , x∈a₁ , a∈A) → ubhood a a∈A x∈a₁ })
      (unresize x∈sup)
```

至此, 我们证明了链集中的任意链都能找到上确界.

```
  ⪯-allChainHasSup : ⪯.allChainHasSup
  ⪯-allChainHasSup A isChainA = sup A isChainA , suphood A isChainA
```

### 后继性

接下来我们将证明一个关键的引理. 它的前两个前提与佐恩引理相同, 第三个前提则是对佐恩引理结论的否定, 我们将在最后一节使用选择公理来证明这一点. 最后, 我们将采用反证法来证明佐恩引理, 只需将下面引理的结论与上一小节所证明的事实结合起来找到矛盾即可.

先回到该引理的证明, 要找到给定的 `a : Chain` 的后继. 具体地, 有五个子目标: 给出后继 `a'`; 说明它小于等于 `a`; 说明它不等于 `a`; 说明 `a` 与 `a'` 之间没有其他元素.

```agda
  ⪯-successvie : ≤.isPoset → ≤.allChainHasUb → ≤.unbound → ⪯.successive
  ⪯-successvie (Uset , ≤-po) hasUb unbnd a@(A , isChainA) = a' , resize ∘ inl , a≢a' , noMid where
```

由前提, `≤` 自反, 反对称且传递.

```agda
    ≤-refl    = ≤-po .snd .fst
    ≤-antisym = ≤-po .snd .snd .fst
    ≤-trans   = ≤-po .snd .snd .snd
```

将 `a` 分解为 `U` 的子集 `A` 以及它是 ≤-链的证据 `isChainA`. 由于 `A` 是 ≤-链, 由前提, 它有上界 `ub`. 又 `U` ≤-无界, 所以有比 `ub` 更大的 `ub'`.

```agda
    ub        = hasUb A isChainA .fst
    ubhood    = hasUb A isChainA .snd
    ub'       = unbnd ub .fst
    ub≤       = unbnd ub .snd .fst
    ub≢       = unbnd ub .snd. snd
```

现在, 取 `A` 中元素与 `ub` 所组成的集合, 记作 `A ⨭ ub`, 命名为 `A'`, 并 `Resize` 到最低宇宙. 注意, 这里的 `⨭` 运算要求全集 `U` 是集合.

```agda
    open SetBased Uset using (_⨭_)
    A' = Resize ∘ (A ⨭ ub')
```

由于 `ub'` 比 `A` 中元素都大, 所以把它加进 `A` 后可以与 `A` 中所有元素比出大小, 所以 `A'` 也是 ≤-链.

```agda
    isChainA' : ≤.isChain A'
    isChainA' x y x∈ y∈ = rec2 squash₁
      (λ{ (⊎.inl x∈A)    (⊎.inl y∈A)    → isChainA x y x∈A y∈A
        ; (⊎.inl x∈A)    (⊎.inr reflId) → inl $ ≤-trans x ub y (ubhood x x∈A) ub≤
        ; (⊎.inr reflId) (⊎.inl y∈A)    → inr $ ≤-trans y ub x (ubhood y y∈A) ub≤
        ; (⊎.inr reflId) (⊎.inr reflId) → inl $ ≤-refl x })
      (unresize x∈) (unresize y∈)
```

`A'` 配备上它是 ≤-链的证据 `isChainA'` 得到 `a' : Chain`. 我们宣称 `a'` 就是所需后继. 显然 `A ⊆ A'`, 所以 `a ⪯ a'`.

```agda
    a' = A' , isChainA'
```

由于 `ub'` 比 `A` 中所有元素都大, 所以它不在 `A` 中, 所以 `A` 与 `A'` 不同, 这就说明了 `a` 与 `a'` 不同.

```agda
    a≢a' : ¬ a ≡ a'
    a≢a' eq = let eq = PathPΣ eq .fst in
      ub≢ $ ≤-antisym ub ub' ub≤ $ ubhood ub' $
      subst (ub' ∈_) (sym eq) $ resize $ inr reflId
```

最后, 我们要说明 `a` 与 `a'` 之间没有其他元素. 给定 `b` 在 `a` 与 `a'` 之间, 我们说明 `b` 要么等于 `a`, 要么等于 `a'`. 将 `b` 分解为 `U` 的子集 `B` 以及它是 ≤-链的证据 `isChainB`. 现在, 用排中律讨论 `ub'` 是否在 `B` 中.

```agda
    noMid : ∀ b → a ⪯ b → b ⪯ a' → b ≡ a ∨ b ≡ a'
    noMid b@(B , isChainB) A⊆B B⊆A' with em ⦃ ∈-isProp B ub' _ _ ⦄
```

- 若 `ub' ∈ B`, 我们证 `b ≡ a'`, 只需证 `B ≡ A'`, 至于它们的 `isChain` 证据, 由于是命题, 必然相等. 我们用 `⊆` 的反自反性证明 `B ≡ A'`. 已知 `B ⊆ A'` 是前提, 只需证 `A' ⊆ B`. `A'` 中的元素要么是 `A` 中的元素, 要么是 `ub'`, 而 `A ⊆ B`, `ub' ∈ B`, 所以 `A' ⊆ B`.

```agda
    ... | yes ub'∈B = inr $ ΣPathP $ ⊆-antisym B A' B⊆A' A'⊆B , toPathP (≤.isPropIsChain _ isChainA')
      where A'⊆B : A' ⊆ B
            A'⊆B x∈A' = rec (∈-isProp B _)
              (λ{ (⊎.inl x∈A)    → A⊆B x∈A
                ; (⊎.inr reflId) → ub'∈B })
              (unresize x∈A')
```

- 若 `ub' ∉ B`, 我们证 `b ≡ a`, 只需证 `B ≡ A`. 同样用 `⊆` 的反自反性, 已知 `A ⊆ B` 是前提, 只需证 `B ⊆ A`. 由于 `B ⊆ A'`, `A'` 只比 `A` 多了一个元素 `ub'`, 而 `ub' ∉ B`, 所以 `B ⊆ A`.

```agda
    ... | no  ub'∉B = inl $ ΣPathP $ ⊆-antisym B A B⊆A A⊆B , toPathP (≤.isPropIsChain _ isChainA)
      where B⊆A : B ⊆ A
            B⊆A x∈B = rec (∈-isProp A _)
              (λ{ (⊎.inl x∈A)    → x∈A
                ; (⊎.inr reflId) → ⊥.rec $ ub'∉B x∈B })
              (unresize (B⊆A' x∈B))
```

至此, 我们证明了某个序在一定条件下同时满足 "任意链都能取上确界" 与 "任意元素都取后继". 我们将证明, 这实际上是矛盾的.

## 构造矛盾

假设排中律, 给定偏序 `≤`, 假设其下任意链都能取上确界, 且任意元素都取后继.

```agda
module Contra ⦃ em : ∀ {ℓ} → EM ℓ ⦄ {U : Type u} {_≤_ : Rel U U r}
  (≤-po : Order.isPo _≤_) (hasSup : Order.allChainHasSup _≤_) (hasSuc : Order.successive _≤_) where
  open import CubicalExt.Logic.Classical
  open Order _≤_
```

由前提, `≤` 取值到命题, 自反, 反对称且传递.

```agda
  private
    ≤-prop    = ≤-po .fst
    ≤-refl    = ≤-po .snd .fst
    ≤-antisym = ≤-po .snd .snd .fst
    ≤-trans   = ≤-po .snd .snd .snd
    instance
      ≤-propImplicit : {x y : U} → isPropImplicit (x ≤ y)
      ≤-propImplicit = ≤-prop _ _ _ _
```

以下构造在集合论中用序数上的超限递归实现, 在类型论中我们用归纳类型实现. 我们将定义 `U` 的一个谓词, 命名为 `Tower`. 我们会把它截断为 `U` 的子集, 命名为 `TowerSetℓ`, 然后再 `Resize` 到最低宇宙, 命名为 `TowerSet`.

```agda
  data Tower : U → Type (ℓ-max (ℓ-suc ℓ-zero) (ℓ-max u r))
  TowerSetℓ : 𝒫 U _
  TowerSetℓ x = ∥ Tower x ∥ₚ
  TowerSet : 𝒫 U ℓ-zero
  TowerSet = Resize ∘ TowerSetℓ
```

现在归纳定义谓词 `Tower`:
- 对任意 `x` 满足 `Tower`, `x` 的后继也满足 `Tower`.
- 对任意 `U` 的子集 `A`, 如果它包含于 `TowerSetℓ`, 且是链, 那么它的上确界也满足 `Tower`.

```agda
  data Tower where
    includeSuc : (x : U) → Tower x → Tower (hasSuc x .fst)
    includeSup : (A : 𝒫 U ℓ-zero) → (A ⊆ TowerSetℓ) → (isChainA : isChain A) →
      Tower (hasSup A isChainA .fst)
```

注意 `TowerSetℓ` 在 `Tower` 定义完成之前就被使用了. Agda 允许这种写法, 只要满足一定条件, 这里不展开.

接下来, 我们将证明任意两个满足 `Tower` 的元素都可以比较大小, 命名为 `isChainTower`. 一旦其证明完成, 就可以立即证明 `TowerSetℓ` 是链, 乃至 `TowerSet` 是链.

```agda
  isChainTower : ∀ x y → Tower x → Tower y → x ≤ y ∨ y ≤ x
  isChainTowerSetℓ : isChain TowerSetℓ
  isChainTowerSetℓ x y = rec2 squash₁ (isChainTower x y)
  isChainTowerSet : isChain TowerSet
  isChainTowerSet x y x∈ y∈ = isChainTowerSetℓ x y (unresize x∈) (unresize y∈)
```

该命题的证明需要复杂的递归, 为了使结构更清晰, 我们写成互递归 (mutual recursion).

我们先证明结论的一个弱化版, 作为中间引理, 命名为 `almostChain`, 其证明会递归调用 `isChainTower`. 随后, 我们完成 `isChainTower` 的证明, 其中会递归调用 `almostChain`. Agda 会保证循环论证不会通过.

现在, 给定满足 `Tower` 条件的 `y`. 将 `y` 的后继记作 `y'`.

```agda
  module _ y (y∈ : Tower y) where
    private y' = hasSuc y .fst
```

`almostChain` 是说任意满足 `Tower` 条件的 `x` 要么小于等于 `y` 要么大于等于 `y'`.

```agda
    almostChain : ∀ x → Tower x → x ≤ y ∨ y' ≤ x
```



```agda
    almostChain' : ∀ x → x ∈ TowerSetℓ → x ≤ y ∨ y' ≤ x
    almostChain' x ∣ x∈ ∣₁ = almostChain x x∈
    almostChain' x (squash₁ x∈₁ x∈₂ i) = squash₁ (almostChain' x x∈₁) (almostChain' x x∈₂) i
```

```agda
    almostChain x' (includeSuc x x∈) with isChainTower x' y (includeSuc x x∈) y∈
    ... | IH = rec2 squash₁
      (λ{ (⊎.inl x≤y) (⊎.inl x'≤y) → inl x'≤y
        ; (⊎.inl x≤y) (⊎.inr y≤x') → rec squash₁
          (λ{ (⊎.inl y≡x)  → inr $ subst (λ x → _ ≤ hasSuc x .fst) y≡x (≤-refl _)
            ; (⊎.inr y≡x') → inl $ subst (λ x → _ ≤ x) (sym y≡x') (≤-refl _) })
          (noMid y x≤y y≤x')
        ; (⊎.inr y'≤x) _ → inr $ ≤-trans y' x x' y'≤x x≤x' })
      (almostChain x x∈) IH where
      x≤x'  = hasSuc x .snd .fst
      noMid = hasSuc x .snd .snd .snd
```

```agda
    almostChain x (includeSup A A⊆ isChainA) with em {P = upperBound A y}
    ... | yes p = inl $ hasSup A isChainA .snd .snd y p
    ... | no ¬p = inr $ rec (≤-prop _ _)
      (λ{ (z , ¬ub) → let (z∈A , ¬z≤y) = ¬→→∧ (z ∈ A) ⦃ ∈-isProp _ _ _ _ ⦄ (z ≤ y) ¬ub in
        ≤-trans y' z x
          (∨-elimʳ (≤-prop _ _) (almostChain' z (A⊆ z∈A)) ¬z≤y)
          (hasSup A isChainA .snd .fst z z∈A) })
      (¬∀→∃¬ ¬p)
```

```agda
  isChainTower' : ∀ x y → Tower x → y ∈ TowerSetℓ → x ≤ y ∨ y ≤ x
  isChainTower' x y x∈ ∣ y∈ ∣₁ = isChainTower x y x∈ y∈
  isChainTower' x y x∈ (squash₁ y∈₁ y∈₂ i) = squash₁ (isChainTower' x y x∈ y∈₁) (isChainTower' x y x∈ y∈₂) i
```

```agda
  isChainTower x y' x∈ (includeSuc y y∈) = rec squash₁
    (λ{ (⊎.inl x≤y)  → inl (≤-trans x y y' x≤y y≤y')
      ; (⊎.inr y'≤x) → inr y'≤x })
    (almostChain y y∈ x x∈) where y≤y' = hasSuc y .snd .fst
```

```agda
  isChainTower x y x∈ (includeSup A A⊆ isChainA) with em {P = upperBound A x}
  ... | yes p = inr $ hasSup A isChainA .snd .snd x p
  ... | no ¬p = inl $ rec (≤-prop _ _)
    (λ{ (z , ¬ub) → let (z∈A , ¬z≤x) = ¬→→∧ (z ∈ A) ⦃ ∈-isProp _ _ _ _ ⦄ (z ≤ x) ¬ub in
      ≤-trans x z y
        (∨-elimˡ (≤-prop _ _) (isChainTower' x z x∈ (A⊆ z∈A)) ¬z≤x)
        (hasSup A isChainA .snd .fst z z∈A) })
    (¬∀→∃¬ ¬p)
```

```agda
  Σsup = hasSup TowerSet isChainTowerSet
  sup = Σsup .fst
  ubhood = Σsup .snd .fst

  Σsuc = hasSuc sup
  suc = Σsuc .fst
  sup≤suc = Σsuc .snd .fst
  sup≢suc = Σsuc .snd .snd .fst

  sup∈Tower : Tower sup
  sup∈Tower = includeSup TowerSet unresize isChainTowerSet

  suc∈TowerSet : suc ∈ TowerSet
  suc∈TowerSet = resize $ map (includeSuc sup) ∣ sup∈Tower ∣₁

  suc≤sup : suc ≤ sup
  suc≤sup = ubhood suc suc∈TowerSet

  false : ⊥
  false = sup≢suc $ ≤-antisym _ _ sup≤suc suc≤sup
```

## 证明

```agda
module _ (ac : ∀ {ℓ ℓ'} → AC ℓ ℓ') {U : Type u} {_≤_ : Rel U U r} where
  open import CubicalExt.Logic.ClassicalChoice ac
  open Order _≤_

  noMaximum→unbound : isPoset → ¬ (∃[ m ∈ U ] maximum m) → ∥ unbound ∥₁
  noMaximum→unbound ≤-poset noMax = ac Uset Σset H where
    Uset = ≤-poset .fst
    ≤-prop = ≤-poset .snd .fst
    instance
      ≤-propImplicit : {x y : U} → isPropImplicit (x ≤ y)
      ≤-propImplicit = ≤-prop _ _ _ _
      ≡-propImplicit : {x y : U} → isPropImplicit (x ≡ y)
      ≡-propImplicit = Uset _ _ _ _
    H₀ : ∀ x → ∃[ x' ∈ U ] ¬ (x ≤ x' → x ≡ x')
    H₀ x = ¬∀→∃¬ λ H → noMax ∣ x , H ∣₁
    H : ∀ x → ∃[ x' ∈ U ] (x ≤ x' ∧ ¬ x ≡ x')
    H x = rec squash₁ (λ { (x' , H) → ∣ x' , ¬→→∧ (x ≤ x') (x ≡ x') H ∣₁ }) (H₀ x)
    Σset : ∀ x → isSet (Σ[ x' ∈ U ] (x ≤ x' ∧ ¬ x ≡ x'))
    Σset = λ _ → isSetΣ Uset λ _ → isProp→isSet $ isPropΣ (≤-prop _ _) λ _ → isPropΠ λ _ → isProp⊥

  zorn : Zorn
  zorn ≤-poset hasUb = byContra λ noMax → rec isProp⊥
    (Contra.false ⪯-po ⪯-allChainHasSup ∘ ⪯-successvie ≤-poset hasUb)
    (noMaximum→unbound ≤-poset noMax)
    where open Chain _≤_
```
