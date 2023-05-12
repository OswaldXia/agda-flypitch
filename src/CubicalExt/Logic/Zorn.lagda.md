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

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module CubicalExt.Logic.Zorn where
```

```agda
open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Empty as ⊥ using (⊥; isProp⊥)
open import Cubical.Data.Sigma renaming (_×_ to infixr 3 _×_)
import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁; rec; rec2; map)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import Cubical.Relation.Binary
open BinaryRelation
```

```agda
open import CubicalExt.Axiom.Choice
open import CubicalExt.Axiom.ExcludedMiddle
open import CubicalExt.Foundations.Powerset* hiding (U)
open import CubicalExt.Foundations.Function using (_∘_; _$_; it)
open import CubicalExt.Functions.Logic using (∥_∥ₚ; inl; inr; _∨_; _∧_; ∨-elimˡ; ∨-elimʳ)
```

```agda
private variable
  ℓ u r : Level
  U : Type ℓ
  A : 𝒫 U ℓ
```

## 序理论

```agda
module Order {U : Type u} (R : Rel U U r) where
```

偏序

```agda
  isPo : Type _
  isPo = isPropValued R × isRefl R × isAntisym R × isTrans R

  isPoset : Type _
  isPoset = isSet U × isPo
```

无界

```agda
  private _≤_ = R

  unbound : Type _
  unbound = ∀ x → Σ[ y ∈ _ ] x ≤ y × (¬ x ≡ y)
```

后继的

```agda
  successive : Type _
  successive = ∀ x → Σ[ y ∈ _ ] x ≤ y × (¬ x ≡ y) × ∀ z → x ≤ z → z ≤ y → z ≡ x ∨ z ≡ y
```

考虑 `U` 的子集 `𝒫 U ℓ`

链

```agda
  isChain : 𝒫 U ℓ → Type _
  isChain A = ∀ x y → x ∈ A → y ∈ A → x ≤ y ∨ y ≤ x
```

"某某是链"是命题

```agda
  isPropIsChain : isProp (isChain A)
  isPropIsChain = isPropΠ2 λ _ _ → isPropΠ2 λ _ _ → squash₁
```

上界

```agda
  upperBound : 𝒫 U ℓ → U → Type _
  upperBound A ub = ∀ x → x ∈ A → x ≤ ub
```

所有链都有上界

```agda
  allChainHasUb = ∀ {ℓ} (A : 𝒫 U ℓ) → isChain A → Σ[ ub ∈ U ] upperBound A ub
```

最大元

```agda
  maximum : U → Type _
  maximum m = ∀ x → m ≤ x → m ≡ x
```

上确界

```agda
  supremum : 𝒫 U ℓ → U → Type _
  supremum A sup = upperBound A sup × ∀ ub → upperBound A ub → sup ≤ ub
```

所有链都有上确界

```agda
  allChainHasSup = ∀ {ℓ} (A : 𝒫 U ℓ) → isChain A → Σ[ sup ∈ U ] supremum A sup
```

给定偏序集 (`U`, `≤`), 如果 `U` 中的所有链都有上界, 那么 (`U`, `≤`) 中存在一个最大元.

```agda
  Zorn = isPoset → allChainHasUb → ∃[ m ∈ U ] maximum m
```

## 链的链

给定偏序 (`U`, `≤`)

```agda
module Chain ⦃ em : ∀ {ℓ} → EM ℓ ⦄ {U : Type u} (_≤_ : Rel U U r) where
  open import CubicalExt.Logic.Classical
  open module ≤ = Order _≤_
```

链的链

```agda
  Chain = Σ[ S ∈ 𝒫 U ℓ-zero ] ≤.isChain S
```

### 偏序

链的链上的偏序

```agda
  _⪯_ : Rel Chain Chain u
  a ⪯ b = a .fst ⊆ b .fst
```

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

### 上确界

```agda
  sup : (A : 𝒫 Chain ℓ) → ⪯.isChain A → Chain
  sup A isChainA = Resize ∘ (λ x → (∃[ a ∈ Chain ] x ∈ a .fst × a ∈ A) , squash₁) ,
    λ x y x∈ y∈ → rec2 squash₁
      (λ{ (a , x∈a , a∈A) (b , y∈b , b∈A) → rec squash₁
        (λ{ (⊎.inl a⪯b) → b .snd x y (a⪯b x∈a) y∈b
          ; (⊎.inr b⪯a) → a .snd x y x∈a (b⪯a y∈b) })
        (isChainA a b a∈A b∈A)})
      (unresize x∈) (unresize y∈)

  suphood : (A : 𝒫 Chain ℓ) (isChainA : ⪯.isChain A) → ⪯.supremum A (sup A isChainA)
  suphood A isChainA = (λ { a a∈A x∈a₁ → resize ∣ a , x∈a₁ , a∈A ∣₁ }) ,
    λ ub ubhood x∈sup → rec (∈-isProp (ub .fst) _)
      (λ{ (a , x∈a₁ , a∈A) → ubhood a a∈A x∈a₁ })
      (unresize x∈sup)

  ⪯-allChainHasSup : ⪯.allChainHasSup
  ⪯-allChainHasSup A isChainA = sup A isChainA , suphood A isChainA
```

### 后继性

```agda
  ⪯-successvie : ≤.isPoset → ≤.allChainHasUb → ≤.unbound → ⪯.successive
  ⪯-successvie (Uset , ≤-po) hasUb unbnd a@(A , isChainA) = a' , resize ∘ inl , a≢a' , noMid where

    ≤-refl    = ≤-po .snd .fst
    ≤-antisym = ≤-po .snd .snd .fst
    ≤-trans   = ≤-po .snd .snd .snd

    ub        = hasUb A isChainA .fst
    ubhood    = hasUb A isChainA .snd
    ub'       = unbnd ub .fst
    ub≤       = unbnd ub .snd .fst
    ub≢       = unbnd ub .snd. snd

    open SetBased Uset using (_⨭_)
    A' = Resize ∘ (A ⨭ ub')

    isChainA' : ≤.isChain A'
    isChainA' x y x∈ y∈ = rec2 squash₁
      (λ{ (⊎.inl x∈A)    (⊎.inl y∈A)    → isChainA x y x∈A y∈A
        ; (⊎.inl x∈A)    (⊎.inr reflId) → inl $ ≤-trans x ub y (ubhood x x∈A) ub≤
        ; (⊎.inr reflId) (⊎.inl y∈A)    → inr $ ≤-trans y ub x (ubhood y y∈A) ub≤
        ; (⊎.inr reflId) (⊎.inr reflId) → inl $ ≤-refl x })
      (unresize x∈) (unresize y∈)

    a' = A' , isChainA'
    a≢a' : ¬ a ≡ a'
    a≢a' eq = let eq = PathPΣ eq .fst in
      ub≢ $ ≤-antisym ub ub' ub≤ $ ubhood ub' $
      subst (ub' ∈_) (sym eq) $ resize $ inr reflId

    noMid : ∀ b → a ⪯ b → b ⪯ a' → b ≡ a ∨ b ≡ a'
    noMid b@(B , isChainB) A⊆B B⊆A' with em ⦃ ∈-isProp B ub' _ _ ⦄
    ... | yes ub'∈B = inr $ ΣPathP $ ⊆-antisym B A' B⊆A' A'⊆B , toPathP (≤.isPropIsChain _ isChainA')
      where A'⊆B : A' ⊆ B
            A'⊆B x∈A' = rec (∈-isProp B _)
              (λ{ (⊎.inl x∈A)    → A⊆B x∈A
                ; (⊎.inr reflId) → ub'∈B })
              (unresize x∈A')
    ... | no  ub'∉B = inl $ ΣPathP $ ⊆-antisym B A B⊆A A⊆B , toPathP (≤.isPropIsChain _ isChainA)
      where B⊆A : B ⊆ A
            B⊆A x∈B = rec (∈-isProp A _)
              (λ{ (⊎.inl x∈A)    → x∈A
                ; (⊎.inr reflId) → ⊥.rec $ ub'∉B x∈B })
              (unresize (B⊆A' x∈B))
```

## 构造矛盾

```agda
module Contra ⦃ em : ∀ {ℓ} → EM ℓ ⦄ {U : Type u} {_≤_ : Rel U U r}
  (≤-po : Order.isPo _≤_) (hasSup : Order.allChainHasSup _≤_) (hasSuc : Order.successive _≤_) where
  open import CubicalExt.Logic.Classical
  open Order _≤_

  private
    ≤-prop    = ≤-po .fst
    ≤-refl    = ≤-po .snd .fst
    ≤-antisym = ≤-po .snd .snd .fst
    ≤-trans   = ≤-po .snd .snd .snd
    variable
      x y : U
    instance
      ≤-propImplicit : isPropImplicit (x ≤ y)
      ≤-propImplicit = ≤-prop _ _ _ _

  data Tower : U → Type (ℓ-max (ℓ-suc ℓ-zero) (ℓ-max u r))
  TowerSetℓ : 𝒫 U _
  TowerSetℓ x = ∥ Tower x ∥ₚ
  TowerSet : 𝒫 U ℓ-zero
  TowerSet = Resize ∘ TowerSetℓ

  data Tower where
    includeSuc : (x : U) → Tower x → Tower (hasSuc x .fst)
    includeSup : (A : 𝒫 U ℓ-zero) → (A ⊆ TowerSetℓ) → (isChainA : isChain A) →
      Tower (hasSup A isChainA .fst)

  isChainTower : ∀ x y → Tower x → Tower y → x ≤ y ∨ y ≤ x
  isChainTowerSetℓ : isChain TowerSetℓ
  isChainTowerSetℓ x y = rec2 squash₁ (isChainTower x y)
  isChainTowerSet : isChain TowerSet
  isChainTowerSet x y x∈ y∈ = isChainTowerSetℓ x y (unresize x∈) (unresize y∈)

  isChainTower' : ∀ x y → Tower x → y ∈ TowerSetℓ → x ≤ y ∨ y ≤ x
  isChainTower' x y x∈ ∣ y∈ ∣₁ = isChainTower x y x∈ y∈
  isChainTower' x y x∈ (squash₁ y∈₁ y∈₂ i) = squash₁ (isChainTower' x y x∈ y∈₁) (isChainTower' x y x∈ y∈₂) i

  module _ y (y∈ : Tower y) where
    private y' = hasSuc y .fst
    almostChain : ∀ x → Tower x → x ≤ y ∨ y' ≤ x
    almostChain' : ∀ x → x ∈ TowerSetℓ → x ≤ y ∨ y' ≤ x
    almostChain' x ∣ x∈ ∣₁ = almostChain x x∈
    almostChain' x (squash₁ x∈₁ x∈₂ i) = squash₁ (almostChain' x x∈₁) (almostChain' x x∈₂) i

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

    almostChain x (includeSup A A⊆ isChainA) with em {P = upperBound A y}
    ... | yes p = inl $ hasSup A isChainA .snd .snd y p
    ... | no ¬p = inr $ rec (≤-prop _ _)
      (λ{ (z , ¬ub) → let (z∈A , ¬z≤y) = ¬→→∧ (z ∈ A) ⦃ ∈-isProp _ _ _ _ ⦄ (z ≤ y) ¬ub in
        ≤-trans y' z x
          (∨-elimʳ (≤-prop _ _) (almostChain' z (A⊆ z∈A)) ¬z≤y)
          (hasSup A isChainA .snd .fst z z∈A) })
      (¬∀→∃¬ ¬p)

  isChainTower x y' x∈ (includeSuc y y∈) = rec squash₁
    (λ{ (⊎.inl x≤y)  → inl (≤-trans x y y' x≤y y≤y')
      ; (⊎.inr y'≤x) → inr y'≤x })
    (almostChain y y∈ x x∈) where y≤y' = hasSuc y .snd .fst

  isChainTower x y x∈ (includeSup A A⊆ isChainA) with em {P = upperBound A x}
  ... | yes p = inr $ hasSup A isChainA .snd .snd x p
  ... | no ¬p = inl $ rec (≤-prop _ _)
    (λ{ (z , ¬ub) → let (z∈A , ¬z≤x) = ¬→→∧ (z ∈ A) ⦃ ∈-isProp _ _ _ _ ⦄ (z ≤ x) ¬ub in
      ≤-trans x z y
        (∨-elimˡ (≤-prop _ _) (isChainTower' x z x∈ (A⊆ z∈A)) ¬z≤x)
        (hasSup A isChainA .snd .fst z z∈A) })
    (¬∀→∃¬ ¬p)

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

  noMaximum→unbound : isPoset → ¬ (∃[ m ∈ U ] maximum m) → unbound
  noMaximum→unbound ≤-poset noMax = {! H₁  !} where
    --ac Uset (λ x → isSetΣ Uset (λ _ → {!   !})) H₁ where
    Uset = ≤-poset .fst
    ≤-po = ≤-poset .snd .fst
    instance
      ≤-prop : ∀ {x y} → isPropImplicit (x ≤ y)
      ≤-prop = ≤-po _ _ _ _
      ≡-prop : ∀ {x y} → isPropImplicit (x ≡ y)
      ≡-prop = Uset _ _ _ _
    H₀ : ∀ x → ∃[ x' ∈ U ] ¬ (x ≤ x' → x ≡ x')
    H₀ x = ¬∀→∃¬ λ H → noMax ∣ x , H ∣₁
    H₁ : ∀ x → ∃[ x' ∈ U ] (x ≤ x' ∧ ¬ x ≡ x')
    H₁ x = rec squash₁ (λ { (x' , H) → ∣ x' , ¬→→∧ (x ≤ x') (x ≡ x') H ∣₁ }) (H₀ x)

  zorn : Zorn
  zorn ≤-poset hasUb = byContra λ noMax →
    --rec isProp⊥
    --(Contra.false ⪯-po ⪯-allChainHasSup ∘ ⪯-successvie ≤-poset hasUb)
    Contra.false ⪯-po ⪯-allChainHasSup $ ⪯-successvie ≤-poset hasUb (noMaximum→unbound {!   !} noMax) --(noMaximum→unbound ≤-poset noMax)
    where open Chain _≤_
```
