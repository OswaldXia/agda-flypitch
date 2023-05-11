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
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (∃-syntax; ΣPathP) renaming (_×_ to infixr 3 _×_)
import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec; rec2; map)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import Cubical.Relation.Binary
open BinaryRelation
```

```agda
open import CubicalExt.Axiom.ExcludedMiddle
open import CubicalExt.Foundations.Powerset*
  using (𝒫; lift𝒫; _∈_; _⊆_; ∈-isProp; ⊆-isProp; ⊆-refl; ⊆-antisym; ⊆-trans)
open import CubicalExt.Foundations.Function using (_∘_; _$_; it)
open import CubicalExt.Functions.Logic using (∥_∥ₚ; inl; inr; _∨_; _∧_; ∨-elimˡ; ∨-elimʳ)
```

```agda
private variable
  ℓ u r : Level
  U : Type ℓ
  A : 𝒫 U ℓ
  _≤_ : Rel U U ℓ
```

## 定义

偏序

```agda
isPo : Rel U U ℓ → Type _
isPo R = isPropValued R × isRefl R × isAntisym R × isTrans R

isPoset : Rel U U ℓ → Type _
isPoset {_} {U} R = isSet U × isPo R
```

预序

```agda
isPro : Rel U U ℓ → Type _
isPro R = isPropValued R × isRefl R × isTrans R

isProset : Rel U U ℓ → Type _
isProset {_} {U} R = isSet U × isPro R
```

偏序是预序

```agda
isPo→isPro : isPo _≤_ → isPro _≤_
isPo→isPro (isProp , isRefl , isAntisym , isTrans) = (isProp , isRefl , isTrans)
```

无界

```agda
unbound : Rel U U ℓ → Type _
unbound _≤_ = ∀ x → Σ[ y ∈ _ ] x ≤ y × (¬ x ≡ y)
```

后继的

```agda
successive : Rel U U ℓ → Type _
successive _≤_ = ∀ x → Σ[ y ∈ _ ] x ≤ y × (¬ x ≡ y) × ∀ z → x ≤ z → z ≤ y → z ≡ x ∨ z ≡ y
```

考虑 `U` 的子集 `𝒫 U ℓ`

```agda
module Def {U : Type u} (_≤_ : Rel U U r) where
```

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
  AllChainHasUb = ∀ {ℓ} (A : 𝒫 U ℓ) → isChain A → Σ[ ub ∈ U ] upperBound A ub
```

最大元

```agda
  maximum : U → Type _
  maximum m = ∀ x → m ≤ x → x ≡ m
```

给定偏序集 (`U`, `≤`), 如果 `U` 中的所有链都有上界, 那么 (`U`, `≤`) 中存在一个最大元.

```agda
  Zorn = isPoset _≤_ → AllChainHasUb → ∃[ m ∈ U ] maximum m
```

上确界

```agda
  -- least upper bound
  supremum : 𝒫 U ℓ → U → Type _
  supremum A sup = upperBound A sup × ∀ ub → upperBound A ub → sup ≤ ub
```

所有链都有上确界

```agda
  AllChainHasSup = ∀ {ℓ} (A : 𝒫 U ℓ) → isChain A → Σ[ sup ∈ U ] supremum A sup
```

## 链的链

给定偏序 (`U`, `≤`)

```agda
module Chain ⦃ em : ∀ {ℓ} → EM ℓ ⦄ {U : Type u} {_≤_ : Rel U U r}
  (≤-po : isPo _≤_) where
  open import CubicalExt.Logic.Classical
```

链的链

```agda
  Chain = Σ[ S ∈ 𝒫 U ℓ-zero ] isChain S
    where open Def _≤_
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
  ⪯-antisym _ _ H₁ H₂ = ΣPathP $ ⊆-antisym _ _ H₁ H₂ , toPathP (isPropIsChain _ _)
    where open Def _≤_

  ⪯-trans : isTrans _⪯_
  ⪯-trans _ _ _ H₁ H₂ x∈ = H₂ $ H₁ x∈

  ⪯-po : isPo _⪯_
  ⪯-po = ⪯-prop , ⪯-refl , ⪯-antisym , ⪯-trans
```

### 上确界

```agda
  open Def _⪯_

  sup : (A : 𝒫 Chain ℓ) → isChain A → Chain
  sup A isChainA = Resize ∘ (λ x → (∃[ a ∈ Chain ] x ∈ a .fst × a ∈ A) , squash₁) ,
    λ x y x∈ y∈ → rec2 squash₁
      (λ { (a , x∈a , a∈A) (b , y∈b , b∈A) → rec squash₁
        (λ { (⊎.inl a⪯b) → b .snd x y (a⪯b x∈a) y∈b
           ; (⊎.inr b⪯a) → a .snd x y x∈a (b⪯a y∈b) })
        (isChainA a b a∈A b∈A)})
      (unresize x∈) (unresize y∈)

  suphood : (A : 𝒫 Chain ℓ) (isChainA : isChain A) → supremum A (sup A isChainA)
  suphood A isChainA = (λ { a a∈A x∈a₁ → resize ∣ a , x∈a₁ , a∈A ∣₁ }) ,
    λ ub ubhood x∈sup → rec (∈-isProp (ub .fst) _)
      (λ { (a , x∈a₁ , a∈A) → ubhood a a∈A x∈a₁ })
      (unresize x∈sup)

  allChainHasSup : AllChainHasSup
  allChainHasSup A isChainA = sup A isChainA , suphood A isChainA
```

### 后继性

```agda
  ⪯-successvie : isSet U → Def.AllChainHasUb _≤_ → unbound _≤_ → successive _⪯_
  ⪯-successvie Uset hasUb unbnd (A , isChainA) =
    let (ub , ubhood) = hasUb A isChainA
        (ub2 , ub≤ , ub≢) = unbnd ub
    in
    {! ub2  !}
```

## 构造矛盾

```agda
module Contra ⦃ em : ∀ {ℓ} → EM ℓ ⦄ {U : Type u} {_≤_ : Rel U U r}
  (≤-po : isPo _≤_) (hasSup : Def.AllChainHasSup _≤_) (hasSuc : successive _≤_) where
  open import CubicalExt.Logic.Classical
  open Def _≤_

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
      (λ { (z , ¬ub) → let (z∈A , ¬z≤y) = ¬→→∧ (z ∈ A) ⦃ ∈-isProp _ _ _ _ ⦄ (z ≤ y) ¬ub in
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
module PartialOrder ⦃ em : ∀ {ℓ} → EM ℓ ⦄ {U : Type u} (_≤_ : Rel U U r) where
  open import CubicalExt.Logic.Classical
  open Def _≤_

  zorn : Zorn
  zorn (Uset , ≤-po) hasUb = byContra λ noMax → Contra.false ⪯-po allChainHasSup $
    ⪯-successvie Uset hasUb {!   !}
    where open Chain ≤-po
```
