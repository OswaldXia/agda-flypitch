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
open import Cubical.Foundations.HLevels using (hProp; isPropΠ2)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (∃-syntax; _×_; ΣPathP)
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

```agda
isPoset : Rel U U ℓ → Type _
isPoset R = isPropValued R × isRefl R × isAntisym R × isTrans R

isProset : Rel U U ℓ → Type _
isProset R = isPropValued R × isRefl R × isTrans R

isPoset→isProset : isPoset _≤_ → isProset _≤_
isPoset→isProset (isProp , isRefl , isAntisym , isTrans) = (isProp , isRefl , isTrans)
```

```agda
module Def {U : Type u} (_≤_ : Rel U U r) where

  isChain : 𝒫 U ℓ → Type _
  isChain A = ∀ x y → x ∈ A → y ∈ A → x ≤ y ∨ y ≤ x

  isPropIsChain : isProp (isChain A)
  isPropIsChain = isPropΠ2 λ _ _ → isPropΠ2 λ _ _ → squash₁

  upperBound : 𝒫 U ℓ → U → Type _
  upperBound A ub = ∀ x → x ∈ A → x ≤ ub

  AllChainHasUb = ∀ {ℓ} (A : 𝒫 U ℓ) → isChain A → Σ[ ub ∈ U ] upperBound A ub

  maximum : U → Type _
  maximum m = ∀ x → m ≤ x → x ≡ m
```

给定偏序结构 (`U`, `≤`), 如果 `U` 中的每条链都有一个上界, 那么 (`U`, `≤`) 中存在一个最大元.

```agda
  Zorn = isPoset _≤_ → AllChainHasUb → ∃[ m ∈ U ] maximum m
```

```agda
  -- least upper bound
  supremum : 𝒫 U ℓ → U → Type _
  supremum A sup = upperBound A sup × ∀ ub → upperBound A ub → sup ≤ ub

  AllChainHasSup = ∀ {ℓ} (A : 𝒫 U ℓ) → isChain A → Σ[ sup ∈ U ] supremum A sup

  Successive = ∀ x → Σ[ y ∈ U ] x ≤ y × (¬ x ≡ y) × ∀ z → x ≤ z → z ≤ y → z ≡ x ∨ z ≡ y
```

## 证明

### 构造矛盾

```agda
module Contra ⦃ em : ∀ {ℓ} → EM ℓ ⦄ {U : Type u} {_≤_ : Rel U U r}
  (≤-poset : isPoset _≤_) (hasSuc : Def.Successive _≤_) (hasSup : Def.AllChainHasSup _≤_) where
  open import CubicalExt.Logic.Classical
  open Def _≤_

  private
    ≤-prop    = ≤-poset .fst
    ≤-refl    = ≤-poset .snd .fst
    ≤-antisym = ≤-poset .snd .snd .fst
    ≤-trans   = ≤-poset .snd .snd .snd
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
  sup-ub = Σsup .snd .fst

  Σsuc = hasSuc sup
  suc = Σsuc .fst
  sup≤suc = Σsuc .snd .fst
  sup≢suc = Σsuc .snd .snd .fst

  sup∈Tower : Tower sup
  sup∈Tower = includeSup TowerSet unresize isChainTowerSet

  suc∈TowerSet : suc ∈ TowerSet
  suc∈TowerSet = resize $ map (includeSuc sup) ∣ sup∈Tower ∣₁

  suc≤sup : suc ≤ sup
  suc≤sup = sup-ub suc suc∈TowerSet

  false : ⊥
  false = sup≢suc $ ≤-antisym _ _ sup≤suc suc≤sup
```

### 构造链的偏序

```agda
module Chain {U : Type u} {_≤_ : Rel U U r} (≤-poset : isPoset _≤_) (hasUb : Def.AllChainHasUb _≤_) where
  open Def _≤_

  private
    ≤-prop    = ≤-poset .fst
    ≤-refl    = ≤-poset .snd .fst
    ≤-antisym = ≤-poset .snd .snd .fst
    ≤-trans   = ≤-poset .snd .snd .snd
```

```agda
  Chain = Σ[ S ∈ 𝒫 U ℓ-zero ] isChain S

  _⪯_ : Rel Chain Chain u
  X ⪯ Y = X .fst ⊆ Y .fst
```

```agda
  ⪯-prop : isPropValued _⪯_
  ⪯-prop _ _ = ⊆-isProp _ _

  ⪯-refl : isRefl _⪯_
  ⪯-refl = ⊆-refl ∘ fst

  ⪯-antisym : isAntisym _⪯_
  ⪯-antisym _ _ H₁ H₂ = ΣPathP $ ⊆-antisym _ _ H₁ H₂ , toPathP (isPropIsChain _ _)

  ⪯-trans : isTrans _⪯_
  ⪯-trans = {!   !}

  ⪯-poset : isPoset _⪯_
  ⪯-poset = ⪯-prop , ⪯-refl , ⪯-antisym , ⪯-trans
```
