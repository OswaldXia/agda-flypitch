---
title: Agda综合哥德尔不完备
---

# Agda综合哥德尔不完备 (1) 偏函数

传统数学广泛使用偏函数, 本讲的内容亦是如此. 然而, 在类型论中, 函数默认被视为全函数, 这就要求我们在类型论中为偏函数建立模型. 实现这一目标的方法众多, 有一篇出色的[文献](https://arxiv.org/abs/2011.00272)较为全面地考察了泛等基础中的偏函数, 可作为拓展阅读材料. 我们所采用的形式没有文献中那么一般化, 但对于本讲的目标来说是足够的.

```agda
{-# OPTIONS --cubical --safe #-}

module Synthetic.PartialFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Logic.ConstructiveEpsilon

private variable
  ℓ : Level
  A B : Type ℓ

deterministic : (A → Maybe B) → Type _
deterministic f = isProp (Σ _ λ y → ∃ _ λ x → f x ≡ just y)

deterministic₂ : (A → Maybe B) → Type _
deterministic₂ f = ∀ {n m x y} → f n ≡ just x → f m ≡ just y → x ≡ y

deterministic→₂ : {f : A → Maybe B} → deterministic f → deterministic₂ f
deterministic→₂ H p q = cong fst $ H (_ , ∣ _ , p ∣₁) (_ , ∣ _ , q ∣₁)

deterministic₂→ : {f : A → Maybe B} → isSet B → deterministic₂ f → deterministic f
deterministic₂→ Bset H (x , H₁) (y , H₂) = ΣPathP
  $ rec2 (Bset x y) (λ (_ , p) (_ , q) → H p q) H₁ H₂
  , isProp→PathP (λ _ → squash₁) _ _

record part (A : Type ℓ) : Type ℓ where
  constructor mkPart
  field
    eval : ℕ → Maybe A
    proper : deterministic eval
  proper₂ : deterministic₂ eval
  proper₂ = deterministic→₂ proper

  evalTo : A → Type ℓ
  evalTo x = ∃ _ λ k → eval k ≡ just x

  functional : ∀ {x y} → evalTo x → evalTo y → x ≡ y
  functional {x} {y} H₁ H₂ = cong fst $ proper (x , H₁) (y , H₂)

  opaque
    totalise : isSet A → ∃ _ evalTo → Σ _ evalTo
    totalise Aset xₚ = σ .snd .fst , ∣ σ .fst , σ .snd .snd ∣₁ where
      swapevalTo : ∃ _ evalTo → ∃ _ λ k → Σ _ λ x → eval k ≡ just x
      swapevalTo = ∥₁.rec squash₁ λ (x , ea) → map (λ (n , H) → n , x , H) ea
      Σ[x] : ℕ → Type ℓ
      Σ[x] n = Σ _ λ x → eval n ≡ just x
      isSetΣ[x] : ∀ n → isSet (Σ[x] n)
      isSetΣ[x] _ = isSetΣ Aset λ _ → isProp→isSet (isOfHLevelMaybe 0 (λ _ _ → Aset _ _) _ _)
      DecΣ[x] : ∀ n → Dec (Σ[x] n)
      DecΣ[x] n with eval n
      ... | nothing = no λ (_ , H) → ⊥.rec (¬nothing≡just H)
      ... | just x = yes (x , refl)
      σ : Σ _ Σ[x]
      σ = ε isSetΣ[x] DecΣ[x] (swapevalTo xₚ)

mkPart₂ : isSet A → (eval : ℕ → Maybe A) → deterministic₂ eval → part A
mkPart₂ Aset eval proper = mkPart eval (deterministic₂→ Aset proper)

_≐_ : part A → A → Type _
xₚ ≐ x = part.evalTo xₚ x

≐-functional : (xₚ : part A) {x y : A} → xₚ ≐ x → xₚ ≐ y → x ≡ y
≐-functional = part.functional

convergent : part A → Type _
convergent xₚ = ∃ _ (xₚ ≐_)

divergent : part A → Type _
divergent xₚ = ∀ x → ¬ xₚ ≐ x

total : (A → part B) → Type _
total eval = ∀ x → convergent (eval x)

totalise : isSet B → (f : A → part B) → total f → (∀ x → Σ _ (f x ≐_))
totalise Bset f H x = part.totalise (f x) Bset (H x)

partialise : isSet B → (A → B) → A → part B
partialise Bset f x = mkPart (λ _ → just (f x))
  (deterministic₂→ Bset λ p q → just-inj _ _ ((sym p) ∙ q))

--------------------------------------------------------------------------------
-- h-level of part

partΣ : Type ℓ → Type ℓ
partΣ A = Σ (ℕ → Maybe A) deterministic

partΣIsoPart : Iso (partΣ A) (part A)
Iso.fun       partΣIsoPart (eval , p) = mkPart eval p
Iso.inv       partΣIsoPart xₚ = part.eval xₚ , part.proper xₚ
Iso.leftInv   partΣIsoPart a = refl
Iso.rightInv  partΣIsoPart b = refl

partΣ≡Part : partΣ A ≡ part A
partΣ≡Part = isoToPath partΣIsoPart

isOfHLevelPartΣ : ∀ {ℓ} (n : HLevel) {A : Type ℓ} →
  isOfHLevel (suc (suc n)) A →
  isOfHLevel (suc (suc n)) (partΣ A)
isOfHLevelPartΣ n lA = isOfHLevelΣ (suc (suc n))
  (isOfHLevelΠ (suc (suc n)) λ _ → isOfHLevelMaybe n lA)
  λ _ → isProp→isOfHLevelSuc (suc n) isPropIsProp

isOfHLevelPart : ∀ {ℓ} (n : HLevel) {A : Type ℓ} →
  isOfHLevel (suc (suc n)) A →
  isOfHLevel (suc (suc n)) (part A)
isOfHLevelPart n lA = subst (isOfHLevel (suc (suc n))) partΣ≡Part (isOfHLevelPartΣ n lA)
```
