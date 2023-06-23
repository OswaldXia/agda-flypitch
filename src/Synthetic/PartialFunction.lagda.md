---
title: Agda综合哥德尔不完备 (1) 偏函数
---

# Agda综合哥德尔不完备 (1) 偏函数

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Synthetic.PartialFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import CubicalExt.Functions.Logic using (⊤; ⊥)
open import Cubical.Data.Bool
open import Cubical.Data.Empty as ⊥ using (rec)
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Equality using (eqToPath)
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁

private variable
  ℓ ℓ' : Level
  A B : Type ℓ
```

传统数学广泛使用偏函数, 本讲亦是如此. 由于类型论中的函数默认是全函数, 这就要求我们首先要定义什么是偏函数. 实现这一目标的方法众多, 我们采用与泛等基础比较兼容的方法, 使偏函数的主要性质和相关构造不依赖于目标类型的同伦层级.

## 偏函数的定义

对任意类型 `A`, 我们定义一个偏类型 `Part A`. 而 `A` 到 `B` 的偏函数则写作 `A → Part B`.

```agda
Part : Type ℓ → (ℓ' : Level) → Type _
```

偏类型 `Part A` 的项 (以下称偏元素) 是一个二元组 `(P , f)`, 其中 `P` 是一个命题, 而 `f` 是一个函数, 它接受 `P` 的证明, 并返回一个 `A` 的元素. 由于 `P` 是一个命题, 所以 `P` 的证明是唯一的, 从而 `f` 的返回值也是唯一的.

```agda
Part A ℓ' = Σ (hProp ℓ') λ P → ⟨ P ⟩ → A
```

我们说偏元素有定义, 当且仅当二元组中的那个 `P` 成立.

```agda
defined : Part A ℓ → Type _
defined (P , _) = ⟨ P ⟩
```

"有定义"是一个谓词, 因为 `P` 是命题.

```agda
isPropDefined : (x : Part A ℓ) → isProp (defined x)
isPropDefined (P , _) = str P
```

如果偏元素有定义, 我们就可以拿到定义值.

```agda
value : (xₚ : Part A ℓ) → defined xₚ → A
value (_ , f) H = f H
```

## 偏类型单子

以下三项表明 `Part` 是一个单子, 这从另一个角度说明了我们的定义是恰当的. 不理解这一点也不影响后续内容的理解.

```agda
∅ : Part A ℓ
∅ = ⊥ , λ ()

return : A → Part A ℓ
return x = ⊤ , λ _ → x

_>>=_ : Part A ℓ → (A → Part B ℓ) → Part B ℓ
(P , f) >>= g = (Σ ⟨ P ⟩ (defined ∘ g ∘ f) , isPropΣ (str P) (isPropDefined ∘ g ∘ f)) ,
  uncurry λ p def → value (g (f p)) def
```

## 定义值的判别

我们说偏元素 `xₚ` "等于" `x` (记作 `xₚ ≐ x`), 当且仅当 `xₚ` 有定义, 且 `xₚ` 的定义值等于 `x`.

```agda
_≐_ : Part A ℓ → A → Type _
xₚ ≐ x = Σ (defined xₚ) λ H → value xₚ H ≡ x
```

`≐` 还有一种等价定义但不方便处理.

```agda
_≐'_ : Part A ℓ → A → Type _
xₚ ≐' x = xₚ ≡ return x
```

可以证明 `≐` 是一个具有函数性的关系.

```agda
≐-functional : (xₚ : Part A ℓ) {x y : A} → xₚ ≐ x → xₚ ≐ y → x ≡ y
≐-functional (P , f) (p , fp≡x) (q , fq≡y) = sym fp≡x ∙ (cong f (str P p q)) ∙ fq≡y
```

我们说一个偏元素是未定义的, 当且仅当对任意元素 `x` 都不满足 `xₚ ≐ x`.

```agda
undefined : Part A ℓ → Type _
undefined xₚ = ∀ x → ¬ xₚ ≐ x
```

## 定义域与值域

```agda
module _ (f : A → Part B ℓ) where

  domain : A → Type _
  domain x = defined (f x)

  range : B → Type _
  range y = ∃ A λ x → f x ≐ y
```

## 与全函数的相互转化

给定偏函数 `f : A → Part B`, 我们说它是全的, 当且仅当任意 `f x` 都有定义.

```agda
total : (A → Part B ℓ) → Type _
total f = ∀ x → defined (f x)
```

我们可以把一个全的偏函数转化为全函数.

```agda
totalise : (f : A → Part B ℓ) → total f → (∀ x → Σ _ (f x ≐_))
totalise f H x = value (f x) (H x) , H x , refl
```

反过来, 任意全函数都可以转化为全的偏函数.

```agda
partialise : (A → B) → A → Part B ℓ
partialise f x = return (f x)

total-partialise : (f : A → B) → total {ℓ = ℓ} (partialise f)
total-partialise _ _ = tt*
```

## 偏类型的同伦层级

偏类型与基底类型具有相同的同伦层级, 且至少是集合.

```agda
isOfHLevelPart : ∀ n → isOfHLevel (suc (suc n)) A → isOfHLevel (suc (suc n)) (Part A ℓ)
isOfHLevelPart n lA = isOfHLevelΣ (suc (suc n))
  (isOfHLevelPlus' 2 isSetHProp) λ _ → isOfHLevelΠ (suc (suc n)) λ _ → lA

isSetPart : isSet A → isSet (Part A ℓ)
isSetPart = isOfHLevelPart 0
```

`≐` 的同伦层级比基底类型低一级. 如果基底类型是集合, 那么 `≐` 是命题.

```agda
isOfHLevel≐ : ∀ n → isOfHLevel (suc (suc n)) A → (xₚ : Part A ℓ) (x : A) → isOfHLevel (suc n) (xₚ ≐ x)
isOfHLevel≐ n lA (P , f) x = isOfHLevelΣ (suc n)
  (isOfHLevelPlus' 1 (str P)) λ _ → lA _ _

isProp≐ : isSet A → (xₚ : Part A ℓ) (x : A) → isProp (xₚ ≐ x)
isProp≐ = isOfHLevel≐ 0
```

## 半可判定偏类型

```agda
_semidec_ : (ℕ → Bool) → Type ℓ → Type _
f semidec A = A ≡ Lift (∃ _ λ n → f n ≡ true)

Semidec : Type ℓ → Type _
Semidec A = Σ (ℕ → Bool) (_semidec A)

SemidecPart : Type ℓ → (ℓ' : Level) → Type _
SemidecPart A ℓ' = Σ (Part A ℓ') (Semidec ∘ defined)

isPropSemidec : (X@(xₚ , fₛ , Hₛ) : SemidecPart A ℓ) → isProp (fₛ semidec defined xₚ)
isPropSemidec X = {!   !}

module _ ((xₚ , fₛ , Hₛ) : SemidecPart A ℓ) where
  true→defined : ∀ n → fₛ n ≡ true → defined xₚ
  true→defined n eq = transport (sym Hₛ) (lift ∣ n , eq ∣₁)

  defined→true : defined xₚ → ∃ _ λ n → fₛ n ≡ true
  defined→true def = lower $ transport Hₛ def
```

## 单值可选序列

```agda
single : (A → Maybe B) → Type _
single f = isProp (Σ _ λ y → ∃ _ λ x → f x ≡ just y)

single₂ : (A → Maybe B) → Type _
single₂ f = ∀ {n m x y} → f n ≡ just x → f m ≡ just y → x ≡ y

single→₂ : {f : A → Maybe B} → single f → single₂ f
single→₂ H p q = cong fst $ H (_ , ∣ _ , p ∣₁) (_ , ∣ _ , q ∣₁)

single₂→ : {f : A → Maybe B} → isSet B → single₂ f → single f
single₂→ Bset H (x , H₁) (y , H₂) = ΣPathP
  $ rec2 (Bset x y) (λ (_ , p) (_ , q) → H p q) H₁ H₂
  , isProp→PathP (λ _ → squash₁) _ _

SingleMaybeSeq : Type ℓ → Type ℓ
SingleMaybeSeq A = Σ (ℕ → Maybe A) single
```

## 半可判定偏类型与单值可选序列同构

```agda
module PartIso {ℓ} {A : Type ℓ} (Aset : isSet A) where

  module Fun (X@(xₚ , fₛ , Hₛ) : SemidecPart A ℓ) where
    fₘ : ℕ → Maybe A
    fₘ n with fₛ n | true→defined X n
    ... | true  | H  = just $ value xₚ $ H refl
    ... | false | _  = nothing
    Hₘ : single₂ fₘ
    Hₘ {n} {m} p q with fₛ n | fₛ m | true→defined X n | true→defined X m
    ... | true  | true  | c | d = just-inj _ _ $
      (sym p) ∙ cong (just ∘ value xₚ) (isPropDefined xₚ _ _) ∙ q
    ... | true  | false | _ | _ = ⊥.rec $ ¬nothing≡just q
    ... | false | _     | _ | _ = ⊥.rec $ ¬nothing≡just p
    Y : SingleMaybeSeq A
    Y = fₘ , single₂→ Aset Hₘ
    just→true : ∀ {n x} → fₘ n ≡ just x → fₛ n ≡ true
    just→true {n} H with fₛ n | true→defined X n
    ... | true  | _ = refl
    ... | false | _ = ⊥.rec $ ¬nothing≡just H
    true→just : ∀ {n} → fₛ n ≡ true → Σ _ λ x → fₘ n ≡ just x
    true→just {n} H with fₛ n | true→defined X n
    ... | true  | def = (value xₚ (def refl)) , refl
    ... | false | _   = ⊥.rec $ false≢true H
    true→just≡ : ∀ {n} (H : fₛ n ≡ true) (def : defined xₚ) → true→just H .fst ≡ value xₚ def
    true→just≡ {n} H def with fₛ n | true→defined X n
    ... | true  | _ = cong (value xₚ) (isPropDefined xₚ _ _)
    ... | false | _ = ⊥.rec $ false≢true H

  module Inv (Y@(fₘ , Hₘ) : SingleMaybeSeq A) where
    P = Σ _ λ y → ∃ _ λ n → fₘ n ≡ just y
    fₛ : ℕ → Bool
    fₛ n with fₘ n
    ... | just _ = true
    ... | _      = false
    xₚ : Part A _
    xₚ = (P , Hₘ) , fst
    just→true : ∀ {n x} → fₘ n ≡ just x → fₛ n ≡ true
    just→true {n} H with fₘ n
    ... | just x = refl
    ... | nothing = ⊥.rec $ ¬nothing≡just H
    true→just : ∀ {n} → fₛ n ≡ true → Σ _ λ x → fₘ n ≡ just x
    true→just {n} H with fₘ n
    ... | just x = x , refl
    ... | nothing = ⊥.rec $ false≢true H
    Hₛ : fₛ semidec defined ((P , Hₘ) , fst)
    Hₛ = hPropExt (isPropDefined xₚ) (isOfHLevelLift 1 squash₁)
      (lift ∘ (map $ uncurry λ n H → n , just→true H) ∘ snd)
      ((∥₁.rec (isPropDefined xₚ) (uncurry λ n H →
        let (x , H) = true→just H in x , ∣ n , H ∣₁)) ∘ lower)
    X : SemidecPart A ℓ
    X = xₚ , fₛ , Hₛ

  SemidecPartIsoSingleMaybeSeq : Iso (SemidecPart A ℓ) (SingleMaybeSeq A)
  Iso.fun       SemidecPartIsoSingleMaybeSeq = Fun.Y
  Iso.inv       SemidecPartIsoSingleMaybeSeq = Inv.X
  Iso.leftInv   SemidecPartIsoSingleMaybeSeq X@(xₚ , fₛ , Hₛ) =
    let Y@(fₘ , Hₘ)          = Fun.Y X
        X'@(xₚ' , fₛ' , Hₛ') = Inv.X Y
        defined≡ : defined xₚ' ≡ defined xₚ
        defined≡ = hPropExt (isPropDefined xₚ') (isPropDefined xₚ)
          (λ { (x , H) → ∥₁.rec (isPropDefined xₚ)
            (λ (n , H) → true→defined X n $ Fun.just→true X H) H })
          (λ def → ∥₁.rec Hₘ
            (λ (n , H) → let (x , H) = Fun.true→just X H in x , ∣ n , H ∣₁)
            (defined→true X def))
        P≡ : fst xₚ' ≡ fst xₚ
        P≡ = ΣPathP $ defined≡ , isProp→PathP (λ _ → isPropIsProp) Hₘ (isPropDefined xₚ)
    in ΣPathP $ ΣPathP (P≡ , toPathP (funExt λ def → {!   !}))
    , {!   !}
  Iso.rightInv  SemidecPartIsoSingleMaybeSeq = {!   !}
```
