---
title: Agda一阶逻辑(?) Henkin模型
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(?) Henkin模型

> 交流Q群: 893531731  
> 本文源码: [Henkin.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Henkin.lagda.md)  
> 高亮渲染: [Henkin.html](https://choukh.github.io/agda-flypitch/FOL.Henkin.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module FOL.Constructions.Henkin {u} where
open import FOL.Language hiding (u)
open import FOL.Bounded.Base using (Formula; Sentence; Theory)
open import FOL.Language.DirectedDiagram
```

```agda
import FOL.Language.Homomorphism as LHom
import FOL.Bounded.Substitution
open LHom using (_⟶_) renaming (id to idᴸ; _∘_ to _◯_)
open DirectedDiagramLanguage using (Colimit; canonicalMorph)
open Language {u}
```

```agda
open import Cubical.Core.Everything using (Type)
open import CubicalExt.Data.Nat using (ℕ-UIP)
open import Tools.DirectedDiagram using (DirectedType)
```

```agda
open import Data.Nat.Properties
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (_∘_; _$_; id)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import StdlibExt.Data.Nat
open import StdlibExt.Relation.Unary using (_∪_; _⟦_⟧; ⋃_; replacement-syntax)
```

```agda
data Functions ℒ : ℕ → Type u where
  include  : ∀ {n} → ℒ .functions n → Functions ℒ n
  witness : Formula ℒ 1 → Functions ℒ 0
```

```agda
languageStep : Language → Language
languageStep ℒ = record { functions = Functions ℒ ; relations = ℒ .relations }
```

```agda
languageMorph : ℒ ⟶ languageStep ℒ
languageMorph = record { funMorph = Functions.include ; relMorph = id }
```

```agda
module LanguageChain where

  obj : Language → ℕ → Language
  obj ℒ zero    = ℒ
  obj ℒ (suc n) = languageStep (obj ℒ n)
```

```agda
  morph : ∀ {x y} → .(x ≤₃ y) → obj ℒ x ⟶ obj ℒ y
  morph {ℒ} {x} {y} x≤y with <-cmp x y
  ... | tri< (s≤s x≤y-1) _ _ = languageMorph ◯ morph (≤⇒≤₃ x≤y-1)
  ... | tri≈ _ refl _ = idᴸ
```

```agda
  functorial : ∀ {x y z : ℕ} .{f₁ : x ≤₃ y} .{f₂ : y ≤₃ z} .{f₃ : x ≤₃ z}
    → morph {ℒ} f₃ ≡ (morph f₂ ◯ morph f₁)
  functorial {ℒ} {x} {y} {z} {x≤y} {y≤z} {x≤z} with <-cmp x y | <-cmp y z | <-cmp x z
  ... | tri< _ _ x≰y  | tri< x≤y _ _  | tri≈ _ refl _ = ⊥-elim $ x≰y x≤y
  ... | tri< sx≤x _ _ | tri≈ _ refl _ | tri≈ _ refl _ = ⊥-elim $ 1+n≰n sx≤x
  ... | tri≈ _ refl _ | tri< sx≤x _ _ | tri≈ _ refl _ = ⊥-elim $ 1+n≰n sx≤x
  ... | tri≈ _ refl _ | tri≈ _ refl _ | tri< sx≤x _ _ = ⊥-elim $ 1+n≰n sx≤x
  ... | tri< (s≤s _) _ _ | tri≈ _ refl _    | tri< (s≤s _) _ _ = refl
  ... | tri≈ _ refl _    | tri< (s≤s _) _ _ | tri< (s≤s _) _ _ = refl
  ... | tri< (s≤s x≤y-1) x≢x y≮x | tri< (s≤s y≤z-1) _ _ | tri< (s≤s x≤z-1) _ _ =
    cong (languageMorph ◯_) $ trans
      (functorial {f₁ = x≤₃y} {f₂ = ≤⇒≤₃ y≤z-1} {f₃ = ≤⇒≤₃ x≤z-1})
      (cong (morph (≤⇒≤₃ y≤z-1) ◯_) eq) where
        x≤₃y : x ≤₃ y
        x≤₃y with <-cmp x y
        ... | tri< _ _ _ = tt
        ... | tri≈ _ _ _ = tt
        ... | tri> _ _ y<x = y≮x y<x
        eq : morph x≤₃y ≡ languageMorph ◯ morph (≤⇒≤₃ x≤y-1)
        eq with <-cmp x y
        ... | tri< (s≤s _) _ _ = refl
        ... | tri≈ _ refl _ = ⊥-elim $ x≢x refl
        ... | tri> _ _ y<x  = ⊥-elim $ y≮x y<x
  ... | tri≈ _ refl _ | tri≈ _ refl _ | tri≈ _ x≡x _ with ℕ-UIP x≡x
  ... | refl = refl
```

```agda
ℕᴰ : DirectedType
ℕᴰ = record
  { Carrier = ℕ
  ; _~_ = _≤₃_
  ; ~-refl = ≤⇒≤₃ ≤-refl
  ; ~-trans = λ p q → ≤⇒≤₃ $ ≤-trans (≤₃⇒≤ p) (≤₃⇒≤ q)
  ; directed = λ x y → x + y , ≤⇒≤₃ (m≤m+n _ _) , ≤⇒≤₃ (m≤n+m _ _)
  }
```

```agda
languageChain : Language → DirectedDiagramLanguage ℕᴰ
languageChain ℒ = record
  { obj         = obj ℒ
  ; morph       = morph
  ; functorial  = functorial
  } where open LanguageChain
```

```agda
∞-language : Language → Language
∞-language = Colimit ∘ languageChain

[_]-language : ℕ → Language → Language
[ n ]-language ℒ = LanguageChain.obj ℒ n
```

```agda
languageCanonicalMorph : ∀ n → [ n ]-language ℒ ⟶ ∞-language ℒ
languageCanonicalMorph {ℒ} n = canonicalMorph (languageChain ℒ) n
```

```agda
henkinization : (ℒ : Language) → ℒ ⟶ ∞-language ℒ
henkinization _ = languageCanonicalMorph 0
```

```agda
witnessOf : Formula ℒ 1 → Constant $ languageStep ℒ
witnessOf = Functions.witness
```

```agda
[_witnessing_] : Constant ℒ → Formula ℒ 1 → Sentence ℒ
[_witnessing_] {ℒ} c φ = (∃' φ) ⇒ φ [ const c / 0 ] where
  open FOL.Bounded.Base ℒ
  open FOL.Bounded.Substitution ℒ
```

```agda
theoryStep : Theory ℒ → Theory $ languageStep ℒ
theoryStep {ℒ} Γ = theoryMorph Γ ∪ ｛ [ witnessOf φ witnessing formulaMorph φ ] ∣ φ ∈ Formula ℒ 1 ｝
  where open LHom.Bounded languageMorph
```

```agda
[_]-theory : ∀ n → Theory ℒ → Theory $ [ n ]-language ℒ
[ zero ]-theory T = T
[ suc n ]-theory T = theoryStep $ [ n ]-theory T
```

```agda
[_]-∞-theory : ∀ n → Theory ℒ → Theory $ ∞-language ℒ
[ n ]-∞-theory T = sentenceMorph ⟦ ([ n ]-theory T) ⟧
  where open LHom.Bounded (languageCanonicalMorph n)
```

```agda
∞-theory : Theory ℒ → Theory $ ∞-language ℒ
∞-theory T = ⋃ (λ n → [ n ]-∞-theory T)
```
