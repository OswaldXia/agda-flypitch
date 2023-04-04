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
open import FOL.Bounded.Base using (Termₗ; Formulaₗ; Formula; Sentence; Theory)
open import FOL.Language.DirectedDiagram
open import Tools.DirectedDiagram using (DirectedDiagram; Cocone)

import FOL.Bounded.Substitution
import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_; ⟪_,_⟫) renaming (id to idᴸ; _∘_ to _◯_)
open LHom.BoundedComp
open _⟶_

open Language {u}
open Termₗ
open DirectedDiagramLanguage using (ColimitLanguage; canonicalMorph)
open DirectedDiagram using (Coproduct; Colimit)
open CoconeLanguage using (compat)
open Cocone using (universalMap)
```

```agda
open import Cubical.Core.Primitives using (Type; _,_; fst; snd; Σ-syntax)
open import Cubical.Foundations.Prelude using (isProp; isSet; isProp→isSet; toPathP)
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.HLevels using (isSetΣ)
open import Cubical.Data.Equality using (reflPath; symPath; compPath; congPath; eqToPath; pathToEq)
open import Cubical.Data.Nat using (isSetℕ)
open import Cubical.Data.Sigma using (ΣPathP) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.SetQuotients using (eq/; squash/) renaming ([_] to [_]/)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim; elim→Set)
open import CubicalExt.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; squash₂; rec; map; map-functorial)
open import CubicalExt.Data.Nat using (ℕ-UIP)
open import Tools.DirectedDiagram using (DirectedType)
```

```agda
open import Data.Nat.Properties
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Function using (id; _∘_; _$_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import StdlibExt.Data.Nat
open import StdlibExt.Relation.Unary using (_∪_; _⟦_⟧; ⋃_; replacement-syntax)
```

## 语言链

```agda
data HekinFunctions ℒ : ℕ → Type u where
  include  : ∀ {n} → ℒ .functions n → HekinFunctions ℒ n
  witness : Formula ℒ 1 → HekinFunctions ℒ 0
  isSetHekinFunctions : ∀ n → isSet (HekinFunctions ℒ n)
```

```agda
languageStep : Language → Language
languageStep ℒ = record
  { functions = HekinFunctions ℒ
  ; relations = ℒ .relations
  ; isSetFunctions = isSetHekinFunctions
  ; isSetRelations = ℒ .isSetRelations
  }
```

```agda
languageMorph : ℒ ⟶ languageStep ℒ
languageMorph = ⟪ include , id ⟫
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
  ; isSetCarrier = isSetℕ
  ; _~_ = _≤₃_
  ; isRefl~ = λ _ → ≤⇒≤₃ ≤-refl
  ; isTrans~ = λ _ _ _ p q → ≤⇒≤₃ $ ≤-trans (≤₃⇒≤ p) (≤₃⇒≤ q)
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

open LanguageChain
```

```agda
∞-language : Language → Language
∞-language = ColimitLanguage ∘ languageChain

[_]-language : ℕ → Language → Language
[ n ]-language ℒ = LanguageChain.obj ℒ n
```

```agda
languageCanonicalMorph : ∀ n → [ n ]-language ℒ ⟶ ∞-language ℒ
languageCanonicalMorph {ℒ} = canonicalMorph (languageChain ℒ)
```

```agda
henkinization : (ℒ : Language) → ℒ ⟶ ∞-language ℒ
henkinization _ = languageCanonicalMorph 0
```

```agda
coconeOfLanguageChain : CoconeLanguage $ languageChain ℒ
coconeOfLanguageChain = coconeOfColimitLanguage _
```

## 项链

```agda
termChain : ∀ ℒ n l → DirectedDiagram ℕᴰ
termChain ℒ n l = record
  { obj = λ k → ∥ Termₗ ([ k ]-language ℒ) n l ∥₂
  ; morph = λ i≤j → map $ termMorph $ morph i≤j
  ; functorial = trans (cong (map ∘ λ t → termMorph t) functorial)
               $ trans (cong map $ termMorphComp _ _)
               $ pathToEq $ map-functorial _ _
  } where open LHom.Bounded using (termMorph)
```

```agda
coconeOfTermChain : ∀ ℒ n l → Cocone (termChain ℒ n l)
coconeOfTermChain ℒ n l = record
  { Vertex = ∥ Termₗ (∞-language ℒ ) n l ∥₂
  ; isSetVertex = squash₂
  ; map = λ i → map $ termMorph $ languageCanonicalMorph i
  ; compat = λ i~j → trans (cong (map ∘ λ t → termMorph t) (coconeOfLanguageChain .compat i~j))
                   $ trans (cong map $ termMorphComp _ _)
                   $ pathToEq $ map-functorial _ _
  } where open LHom.Bounded using (termMorph)
```

```agda
termComparison : ∀ {ℒ n l} → Colimit (termChain ℒ n l) → ∥ Termₗ (∞-language ℒ) n l ∥₂
termComparison {ℒ} {n} {l} = universalMap (coconeOfTermChain ℒ n l)
```

```agda
termComparisonFiber : ∀ {ℒ n l} (t : Termₗ (∞-language ℒ) n l) → fiber termComparison ∣ t ∣₂
termComparisonFiber (var k) = [ 0 , ∣ var k ∣₂ ]/ , reflPath
termComparisonFiber {ℒ} {n} {l} (func f) = elim→Set
  (λ _ → isSetΣ squash/ $ λ _ → isProp→isSet $ squash₂ _ _)
  (λ ((i , fᵢ) , H) → [ i , ∣ func fᵢ ∣₂ ]/ , congPath (∣_∣₂ ∘ func) H)
  (λ ((i , fᵢ) , Hi) ((j , fⱼ) , Hj) → ΣPathP $
      (eq/ _ _ $ elim {P = λ _ → (i , ∣ func fᵢ ∣₂) ≃ (j , ∣ func fⱼ ∣₂)} (λ _ → squash₁)
        (λ (k , fₖ , i~k , j~k , H₁ , H₂) → ∣ k , ∣ func fₖ ∣₂ , i~k , j~k , cong (∣_∣₂ ∘ func) H₁ , cong (∣_∣₂ ∘ func) H₂ ∣₁)
        (effective $ compPath Hi $ symPath Hj))
    , (toPathP $ squash₂ _ _ _ _))
  (representative f)
  where open DirectedDiagram (termChain ℒ n l) using (_≃_)
        open DirectedDiagramLanguage (languageChain ℒ) using (functionsᴰ)
        open DirectedDiagram (functionsᴰ l) using (representative; effective)
termComparisonFiber (app t₁ t₂) = {!   !}
```

## 公式链

```agda
formulaChain : ∀ ℒ n l → DirectedDiagram ℕᴰ
formulaChain ℒ n l = record
  { obj = λ k → ∥ Formulaₗ ([ k ]-language ℒ) n l ∥₂
  ; morph = λ i≤j → map $ formulaMorph $ morph i≤j
  ; functorial = trans (cong (map ∘ λ φ → formulaMorph φ) functorial)
               $ trans (cong map $ formulaMorphComp _ _)
               $ pathToEq $ map-functorial _ _
  } where open LHom.Bounded using (formulaMorph)
```

```agda
coconeOfFormulaChain : ∀ ℒ n l → Cocone (formulaChain ℒ n l)
coconeOfFormulaChain ℒ n l = record
  { Vertex = ∥ Formulaₗ (∞-language ℒ ) n l ∥₂
  ; isSetVertex = squash₂
  ; map = λ i → map $ formulaMorph $ languageCanonicalMorph i
  ; compat = λ i~j → trans (cong (map ∘ λ φ → formulaMorph φ) (coconeOfLanguageChain .compat i~j))
                   $ trans (cong map $ formulaMorphComp _ _)
                   $ pathToEq $ map-functorial _ _
  } where open LHom.Bounded using (formulaMorph)
          open CoconeLanguage using (compat)
```

```agda
formulaComparison : ∀ {ℒ n l} → Colimit (formulaChain ℒ n l) → ∥ Formulaₗ (∞-language ℒ ) n l ∥₂
formulaComparison {ℒ} {n} {l} = universalMap (coconeOfFormulaChain ℒ n l)
```

## Henkin化理论

```agda
witnessOf : Formula ℒ 1 → Constant $ languageStep ℒ
witnessOf = witness
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
[ n ]-∞-theory T = sentenceMorph ⟦ [ n ]-theory T ⟧
  where open LHom.Bounded (languageCanonicalMorph n)
```

```agda
∞-theory : Theory ℒ → Theory $ ∞-language ℒ
∞-theory T = ⋃ (λ n → [ n ]-∞-theory T)
```

```agda
∞-witness : {T : Theory ℒ} (φ : Formula (∞-language ℒ) 1) →
  Σ[ c ∈ Constant $ ∞-language ℒ ]
  Σ[ φₗ ∈ Colimit (formulaChain ℒ 1 0) ]
  Σ[ φₚ@(i , φᵢ) ∈ Coproduct (formulaChain ℒ 1 0) ]
    [ φₚ ]/ ≡ φₗ
  × formulaComparison φₗ ≡ ∣ φ ∣₂
  × c ≡ languageCanonicalMorph (suc i) .funMorph (rec (isSetFunctions ([ suc i ]-language ℒ) _) witnessOf φᵢ)
∞-witness = {!   !}
```
