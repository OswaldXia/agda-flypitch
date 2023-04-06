{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module FOL.Constructions.Henkin.LanguageChain u where
open import FOL.Constructions.Henkin.Base
open import FOL.Bounded.Base using (Formula; Sentence; Theory)
open import FOL.Language hiding (u)
open Language {u}

open import Tools.DirectedDiagram using (ℕᴰ)
open import FOL.Language.DirectedDiagram
open DirectedDiagramLanguage using (ColimitLanguage; canonicalMorph)
import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_; ⟪_,_⟫) renaming (id to idᴸ; _∘_ to _◯_)

open import Cubical.Core.Primitives hiding (_≡_)
open import Cubical.Foundations.Prelude using (isSet)
open import CubicalExt.Data.Nat using (ℕ-UIP)

open import StdlibExt.Data.Nat
open import Data.Nat.Properties
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Function using (id; _∘_; _$_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

languageStep : Language → Language
languageStep ℒ = record
  { functions = HekinFunctions ℒ
  ; relations = ℒ .relations
  ; isSetFunctions = isSetHekinFunctions
  ; isSetRelations = ℒ .isSetRelations
  }

languageMorph : ℒ ⟶ languageStep ℒ
languageMorph = ⟪ include , id ⟫

obj : Language → ℕ → Language
obj ℒ zero    = ℒ
obj ℒ (suc n) = languageStep (obj ℒ n)

morph : ∀ {x y} → .(x ≤₃ y) → obj ℒ x ⟶ obj ℒ y
morph {ℒ} {x} {y} x≤y with <-cmp x y
... | tri< (s≤s x≤y-1) _ _ = languageMorph ◯ morph (≤⇒≤₃ x≤y-1)
... | tri≈ _ refl _ = idᴸ

abstract
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
        eq : morph {ℒ} x≤₃y ≡ languageMorph ◯ morph (≤⇒≤₃ x≤y-1)
        eq with <-cmp x y
        ... | tri< (s≤s _) _ _ = refl
        ... | tri≈ _ refl _ = ⊥-elim $ x≢x refl
        ... | tri> _ _ y<x  = ⊥-elim $ y≮x y<x
  ... | tri≈ _ refl _ | tri≈ _ refl _ | tri≈ _ x≡x _ with ℕ-UIP x≡x
  ... | refl = refl

languageChain : Language → DirectedDiagramLanguage ℕᴰ
languageChain ℒ = record
  { obj         = obj ℒ
  ; morph       = morph
  ; functorial  = functorial
  }

endomorph≡id : ∀ {i} → morph {ℒ} {i} (≤⇒≤₃ $ ≤-refl) ≡ idᴸ
endomorph≡id {_} {zero} = refl
endomorph≡id {_} {suc i} with <-cmp (suc i) (suc i)
... | tri< _ ¬p _ = ⊥-elim $ ¬p refl
... | tri> _ ¬p _ = ⊥-elim $ ¬p refl
... | tri≈ _ s≡s _ with ℕ-UIP s≡s
... | refl = refl

∞-language : Language → Language
∞-language = ColimitLanguage ∘ languageChain

[_]-language : ℕ → Language → Language
[ n ]-language ℒ = obj ℒ n

languageCanonicalMorph : ∀ n → [ n ]-language ℒ ⟶ ∞-language ℒ
languageCanonicalMorph {ℒ} = canonicalMorph (languageChain ℒ)

henkinization : (ℒ : Language) → ℒ ⟶ ∞-language ℒ
henkinization _ = languageCanonicalMorph 0

coconeOfLanguageChain : CoconeLanguage $ languageChain ℒ
coconeOfLanguageChain = coconeOfColimitLanguage _
