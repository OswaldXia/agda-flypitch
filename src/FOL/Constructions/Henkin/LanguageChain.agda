{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Constructions.Henkin.LanguageChain ⦃ _ : EM ⦄ u where
open import FOL.Constructions.Henkin.Base
open import FOL.Bounded.Base using (Formula; Sentence)
open import FOL.Language hiding (u)
open Language {u}

open import FOL.Language.Homomorphism using (_⟶_; ⟪_,_⟫) renaming (id to idᴸ; _∘_ to _◯_)
open import Tools.DirectedDiagram using (ℕᴰ)
open import FOL.Language.DirectedDiagram
open DirectedDiagramLanguage using (ColimitLanguage; canonicalMorph)

open import Cubical.Foundations.Prelude using (isSet)
open import CubicalExt.Data.Nat using (ℕ-UIP)

open import StdlibExt.Data.Nat
open import Data.Nat.Properties
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Function using (id; _∘_; _$_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

languageStep : Language → Language
languageStep ℒ = record
  { 𝔉 = HekinFunctions ℒ
  ; ℜ = ℒ .ℜ
  ; discrete𝔉 = discreteHekinFunctions ℒ
  ; discreteℜ = ℒ .discreteℜ
  }

languageMorph : ℒ ⟶ languageStep ℒ
languageMorph = ⟪ include , id ⟫

obj : Language → ℕ → Language
obj ℒ zero    = ℒ
obj ℒ (suc n) = languageStep (obj ℒ n)

abstract
  morph : ∀ {i j} → .(i ≤₃ j) → obj ℒ i ⟶ obj ℒ j
  morph {ℒ} {i} {j} i≤y with <-cmp i j
  ... | tri< (s≤s i≤y-1) _ _ = languageMorph ◯ morph (≤⇒≤₃ i≤y-1)
  ... | tri≈ _ refl _ = idᴸ

  zeroMorph≡id : ∀ {i} → morph {ℒ} {i} (≤⇒≤₃ $ ≤-refl) ≡ idᴸ
  zeroMorph≡id {_} {i} with <-cmp i i
  ... | tri< _ ¬p _ = ⊥-elim $ ¬p refl
  ... | tri> _ ¬p _ = ⊥-elim $ ¬p refl
  ... | tri≈ _ s≡s _ with ℕ-UIP s≡s
  ... | refl = refl

  sucMorph≡languageMorph : ∀ {i} → morph {ℒ} {i} (≤⇒≤₃ $ n≤1+n i) ≡ languageMorph
  sucMorph≡languageMorph {ℒ} {i} with <-cmp (i) (suc i)
  ... | tri< (s≤s _) _ _ = subst (λ x → languageMorph ◯ x ≡ _) (sym zeroMorph≡id) refl
  ... | tri> ¬p _ _ = ⊥-elim $ ¬p ≤-refl

  functorial : ∀ {i j k} .{f₁ : i ≤₃ j} .{f₂ : j ≤₃ k} .{f₃ : i ≤₃ k}
    → morph {ℒ} f₃ ≡ (morph f₂ ◯ morph f₁)
  functorial {ℒ} {i} {j} {k} {i≤j} {j≤k} {i≤k} with <-cmp i j | <-cmp j k | <-cmp i k
  ... | tri< _ _ i≰j  | tri< i≤j _ _  | tri≈ _ refl _ = ⊥-elim $ i≰j i≤j
  ... | tri< si≤i _ _ | tri≈ _ refl _ | tri≈ _ refl _ = ⊥-elim $ 1+n≰n si≤i
  ... | tri≈ _ refl _ | tri< si≤i _ _ | tri≈ _ refl _ = ⊥-elim $ 1+n≰n si≤i
  ... | tri≈ _ refl _ | tri≈ _ refl _ | tri< si≤i _ _ = ⊥-elim $ 1+n≰n si≤i
  ... | tri< (s≤s _) _ _ | tri≈ _ refl _    | tri< (s≤s _) _ _ = refl
  ... | tri≈ _ refl _    | tri< (s≤s _) _ _ | tri< (s≤s _) _ _ = refl
  ... | tri< (s≤s i≤j-1) i≢i j≮i | tri< (s≤s j≤k-1) _ _ | tri< (s≤s i≤k-1) _ _ =
    cong (languageMorph ◯_) $ trans
      (functorial {f₁ = i≤₃j} {f₂ = ≤⇒≤₃ j≤k-1} {f₃ = ≤⇒≤₃ i≤k-1})
      (cong (morph (≤⇒≤₃ j≤k-1) ◯_) eq) where
        i≤₃j : i ≤₃ j
        i≤₃j with <-cmp i j
        ... | tri< _ _ _ = tt
        ... | tri≈ _ _ _ = tt
        ... | tri> _ _ j<i = j≮i j<i
        eq : morph {ℒ} i≤₃j ≡ languageMorph ◯ morph (≤⇒≤₃ i≤j-1)
        eq with <-cmp i j
        ... | tri< (s≤s _) _ _ = refl
        ... | tri≈ _ refl _ = ⊥-elim $ i≢i refl
        ... | tri> _ _ j<i  = ⊥-elim $ j≮i j<i
  ... | tri≈ _ refl _ | tri≈ _ refl _ | tri≈ _ i≡i _ with ℕ-UIP i≡i
  ... | refl = refl

languageChain : Language → DirectedDiagramLanguage ℕᴰ
languageChain ℒ = record
  { obj         = obj ℒ
  ; morph       = morph
  ; functorial  = functorial
  }

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
