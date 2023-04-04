{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module FOL.Constructions.Henkin.TermChain u where
open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Language using (Language)
open import FOL.Bounded.Base using (Termₗ)
open Termₗ

import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_) renaming (_∘_ to _◯_)
open LHom.Bounded using (termMorph)
open LHom.BoundedProperties

open import Tools.DirectedDiagram using (ℕᴰ; DirectedDiagram; Cocone)
open DirectedDiagram using (Colimit)
open Cocone using (universalMap)
open import FOL.Language.DirectedDiagram using (DirectedDiagramLanguage; CoconeLanguage)
open CoconeLanguage using (compat)

open import Cubical.Core.Primitives renaming (_≡_ to _≡ₚ_)
open import Cubical.Foundations.Prelude using (isProp; isSet; isProp→isSet; toPathP)
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.HLevels using (isSetΣ)
open import Cubical.HITs.SetQuotients using (eq/; [_]; squash/)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim; elim→Set; elim2→Set)
open import CubicalExt.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; squash₂; map; map2; map-functorial)
open import Cubical.Data.Equality using (pathToEq; reflPath; symPath; compPath; congPath)
open import Cubical.Data.Sigma using (ΣPathP) renaming (_×_ to infixr 3 _×_)

open import StdlibExt.Data.Nat
open import Data.Nat.Properties
open import Function using (_∘_; _$_; flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong-app; subst)

mapTermMorph-functorial : ∀ {ℒ₁ ℒ₂ ℒ₃ : Language {u}} {n l : ℕ}
  {F₁ : ℒ₁ ⟶ ℒ₂} {F₂ : ℒ₂ ⟶ ℒ₃} {F₃ : ℒ₁ ⟶ ℒ₃} → F₃ ≡ F₂ ◯ F₁ →
  (map $ termMorph F₃ {n} {l}) ≡ (map $ termMorph F₂) ∘ (map $ termMorph F₁)
mapTermMorph-functorial H = trans (cong (map ∘ λ t → termMorph t) H)
  $ trans (cong map $ termMorphComp _ _)
  $ pathToEq $ map-functorial _ _

termChain : ∀ ℒ n l → DirectedDiagram ℕᴰ
termChain ℒ n l = record
  { obj = λ k → ∥ Termₗ ([ k ]-language ℒ) n l ∥₂
  ; morph = λ i≤j → map $ termMorph $ morph i≤j
  ; functorial = mapTermMorph-functorial functorial
  }

coconeOfTermChain : ∀ ℒ n l → Cocone (termChain ℒ n l)
coconeOfTermChain ℒ n l = record
  { Vertex = ∥ Termₗ (∞-language ℒ ) n l ∥₂
  ; isSetVertex = squash₂
  ; map = λ i → map $ termMorph $ languageCanonicalMorph i
  ; compat = λ {i} i~j → mapTermMorph-functorial (coconeOfLanguageChain .compat i~j)
  }

termComparison : ∀ {ℒ n l} → Colimit (termChain ℒ n l) → ∥ Termₗ (∞-language ℒ) n l ∥₂
termComparison {ℒ} {n} {l} = universalMap (coconeOfTermChain ℒ n l)

termComparisonFiber : ∀ {ℒ n l} (t : Termₗ (∞-language ℒ) n l) → fiber termComparison ∣ t ∣₂
termComparisonFiber (var k) = [ 0 , ∣ var k ∣₂ ] , reflPath
termComparisonFiber {ℒ} {n} {l} (func f) =
  elim→Set {P = λ _ → fiber termComparison ∣ func f ∣₂}
    (λ _ → isSetΣ squash/ $ λ _ → isProp→isSet $ squash₂ _ _)
    (λ ((i , fᵢ) , H) → [ i , ∣ func fᵢ ∣₂ ] , congPath (∣_∣₂ ∘ func) H)
    (λ ((i , fᵢ) , Hi) ((j , fⱼ) , Hj) → ΣPathP $
      (eq/ _ _ $ elim {P = λ _ → (i , ∣ func fᵢ ∣₂) ≃ (j , ∣ func fⱼ ∣₂)} (λ _ → squash₁)
        (λ (k , fₖ , i~k , j~k , H₁ , H₂) → ∣ k , ∣ func fₖ ∣₂ , i~k , j~k , cong (∣_∣₂ ∘ func) H₁ , cong (∣_∣₂ ∘ func) H₂ ∣₁)
        (effective $ compPath Hi $ symPath Hj))
    , (toPathP $ squash₂ _ _ _ _))
    (representative f)
  where open DirectedDiagram (termChain ℒ n l) using (_≃_)
        open DirectedDiagramLanguage (languageChain ℒ) using (functionsᴰ)
        open DirectedDiagram (functionsᴰ l) using (representative; effective)
termComparisonFiber {ℒ} {n} {l} (app g s) =
  let (f , Hf) = termComparisonFiber g
      (t , Ht) = termComparisonFiber s in
  elim2→Set {P = λ _ _ → fiber termComparison ∣ app g s ∣₂}
    (λ _ _ → isSetΣ squash/ $ λ _ → isProp→isSet $ squash₂ _ _)
    (λ ((i , fᵢ) , Hi) ((j , tⱼ) , Hj) →
      let
      fᵢ₊ⱼ = morᶠ (≤⇒≤₃ $ m≤m+n _ _) fᵢ
      tᵢ₊ⱼ = morᵗ (≤⇒≤₃ $ m≤n+m _ _) tⱼ
      eqf : [ i + j , fᵢ₊ⱼ ] ≡ₚ f
      eqf = (flip compPath) Hi $ eq/ _ _ $ ∣_∣₁ $
        ( i + j , fᵢ₊ⱼ , (≤⇒≤₃ $ ≤-refl) , (≤⇒≤₃ $ m≤m+n _ _)
        , (sym $ (flip cong-app) fᵢ $ mapTermMorph-functorial $ subst (λ x → morph _ ≡ x ◯ morph _) (sym endomorph≡id) refl)
        , refl)
      eqt : [ i + j , tᵢ₊ⱼ ] ≡ₚ t
      eqt = (flip compPath) Hj $ eq/ _ _ $ ∣_∣₁ $
        ( i + j , tᵢ₊ⱼ , (≤⇒≤₃ $ ≤-refl) , (≤⇒≤₃ $ m≤n+m _ _)
        , (sym $ (flip cong-app) tⱼ $ mapTermMorph-functorial $ subst (λ x → morph _ ≡ x ◯ morph _) (sym endomorph≡id) refl)
        , refl)
      in
      [ i + j , map2 app fᵢ₊ⱼ tᵢ₊ⱼ ]
    , {!   !})
    {!   !}
    {!   !}
    {!   !}
    (repᶠ f) (repᵗ t)
  where open DirectedDiagram (termChain ℒ n (suc l)) renaming (representative to repᶠ ; morph to morᶠ)
        open DirectedDiagram (termChain ℒ n 0)       renaming (representative to repᵗ ; morph to morᵗ)
