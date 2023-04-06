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
open DirectedDiagram using (Colimit; Coproduct)
open Cocone using (universalMap)
open import FOL.Language.DirectedDiagram using (DirectedDiagramLanguage; CoconeLanguage)
open CoconeLanguage using (compat)

open import Cubical.Core.Primitives renaming (_≡_ to _≡ₚ_)
open import Cubical.Foundations.Prelude
  using (cong₂; isProp; isSet; isProp→isSet; toPathP; step-≡; _≡⟨⟩_; _∎)
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.HLevels using (isSetΣ; isSet→isGroupoid)
open import Cubical.HITs.SetQuotients using (eq/; [_]; squash/)
open import Cubical.HITs.PropositionalTruncation
  using (∣_∣₁; squash₁; elim; elim→Set; elim2→Set)
open import CubicalExt.HITs.SetTruncation
  using (∥_∥₂; ∣_∣₂; squash₂; rec; rec2; elim2; recComp2; map; map2; map-functorial)
open import Cubical.Data.Equality
  using (eqToPath; pathToEq; reflPath; symPath; compPath; congPath)
open import Cubical.Data.Sigma using (ΣPathP) renaming (_×_ to infixr 3 _×_)

open import StdlibExt.Data.Nat
open import Data.Nat.Properties
open import Function using (flip; _$_; _∘_; _∘₂_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong-app; subst)

abstract
  mapTermMorph-functorial : ∀ {ℒ₁ ℒ₂ ℒ₃ : Language {u}} {n l : ℕ}
    {F₁ : ℒ₁ ⟶ ℒ₂} {F₂ : ℒ₂ ⟶ ℒ₃} {F₃ : ℒ₁ ⟶ ℒ₃} → F₃ ≡ F₂ ◯ F₁ →
    (map $ termMorph F₃ {n} {l}) ≡ (map $ termMorph F₂) ∘ (map $ termMorph F₁)
  mapTermMorph-functorial H = trans (cong (map ∘ λ t → termMorph t) H)
    $ trans (cong map $ termMorphComp _ _)
    $ pathToEq $ map-functorial _ _
  
  termMorph-distrib-app : ∀ {ℒ₁ ℒ₂ : Language {u}} {n l : ℕ} {F : ℒ₁ ⟶ ℒ₂}
    (f : ∥ Termₗ ℒ₁ n (suc l) ∥₂) (t : ∥ Termₗ ℒ₁ n 0 ∥₂) →
    map (termMorph F) (map2 app f t) ≡ₚ map2 app (map (termMorph F) f) (map (termMorph F) t)
  termMorph-distrib-app = elim2 (λ _ _ → isSet→isGroupoid squash₂ _ _) (λ _ _ → reflPath)

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

_ : ∀ {ℒ n l i} (t : ∥ Termₗ ([ i ]-language ℒ) n l ∥₂) →
  termComparison [ i , t ] ≡ₚ map (termMorph $ languageCanonicalMorph i) t
_ = λ _ → reflPath

private
  abstract
    _↑ʳ_ : ∀ {ℒ n l i} → ∥ Termₗ ([ i ]-language ℒ) n l ∥₂ → (j : ℕ) → ∥ Termₗ ([ i + j ]-language ℒ) n l ∥₂
    _↑ʳ_ {ℒ} {n} {l} t _ = mor (≤⇒≤₃ $ m≤m+n _ _) t
      where open DirectedDiagram (termChain ℒ n l) renaming (morph to mor)

    _↑ˡ_ : ∀ {ℒ n l j} → ∥ Termₗ ([ j ]-language ℒ) n l ∥₂ → (i : ℕ) → ∥ Termₗ ([ i + j ]-language ℒ) n l ∥₂
    _↑ˡ_ {ℒ} {n} {l} t _ = mor (≤⇒≤₃ $ m≤n+m _ _) t
      where open DirectedDiagram (termChain ℒ n l) renaming (morph to mor)

    _≡↑ʳ_ : ∀ {ℒ n l i} {tᵢ : ∥ Termₗ ([ i ]-language ℒ) n l ∥₂} {t : Colimit (termChain ℒ n l)} →
      [ i , tᵢ ] ≡ₚ t → (j : ℕ) → [ i + j , tᵢ ↑ʳ j ] ≡ₚ t
    _≡↑ʳ_ {ℒ} {n} {l} {i} {tᵢ} H j = (flip compPath) H $ eq/ _ _
      ∣ i + j , tᵢ ↑ʳ j , ≤⇒≤₃ ≤-refl , ≤⇒≤₃ (m≤m+n _ _)
      , (sym $ (flip cong-app) tᵢ $ mapTermMorph-functorial
             $ subst (λ x → morph _ ≡ x ◯ morph _) (sym endomorph≡id) refl)
      , refl
      ∣₁

    _≡↑ˡ_ : ∀ {ℒ n l j} {tⱼ : ∥ Termₗ ([ j ]-language ℒ) n l ∥₂} {t : Colimit (termChain ℒ n l)} →
      [ j , tⱼ ] ≡ₚ t → (i : ℕ) → [ i + j , tⱼ ↑ˡ i ] ≡ₚ t
    _≡↑ˡ_ {ℒ} {n} {l} {j} {tⱼ} H i = (flip compPath) H $ eq/ _ _
      ∣ i + j , tⱼ ↑ˡ i , ≤⇒≤₃ ≤-refl , ≤⇒≤₃ (m≤n+m _ _)
      , (sym $ (flip cong-app) tⱼ $ mapTermMorph-functorial
             $ subst (λ x → morph _ ≡ x ◯ morph _) (sym endomorph≡id) refl)
      , refl
      ∣₁

  app₂ : ∀ {ℒ n l i j}
    (f : ∥ Termₗ ([ i ]-language ℒ) n (suc l) ∥₂)
    (t : ∥ Termₗ ([ j ]-language ℒ) n 0 ∥₂) →
    ∥ Termₗ ([ i + j ]-language ℒ) n l ∥₂
  app₂ {ℒ} {n} {l} {i} {j} f t = map2 app (f ↑ʳ j) (t ↑ˡ i)

termComparisonFiber : ∀ {ℒ n l} (t : Termₗ (∞-language ℒ) n l) → fiber termComparison ∣ t ∣₂
termComparisonFiber (var k) = [ 0 , ∣ var k ∣₂ ] , reflPath
termComparisonFiber {ℒ} {n} {l} (func f) =
  elim→Set {P = λ _ → fiber termComparison ∣ func f ∣₂}
    (λ _ → isSetΣ squash/ $ λ _ → isProp→isSet $ squash₂ _ _)
    (λ ((i , fᵢ) , H) → [ i , ∣ func fᵢ ∣₂ ] , congPath (∣_∣₂ ∘ func) H)
    (λ ((i , fᵢ) , Hi) ((j , fⱼ) , Hj) → ΣPathP $
      (eq/ _ _ $ elim {P = λ _ → (i , ∣ func fᵢ ∣₂) ≃ (j , ∣ func fⱼ ∣₂)}
        (λ _ → squash₁)
        (λ (k , fₖ , i~k , j~k , H₁ , H₂) →
          ∣ k , ∣ func fₖ ∣₂ , i~k , j~k , cong (∣_∣₂ ∘ func) H₁ , cong (∣_∣₂ ∘ func) H₂ ∣₁)
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
      [ i + j , app₂ fᵢ tⱼ ]
    , ( map (termMorph _) (app₂ fᵢ tⱼ)
          ≡⟨ termMorph-distrib-app _ _ ⟩
        map2 app (termComparison [ i + j , fᵢ ↑ʳ j ]) (termComparison [ i + j , tⱼ ↑ˡ i ])
          ≡⟨ cong₂ (map2 app) (compPath (congPath termComparison (Hi ≡↑ʳ j)) Hf)
                              (compPath (congPath termComparison (Hj ≡↑ˡ i)) Ht) ⟩
        ∣ app g s ∣₂ ∎))
    (λ ((i , fᵢ) , Hi) ((j , fⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
      (eq/ _ _ $ elim {P = λ _ → (i + k , app₂ fᵢ tₖ) ≃ (j + k , app₂ fⱼ tₖ)}
        (λ _ → squash₁)
        (λ (o , fₒ , i~o , j~o , H₁ , H₂) →
          ∣ o + k , app₂ fₒ tₖ
          , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ i~o)
          , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ j~o)
          , pathToEq (
            map (termMorph {!   !}) (app₂ fᵢ tₖ)
              ≡⟨ {!   !} ⟩
            map2 app (map (termMorph {!   !}) fᵢ) (map (termMorph {!   !}) tₖ)
              ≡⟨ {!   !} ⟩
            app₂ fₒ tₖ ∎)
          , {!   !}
          ∣₁)
        (effᶠ $ compPath Hi $ symPath Hj))
    , (toPathP $ squash₂ _ _ _ _))
    (λ ((i , fᵢ) , Hi) ((j , tⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
      {!   !}
    , (toPathP $ squash₂ _ _ _ _))
    {!   !} --(λ ((i , fᵢ) , Hi) ((j , fⱼ) , Hj) ((k , fₖ) , Hk) ((o , tₒ) , Ho) → {!   !})
    (repᶠ f) (repᵗ t)
  where open DirectedDiagram (termChain ℒ n (suc l)) using () renaming (morph to morᶠ; representative to repᶠ; effective to effᶠ)
        open DirectedDiagram (termChain ℒ n 0)       using () renaming (morph to morᵗ; representative to repᵗ; effective to effᵗ)
        open DirectedDiagram (termChain ℒ n l) using (_≃_)
