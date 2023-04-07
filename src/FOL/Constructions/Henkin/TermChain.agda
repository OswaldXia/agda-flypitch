{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module FOL.Constructions.Henkin.TermChain u where
open import FOL.Constructions.Henkin.LanguageChain u
  renaming (obj to langObj ; morph to langMorph; functorial to langFunctorial)
open import FOL.Language using (Language)
open import FOL.Bounded.Base using (Termₗ)
open Termₗ

import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_) renaming (_∘_ to _◯_)
open LHom.Bounded using (termMorph)
open LHom.BoundedProperties

open import Tools.DirectedDiagram using (ℕᴰ; DirectedDiagram; Cocone)
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
  using (eqToPath; pathToEq; reflPath; symPath; compPath; congPath; substPath)
open import Cubical.Data.Sigma using (ΣPathP) renaming (_×_ to infixr 3 _×_)

open import StdlibExt.Data.Nat
open import Data.Nat.Properties
open import Function using (flip; _$_; _∘_; _∘₂_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong-app; subst)

abstract
  map-$-termMorph-functorial : ∀ {ℒ₁ ℒ₂ ℒ₃ : Language {u}} {n l : ℕ}
    {F₁ : ℒ₁ ⟶ ℒ₂} {F₂ : ℒ₂ ⟶ ℒ₃} {F₃ : ℒ₁ ⟶ ℒ₃} → F₃ ≡ F₂ ◯ F₁ →
    (map $ termMorph F₃ {n} {l}) ≡ (map $ termMorph F₂) ∘ (map $ termMorph F₁)
  map-$-termMorph-functorial H = trans (cong (map ∘ λ t → termMorph t) H)
    $ trans (cong map $ termMorphComp _ _)
    $ pathToEq $ map-functorial _ _

termChain : ∀ ℒ n l → DirectedDiagram ℕᴰ
termChain ℒ n l = record
  { obj = λ k → ∥ Termₗ ([ k ]-language ℒ) n l ∥₂
  ; morph = λ i≤j → map $ termMorph $ langMorph i≤j
  ; functorial = map-$-termMorph-functorial langFunctorial
  }

coconeOfTermChain : ∀ ℒ n l → Cocone (termChain ℒ n l)
coconeOfTermChain ℒ n l = record
  { Vertex = ∥ Termₗ (∞-language ℒ ) n l ∥₂
  ; isSetVertex = squash₂
  ; map = λ i → map $ termMorph $ languageCanonicalMorph i
  ; compat = λ {i} i~j → map-$-termMorph-functorial (coconeOfLanguageChain .compat i~j)
  }

module _ {ℒ n l} where
  open DirectedDiagram (termChain ℒ n l) using (obj; morph; functorial; Colimit) public

  termComparison : Colimit → ∥ Termₗ (∞-language ℒ) n l ∥₂
  termComparison = universalMap (coconeOfTermChain ℒ n l)

  _ : ∀ {i} (t : obj i) → termComparison [ i , t ] ≡ₚ map (termMorph $ languageCanonicalMorph i) t
  _ = λ _ → reflPath

  abstract
    _↑ʳ_ : ∀ {i} → obj i → (j : ℕ) → obj (i + j)
    _↑ʳ_ t _ = morph (≤⇒≤₃ $ m≤m+n _ _) t

    _↑ˡ_ : ∀ {j} → obj j → (i : ℕ) → obj (i + j)
    _↑ˡ_ t _ = morph (≤⇒≤₃ $ m≤n+m _ _) t

    _≡↑ʳ_ : ∀ {i} {tᵢ : obj i} {t : Colimit} →
      [ i , tᵢ ] ≡ₚ t → (j : ℕ) → [ i + j , tᵢ ↑ʳ j ] ≡ₚ t
    _≡↑ʳ_ {i} {tᵢ} H j = (flip compPath) H $ eq/ _ _
      ∣ i + j , tᵢ ↑ʳ j , ≤⇒≤₃ ≤-refl , ≤⇒≤₃ (m≤m+n _ _)
      , (sym $ (flip cong-app) tᵢ $ map-$-termMorph-functorial
             $ subst (λ x → langMorph _ ≡ x ◯ langMorph _) (sym endomorph≡id) refl)
      , refl
      ∣₁

    _≡↑ˡ_ : ∀ {j} {tⱼ : obj j} {t : Colimit} →
      [ j , tⱼ ] ≡ₚ t → (i : ℕ) → [ i + j , tⱼ ↑ˡ i ] ≡ₚ t
    _≡↑ˡ_ {j} {tⱼ} H i = (flip compPath) H $ eq/ _ _
      ∣ i + j , tⱼ ↑ˡ i , ≤⇒≤₃ ≤-refl , ≤⇒≤₃ (m≤n+m _ _)
      , (sym $ (flip cong-app) tⱼ $ map-$-termMorph-functorial
             $ subst (λ x → langMorph _ ≡ x ◯ langMorph _) (sym endomorph≡id) refl)
      , refl
      ∣₁

app₂ : ∀ {ℒ n l i j} (f : obj {ℒ} {n} {suc l} i) (t : obj {ℒ} {n} {0} j) → obj (i + j)
app₂ {_} {_} {_} {i} {j} f t = map2 app (f ↑ʳ j) (t ↑ˡ i)

abstract
  termMorph-$-langMorph-functorial : ∀ {ℒ n l x y z} .{f₁ : x ≤₃ y} .{f₂ : y ≤₃ z} .{f₃ : x ≤₃ z} → 
    (termMorph $ langMorph {ℒ} f₃) {n} {l} ≡ (termMorph $ langMorph f₂) ∘ (termMorph $ langMorph f₁)
  termMorph-$-langMorph-functorial {f₁ = f₁} {f₂ = f₂} = trans (cong (λ t → termMorph t) langFunctorial)
    (termMorphComp (langMorph f₂) (langMorph f₁))

  map-$-termMorph-distrib-app : ∀ {ℒ₁ ℒ₂ : Language {u}} {n l : ℕ} {F : ℒ₁ ⟶ ℒ₂}
    (f : ∥ Termₗ ℒ₁ n (suc l) ∥₂) (t : ∥ Termₗ ℒ₁ n 0 ∥₂) →
    map (termMorph F) (map2 app f t) ≡ₚ map2 app (map (termMorph F) f) (map (termMorph F) t)
  map-$-termMorph-distrib-app = elim2 (λ _ _ → isSet→isGroupoid squash₂ _ _) (λ _ _ → reflPath)

  map-$-termMorph-distrib-app₂ : ∀ {ℒ n l i j k}
    .{f₀ : i + j ≤₃ k} .{f₁ : i ≤₃ k} .{f₂ : j ≤₃ k}
    (f : ∥ Termₗ ([ i ]-language ℒ) n (suc l) ∥₂)
    (t : ∥ Termₗ ([ j ]-language ℒ) n 0 ∥₂) →
    map (termMorph $ langMorph f₀) (app₂ f t) ≡ₚ
    map2 app (map (termMorph $ langMorph f₁) f) (map (termMorph $ langMorph f₂) t)
  map-$-termMorph-distrib-app₂ =
    elim2 (λ _ _ → isSet→isGroupoid squash₂ _ _) λ a b → cong₂ (∣_∣₂ ∘₂ app)
      (eqToPath $ sym $ cong-app termMorph-$-langMorph-functorial a)
      (eqToPath $ sym $ cong-app termMorph-$-langMorph-functorial b)

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
          ≡⟨ map-$-termMorph-distrib-app _ _ ⟩
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
            morph _ (app₂ fᵢ tₖ)
              ≡⟨ map-$-termMorph-distrib-app₂ _ _ ⟩
            map2 app (morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ i~o) (m≤m+n _ _)) fᵢ)
                     (morph (≤⇒≤₃ $ m≤n+m _ _) tₖ)
              ≡⟨ cong₂ (map2 app)
                ( morph _ fᵢ        ≡⟨ {!   !} ⟩
                  morph i~o fᵢ ↑ʳ k ≡⟨ eqToPath $ cong (_↑ʳ k) H₁ ⟩
                  fₒ ↑ʳ k                             ∎)
                {!   !} ⟩
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
