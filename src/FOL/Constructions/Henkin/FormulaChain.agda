{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module FOL.Constructions.Henkin.FormulaChain u where
open import FOL.Constructions.Henkin.LanguageChain u
  renaming (obj to langObj ; morph to langMorph; functorial to langFunctorial)
open import FOL.Constructions.Henkin.TermChain u as T
  using (termChain; termComparison; termComparisonFiber; termMorph-$-langMorph-functorial)
open import FOL.Language using (Language)
open import FOL.Bounded.Base using (Termₗ; Formulaₗ)
open Formulaₗ

import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_) renaming (_∘_ to _◯_)
open LHom.Bounded using (termMorph; formulaMorph)
open LHom.BoundedProperties

open import Tools.DirectedDiagram using (ℕᴰ; DirectedDiagram; Cocone)
open Cocone using (universalMap)
open import FOL.Language.DirectedDiagram using (DirectedDiagramLanguage; CoconeLanguage)
open CoconeLanguage using (compat)

open import Cubical.Core.Primitives renaming (_≡_ to _≡ₚ_)
open import Cubical.Foundations.Prelude
  using (cong₂; isProp; isSet; isProp→isSet; toPathP; step-≡; _≡⟨⟩_; _∎; _≡$_)
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.HLevels using (isSetΣ; isSet→isGroupoid)
open import Cubical.Data.Equality
  using (eqToPath; pathToEq; reflPath; symPath; compPath; congPath; substPath)
open import Cubical.Data.Sigma using (ΣPathP) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.SetQuotients
  using ([_]; eq/; squash/)
open import Cubical.HITs.PropositionalTruncation
  using (∣_∣₁; squash₁; elim; elim→Set; elim2→Set)
open import CubicalExt.HITs.SetTruncation
  using (∥_∥₂; ∣_∣₂; squash₂; rec; rec2; elim2; recComp2; map; map2; map-functorial)

open import StdlibExt.Data.Nat
open import Data.Nat.Properties
open import Function using (flip; _$_; _∘_; _∘₂_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong-app; subst)

abstract
  map-$-formulaMorph-functorial : ∀ {ℒ₁ ℒ₂ ℒ₃ : Language {u}} {n l : ℕ}
    {F₁ : ℒ₁ ⟶ ℒ₂} {F₂ : ℒ₂ ⟶ ℒ₃} {F₃ : ℒ₁ ⟶ ℒ₃} → F₃ ≡ F₂ ◯ F₁ →
    (map $ formulaMorph F₃ {n} {l}) ≡ (map $ formulaMorph F₂) ∘ (map $ formulaMorph F₁)
  map-$-formulaMorph-functorial H = trans (cong (map ∘ λ t → formulaMorph t) H)
    $ trans (cong map $ formulaMorphComp _ _)
    $ pathToEq $ map-functorial _ _

formulaChain : ∀ ℒ n l → DirectedDiagram ℕᴰ
formulaChain ℒ n l = record
  { obj = λ k → ∥ Formulaₗ ([ k ]-language ℒ) n l ∥₂
  ; morph = λ i≤j → map $ formulaMorph $ langMorph i≤j
  ; functorial = map-$-formulaMorph-functorial langFunctorial
  }

coconeOfFormulaChain : ∀ ℒ n l → Cocone (formulaChain ℒ n l)
coconeOfFormulaChain ℒ n l = record
  { Vertex = ∥ Formulaₗ (∞-language ℒ ) n l ∥₂
  ; isSetVertex = squash₂
  ; map = λ i → map $ formulaMorph $ languageCanonicalMorph i
  ; compat = λ i~j → map-$-formulaMorph-functorial (coconeOfLanguageChain .compat i~j)
  }

module _ {ℒ n l} where
  open DirectedDiagram (formulaChain ℒ n l) using (obj; morph; functorial; Colimit; representative; effective) public

  formulaComparison : Colimit → ∥ Formulaₗ (∞-language ℒ) n l ∥₂
  formulaComparison = universalMap (coconeOfFormulaChain ℒ n l)

  _ : ∀ {i} (φ : obj i) → formulaComparison [ i , φ ] ≡ₚ map (formulaMorph $ languageCanonicalMorph i) φ
  _ = λ _ → reflPath

  _↑ʳ_ : ∀ {i} → obj i → (j : ℕ) → obj (i + j)
  φ ↑ʳ _ = morph (≤⇒≤₃ $ m≤m+n _ _) φ

  _↑ˡ_ : ∀ {j} → obj j → (i : ℕ) → obj (i + j)
  φ ↑ˡ _ = morph (≤⇒≤₃ $ m≤n+m _ _) φ

  abstract
    _≡↑ʳ_ : ∀ {i} {tᵢ : obj i} {t : Colimit} →
      [ i , tᵢ ] ≡ₚ t → (j : ℕ) → [ i + j , tᵢ ↑ʳ j ] ≡ₚ t
    _≡↑ʳ_ {i} {tᵢ} H j = (flip compPath) H $ eq/ _ _
      ∣ i + j , tᵢ ↑ʳ j , ≤⇒≤₃ ≤-refl , ≤⇒≤₃ (m≤m+n _ _)
      , (sym $ (flip cong-app) tᵢ $ map-$-formulaMorph-functorial
             $ subst (λ x → langMorph _ ≡ x ◯ langMorph _) (sym endomorph≡id) refl)
      , refl
      ∣₁

    _≡↑ˡ_ : ∀ {j} {tⱼ : obj j} {t : Colimit} →
      [ j , tⱼ ] ≡ₚ t → (i : ℕ) → [ i + j , tⱼ ↑ˡ i ] ≡ₚ t
    _≡↑ˡ_ {j} {tⱼ} H i = (flip compPath) H $ eq/ _ _
      ∣ i + j , tⱼ ↑ˡ i , ≤⇒≤₃ ≤-refl , ≤⇒≤₃ (m≤n+m _ _)
      , (sym $ (flip cong-app) tⱼ $ map-$-formulaMorph-functorial
             $ subst (λ x → langMorph _ ≡ x ◯ langMorph _) (sym endomorph≡id) refl)
      , refl
      ∣₁

appᵣ↑ : ∀ {ℒ n l i j} → obj {ℒ} {n} {suc l} i → T.obj {ℒ} {n} {0} j → obj (i + j)
appᵣ↑ {_} {_} {_} {i} {j} r t = map2 appᵣ (r ↑ʳ j) (t T.↑ˡ i)

abstract
  formulaMorph-$-langMorph-functorial : ∀ {ℒ n l x y z} .{f₁ : x ≤₃ y} .{f₂ : y ≤₃ z} .{f₃ : x ≤₃ z} → 
    (formulaMorph $ langMorph {ℒ} f₃) {n} {l} ≡ (formulaMorph $ langMorph f₂) ∘ (formulaMorph $ langMorph f₁)
  formulaMorph-$-langMorph-functorial {f₁ = f₁} {f₂ = f₂} = trans (cong (λ φ → formulaMorph φ) langFunctorial)
    (formulaMorphComp (langMorph f₂) (langMorph f₁))

  map-$-formulaMorph-distrib-appᵣ : ∀ {ℒ₁ ℒ₂ : Language {u}} {n l : ℕ} {F : ℒ₁ ⟶ ℒ₂}
    (r : ∥ Formulaₗ ℒ₁ n (suc l) ∥₂) (t : ∥ Termₗ ℒ₁ n 0 ∥₂) →
    map (formulaMorph F) (map2 appᵣ r t) ≡ₚ map2 appᵣ (map (formulaMorph F) r) (map (termMorph F) t)
  map-$-formulaMorph-distrib-appᵣ = elim2 (λ _ _ → isSet→isGroupoid squash₂ _ _) (λ _ _ → reflPath)

  map-$-formulaMorph-distrib-appᵣ↑ : ∀ {ℒ n l i j k} .{f₀ : i + j ≤₃ k} .{f₁ : i ≤₃ k} .{f₂ : j ≤₃ k}
    (r : obj {ℒ} {n} {suc l} i) (t : T.obj {ℒ} {n} {0} j) →
    map (formulaMorph $ langMorph f₀) (appᵣ↑ r t) ≡ₚ
    map2 appᵣ (map (formulaMorph $ langMorph f₁) r) (map (termMorph $ langMorph f₂) t)
  map-$-formulaMorph-distrib-appᵣ↑ =
    elim2 (λ _ _ → isSet→isGroupoid squash₂ _ _) λ a b → cong₂ (∣_∣₂ ∘₂ appᵣ)
      (eqToPath $ sym $ cong-app formulaMorph-$-langMorph-functorial a)
      (eqToPath $ sym $ cong-app termMorph-$-langMorph-functorial b)

  isSetFiber : ∀ {ℒ n l} {φ : Formulaₗ (∞-language ℒ) n l} → isSet (fiber formulaComparison ∣ φ ∣₂)
  isSetFiber = isSetΣ squash/ $ λ _ → isProp→isSet $ squash₂ _ _

  formulaComparisonFiber : ∀ {ℒ n l} (φ : Formulaₗ (∞-language ℒ) n l) → fiber formulaComparison ∣ φ ∣₂
  formulaComparisonFiber ⊥ = [ 0 , ∣ ⊥ ∣₂ ] , reflPath
  formulaComparisonFiber {ℒ} {n} {l} (rel R) =
    elim→Set {P = λ _ → fiber formulaComparison ∣ rel R ∣₂}
      (λ _ → isSetFiber)
      (λ ((i , Rᵢ) , H) → [ i , ∣ rel Rᵢ ∣₂ ] , congPath (∣_∣₂ ∘ rel) H)
      (λ ((i , Rᵢ) , Hi) ((j , Rⱼ) , Hj) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i , ∣ rel Rᵢ ∣₂) ≃ (j , ∣ rel Rⱼ ∣₂)}
          (λ _ → squash₁)
          (λ (k , Rₖ , i~k , j~k , H₁ , H₂) →
            ∣ k , ∣ rel Rₖ ∣₂ , i~k , j~k , cong (∣_∣₂ ∘ rel) H₁ , cong (∣_∣₂ ∘ rel) H₂ ∣₁)
          (eff $ compPath Hi $ symPath Hj))
      , (toPathP $ squash₂ _ _ _ _))
      (rep R)
    where open DirectedDiagramLanguage (languageChain ℒ) using (relationsᴰ)
          open DirectedDiagram (relationsᴰ l) using () renaming (representative to rep; effective to eff)
          open DirectedDiagram (formulaChain ℒ n l) using (_≃_)
  formulaComparisonFiber {ℒ} {n} {l} (appᵣ ρ τ) =
    let (r , Hr) = formulaComparisonFiber ρ
        (t , Ht) = termComparisonFiber    τ in
    elim2→Set {P = λ _ _ → fiber formulaComparison ∣ appᵣ ρ τ ∣₂}
      (λ _ _ → isSetFiber)
      (λ ((i , rᵢ) , Hi) ((j , tⱼ) , Hj) →
        [ i + j , appᵣ↑ rᵢ tⱼ ]
      , ( map (formulaMorph _) (appᵣ↑ rᵢ tⱼ)
            ≡⟨ map-$-formulaMorph-distrib-appᵣ _ _ ⟩
          map2 appᵣ (formulaComparison [ i + j , rᵢ ↑ʳ j ]) (termComparison [ i + j , tⱼ T.↑ˡ i ])
            ≡⟨ cong₂ (map2 appᵣ) (compPath (congPath formulaComparison (Hi ≡↑ʳ j)) Hr)
                                 (compPath (congPath termComparison (Hj T.≡↑ˡ i)) Ht) ⟩
          ∣ appᵣ ρ τ ∣₂ ∎))
      (λ ((i , rᵢ) , Hi) ((j , rⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i + k , appᵣ↑ rᵢ tₖ) ≃ (j + k , appᵣ↑ rⱼ tₖ)}
          (λ _ → squash₁)
          (λ (o , rₒ , i~o , j~o , H₁ , H₂) →
            ∣ o + k , appᵣ↑ rₒ tₖ
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ i~o)
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ j~o)
            , (pathToEq $
                morph _ (appᵣ↑ rᵢ tₖ)
                  ≡⟨ map-$-formulaMorph-distrib-appᵣ↑ _ _ ⟩
                map2 appᵣ (morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ i~o) (m≤m+n _ _)) rᵢ) (T.morph _ tₖ)
                  ≡⟨ cong₂ (map2 appᵣ)
                    ( morph _ rᵢ        ≡⟨ eqToPath functorial ≡$ rᵢ ⟩
                      morph i~o rᵢ ↑ʳ k ≡⟨ eqToPath $ cong (_↑ʳ k) H₁ ⟩
                      rₒ ↑ʳ k           ∎
                    ) reflPath ⟩
                appᵣ↑ rₒ tₖ ∎)
            , (pathToEq $
                morph _ (appᵣ↑ rⱼ tₖ)
                  ≡⟨ map-$-formulaMorph-distrib-appᵣ↑ _ _ ⟩
                map2 appᵣ (morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤m+n _ _)) rⱼ) (T.morph _ tₖ)
                  ≡⟨ cong₂ (map2 appᵣ)
                    ( morph _ rⱼ        ≡⟨ eqToPath functorial ≡$ rⱼ ⟩
                      morph j~o rⱼ ↑ʳ k ≡⟨ eqToPath $ cong (_↑ʳ k) H₂ ⟩
                      rₒ ↑ʳ k           ∎
                    ) reflPath ⟩
                appᵣ↑ rₒ tₖ ∎)
            ∣₁)
          (effʳ $ compPath Hi $ symPath Hj))
      , (toPathP $ squash₂ _ _ _ _))
      (λ ((i , rᵢ) , Hi) ((j , tⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i + j , appᵣ↑ rᵢ tⱼ) ≃ (i + k , appᵣ↑ rᵢ tₖ)}
          (λ _ → squash₁)
          (λ (o , tₒ , j~o , k~o , H₁ , H₂) →
            ∣ i + o , appᵣ↑ rᵢ tₒ
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ j~o)
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ k~o)
            , (pathToEq $
                morph _ (appᵣ↑ rᵢ tⱼ)
                  ≡⟨ map-$-formulaMorph-distrib-appᵣ↑ _ _ ⟩
                map2 appᵣ (morph _ rᵢ) (T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤n+m _ _)) tⱼ)
                  ≡⟨ cong₂ (map2 appᵣ) reflPath (
                    T.morph _ tⱼ          ≡⟨ eqToPath T.functorial ≡$ tⱼ ⟩
                    T.morph j~o tⱼ T.↑ˡ i ≡⟨ eqToPath $ cong (T._↑ˡ i) H₁ ⟩
                    tₒ T.↑ˡ i           ∎) ⟩
                appᵣ↑ rᵢ tₒ ∎)
            , (pathToEq $
                morph _ (appᵣ↑ rᵢ tₖ)
                  ≡⟨ map-$-formulaMorph-distrib-appᵣ↑ _ _ ⟩
                map2 appᵣ (morph _ rᵢ) (T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ k~o) (m≤n+m _ _)) tₖ)
                  ≡⟨ cong₂ (map2 appᵣ) reflPath (
                    T.morph _ tₖ          ≡⟨ eqToPath T.functorial ≡$ tₖ ⟩
                    T.morph k~o tₖ T.↑ˡ i ≡⟨ eqToPath $ cong (T._↑ˡ i) H₂ ⟩
                    tₒ T.↑ˡ i           ∎) ⟩
                appᵣ↑ rᵢ tₒ ∎)
            ∣₁)
          (effᵗ $ compPath Hj $ symPath Hk))
      , (toPathP $ squash₂ _ _ _ _))
      (λ _ _ _ _ → toPathP $ isSetFiber _ _ _ _)
      (repʳ r) (repᵗ t)
    where open DirectedDiagram (formulaChain ℒ n (suc l)) using () renaming (representative to repʳ; effective to effʳ)
          open DirectedDiagram (termChain ℒ n 0)          using () renaming (representative to repᵗ; effective to effᵗ)
          open DirectedDiagram (formulaChain ℒ n l) using (_≃_)
  formulaComparisonFiber (t₁ ≈ t₂) = {!   !}
  formulaComparisonFiber (φ₁ ⇒ φ₂) = {!   !}
  formulaComparisonFiber {ℒ} {n} {l} (∀' ψ) =
    let (φ , Hφ) = formulaComparisonFiber ψ in
    elim→Set {P = λ _ → fiber formulaComparison ∣ ∀' ψ ∣₂}
      (λ _ → isSetFiber)
      (λ ((i , φᵢ) , H) → [ i , map ∀'_ φᵢ ] , {!   !})
      (λ ((i , φᵢ) , Hi) ((j , φⱼ) , Hj) → {!   !})
      (representative φ)
    where open DirectedDiagram (formulaChain ℒ n l) using (_≃_)
