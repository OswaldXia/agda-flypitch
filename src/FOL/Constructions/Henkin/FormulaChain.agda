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
  using (∣_∣₁; squash₁; elim→Set; elim2→Set)
  renaming (elim to elim₁)
open import CubicalExt.HITs.SetTruncation
  using (∥_∥₂; ∣_∣₂; squash₂; rec; rec2; elim2; recComp2; map; map2; map-functorial)
  renaming (elim to elim₂)

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

_≈↑_ : ∀ {ℒ n i j} → T.obj {ℒ} {n} {0} i → T.obj {ℒ} {n} {0} j → obj (i + j)
_≈↑_ {_} {_} {i} {j} t₁ t₂ = map2 _≈_ (t₁ T.↑ʳ j) (t₂ T.↑ˡ i)

abstract
  formulaMorph-$-langMorph-functorial : ∀ {ℒ n l x y z} .{f₁ : x ≤₃ y} .{f₂ : y ≤₃ z} .{f₃ : x ≤₃ z} → 
    (formulaMorph $ langMorph {ℒ} f₃) {n} {l} ≡ (formulaMorph $ langMorph f₂) ∘ (formulaMorph $ langMorph f₁)
  formulaMorph-$-langMorph-functorial {f₁ = f₁} {f₂ = f₂} = trans (cong (λ φ → formulaMorph φ) langFunctorial)
    (formulaMorphComp (langMorph f₂) (langMorph f₁))

  map-$-formulaMorph-distrib-appᵣ : ∀ {ℒ₁ ℒ₂ : Language {u}} {n l : ℕ} {F : ℒ₁ ⟶ ℒ₂}
    (r : ∥ Formulaₗ ℒ₁ n (suc l) ∥₂) (t : ∥ Termₗ ℒ₁ n 0 ∥₂) →
    map (formulaMorph F) (map2 appᵣ r t) ≡ₚ map2 appᵣ (map (formulaMorph F) r) (map (termMorph F) t)
  map-$-formulaMorph-distrib-appᵣ = elim2 (λ _ _ → isSet→isGroupoid squash₂ _ _) (λ _ _ → reflPath)

  morph-distrib-appᵣ↑ : ∀ {ℒ n l i j k} .{f₀ : i + j ≤₃ k} .{f₁ : i ≤₃ k} .{f₂ : j ≤₃ k}
    (r : obj {ℒ} {n} {suc l} i) (t : T.obj {ℒ} {n} {0} j) →
    (morph f₀) (appᵣ↑ r t) ≡ₚ map2 appᵣ (morph f₁ r) (T.morph f₂ t)
  morph-distrib-appᵣ↑ = elim2 (λ _ _ → isSet→isGroupoid squash₂ _ _) λ a b → cong₂ (∣_∣₂ ∘₂ appᵣ)
    (eqToPath $ sym $ cong-app formulaMorph-$-langMorph-functorial a)
    (eqToPath $ sym $ cong-app termMorph-$-langMorph-functorial b)

  map-$-formulaMorph-distrib-≈ : ∀ {ℒ₁ ℒ₂ : Language {u}} {n : ℕ} {F : ℒ₁ ⟶ ℒ₂} (t₁ t₂ : ∥ Termₗ ℒ₁ n 0 ∥₂) →
    map (formulaMorph F) (map2 _≈_ t₁ t₂) ≡ₚ map2 _≈_ (map (termMorph F) t₁) (map (termMorph F) t₂)
  map-$-formulaMorph-distrib-≈ = elim2 (λ _ _ → isSet→isGroupoid squash₂ _ _) (λ _ _ → reflPath)

  morph-distrib-≈↑ : ∀ {ℒ n i j k} .{f₀ : i + j ≤₃ k} .{f₁ : i ≤₃ k} .{f₂ : j ≤₃ k}
    (t₁ : T.obj {ℒ} {n} {0} i) (t₂ : T.obj {ℒ} {n} {0} j) →
    (morph f₀) (t₁ ≈↑ t₂) ≡ₚ map2 _≈_ (T.morph f₁ t₁) (T.morph f₂ t₂)
  morph-distrib-≈↑ = elim2 (λ _ _ → isSet→isGroupoid squash₂ _ _) λ a b → cong₂ (∣_∣₂ ∘₂ _≈_)
    (eqToPath $ sym $ cong-app termMorph-$-langMorph-functorial a)
    (eqToPath $ sym $ cong-app termMorph-$-langMorph-functorial b)

  map-$-formulaMorph-∀'-comm : ∀ {ℒ₁ ℒ₂ : Language {u}} {n : ℕ} {F : ℒ₁ ⟶ ℒ₂}
    (φ : ∥ Formulaₗ ℒ₁ (suc n) 0 ∥₂) → map (formulaMorph F) (map ∀'_ φ) ≡ₚ map ∀'_ (map (formulaMorph F) φ)
  map-$-formulaMorph-∀'-comm = elim₂ (λ _ → isSet→isGroupoid squash₂ _ _) (λ _ → reflPath)

  isSetFiber : ∀ {ℒ n l} {φ : Formulaₗ (∞-language ℒ) n l} → isSet (fiber formulaComparison ∣ φ ∣₂)
  isSetFiber = isSetΣ squash/ $ λ _ → isProp→isSet $ squash₂ _ _

  formulaComparisonFiber : ∀ {ℒ n l} (φ : Formulaₗ (∞-language ℒ) n l) → fiber formulaComparison ∣ φ ∣₂
  formulaComparisonFiber ⊥ = [ 0 , ∣ ⊥ ∣₂ ] , reflPath
  formulaComparisonFiber {ℒ} {n} {l} (rel R) =
    elim→Set {P = λ _ → fiber formulaComparison ∣ rel R ∣₂}
      (λ _ → isSetFiber)
      (λ ((i , Rᵢ) , H) → [ i , ∣ rel Rᵢ ∣₂ ] , congPath (∣_∣₂ ∘ rel) H)
      (λ ((i , Rᵢ) , Hi) ((j , Rⱼ) , Hj) → ΣPathP $
        (eq/ _ _ $ elim₁ {P = λ _ → (i , ∣ rel Rᵢ ∣₂) ≃ (j , ∣ rel Rⱼ ∣₂)}
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
      (λ ((i , rᵢ) , Hi) ((j , tⱼ) , Hj) → [ i + j , appᵣ↑ rᵢ tⱼ ]
      , ( map (formulaMorph _) (appᵣ↑ rᵢ tⱼ)
            ≡⟨ map-$-formulaMorph-distrib-appᵣ _ _ ⟩
          map2 appᵣ (formulaComparison [ i + j , rᵢ ↑ʳ j ]) (termComparison [ i + j , tⱼ T.↑ˡ i ])
            ≡⟨ cong₂ (map2 appᵣ) (compPath (congPath formulaComparison (Hi ≡↑ʳ j)) Hr)
                                 (compPath (congPath termComparison (Hj T.≡↑ˡ i)) Ht) ⟩
          ∣ appᵣ ρ τ ∣₂ ∎))
      (λ ((i , rᵢ) , Hi) ((j , rⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim₁ {P = λ _ → (i + k , appᵣ↑ rᵢ tₖ) ≃ (j + k , appᵣ↑ rⱼ tₖ)}
          (λ _ → squash₁)
          (λ (o , rₒ , i~o , j~o , H₁ , H₂) →
            ∣ o + k , appᵣ↑ rₒ tₖ
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ i~o)
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ j~o)
            , (pathToEq $
                morph _ (appᵣ↑ rᵢ tₖ)
                  ≡⟨ morph-distrib-appᵣ↑ _ _ ⟩
                map2 appᵣ (morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ i~o) (m≤m+n _ _)) rᵢ) (T.morph _ tₖ)
                  ≡⟨ cong₂ (map2 appᵣ)
                    ( morph _ rᵢ        ≡⟨ eqToPath functorial ≡$ rᵢ ⟩
                      morph i~o rᵢ ↑ʳ k ≡⟨ eqToPath $ cong (_↑ʳ k) H₁ ⟩
                      rₒ ↑ʳ k           ∎
                    ) reflPath ⟩
                appᵣ↑ rₒ tₖ ∎)
            , (pathToEq $
                morph _ (appᵣ↑ rⱼ tₖ)
                  ≡⟨ morph-distrib-appᵣ↑ _ _ ⟩
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
        (eq/ _ _ $ elim₁ {P = λ _ → (i + j , appᵣ↑ rᵢ tⱼ) ≃ (i + k , appᵣ↑ rᵢ tₖ)}
          (λ _ → squash₁)
          (λ (o , tₒ , j~o , k~o , H₁ , H₂) →
            ∣ i + o , appᵣ↑ rᵢ tₒ
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ j~o)
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ k~o)
            , (pathToEq $
                morph _ (appᵣ↑ rᵢ tⱼ)
                  ≡⟨ morph-distrib-appᵣ↑ _ _ ⟩
                map2 appᵣ (morph _ rᵢ) (T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤n+m _ _)) tⱼ)
                  ≡⟨ cong₂ (map2 appᵣ) reflPath (
                    T.morph _ tⱼ          ≡⟨ eqToPath T.functorial ≡$ tⱼ ⟩
                    T.morph j~o tⱼ T.↑ˡ i ≡⟨ eqToPath $ cong (T._↑ˡ i) H₁ ⟩
                    tₒ T.↑ˡ i           ∎) ⟩
                appᵣ↑ rᵢ tₒ ∎)
            , (pathToEq $
                morph _ (appᵣ↑ rᵢ tₖ)
                  ≡⟨ morph-distrib-appᵣ↑ _ _ ⟩
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
  formulaComparisonFiber {ℒ} {n} {l} (s₁ ≈ s₂) =
    let (t₁ , Ht₁) = termComparisonFiber s₁
        (t₂ , Ht₂) = termComparisonFiber s₂ in
    elim2→Set {P = λ _ _ → fiber formulaComparison ∣ s₁ ≈ s₂ ∣₂}
      (λ _ _ → isSetFiber)
      (λ ((i , tᵢ) , Hi) ((j , tⱼ) , Hj) → [ i + j , tᵢ ≈↑ tⱼ ]
      , ( map (formulaMorph _) (tᵢ ≈↑ tⱼ)
            ≡⟨ map-$-formulaMorph-distrib-≈ _ _ ⟩
          map2 _≈_ (termComparison [ i + j , tᵢ T.↑ʳ j ]) (termComparison [ i + j , tⱼ T.↑ˡ i ])
            ≡⟨ cong₂ (map2 _≈_) (compPath (congPath termComparison (Hi T.≡↑ʳ j)) Ht₁)
                                (compPath (congPath termComparison (Hj T.≡↑ˡ i)) Ht₂) ⟩
          ∣ s₁ ≈ s₂ ∣₂ ∎))
      (λ ((i , tᵢ) , Hi) ((j , tⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim₁ {P = λ _ → (i + k , tᵢ ≈↑ tₖ) ≃ (j + k , tⱼ ≈↑ tₖ)}
          (λ _ → squash₁)
          (λ (o , tₒ , i~o , j~o , H₁ , H₂) →
            ∣ o + k , tₒ ≈↑ tₖ
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ i~o)
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ j~o)
            , (pathToEq $
                morph _ (tᵢ ≈↑ tₖ)
                  ≡⟨ morph-distrib-≈↑ _ _ ⟩
                map2 _≈_ (T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ i~o) (m≤m+n _ _)) tᵢ) (T.morph _ tₖ)
                  ≡⟨ cong₂ (map2 _≈_)
                    ( T.morph _ tᵢ          ≡⟨ eqToPath T.functorial ≡$ tᵢ ⟩
                      T.morph i~o tᵢ T.↑ʳ k ≡⟨ eqToPath $ cong (T._↑ʳ k) H₁ ⟩
                      tₒ T.↑ʳ k             ∎
                    ) reflPath ⟩
                tₒ ≈↑ tₖ ∎)
            , (pathToEq $
                morph _ (tⱼ ≈↑ tₖ)
                  ≡⟨ morph-distrib-≈↑ _ _ ⟩
                map2 _≈_ (T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤m+n _ _)) tⱼ) (T.morph _ tₖ)
                  ≡⟨ cong₂ (map2 _≈_)
                    ( T.morph _ tⱼ          ≡⟨ eqToPath T.functorial ≡$ tⱼ ⟩
                      T.morph j~o tⱼ T.↑ʳ k ≡⟨ eqToPath $ cong (T._↑ʳ k) H₂ ⟩
                      tₒ T.↑ʳ k             ∎
                    ) reflPath ⟩
                tₒ ≈↑ tₖ ∎)
            ∣₁)
          (eff $ compPath Hi $ symPath Hj))
      , (toPathP $ squash₂ _ _ _ _))
      (λ ((i , tᵢ) , Hi) ((j , tⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim₁ {P = λ _ → (i + j , tᵢ ≈↑ tⱼ) ≃ (i + k , tᵢ ≈↑ tₖ)}
          (λ _ → squash₁)
          (λ (o , tₒ , j~o , k~o , H₁ , H₂) →
            ∣ i + o , tᵢ ≈↑ tₒ
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ j~o)
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ k~o)
            , (pathToEq $
                morph _ (tᵢ ≈↑ tⱼ)
                  ≡⟨ morph-distrib-≈↑ _ _ ⟩
                map2 _≈_ (T.morph _ tᵢ) (T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤n+m _ _)) tⱼ)
                  ≡⟨ cong₂ (map2 _≈_) reflPath
                    ( T.morph _ tⱼ          ≡⟨ eqToPath T.functorial ≡$ tⱼ ⟩
                      T.morph j~o tⱼ T.↑ˡ i ≡⟨ eqToPath $ cong (T._↑ˡ i) H₁ ⟩
                      tₒ T.↑ˡ i           ∎
                    ) ⟩
                tᵢ ≈↑ tₒ ∎)
            , (pathToEq $
                morph _ (tᵢ ≈↑ tₖ)
                  ≡⟨ morph-distrib-≈↑ _ _ ⟩
                map2 _≈_ (T.morph _ tᵢ) (T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ k~o) (m≤n+m _ _)) tₖ)
                  ≡⟨ cong₂ (map2 _≈_) reflPath
                    ( T.morph _ tₖ          ≡⟨ eqToPath T.functorial ≡$ tₖ ⟩
                      T.morph k~o tₖ T.↑ˡ i ≡⟨ eqToPath $ cong (T._↑ˡ i) H₂ ⟩
                      tₒ T.↑ˡ i             ∎
                    ) ⟩
                tᵢ ≈↑ tₒ ∎)
            ∣₁)
          (eff $ compPath Hj $ symPath Hk))
      , (toPathP $ squash₂ _ _ _ _))
      (λ _ _ _ _ → toPathP $ isSetFiber _ _ _ _)
      (rep t₁) (rep t₂)
    where open DirectedDiagram (termChain ℒ n 0) using () renaming (representative to rep; effective to eff)
          open DirectedDiagram (formulaChain ℒ n l) using (_≃_)
  formulaComparisonFiber (φ₁ ⇒ φ₂) = {!   !}
  formulaComparisonFiber {ℒ} {n} {l} (∀' ψ) =
    let (φ , Hφ) = formulaComparisonFiber ψ in
    elim→Set {P = λ _ → fiber formulaComparison ∣ ∀' ψ ∣₂}
      (λ _ → isSetFiber)
      (λ ((i , φᵢ) , H) → [ i , map ∀'_ φᵢ ] , (
        map (formulaMorph _) (map ∀'_ φᵢ)       ≡⟨ map-$-formulaMorph-∀'-comm _ ⟩
        map ∀'_ (formulaComparison [ i , φᵢ ])  ≡⟨ congPath (map ∀'_) (compPath (congPath formulaComparison H) Hφ) ⟩
        ∣ ∀' ψ ∣₂                               ∎))
      (λ ((i , φᵢ) , Hi) ((j , φⱼ) , Hj) → ΣPathP $
        (eq/ _ _ $ elim₁ {P = λ _ → (i , map ∀'_ φᵢ) ≃ (j , map ∀'_ φⱼ)}
          (λ _ → squash₁)
          (λ (k , φₖ , i~k , j~k , H₁ , H₂) →
            ∣ k , map ∀'_ φₖ , i~k , j~k
            , (pathToEq $
                morph _ (map ∀'_ φᵢ) ≡⟨ map-$-formulaMorph-∀'-comm _ ⟩
                map ∀'_ (morph _ φᵢ) ≡⟨ congPath (map ∀'_) (eqToPath H₁) ⟩
                map ∀'_ φₖ           ∎)
            , (pathToEq $
                morph _ (map ∀'_ φⱼ) ≡⟨ map-$-formulaMorph-∀'-comm _ ⟩
                map ∀'_ (morph _ φⱼ) ≡⟨ congPath (map ∀'_) (eqToPath H₂) ⟩
                map ∀'_ φₖ           ∎)
            ∣₁)
          (effective $ compPath Hi $ symPath Hj))
      , (toPathP $ squash₂ _ _ _ _))
      (representative φ)
    where open DirectedDiagram (formulaChain ℒ n l) using (_≃_)
