{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Constructions.Henkin.FormulaChain ⦃ em : EM ⦄ u where
open import FOL.Constructions.Henkin.LanguageChain u
  renaming (obj to langObj ; morph to langMorph; functorial to langFunctorial)
open import FOL.Constructions.Henkin.TermChain u as T
  using (termChain; termComparison; termComparisonFiber)
open import FOL.Language using (Language)
open import FOL.Bounded.Base using (Termₗ; Formulaₗ)
open import FOL.Bounded.Sethood using (isSetFormula)
open Formulaₗ

import FOL.Language.Homomorphism as LHom
open LHom using (_∘_)
open LHom.Bounded using (termMorph; formulaMorph)
open LHom.BoundedProperties

open import Tools.DirectedDiagram using (ℕᴰ; DirectedDiagram; Cocone)
open Cocone using (universalMap)
open import FOL.Language.DirectedDiagram using (DirectedDiagramLanguage; CoconeLanguage)
open CoconeLanguage using (compat)

open import Cubical.Foundations.Prelude hiding (refl; sym; cong; subst) renaming (_≡_ to _≡ₚ_)
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.HLevels using (isSetΣ)
open import Cubical.Data.Equality using (eqToPath; pathToEq; reflPath; symPath; compPath; congPath)
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.HITs.SetQuotients using ([_]; eq/; squash/)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim; elim→Set; elim2→Set)

open import StdlibExt.Data.Nat
open import StdlibExt.Data.Nat.Properties
open import Function using (flip; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong-app; subst)

formulaChain : ∀ ℒ n l → DirectedDiagram ℕᴰ
formulaChain ℒ n l = record
  { obj = λ k → Formulaₗ ([ k ]-language ℒ) n l
  ; morph = λ i≤j → formulaMorph $ langMorph i≤j
  ; functorial = formulaMorphFunctorial langFunctorial
  }

coconeOfFormulaChain : ∀ ℒ n l → Cocone (formulaChain ℒ n l)
coconeOfFormulaChain ℒ n l = record
  { Vertex = Formulaₗ (∞-language ℒ ) n l
  ; isSetVertex = isSetFormula _
  ; map = λ i → formulaMorph $ languageCanonicalMorph i
  ; compat = λ i~j → formulaMorphFunctorial (coconeOfLanguageChain .compat i~j)
  }

module _ {ℒ n l} where
  open DirectedDiagram (formulaChain ℒ n l) using (obj; morph; functorial; Colimit; representative; effective) public

  formulaComparison : Colimit → Formulaₗ (∞-language ℒ) n l
  formulaComparison = universalMap (coconeOfFormulaChain ℒ n l)

  _ : ∀ {i} (φ : obj i) → formulaComparison [ i , φ ] ≡ₚ (formulaMorph $ languageCanonicalMorph i) φ
  _ = λ _ → reflPath

  _↑ʳ_ : ∀ {i} → obj i → (j : ℕ) → obj (i + j)
  φ ↑ʳ _ = morph m≤₃m+n φ

  _↑ˡ_ : ∀ {j} → obj j → (i : ℕ) → obj (i + j)
  φ ↑ˡ _ = morph m≤₃n+m φ

  abstract
    _≡↑ʳ_ : ∀ {i} {tᵢ : obj i} {t : Colimit} →
      [ i , tᵢ ] ≡ₚ t → (j : ℕ) → [ i + j , tᵢ ↑ʳ j ] ≡ₚ t
    _≡↑ʳ_ {i} {tᵢ} H j = (flip compPath) H $ eq/ _ _
      ∣ i + j , tᵢ ↑ʳ j , ≤₃-refl , m≤₃m+n
      , (sym $ (flip cong-app) tᵢ $ formulaMorphFunctorial
             $ subst (λ x → langMorph m≤₃m+n ≡ x ∘ langMorph m≤₃m+n) (sym endomorph≡id) refl)
      , refl
      ∣₁

    _≡↑ˡ_ : ∀ {j} {tⱼ : obj j} {t : Colimit} →
      [ j , tⱼ ] ≡ₚ t → (i : ℕ) → [ i + j , tⱼ ↑ˡ i ] ≡ₚ t
    _≡↑ˡ_ {j} {tⱼ} H i = (flip compPath) H $ eq/ _ _
      ∣ i + j , tⱼ ↑ˡ i , ≤₃-refl , m≤₃n+m
      , (sym $ (flip cong-app) tⱼ $ formulaMorphFunctorial
             $ subst (λ x → langMorph m≤₃n+m ≡ x ∘ langMorph m≤₃n+m) (sym endomorph≡id) refl)
      , refl
      ∣₁

appᵣ↑ : ∀ {ℒ n l i j} → obj {ℒ} {n} {suc l} i → T.obj {ℒ} {n} {0} j → obj (i + j)
appᵣ↑ {i = i} {j = j} r t = appᵣ (r ↑ʳ j) (t T.↑ˡ i)

_≈↑_ : ∀ {ℒ n i j} → T.obj {ℒ} {n} {0} i → T.obj {ℒ} {n} {0} j → obj (i + j)
_≈↑_ {i = i} {j = j} t₁ t₂ = t₁ T.↑ʳ j ≈ t₂ T.↑ˡ i

_⇒↑_ : ∀ {ℒ n i j} → obj {ℒ} {n} {0} i → obj {ℒ} {n} {0} j → obj (i + j)
_⇒↑_ {i = i} {j = j} φ₁ φ₂ = φ₁ ↑ʳ j ⇒ φ₂ ↑ˡ i

abstract
  morph-distrib-appᵣ↑ : ∀ {ℒ n l i j k} .{f₀ : i + j ≤₃ k} .{f₁ : i ≤₃ k} .{f₂ : j ≤₃ k}
    (r : obj {ℒ} {n} {suc l} i) (t : T.obj {ℒ} {n} {0} j) →
    (morph f₀) (appᵣ↑ r t) ≡ₚ appᵣ (morph f₁ r) (T.morph f₂ t)
  morph-distrib-appᵣ↑ r t = cong₂ appᵣ
    (eqToPath $ sym $ cong-app functorial r)
    (eqToPath $ sym $ cong-app T.functorial t)

  morph-distrib-≈↑ : ∀ {ℒ n i j k} .{f₀ : i + j ≤₃ k} .{f₁ : i ≤₃ k} .{f₂ : j ≤₃ k}
    (t₁ : T.obj {ℒ} {n} {0} i) (t₂ : T.obj {ℒ} {n} {0} j) →
    (morph f₀) (t₁ ≈↑ t₂) ≡ₚ T.morph f₁ t₁ ≈ T.morph f₂ t₂
  morph-distrib-≈↑ t₁ t₂ = cong₂ _≈_
    (eqToPath $ sym $ cong-app T.functorial t₁)
    (eqToPath $ sym $ cong-app T.functorial t₂)

  morph-distrib-⇒↑ : ∀ {ℒ n i j k} .{f₀ : i + j ≤₃ k} .{f₁ : i ≤₃ k} .{f₂ : j ≤₃ k}
    (φ₁ : obj {ℒ} {n} {0} i) (φ₂ : obj {ℒ} {n} {0} j) →
    (morph f₀) (φ₁ ⇒↑ φ₂) ≡ₚ morph f₁ φ₁ ⇒ morph f₂ φ₂
  morph-distrib-⇒↑ φ₁ φ₂ = cong₂ _⇒_
    (eqToPath $ sym $ cong-app functorial φ₁)
    (eqToPath $ sym $ cong-app functorial φ₂)

  isSetFiber : ∀ {ℒ n l} {φ : Formulaₗ (∞-language ℒ) n l} → isSet (fiber formulaComparison φ)
  isSetFiber = isSetΣ squash/ $ λ _ → isProp→isSet $ isSetFormula _ _ _

  formulaComparisonFiber : ∀ {ℒ n l} (φ : Formulaₗ (∞-language ℒ) n l) → fiber formulaComparison φ
  formulaComparisonFiber ⊥ = [ 0 , ⊥ ] , reflPath
  formulaComparisonFiber {ℒ} {n} {l} (rel R) =
    elim→Set {P = λ _ → fiber formulaComparison (rel R)}
      (λ _ → isSetFiber)
      (λ ((i , Rᵢ) , H) → [ i , rel Rᵢ ] , congPath rel H)
      (λ ((i , Rᵢ) , Hi) ((j , Rⱼ) , Hj) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i , rel Rᵢ) ≃ (j , rel Rⱼ)}
          (λ _ → squash₁)
          (λ (k , Rₖ , i~k , j~k , H₁ , H₂) →
            ∣ k , rel Rₖ , i~k , j~k , cong rel H₁ , cong rel H₂ ∣₁)
          (eff $ compPath Hi $ symPath Hj))
      , (toPathP $ isSetFormula _ _ _ _ _))
      (rep R)
    where open DirectedDiagramLanguage (languageChain ℒ) using (relationsᴰ)
          open DirectedDiagram (relationsᴰ l) using () renaming (representative to rep; effective to eff)
          open DirectedDiagram (formulaChain ℒ n l) using (_≃_)
  formulaComparisonFiber {ℒ} {n} {l} (appᵣ ρ τ) =
    let (r , Hr) = formulaComparisonFiber ρ
        (t , Ht) = termComparisonFiber    τ in
    elim2→Set {P = λ _ _ → fiber formulaComparison (appᵣ ρ τ)}
      (λ _ _ → isSetFiber)
      (λ ((i , rᵢ) , Hi) ((j , tⱼ) , Hj) → [ i + j , appᵣ↑ rᵢ tⱼ ]
      , ( formulaMorph _ (appᵣ↑ rᵢ tⱼ) ≡⟨⟩
          appᵣ (formulaComparison [ i + j , rᵢ ↑ʳ j ]) (termComparison [ i + j , tⱼ T.↑ˡ i ])
            ≡⟨ cong₂ appᵣ (compPath (congPath formulaComparison (Hi ≡↑ʳ j)) Hr)
                          (compPath (congPath termComparison (Hj T.≡↑ˡ i)) Ht) ⟩
          appᵣ ρ τ ∎))
      (λ ((i , rᵢ) , Hi) ((j , rⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i + k , appᵣ↑ rᵢ tₖ) ≃ (j + k , appᵣ↑ rⱼ tₖ)}
          (λ _ → squash₁)
          (λ (o , rₒ , i~o , j~o , H₁ , H₂) →
            ∣ o + k , appᵣ↑ rₒ tₖ
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ i~o)
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ j~o)
            , (pathToEq $
                morph _ (appᵣ↑ rᵢ tₖ)
                  ≡⟨ morph-distrib-appᵣ↑ _ _ ⟩
                appᵣ (morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ i~o) (m≤m+n _ _)) rᵢ) (T.morph _ tₖ)
                  ≡⟨ cong₂ appᵣ
                    ( morph _ rᵢ        ≡⟨ eqToPath functorial ≡$ rᵢ ⟩
                      morph i~o rᵢ ↑ʳ k ≡⟨ eqToPath $ cong (_↑ʳ k) H₁ ⟩
                      rₒ ↑ʳ k           ∎
                    ) reflPath ⟩
                appᵣ↑ rₒ tₖ ∎)
            , (pathToEq $
                morph _ (appᵣ↑ rⱼ tₖ)
                  ≡⟨ morph-distrib-appᵣ↑ _ _ ⟩
                appᵣ (morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤m+n _ _)) rⱼ) (T.morph _ tₖ)
                  ≡⟨ cong₂ appᵣ
                    ( morph _ rⱼ        ≡⟨ eqToPath functorial ≡$ rⱼ ⟩
                      morph j~o rⱼ ↑ʳ k ≡⟨ eqToPath $ cong (_↑ʳ k) H₂ ⟩
                      rₒ ↑ʳ k           ∎
                    ) reflPath ⟩
                appᵣ↑ rₒ tₖ ∎)
            ∣₁)
          (effʳ $ compPath Hi $ symPath Hj))
      , (toPathP $ isSetFormula _ _ _ _ _))
      (λ ((i , rᵢ) , Hi) ((j , tⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i + j , appᵣ↑ rᵢ tⱼ) ≃ (i + k , appᵣ↑ rᵢ tₖ)}
          (λ _ → squash₁)
          (λ (o , tₒ , j~o , k~o , H₁ , H₂) →
            ∣ i + o , appᵣ↑ rᵢ tₒ
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ j~o)
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ k~o)
            , (pathToEq $
                morph _ (appᵣ↑ rᵢ tⱼ)
                  ≡⟨ morph-distrib-appᵣ↑ _ _ ⟩
                appᵣ (morph _ rᵢ) (T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤n+m _ _)) tⱼ)
                  ≡⟨ cong₂ appᵣ reflPath (
                    T.morph _ tⱼ          ≡⟨ eqToPath T.functorial ≡$ tⱼ ⟩
                    T.morph j~o tⱼ T.↑ˡ i ≡⟨ eqToPath $ cong (T._↑ˡ i) H₁ ⟩
                    tₒ T.↑ˡ i           ∎) ⟩
                appᵣ↑ rᵢ tₒ ∎)
            , (pathToEq $
                morph _ (appᵣ↑ rᵢ tₖ)
                  ≡⟨ morph-distrib-appᵣ↑ _ _ ⟩
                appᵣ (morph _ rᵢ) (T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ k~o) (m≤n+m _ _)) tₖ)
                  ≡⟨ cong₂ appᵣ reflPath (
                    T.morph _ tₖ          ≡⟨ eqToPath T.functorial ≡$ tₖ ⟩
                    T.morph k~o tₖ T.↑ˡ i ≡⟨ eqToPath $ cong (T._↑ˡ i) H₂ ⟩
                    tₒ T.↑ˡ i           ∎) ⟩
                appᵣ↑ rᵢ tₒ ∎)
            ∣₁)
          (effᵗ $ compPath Hj $ symPath Hk))
      , (toPathP $ isSetFormula _ _ _ _ _))
      (λ _ _ _ _ → toPathP $ isSetFiber _ _ _ _)
      (repʳ r) (repᵗ t)
    where open DirectedDiagram (formulaChain ℒ n (suc l)) using () renaming (representative to repʳ; effective to effʳ)
          open DirectedDiagram (termChain ℒ n 0)          using () renaming (representative to repᵗ; effective to effᵗ)
          open DirectedDiagram (formulaChain ℒ n l) using (_≃_)
  formulaComparisonFiber {ℒ} {n} {l} (s₁ ≈ s₂) =
    let (t₁ , Ht₁) = termComparisonFiber s₁
        (t₂ , Ht₂) = termComparisonFiber s₂ in
    elim2→Set {P = λ _ _ → fiber formulaComparison (s₁ ≈ s₂)}
      (λ _ _ → isSetFiber)
      (λ ((i , tᵢ) , Hi) ((j , tⱼ) , Hj) → [ i + j , tᵢ ≈↑ tⱼ ]
      , ( formulaMorph _ (tᵢ ≈↑ tⱼ) ≡⟨⟩
          termComparison [ i + j , tᵢ T.↑ʳ j ] ≈ termComparison [ i + j , tⱼ T.↑ˡ i ]
            ≡⟨ cong₂ _≈_ (compPath (congPath termComparison (Hi T.≡↑ʳ j)) Ht₁)
                         (compPath (congPath termComparison (Hj T.≡↑ˡ i)) Ht₂) ⟩
          s₁ ≈ s₂ ∎))
      (λ ((i , tᵢ) , Hi) ((j , tⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i + k , tᵢ ≈↑ tₖ) ≃ (j + k , tⱼ ≈↑ tₖ)}
          (λ _ → squash₁)
          (λ (o , tₒ , i~o , j~o , H₁ , H₂) →
            ∣ o + k , tₒ ≈↑ tₖ
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ i~o)
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ j~o)
            , (pathToEq $
                morph _ (tᵢ ≈↑ tₖ)
                  ≡⟨ morph-distrib-≈↑ _ _ ⟩
                T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ i~o) (m≤m+n _ _)) tᵢ ≈ T.morph _ tₖ
                  ≡⟨ cong₂ _≈_
                    ( T.morph _ tᵢ          ≡⟨ eqToPath T.functorial ≡$ tᵢ ⟩
                      T.morph i~o tᵢ T.↑ʳ k ≡⟨ eqToPath $ cong (T._↑ʳ k) H₁ ⟩
                      tₒ T.↑ʳ k             ∎
                    ) reflPath ⟩
                tₒ ≈↑ tₖ ∎)
            , (pathToEq $
                morph _ (tⱼ ≈↑ tₖ)
                  ≡⟨ morph-distrib-≈↑ _ _ ⟩
                T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤m+n _ _)) tⱼ ≈ T.morph _ tₖ
                  ≡⟨ cong₂ _≈_
                    ( T.morph _ tⱼ          ≡⟨ eqToPath T.functorial ≡$ tⱼ ⟩
                      T.morph j~o tⱼ T.↑ʳ k ≡⟨ eqToPath $ cong (T._↑ʳ k) H₂ ⟩
                      tₒ T.↑ʳ k             ∎
                    ) reflPath ⟩
                tₒ ≈↑ tₖ ∎)
            ∣₁)
          (eff $ compPath Hi $ symPath Hj))
      , (toPathP $ isSetFormula _ _ _ _ _))
      (λ ((i , tᵢ) , Hi) ((j , tⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i + j , tᵢ ≈↑ tⱼ) ≃ (i + k , tᵢ ≈↑ tₖ)}
          (λ _ → squash₁)
          (λ (o , tₒ , j~o , k~o , H₁ , H₂) →
            ∣ i + o , tᵢ ≈↑ tₒ
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ j~o)
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ k~o)
            , (pathToEq $
                morph _ (tᵢ ≈↑ tⱼ)
                  ≡⟨ morph-distrib-≈↑ _ _ ⟩
                T.morph _ tᵢ ≈ T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤n+m _ _)) tⱼ
                  ≡⟨ cong₂ _≈_ reflPath
                    ( T.morph _ tⱼ          ≡⟨ eqToPath T.functorial ≡$ tⱼ ⟩
                      T.morph j~o tⱼ T.↑ˡ i ≡⟨ eqToPath $ cong (T._↑ˡ i) H₁ ⟩
                      tₒ T.↑ˡ i             ∎
                    ) ⟩
                tᵢ ≈↑ tₒ ∎)
            , (pathToEq $
                morph _ (tᵢ ≈↑ tₖ)
                  ≡⟨ morph-distrib-≈↑ _ _ ⟩
                T.morph _ tᵢ ≈ T.morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ k~o) (m≤n+m _ _)) tₖ
                  ≡⟨ cong₂ _≈_ reflPath
                    ( T.morph _ tₖ          ≡⟨ eqToPath T.functorial ≡$ tₖ ⟩
                      T.morph k~o tₖ T.↑ˡ i ≡⟨ eqToPath $ cong (T._↑ˡ i) H₂ ⟩
                      tₒ T.↑ˡ i             ∎
                    ) ⟩
                tᵢ ≈↑ tₒ ∎)
            ∣₁)
          (eff $ compPath Hj $ symPath Hk))
      , (toPathP $ isSetFormula _ _ _ _ _))
      (λ _ _ _ _ → toPathP $ isSetFiber _ _ _ _)
      (rep t₁) (rep t₂)
    where open DirectedDiagram (termChain ℒ n 0) using () renaming (representative to rep; effective to eff)
          open DirectedDiagram (formulaChain ℒ n l) using (_≃_)
  formulaComparisonFiber {ℒ} {n} {l} (ψ₁ ⇒ ψ₂) =
    let (φ₁ , Hφ₁) = formulaComparisonFiber ψ₁
        (φ₂ , Hφ₂) = formulaComparisonFiber ψ₂ in
    elim2→Set {P = λ _ _ → fiber formulaComparison (ψ₁ ⇒ ψ₂)}
      (λ _ _ → isSetFiber)
      (λ ((i , φᵢ) , Hi) ((j , φⱼ) , Hj) → [ i + j , φᵢ ⇒↑ φⱼ ]
      , ( formulaMorph _ (φᵢ ⇒↑ φⱼ) ≡⟨⟩
          formulaComparison [ i + j , φᵢ ↑ʳ j ] ⇒ formulaComparison [ i + j , φⱼ ↑ˡ i ]
            ≡⟨ cong₂ _⇒_ (compPath (congPath formulaComparison (Hi ≡↑ʳ j)) Hφ₁)
                         (compPath (congPath formulaComparison (Hj ≡↑ˡ i)) Hφ₂) ⟩
          ψ₁ ⇒ ψ₂ ∎))
      (λ ((i , φᵢ) , Hi) ((j , φⱼ) , Hj) ((k , φₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i + k , φᵢ ⇒↑ φₖ) ≃ (j + k , φⱼ ⇒↑ φₖ)}
          (λ _ → squash₁)
          (λ (o , φₒ , i~o , j~o , H₁ , H₂) →
            ∣ o + k , φₒ ⇒↑ φₖ
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ i~o)
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ j~o)
            , (pathToEq $
                morph _ (φᵢ ⇒↑ φₖ)
                  ≡⟨ morph-distrib-⇒↑ _ _ ⟩
                 morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ i~o) (m≤m+n _ _)) φᵢ ⇒ morph _ φₖ
                  ≡⟨ cong₂ _⇒_
                    ( morph _ φᵢ        ≡⟨ eqToPath functorial ≡$ φᵢ ⟩
                      morph i~o φᵢ ↑ʳ k ≡⟨ eqToPath $ cong (_↑ʳ k) H₁ ⟩
                      φₒ ↑ʳ k           ∎
                    ) reflPath ⟩
                φₒ ⇒↑ φₖ ∎)
            , (pathToEq $
                morph _ (φⱼ ⇒↑ φₖ)
                  ≡⟨ morph-distrib-⇒↑ _ _ ⟩
                morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤m+n _ _)) φⱼ ⇒ morph _ φₖ
                  ≡⟨ cong₂ _⇒_
                    ( morph _ φⱼ        ≡⟨ eqToPath functorial ≡$ φⱼ ⟩
                      morph j~o φⱼ ↑ʳ k ≡⟨ eqToPath $ cong (_↑ʳ k) H₂ ⟩
                      φₒ ↑ʳ k           ∎
                    ) reflPath ⟩
                φₒ ⇒↑ φₖ ∎)
            ∣₁)
          (effective $ compPath Hi $ symPath Hj))
      , (toPathP $ isSetFormula _ _ _ _ _))
      (λ ((i , φᵢ) , Hi) ((j , φⱼ) , Hj) ((k , φₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i + j , φᵢ ⇒↑ φⱼ) ≃ (i + k , φᵢ ⇒↑ φₖ)}
          (λ _ → squash₁)
          (λ (o , φₒ , j~o , k~o , H₁ , H₂) →
            ∣ i + o , φᵢ ⇒↑ φₒ
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ j~o)
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ k~o)
            , (pathToEq $
                morph _ (φᵢ ⇒↑ φⱼ)
                  ≡⟨ morph-distrib-⇒↑ _ _ ⟩
                morph _ φᵢ ⇒ morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤n+m _ _)) φⱼ
                  ≡⟨ cong₂ _⇒_ reflPath
                    ( morph _ φⱼ        ≡⟨ eqToPath functorial ≡$ φⱼ ⟩
                      morph j~o φⱼ ↑ˡ i ≡⟨ eqToPath $ cong (_↑ˡ i) H₁ ⟩
                      φₒ ↑ˡ i           ∎
                    ) ⟩
                φᵢ ⇒↑ φₒ ∎)
            , (pathToEq $
                morph _ (φᵢ ⇒↑ φₖ)
                  ≡⟨ morph-distrib-⇒↑ _ _ ⟩
                morph _ φᵢ ⇒ morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ k~o) (m≤n+m _ _)) φₖ
                  ≡⟨ cong₂ _⇒_ reflPath
                    ( morph _ φₖ        ≡⟨ eqToPath functorial ≡$ φₖ ⟩
                      morph k~o φₖ ↑ˡ i ≡⟨ eqToPath $ cong (_↑ˡ i) H₂ ⟩
                      φₒ ↑ˡ i           ∎
                    ) ⟩
                φᵢ ⇒↑ φₒ ∎)
            ∣₁)
          (effective $ compPath Hj $ symPath Hk))
      , (toPathP $ isSetFormula _ _ _ _ _))
      (λ _ _ _ _ → toPathP $ isSetFiber _ _ _ _)
      (representative φ₁) (representative φ₂)
    where open DirectedDiagram (formulaChain ℒ n l) using (_≃_)
  formulaComparisonFiber {ℒ} {n} {l} (∀' ψ) =
    let (φ , Hφ) = formulaComparisonFiber ψ in
    elim→Set {P = λ _ → fiber formulaComparison (∀' ψ)}
      (λ _ → isSetFiber)
      (λ ((i , φᵢ) , H) → [ i , ∀' φᵢ ] , (
        formulaMorph _ (∀' φᵢ)            ≡⟨⟩
        ∀' (formulaComparison [ i , φᵢ ]) ≡⟨ congPath ∀'_ (compPath (congPath formulaComparison H) Hφ) ⟩
        ∀' ψ                              ∎))
      (λ ((i , φᵢ) , Hi) ((j , φⱼ) , Hj) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i , ∀' φᵢ) ≃ (j , ∀' φⱼ)}
          (λ _ → squash₁)
          (λ (k , φₖ , i~k , j~k , H₁ , H₂) →
            ∣ k , ∀' φₖ , i~k , j~k
            , (pathToEq $
                morph _ (∀' φᵢ) ≡⟨⟩
                ∀' (morph _ φᵢ) ≡⟨ congPath ∀'_ (eqToPath H₁) ⟩
                ∀' φₖ           ∎)
            , (pathToEq $
                morph _ (∀' φⱼ) ≡⟨⟩
                ∀' (morph _ φⱼ) ≡⟨ congPath ∀'_ (eqToPath H₂) ⟩
                ∀' φₖ           ∎)
            ∣₁)
          (effective $ compPath Hi $ symPath Hj))
      , (toPathP $ isSetFormula _ _ _ _ _))
      (representative φ)
    where open DirectedDiagram (formulaChain ℒ n l) using (_≃_)
