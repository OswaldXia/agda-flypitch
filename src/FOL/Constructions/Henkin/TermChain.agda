{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Constructions.Henkin.TermChain ⦃ em : EM ⦄ u where
open import FOL.Constructions.Henkin.LanguageChain u
  renaming (obj to langObj ; morph to langMorph; functorial to langFunctorial)
open import FOL.Language using (Language)
open import FOL.Bounded.Base using (Termₗ)
open import FOL.Bounded.Sethood using (isSetTerm)
open Termₗ

import FOL.Language.Homomorphism as LHom
open LHom using (_∘_ )
open LHom.Bounded using (termMorph)
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
open import Function using (flip; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong-app; subst)

termChain : ∀ ℒ n l → DirectedDiagram ℕᴰ
termChain ℒ n l = record
  { obj = λ k → Termₗ ([ k ]-language ℒ) n l
  ; morph = λ i≤j → termMorph $ langMorph i≤j
  ; functorial = termMorphFunctorial langFunctorial
  }

coconeOfTermChain : ∀ ℒ n l → Cocone (termChain ℒ n l)
coconeOfTermChain ℒ n l = record
  { Vertex = Termₗ (∞-language ℒ ) n l
  ; isSetVertex = isSetTerm _
  ; map = λ i → termMorph $ languageCanonicalMorph i
  ; compat = λ {i} i~j → termMorphFunctorial (coconeOfLanguageChain .compat i~j)
  }

module _ {ℒ n l} where
  open DirectedDiagram (termChain ℒ n l) using (obj; morph; functorial; Colimit) public

  termComparison : Colimit → Termₗ (∞-language ℒ) n l
  termComparison = universalMap (coconeOfTermChain ℒ n l)

  _ : ∀ {i} (t : obj i) → termComparison [ i , t ] ≡ₚ (termMorph $ languageCanonicalMorph i) t
  _ = λ _ → reflPath

  _↑ʳ_ : ∀ {i} → obj i → (j : ℕ) → obj (i + j)
  t ↑ʳ _ = morph m≤₃m+n t

  _↑ˡ_ : ∀ {j} → obj j → (i : ℕ) → obj (i + j)
  t ↑ˡ _ = morph m≤₃n+m t

  abstract
    _≡↑ʳ_ : ∀ {i} {tᵢ : obj i} {t : Colimit} → [ i , tᵢ ] ≡ₚ t → (j : ℕ) → [ i + j , tᵢ ↑ʳ j ] ≡ₚ t
    _≡↑ʳ_ {i} {tᵢ} H j = flip compPath H $ eq/ _ _
      ∣ i + j , tᵢ ↑ʳ j , ≤₃-refl , m≤₃m+n
      , (sym $ (flip cong-app) tᵢ $ termMorphFunctorial
             $ subst (λ x → langMorph m≤₃m+n ≡ x ∘ langMorph m≤₃m+n) (sym endomorph≡id) refl)
      , refl
      ∣₁

    _≡↑ˡ_ : ∀ {j} {tⱼ : obj j} {t : Colimit} →
      [ j , tⱼ ] ≡ₚ t → (i : ℕ) → [ i + j , tⱼ ↑ˡ i ] ≡ₚ t
    _≡↑ˡ_ {j} {tⱼ} H i = (flip compPath) H $ eq/ _ _
      ∣ i + j , tⱼ ↑ˡ i , ≤₃-refl , m≤₃n+m
      , (sym $ (flip cong-app) tⱼ $ termMorphFunctorial
             $ subst (λ x → langMorph m≤₃n+m ≡ x ∘ langMorph m≤₃n+m) (sym endomorph≡id) refl)
      , refl
      ∣₁

app↑ : ∀ {ℒ n l i j} → obj {ℒ} {n} {suc l} i → obj {ℒ} {n} {0} j → obj (i + j)
app↑ {i = i} {j = j} f t = app (f ↑ʳ j) (t ↑ˡ i)

abstract
  morph-distrib-app↑ : ∀ {ℒ n l i j k} .{f₀ : i + j ≤₃ k} .{f₁ : i ≤₃ k} .{f₂ : j ≤₃ k}
    (f : obj {ℒ} {n} {suc l} i) (t : obj {ℒ} {n} {0} j) →
    (morph f₀) (app↑ f t) ≡ₚ app (morph f₁ f) (morph f₂ t)
  morph-distrib-app↑ f t = cong₂ app (eqToPath $ sym $ cong-app functorial f) (eqToPath $ sym $ cong-app functorial t)

  isSetFiber : ∀ {ℒ n l} {t : Termₗ (∞-language ℒ) n l} → isSet (fiber termComparison t)
  isSetFiber = isSetΣ squash/ $ λ _ → isProp→isSet $ isSetTerm _ _ _

  termComparisonFiber : ∀ {ℒ n l} (t : Termₗ (∞-language ℒ) n l) → fiber termComparison t
  termComparisonFiber (var k) = [ 0 , var k ] , reflPath
  termComparisonFiber {ℒ} {n} {l} (func f) =
    elim→Set {P = λ _ → fiber termComparison (func f)}
      (λ _ → isSetFiber)
      (λ ((i , fᵢ) , H) → [ i , func fᵢ ] , congPath func H)
      (λ ((i , fᵢ) , Hi) ((j , fⱼ) , Hj) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i , func fᵢ) ≃ (j , func fⱼ)}
          (λ _ → squash₁)
          (λ (k , fₖ , i~k , j~k , H₁ , H₂) →
            ∣ k , func fₖ , i~k , j~k , cong func H₁ , cong func H₂ ∣₁)
          (effective $ compPath Hi $ symPath Hj))
      , (toPathP $ isSetTerm _ _ _ _ _))
      (representative f)
    where open DirectedDiagram (termChain ℒ n l) using (_≃_)
          open DirectedDiagramLanguage (languageChain ℒ) using (functionsᴰ)
          open DirectedDiagram (functionsᴰ l) using (representative; effective)
  termComparisonFiber {ℒ} {n} {l} (app g s) =
    let (f , Hf) = termComparisonFiber g
        (t , Ht) = termComparisonFiber s in
    elim2→Set {P = λ _ _ → fiber termComparison (app g s)}
      (λ _ _ → isSetFiber)
      (λ ((i , fᵢ) , Hi) ((j , tⱼ) , Hj) → [ i + j , app↑ fᵢ tⱼ ]
      , ( termMorph _ (app↑ fᵢ tⱼ) ≡⟨⟩
          app (termComparison [ i + j , fᵢ ↑ʳ j ]) (termComparison [ i + j , tⱼ ↑ˡ i ])
            ≡⟨ cong₂ app (compPath (congPath termComparison (Hi ≡↑ʳ j)) Hf)
                         (compPath (congPath termComparison (Hj ≡↑ˡ i)) Ht) ⟩
          app g s ∎))
      (λ ((i , fᵢ) , Hi) ((j , fⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i + k , app↑ fᵢ tₖ) ≃ (j + k , app↑ fⱼ tₖ)}
          (λ _ → squash₁)
          (λ (o , fₒ , i~o , j~o , H₁ , H₂) →
            ∣ o + k , app↑ fₒ tₖ
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ i~o)
            , (≤⇒≤₃ $ +-monoˡ-≤ k $ ≤₃⇒≤ j~o)
            , (pathToEq $
                morph _ (app↑ fᵢ tₖ) ≡⟨ morph-distrib-app↑ _ _ ⟩
                app (morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ i~o) (m≤m+n _ _)) fᵢ) (morph _ tₖ)
                  ≡⟨ cong₂ app
                    ( morph _ fᵢ        ≡⟨ eqToPath functorial ≡$ fᵢ ⟩
                      morph i~o fᵢ ↑ʳ k ≡⟨ eqToPath $ cong (_↑ʳ k) H₁ ⟩
                      fₒ ↑ʳ k           ∎
                    ) reflPath ⟩
                app↑ fₒ tₖ ∎)
            , (pathToEq $
                morph _ (app↑ fⱼ tₖ) ≡⟨ morph-distrib-app↑ _ _ ⟩
                app (morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤m+n _ _)) fⱼ) (morph _ tₖ)
                  ≡⟨ cong₂ app
                    ( morph _ fⱼ        ≡⟨ eqToPath functorial ≡$ fⱼ ⟩
                      morph j~o fⱼ ↑ʳ k ≡⟨ eqToPath $ cong (_↑ʳ k) H₂ ⟩
                      fₒ ↑ʳ k           ∎
                    ) reflPath ⟩
                app↑ fₒ tₖ ∎)
            ∣₁)
          (effᶠ $ compPath Hi $ symPath Hj))
      , (toPathP $ isSetTerm _ _ _ _ _))
      (λ ((i , fᵢ) , Hi) ((j , tⱼ) , Hj) ((k , tₖ) , Hk) → ΣPathP $
        (eq/ _ _ $ elim {P = λ _ → (i + j , app↑ fᵢ tⱼ) ≃ (i + k , app↑ fᵢ tₖ)}
          (λ _ → squash₁)
          (λ (o , tₒ , j~o , k~o , H₁ , H₂) →
            ∣ i + o , app↑ fᵢ tₒ
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ j~o)
            , (≤⇒≤₃ $ +-monoʳ-≤ i $ ≤₃⇒≤ k~o)
            , (pathToEq $
                morph _ (app↑ fᵢ tⱼ) ≡⟨ morph-distrib-app↑ _ _ ⟩
                app (morph _ fᵢ) (morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ j~o) (m≤n+m _ _)) tⱼ)
                  ≡⟨ cong₂ app reflPath (
                    morph _ tⱼ        ≡⟨ eqToPath functorial ≡$ tⱼ ⟩
                    morph j~o tⱼ ↑ˡ i ≡⟨ eqToPath $ cong (_↑ˡ i) H₁ ⟩
                    tₒ ↑ˡ i           ∎) ⟩
                app↑ fᵢ tₒ ∎)
            , (pathToEq $
                morph _ (app↑ fᵢ tₖ) ≡⟨ morph-distrib-app↑ _ _ ⟩
                app (morph _ fᵢ) (morph (≤⇒≤₃ $ ≤-trans (≤₃⇒≤ k~o) (m≤n+m _ _)) tₖ)
                  ≡⟨ cong₂ app reflPath (
                    morph _ tₖ        ≡⟨ eqToPath functorial ≡$ tₖ ⟩
                    morph k~o tₖ ↑ˡ i ≡⟨ eqToPath $ cong (_↑ˡ i) H₂ ⟩
                    tₒ ↑ˡ i           ∎) ⟩
                app↑ fᵢ tₒ ∎)
            ∣₁)
          (effᵗ $ compPath Hj $ symPath Hk))
      , (toPathP $ isSetTerm _ _ _ _ _))
      (λ _ _ _ _ → toPathP $ isSetFiber _ _ _ _)
      (repᶠ f) (repᵗ t)
    where open DirectedDiagram (termChain ℒ n l) using (_≃_)
          open DirectedDiagram (termChain ℒ n (suc l)) using () renaming (representative to repᶠ; effective to effᶠ)
          open DirectedDiagram (termChain ℒ n 0)       using () renaming (representative to repᵗ; effective to effᵗ)
