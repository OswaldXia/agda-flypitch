{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import FOL.Bounded.Syntactics using (Theory)
open import FOL.PropertiesOfTheory using (complete; hasEnoughConstants)
module FOL.Constructions.TermModel.Properties {ℒ : Language {u}} {T : Theory ℒ}
  (H₁ : complete ℒ T) (H₂ : hasEnoughConstants ℒ T) where
open Language ℒ

open import FOL.Constructions.TermModel.Base T
open TermModel hiding (Domain; func; rel)

open import FOL.Structure.Base using (Structure)
open Structure termModel using (Domain; relMap)

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.Bounded.Lemmas.Realization termModel
open import FOL.PropertiesOfTheory ℒ using (⇒-intro-of-complete)
open import FOL.Constructions.Equivalence.BoundedTruncated T

import FOL.Base ℒ as Free
open Free.Formulaₗ
open import FOL.Syntactics ℒ using (⇒-elim)

open import Cubical.Foundations.Prelude renaming (_,_ to infix 5 _,_)
open import Cubical.Foundations.HLevels using (isSetHProp)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import CubicalExt.Foundations.Powerset* using (_∈_)
open import Cubical.Functions.Logic using (∥_∥ₚ)
open import CubicalExt.Functions.Logic.Iff
open import CubicalExt.Data.Vec using (quotientBeta)
open import Cubical.HITs.SetQuotients using ([_]; eq/; squash/; effective)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim; map2)

open import Data.Nat
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m)
open import Data.Vec using (Vec; []; _∷_; map)
open import Function using (_∘_; _∘₂_; _$_)
open import Relation.Binary.PropositionalEquality
  using () renaming (subst to substEq; sym to symEq)

private variable
  n : ℕ

module _ where
  open PreRealizer termModel

  ≡preFunc : (f : ClosedTermₗ l) (xs : Vec ClosedTerm l) →
    realizeₜ [] f (map [_] xs) ≡ preFunc f xs
  ≡preFunc (func f) = quotientBeta ≋-refl squash/ (preFunc (func f)) (preFunc-pointwiseEq (func f))
  ≡preFunc (app t₁ t₂) xs =
    realizeₜ [] t₁ (realizeₜ [] t₂ [] ∷ map [_] xs) ≡⟨ cong (λ x → realizeₜ [] t₁ (x ∷ _)) (≡preFunc t₂ []) ⟩
    realizeₜ [] t₁ ([ t₂ ] ∷ map [_] xs)            ≡⟨⟩
    realizeₜ [] t₁ (map [_] (t₂ ∷ xs))              ≡⟨ ≡preFunc t₁ (t₂ ∷ xs) ⟩
    [ apps t₁ (t₂ ∷ xs)]                            ∎

module _ where
  open ClosedRealizer termModel

  ≡preRel : (R : ℜ l) (xs : Vec ClosedTerm l) →
    relMap R (map [_] xs) ≡ preRel (rel R) xs , squash₁
  ≡preRel R = quotientBeta ≋-refl isSetHProp _
    λ x → hPropExt $ preRel-pointwiseIff (rel R) x

  ≡[] : (t : ClosedTerm) → realizeₜ t ≡ [ t ]
  ≡[] t = ≡preFunc t []

  ≡map[] : (xs : Vec ClosedTerm l) → map realizeₜ xs ≡ map [_] xs
  ≡map[] [] = refl
  ≡map[] (x ∷ xs) = cong₂ _∷_ (≡[] x) (≡map[] xs)

open ClosedRealizer termModel

termModelCompleteGuarded : (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  count∀ φ < n → T ⊦ appsᵣ φ xs ↔ termModel ⊨ˢ appsᵣ φ xs
termModelCompleteGuarded {0} {suc n} ⊥ [] _ =
  →: elim (λ _ → isProp-⊨ˢ termModel ⊥) (lift ∘ H₁ .fst)
  ←: λ ()
termModelCompleteGuarded {l} {suc n} (rel R) xs H = hPropExt⁻ $ sym $
  termModel ⊨ˢ appsᵣ (rel R) xs , isProp-⊨ˢ _ _ ≡⟨ hPropExt $ realize-appsᵣ-iff [] (rel R) _ ⟩
  relMap R (map realizeₜ xs)                    ≡⟨ cong (relMap R) (≡map[] _) ⟩
  relMap R (map [_] xs)                         ≡⟨ ≡preRel _ _ ⟩
  preRel (rel R) xs , squash₁                   ≡⟨⟩
  ∥ T ⊢ appsᵣ (rel R) xs ∥ₚ                     ∎
termModelCompleteGuarded {l} {suc n} (appᵣ φ t) xs H with (unbound φ) in eq
... | rel _    = termModelCompleteGuarded φ (t ∷ xs) $ substEq (λ φ → Free.count∀ φ < suc n) (symEq eq) H
... | appᵣ _ _ = termModelCompleteGuarded φ (t ∷ xs) $ substEq (λ φ → Free.count∀ φ < suc n) (symEq eq) H
termModelCompleteGuarded {0} {suc n} (t₁ ≈ t₂) [] H =
  T ⊦ t₁ ≈ t₂               ↔⟨ →: eq/ _ _ ←: effective isPropValued≋ isEquivRel≋ _ _ ⟩
  [ t₁ ] ≡ [ t₂ ]           ↔≡⟨ subst2 (λ x y → (x ≡ y) ≡ (realizeₜ t₁ ≡ realizeₜ t₂)) (≡[] t₁) (≡[] t₂) refl ⟩
  realizeₜ t₁ ≡ realizeₜ t₂ ↔⟨⟩
  termModel ⊨ˢ t₁ ≈ t₂      ↔∎
termModelCompleteGuarded {0} {suc n} (φ₁ ⇒ φ₂) [] H =
  let IH₁ : T ⊦ appsᵣ φ₁ [] ↔ termModel ⊨ˢ appsᵣ φ₁ []
      IH₁ = termModelCompleteGuarded φ₁ [] $ ≤-trans (s≤s (m≤m+n _ _)) H
      IH₂ : T ⊦ appsᵣ φ₂ [] ↔ termModel ⊨ˢ appsᵣ φ₂ []
      IH₂ = termModelCompleteGuarded φ₂ [] $ ≤-trans (s≤s (m≤n+m _ _)) H
  in
    →: (λ ⊦ ⊨ → to IH₂ $ map2 ⇒-elim ⊦ $ from IH₁ ⊨)
    ←: (λ ⊨ → ⇒-intro-of-complete H₁ λ ⊦ → from IH₂ $ ⊨ $ to IH₁ ⊦)
termModelCompleteGuarded {0} {suc n} (∀' φ) [] H =
  →: (λ ⊦ t → {!   !})
  ←: {!   !}

termModelComplete : (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  T ⊦ appsᵣ φ xs ↔ termModel ⊨ˢ appsᵣ φ xs
termModelComplete φ xs = termModelCompleteGuarded φ xs (s≤s ≤-refl)

termModelWellDefined : termModel ⊨ᵀ T
termModelWellDefined φ φ∈T = to (termModelComplete φ []) ∣ axiom φ∈T ∣₁

-- completeness for complete theories with enough constanxs
open Implication (ℓ-suc u) using (_⊨_)
completeness : (φ : Sentence) → T ⊨ φ → T ⊦ φ
completeness φ T⊨φ = from (termModelComplete φ []) $
  T⊨φ termModel (nonempty H₂) termModelWellDefined
