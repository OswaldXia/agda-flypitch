{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import FOL.Bounded.Syntactics using (Theory)
open import FOL.Bounded.PropertiesOfTheory using (complete; hasEnoughConstants)
module FOL.Constructions.TermModel.Properties {ℒ : Language {u}} {T : Theory ℒ}
  (H₁ : complete ℒ T) (H₂ : hasEnoughConstants ℒ T) where
open Language ℒ

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.Constructions.Equivalence.BoundedTruncated T

import FOL.Base ℒ as Free
open Free.Formulaₗ

open import FOL.Constructions.TermModel.Base T
open TermModel using (nonempty; preFunc; preRel; preFunc-pointwiseEq; preRel-pointwiseIff)

open import FOL.Structure.Base using (Structure)
open Structure termModel using (Domain; relMap)

open import Cubical.Foundations.Prelude renaming (_,_ to infix 5 _,_)
open import Cubical.Foundations.HLevels using (isSetHProp)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import CubicalExt.Foundations.Powerset* using (_∈_)
open import Cubical.Functions.Logic using (∥_∥ₚ)
open import CubicalExt.Functions.Logic.Iff
open import CubicalExt.Data.Vec using (quotientBeta)
open import Cubical.HITs.SetQuotients using ([_]; eq/; squash/; effective)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim)

open import Data.Nat
open import Data.Nat.Properties using (≤-refl)
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

  realizeAppsᵣ↔ : (𝓋 : Vec Domain n) (r : Formulaₗ n l) (xs : Vec (Term n) l) →
    realize 𝓋 (appsᵣ r xs) [] ↔ realize 𝓋 r (map (λ t → realizeₜ 𝓋 t []) xs)
  realizeAppsᵣ↔ 𝓋 r [] = ↔-refl
  realizeAppsᵣ↔ 𝓋 r (x ∷ xs) = realizeAppsᵣ↔ 𝓋 (appᵣ r x) xs

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

hPropEqual : (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  count∀ φ < n → ∥ T ⊢ appsᵣ φ xs ∥ₚ ≡ termModel ⊨ˢ appsᵣ φ xs , isProp-⊨ˢ _ _
hPropEqual {0} {suc n} ⊥ [] _ = hPropExt $
  →: elim (λ _ → isProp-⊨ˢ termModel ⊥) (lift ∘ H₁ .fst)
  ←: λ ()
hPropEqual {l} {suc n} (rel R) xs H = sym $
  termModel ⊨ˢ appsᵣ (rel R) xs , _ ≡⟨ hPropExt $ realizeAppsᵣ↔ [] (rel R) _ ⟩
  relMap R (map realizeₜ xs)        ≡⟨ cong (relMap R) (≡map[] _) ⟩
  relMap R (map [_] xs)             ≡⟨ ≡preRel _ _ ⟩
  preRel (rel R) xs , squash₁       ≡⟨⟩
  ∥ T ⊢ appsᵣ (rel R) xs ∥ₚ         ∎
hPropEqual {l} {suc n} (appᵣ φ t) xs H with (unbound φ) in eq
... | rel _    = hPropEqual φ (t ∷ xs) $ substEq (λ φ → Free.count∀ φ < suc n) (symEq eq) H
... | appᵣ _ _ = hPropEqual φ (t ∷ xs) $ substEq (λ φ → Free.count∀ φ < suc n) (symEq eq) H
hPropEqual {0} {suc n} (t₁ ≈ t₂) [] H = hPropExt $
  T ⊦ t₁ ≈ t₂               ↔⟨ →: eq/ _ _ ←: effective isPropValued≋ isEquivRel≋ _ _ ⟩
  [ t₁ ] ≡ [ t₂ ]           ↔≡⟨ subst2 (λ x y → (x ≡ y) ≡ (realizeₜ t₁ ≡ realizeₜ t₂)) (≡[] t₁) (≡[] t₂) refl ⟩
  realizeₜ t₁ ≡ realizeₜ t₂ ↔⟨⟩
  termModel ⊨ˢ t₁ ≈ t₂      ↔∎
hPropEqual {0} {suc n} (φ ⇒ φ₁) xs H = {!   !}
hPropEqual {0} {suc n} (∀' φ) xs H = {!   !}

termModelComplete : (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  T ⊦ appsᵣ φ xs ↔ termModel ⊨ˢ appsᵣ φ xs
termModelComplete φ xs = hPropExt⁻ $ hPropEqual φ xs (s≤s ≤-refl)

termModelWellDefined : termModel ⊨ᵀ T
termModelWellDefined φ φ∈T = to (termModelComplete φ []) ∣ axiom φ∈T ∣₁

-- completeness for complete theories with enough constanxs
open Implication (ℓ-suc u) using (_⊨_)
completeness : (φ : Sentence) → T ⊨ φ → T ⊦ φ
completeness φ T⊨φ = from (termModelComplete φ []) $
  T⊨φ termModel (nonempty H₂) termModelWellDefined
