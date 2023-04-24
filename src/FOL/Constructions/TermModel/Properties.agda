{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import FOL.Bounded.Syntactics using (Theory)
open import FOL.Bounded.PropertiesOfTheory using (complete; hasEnoughConstants)
module FOL.Constructions.TermModel.Properties {ℒ : Language {u}} {T : Theory ℒ}
  (H₁ : complete ℒ T) (H₂ : hasEnoughConstants ℒ T) where
open Language ℒ

open import FOL.Constructions.TermModel.Base T
open TermModel using (nonempty; preFunc; preFunc-pointwiseEq)

open import FOL.Structure.Base using (Structure)
open Structure termModel using (Domain; relMap)

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.Constructions.Equivalence.BoundedTruncated T

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import CubicalExt.Foundations.Powerset* using (_∈_)
open import CubicalExt.Functions.Logic.Iff
open import CubicalExt.Data.Vec using (quotientBeta)
open import Cubical.HITs.SetQuotients using ([_]; eq/; squash/; effective)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open import Data.Nat
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec using (Vec; []; _∷_; map)
open import Function using (_$_)

private variable
  n : ℕ

module _ where
  open PreRealizer termModel

  realizeFunc≡ : (f : ClosedTermₗ l) (xs : Vec ClosedTerm l) →
    realizeₜ [] f (map [_] xs) ≡ preFunc f xs
  realizeFunc≡ (func f) = quotientBeta ≋-refl squash/ (preFunc (func f)) (preFunc-pointwiseEq (func f))
  realizeFunc≡ (app t₁ t₂) xs =
    realizeₜ [] t₁ (realizeₜ [] t₂ [] ∷ map [_] xs) ≡⟨ cong (λ x → realizeₜ [] t₁ (x ∷ _)) (realizeFunc≡ t₂ []) ⟩
    realizeₜ [] t₁ ([ t₂ ] ∷ map [_] xs)            ≡⟨⟩
    realizeₜ [] t₁ (map [_] (t₂ ∷ xs))              ≡⟨ realizeFunc≡ t₁ (t₂ ∷ xs) ⟩
    [ apps t₁ (t₂ ∷ xs)]                            ∎

  realizeAppsᵣ↔ : (𝓋 : Vec Domain n) (r : Formulaₗ n l) (xs : Vec (Term n) l) →
    realize 𝓋 (appsᵣ r xs) [] ↔ realize 𝓋 r (map (λ t → realizeₜ 𝓋 t []) xs)
  realizeAppsᵣ↔ 𝓋 r [] = ↔-refl
  realizeAppsᵣ↔ 𝓋 r (x ∷ xs) = realizeAppsᵣ↔ 𝓋 (appᵣ r x) xs

module _ where
  open ClosedRealizer termModel

  realizeTerm≡ : (t : ClosedTerm) → realizeₜ t ≡ [ t ]
  realizeTerm≡ t = realizeFunc≡ t []

  realizeRel↔ : (R : ℜ l) (xs : Vec ClosedTerm l) →
    realize (appsᵣ (rel R) xs) ↔ ⟨ relMap R (map realizeₜ xs) ⟩
  realizeRel↔ R = realizeAppsᵣ↔ [] (rel R)

termModelSound : {n : ℕ} (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  count∀ φ < n → T ⊢ appsᵣ φ xs → termModel ⊨ˢ appsᵣ φ xs
termModelSound {_} {zero} _ _ ()
termModelSound {0} {suc n} ⊥          [] _ ⊢⊥ = lift $ H₁ .fst ⊢⊥
termModelSound {l} {suc n} (rel R)    xs < ⊢R = from (realizeRel↔ R xs) {!   !}
termModelSound {l} {suc n} (appᵣ φ t) xs < = {!   !}
termModelSound {0} {suc n} (t₁ ≈ t₂)  [] < ⊢≈ =
  subst2 _≡_ (sym $ realizeTerm≡ _) (sym $ realizeTerm≡ _) (eq/ _ _ ∣ ⊢≈ ∣₁)
termModelSound {0} {suc n} (φ ⇒ φ₁)   xs < = {!   !}
termModelSound {0} {suc n} (∀' φ)     xs < = {!   !}

termModelComplete : {n : ℕ} (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  count∀ φ < n → termModel ⊨ˢ appsᵣ φ xs → T ⊦ appsᵣ φ xs
termModelComplete {_} {zero} _ _ ()
termModelComplete {0} {suc n} ⊥ [] _ ()
termModelComplete {l} {suc n} (rel R)    xs < H = {!   !}
termModelComplete {l} {suc n} (appᵣ φ t) xs < = {!   !}
termModelComplete {0} {suc n} (t₁ ≈ t₂)  [] < ⊨≈ = effective isPropValued≋ isEquivRel≋ _ _ $
  subst2 _≡_ (realizeTerm≡ _) (realizeTerm≡ _) ⊨≈
termModelComplete {0} {suc n} (φ ⇒ φ₁)   xs < = {!   !}
termModelComplete {0} {suc n} (∀' φ)     xs < = {!   !}

termModelWellDefined : termModel ⊨ᵀ T
termModelWellDefined φ φ∈T = termModelSound φ [] (s≤s ≤-refl) (axiom φ∈T)

-- completeness for complete theories with enough constanxs
open Implication (ℓ-suc u) using (_⊨_)
completeness : (φ : Sentence) → T ⊨ φ → T ⊦ φ
completeness φ T⊨φ = termModelComplete φ [] (s≤s ≤-refl) $
  T⊨φ termModel (nonempty H₂) termModelWellDefined
