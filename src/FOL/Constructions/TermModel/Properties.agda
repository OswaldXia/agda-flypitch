{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import FOL.Bounded.Syntactics using (Theory)
open import FOL.Bounded.PropertiesOfTheory using (complete; hasEnoughConstants)
module FOL.Constructions.TermModel.Properties {ℒ : Language {u}} {T : Theory ℒ}
  (H₁ : complete ℒ T) (H₂ : hasEnoughConstants ℒ T) where
open import FOL.Constructions.TermModel.Base
open TermModel using (nonempty; preFunc; preFunc-pointwiseEq)

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.Constructions.Equivalence.BoundedTruncated T

open import Cubical.Foundations.Prelude
open import CubicalExt.Foundations.Powerset* using (_∈_)
open import CubicalExt.Data.Vec using (quotientBeta)
open import Cubical.HITs.SetQuotients using ([_]; eq/; squash/; effective)

open import Data.Nat
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec using (Vec; []; _∷_; map)
open import Function using (_$_)

module _ where
  open PreRealizer (termModel T)

  realize≡[] : (t : ClosedTermₗ l) (xs : Vec ClosedTerm l) →
    realizeₜ [] t (map [_] xs) ≡ [ apps t xs ]
  realize≡[] (func f) = quotientBeta ≋-refl squash/ (preFunc T (func f)) (preFunc-pointwiseEq T (func f))
  realize≡[] (app t₁ t₂) xs =
    realizeₜ [] t₁ (realizeₜ [] t₂ [] ∷ map [_] xs) ≡⟨ cong (λ x → realizeₜ [] t₁ (x ∷ _)) (realize≡[] t₂ []) ⟩
    realizeₜ [] t₁ ([ t₂ ] ∷ map [_] xs)            ≡⟨⟩
    realizeₜ [] t₁ (map [_] (t₂ ∷ xs))              ≡⟨ realize≡[] t₁ (t₂ ∷ xs) ⟩
    [ apps t₁ (t₂ ∷ xs)]                            ∎

termModelSound : {n : ℕ} (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  count∀ φ < n → T ⊢ appsᵣ φ xs → termModel T ⊨ˢ appsᵣ φ xs
termModelSound {_} {zero} _ _ ()
termModelSound {0} {suc n} ⊥          [] _ ⊢⊥ = lift $ H₁ .fst ⊢⊥
termModelSound {l} {suc n} (rel R)    xs < ⊢R = {!   !}
termModelSound {l} {suc n} (appᵣ φ t) xs < = {!   !}
termModelSound {0} {suc n} (t₁ ≈ t₂)  [] < ⊢≈ = subst2 _≡_ (sym $ realize≡[] _ _) (sym $ realize≡[] _ _) (eq/ {!   !} {!   !} {!   !})
  --subst2 _≡_ (sym $ realize≡[] _ _) (sym $ realize≡[] _ _) (eq/ _ _ ⊢≈)
termModelSound {0} {suc n} (φ ⇒ φ₁)   xs < = {!   !}
termModelSound {0} {suc n} (∀' φ)     xs < = {!   !}

termModelComplete : {n : ℕ} (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  count∀ φ < n → termModel T ⊨ˢ appsᵣ φ xs → T ⊢ appsᵣ φ xs
termModelComplete {_} {zero} _ _ ()
termModelComplete {0} {suc n} ⊥ [] _ ()
termModelComplete {l} {suc n} (rel R)    xs < = {!   !}
termModelComplete {l} {suc n} (appᵣ φ t) xs < = {!   !}
termModelComplete {0} {suc n} (t₁ ≈ t₂)  [] < ⊨≈ = {!   !}
  --effective {!   !} {! ≋-refl  !} _ _ $
  --subst2 _≡_ (realize≡[] _ _) (realize≡[] _ _) ⊨≈
termModelComplete {0} {suc n} (φ ⇒ φ₁)   xs < = {!   !}
termModelComplete {0} {suc n} (∀' φ)     xs < = {!   !}

termModelWellDefined : termModel T ⊨ᵀ T
termModelWellDefined φ φ∈T = termModelSound φ [] (s≤s ≤-refl) (axiom φ∈T)

-- completeness for complete theories with enough constants
open Implication (ℓ-suc u) using (_⊨_)
completeness : (φ : Sentence) → T ⊨ φ → T ⊢ φ
completeness φ T⊨φ = termModelComplete φ [] (s≤s ≤-refl) $
  T⊨φ (termModel T) (nonempty T H₂) termModelWellDefined
