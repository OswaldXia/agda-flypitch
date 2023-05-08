{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Structure.Base
open import FOL.Language.Homomorphism as LHom using (_⟶_)
module FOL.Structure.Reduction.Properties {v} {ℒ₁ ℒ₂ : Language {u}} (F : ℒ₁ ⟶ ℒ₂) (𝒮 : Structure ℒ₂ {v}) where
open LHom.OnBounded F
open _⟶_ F

open import FOL.Structure.Reduction.Base F
open Structure

open import FOL.Bounded.Base ℒ₁
open import FOL.Bounded.Syntactics ℒ₁
import FOL.Bounded.Semantics as Semantics
open Semantics ℒ₁ renaming (_⊨ˢ_ to _⊨ˢ₁_; _⊨ᵀ_ to _⊨ᵀ₁_)
open Semantics ℒ₂ renaming (_⊨ˢ_ to _⊨ˢ₂_; _⊨ᵀ_ to _⊨ᵀ₂_)
open Semantics.PreRealizer

open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (_,_)
open import CubicalExt.Functions.Logic.Iff
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

private variable
  n : ℕ

reductNonempty : nonempty 𝒮 → nonempty ⟦ 𝒮 ⟧
reductNonempty = rec squash₁ (λ x → ∣ (reductId 𝒮 x) ∣₁)

module _ (𝓋 : Vec (Domain 𝒮) n) where
  realizeₜ-reduct-eq : (t : Termₗ n l) (xs : Vec (Domain 𝒮) l) →
    realizeₜ ℒ₂ 𝒮 𝓋 (termMorph t) xs ≡ realizeₜ ℒ₁ ⟦ 𝒮 ⟧ 𝓋 t xs
  realizeₜ-reduct-eq (var k)  xs = refl
  realizeₜ-reduct-eq (func f) xs = refl
  realizeₜ-reduct-eq (app t₁ t₂) xs
    rewrite realizeₜ-reduct-eq t₂ []
          | realizeₜ-reduct-eq t₁ (realizeₜ ℒ₁ ⟦ 𝒮 ⟧ 𝓋 t₂ [] ∷ xs) = refl

realize-reduct-iff : (𝓋 : Vec (Domain 𝒮) n) (φ : Formulaₗ n l) (xs : Vec (Domain 𝒮) l) →
  realize ℒ₂ 𝒮 𝓋 (formulaMorph φ) xs ↔ realize ℒ₁ ⟦ 𝒮 ⟧ 𝓋 φ xs
realize-reduct-iff 𝓋 ⊥ [] = ↔-refl
realize-reduct-iff 𝓋 (rel R) xs = ↔-refl
realize-reduct-iff 𝓋 (appᵣ φ t) xs
  rewrite realizeₜ-reduct-eq 𝓋 t [] = realize-reduct-iff 𝓋 φ _
realize-reduct-iff 𝓋 (t₁ ≈ t₂) []
  rewrite realizeₜ-reduct-eq 𝓋 t₁ []
        | realizeₜ-reduct-eq 𝓋 t₂ [] = ↔-refl
realize-reduct-iff 𝓋 (φ₁ ⇒ φ₂) [] = →↔→
  (realize-reduct-iff 𝓋 φ₁ [])
  (realize-reduct-iff 𝓋 φ₂ [])
realize-reduct-iff 𝓋 (∀' φ) [] = Π↔Π λ x → realize-reduct-iff (x ∷ 𝓋) φ []

reduct⊨ˢ : (φ : Sentence) → 𝒮 ⊨ˢ₂ sentenceMorph φ → ⟦ 𝒮 ⟧ ⊨ˢ₁ φ
reduct⊨ˢ φ = to (realize-reduct-iff [] φ [])

reduct⊨ᵀ : (T : Theory) → 𝒮 ⊨ᵀ₂ theoryMorph T → ⟦ 𝒮 ⟧ ⊨ᵀ₁ T
reduct⊨ᵀ T ⊨₂ φ φ∈T = reduct⊨ˢ φ (⊨₂ (sentenceMorph φ) ∣ φ , φ∈T , reflId ∣₁)
