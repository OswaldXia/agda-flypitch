{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Language.Homomorphism as LHom using (_⟶_)
module FOL.Structure.Reduction.Properties {ℒ₁ ℒ₂ : Language {u}} (F : ℒ₁ ⟶ ℒ₂) where
open LHom.OnBounded F
open _⟶_ F

open import FOL.Structure.Base {u}
open import FOL.Structure.Reduction.Base F
open Structure

open import FOL.Bounded.Base ℒ₁
open import FOL.Bounded.Semantics
open PreRealizer

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

private variable
  n : ℕ

module _ {v} {𝒮 : Structure ℒ₂ {v}} where
  realizeₜ-reduct-eq : (𝓋 : Vec (Domain 𝒮) n) (t : Termₗ n l) (xs : Vec (Domain 𝒮) l) →
    realizeₜ ℒ₂ 𝒮 𝓋 (termMorph t) xs ≡ realizeₜ ℒ₁ ⟦ 𝒮 ⟧ 𝓋 t xs
  realizeₜ-reduct-eq 𝓋 (var k)     xs = refl
  realizeₜ-reduct-eq 𝓋 (func f)    xs = refl
  realizeₜ-reduct-eq 𝓋 (app t₁ t₂) xs
    rewrite realizeₜ-reduct-eq 𝓋 t₂ []
          | realizeₜ-reduct-eq 𝓋 t₁ (realizeₜ ℒ₁ ⟦ 𝒮 ⟧ 𝓋 t₂ [] ∷ xs) = refl

  module _ (inj : injective) where
    
