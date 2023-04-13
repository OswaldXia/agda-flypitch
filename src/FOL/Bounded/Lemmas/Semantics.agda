{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
module FOL.Bounded.Lemmas.Semantics (ℒ : Language {u}) where

import FOL.Semantics ℒ as Free
open import FOL.Bounded.Truncated ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.Bounded.Lemmas.Realization
open Closed using (realize-eq)

open import Cubical.Core.Primitives
open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (sym; subst)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Functions.Logic using (isProp⟨⟩)
open import Cubical.HITs.PropositionalTruncation using (elim)
open import CubicalExt.Foundations.Powerset* using (_⟦_⟧)
open import CubicalExt.HITs.SetTruncation using (map)
open import Function using (_$_)

bound⊨ : ∀ {Γ φ} → unbound ⟦ Γ ⟧ Free.⊨ unbound φ → Γ ⊨ φ
bound⊨ {Γ} {φ} free⊨ 𝒮 x 𝒮⊨φ = let 𝓋 = λ _ → x in
  subst ⟨_⟩ (sym $ realize-eq 𝒮 𝓋 φ) $ free⊨ 𝒮 𝓋 λ _ →
    elim (λ x → isProp⟨⟩ _) $ λ { (ψ , ψ∈Γ , reflId) →
      subst ⟨_⟩ (realize-eq 𝒮 𝓋 ψ) (𝒮⊨φ ψ ψ∈Γ) }
