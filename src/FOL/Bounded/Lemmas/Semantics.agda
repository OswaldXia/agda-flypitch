{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Bounded.Lemmas.Semantics ⦃ em : EM ⦄ (ℒ : Language {u}) where

open import FOL.Bounded.Base ⦃ em ⦄ ℒ
open import FOL.Bounded.Semantics ⦃ em ⦄ ℒ
open import FOL.Bounded.Lemmas.Realization ⦃ em ⦄
import FOL.Semantics ⦃ em ⦄ ℒ as Free
open Free.Realizer using (isPropRealize)
open Closed using (realize-iff)

open import Cubical.Core.Id using (reflId)
open import CubicalExt.Foundations.Powerset* using (_⟦_⟧)
open import Cubical.HITs.PropositionalTruncation using (elim)

open import Agda.Builtin.Sigma using (_,_)
open import Function.Equality using (_⟨$⟩_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import StdlibExt.Relation.Binary.PropositionalEquivalence

bound⊨ : ∀ {Γ φ} → unbound ⟦ Γ ⟧ Free.⊨ unbound φ → Γ ⊨ φ
bound⊨ {Γ} {φ} ⊨ 𝒮 x vld = let 𝓋 = λ _ → x in
  from (realize-iff 𝒮 𝓋 φ) ⟨$⟩ ⊨ 𝒮 𝓋 λ φ' →
    elim (λ _ → isPropRealize _ _ _) λ { (ψ , ψ∈Γ , reflId) →
      to (realize-iff 𝒮 𝓋 ψ) ⟨$⟩ (vld ψ ψ∈Γ) }
