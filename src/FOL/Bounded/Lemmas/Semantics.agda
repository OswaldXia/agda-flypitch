{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
module FOL.Bounded.Lemmas.Semantics (ℒ : Language {u}) v where

module Free where
  open import FOL.Semantics ℒ
  open Implication v using (_⊨_) public
  open Realizer using (isPropRealize) public
open import FOL.Bounded.Semantics ℒ
open Implication v using (_⊨_)

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Lemmas.Realization
open Closed using (realize-iff)

open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (_,_)
open import CubicalExt.Foundations.Powerset* using (_⟦_⟧)
open import CubicalExt.Functions.Logic.Iff
open import Cubical.HITs.PropositionalTruncation using (elim)
open import Function using (flip; _$_)

bound⊨ : ∀ {Γ φ} → unbound ⟦ Γ ⟧ Free.⊨ unbound φ → Γ ⊨ φ
bound⊨ {Γ} {φ} ⊨ 𝒮 = flip $ λ vld →
  elim (λ _ → isProp-⊨ˢ _ _) λ x → let 𝓋 = λ _ → x in
    from (realize-iff 𝒮 𝓋 φ) $ ⊨ 𝒮 𝓋 λ φ' →
      elim (λ _ → Free.isPropRealize _ _ _) $ λ { (ψ , ψ∈Γ , reflId) →
        to (realize-iff 𝒮 𝓋 ψ) (vld ψ ψ∈Γ) }
