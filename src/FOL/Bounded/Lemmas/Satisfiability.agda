{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
module FOL.Bounded.Lemmas.Satisfiability (ℒ : Language {u}) where

import FOL.Semantics ℒ as Free
open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.Bounded.Lemmas.Realization
open Closed using (realize-iff)

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude using (subst)
open import CubicalExt.Foundations.Powerset* using (_⟦_⟧)
open import CubicalExt.HITs.SetTruncation using (∣_∣₂; map; elim; sigmaElim)
open import Function using (_$_)

bound⊨ : ∀ {Γ φ} → map unbound ⟦ Γ ⟧ Free.⊨ map unbound φ → Γ ⊨ φ
bound⊨ {Γ} {φ} ⊨ 𝒮 x vld = let 𝓋 = λ _ → x in {!   !}
  --from (realize-iff 𝒮 𝓋 φ) ⟨$⟩ ⊨ 𝒮 𝓋 λ { ψ' (ψ , ψ∈Γ , refl) →
  --to (realize-iff 𝒮 𝓋 ψ) ⟨$⟩ vld ψ ψ∈Γ
