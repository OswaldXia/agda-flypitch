{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
module FOL.Bounded.Lemmas.Satisfiability (ℒ : Language {u}) where

import FOL.Semantics ℒ as Free
open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.Bounded.Lemmas.Realization
open Closed using (realize-iff)

open import Agda.Builtin.Sigma using (_,_)
open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (isProp→isSet)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import CubicalExt.Foundations.Powerset* using (_⟦_⟧)
open import Cubical.HITs.PropositionalTruncation using (elim)
open import CubicalExt.HITs.SetTruncation using (∣_∣₂; map; sigmaElim)

open import Function using (_$_)
open import Function.Equality using (_⟨$⟩_) public
open import StdlibExt.Relation.Binary.PropositionalEquivalence hiding (map)

bound⊨ : ∀ {Γ φ} → ⟨ map unbound ⟦ Γ ⟧ Free.⊨ map unbound φ ⟩ → ⟨ Γ ⊨ φ ⟩
bound⊨ {Γ} {φ} ⊨ 𝒮 x vld = let 𝓋 = λ _ → x in {! realize-iff 𝒮 𝓋 φ  !}
  --from (realize-iff 𝒮 𝓋 φ) ⟨$⟩ ⊨ 𝒮 𝓋 λ { ψ' (ψ , ψ∈Γ , refl) →
  --to (realize-iff 𝒮 𝓋 ψ) ⟨$⟩ vld ψ ψ∈Γ
