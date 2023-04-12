{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Bounded.Lemmas.Satisfiability (ℒ : Language {u}) where

import FOL.Interpretation ℒ as Free
open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Interpretation ℒ
open import FOL.Bounded.Lemmas.Realization
open Closed using (realize-iff)

open import Agda.Builtin.Sigma using (_,_)
open import Cubical.Core.Id using (reflId)
open import CubicalExt.Foundations.Powerset* using (_⟦_⟧)
open import Cubical.HITs.PropositionalTruncation using (elim)
open import CubicalExt.HITs.SetTruncation using (∣_∣₂; map)

open import Function.Equality using (_⟨$⟩_) public
open import StdlibExt.Relation.Binary.PropositionalEquivalence hiding (map)

bound⊨ : ∀ {Γ φ} → map unbound ⟦ Γ ⟧ Free.⊨ unbound φ → Γ ⊨ φ
bound⊨ {Γ} {φ} ⊨ 𝒮 x vld = let 𝓋 = λ _ → x in
  from (realize-iff 𝒮 𝓋 φ) ⟨$⟩ ⊨ 𝒮 𝓋
    λ { ψ' → elim (λ _ → isPropRealization 𝓋 ψ')
      λ { (ψ , ψ∈Γ , fuck) → {!  realize-iff 𝒮 𝓋  !}
    }}
  --from (realize-iff 𝒮 𝓋 φ) ⟨$⟩ ⊨ 𝒮 𝓋 λ { ψ' (ψ , ψ∈Γ , refl) →
  --to   (realize-iff 𝒮 𝓋 ψ) ⟨$⟩ vld ψ ψ∈Γ }
  where open Free.Realizer 𝒮 using (isPropRealization)
