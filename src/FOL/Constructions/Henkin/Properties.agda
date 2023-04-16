{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Constructions.Henkin.Properties ⦃ _ : EM ⦄ (ℒ : Language {u}) where
open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Constructions.Henkin.TermChain u
open import FOL.Constructions.Henkin.FormulaChain u
open import FOL.Constructions.Henkin.Witness u
open import FOL.Constructions.Henkin.TheoryChain u

import FOL.Base (∞-language ℒ) as Free
open import FOL.Syntactics (∞-language ℒ) using (axiom)
open import FOL.Bounded.Base (∞-language ℒ) using (_⇒_; ∃'_; unbound)
open import FOL.Bounded.Syntactics (∞-language ℒ) using (_⊢_)
open import FOL.Bounded.PropertiesOfTheory (∞-language ℒ)
  using (hasEnoughConstants; [_witnessing_])
open Language (∞-language ℒ) using (Constant)

import FOL.Language.Homomorphism as LHom
open LHom.Bounded using (formulaMorph)

open import Tools.DirectedDiagram using (Cocone)
open Cocone (coconeOfTermChain ℒ 0 0) renaming (map to mapₜ)
open Cocone (coconeOfFormulaChain ℒ 0 0) renaming (map to map0)
open Cocone (coconeOfFormulaChain ℒ 1 0) renaming (map to map1)

open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude renaming (subst to substPath)
open import Cubical.Foundations.Id using (pathToId)
open import Cubical.Functions.Logic using (inl; inr)
open import Cubical.Data.Unit using (tt*)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim)
open import CubicalExt.Foundations.Powerset* using (_∈_; ∈-isProp)

open import Data.Nat using (ℕ; suc; _+_)
open import Function using (_$_)

∞-theory-hasEnoughConstants : ∀ T → hasEnoughConstants $ ∞-theory T
∞-theory-hasEnoughConstants T φ =
  elim {P = λ _ → ∃[ c ∈ Constant ] (∞-theory T) ⊢ [ c witnessing φ ]}
    (λ _ → squash₁)
    (λ { (c , φ∞ , φₚ@(i , φᵢ) , [φₚ]≡φ∞ , fCφ∞≡φ , c≡) →
      ∣_∣₁ $ c ,_ $ axiom $ ∣_∣₁ $
        map0 (suc i) (witnessStatement φᵢ)
      , ∣ suc i , ∈-∞-theory i (witnessStatement φᵢ) (inr ∣ φᵢ , tt* , reflId ∣₁) ∣₁
      , let open LHom._⟶_ (languageCanonicalMorph {ℒ} (suc i)) using (funMorph)
            ψ = formulaMorph languageMorph φᵢ in
        pathToId (cong unbound $
          [ c witnessing φ ]
            ≡⟨ cong [_witnessing φ ] c≡ ⟩
          [ funMorph (witnessOf φᵢ) witnessing φ ]
            ≡⟨⟩
          ∃' φ ⇒ subst _ {0} φ (const _ (funMorph (witnessOf φᵢ)))
            ≡⟨ {!   !} ⟩
          ∃' (map1 (suc i) ψ) ⇒ subst _ {0} (map1 (suc i) ψ) (const _ (funMorph (witnessOf φᵢ)))
            ≡⟨ {!   !} ⟩
          ∃' (map1 (suc i) ψ) ⇒ map0 (suc i) (subst _ {0} ψ (const _ (witnessOf φᵢ)))
            ≡⟨⟩
          map0 (suc i) (witnessStatement φᵢ) ∎)
    })
    (∞-witnessing φ)
  where open import FOL.Bounded.Base using (const)
        open import FOL.Bounded.Substitution using (subst)
