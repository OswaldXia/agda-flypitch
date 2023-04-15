{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Constructions.Henkin.Properties ⦃ em : EM ⦄ (ℒ : Language {u}) where
open import FOL.Constructions.Henkin.LanguageChain ⦃ em ⦄ u
open import FOL.Constructions.Henkin.FormulaChain ⦃ em ⦄ u
open import FOL.Constructions.Henkin.Witness ⦃ em ⦄ u
open import FOL.Constructions.Henkin.TheoryChain ⦃ em ⦄ u

open import FOL.Base ⦃ em ⦄ (∞-language ℒ) using (∃'_; _⇒_)
open import FOL.Syntactics ⦃ em ⦄ (∞-language ℒ) using (axiom)
open import FOL.Bounded.Base ⦃ em ⦄ (∞-language ℒ) using (unbound)
open import FOL.Bounded.Syntactics ⦃ em ⦄ (∞-language ℒ) using (_⊢_)
open import FOL.Bounded.PropertiesOfTheory ⦃ em ⦄ (∞-language ℒ)
  using (hasEnoughConstants; [_witnessing_])
open Language (∞-language ℒ) using (Constant)

import FOL.Language.Homomorphism as LHom
open LHom.Bounded using (formulaMorph)

open import Tools.DirectedDiagram using (Cocone)
open Cocone (coconeOfFormulaChain ℒ 0 0) renaming (map to map0)
open Cocone (coconeOfFormulaChain ℒ 1 0) renaming (map to map1)

open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude hiding (subst)
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
    (λ { (c , φ∞ , φₚ@(i , φᵢ) , [φₚ]≡φ∞ , fCφ∞≡∣φ∣₂ , c≡) →
      ∣_∣₁ $ c ,_ $ axiom $ ∣_∣₁ $
        map0 (suc i) (witnessStatement φᵢ)
      , ∣ suc i , ∈-∞-theory i (witnessStatement φᵢ) (inr ∣ φᵢ , tt* , reflId ∣₁) ∣₁
      , pathToId (H c φ i φᵢ)
    })
    (∞-witnessing φ)
  where
  open import FOL.Bounded.Base ⦃ em ⦄ using (Formula)
  H : (c : Constant) (φ : Formula (∞-language ℒ) 1) (i : ℕ) (φᵢ : Formula ([ i ]-language ℒ) 1) →
    unbound [ c witnessing φ ] ≡ unbound (map0 (suc i) (witnessStatement φᵢ))
  H c φ i φᵢ =
    unbound [ c witnessing φ ]
      ≡⟨ {!   !} ⟩
    ∃' (unbound (map1 (suc i) (formulaMorph languageMorph φᵢ)))
      ⇒ unbound (map0 (suc i) (formulaMorph languageMorph φᵢ [ const (witnessOf φᵢ) / 0 ]))
      ≡⟨⟩
    unbound (map0 (suc i) (witnessStatement φᵢ)) ∎
    where open import FOL.Bounded.Base ⦃ em ⦄ (languageStep ([ i ]-language ℒ)) using (const)
          open import FOL.Bounded.Substitution ⦃ em ⦄ (languageStep ([ i ]-language ℒ)) using (subst)
