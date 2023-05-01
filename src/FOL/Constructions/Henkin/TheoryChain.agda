{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Constructions.Henkin.TheoryChain ⦃ _ : ∀ {ℓ} → EM ℓ ⦄ u where
open import FOL.Constructions.Henkin.Base
open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Constructions.Henkin.FormulaChain u using (coconeOfFormulaChain)
open import FOL.Constructions.Henkin.Witness u using (witnessStatement)

import FOL.Language.Homomorphism as LHom
open import FOL.Bounded.Base using (Formula; Sentence)
open import FOL.Bounded.Syntactics using (Theory)
open import FOL.Language hiding (u)
open Language {u}

open import Cubical.Core.Primitives
open import Cubical.Core.Id using (reflId)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
import Cubical.Data.Sum as ⊎
open import Cubical.Functions.Logic using (inl; inr)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; elim)

open import StdlibExt.Data.Nat hiding (_/_)
open import Function using (_$_)
open import CubicalExt.Foundations.Powerset* using (_∈_; ∈-isProp; _∪_; ⋃_; _⟦_⟧; replacement-syntax)

theoryStep : Theory ℒ → Theory $ languageStep ℒ
theoryStep {ℒ} Γ = theoryMorph Γ ∪ ｛ witnessStatement φ ∣ φ ∈ Formula ℒ 1 ｝
  where open LHom.OnBounded (languageMorph {ℒ})

[_]-theory : ∀ n → Theory ℒ → Theory $ [ n ]-language ℒ
[ zero ]-theory T = T
[ suc n ]-theory T = theoryStep $ [ n ]-theory T

[_]→∞-theory : ℕ → Theory ℒ → Theory $ ∞-language ℒ
[ n ]→∞-theory T = theoryMorph ([ n ]-theory T)
  where open LHom.OnBounded (languageCanonicalMorph n)

∞-theory : Theory ℒ → Theory $ ∞-language ℒ
∞-theory T = ⋃ (λ n → [ n ]→∞-theory T)

module _ {ℒ : Language} where
  open import Tools.DirectedDiagram using (Cocone)
  open Cocone (coconeOfFormulaChain ℒ 0 0) using (map)

  ∈-∞-theory : ∀ {T : Theory ℒ} (i : ℕ) (φ : Sentence $ obj ℒ $ suc i) →
    φ ∈ [ suc i ]-theory T → map (suc i) φ ∈ [ suc i ]→∞-theory T
  ∈-∞-theory {ℒ} i φ = elim (λ _ → ∈-isProp _ _)
    λ { (⊎.inl ∈) → ∣ φ , inl ∈ , reflId ∣₁
      ; (⊎.inr ∈) → ∣ φ , inr ∈ , reflId ∣₁ }
