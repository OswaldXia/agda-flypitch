{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Constructions.Henkin.Witness ⦃ em : EM ⦄ u where
open import FOL.Constructions.Henkin.Base
open import FOL.Constructions.Henkin.LanguageChain u
  using (obj; languageStep; languageMorph; ∞-language; languageCanonicalMorph)
open import FOL.Constructions.Henkin.FormulaChain u
  using (formulaChain; formulaComparison; formulaComparisonFiber)
open import FOL.Bounded.Base using (Formula; Sentence)
open import FOL.Language hiding (u)
open Language {u}

import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_)
open LHom._⟶_ using (funMorph)

open import Tools.DirectedDiagram using (DirectedDiagram; Cocone)
open DirectedDiagram using (Colimit; Coproduct)

open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (Type; Σ-syntax; _,_) renaming (_≡_ to _≡ₚ_)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
open import Cubical.Functions.Logic using (inl; inr)
open import Cubical.HITs.SetQuotients using ([_])
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim)

open import StdlibExt.Data.Nat hiding (_/_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

witnessOf : Formula ℒ 1 → Constant $ languageStep ℒ
witnessOf = witness

witnessStatement : Formula ℒ 1 → Sentence $ languageStep ℒ
witnessStatement {ℒ} φ = [ witnessOf φ witnessing formulaMorph φ ]
  where open LHom.Bounded (languageMorph {ℒ}) using (formulaMorph)
        open import FOL.Bounded.PropertiesOfTheory (languageStep ℒ) using ([_witnessing_])

∞-witness : ∀ {i} → Formula (obj ℒ i) 1 → Constant (∞-language ℒ)
∞-witness {_} {i} φ = languageCanonicalMorph (suc i) .funMorph (witnessOf φ)

∞-Witnessing : (φ : Formula (∞-language ℒ) 1) → Type u
∞-Witnessing {ℒ} φ =
  ∃[ c ∈ Constant $ ∞-language ℒ ]
  Σ[ φ∞ ∈ Colimit (formulaChain ℒ 1 0) ]
  Σ[ φₚ@(i , φᵢ) ∈ Coproduct (formulaChain ℒ 1 0) ]
    [ φₚ ] ≡ₚ φ∞
  × formulaComparison φ∞ ≡ₚ φ
  × c ≡ languageCanonicalMorph (suc i) .funMorph (witnessOf φᵢ)

∞-witnessing : (φ : Formula (∞-language ℒ) 1) → ∞-Witnessing φ
∞-witnessing {ℒ} φ = let (φ∞ , Hφ∞) = formulaComparisonFiber φ in
  elim {P = λ _ → ∞-Witnessing φ}
    (λ _ → squash₁)
    (λ { (φₚ@(i , φᵢ) , Hi) →
      ∣ ∞-witness φᵢ , φ∞ , φₚ , Hi , Hφ∞ , refl ∣₁
    })
    (representative φ∞)
  where open DirectedDiagram (formulaChain ℒ 1 0) using (representative)

module _ {ℒ : Language} where
  import FOL.Base (∞-language ℒ) as Free
  open import FOL.Bounded.Base (∞-language ℒ) using (unbound; ∃'_; _⇒_; const)
  open import FOL.Bounded.Substitution (∞-language ℒ)

  unbound-witness : ∀ {i} → (φ : Formula (∞-language ℒ) 1) (φᵢ : Formula (obj ℒ i) 1) →
      unbound ((∃' φ) ⇒ φ [ const (∞-witness φᵢ) / 0 ])
    ≡ unbound (∃' φ) Free.⇒ unbound φ Free.[ Free.func (∞-witness φᵢ) / 0 ]
  unbound-witness φ φᵢ = cong (unbound (∃' φ) Free.⇒_) (unbound-subst _ _)
