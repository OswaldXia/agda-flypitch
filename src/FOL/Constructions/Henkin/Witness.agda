{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Constructions.Henkin.Witness ⦃ _ : ∀ {ℓ} → EM ℓ ⦄ u where
open import FOL.Constructions.Henkin.Base
open import FOL.Constructions.Henkin.LanguageChain u
  using (obj; languageStep; languageMorph; ∞-language; languageCanonicalMorph)
open import FOL.Constructions.Henkin.FormulaChain u
  using (formulaChain; formulaComparison; formulaComparisonFiber)
open import FOL.Bounded.Base using (Formula; Sentence)
open import FOL.Language hiding (u)
open Language {u}

open import FOL.Language.Homomorphism as LHom using (_⟶_)
open LHom._⟶_ using (funMorph)

open import Tools.DirectedDiagram using (DirectedDiagram; Cocone)
open DirectedDiagram using (Colimit; Coproduct)

open import Cubical.Foundations.Prelude
open import Cubical.Data.Equality using (eqToPath)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
open import Cubical.Functions.Logic using (inl; inr)
open import Cubical.HITs.SetQuotients using ([_])
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim)

open import StdlibExt.Data.Nat hiding (_/_)
open import Function using (_$_)

witnessOf : Formula ℒ 1 → Constant $ languageStep ℒ
witnessOf = witness

witnessStatement : Formula ℒ 1 → Sentence $ languageStep ℒ
witnessStatement {ℒ} φ = [ witnessOf φ witnessing formulaMorph φ ]
  where open LHom.OnBounded (languageMorph {ℒ}) using (formulaMorph)
        open import FOL.PropertiesOfTheory (languageStep ℒ) using ([_witnessing_])

∞-witness : ∀ {i} → Formula (obj ℒ i) 1 → Constant (∞-language ℒ)
∞-witness {_} {i} φ = languageCanonicalMorph (suc i) .funMorph (witnessOf φ)

∞-Witnessing : (φ : Formula (∞-language ℒ) 1) → Type u
∞-Witnessing {ℒ} φ =
  ∃[ c ∈ Constant $ ∞-language ℒ ]
  Σ[ φ∞ ∈ Colimit (formulaChain ℒ 1 0) ]
  Σ[ φₚ@(i , φᵢ) ∈ Coproduct (formulaChain ℒ 1 0) ]
    φ∞ ≡ [ φₚ ]
  × φ ≡ formulaComparison φ∞
  × c ≡ languageCanonicalMorph (suc i) .funMorph (witnessOf φᵢ)

∞-witnessing : (φ : Formula (∞-language ℒ) 1) → ∞-Witnessing φ
∞-witnessing {ℒ} φ = let (φ∞ , Hφ∞) = formulaComparisonFiber φ in
  elim {P = λ _ → ∞-Witnessing φ}
    (λ _ → squash₁)
    (λ { (φₚ@(i , φᵢ) , Hi) →
      ∣ ∞-witness φᵢ , φ∞ , φₚ , sym Hi , sym Hφ∞ , refl ∣₁
    })
    (representative φ∞)
  where open DirectedDiagram (formulaChain ℒ 1 0) using (representative)
