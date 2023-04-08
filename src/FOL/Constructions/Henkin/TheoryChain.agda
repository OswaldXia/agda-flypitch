{-# OPTIONS --cubical --safe #-}

module FOL.Constructions.Henkin.TheoryChain u where
open import FOL.Constructions.Henkin.Base
open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Constructions.Henkin.FormulaChain u
  using (formulaChain; formulaComparison; formulaComparisonFiber)
open import FOL.Bounded.Base using (Formula; Sentence; Theory)
open import FOL.Language hiding (u)
open Language {u}

import FOL.Language.Homomorphism as LHom
open LHom using (_⟶_)
open LHom._⟶_ using (funMorph)

open import Tools.DirectedDiagram using (DirectedDiagram)
open DirectedDiagram using (Colimit; Coproduct)
open import FOL.Language.DirectedDiagram using (DirectedDiagramLanguage)

open import Cubical.Core.Primitives renaming (_≡_ to _≡ₚ_)
open import Cubical.Data.Sigma using () renaming (_×_ to infixr 3 _×_)
open import Cubical.Data.Equality using (reflPath; symPath; compPath)
open import Cubical.HITs.SetQuotients using ([_]; eq/; squash/)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim; elim→Set)
open import Cubical.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; rec)

open import StdlibExt.Data.Nat hiding (_/_)
open import Function using (_∘_; _$_)
open import StdlibExt.Relation.Unary using (_∪_; _⟦_⟧; ⋃_; replacement-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

witnessOf : ∥ Formula ℒ 1 ∥₂ → Constant $ languageStep ℒ
witnessOf = witness

[_witnessing_] : Constant ℒ → Formula ℒ 1 → Sentence ℒ
[_witnessing_] {ℒ} c φ = (∃' φ) ⇒ φ [ const c / 0 ] where
  open import FOL.Bounded.Base ℒ using (∃'_; _⇒_; const)
  open import FOL.Bounded.Substitution ℒ

theoryStep : Theory ℒ → Theory $ languageStep ℒ
theoryStep {ℒ} Γ = theoryMorph Γ ∪ ｛ [ witnessOf ∣ φ ∣₂ witnessing formulaMorph φ ] ∣ φ ∈ Formula ℒ 1 ｝
  where open LHom.Bounded languageMorph

[_]-theory : ∀ n → Theory ℒ → Theory $ [ n ]-language ℒ
[ zero ]-theory T = T
[ suc n ]-theory T = theoryStep $ [ n ]-theory T

[_]-∞-theory : ∀ n → Theory ℒ → Theory $ ∞-language ℒ
[ n ]-∞-theory T = sentenceMorph ⟦ [ n ]-theory T ⟧
  where open LHom.Bounded (languageCanonicalMorph n)

∞-theory : Theory ℒ → Theory $ ∞-language ℒ
∞-theory T = ⋃ (λ n → [ n ]-∞-theory T)

funMorph-$-morph-witnessOf-comm : ∀ {ℒ i j} .{i~j : i ≤₃ j}
    (φ : ∥ Formula ([ i ]-language ℒ) 1 ∥₂) → funMorph (morph i~j) {!   !} ≡ₚ {!  witnessOf (funMorph (morph i~j) φ) !} --witnessOf (funMorph (morph i~j) φ)
funMorph-$-morph-witnessOf-comm = {!   !} --elim₂ (λ _ → isSet→isGroupoid squash₂ _ _) (λ _ → reflPath)

∞-witness : {T : Theory ℒ} (φ : Formula (∞-language ℒ) 1) → Constant $ ∞-language ℒ
∞-witness {ℒ} {T} φ = let (φ∞ , _) = formulaComparisonFiber φ in
  elim→Set (λ _ → squash/)
    (λ ((i , φᵢ) , _) → languageCanonicalMorph (suc i) .funMorph (witnessOf φᵢ))
    (λ ((i , φᵢ) , Hi) ((j , φⱼ) , Hj) → eq/ _ _ $
      elim {P = λ _ → (suc i , witnessOf φᵢ) ≃ (suc j , witnessOf φⱼ)}
        (λ _ → squash₁)
        (λ (k , φₖ , i~k , j~k , H₁ , H₂) →
          ∣ suc k , witnessOf φₖ
          , (≤⇒≤₃ $ s≤s $ ≤₃⇒≤ i~k)
          , (≤⇒≤₃ $ s≤s $ ≤₃⇒≤ j~k)
          , {! φₖ !}
          , {!   !}
          ∣₁)
        (effective $ compPath Hi $ symPath Hj))
    (representative φ∞)
  where open DirectedDiagram (formulaChain ℒ 1 0) using (representative; effective)
        open DirectedDiagramLanguage (languageChain ℒ) using (functionsᴰ)
        open DirectedDiagram (functionsᴰ 0) using (_≃_)
