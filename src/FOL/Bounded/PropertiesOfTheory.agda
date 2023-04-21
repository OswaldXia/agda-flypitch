{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
module FOL.Bounded.PropertiesOfTheory (ℒ : Language {u}) where

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.Bounded.Substitution ℒ
open import FOL.Bounded.Semantics ℒ using (Model)
open import FOL.Structure.Base
open Language ℒ using (Constant)
open Structure using (nonempty)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΣ)
open import CubicalExt.Foundations.Powerset* using (_∈_)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
open import Cubical.Functions.Logic using () renaming (_⊔′_ to infixr 3 _∨_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; squash₁)
open import Cubical.Relation.Nullary using (¬_; isProp¬)
open import Function using (_$_)

-- 理论的一致性

Con : Theory → Type (ℓ-suc u)
Con T = ¬ T ⊢ ⊥

isPropCon : ∀ {T} → isProp (Con T)
isPropCon = isProp¬ _

¬Con : Theory → Type (ℓ-suc u)
¬Con T = T ⊦ ⊥

isProp¬Con : ∀ {T} → isProp (¬Con T)
isProp¬Con = squash₁

-- 理论的完全性

complete : Theory → Type (ℓ-suc u)
complete T = Con T × ∀ φ → φ ∈ T ∨ ¬ φ ∈ T

isPropComplete : ∀ {T} → isProp (complete T)
isPropComplete = isPropΣ isPropCon λ _ → isPropΠ λ _ → squash₁

-- 有足够常元的理论

[_witnessing_] : Constant → Formula 1 → Sentence
[_witnessing_] c φ = (∃' φ) ⇒ φ [ const c / 0 ]

hasEnoughConstants : Theory → Type (ℓ-suc u)
hasEnoughConstants T = ∀ (φ : Formula 1) → ∃[ c ∈ Constant ] T ⊢ [ c witnessing φ ]
