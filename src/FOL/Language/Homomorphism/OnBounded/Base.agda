{-# OPTIONS --cubical --safe #-}

module FOL.Language.Homomorphism.OnBounded.Base {u} where
open import FOL.Language hiding (u)
open import FOL.Bounded.Base {u} hiding (l)
open import FOL.Bounded.Syntactics using (Theory)
open import FOL.Language.Homomorphism.Base {u} using (_⟶_)

open import CubicalExt.Foundations.Powerset* using (_⟦_⟧)
open import Data.Nat using (ℕ)

private variable
  ℒ₁ ℒ₂ : Language
  n l : ℕ

module Definitions (F : ℒ₁ ⟶ ℒ₂) where
  open _⟶_ {ℒ₁} {ℒ₂} F

  termMorph : Termₗ ℒ₁ n l → Termₗ ℒ₂ n l
  termMorph (var k)     = var k
  termMorph (func f)    = func (funMorph f)
  termMorph (app t₁ t₂) = app (termMorph t₁) (termMorph t₂)

  formulaMorph : Formulaₗ ℒ₁ n l → Formulaₗ ℒ₂ n l
  formulaMorph ⊥          = ⊥
  formulaMorph (rel R)    = rel (relMorph R)
  formulaMorph (appᵣ φ t) = appᵣ (formulaMorph φ) (termMorph t)
  formulaMorph (t₁ ≈ t₂)  = termMorph t₁ ≈ termMorph t₂
  formulaMorph (φ₁ ⇒ φ₂)  = formulaMorph φ₁ ⇒ formulaMorph φ₂
  formulaMorph (∀' φ)     = ∀' formulaMorph φ

  closedTermMorph : ClosedTerm ℒ₁ → ClosedTerm ℒ₂
  closedTermMorph = termMorph

  sentenceMorph : Sentence ℒ₁ → Sentence ℒ₂
  sentenceMorph = formulaMorph

  theoryMorph : Theory ℒ₁ → Theory ℒ₂
  theoryMorph Γ = sentenceMorph ⟦ Γ ⟧
