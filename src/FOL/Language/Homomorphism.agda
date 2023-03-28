{-# OPTIONS --cubical --safe #-}

module FOL.Language.Homomorphism {u} where
open import FOL.Language hiding (u)

open import Cubical.Core.Everything using (Type)
open import Data.Nat using (ℕ)
open import Function using () renaming (id to ⟨id⟩; _∘_ to _⟨∘⟩_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import StdlibExt.Relation.Unary using (_⟦_⟧)

private variable
  ℒ₁ ℒ₂ ℒ₃ ℒ₄ : Language

record _⟶_ (ℒ₁ : Language) (ℒ₂ : Language) : Type u where
  open Language {u}
  field
    funMorph : ∀ {n} → ℒ₁ .functions n → ℒ₂ .functions n
    relMorph : ∀ {n} → ℒ₁ .relations n → ℒ₂ .relations n

id : ℒ ⟶ ℒ
id = record { funMorph = ⟨id⟩ ; relMorph = ⟨id⟩ }

_∘_ : ℒ₂ ⟶ ℒ₃ → ℒ₁ ⟶ ℒ₂ → ℒ₁ ⟶ ℒ₃
F ∘ G = record
  { funMorph = F .funMorph ⟨∘⟩ G .funMorph
  ; relMorph = F .relMorph  ⟨∘⟩ G .relMorph } where open _⟶_

module Bounded (F : ℒ₁ ⟶ ℒ₂) where
  open import FOL.Bounded.Base {u} hiding (l)
  open _⟶_ {ℒ₁} {ℒ₂} F

  private variable
    n l : ℕ

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
