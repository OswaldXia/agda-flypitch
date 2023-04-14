{-# OPTIONS --cubical --safe #-}

open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Language.Homomorphism ⦃ em : EM ⦄ {u} where
open import FOL.Language ⦃ em ⦄ hiding (u)

open import Cubical.Core.Primitives using (Type)
open import Cubical.Data.Equality using (funExt)
open import CubicalExt.HITs.SetTruncation using (map)
open import CubicalExt.Foundations.Powerset* using (_⟦_⟧)

open import Data.Nat using (ℕ)
open import Function using (_$_; _∘₂_) renaming (id to ⟨id⟩; _∘_ to _⟨∘⟩_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

private variable
  ℒ₁ ℒ₂ ℒ₃ ℒ₄ : Language
  n l : ℕ

record _⟶_ (ℒ₁ : Language) (ℒ₂ : Language) : Type u where
  constructor ⟪_,_⟫
  open Language {u}
  field
    funMorph : ∀ {n} → ℒ₁ .𝔉 n → ℒ₂ .𝔉 n
    relMorph : ∀ {n} → ℒ₁ .ℜ n → ℒ₂ .ℜ n

id : ℒ ⟶ ℒ
id = ⟪ ⟨id⟩ , ⟨id⟩ ⟫

_∘_ : ℒ₂ ⟶ ℒ₃ → ℒ₁ ⟶ ℒ₂ → ℒ₁ ⟶ ℒ₃
F ∘ G = ⟪ F .funMorph ⟨∘⟩ G .funMorph , F .relMorph ⟨∘⟩ G .relMorph ⟫ where open _⟶_

module _ where
  open _⟶_

  homExt : {F G : ℒ₁ ⟶ ℒ₂} → (λ {n} → funMorph F {n}) ≡ funMorph G → (λ {n} → relMorph F {n}) ≡ relMorph G → F ≡ G
  homExt funMorphEq relMorphEq = cong₂ ⟪_,_⟫ funMorphEq relMorphEq

  funMorph-∘ : (G : ℒ₂ ⟶ ℒ₃) (F : ℒ₁ ⟶ ℒ₂) (n : ℕ) → funMorph (G ∘ F) {n} ≡ funMorph G ⟨∘⟩ funMorph F
  funMorph-∘ G F n = refl

  relMorph-∘ : (G : ℒ₂ ⟶ ℒ₃) (F : ℒ₁ ⟶ ℒ₂) (n : ℕ) → relMorph (G ∘ F) {n} ≡ relMorph G ⟨∘⟩ relMorph F
  relMorph-∘ G F n = refl

module Bounded (F : ℒ₁ ⟶ ℒ₂) where
  open import FOL.Bounded.Base {u} hiding (l)
  open import FOL.Syntactics ⦃ em ⦄ using (Theory)
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

module BoundedProperties where
  open import FOL.Bounded.Base {u} hiding (l)
  open Bounded

  termMorphId : (t : Termₗ ℒ₁ n l) → termMorph id t ≡ t
  termMorphId (var k) = refl
  termMorphId (func f) = refl
  termMorphId (app t₁ t₂) = cong₂ app (termMorphId t₁) (termMorphId t₂)

  termMorphCompApp : (G : ℒ₂ ⟶ ℒ₃) (F : ℒ₁ ⟶ ℒ₂) → (t : Termₗ ℒ₁ n l) →
    termMorph (G ∘ F) t ≡ termMorph G (termMorph F t)
  termMorphCompApp G F (var k) = refl
  termMorphCompApp G F (func f) = refl
  termMorphCompApp G F (app t₁ t₂)
    rewrite termMorphCompApp G F t₁
          | termMorphCompApp G F t₂ = refl

  termMorphComp : (G : ℒ₂ ⟶ ℒ₃) (F : ℒ₁ ⟶ ℒ₂) →
    termMorph (G ∘ F) {n} {l} ≡ termMorph G ⟨∘⟩ termMorph F
  termMorphComp = funExt ∘₂ termMorphCompApp

  formulaMorphCompApp : (G : ℒ₂ ⟶ ℒ₃) (F : ℒ₁ ⟶ ℒ₂) → (φ : Formulaₗ ℒ₁ n l) →
    formulaMorph (G ∘ F) φ ≡ (formulaMorph G ⟨∘⟩ formulaMorph F) φ
  formulaMorphCompApp G F ⊥ = refl
  formulaMorphCompApp G F (rel R) = refl
  formulaMorphCompApp G F (appᵣ φ t)
    rewrite formulaMorphCompApp G F φ
          | termMorphCompApp G F t = refl
  formulaMorphCompApp G F (t₁ ≈ t₂)
    rewrite termMorphCompApp G F t₁
          | termMorphCompApp G F t₂ = refl
  formulaMorphCompApp G F (φ₁ ⇒ φ₂)
    rewrite formulaMorphCompApp G F φ₁
          | formulaMorphCompApp G F φ₂ = refl
  formulaMorphCompApp G F (∀' φ)
    rewrite formulaMorphCompApp G F φ = refl

  formulaMorphComp : (G : ℒ₂ ⟶ ℒ₃) (F : ℒ₁ ⟶ ℒ₂) →
    formulaMorph (G ∘ F) {n} {l} ≡ formulaMorph G ⟨∘⟩ formulaMorph F
  formulaMorphComp = funExt ∘₂ formulaMorphCompApp
