{-# OPTIONS --cubical --safe #-}

module FOL.Language.Homomorphism.OnBounded.Properties {u} where
open import FOL.Language hiding (u)
open import FOL.Bounded.Base {u} hiding (l)
open import FOL.Bounded.Substitution using (subst)
open import FOL.Language.Homomorphism.Base {u} using (_⟶_; id; _∘_)
open import FOL.Language.Homomorphism.OnBounded.Base {u}
open Definitions

open import Cubical.Data.Equality using (funExt)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Function using ( _∘₂_) renaming (_∘_ to _⟨∘⟩_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)

private variable
  ℒ₁ ℒ₂ ℒ₃ ℒ₄ : Language
  F F₁ : ℒ₁ ⟶ ℒ₂
  F₂ : ℒ₂ ⟶ ℒ₃
  F₃ : ℒ₁ ⟶ ℒ₃
  m n l : ℕ

abstract
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

  termMorphFunctorial : F₃ ≡ F₂ ∘ F₁ → termMorph F₃ {n} {l} ≡ termMorph F₂ ⟨∘⟩ termMorph F₁
  termMorphFunctorial H = trans (cong (λ t → termMorph t) H) (termMorphComp _ _)

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

  formulaMorphFunctorial : F₃ ≡ F₂ ∘ F₁ → formulaMorph F₃ {n} {l} ≡ formulaMorph F₂ ⟨∘⟩ formulaMorph F₁
  formulaMorphFunctorial H = trans (cong (λ t → formulaMorph t) H) (formulaMorphComp _ _)
