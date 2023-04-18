{-# OPTIONS --cubical --safe #-}

module FOL.Language.Homomorphism.OnBounded.Properties {u} where
open import FOL.Language hiding (u)
open import FOL.Bounded.Base {u} hiding (l)
open import FOL.Language.Homomorphism.Base {u} using (_⟶_; id; _∘_)
open import FOL.Language.Homomorphism.OnBounded.Base {u}
open Definitions

module _ {ℒ : Language {u}} where
  open import FOL.Bounded.Casting ℒ using (castₜ) public
  open import FOL.Bounded.Lifting ℒ using (_↑_) public
  open import FOL.Bounded.Substitution ℒ using (substₜ; subst) public

open import Cubical.Data.Equality using (funExt)
open import Data.Fin using (toℕ)
open import StdlibExt.Data.Nat
open import Function using ( _∘₂_) renaming (_∘_ to _⟨∘⟩_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)

private variable
  ℒ₁ ℒ₂ ℒ₃ : Language
  F  : ℒ ⟶ ℒ₁
  F₁ : ℒ₁ ⟶ ℒ₂
  F₂ : ℒ₂ ⟶ ℒ₃
  F₃ : ℒ₁ ⟶ ℒ₃
  m n l : ℕ

abstract
  -- currently not used
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

  termMorphComp : (G : ℒ₂ ⟶ ℒ₃) (F : ℒ₁ ⟶ ℒ₂) →
    termMorph (G ∘ F) {n} {l} ≡ termMorph G ⟨∘⟩ termMorph F
  termMorphComp = funExt ∘₂ termMorphCompApp

  formulaMorphComp : (G : ℒ₂ ⟶ ℒ₃) (F : ℒ₁ ⟶ ℒ₂) →
    formulaMorph (G ∘ F) {n} {l} ≡ formulaMorph G ⟨∘⟩ formulaMorph F
  formulaMorphComp = funExt ∘₂ formulaMorphCompApp

  termMorphFunctorial : F₃ ≡ F₂ ∘ F₁ → termMorph F₃ {n} {l} ≡ termMorph F₂ ⟨∘⟩ termMorph F₁
  termMorphFunctorial H = trans (cong (λ t → termMorph t) H) (termMorphComp _ _)

  formulaMorphFunctorial : F₃ ≡ F₂ ∘ F₁ → formulaMorph F₃ {n} {l} ≡ formulaMorph F₂ ⟨∘⟩ formulaMorph F₁
  formulaMorphFunctorial H = trans (cong (λ t → formulaMorph t) H) (formulaMorphComp _ _)

  -- currently not used
  termMorphCast : {m≤n : m ≤ n} (t : Termₗ ℒ m l) →
    termMorph F (castₜ m≤n t) ≡ castₜ m≤n (termMorph F t)
  termMorphCast (var k) = refl
  termMorphCast (func f) = refl
  termMorphCast (app t₁ t₂) = cong₂ app (termMorphCast t₁) (termMorphCast t₂)

  termMorphCastLift : (t : Termₗ ℒ m l) →
    termMorph F (castₜ (m+n≤n+m m n) (t ↑ n)) ≡ castₜ (m+n≤n+m m n) (termMorph F t ↑ n)
  termMorphCastLift (var k) = refl
  termMorphCastLift (func f) = refl
  termMorphCastLift (app t₁ t₂) = cong₂ app (termMorphCastLift t₁) (termMorphCastLift t₂)

  termMorphSubst : (t : Termₗ ℒ (suc n + m) l) (s : Term ℒ m) →
    termMorph F (t [ s / n ]ₜ) ≡ termMorph F t [ termMorph F s / n ]ₜ
  termMorphSubst {_} {n} (var k) s with <-cmp (toℕ k) n
  ... | tri< _ _ _ = refl
  ... | tri≈ _ _ _ = termMorphCastLift s
  ... | tri> _ _ _ = refl
  termMorphSubst (func f) s = refl
  termMorphSubst (app t₁ t₂) s = cong₂ app (termMorphSubst t₁ s) (termMorphSubst t₂ s)

  formulaMorphSubst : (φ : Formulaₗ ℒ (suc n + m) l) (s : Term ℒ m) →
    formulaMorph F (φ [ s / n ]) ≡ formulaMorph F φ [ termMorph F s / n ]
  formulaMorphSubst ⊥ _ = refl
  formulaMorphSubst (rel R) _ = refl
  formulaMorphSubst (appᵣ r t) s = cong₂ appᵣ (formulaMorphSubst r s) (termMorphSubst t s)
  formulaMorphSubst (t₁ ≈ t₂) s = cong₂ _≈_ (termMorphSubst t₁ s) (termMorphSubst t₂ s)
  formulaMorphSubst (φ₁ ⇒ φ₂) s = cong₂ _⇒_ (formulaMorphSubst φ₁ s) (formulaMorphSubst φ₂ s)
  formulaMorphSubst (∀' φ) s = cong ∀'_ (formulaMorphSubst φ s)
