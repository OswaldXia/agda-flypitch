{-# OPTIONS --cubical --safe #-}

module FOL.Language.Homomorphism.OnBounded.Properties {u} where
open import FOL.Language hiding (u)
open import FOL.Bounded.Base {u} hiding (l)
open import FOL.Language.Homomorphism.Base {u} using (_⟶_; id; _∘_)
open import FOL.Language.Homomorphism.OnBounded.Base {u}

module _ {ℒ : Language {u}} where
  open import FOL.Bounded.Manipulations.Injecting ℒ using (injectₜ) public
  open import FOL.Bounded.Manipulations.Lifting ℒ using (_↑_) public
  open import FOL.Bounded.Manipulations.Substitution.Closed ℒ using (substₜ; subst) public

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
  termMorphCompApp G F (app t₁ t₂) = cong₂ app (termMorphCompApp G F t₁) (termMorphCompApp G F t₂)

  formulaMorphCompApp : (G : ℒ₂ ⟶ ℒ₃) (F : ℒ₁ ⟶ ℒ₂) → (φ : Formulaₗ ℒ₁ n l) →
    formulaMorph (G ∘ F) φ ≡ (formulaMorph G ⟨∘⟩ formulaMorph F) φ
  formulaMorphCompApp G F ⊥ = refl
  formulaMorphCompApp G F (rel R) = refl
  formulaMorphCompApp G F (appᵣ φ t) = cong₂ appᵣ (formulaMorphCompApp G F φ) (termMorphCompApp G F t)
  formulaMorphCompApp G F (t₁ ≈ t₂) = cong₂ _≈_ (termMorphCompApp G F t₁) (termMorphCompApp G F t₂)
  formulaMorphCompApp G F (φ₁ ⇒ φ₂) = cong₂ _⇒_ (formulaMorphCompApp G F φ₁) (formulaMorphCompApp G F φ₂)
  formulaMorphCompApp G F (∀' φ) = cong ∀'_ (formulaMorphCompApp G F φ)

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
  termMorphInject : {m≤n : m ≤ n} (t : Termₗ ℒ m l) →
    termMorph F (injectₜ m≤n t) ≡ injectₜ m≤n (termMorph F t)
  termMorphInject (var k) = refl
  termMorphInject (func f) = refl
  termMorphInject (app t₁ t₂) = cong₂ app (termMorphInject t₁) (termMorphInject t₂)

  -- currently not used
  termMorphInjectLift : (t : Termₗ ℒ m l) →
    termMorph F (injectₜ (m+n≤n+m m n) (t ↑ n)) ≡ injectₜ (m+n≤n+m m n) (termMorph F t ↑ n)
  termMorphInjectLift (var k) = refl
  termMorphInjectLift (func f) = refl
  termMorphInjectLift (app t₁ t₂) = cong₂ app (termMorphInjectLift t₁) (termMorphInjectLift t₂)

  ternMorphLift : (s : Termₗ ℒ m l) → termMorph F (s ↑ n) ≡ termMorph F s ↑ n
  ternMorphLift (var k) = refl
  ternMorphLift (func f) = refl
  ternMorphLift (app t₁ t₂) = cong₂ app (ternMorphLift t₁) (ternMorphLift t₂)

  termMorphSubst : (t : Termₗ ℒ (suc n) l) (s : ClosedTerm ℒ) →
    termMorph F (t [≔ s ]ₜ) ≡ termMorph F t [≔ termMorph F s ]ₜ
  termMorphSubst {_} {n} (var k) s with <-cmp (toℕ k) n
  ... | tri< _ _ _ = refl
  ... | tri≈ _ _ _ = ternMorphLift s
  ... | tri> _ _ _ = refl
  termMorphSubst (func f) s = refl
  termMorphSubst (app t₁ t₂) s = cong₂ app (termMorphSubst t₁ s) (termMorphSubst t₂ s)

  formulaMorphSubst : (φ : Formulaₗ ℒ (suc n) l) (s : ClosedTerm ℒ) →
    formulaMorph F (φ [≔ s ]) ≡ formulaMorph F φ [≔ termMorph F s ]
  formulaMorphSubst ⊥ _ = refl
  formulaMorphSubst (rel R) _ = refl
  formulaMorphSubst (appᵣ r t) s = cong₂ appᵣ (formulaMorphSubst r s) (termMorphSubst t s)
  formulaMorphSubst (t₁ ≈ t₂) s = cong₂ _≈_ (termMorphSubst t₁ s) (termMorphSubst t₂ s)
  formulaMorphSubst (φ₁ ⇒ φ₂) s = cong₂ _⇒_ (formulaMorphSubst φ₁ s) (formulaMorphSubst φ₂ s)
  formulaMorphSubst (∀' φ) s = cong ∀'_ (formulaMorphSubst φ s)
