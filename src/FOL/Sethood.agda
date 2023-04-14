{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Sethood ⦃ em : EM ⦄ (ℒ : Language {u}) where
open import FOL.Base ⦃ em ⦄ ℒ
open Language ℒ

open import Cubical.Foundations.Prelude using (isSet)
open import CubicalExt.Relation.Nullary using (¬_; yes; no; DiscreteEq; DiscreteEq→isSet)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

var-injective : ∀ {k₁ k₂ : ℕ} → var k₁ ≡ var k₂ → k₁ ≡ k₂
var-injective refl = refl

func-injective : ∀ {f₁ f₂ : 𝔉 l} → func f₁ ≡ func f₂ → f₁ ≡ f₂
func-injective refl = refl

app-injectiveˡ : {f₁ f₂ : Termₗ (suc l)} {t₁ t₂ : Term}
  → app f₁ t₁ ≡ app f₂ t₂ → f₁ ≡ f₂
app-injectiveˡ refl = refl

app-injectiveʳ : {f₁ f₂ : Termₗ (suc l)} {t₁ t₂ : Term}
  → app f₁ t₁ ≡ app f₂ t₂ → t₁ ≡ t₂
app-injectiveʳ refl = refl

discreteTerm : DiscreteEq (Termₗ l)
discreteTerm (var zero)     (var zero)      = yes refl
discreteTerm (var zero)     (var (suc k₂))  = no λ ()
discreteTerm (var (suc k₁)) (var zero)      = no λ ()
discreteTerm (func f)       (app t₁ t₂)     = no λ ()
discreteTerm (app t₁ t₂)    (var k)         = no λ ()
discreteTerm (app t₁ t₂)    (func f)        = no λ ()
discreteTerm (var k)        (func f)        = no λ ()
discreteTerm (var k)        (app t₁ t₂)     = no λ ()
discreteTerm (func f)       (var k)         = no λ ()

discreteTerm (var (suc k₁)) (var (suc k₂)) with discreteTerm (var k₁) (var k₂)
... | yes p rewrite var-injective p = yes refl
... | no ¬p = no λ q → ¬p $ cong var $ suc-injective $ var-injective q

discreteTerm (func f₁) (func f₂) with discrete𝔉 _ f₁ f₂
... | yes p = yes (cong func p)
... | no ¬p = no λ q → ¬p $ func-injective q

discreteTerm (app f₁ t₁) (app f₂ t₂) with discreteTerm f₁ f₂ | discreteTerm t₁ t₂
... | yes p | yes q = yes (cong₂ app p q)
... | no ¬p | _     = no λ r → ¬p $ app-injectiveˡ r
... | _     | no ¬q = no λ r → ¬q $ app-injectiveʳ r

isSetTerm : isSet Term
isSetTerm = DiscreteEq→isSet discreteTerm

discreteFormula : DiscreteEq (Formulaₗ l)
discreteFormula ⊥           ⊥           = yes refl
discreteFormula ⊥           (rel R)     = no λ ()
discreteFormula ⊥           (appᵣ r t)  = no λ ()
discreteFormula ⊥           (t₁ ≈ t₂)   = no λ ()
discreteFormula ⊥           (φ₁ ⇒ φ₂)   = no λ ()
discreteFormula ⊥           (∀' φ)      = no λ ()
discreteFormula (rel R)     ⊥           = no λ ()
discreteFormula (rel R)     (appᵣ r t)  = no λ ()
discreteFormula (rel R)     (t₁ ≈ t₂)   = no λ ()
discreteFormula (rel R)     (φ₁ ⇒ φ₂)   = no λ ()
discreteFormula (rel R)     (∀' φ)      = no λ ()
discreteFormula (appᵣ r t)  ⊥           = no λ ()
discreteFormula (appᵣ r t)  (rel R)     = no λ ()
discreteFormula (appᵣ r t)  (t₁ ≈ t₂)   = no λ ()
discreteFormula (appᵣ r t)  (φ₁ ⇒ φ₂)   = no λ ()
discreteFormula (appᵣ r t)  (∀' φ)      = no λ ()
discreteFormula (t₁ ≈ t₂)   ⊥           = no λ ()
discreteFormula (t₁ ≈ t₂)   (rel R)     = no λ ()
discreteFormula (t₁ ≈ t₂)   (appᵣ r t)  = no λ ()
discreteFormula (t₁ ≈ t₂)   (φ₁ ⇒ φ₂)   = no λ ()
discreteFormula (t₁ ≈ t₂)   (∀' φ)      = no λ ()
discreteFormula (φ₁ ⇒ φ₂)   ⊥           = no λ ()
discreteFormula (φ₁ ⇒ φ₂)   (rel R)     = no λ ()
discreteFormula (φ₁ ⇒ φ₂)   (appᵣ r t)  = no λ ()
discreteFormula (φ₁ ⇒ φ₂)   (t₁ ≈ t₂)   = no λ ()
discreteFormula (φ₁ ⇒ φ₂)   (∀' φ)      = no λ ()
discreteFormula (∀' φ)      ⊥           = no λ ()
discreteFormula (∀' φ)      (rel R)     = no λ ()
discreteFormula (∀' φ)      (appᵣ r t)  = no λ ()
discreteFormula (∀' φ)      (t₁ ≈ t₂)   = no λ ()
discreteFormula (∀' φ)      (φ₁ ⇒ φ₂)   = no λ ()

discreteFormula (rel R₁) (rel R₂) with discreteℜ _ R₁ R₂
... | yes p = yes (cong rel p)
... | no ¬p = no λ q → ¬p {!   !}

discreteFormula (appᵣ r t) (appᵣ φ₂ t₁) = {!   !}

discreteFormula (t₁ ≈ t₂) (t₃ ≈ t₄) = {!   !}

discreteFormula (φ₁ ⇒ φ₂) (φ₃ ⇒ φ₄) = {!   !}

discreteFormula (∀' φ₁) (∀' φ₂) = {!   !}
