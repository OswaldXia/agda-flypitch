{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Sethood ⦃ em : EM ⦄ (ℒ : Language {u}) where
open import FOL.Base ⦃ em ⦄ ℒ
open Language ℒ

open import Cubical.Foundations.Prelude using (isSet)
open import CubicalExt.Relation.Nullary using (¬_; yes; no; DiscreteEq; DiscreteEq→isSet)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

var-injective : {k₁ k₂ : ℕ} → var k₁ ≡ var k₂ → k₁ ≡ k₂
var-injective refl = refl

func-injective : {f₁ f₂ : 𝔉 l} → func f₁ ≡ func f₂ → f₁ ≡ f₂
func-injective refl = refl

app-injectiveˡ : {f₁ f₂ : Termₗ (suc l)} {t₁ t₂ : Term}
  → app f₁ t₁ ≡ app f₂ t₂ → f₁ ≡ f₂
app-injectiveˡ refl = refl

app-injectiveʳ : {f₁ f₂ : Termₗ (suc l)} {t₁ t₂ : Term}
  → app f₁ t₁ ≡ app f₂ t₂ → t₁ ≡ t₂
app-injectiveʳ refl = refl

rel-injective : {R₁ R₂ : ℜ l} → rel R₁ ≡ rel R₂ → R₁ ≡ R₂
rel-injective refl = refl

appᵣ-injectiveˡ : {r₁ r₂ : Formulaₗ (suc l)} {t₁ t₂ : Term}
  → appᵣ r₁ t₁ ≡ appᵣ r₂ t₂ → r₁ ≡ r₂
appᵣ-injectiveˡ refl = refl

appᵣ-injectiveʳ : {r₁ r₂ : Formulaₗ (suc l)} {t₁ t₂ : Term}
  → appᵣ r₁ t₁ ≡ appᵣ r₂ t₂ → t₁ ≡ t₂
appᵣ-injectiveʳ refl = refl

≈-injectiveˡ : {t₁ t₂ s₁ s₂ : Term} → t₁ ≈ s₁ ≡ t₂ ≈ s₂ → t₁ ≡ t₂
≈-injectiveˡ refl = refl

≈-injectiveʳ : {t₁ t₂ s₁ s₂ : Term} → t₁ ≈ s₁ ≡ t₂ ≈ s₂ → s₁ ≡ s₂
≈-injectiveʳ refl = refl

⇒-injectiveˡ : {φ₁ φ₂ ψ₁ ψ₂ : Formulaₗ 0} → φ₁ ⇒ ψ₁ ≡ φ₂ ⇒ ψ₂ → φ₁ ≡ φ₂
⇒-injectiveˡ refl = refl

⇒-injectiveʳ : {φ₁ φ₂ ψ₁ ψ₂ : Formulaₗ 0} → φ₁ ⇒ ψ₁ ≡ φ₂ ⇒ ψ₂ → ψ₁ ≡ ψ₂
⇒-injectiveʳ refl = refl

∀'-injective : {φ₁ φ₂ : Formulaₗ 0} → ∀' φ₁ ≡ ∀' φ₂ → φ₁ ≡ φ₂
∀'-injective refl = refl

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
... | yes refl = yes refl
... | no  ¬p   = no λ { refl → ¬p refl }

discreteTerm (func f₁) (func f₂) with discrete𝔉 _ f₁ f₂
... | yes refl = yes refl
... | no  ¬p   = no λ { refl → ¬p refl }

discreteTerm (app f₁ t₁) (app f₂ t₂) with discreteTerm f₁ f₂ | discreteTerm t₁ t₂
... | yes refl | yes refl = yes refl
... | no  ¬p   | _        = no λ r → ¬p $ app-injectiveˡ r
... | _        | no  ¬q   = no λ r → ¬q $ app-injectiveʳ r

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
... | no ¬p = no λ q → ¬p $ rel-injective q

discreteFormula (appᵣ r₁ t₁) (appᵣ r₂ t₂) with discreteFormula r₁ r₂ | discreteTerm t₁ t₂
... | yes p | yes q = yes (cong₂ appᵣ p q)
... | no ¬p | _     = no λ r → ¬p $ appᵣ-injectiveˡ r
... | _     | no ¬q = no λ r → ¬q $ appᵣ-injectiveʳ r

discreteFormula (t₁ ≈ s₁) (t₂ ≈ s₂) with discreteTerm t₁ t₂ | discreteTerm s₁ s₂
... | yes p | yes q = yes {!   !}
... | no ¬p | _     = no λ r → ¬p $ ≈-injectiveˡ r
... | _     | no ¬q = no λ r → ¬q $ ≈-injectiveʳ r

discreteFormula (φ₁ ⇒ ψ₁) (φ₂ ⇒ ψ₂) = {!   !}

discreteFormula (∀' φ₁) (∀' φ₂) = {!   !}
