{-# OPTIONS --cubical --safe #-}

module Synthetic.Definitions where
open import Synthetic.PartialFunction

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ ℓ' : Level
  A A' : Type ℓ
  B B' B₁ B₂ : A → Type ℓ
  b : Bool
  f : A → Bool
  fₛ : A → ℕ → Bool
  fₑ : ℕ → Maybe A
  fₚ : A → part Bool
  fᵣ : A → A'

_decides_ : (A → Bool) → (A → Type ℓ) → Type _
f decides B = ∀ a → B a ↔ f a ≡ true

decidable : (A → Type ℓ) → Type _
decidable B = ∃ _ λ f → f decides B

_semiDecides_ : (A → ℕ → Bool) → (A → Type ℓ) → Type _
fₛ semiDecides B = ∀ a → B a ↔ ∃ _ λ n → fₛ a n ≡ true

semiDecidable : (A → Type ℓ) → Type _
semiDecidable B = ∃ _ λ fₛ → fₛ semiDecides B

_enumerates_ : (ℕ → Maybe A) → (A → Type ℓ) → Type _
fₑ enumerates B = ∀ a → B a ↔ ∃ _ λ n → fₑ n ≡ just a

enumerable : (A → Type ℓ) → Type _
enumerable B = ∃ _ λ fₑ → fₑ enumerates B

_separates_and_ : (A → part Bool) → (A → Type ℓ) → (A → Type ℓ') → Type _
fₚ separates B₁ and B₂ = (∀ x → B₁ x ↔ fₚ x ▻ true) × (∀ x → B₂ x ↔ fₚ x ▻ false)

separatable : (A → Type ℓ) → (A → Type ℓ') → Type _
separatable B₁ B₂ = ∃ _ λ f → f separates B₁ and B₂

discrete : Type ℓ → Type _
discrete A = decidable {A = A × A} λ (a , b) → a ≡ b

_reducts_to_ : (fᵣ : A → A') (B : A → Type ℓ) → (B' : A' → Type ℓ') → Type _
fᵣ reducts B to B' = ∀ x → B x ↔ B' (fᵣ x)

_⪯_ : (A → Type ℓ) → (A' → Type ℓ') → Type _
B ⪯ B' = ∃ _ λ fᵣ → fᵣ reducts B to B'

isPredicate : (A → Type ℓ) → Type _
isPredicate B = ∀ x → isProp (B x)

isPropDecides : isPredicate B → isProp (f decides B)
isPropDecides pred = isPropΠ λ _ → isPropIff (pred _) (isSetBool _ _)

isPropDecidable : isProp (decidable B)
isPropDecidable = squash₁

isPropSemiDecides : isPredicate B → isProp (fₛ semiDecides B)
isPropSemiDecides pred = isPropΠ (λ _ → isPropIff (pred _) squash₁)

isPropSemiDecidable : isProp (semiDecidable B)
isPropSemiDecidable = squash₁

isPropEnumerates : isPredicate B → isProp (fₑ enumerates B)
isPropEnumerates pred = isPropΠ (λ _ → isPropIff (pred _) squash₁)

isPropEnumeratable : isProp (enumerable B)
isPropEnumeratable = squash₁

isPropSeparates : isPredicate B₁ → isPredicate B₂ → isProp (fₚ separates B₁ and B₂)
isPropSeparates pred₁ pred₂ = isProp×
  (isPropΠ (λ x → isPropIff (pred₁ x) squash₁))
  (isPropΠ (λ x → isPropIff (pred₂ x) squash₁))

isPropSeparatable : isProp (separatable B₁ B₂)
isPropSeparatable = squash₁

isPropDiscrete : isProp (discrete A)
isPropDiscrete = isPropDecidable

isProp⪯ : isProp (B ⪯ B')
isProp⪯ = squash₁
