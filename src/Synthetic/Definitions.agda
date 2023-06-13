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
  A A' P : Type ℓ
  B B' B₁ B₂ : A → Type ℓ
  b : Bool
  f : A → Bool
  fₛ : A → ℕ → Bool
  fₑ : ℕ → Maybe A
  fₚ : A → part Bool
  fᵣ : A → A'

reflects : Bool → Type ℓ → Type _
reflects b P = P ↔ b ≡ true

decide : (A → Bool) → (A → Type ℓ) → Type _
decide f B = ∀ a → reflects (f a) (B a)

decidable : (A → Type ℓ) → Type _
decidable P = ∃ _ λ f → decide f P

semiDecide : (A → ℕ → Bool) → (A → Type ℓ) → Type _
semiDecide fₛ B = ∀ a → B a ↔ ∃ _ λ n → fₛ a n ≡ true

semiDecidable : (A → Type ℓ) → Type _
semiDecidable P = ∃ _ λ fₛ → semiDecide fₛ P

enumerate : (ℕ → Maybe A) → (A → Type ℓ) → Type _
enumerate fₑ B = ∀ a → B a ↔ ∃ _ λ n → fₑ n ≡ just a

enumerable : (A → Type ℓ) → Type _
enumerable P = ∃ _ λ fₑ → enumerate fₑ P

separate : (A → part Bool) → (A → Type ℓ) → (A → Type ℓ') → Type _
separate fₚ B₁ B₂ = (∀ x → B₁ x ↔ fₚ x ▻ true) × (∀ x → B₂ x ↔ fₚ x ▻ false)

separatable : (A → Type ℓ) → (A → Type ℓ') → Type _
separatable B₁ B₂ = ∃ _ λ f → separate f B₁ B₂

discrete : Type ℓ → Type _
discrete A = decidable {A = A × A} λ (a , b) → a ≡ b

reduct : (fᵣ : A → A') (B : A → Type ℓ) → (B' : A' → Type ℓ') → Type _
reduct fᵣ B B' = ∀ x → B x ↔ B' (fᵣ x)

_⪯_ : (A → Type ℓ) → (A' → Type ℓ') → Type _
B ⪯ B' = ∃ _ λ fᵣ → reduct fᵣ B B'

isPredicate : (A → Type ℓ) → Type _
isPredicate B = ∀ x → isProp (B x)

isPropReflects : isProp P → isProp (reflects b P)
isPropReflects Pprop = isPropIff Pprop (isSetBool _ _)

isPropDecide : isPredicate B → isProp (decide f B)
isPropDecide pred = isPropΠ λ _ → isPropReflects (pred _)

isPropDecidable : isProp (decidable B)
isPropDecidable = squash₁

isPropSemiDecide : isPredicate B → isProp (semiDecide fₛ B)
isPropSemiDecide pred = isPropΠ (λ _ → isPropIff (pred _) squash₁)

isPropSemiDecidable : isProp (semiDecidable B)
isPropSemiDecidable = squash₁

isPropEnumerate : isPredicate B → isProp (enumerate fₑ B)
isPropEnumerate pred = isPropΠ (λ _ → isPropIff (pred _) squash₁)

isPropEnumeratable : isProp (enumerable B)
isPropEnumeratable = squash₁

isPropSeparate : isPredicate B₁ → isPredicate B₂ → isProp (separate fₚ B₁ B₂)
isPropSeparate pred₁ pred₂ = isProp×
  (isPropΠ (λ x → isPropIff (pred₁ x) squash₁))
  (isPropΠ (λ x → isPropIff (pred₂ x) squash₁))

isPropSeparatable : isProp (separatable B₁ B₂)
isPropSeparatable = squash₁

isPropDiscrete : isProp (discrete A)
isPropDiscrete = isPropDecidable

isProp⪯ : isProp (B ⪯ B')
isProp⪯ = squash₁
