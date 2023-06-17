{-# OPTIONS --cubical --safe #-}

module Synthetic.Definitions.Base where
open import Synthetic.PartialFunction

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ ℓ' : Level
  A A' : Type ℓ

isPredicate : (A → Type ℓ) → Type _
isPredicate B = ∀ x → isProp (B x)

_decides_ : (A → Bool) → (A → Type ℓ) → Type _
fᵈ decides B = ∀ x → B x ↔ fᵈ x ≡ true

decidable : (A → Type ℓ) → Type _
decidable B = Σ _ (_decides B)

discrete : Type ℓ → Type _
discrete A = decidable {A = A × A} λ (x , y) → x ≡ y

_semiDecides_ : (A → ℕ → Bool) → (A → Type ℓ) → Type _
fᵈ⁻ semiDecides B = ∀ x → B x ↔ ∃ _ λ n → fᵈ⁻ x n ≡ true

semiDecidable : (A → Type ℓ) → Type _
semiDecidable B = Σ _ (_semiDecides B)

_partialDecides_ : (A → part Bool) → (A → Type ℓ) → Type _
fₚ partialDecides B = ∀ x → B x ↔ fₚ x ≐ true

_partialDecides⁰_ : (A → part Bool) → (A → Type ℓ) → Type _
fₚ partialDecides⁰ B = ∀ x → B x ↔ fₚ x ≐ false

partialDecidable : (A → Type ℓ) → Type _
partialDecidable B = Σ _ (_partialDecides B)

_separates_and_ : (A → part Bool) → (A → Type ℓ) → (A → Type ℓ') → Type _
fₚ separates B₁ and B₂ = fₚ partialDecides B₁ × fₚ partialDecides⁰ B₂

separatable : (A → Type ℓ) → (A → Type ℓ') → Type _
separatable B₁ B₂ = Σ _ (_separates B₁ and B₂)

_enumerates_ : (ℕ → Maybe A) → (A → Type ℓ) → Type _
fₑ enumerates B = ∀ x → B x ↔ ∃ _ λ n → fₑ n ≡ just x

enumerable : (A → Type ℓ) → Type _
enumerable B = Σ _ (_enumerates B)

_reducts_to_ : (fᵣ : A → A') (B : A → Type ℓ) → (B' : A' → Type ℓ') → Type _
fᵣ reducts B to B' = ∀ x → B x ↔ B' (fᵣ x)

_⪯_ : (A → Type ℓ) → (A' → Type ℓ') → Type _
B ⪯ B' = Σ _ (_reducts B to B')
