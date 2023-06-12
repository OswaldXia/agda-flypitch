{-# OPTIONS --cubical --safe #-}

module Synthetic.Definitions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Equality using (pathToEq) renaming (refl to reflEq)
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import CubicalExt.Functions.Logic.Iff
open import CubicalExt.StdlibBridge.Bool

open import Data.Nat
open import Data.Bool
import Cubical.Data.Bool as Cubical

private variable
  ℓ : Level
  A P : Type ℓ
  B : A → Type ℓ
  b : Bool
  f : A → Bool
  fₛ : A → ℕ → Bool
  fₑ : ℕ → Maybe A

reflects : Bool → Type ℓ → Type _
reflects b P = P ↔ b ≡ true

decide : (A → Bool) → (A → Type ℓ) → Type _
decide f B = ∀ a → reflects (f a) (B a)

decidable : (A → Type ℓ) → Type _
decidable P = ∃[ f ∈ _ ] decide f P

semiDecide : (A → ℕ → Bool) → (A → Type ℓ) → Type _
semiDecide fₛ B = ∀ a → B a ↔ (∃[ n ∈ ℕ ] fₛ a n ≡ true)

semiDecidable : (A → Type ℓ) → Type _
semiDecidable P = ∃[ fₛ ∈ _ ] semiDecide fₛ P

enumerate : (ℕ → Maybe A) → (A → Type ℓ) → Type _
enumerate fₑ B = ∀ a → B a ↔ (∃[ n ∈ ℕ ] fₑ n ≡ just a)

enumerable : (A → Type ℓ) → Type _
enumerable P = ∃[ fₑ ∈ _ ] enumerate fₑ P

isSetBool : isSet Bool
isSetBool = subst isSet boolBridge Cubical.isSetBool

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

discrete : Type ℓ → Type _
discrete A = decidable {A = A × A} λ (a , b) → a ≡ b

isPropDiscrete : isProp (discrete A)
isPropDiscrete = isPropDecidable

discreteℕ : discrete ℕ
discreteℕ = ∣_∣₁ $ (λ (n , m) → n ≡ᵇ m)
                 , (λ (n , m) → →: ≡→≡ᵇ ←: ≡ᵇ→≡)
  where
  ≡→≡ᵇ : {n m : ℕ} → n ≡ m → (n ≡ᵇ m) ≡ true
  ≡→≡ᵇ {n} path with pathToEq path
  ... | reflEq = ≡ᵇ-refl n where
    ≡ᵇ-refl : (n : ℕ) → (n ≡ᵇ n) ≡ true
    ≡ᵇ-refl zero = refl
    ≡ᵇ-refl (suc n) = ≡ᵇ-refl n

  ≡ᵇ→≡ : {n m : ℕ} → (n ≡ᵇ m) ≡ true → n ≡ m
  ≡ᵇ→≡ {zero} {zero} _ = refl
  ≡ᵇ→≡ {zero} {suc m} H with pathToEq H
  ... | ()
  ≡ᵇ→≡ {suc n} {zero} H with pathToEq H
  ... | ()
  ≡ᵇ→≡ {suc n} {suc m} H = cong suc (≡ᵇ→≡ H)
 