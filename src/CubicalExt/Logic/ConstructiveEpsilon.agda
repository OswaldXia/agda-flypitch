{-# OPTIONS --cubical --safe #-}

module CubicalExt.Logic.ConstructiveEpsilon where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Nullary
open SetElim

module _ {ℓ} {A : ℕ → Type ℓ} (Aset : ∀ n → isSet (A n)) (Adec : ∀ n → Dec (A n)) where

  data <witness : ℕ → Type ℓ where
    witness : ∀ {n} → A n → <witness n
    step↓   : ∀ {n} → <witness (suc n) → <witness n

  initial : ∀ {n} → <witness n → <witness 0
  initial {zero} w₀ = w₀
  initial {suc n} wₛ = initial (step↓ wₛ)

  search : ∀ n → <witness n → Σ ℕ A
  search n wₙ with Adec n
  search n wₙ          | yes p = n , p
  search n (witness p) | no ¬p = ⊥.rec (¬p p)
  search n (step↓ wₛ)  | no ¬p = search (suc n) wₛ

  searchEq : ∀ {n} (w w' : <witness n) → search n w ≡ search n w'
  searchEq {n} w w' with Adec n | w | w'
  ... | yes p | _         | _         = refl
  ... | no ¬p | witness p | _         = ⊥.rec (¬p p)
  ... | no ¬p | _         | witness p = ⊥.rec (¬p p)
  ... | no ¬p | step↓ w   | step↓ w'  = searchEq w w'

  minWit : Σ ℕ A → Σ ℕ A
  minWit (n , p) = search 0 (initial (witness p))

  minWitEq : (p q : Σ ℕ A) → minWit p ≡ minWit q
  minWitEq (_ , pₙ) (_ , qₘ) = searchEq (initial (witness pₙ)) (initial (witness qₘ))

  ε : ∃ ℕ A → Σ ℕ A
  ε = rec→Set (isSetΣ isSetℕ Aset) minWit minWitEq
