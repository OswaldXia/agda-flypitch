{-# OPTIONS --cubical --safe #-}

module Synthetic.PartialFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as HL1
open import CubicalExt.Logic.ConstructiveEpsilon

private variable
  ℓ : Level
  A B : Type ℓ

record part (A : Type) : Type where
  field
    f : ℕ → Maybe A
    proper : ∀ {n m a b} → f n ≡ just a → f m ≡ just b → a ≡ b

  eval : A → Type
  eval a = ∃ _ λ k → f k ≡ just a

  functional : isSet A → ∀ {a b} → eval a → eval b → a ≡ b
  functional Aset = rec2 (Aset _ _)
    (λ { (_ , Hn) (_ , Hm) → proper Hn Hm })

  totalise : isSet A → ∃ _ eval → Σ _ eval
  totalise Aset aₚ = σ .snd .fst , ∣ σ .fst , σ .snd .snd ∣₁ where
    swapEval : ∃ _ eval → ∃ _ λ k → Σ _ λ x → f k ≡ just x
    swapEval = HL1.rec squash₁ λ (a , ea) → map (λ (n , H) → n , a , H) ea
    Σ[a] : ℕ → Type
    Σ[a] n = Σ _ λ a → f n ≡ just a
    isSetΣ[a] : ∀ n → isSet (Σ[a] n)
    isSetΣ[a] _ = isSetΣ Aset λ _ → isProp→isSet (isOfHLevelMaybe 0 (λ _ _ → Aset _ _) _ _)
    DecΣ[a] : ∀ n → Dec (Σ[a] n)
    DecΣ[a] n with f n
    ... | nothing = no λ (_ , H) → ⊥.rec (¬nothing≡just H)
    ... | just a = yes (a , refl)
    σ : Σ _ Σ[a]
    σ = ε isSetΣ[a] DecΣ[a] (swapEval aₚ)

_▻_ : part A → A → Type
aᵖ ▻ a = part.eval aᵖ a

total : (f : A → part B) → Type _
total f = ∀ x → ∃ _ (f x ▻_)

totalise : (f : A → part B) → total f → isSet B → A → B
totalise f H Bset x = part.totalise (f x) Bset (H x) .fst

partialise : (A → B) → A → part B
partialise f x = record { f = λ _ → just (f x) ; proper = λ p q → just-inj _ _ ((sym p) ∙ q) }
