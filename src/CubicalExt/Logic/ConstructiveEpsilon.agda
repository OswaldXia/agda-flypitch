{-# OPTIONS --cubical --safe #-}

module CubicalExt.Logic.ConstructiveEpsilon where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as ₁
open import Cubical.Relation.Nullary

module PropTarget {ℓ} {P : ℕ → Type ℓ} (Pprop : ∀ n → isProp (P n)) where

  Q : ℕ → Type ℓ
  Q n = P n × ∀ m → P m → n ≤ m

  Qprop : ∀ n → isProp (Q n)
  Qprop n = isProp× (Pprop n) (isPropΠ λ _ → isProp→ isProp≤)

  isSetΣQ : isSet (Σ ℕ Q)
  isSetΣQ = isSetΣ isSetℕ (λ n → isProp→isSet (Qprop n))

  ∃Q→ΣQ : ∃ ℕ Q → Σ ℕ Q
  ∃Q→ΣQ = rec→Set isSetΣQ (idfun _)
    λ { (n , Pn , Hn) (m , Pm , Hm) → ΣPathP (≤-antisym (Hn m Pm) (Hm n Pn) , isProp→PathP (λ _ → Qprop _) _ _) }

  ΣP→ΣQ : Σ ℕ P → Σ ℕ Q
  ΣP→ΣQ (n , Pn) = {!   !}

  ΣQ→ΣP : Σ ℕ Q → Σ ℕ P
  ΣQ→ΣP (n , Pn , _) = n , Pn

  ε : ∃ ℕ P → Σ ℕ P
  ε = ΣQ→ΣP ∘ ∃Q→ΣQ ∘ (map ΣP→ΣQ)

module SetTarget {ℓ} {A : ℕ → Type ℓ} (Aset : ∀ n → isSet (A n)) (Adec : ∀ n → Dec (A n)) where
  open SetElim

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

  search≡ : ∀ {n} (w w' : <witness n) → search n w ≡ search n w'
  search≡ {n} w w' with Adec n | w | w'
  ... | yes p | _         | _         = refl
  ... | no ¬p | witness p | _         = ⊥.rec (¬p p)
  ... | no ¬p | _         | witness p = ⊥.rec (¬p p)
  ... | no ¬p | step↓ w   | step↓ w'  = search≡ w w'

  minWit : Σ ℕ A → Σ ℕ A
  minWit (_ , p) = search 0 (initial (witness p))

  minWit≡ : (p q : Σ ℕ A) → minWit p ≡ minWit q
  minWit≡ (_ , pₙ) (_ , qₘ) = search≡ (initial (witness pₙ)) (initial (witness qₘ))

  ε : ∃ ℕ A → Σ ℕ A
  ε = rec→Set (isSetΣ isSetℕ Aset) minWit minWit≡
