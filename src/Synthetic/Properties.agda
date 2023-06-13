{-# OPTIONS --cubical --safe #-}

module Synthetic.Properties where
open import Synthetic.Definitions

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Equality using (pathToEq) renaming (refl to reflEq)
open import Cubical.Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Cubical.Data.Maybe as ⁇
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ : Level
  A : Type ℓ

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

enum→semiDec : {B : A → Type ℓ} → discrete A → enumerable B → semiDecidable B
enum→semiDec {_} {A} = rec2 isPropSemiDecidable λ { (d , Hd) (fₑ , Hₑ) →
  let open Lemma d Hd fₑ Hₑ in
  ∣_∣₁ $ fₛ , λ a → ↔-trans (Hₑ a) $
    →: map (λ (n , H) → n , subst (λ x → ⁇.rec _ _ x ≡ _) (sym H) (≡→≟ a))
    ←: map (λ (n , H) → n , ≟→≡ a (fₑ n) H) }
  where
  module Lemma {B : A → Type ℓ}
    (d : A × A → Bool) (Hd : decide d (λ (a , b) → a ≡ b))
    (fₑ : ℕ → Maybe A) (Hₑ : enumerate fₑ B)
    where
    _≟_ : A → Maybe A → Bool
    _≟_ a = ⁇.rec false (λ b → d (a , b))
    ≡→≟ : ∀ a → a ≟ just a ≡ true
    ≡→≟ a = Hd _ .to refl
    ≟→≡ : ∀ a a? → a ≟ a? ≡ true → a? ≡ just a
    ≟→≡ a nothing H with pathToEq H
    ... | ()
    ≟→≡ a (just x) H = cong just $ sym $ Hd _ .from H
    fₛ : A → ℕ → Bool
    fₛ a n = a ≟ fₑ n
