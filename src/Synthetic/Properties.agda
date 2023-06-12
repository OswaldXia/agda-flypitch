{-# OPTIONS --cubical --safe #-}

module Synthetic.Properties where
open import Synthetic.Definitions

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Equality using (pathToEq)
open import Cubical.Data.Maybe as ⁇
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import CubicalExt.Functions.Logic.Iff

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)

private variable
  ℓ : Level
  A : Type ℓ

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
