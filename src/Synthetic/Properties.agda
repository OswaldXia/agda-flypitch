{-# OPTIONS --cubical --safe #-}

module Synthetic.Properties where
open import Synthetic.Definitions
open import Synthetic.PartialFunction

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Equality using (pathToEq) renaming (refl to reflEq)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe as ⁇
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ ℓ' : Level
  A A' : Type ℓ

decReduction : (B : A → Type ℓ) (B' : A' → Type ℓ') → B ⪯ B' → decidable B' → decidable B
decReduction B B' = map2 λ { (fᵣ , Hᵣ) (d , Hd) → d ∘ fᵣ , λ x →
  B x             ↔⟨ Hᵣ x ⟩
  B' (fᵣ x)       ↔⟨ Hd (fᵣ x) ⟩
  d (fᵣ x) ≡ true ↔∎ }

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

semiDec→sep : (B₁ : A → Type ℓ) (B₂ : A → Type ℓ') → (∀ x → B₁ x → B₂ x → ⊥) →
  semiDecidable B₁ → semiDecidable B₂ → separatable B₁ B₂
semiDec→sep B₁ B₂ disjoint = map2 λ { (f₁ , H₁) (f₂ , H₂) →
  let open Lemma f₁ f₂ H₁ H₂ in
    (λ x → record { f = f x ; proper = proper x })
  , (λ x → {!   !})
  , (λ x → {!   !}) }
  where
  module Lemma {B₁ : A → Type ℓ} {B₂ : A → Type ℓ'}
    (f₁ f₂ : A → ℕ → Bool) (H₁ : semiDecide f₁ B₁) (H₂ : semiDecide f₂ B₂)
    where
    f : A → ℕ → Maybe Bool
    f x n = if (f₁ x n) then just true else (if f₂ x n then just false else nothing)
    proper : {n m : ℕ} {a b : Bool} (x : A) → f x n ≡ just a → f x m ≡ just b → a ≡ b
    proper {n} {m} x p q with
         f₁ x n | f₂ x n | f₁ x m | f₂ x m
    ... | false | false  | _      | _     = ⊥.rec (¬nothing≡just p)
    ... | _     | _      | false  | false = ⊥.rec (¬nothing≡just q)
    ... | false | true   | true   | _     = {!   !}
    ... | true  | _      | false  | true  = {!   !}
    ... | false | true   | false  | true  = {!   !}
    ... | true  | _      | true   | _     = {!   !}
