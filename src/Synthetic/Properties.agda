{-# OPTIONS --cubical --safe #-}

module Synthetic.Properties where
open import Synthetic.Definitions
open import Synthetic.PartialFunction

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Bool using (true≢false; false≢true)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe as ⁇
open import Cubical.Data.Sigma
open import Cubical.Data.Equality using (pathToEq; eqToPath) renaming (refl to reflEq)
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

private variable
  ℓ ℓ' : Level
  A A' : Type ℓ
  B B' : A → Type ℓ

decReduction : B ⪯ B' → decidable B' → decidable B
decReduction {B = B} {B' = B'} = map2 λ { (fᵣ , Hᵣ) (d , Hd) → d ∘ fᵣ , λ x →
  B x             ↔⟨ Hᵣ x ⟩
  B' (fᵣ x)       ↔⟨ Hd (fᵣ x) ⟩
  d (fᵣ x) ≡ true ↔∎ }

semiDecReduction : B ⪯ B' → semiDecidable B' → semiDecidable B
semiDecReduction {B = B} {B' = B'} = map2 λ { (fᵣ , Hᵣ) (d , Hd) → d ∘ fᵣ , λ x →
  B x             ↔⟨ Hᵣ x ⟩
  B' (fᵣ x)       ↔⟨ Hd (fᵣ x) ⟩
  ∃ ℕ (λ n → d (fᵣ x) n ≡ true) ↔∎ }

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
  ≡ᵇ→≡ {zero} {suc m} H = ⊥.rec $ false≢true H
  ≡ᵇ→≡ {suc n} {zero} H = ⊥.rec $ false≢true H
  ≡ᵇ→≡ {suc n} {suc m} H = cong suc (≡ᵇ→≡ H)

enum→semiDec : {B : A → Type ℓ} → discrete A → enumerable B → semiDecidable B
enum→semiDec {_} {A} = rec2 isPropSemiDecidable λ { (d , Hd) (fₑ , Hₑ) →
  let open Lemma d Hd fₑ Hₑ in
  ∣_∣₁ $ fₛ , λ a → ↔-trans (Hₑ a) $
    →: map (λ (n , H) → n , subst (λ x → ⁇.rec _ _ x ≡ _) (sym H) (≡→≟ a))
    ←: map (λ (n , H) → n , ≟→≡ a (fₑ n) H) }
  where
  module Lemma {B : A → Type ℓ}
    (d : A × A → Bool) (Hd : d decides (λ (a , b) → a ≡ b))
    (fₑ : ℕ → Maybe A) (Hₑ : fₑ enumerates B)
    where
    _≟_ : A → Maybe A → Bool
    _≟_ a = ⁇.rec false (λ b → d (a , b))
    ≡→≟ : ∀ a → a ≟ just a ≡ true
    ≡→≟ a = Hd _ .to refl
    ≟→≡ : ∀ a a? → a ≟ a? ≡ true → a? ≡ just a
    ≟→≡ a nothing H = ⊥.rec $ false≢true H
    ≟→≡ a (just x) H = cong just $ sym $ Hd _ .from H
    fₛ : A → ℕ → Bool
    fₛ a n = a ≟ fₑ n

semiDec→sep : {B₁ : A → Type ℓ} {B₂ : A → Type ℓ'} →
  isPredicate B₁ → isPredicate B₂ → (∀ x → B₁ x → B₂ x → ⊥) →
  semiDecidable B₁ → semiDecidable B₂ → separatable B₁ B₂
semiDec→sep predB₁ predB₂ disjoint = map2 λ { (f , Hf) (g , Hg) →
  let open Lemma predB₁ predB₂ disjoint f g Hf Hg in
  separator , (λ x → →: H₁ x ←: H₃ x), (λ x → →: H₂ x ←: H₄ x) }
  where
  module Lemma {B₁ : A → Type ℓ} {B₂ : A → Type ℓ'}
    (predB₁ : isPredicate B₁) (predB₂ : isPredicate B₂) (disjoint : ∀ x → B₁ x → B₂ x → ⊥)
    (f g : A → ℕ → Bool) (Hf : f semiDecides B₁) (Hg : g semiDecides B₂)
    where
    fₚ : A → ℕ → Maybe Bool
    fₚ x n = if (f x n) then just true else (if g x n then just false else nothing)
    proper : {n m : ℕ} {a b : Bool} (x : A) → fₚ x n ≡ just a → fₚ x m ≡ just b → a ≡ b
    proper {n} {m} x p q with
         f x n in α | g x n in β | f x m in γ | g x m in δ
    ... | false     | false      | _          | _         = ⊥.rec $ ¬nothing≡just p
    ... | _         | _          | false      | false     = ⊥.rec $ ¬nothing≡just q
    ... | false     | true       | true       | _         = ⊥.rec $ disjoint x (Hf x .from ∣ m , eqToPath γ ∣₁)
                                                                               (Hg x .from ∣ n , eqToPath β ∣₁)
    ... | true      | _          | false      | true      = ⊥.rec $ disjoint x (Hf x .from ∣ n , eqToPath α ∣₁)
                                                                               (Hg x .from ∣ m , eqToPath δ ∣₁)
    ... | false     | true       | false      | true      = (sym $ just-inj _ _ p) ∙ (just-inj _ _ q)
    ... | true      | _          | true       | _         = (sym $ just-inj _ _ p) ∙ (just-inj _ _ q)
    separator : A → part Bool
    separator x = record { f = fₚ x ; proper = proper x }
    H₁ : ∀ x → B₁ x → separator x ▻ true
    H₁ x B₁x = map (λ (n , H) → n , subst (λ x → (if x then _ else _) ≡ _) (sym H) refl) (Hf x .to B₁x)
    H₂ : ∀ x → B₂ x → separator x ▻ false
    H₂ x B₂x = map (λ (n , H) → n , aux n H) (Hg x .to B₂x) where
      aux : ∀ n → g x n ≡ true → fₚ x n ≡ just false
      aux n H with f x n in α
      ... | false = subst (λ x → (if x then _ else _) ≡ _) (sym H) refl
      ... | true = ⊥.rec $ disjoint x (Hf x .from ∣ n , eqToPath α ∣₁) B₂x
    H₃ : ∀ x → separator x ▻ true → B₁ x
    H₃ x = ∥₁.rec (predB₁ x) λ (n , H) → Hf x .from ∣ n , aux n H ∣₁ where
      aux : ∀ n → fₚ x n ≡ just true → f x n ≡ true
      aux n H with
            f x n | g x n
      ... | true  | _       = refl
      ... | false | true    = ⊥.rec $ false≢true (just-inj _ _ H)
      ... | false | false   = ⊥.rec $ ¬nothing≡just H
    H₄ : ∀ x → separator x ▻ false → B₂ x
    H₄ x = ∥₁.rec (predB₂ x) λ (n , H) → Hg x .from ∣ n , aux n H ∣₁ where
      aux : ∀ n → fₚ x n ≡ just false → g x n ≡ true
      aux n H with
            g x n | f x n
      ... | true  | _       = refl
      ... | false | true    = ⊥.rec $ true≢false (just-inj _ _ H)
      ... | false | false   = ⊥.rec $ ¬nothing≡just H
