{-# OPTIONS --cubical --safe #-}

module SyntheticAlt.Definitions.Properties where
open import SyntheticAlt.PartialFunction
open import SyntheticAlt.Definitions.Base
open import SyntheticAlt.Definitions.Prophood

open import Cubical.Foundations.Prelude hiding (_∨_)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Logic using (∥_∥ₚ; ⊤; ⊥)
open import Data.Nat hiding (_≟_)
open import CubicalExt.Data.Bool hiding (_≟_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe as ⁇
open import Cubical.Data.Sigma hiding (_∨_)
open import Cubical.Data.Unit
open import Cubical.Data.Equality using (pathToEq; eqToPath) renaming (refl to reflEq)
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff
open import CubicalExt.Logic.ConstructiveEpsilon

private variable
  ℓ ℓ' : Level
  A A' : Type ℓ
  B B' : A → Type ℓ

decReduction : isPredicate B → B ⪯ B' → decidable B' → decidable B
decReduction {B = B} {B' = B'} pred (fᵣ , Hᵣ) (fᵈ , Hᵈ) =  fᵈ ∘ fᵣ , λ x →
  B x               ↔⟨ Hᵣ x ⟩
  B' (fᵣ x)         ↔⟨ Hᵈ (fᵣ x) ⟩
  fᵈ (fᵣ x) ≡ true  ↔∎

semiDecReduction : B ⪯ B' → semiDecidable B' → semiDecidable B
semiDecReduction {B = B} {B' = B'} (fᵣ , Hᵣ) (fᵈ , Hᵈ) = fᵈ ∘ fᵣ , λ x →
  B x                             ↔⟨ Hᵣ x ⟩
  B' (fᵣ x)                       ↔⟨ Hᵈ (fᵣ x) ⟩
  ∃ ℕ (λ n → fᵈ (fᵣ x) n ≡ true)  ↔∎

dec→pDec : isPredicate B → decidable B → decidableₚ B
dec→pDec pred (fᵈ , Hᵈ) = (λ x → ⊤ , λ _ → fᵈ x) ,
  λ x → →: (λ H → tt* , Hᵈ x .to H)
        ←: (λ (_ , H) → Hᵈ x .from H)

discreteℕ : discrete ℕ
discreteℕ = (λ (n , m) → n ≡ᵇ m)
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
enum→semiDec {_} {A} (fᵈ , Hᵈ) (fₑ , Hₑ) =
  fᵈ⁻ , λ x → ↔-trans (Hₑ x) $
    →: map (λ (n , H) → n , subst (λ x → ⁇.rec _ _ x ≡ _) (sym H) (≡→≟ x))
    ←: map (λ (n , H) → n , ≟→≡ x (fₑ n) H)
  where
  _≟_ : A → Maybe A → Bool
  _≟_ x = ⁇.rec false (λ y → fᵈ (x , y))
  ≡→≟ : ∀ x → x ≟ just x ≡ true
  ≡→≟ x = Hᵈ _ .to refl
  ≟→≡ : ∀ x x? → x ≟ x? ≡ true → x? ≡ just x
  ≟→≡ x nothing H = ⊥.rec $ false≢true H
  ≟→≡ x (just _) H = cong just $ sym $ Hᵈ _ .from H
  fᵈ⁻ : A → ℕ → Bool
  fᵈ⁻ x n = x ≟ fₑ n

semiDec→sep : {B₁ : A → Type ℓ} {B₂ : A → Type ℓ'} →
  isPredicate B₁ → isPredicate B₂ → (∀ x → B₁ x → B₂ x → ⊥.⊥) →
  semiDecidable B₁ → semiDecidable B₂ → separatable B₁ B₂
semiDec→sep {_} {A} {_} {_} {B₁} {B₂} pred₁ pred₂ disjoint (f , Hf) (g , Hg) =
  fₚ , (λ x → →: H₁ x ←: H₃ x), (λ x → →: H₂ x ←: H₄ x)
  where
  eval : ∀ x n → T (f x n ∨ g x n) → Bool
  eval x n with f x n | g x n
  ... | true  | _     = λ _ → true
  ... | false | true  = λ _ → false
  ... | false | false = λ ()
  2-const : ∀ x → 2-Constant λ { (n , H) → eval x n H }
  2-const x (n , Hn) (m , Hm) = {!   !}
  fₚ : A → part Bool
  fₚ x = ∥ (Σ ℕ λ n → T $ f x n ∨ g x n) ∥ₚ ,
    rec→Set isSetBool (uncurry (eval x)) (2-const x)
  H₁ : ∀ x → B₁ x → fₚ x ≐ true
  H₁ x B₁x = map (λ (n , H) → n , subst (λ b → T $ b ∨ _) (sym H) tt) (Hf x .to B₁x) ,
    {!   !}
  H₂ : ∀ x → B₂ x → fₚ x ≐ false
  H₂ x B₂x = {!     !} , {!   !}
  H₃ : ∀ x → fₚ x ≐ true → B₁ x
  H₃ x (p , H) = {!   !}
  H₄ : ∀ x → fₚ x ≐ false → B₂ x
  H₄ x = {!   !}
