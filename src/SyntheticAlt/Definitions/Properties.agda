{-# OPTIONS --cubical --safe #-}

module SyntheticAlt.Definitions.Properties where
open import SyntheticAlt.PartialFunction
open import SyntheticAlt.Definitions.Base
open import SyntheticAlt.Definitions.Prophood

open import Cubical.Foundations.Prelude hiding (_∨_)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic using (∥_∥ₚ; ⊤)
open import Data.Nat hiding (_≟_)
open import CubicalExt.Data.Bool renaming (_≟_ to discreteBool)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe as ⁇
open import Cubical.Data.Sigma hiding (_∨_)
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
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
  P : A → Type
  P x = (Σ ℕ λ n → f x n ≡ true) ⊎ (Σ ℕ λ n → g x n ≡ true)
  eval : ∀ x → P x → Bool
  eval x (inl _) = true
  eval x (inr _) = false
  2const : ∀ x → 2-Constant (eval x)
  2const x (inl _) (_⊎_.inl _) = refl
  2const x (inr _) (_⊎_.inr _) = refl
  2const x (inl p) (_⊎_.inr q) = ⊥.rec (disjoint x (Hf x .from ∣ p ∣₁) (Hg x .from ∣ q ∣₁))
  2const x (inr p) (_⊎_.inl q) = ⊥.rec (disjoint x (Hf x .from ∣ q ∣₁) (Hg x .from ∣ p ∣₁))
  fₚ : A → part Bool
  fₚ x = ∥ P x ∥ₚ , rec→Set isSetBool (eval x) (2const x)
  H₁ : ∀ x → B₁ x → fₚ x ≐ true
  H₁ x B₁x = ∣ inl $ ε (λ _ → isProp→isSet (isSetBool _ _)) (λ _ → discreteBool _ _) (Hf x .to B₁x) ∣₁ , refl
  H₂ : ∀ x → B₂ x → fₚ x ≐ false
  H₂ x B₂x = ∣ inr $ ε (λ _ → isProp→isSet (isSetBool _ _)) (λ _ → discreteBool _ _) (Hg x .to B₂x) ∣₁ , refl
  H₃ : ∀ x → fₚ x ≐ true → B₁ x
  H₃ x = uncurry aux where
    aux : (p : ⟨ fst (fₚ x) ⟩) → snd (fₚ x) p ≡ true → B₁ x
    aux ∣ inl p ∣₁ H = Hf x .from ∣ p ∣₁
    aux ∣ inr p ∣₁ H = ⊥.rec $ false≢true H
    aux (squash₁ p q i) H = pred₁ x (aux p {!   !}) {!   !} i
  H₄ : ∀ x → fₚ x ≐ false → B₂ x
  H₄ x (∣ inl p ∣₁ , H) = ⊥.rec $ true≢false H
  H₄ x (∣ inr p ∣₁ , H) = Hg x .from ∣ p ∣₁
  H₄ x (squash₁ p q i , H) = pred₂ x (H₄ x (p , {!   !})) (H₄ x (q , {!   !})) i
