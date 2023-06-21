{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module SyntheticAlt.PartialFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic using (⊤; ⊥)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁

private variable
  ℓ ℓ' : Level
  A B : Type ℓ

isPredicate : (A → Type ℓ) → Type _
isPredicate B = ∀ x → isProp (B x)

part : Type ℓ → Type _
part A = Σ (hProp ℓ-zero) λ P → ⟨ P ⟩ → A

isOfHLevelPart : ∀ n → isOfHLevel (suc (suc n)) A → isOfHLevel (suc (suc n)) (part A)
isOfHLevelPart n lA = isOfHLevelΣ (suc (suc n))
  (isOfHLevelPlus' 2 isSetHProp) λ _ → isOfHLevelΠ (suc (suc n)) λ _ → lA

isSetPart : isSet A → isSet (part A)
isSetPart = isOfHLevelPart 0

defined : part A → Type _
defined (P , _) = ⟨ P ⟩

isPropDefined : isPredicate (defined {A = A})
isPropDefined (P , _) = str P

value : (xₚ : part A) → defined xₚ → A
value (_ , f) H = f H

-- canonical undefined
∅ : part A
∅ = ⊥ , λ ()

_≐_ : part A → A → Type _
xₚ ≐ x = Σ (defined xₚ) λ H → value xₚ H ≡ x

isOfHLevel≐ : ∀ n → isOfHLevel (suc (suc n)) A → (xₚ : part A) (x : A) → isOfHLevel (suc n) (xₚ ≐ x)
isOfHLevel≐ n lA (P , f) x = isOfHLevelΣ (suc n)
  (isOfHLevelPlus' 1 (str P)) λ _ → lA _ _

isProp≐ : isSet A → (xₚ : part A) (x : A) → isProp (xₚ ≐ x)
isProp≐ = isOfHLevel≐ 0

≐-functional : (xₚ : part A) {x y : A} → xₚ ≐ x → xₚ ≐ y → x ≡ y
≐-functional (P , f) (p , fp≡x) (q , fq≡y) = sym fp≡x ∙ (cong f (str P p q)) ∙ fq≡y

total : (A → part B) → Type _
total f = ∀ x → defined (f x)

totalise : isSet B → (f : A → part B) → total f → (∀ x → Σ _ (f x ≐_))
totalise Bset f H x = value (f x) (H x) , H x , refl

partialise : isSet B → (A → B) → A → part B
partialise Bset f x = ⊤ , λ _ → f x
