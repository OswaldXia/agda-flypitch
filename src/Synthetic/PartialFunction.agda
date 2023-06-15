{-# OPTIONS --cubical --safe #-}

module Synthetic.PartialFunction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Logic.ConstructiveEpsilon

private variable
  ℓ : Level
  A B : Type ℓ

record part (A : Type) : Type where
  constructor mkPart
  field
    f : ℕ → Maybe A
    proper : ∀ {n m x y} → f n ≡ just x → f m ≡ just y → x ≡ y

  eval : A → Type
  eval x = ∃ _ λ k → f k ≡ just x

  functional : isSet A → ∀ {x y} → eval x → eval y → x ≡ y
  functional Aset = rec2 (Aset _ _)
    (λ { (_ , Hn) (_ , Hm) → proper Hn Hm })

  opaque
    totalise : isSet A → ∃ _ eval → Σ _ eval
    totalise Aset xₚ = σ .snd .fst , ∣ σ .fst , σ .snd .snd ∣₁ where
      swapEval : ∃ _ eval → ∃ _ λ k → Σ _ λ x → f k ≡ just x
      swapEval = ∥₁.rec squash₁ λ (x , ea) → map (λ (n , H) → n , x , H) ea
      Σ[x] : ℕ → Type
      Σ[x] n = Σ _ λ x → f n ≡ just x
      isSetΣ[x] : ∀ n → isSet (Σ[x] n)
      isSetΣ[x] _ = isSetΣ Aset λ _ → isProp→isSet (isOfHLevelMaybe 0 (λ _ _ → Aset _ _) _ _)
      DecΣ[x] : ∀ n → Dec (Σ[x] n)
      DecΣ[x] n with f n
      ... | nothing = no λ (_ , H) → ⊥.rec (¬nothing≡just H)
      ... | just x = yes (x , refl)
      σ : Σ _ Σ[x]
      σ = ε isSetΣ[x] DecΣ[x] (swapEval xₚ)

_≐_ : part A → A → Type
xₚ ≐ x = part.eval xₚ x

converging : part A → Type
converging xₚ = ∃ _ (xₚ ≐_)

diverging : part A → Type
diverging xₚ = ∀ x → ¬ xₚ ≐ x

total : (f : A → part B) → Type _
total f = ∀ x → converging (f x)

totalise : (f : A → part B) → total f → isSet B → (∀ x → Σ _ (f x ≐_))
totalise f H Bset x = part.totalise (f x) Bset (H x)

partialise : (A → B) → A → part B
partialise f x = mkPart (λ _ → just (f x)) (λ p q → just-inj _ _ ((sym p) ∙ q))

--------------------------------------------------------------------------------
-- sethood of part

partΣ : Type → Type
partΣ A = Σ (ℕ → Maybe A) λ f → ∀ {n m x y} → f n ≡ just x → f m ≡ just y → x ≡ y

partΣIsoPart : Iso (partΣ A) (part A)
Iso.fun       partΣIsoPart (f , p) = mkPart f p
Iso.inv       partΣIsoPart xₚ = part.f xₚ , part.proper xₚ
Iso.leftInv   partΣIsoPart a = refl
Iso.rightInv  partΣIsoPart b = refl

partΣ≡Part : partΣ A ≡ part A
partΣ≡Part = isoToPath partΣIsoPart

isSetPartΣ : isSet A → isSet (partΣ A)
isSetPartΣ Aset = isSetΣ (isSet→ (isOfHLevelMaybe 0 Aset))
  λ _ → isSetImplicitΠ λ _ → isSetImplicitΠ λ _ → isSetImplicitΠ λ _ → isSetImplicitΠ
    λ _ → isSet→ $ isSet→ $ isProp→isSet $ Aset _ _

isSetPart : isSet A → isSet (part A)
isSetPart Aset = subst isSet partΣ≡Part (isSetPartΣ Aset)
