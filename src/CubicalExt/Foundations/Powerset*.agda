{- Polymorphic version of "powerset" -}

{-# OPTIONS --cubical --safe #-}

module CubicalExt.Foundations.Powerset* where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Foundations.Function
open import Cubical.Data.Empty using (⊥*; isProp⊥*)
open import Cubical.Data.Unit using (Unit*; isPropUnit*)
open import Cubical.Data.Sigma
open import Cubical.Functions.Logic hiding (¬_)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim)

private variable
  ℓ ℓ' ℓ'' ℓ₁ ℓ₂ : Level
  X : Type ℓ
  Y : Type ℓ'

------------------------------------------------------------------------
-- Definition

ℙ : Type ℓ → (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
ℙ X ℓ' = X → hProp ℓ'

isSetℙ : isSet (ℙ X ℓ)
isSetℙ = isSetΠ λ x → isSetHProp

------------------------------------------------------------------------
-- Special sets

-- The empty set.

∅ : ℙ X ℓ-zero
∅ = λ _ → ⊥

∅* : ℙ X ℓ
∅* = λ _ → ⊥* , isProp⊥*

-- The universal set.

U : ℙ X ℓ-zero
U = λ _ → ⊤

U* : ℙ X ℓ
U* = λ _ → Unit* , isPropUnit*

------------------------------------------------------------------------
-- Membership

infix 5 _∈_ _∉_ _⊆_

_∈_ : X → ℙ X ℓ → Type _
x ∈ A = ⟨ A x ⟩

_∉_ : X → ℙ X ℓ → Type _
x ∉ A = ¬ ⟨ A x ⟩

subst-∈ : (A : ℙ X ℓ) {x y : X} → x ≡ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

∈-isProp : (A : ℙ X ℓ) (x : X) → isProp (x ∈ A)
∈-isProp A = snd ∘ A

------------------------------------------------------------------------
-- Subset

_⊆_ : ℙ X ℓ₁ → ℙ X ℓ₂ → Type _
A ⊆ B = ∀ {x} → x ∈ A → x ∈ B

⊆-isProp : (A B : ℙ X ℓ) → isProp (A ⊆ B)
⊆-isProp A B = isPropImplicitΠ $ λ x → isPropΠ $ λ _ → ∈-isProp B x

⊆-refl : (A : ℙ X ℓ) → A ⊆ A
⊆-refl A {x} = idfun (x ∈ A)

⊆-refl-consequence : (A B : ℙ X ℓ) → A ≡ B → (A ⊆ B) × (B ⊆ A)
⊆-refl-consequence A B p = subst (A ⊆_) p (⊆-refl A)
                         , subst (B ⊆_) (sym p) (⊆-refl B)

⊆-extensionality : (A B : ℙ X ℓ) → (A ⊆ B) × (B ⊆ A) → A ≡ B
⊆-extensionality A B (φ , ψ) =
  funExt (λ x → TypeOfHLevel≡ 1 (hPropExt (A x .snd) (B x .snd) φ ψ))

⊆-extensionalityEquiv : (A B : ℙ X ℓ) → (A ⊆ B) × (B ⊆ A) ≃ (A ≡ B)
⊆-extensionalityEquiv A B = isoToEquiv (iso (⊆-extensionality A B)
                                            (⊆-refl-consequence A B)
                                            (λ _ → isSetℙ A B _ _)
                                            (λ _ → isPropΣ (⊆-isProp A B) (λ _ → ⊆-isProp B A) _ _))

------------------------------------------------------------------------
-- Operations on sets

-- Union.

_∪_ : ℙ X ℓ₁ → ℙ X ℓ₂ → ℙ X _
A ∪ B = λ x → (x ∈ A , ∈-isProp A x) ⊔ (x ∈ B , ∈-isProp B x)

-- Intersection.

_∩_ : ℙ X ℓ₁ → ℙ X ℓ₂ → ℙ X _
A ∩ B = λ x → (x ∈ A , ∈-isProp A x) ⊓ (x ∈ B , ∈-isProp B x)

-- Image set.

_⟦_⟧ : (X → Y) → ℙ X ℓ → ℙ Y _
f ⟦ A ⟧ = λ y → (∃[ x ∈ _ ] (x ∈ A) × (y ≡ f x)) , squash₁

private variable
  A B : ℙ X ℓ
  f : X → Y
  x : X

⟦⟧⊆⟦⟧ : A ⊆ B → f ⟦ A ⟧ ⊆ f ⟦ B ⟧
⟦⟧⊆⟦⟧ {B = B} {f = f} A⊆B {x} H = elim (λ _ → ∈-isProp (f ⟦ B ⟧) x)
  (λ (x , x∈A , eq) → ∣ x , A⊆B x∈A , eq ∣₁) H

module SetBased (Xset : isSet X) where

  -- The singleton set.

  ｛_｝ : X → ℙ X _
  ｛ x ｝ = λ y → (x ≡ y) , Xset x y

  -- Incusion.

  infixl 6 _⨭_

  _⨭_ : (A : ℙ X ℓ) (x : X) → ℙ X _
  A ⨭ x = A ∪ ｛ x ｝

  ⊆⨭ : A ⊆ A ⨭ x
  ⊆⨭ x∈A = inl x∈A
