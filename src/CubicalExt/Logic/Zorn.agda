{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary
open BinaryRelation
module CubicalExt.Logic.Zorn {u r} {U : Type u} {_≤_ : Rel U U r}
  (≤-prop : isPropValued _≤_) (≤-refl : isRefl _≤_) (≤-trans : isTrans _≤_) where

open import CubicalExt.Axiom.ExcludedMiddle
open import CubicalExt.Foundations.Powerset* using (𝒫; _∈_; _⊆_; ∈-isProp)
open import CubicalExt.Foundations.Function using (_$_; it)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ2)
open import CubicalExt.Functions.Logic using (∥_∥ₚ; inl; inr; _∨_; _∧_; ∨-elimˡ)
open import Cubical.Data.Sigma using (∃-syntax; _×_)
open import Cubical.HITs.PropositionalTruncation using (squash₁; elim; elim2)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
import Cubical.Data.Sum as ⊎

private variable
  ℓ : Level
  x y : U
  A : 𝒫 U ℓ

instance
  ≤-propImplicit : isPropImplicit (x ≤ y)
  ≤-propImplicit = ≤-prop _ _ _ _

--------------------------------------------------
-- Definition

isChain : 𝒫 U ℓ → Type _
isChain A = ∀ x y → x ∈ A → y ∈ A → x ≤ y ∨ y ≤ x

upperBound : 𝒫 U ℓ → U → Type _
upperBound A ub = ∀ x → x ∈ A → x ≤ ub

EveryChainHasUpperBound = ∀ {ℓ} (A : 𝒫 U ℓ) → Σ[ ub ∈ U ] upperBound A ub

premaximum : U → Type _
premaximum m = ∀ x → m ≤ x → x ≤ m

-- Given preorder (U, ≤), if every chain A ⊆ U has an upper bound, then (U, ≤) merely has a premaximum.
Zorn = EveryChainHasUpperBound → ∃[ m ∈ U ] premaximum m

--------------------------------------------------
-- Proof

Successive = ∀ x → Σ[ y ∈ U ] x ≤ y × (¬ x ≡ y) × ∀ z → x ≤ z → z ≤ y → z ≡ x ∨ z ≡ y

-- least upper bound
supremum : 𝒫 U ℓ → U → Type _
supremum A sup = upperBound A sup × ∀ ub → upperBound A ub → sup ≤ ub

EveryChainHasSupremum = ∀ {ℓ} (A : 𝒫 U ℓ) → isChain A → Σ[ sup ∈ U ] supremum A sup

module _ ⦃ em : ∀ {ℓ} → EM ℓ ⦄ (hasSuc : Successive) (hasSup : EveryChainHasSupremum) where
  open import CubicalExt.Logic.Classical

  data Tower (ℓ : Level) : U → Type (ℓ-max (ℓ-max u r) (ℓ-suc ℓ)) where
    includeSuc : (x : U) → Tower ℓ x → Tower ℓ (hasSuc x .fst)
    includeSup : (A : 𝒫 U ℓ) → (∀ x → x ∈ A → Tower ℓ x) → (isChainA : isChain A) →
      Tower ℓ (hasSup A isChainA .fst)

  TowerSet : (ℓ : Level) → 𝒫 U _
  TowerSet ℓ x = ∥ Tower ℓ x ∥ₚ

  isChainTowerSet : isChain (TowerSet ℓ)
  isChainTowerSet x y = elim2 (λ _ _ → squash₁) (isChainTower x y) where
    isChainTower : ∀ x y → Tower ℓ x → Tower ℓ y → x ≤ y ∨ y ≤ x
    isChainTower x .(hasSuc y .fst) x∈ (includeSuc y y∈) with hasSuc y
    ... | (y' , y≤y' , ¬y≡y' , suc) = elim {P = λ _ → x ≤ y' ∨ y' ≤ x} (λ _ → squash₁)
      (λ{ (⊎.inl x≤y ) → inl (≤-trans x y y' x≤y y≤y')
        ; (⊎.inr y'≤x) → inr y'≤x })
      (helper x x∈) where
      helper : ∀ z → Tower ℓ z → z ≤ y ∨ y' ≤ z
      helper = {!   !}
    isChainTower x .(hasSup A isChainA .fst) x∈ (includeSup A A⊆ isChainA) with em {P = upperBound A x}
    ... | yes p = inr $ hasSup A isChainA .snd .snd x p
    ... | no ¬p = inl $ elim (λ _ → ≤-prop _ _)
      (λ { (y , ¬ub) → let (y∈A , ¬y≤x) = ¬→→∧ (y ∈ A) ⦃ ∈-isProp _ _ _ _ ⦄ (y ≤ x) ¬ub in
        ≤-trans x y (hasSup A isChainA .fst)
          (∨-elimˡ (≤-prop _ _) (isChainTower x y x∈ (A⊆ y y∈A)) ¬y≤x)
          (hasSup A isChainA .snd .fst y y∈A) })
      (¬∀→∃¬ ¬p)
