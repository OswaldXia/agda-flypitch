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
open import CubicalExt.Functions.Logic using (∥_∥ₚ; inl; inr; _∨_; _∧_; ∨-elimˡ; ∨-elimʳ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (∃-syntax; _×_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec; rec2; map)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
import Cubical.Data.Sum as ⊎

private variable
  ℓ ℓ' : Level
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

Successive = ∀ x → Σ[ y ∈ U ] x ≤ y × (¬ y ≤ x) × ∀ z → x ≤ z → z ≤ y → z ≡ x ∨ z ≡ y

-- least upper bound
supremum : 𝒫 U ℓ → U → Type _
supremum A sup = upperBound A sup × ∀ ub → upperBound A ub → sup ≤ ub

EveryChainHasSupremum = ∀ {ℓ} (A : 𝒫 U ℓ) → isChain A → Σ[ sup ∈ U ] supremum A sup

module _ ⦃ em : ∀ {ℓ} → EM ℓ ⦄ (hasSuc : Successive) (hasSup : EveryChainHasSupremum) where
  open import CubicalExt.Logic.Classical

  data Tower (ℓ : Level) : U → Type (ℓ-max (ℓ-max u r) (ℓ-suc ℓ))
  TowerSet : (ℓ : Level) → 𝒫 U _
  TowerSet ℓ x = ∥ Tower ℓ x ∥ₚ

  data Tower ℓ where
    includeSuc : (x : U) → Tower ℓ x → Tower ℓ (hasSuc x .fst)
    includeSup : (A : 𝒫 U ℓ) → (A ⊆ TowerSet ℓ) → (isChainA : isChain A) →
      Tower ℓ (hasSup A isChainA .fst)

  isChainTowerSet : isChain (TowerSet ℓ)
  isChainTowerSet x y = rec2 squash₁ (isChainTower x y) where
    isChainTower  : ∀ x y → Tower ℓ x → Tower ℓ' y → x ≤ y ∨ y ≤ x

    isChainTower' : ∀ x y → Tower ℓ x → y ∈ TowerSet ℓ' → x ≤ y ∨ y ≤ x
    isChainTower' x y x∈ ∣ y∈ ∣₁ = isChainTower x y x∈ y∈
    isChainTower' x y x∈ (squash₁ y∈₁ y∈₂ i) = squash₁ (isChainTower' x y x∈ y∈₁) (isChainTower' x y x∈ y∈₂) i

    module _ y (y∈ : Tower ℓ y) where
      private y' = hasSuc y .fst
      almostChain : ∀ x → Tower ℓ' x → x ≤ y ∨ y' ≤ x

      almostChain' : ∀ x → x ∈ TowerSet ℓ' → x ≤ y ∨ y' ≤ x
      almostChain' x ∣ x∈ ∣₁ = almostChain x x∈
      almostChain' x (squash₁ x∈₁ x∈₂ i) = squash₁ (almostChain' x x∈₁) (almostChain' x x∈₂) i

      almostChain x' (includeSuc x x∈) with isChainTower x' y (includeSuc x x∈) y∈
      ... | IH = rec2 squash₁
        (λ{ (⊎.inl x≤y) (⊎.inl x'≤y) → inl x'≤y
          ; (⊎.inl x≤y) (⊎.inr y≤x') → rec squash₁
            (λ{ (⊎.inl y≡x)  → inr $ subst (λ x → _ ≤ hasSuc x .fst) y≡x (≤-refl _)
              ; (⊎.inr y≡x') → inl $ subst (λ x → _ ≤ x) (sym y≡x') (≤-refl _) })
            (noMid y x≤y y≤x')
          ; (⊎.inr y'≤x) _ → inr $ ≤-trans y' x x' y'≤x x≤x' })
        (almostChain x x∈) IH where
        x≤x'  = hasSuc x .snd .fst
        noMid = hasSuc x .snd .snd .snd

      almostChain x (includeSup A A⊆ isChainA) with em {P = upperBound A y}
      ... | yes p = inl $ hasSup A isChainA .snd .snd y p
      ... | no ¬p = inr $ rec (≤-prop _ _)
        (λ { (z , ¬ub) → let (z∈A , ¬z≤y) = ¬→→∧ (z ∈ A) ⦃ ∈-isProp _ _ _ _ ⦄ (z ≤ y) ¬ub in
          ≤-trans y' z x
            (∨-elimʳ (≤-prop _ _) (almostChain' z (A⊆ z∈A)) ¬z≤y)
            (hasSup A isChainA .snd .fst z z∈A) })
        (¬∀→∃¬ ¬p)

    isChainTower x y' x∈ (includeSuc y y∈) = rec squash₁
      (λ{ (⊎.inl x≤y)  → inl (≤-trans x y y' x≤y y≤y')
        ; (⊎.inr y'≤x) → inr y'≤x })
      (almostChain y y∈ x x∈) where y≤y' = hasSuc y .snd .fst

    isChainTower x y x∈ (includeSup A A⊆ isChainA) with em {P = upperBound A x}
    ... | yes p = inr $ hasSup A isChainA .snd .snd x p
    ... | no ¬p = inl $ rec (≤-prop _ _)
      (λ{ (z , ¬ub) → let (z∈A , ¬z≤x) = ¬→→∧ (z ∈ A) ⦃ ∈-isProp _ _ _ _ ⦄ (z ≤ x) ¬ub in
        ≤-trans x z y
          (∨-elimˡ (≤-prop _ _) (isChainTower' x z x∈ (A⊆ z∈A)) ¬z≤x)
          (hasSup A isChainA .snd .fst z z∈A) })
      (¬∀→∃¬ ¬p)

  liftTower : (x : U) → Tower ℓ-zero x → Tower ℓ x
  liftTower _ (includeSuc x x∈) = includeSuc x (liftTower x x∈)
  liftTower {ℓ} _ (includeSup A A⊆ isChainA) = {! includeSup  !}

  sup : U
  sup = hasSup (TowerSet ℓ-zero) isChainTowerSet .fst

  sup∈tower : sup ∈ TowerSet _
  sup∈tower = ∣_∣₁ $ includeSup (TowerSet ℓ-zero) (map $ liftTower _) isChainTowerSet

  false : ⊥
  false = {!   !}
