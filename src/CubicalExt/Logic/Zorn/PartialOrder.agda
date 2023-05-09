{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary
open BinaryRelation
module CubicalExt.Logic.Zorn.PartialOrder {u r} {U : Type u} {_≤_ : Rel U U r}
  (≤-prop     : isPropValued _≤_)
  (≤-refl     : isRefl _≤_)
  (≤-antisym  : isAntisym _≤_)
  (≤-trans    : isTrans _≤_) where

open import CubicalExt.Axiom.ExcludedMiddle
open import CubicalExt.Foundations.Powerset* using (𝒫; lift𝒫; _∈_; _⊆_; ∈-isProp)
open import CubicalExt.Foundations.Function using (_$_; it)
open import Cubical.Foundations.HLevels using (hProp; isPropΠ2)
open import Cubical.Foundations.Isomorphism using (Iso)
open import CubicalExt.Functions.Logic using (∥_∥ₚ; inl; inr; _∨_; _∧_; ∨-elimˡ; ∨-elimʳ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma using (∃-syntax; _×_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec; rec2; map)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
import Cubical.Data.Sum as ⊎

private variable
  ℓ ℓ' : Level
  x y : U

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

maximum : U → Type _
maximum m = ∀ x → m ≤ x → x ≡ m

-- Given a parial order (U, ≤), if every chain A ⊆ U has an upper bound, then (U, ≤) merely has a maximum.
Zorn = EveryChainHasUpperBound → ∃[ m ∈ U ] maximum m

--------------------------------------------------
-- Proof

Successive = ∀ x → Σ[ y ∈ U ] x ≤ y × (¬ x ≡ y) × ∀ z → x ≤ z → z ≤ y → z ≡ x ∨ z ≡ y

-- least upper bound
supremum : 𝒫 U ℓ → U → Type _
supremum A sup = upperBound A sup × ∀ ub → upperBound A ub → sup ≤ ub

supUnique : {A : 𝒫 U ℓ} {sup₁ sup₂ : U} → supremum A sup₁ → supremum A sup₂ → sup₁ ≡ sup₂
supUnique (ub₁ , least₁) (ub₂ , least₂) = ≤-antisym _ _ (least₁ _ ub₂) (least₂ _ ub₁)

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

  isChainTower : ∀ x y → Tower ℓ x → Tower ℓ' y → x ≤ y ∨ y ≤ x
  isChainTowerSet : isChain (TowerSet ℓ)
  isChainTowerSet x y = rec2 squash₁ (isChainTower x y)

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

  module _ {ℓ} {A : 𝒫 U ℓ-zero} (isChainA : isChain A) where
    private
      LiftA = lift𝒫 {ℓ = ℓ} A

    isChainLift : isChain LiftA
    isChainLift x y (lift x∈) (lift y∈) = isChainA x y x∈ y∈

    private
      supA         = hasSup A isChainA .fst
      supA-ish     = hasSup A isChainA .snd
      supLiftA     = hasSup LiftA isChainLift .fst
      supLiftA-ish = hasSup LiftA isChainLift .snd
      supA-ish' : supremum LiftA supA
      supA-ish' = (λ { x (lift x∈) → supA-ish .fst x x∈ }) ,
        λ ub H → supA-ish .snd ub λ x x∈ → H x (lift x∈)

    supLiftA≡supA : supLiftA ≡ supA
    supLiftA≡supA = supUnique supLiftA-ish supA-ish'

  liftTower : Tower ℓ-zero x → Tower ℓ x
  liftTowerSet : x ∈ TowerSet ℓ-zero → x ∈ TowerSet ℓ
  liftTowerSet ∣ x∈ ∣₁ = ∣ liftTower x∈ ∣₁
  liftTowerSet (squash₁ x∈₁ x∈₂ i) = squash₁ (liftTowerSet x∈₁) (liftTowerSet x∈₂) i

  liftTower (includeSuc x x∈) = includeSuc x (liftTower x∈)
  liftTower (includeSup A A⊆ isChainA) = subst (Tower _) (supLiftA≡supA isChainA) $
    includeSup (lift𝒫 A) (λ { (lift x∈) → liftTowerSet (A⊆ x∈)}) (isChainLift isChainA)

  lowerTowerSet : x ∈ TowerSet ℓ → x ∈ TowerSet ℓ-zero
  lowerTowerSet = {!   !}

  Σsup = hasSup (TowerSet ℓ-zero) isChainTowerSet
  sup = Σsup .fst
  sup-ub = Σsup .snd .fst

  sup∈TowerSet : sup ∈ TowerSet ℓ-zero
  sup∈TowerSet = lowerTowerSet $ ∣_∣₁ $
    includeSup (TowerSet ℓ-zero) liftTowerSet isChainTowerSet

  Σsuc = hasSuc sup
  suc = Σsuc .fst
  sup≤suc = Σsuc .snd .fst
  sup≢suc = Σsuc .snd .snd .fst

  false : ⊥
  false = sup≢suc $ ≤-antisym _ _ sup≤suc $
    sup-ub suc $ map (includeSuc sup) sup∈TowerSet
