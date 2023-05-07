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
open import Cubical.Data.Sigma using (∃-syntax; _×_)
open import Cubical.HITs.PropositionalTruncation using (squash₁; elim; elim2)
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
    isChainTower : ∀ x y → Tower ℓ x → Tower ℓ' y → x ≤ y ∨ y ≤ x
    isChainTower x y' x∈ (includeSuc y y∈) = elim (λ _ → squash₁)
      (λ{ (⊎.inl x≤y)  → inl (≤-trans x y y' x≤y y≤y')
        ; (⊎.inr y'≤x) → inr y'≤x })
      (helper x x∈) where
      y≤y' = hasSuc y .snd .fst
      helper : ∀ w → Tower ℓ w → w ≤ y ∨ y' ≤ w
      helper w' (includeSuc w w∈) with isChainTower w' y (includeSuc w w∈) y∈
      ... | IH = elim2 (λ _ _ → squash₁)
        (λ{ (⊎.inl w≤y) (⊎.inl w'≤y) → inl w'≤y
          ; (⊎.inl w≤y) (⊎.inr y≤w') → elim {P = λ _ → w' ≤ y ∨ y' ≤ w'} (λ _ → squash₁)
            (λ{ (⊎.inl y≡w)  → inr $ subst (λ x → _ ≤ hasSuc x .fst) y≡w (≤-refl _)
              ; (⊎.inr y≡w') → inl $ subst (λ x → _ ≤ x) (sym y≡w') (≤-refl _) })
            (noMid y w≤y y≤w')
          ; (⊎.inr y'≤w) _ → inr $ ≤-trans y' w w' y'≤w w≤w' })
        (helper w w∈) IH where
        w≤w'  = hasSuc w .snd .fst
        noMid = hasSuc w .snd .snd .snd
      helper w (includeSup A A⊆ isChainA) with em {P = upperBound A y}
      ... | yes p = inl $ hasSup A isChainA .snd .snd y p
      ... | no ¬p = inr $ elim (λ _ → ≤-prop _ _)
        (λ { (z , ¬ub) → let (z∈A , ¬z≤y) = ¬→→∧ (z ∈ A) ⦃ ∈-isProp _ _ _ _ ⦄ (z ≤ y) ¬ub in
          ≤-trans y' z w
            (∨-elimʳ (≤-prop _ _) (helper z $ A⊆ z z∈A) ¬z≤y)
            (hasSup A isChainA .snd .fst z z∈A) })
        (¬∀→∃¬ ¬p)
    isChainTower x y x∈ (includeSup A A⊆ isChainA) with em {P = upperBound A x}
    ... | yes p = inr $ hasSup A isChainA .snd .snd x p
    ... | no ¬p = inl $ elim (λ _ → ≤-prop _ _)
      (λ { (z , ¬ub) → let (z∈A , ¬z≤x) = ¬→→∧ (z ∈ A) ⦃ ∈-isProp _ _ _ _ ⦄ (z ≤ x) ¬ub in
        ≤-trans x z y
          (∨-elimˡ (≤-prop _ _) (isChainTower x z x∈ $ A⊆ z z∈A) ¬z≤x)
          (hasSup A isChainA .snd .fst z z∈A) })
      (¬∀→∃¬ ¬p)
