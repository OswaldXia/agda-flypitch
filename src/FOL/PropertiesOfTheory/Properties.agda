{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
module FOL.PropertiesOfTheory.Properties (ℒ : Language {u}) where
open import FOL.PropertiesOfTheory.Base ℒ

open import FOL.Syntactics ℒ using (⊥-elim; ⇒-elim; weakening1; axiom1) renaming (⇒-intro to ⇒I)
open import FOL.Bounded.Base ℒ using (_⇒_; ~_)
open import FOL.Bounded.Syntactics ℒ using (_⊦_; axiom)

open import Cubical.Foundations.Prelude hiding (~_)
open import CubicalExt.Foundations.Powerset* using (_∈_)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Empty using () renaming (rec to exfalso)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec; map; map2)
open import Cubical.Relation.Nullary using (¬_)
open import Function using (_∘_; _$_)

module Complete {T} (compl : complete T) where

  ⇒-intro : ∀ {φ₁ φ₂} → (T ⊦ φ₁ → T ⊦ φ₂) → T ⊦ φ₁ ⇒ φ₂
  ⇒-intro {φ₁} H = rec squash₁
    (λ{ (inl  φ₁∈T) → map (⇒I ∘ weakening1) $ H $ map axiom ∣ φ₁∈T ∣₁
      ; (inr ~φ₁∈T) → map (⇒I ∘ ⊥-elim ∘ weakening1) $
        map2 ⇒-elim (map (weakening1 ∘ axiom) ∣ ~φ₁∈T ∣₁) ∣ axiom1 ∣₁ })
    (compl .snd φ₁)

  ~-intro : ∀ {φ} → ¬ T ⊦ φ → T ⊦ ~ φ
  ~-intro ¬⊦ = ⇒-intro λ ⊦ → exfalso $ ¬⊦ ⊦
