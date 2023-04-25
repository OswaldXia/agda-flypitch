{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
module FOL.PropertiesOfTheory.Properties (ℒ : Language {u}) where
open import FOL.PropertiesOfTheory.Base ℒ

open import FOL.Syntactics ℒ using (⊥-elim; ⇒-intro; ⇒-elim; weakening1; axiom1)
open import FOL.Bounded.Base ℒ using (_⇒_)
open import FOL.Bounded.Syntactics ℒ using (_⊦_; axiom)

open import Cubical.Foundations.Prelude
open import CubicalExt.Foundations.Powerset* using (_∈_)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim; map; map2)
open import Function using (_∘_; _$_)

⇒-intro-of-complete : ∀ {T φ₁ φ₂} → complete T →
  (T ⊦ φ₁ → T ⊦ φ₂) → T ⊦ φ₁ ⇒ φ₂
⇒-intro-of-complete {T} {φ₁} compl H = elim (λ _ → squash₁)
  (λ { (inl  φ₁∈T) → map (⇒-intro ∘ weakening1) $ H $ map axiom ∣ φ₁∈T ∣₁
     ; (inr ~φ₁∈T) → map (⇒-intro ∘ ⊥-elim ∘ weakening1) $
        map2 ⇒-elim (map (weakening1 ∘ axiom) ∣ ~φ₁∈T ∣₁) ∣ axiom1 ∣₁ })
  (compl .snd φ₁)
