{-# OPTIONS --cubical --safe #-}

open import CubicalExt.Axiom.ExcludedMiddle
module CubicalExt.Logic.Classical ⦃ em : ∀ {ℓ} → EM ℓ ⦄ where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_; _$_)
open import Cubical.Functions.Logic using () renaming (_⊓′_ to infixr 3 _∧_)
open import Cubical.Data.Empty using (⊥; ⊥*; rec; rec*)
open import Cubical.Data.Sigma using (∃-syntax)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁)
open import CubicalExt.Relation.Nullary

private variable
  ℓ ℓ' : Level
  A : Type ℓ
  P : A → Type ℓ

isSet→Discrete : isSet A → Discrete A
isSet→Discrete Aset x y = em ⦃ Aset x y _ _ ⦄

isSet→DiscreteEq : isSet A → DiscreteEq A
isSet→DiscreteEq = Discrete→DiscreteEq ∘ isSet→Discrete

module _ ⦃ Aprop : isPropImplicit A ⦄ where

  byContra : (¬ A → ⊥) → A
  byContra ¬A⇒⊥ with em ⦃ Aprop ⦄
  ... | yes p = p
  ... | no ¬p = rec (¬A⇒⊥ ¬p)

  byContra* : (¬ A → ⊥* {ℓ}) → A
  byContra* ¬A⇒⊥ with em ⦃ Aprop ⦄
  ... | yes p = p
  ... | no ¬p = rec* (¬A⇒⊥ ¬p)

module _ (A : Type ℓ) ⦃ Aprop : isPropImplicit A ⦄ (B : Type ℓ') ⦃ Bprop : isPropImplicit B ⦄ where

  ¬→→∧ : ¬ (A → B) → A ∧ ¬ B
  ¬→→∧ ¬→ = (byContra λ ¬a → ¬→ λ a → rec $ ¬a a) , (λ b → ¬→ λ _ → b)

module _ ⦃ Pprop : {x : A} → isPropImplicit (P x) ⦄ where

  ¬∀→∃¬ : (¬ ∀ x → P x) → ∃[ x ∈ A ] ¬ P x
  ¬∀→∃¬ ¬∀xPx = byContra ⦃ squash₁ _ _ ⦄ λ ¬∃x¬Px → ¬∀xPx λ x → byContra λ ¬Px → ¬∃x¬Px ∣ x , ¬Px ∣₁
