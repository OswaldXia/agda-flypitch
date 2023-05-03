{-# OPTIONS --cubical --safe #-}

module CubicalExt.Functions.Logic where

open import Cubical.Foundations.Prelude hiding (_∨_; _∧_)
open import Cubical.Functions.Logic hiding (¬_)
  renaming (_⊔′_ to infixr 3 _∨_; _⊓′_ to infixr 3 _∧_) public
open import Cubical.Data.Empty using (rec)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation using (elim)
open import Cubical.Relation.Nullary using (¬_)

private variable
  ℓ : Level
  A B : Type ℓ

∨-elimˡ : isProp A → (A ∨ B) → ¬ B → A
∨-elimˡ Aprop A∨B ¬b = elim (λ _ → Aprop)
  (λ { (inl a) → a ; (inr b) → rec (¬b b) }) A∨B

∨-elimʳ : isProp B → (A ∨ B) → ¬ A → B
∨-elimʳ Bprop A∨B ¬a = elim (λ _ → Bprop)
  (λ { (inl a) → rec (¬a a) ; (inr b) → b }) A∨B
