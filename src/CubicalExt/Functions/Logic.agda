{-# OPTIONS --cubical --safe #-}

module CubicalExt.Functions.Logic where

open import Cubical.Foundations.Prelude hiding (_∨_; _∧_)
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Functions.Logic hiding (⊤; ⊥)
  renaming (_⊔′_ to infixr 3 _∨_; _⊓′_ to infixr 3 _∧_) public
import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (Unit*; tt*)
open import Cubical.HITs.PropositionalTruncation using (rec)

private variable
  ℓ : Level
  A B : Type ℓ

⊥ : ∀ {ℓ} → hProp ℓ
⊥ = ⊥.⊥* , λ ()

⊤ : ∀ {ℓ} → hProp ℓ
⊤ = Unit* , (λ _ _ _ → tt*)

∨-elimˡ : isProp A → (A ∨ B) → (B → ⊥.⊥) → A
∨-elimˡ Aprop A∨B ¬b = rec Aprop
  (λ { (inl a) → a ; (inr b) → ⊥.rec (¬b b) }) A∨B

∨-elimʳ : isProp B → (A ∨ B) → (A → ⊥.⊥) → B
∨-elimʳ Bprop A∨B ¬a = rec Bprop
  (λ { (inl a) → ⊥.rec (¬a a) ; (inr b) → b }) A∨B
