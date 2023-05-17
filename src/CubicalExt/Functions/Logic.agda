{-# OPTIONS --cubical --safe #-}

module CubicalExt.Functions.Logic where

open import Cubical.Foundations.Prelude hiding (_∨_; _∧_; ~_)
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Functions.Logic hiding (⊤; ⊥; ¬_)
  renaming (_⊔′_ to infixr 3 _∨_; _⊓′_ to infixr 3 _∧_) public
import Cubical.Data.Empty as ⊥
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit using (Unit*; tt*)
open import Cubical.HITs.PropositionalTruncation using (rec)
open import Cubical.Relation.Nullary using (¬_)

private variable
  ℓ : Level
  A B : Type ℓ

⊥ : ∀ {ℓ} → hProp ℓ
⊥ = ⊥.⊥* , λ ()

⊤ : ∀ {ℓ} → hProp ℓ
⊤ = Unit* , (λ _ _ _ → tt*)

∨-elimˡ : isProp A → (A ∨ B) → ¬ B → A
∨-elimˡ Aprop A∨B ¬b = rec Aprop
  (λ { (⊎.inl a) → a ; (⊎.inr b) → ⊥.rec (¬b b) }) A∨B

∨-elimʳ : isProp B → (A ∨ B) → ¬ A → B
∨-elimʳ Bprop A∨B ¬a = rec Bprop
  (λ { (⊎.inl a) → ⊥.rec (¬a a) ; (⊎.inr b) → b }) A∨B

¬∨-demorgen : ¬ (A ∨ B) → (¬ A) ∧ (¬ B)
¬∨-demorgen ¬∨ = ¬∨ ∘ inl , ¬∨ ∘ inr
