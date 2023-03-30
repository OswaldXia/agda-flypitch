{-# OPTIONS --cubical --safe #-}

module CubicalExt.Data.Vec where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
  using (_≡_; cong₂; _∙_; isSet; funExt; implicitFunExt; toPathP)
open import Cubical.HITs.SetQuotients using (_/_; rec)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; _∷_; refl)
open import Function using (_$_)
open import Relation.Binary using (Rel; Reflexive)

private variable
  a b r : Level
  A : Type a
  B : Type a
  n : ℕ

module _ {R : Rel A r} where
  private _≈_ = Pointwise R
  module _ (R-refl : Reflexive R) (Bset : isSet B) where

    quotientLift : (f : Vec A n → B) → (∀ {xs ys} → xs ≈ ys → f xs ≡ f ys) → Vec (A / R) n → B
    quotientLift f H [] = f []
    quotientLift f H (x ∷ xs) = rec Bset
      (λ x → quotientLift (λ xs → f $ x ∷ xs) (λ xs≈ys → H $ R-refl ∷ xs≈ys) xs)
      (λ _ _ aRb → cong₂ (λ f (H : ∀ {xs ys} → xs ≈ ys → _) → quotientLift f H xs)
        (funExt $ λ xs → H $ aRb ∷ refl R-refl)
        (implicitFunExt $ implicitFunExt $ funExt $ λ _ → toPathP $ Bset _ _ _ _)
      ) x
