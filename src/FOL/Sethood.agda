{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Sethood (ℒ : Language {u}) where
open import FOL.Base ℒ hiding (⊥)
open Language ℒ

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude using (refl; cong)
open import Cubical.Data.Equality using (eqToPath; pathToEq)
open import Cubical.Relation.Nullary using (¬_; yes; no; Discrete; Discrete→isSet)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Function using (_$_)

discreteTerm : Discrete (Termₗ l)
discreteTerm (var zero) (var zero) = yes refl
discreteTerm (var zero) (var (suc k₂)) = no helper where
  helper : ¬ var zero ≡ var (suc k₂)
  helper p with var-injective $ pathToEq p
  ... | ()
discreteTerm (var (suc k₁)) (var zero) = no helper where
  helper : ¬ var (suc k₁) ≡ var zero
  helper p with var-injective $ pathToEq p
  ... | ()
discreteTerm (var (suc k₁)) (var (suc k₂)) with discreteTerm (var k₁) (var k₂)
... | yes p rewrite var-injective $ pathToEq p = yes refl
... | no ¬p = no λ q → ¬p $ cong var $ eqToPath $ suc-injective $ var-injective $ pathToEq q
discreteTerm (var k) (func f) = no helper where
  helper : ¬ var k ≡ func f
  helper p with pathToEq p
  ... | ()
discreteTerm (var k) (app t₁ t₂) = no helper where
  helper : ¬ var k ≡ app t₁ t₂
  helper p with pathToEq p
  ... | ()
discreteTerm (func f) (var k) = no helper where
  helper : ¬ func f ≡ var k
  helper p with pathToEq p
  ... | ()
discreteTerm (func f₁) (func f₂) with discreteFunctions _ f₁ f₂
... | yes p = {!   !}
... | no ¬p = {!   !}
discreteTerm (func f) (app t₁ t₂) = no helper where
  helper : ¬ func f ≡ app t₁ t₂
  helper p with pathToEq p
  ... | ()
discreteTerm (app t₁ t₂) (var k) = no helper where
  helper : ¬ app t₁ t₂ ≡ var k
  helper p with pathToEq p
  ... | ()
discreteTerm (app t₁ t₂) (func f) = no helper where
  helper : ¬ app t₁ t₂ ≡ func f
  helper p with pathToEq p
  ... | ()
discreteTerm (app t₁ t₂) (app s₁ s₂) = {!   !}
