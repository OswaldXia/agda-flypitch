{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Sethood ⦃ em : EM ⦄ (ℒ : Language {u}) where
open import FOL.Base ⦃ em ⦄ ℒ hiding (⊥)
open Language ℒ

open import Cubical.Foundations.Prelude
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
discreteTerm (func f₁) (func f₂) with discrete𝔉 _ f₁ f₂
... | yes p = yes (cong func p)
... | no ¬p = no λ q → ¬p $ eqToPath $ func-injective $ pathToEq q
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
discreteTerm (app f₁ t₁) (app f₂ t₂) with discreteTerm f₁ f₂ | discreteTerm t₁ t₂
... | yes p | yes q = yes (cong₂ app p q)
... | no ¬p | _     = no λ r → ¬p $ eqToPath $ app-injectiveˡ $ pathToEq r
... | _     | no ¬q = no λ r → ¬q $ eqToPath $ app-injectiveʳ $ pathToEq r

isSetTerm : isSet Term
isSetTerm = Discrete→isSet discreteTerm
