{-# OPTIONS --cubical --safe #-}

module CubicalExt.Axiom.UniquenessOfIdentity.Loop where

open import Cubical.Core.Everything hiding (_≡_)
open import Cubical.Foundations.Prelude using (isSet)
open import Cubical.Data.Equality using (eqToPath; pathToEq; pathToEq-eqToPath)

open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; cong; refl; sym; trans)
open Eq.≡-Reasoning

private variable
  ℓ : Level

UIP : Type ℓ → Type ℓ
UIP A = {x : A} (p : x ≡ x) → refl ≡ p

isSet→UIP : ∀ {A : Type ℓ} → isSet A → UIP A
isSet→UIP Aset p =          begin
  refl                     ≡˘⟨ pathToEq $ pathToEq-eqToPath refl ⟩
  pathToEq (eqToPath refl) ≡⟨ cong pathToEq (pathToEq $ Aset _ _ (eqToPath refl) (eqToPath p)) ⟩
  pathToEq (eqToPath p)    ≡⟨ pathToEq $ pathToEq-eqToPath p ⟩
  p                        ∎
