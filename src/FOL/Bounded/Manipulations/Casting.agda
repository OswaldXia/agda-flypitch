{-# OPTIONS --cubical --safe #-}
{- currently not used -}

open import FOL.Language
module FOL.Bounded.Manipulations.Casting (ℒ : Language {u}) where
import FOL.Base ℒ as Free
open import FOL.Bounded.Base ℒ

open import Agda.Builtin.Equality using (_≡_; refl)
open import CubicalExt.Data.Nat using (ℕ; ℕ-UIP)

private variable
  m n : ℕ

castₜ : m ≡ n → Termₗ m l → Termₗ n l
castₜ refl t = t

castₜ-eq : {t : Termₗ m l} (eq : m ≡ m) → castₜ eq t ≡ t
castₜ-eq eq with ℕ-UIP eq
... | refl = refl

cast : m ≡ n → Formulaₗ m l → Formulaₗ n l
cast refl φ = φ

cast-eq : {φ : Formulaₗ m l} (eq : m ≡ m) → cast eq φ ≡ φ
cast-eq eq with ℕ-UIP eq
... | refl = refl
