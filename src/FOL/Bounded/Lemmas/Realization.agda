{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Structure.Base using (Structure)
module FOL.Bounded.Lemmas.Realization {v} (𝒮 : Structure {u} ℒ {v}) where

open import FOL.Base ℒ using (_[_/_]ᵥ)
open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Semantics ℒ
import FOL.Semantics ℒ as Free
open Structure 𝒮

open import Cubical.Core.Primitives renaming (_≡_ to _≡ₚ_)
open import Cubical.Data.Equality using (pathToEq)
open import Cubical.Foundations.HLevels using (isSet→isGroupoid; isSetHProp)
open import Cubical.HITs.SetTruncation using (∥_∥₂; elim; map)
open import CubicalExt.StdlibBridge.Logic using (hPropExt)

open import Data.Nat
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import StdlibExt.Relation.Binary.PropositionalEquivalence v as Iff hiding (map)

private variable
  n : ℕ

module Pre where
  open PreRealizer 𝒮 using () renaming (realizeₜ to rₜ; realizeType to r) public
  open Free.PreRealizer 𝒮 using () renaming (realizeₜ to 𝑟ₜ; realizeType to 𝑟) public
  open Iff.↔-Reasoning

  realizeₜ-eq : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (t : Termₗ n l) (xs : Vec Domain l)
    → rₜ 𝓋 t xs ≡ 𝑟ₜ 𝑣 (unboundₜ t) xs
  realizeₜ-eq 𝓋 𝑣 eq (var k)     xs = eq k
  realizeₜ-eq 𝓋 𝑣 eq (func f)    xs = refl
  realizeₜ-eq 𝓋 𝑣 eq (app t₁ t₂) xs rewrite realizeₜ-eq 𝓋 𝑣 eq t₂ [] = realizeₜ-eq 𝓋 𝑣 eq t₁ _

  realize-eq : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (φ : Formulaₗ n l) (xs : Vec Domain l)
    → r 𝓋 φ xs ↔ 𝑟 𝑣 (unbound φ) xs
  realize-eq 𝓋 𝑣 eq ⊥          xs = id
  realize-eq 𝓋 𝑣 eq (rel R)    xs = id
  realize-eq 𝓋 𝑣 eq (appᵣ φ t) xs
    rewrite realizeₜ-eq 𝓋 𝑣 eq t [] = realize-eq 𝓋 𝑣 eq φ _
  realize-eq 𝓋 𝑣 eq (t₁ ≈ t₂)  [] = ≡↔≡ (realizeₜ-eq 𝓋 𝑣 eq t₁ []) (realizeₜ-eq 𝓋 𝑣 eq t₂ [])
  realize-eq 𝓋 𝑣 eq (φ₁ ⇒ φ₂)  xs =
    →↔→ (realize-eq 𝓋 𝑣 eq φ₁ xs) (realize-eq 𝓋 𝑣 eq φ₂ xs)
  realize-eq 𝓋 𝑣 eq (∀' φ)     [] = Π↔Π $ λ x →
    realize-eq (x ∷ 𝓋) (𝑣 [ x / 0 ]ᵥ) (eq' x) φ [] where
    eq' : ∀ x k → lookup (x ∷ 𝓋) k ≡ (𝑣 [ x / 0 ]ᵥ) (toℕ k)
    eq' x zero    = refl
    eq' x (suc k) = eq k

module Opened where
  open OpenedRealizer 𝒮 using () renaming (realizeₜ to rₜ; realize to r) public
  open Free.Realizer 𝒮 using () renaming (realizeₜ to 𝑟ₜ; realize to 𝑟) public

  realizeₜ-eq : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (t : Term n)
    → rₜ 𝓋 t ≡ 𝑟ₜ 𝑣 (unboundₜ t)
  realizeₜ-eq 𝓋 𝑣 eq t = Pre.realizeₜ-eq 𝓋 𝑣 eq t []

  realize-eq : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (φ : ∥ Formula n ∥₂)
    → r 𝓋 φ ≡ₚ 𝑟 𝑣 (map unbound φ)
  realize-eq 𝓋 𝑣 eq = elim (λ _ → isSet→isGroupoid isSetHProp _ _)
    λ φ → hPropExt $ Pre.realize-eq 𝓋 𝑣 eq φ []

module Closed where
  open ClosedRealizer 𝒮 using () renaming (realizeₜ to rₜ; realize to r) public
  open Free.Realizer 𝒮 using () renaming (realizeₜ to 𝑟ₜ; realize to 𝑟) public

  realizeₜ-eq : ∀ (𝑣 : ℕ → Domain) (t : ClosedTerm) → rₜ t ≡ 𝑟ₜ 𝑣 (unboundₜ t)
  realizeₜ-eq 𝑣 t = Opened.realizeₜ-eq [] 𝑣 (λ ()) t

  realize-eq : ∀ (𝑣 : ℕ → Domain) (φ : ∥ Sentence ∥₂) → r φ ≡ₚ 𝑟 𝑣 (map unbound φ)
  realize-eq 𝑣 φ = Opened.realize-eq [] 𝑣 (λ ()) φ
