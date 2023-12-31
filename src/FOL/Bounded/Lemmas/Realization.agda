{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Structure.Base using (Structure)
module FOL.Bounded.Lemmas.Realization {ℒ : Language {u}} {v} (𝒮 : Structure ℒ {v}) where

open import FOL.Base ℒ using (_[_≔_]ᵥ)
import FOL.Semantics ℒ as Free
open Structure 𝒮

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.Bounded.Manipulations.Lifting ℒ
open import FOL.Bounded.Manipulations.Substitution.Closed ℒ

open import Cubical.Data.Equality using (eqToPath)
open import CubicalExt.Functions.Logic.Iff

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties using (≤⇒≯; <-cmp)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import StdlibExt.Data.Vec
open import Function using (_$_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

private variable
  n : ℕ

module Pre where
  open PreRealizer 𝒮 using () renaming (realizeₜ to rₜ; realize to r) public
  open Free.PreRealizer 𝒮 using () renaming (realizeₜ to 𝑟ₜ; realize to 𝑟) public

  realizeₜ-eq : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (t : Termₗ n l) (xs : Vec Domain l)
    → rₜ 𝓋 t xs ≡ 𝑟ₜ 𝑣 (unboundₜ t) xs
  realizeₜ-eq 𝓋 𝑣 eq (var k)     xs = eq k
  realizeₜ-eq 𝓋 𝑣 eq (func f)    xs = refl
  realizeₜ-eq 𝓋 𝑣 eq (app t₁ t₂) xs
    rewrite realizeₜ-eq 𝓋 𝑣 eq t₂ [] = realizeₜ-eq 𝓋 𝑣 eq t₁ _

  realize-iff : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (φ : Formulaₗ n l) (xs : Vec Domain l)
    → r 𝓋 φ xs ↔ 𝑟 𝑣 (unbound φ) xs
  realize-iff 𝓋 𝑣 eq ⊥          xs = ↔-refl
  realize-iff 𝓋 𝑣 eq (rel R)    xs = ↔-refl
  realize-iff 𝓋 𝑣 eq (appᵣ φ t) xs
    rewrite realizeₜ-eq 𝓋 𝑣 eq t [] = realize-iff 𝓋 𝑣 eq φ _
  realize-iff 𝓋 𝑣 eq (t₁ ≈ t₂)  [] = ≡↔≡
    (eqToPath $ realizeₜ-eq 𝓋 𝑣 eq t₁ [])
    (eqToPath $ realizeₜ-eq 𝓋 𝑣 eq t₂ [])
  realize-iff 𝓋 𝑣 eq (φ₁ ⇒ φ₂)  xs = →↔→
    (realize-iff 𝓋 𝑣 eq φ₁ xs)
    (realize-iff 𝓋 𝑣 eq φ₂ xs)
  realize-iff 𝓋 𝑣 eq (∀' φ)     [] = Π↔Π $ λ x →
    realize-iff (x ∷ 𝓋) (𝑣 [ 0 ≔ x ]ᵥ) (eq' x) φ [] where
    eq' : ∀ x k → lookup (x ∷ 𝓋) k ≡ (𝑣 [ 0 ≔ x ]ᵥ) (toℕ k)
    eq' x zero    = refl
    eq' x (suc k) = eq k

  realizeₜ-lift-eq : (𝓋 : Vec Domain n) (t : ClosedTermₗ l) (xs : Vec Domain l) →
    rₜ 𝓋 (t ↑ n) xs ≡ rₜ [] t xs
  realizeₜ-lift-eq 𝓋 (func f) xs = refl
  realizeₜ-lift-eq 𝓋 (app t₁ t₂) xs
    rewrite realizeₜ-lift-eq 𝓋 t₂ [] = realizeₜ-lift-eq 𝓋 t₁ _

  realizeₜ-subst-eq : (𝓋 : Vec Domain n) (t : Termₗ (suc n) l) (s : ClosedTerm) (xs : Vec Domain l) →
    rₜ 𝓋 (t [≔ s ]ₜ) xs ≡ rₜ (𝓋 ∷ʳ rₜ [] s []) t xs
  realizeₜ-subst-eq {n} 𝓋 (var k) s [] with <-cmp (toℕ k) n
  ... | tri< k<n _ _ = sym $ lookup∷ʳ-< 𝓋 k k<n
  ... | tri≈ _ k≡n _ rewrite realizeₜ-lift-eq 𝓋 s [] = sym $ lookup∷ʳ-≡ 𝓋 k k≡n
  ... | tri> _ _ k>n = ⊥-elim $ ≤⇒≯ k>n $ toℕ<n k
  realizeₜ-subst-eq 𝓋 (func f)    s xs = refl
  realizeₜ-subst-eq 𝓋 (app t₁ t₂) s xs
    rewrite realizeₜ-subst-eq 𝓋 t₂ s []
          | realizeₜ-subst-eq 𝓋 t₁ s (rₜ (𝓋 ∷ʳ rₜ [] s []) t₂ [] ∷ xs) = refl

  realize-subst-iff : (𝓋 : Vec Domain n) (φ : Formulaₗ (suc n) l) (s : ClosedTerm) (xs : Vec Domain l) →
    r 𝓋 (φ [≔ s ]) xs ↔ r (𝓋 ∷ʳ rₜ [] s []) φ xs
  realize-subst-iff 𝓋 ⊥ s xs = ↔-refl
  realize-subst-iff 𝓋 (rel R) s xs = ↔-refl
  realize-subst-iff 𝓋 (appᵣ φ t) s xs
    rewrite realizeₜ-subst-eq 𝓋 t s [] = realize-subst-iff 𝓋 φ s _
  realize-subst-iff 𝓋 (t₁ ≈ t₂) s xs = ≡↔≡
    (eqToPath $ realizeₜ-subst-eq 𝓋 t₁ s xs)
    (eqToPath $ realizeₜ-subst-eq 𝓋 t₂ s xs)
  realize-subst-iff 𝓋 (φ₁ ⇒ φ₂) s xs = →↔→
    (realize-subst-iff 𝓋 φ₁ s xs)
    (realize-subst-iff 𝓋 φ₂ s xs)
  realize-subst-iff 𝓋 (∀' φ) s xs = Π↔Π λ x →
    realize-subst-iff (x ∷ 𝓋) φ s xs

  realize-appsᵣ-iff : (𝓋 : Vec Domain n) (φ : Formulaₗ n l) (xs : Vec (Term n) l) →
    r 𝓋 (appsᵣ φ xs) [] ↔ r 𝓋 φ (map (λ t → rₜ 𝓋 t []) xs)
  realize-appsᵣ-iff 𝓋 φ [] = ↔-refl
  realize-appsᵣ-iff 𝓋 φ (x ∷ xs) = realize-appsᵣ-iff 𝓋 (appᵣ φ x) xs

module Opened where
  open OpenedRealizer 𝒮 using () renaming (realizeₜ to rₜ; realize to r) public
  open Free.Realizer 𝒮 using () renaming (realizeₜ to 𝑟ₜ; realize to 𝑟) public

  realizeₜ-eq : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (t : Term n)
    → rₜ 𝓋 t ≡ 𝑟ₜ 𝑣 (unboundₜ t)
  realizeₜ-eq 𝓋 𝑣 eq t = Pre.realizeₜ-eq 𝓋 𝑣 eq t []

  realize-iff : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (φ : Formula n)
    → r 𝓋 φ ↔ 𝑟 𝑣 (unbound φ)
  realize-iff 𝓋 𝑣 eq φ = Pre.realize-iff 𝓋 𝑣 eq φ []

  realizeₜ-subst-eq : (𝓋 : Vec Domain n) (t : Term (suc n)) (s : ClosedTerm) →
    rₜ 𝓋 (t [≔ s ]ₜ) ≡ rₜ (𝓋 ∷ʳ rₜ [] s) t
  realizeₜ-subst-eq 𝓋 t s = Pre.realizeₜ-subst-eq 𝓋 t s []

  realize-subst-iff : (𝓋 : Vec Domain n) (φ : Formula (suc n)) (s : ClosedTerm) →
    r 𝓋 (φ [≔ s ]) ↔ r (𝓋 ∷ʳ rₜ [] s) φ
  realize-subst-iff 𝓋 φ s = Pre.realize-subst-iff 𝓋 φ s []

module Closed where
  open ClosedRealizer 𝒮 using () renaming (realizeₜ to rₜ; realize to r) public
  open Free.Realizer 𝒮 using () renaming (realizeₜ to 𝑟ₜ; realize to 𝑟) public

  realizeₜ-eq : ∀ (𝑣 : ℕ → Domain) (t : ClosedTerm) → rₜ t ≡ 𝑟ₜ 𝑣 (unboundₜ t)
  realizeₜ-eq 𝑣 t = Opened.realizeₜ-eq [] 𝑣 (λ ()) t

  realize-iff : ∀ (𝑣 : ℕ → Domain) (φ : Sentence) → r φ ↔ 𝑟 𝑣 (unbound φ)
  realize-iff 𝑣 φ = Opened.realize-iff [] 𝑣 (λ ()) φ
