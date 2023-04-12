{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Structure.Base using (Structure)
module FOL.Lemmas.Realization (𝒮 : Structure {u} ℒ) where

open import FOL.Base ℒ hiding (⊥-elim; subst; _+_)
open import FOL.Lemmas.Lifting ℒ
open import FOL.Lemmas.Substitution ℒ
open import FOL.Semantics ℒ
open Structure 𝒮

open import Cubical.Core.Primitives renaming (_≡_ to _≡ₚ_)
open import Cubical.Data.Equality using (pathToEq)
open import Cubical.Functions.Logic using (⇒∶_⇐∶_)
open import Cubical.HITs.SetTruncation using (∣_∣₂)

open import Data.Nat
open import Data.Empty using (⊥-elim)
open import Function using (_$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; cong; subst)
open import StdlibExt.Data.Vec using (Vec; []; _∷_; []-refl)
open import StdlibExt.Data.Nat.Properties
open import StdlibExt.Relation.Binary.PropositionalEquivalence as Iff hiding (sym)

module Preₜ where
  open PreRealizer 𝒮 renaming (realizeₜ to rₜ; realizeType to r) public
  open Eq.≡-Reasoning

  realizeₜ-cong : (𝓋 𝓊 : ℕ → Domain) (ext : ∀ n → 𝓋 n ≡ 𝓊 n)
    (t : Termₗ l) (xs : Vec Domain l)
    → rₜ 𝓋 t xs ≡ rₜ 𝓊 t xs
  realizeₜ-cong 𝓋 𝓊 ext (var k)     xs = ext k
  realizeₜ-cong 𝓋 𝓊 ext (func f)    xs = refl
  realizeₜ-cong 𝓋 𝓊 ext (app t₁ t₂) xs
    rewrite realizeₜ-cong 𝓋 𝓊 ext t₂ []
    rewrite realizeₜ-cong 𝓋 𝓊 ext t₁ (rₜ 𝓊 t₂ [] ∷ xs) = refl

  realizeₜ-subst : (𝓋 : ℕ → Domain) (n : ℕ) (t : Termₗ l)
    (s : Term) (xs : Vec Domain l)
    → rₜ (𝓋 [ rₜ 𝓋 (s ↑ n) [] / n ]ᵥ) t xs ≡ rₜ 𝓋 (t [ s / n ]ₜ) xs
  realizeₜ-subst 𝓋 n (var k) s xs with <-cmp k n
  ... | tri< _ _ _ = refl
  ... | tri> _ _ _ = refl
  ... | tri≈ _ _ _ = cong (rₜ 𝓋 (s ↑[ 0 ] n)) ([]-refl xs)
  realizeₜ-subst 𝓋 n (func f) s xs = refl
  realizeₜ-subst 𝓋 n (app t₁ t₂) s xs =
    let 𝓋' = 𝓋 [ rₜ 𝓋 (s ↑ n) [] / n ]ᵥ in              begin
    rₜ 𝓋' t₁             (rₜ 𝓋' t₂ [] ∷ xs)             ≡⟨ cong (rₜ 𝓋' t₁) $ cong (_∷ xs) (realizeₜ-subst 𝓋 n t₂ s []) ⟩
    rₜ 𝓋' t₁             (rₜ 𝓋 (t₂ [ s / n ]ₜ) [] ∷ xs) ≡⟨ realizeₜ-subst 𝓋 n t₁ s _ ⟩
    rₜ 𝓋 (t₁ [ s / n ]ₜ) (rₜ 𝓋 (t₂ [ s / n ]ₜ) [] ∷ xs) ∎

  realizeₜ-subst-lift : (𝓋 : ℕ → Domain) (n : ℕ) (t : Termₗ l)
    (x : Domain) (xs : Vec Domain l)
    → rₜ (𝓋 [ x / n ]ᵥ) (t ↑[ n ] 1) xs ≡ rₜ 𝓋 t xs
  realizeₜ-subst-lift 𝓋 n (var k) x xs with <-cmp k n | k <? n
  ... | tri≈ ¬p _ _ | yes p = ⊥-elim $ ¬p p
  ... | tri> ¬p _ _ | yes p = ⊥-elim $ ¬p p
  ... | tri< p ¬q _ | yes _ with <-cmp k n
  ... | tri≈ _ q _  = ⊥-elim $ ¬q q
  ... | tri> ¬p _ _ = ⊥-elim $ ¬p p
  ... | tri< _ _ _  = refl
  realizeₜ-subst-lift 𝓋 n (var k) x xs | _ | no ¬p with <-cmp (k + 1) n
  ... | tri< q _ _    = ⊥-elim $ ¬p (<-trans n<n+1 q)
  ... | tri≈ _ refl _ = ⊥-elim $ ¬p (subst (_≤ k + 1) (+-comm k 1) ≤-refl)
  ... | tri> _ _ _    = cong 𝓋 (m+n∸n≡m k 1)
  realizeₜ-subst-lift 𝓋 n (func f) x xs = refl
  realizeₜ-subst-lift 𝓋 n (app t₁ t₂) x xs =
    let 𝓋' = 𝓋 [ x / n ]ᵥ in                          begin
    rₜ 𝓋' (t₁ ↑[ n ] 1) (rₜ 𝓋' (t₂ ↑[ n ] 1) [] ∷ xs) ≡⟨ realizeₜ-subst-lift 𝓋 n t₁ x _ ⟩
    rₜ 𝓋 t₁             (rₜ 𝓋' (t₂ ↑[ n ] 1) [] ∷ xs) ≡⟨ cong (rₜ 𝓋 t₁) $ cong (_∷ xs) (realizeₜ-subst-lift 𝓋 n t₂ x []) ⟩
    rₜ 𝓋 t₁             (rₜ 𝓋 t₂ [] ∷ xs)             ∎

module Pre where
  open Preₜ public
  open Iff.↔-Reasoning

  realize-cong : (𝓋 𝓊 : ℕ → Domain) (ext : ∀ n → 𝓋 n ≡ 𝓊 n)
    (φ : Formulaₗ l) (xs : Vec Domain l)
    → r 𝓋 φ xs ↔ r 𝓊 φ xs
  realize-cong 𝓋 𝓊 ext ⊥           xs = id
  realize-cong 𝓋 𝓊 ext (rel R)     xs = id
  realize-cong 𝓋 𝓊 ext (appᵣ φ t)  xs
    rewrite realizeₜ-cong 𝓋 𝓊 ext t [] = realize-cong 𝓋 𝓊 ext φ _
  realize-cong 𝓋 𝓊 ext (t₁ ≈ t₂) xs
    rewrite realizeₜ-cong 𝓋 𝓊 ext t₁ xs
          | realizeₜ-cong 𝓋 𝓊 ext t₂ xs = id
  realize-cong 𝓋 𝓊 ext (φ₁ ⇒ φ₂) xs =
    →↔→ (realize-cong 𝓋 𝓊 ext φ₁ xs) (realize-cong 𝓋 𝓊 ext φ₂ xs)
  realize-cong 𝓋 𝓊 ext (∀' φ) xs = Π↔Π $ λ x
    → realize-cong (𝓋 [ x / 0 ]ᵥ) (𝓊 [ x / 0 ]ᵥ) (/ᵥ-cong ext x 0) φ xs

  realize-subst : (𝓋 : ℕ → Domain) (n : ℕ) (φ : Formulaₗ l)
    (s : Term) (xs : Vec Domain l)
    → r (𝓋 [ rₜ 𝓋 (s ↑ n) [] / n ]ᵥ) φ xs ↔ r 𝓋 (φ [ s / n ]) xs
  realize-subst 𝓋 n ⊥          s xs = id
  realize-subst 𝓋 n (rel R₁)   s xs = id
  realize-subst 𝓋 n (appᵣ φ t) s xs
    rewrite realizeₜ-subst 𝓋 n t s [] = realize-subst 𝓋 n φ s _
  realize-subst 𝓋 n (t₁ ≈ t₂) s xs
    rewrite realizeₜ-subst 𝓋 n t₁ s xs
          | realizeₜ-subst 𝓋 n t₂ s xs = id
  realize-subst 𝓋 n (φ₁ ⇒ φ₂) s xs =
    →↔→ (realize-subst 𝓋 n φ₁ s xs) (realize-subst 𝓋 n φ₂ s xs)
  realize-subst 𝓋 n (∀' φ) s xs = Π↔Π $ λ x →
    let t₁ = rₜ (𝓋 [ x / 0 ]ᵥ) (s ↑ suc n)   []
        t₂ = rₜ (𝓋 [ x / 0 ]ᵥ) ((s ↑ n) ↑ 1) []
        𝓋₁ = 𝓋 [ t₁ / n ]ᵥ [ x / 0 ]ᵥ
        𝓋₂ = 𝓋 [ t₂ / n ]ᵥ [ x / 0 ]ᵥ
        t≡ : t₂ ≡ t₁
        t≡ = cong (λ t → rₜ (𝓋 [ x / 0 ]ᵥ) t []) (↑↑˘ s n 1)
        𝓋≡₁ : ∀ m → 𝓋₂ m ≡ 𝓋₁ m
        𝓋≡₁ m = cong (λ t → (𝓋 [ t / n ]ᵥ [ x / 0 ]ᵥ) m) t≡
        𝓋₃ = 𝓋 [ rₜ 𝓋 (s ↑ n) [] / n ]ᵥ [ x / 0 ]ᵥ
        𝓋≡₂ : ∀ m → 𝓋₃ m ≡ 𝓋₂ m
        𝓋≡₂ m = sym $ cong (λ t → (𝓋 [ t / n ]ᵥ [ x / 0 ]ᵥ) m) (realizeₜ-subst-lift 𝓋 0 (s ↑ n) x [])
    in begin
    r 𝓋₃ φ xs                             ≈⟨ realize-cong _ _ 𝓋≡₂ φ xs ⟩
    r 𝓋₂ φ xs                             ≈⟨ realize-cong _ _ 𝓋≡₁ φ xs ⟩
    r 𝓋₁ φ xs                             ≈⟨ realize-cong _ _ (//ᵥ 𝓋 x t₁ 0 n) φ xs ⟩
    r (𝓋 [ x / 0 ]ᵥ [ t₁ / suc n ]ᵥ) φ xs ≈⟨ realize-subst (𝓋 [ x / 0 ]ᵥ) (suc n) φ s xs ⟩
    r (𝓋 [ x / 0 ]ᵥ) (φ [ s / suc n ]) xs ∎

  realize-subst-lift : (𝓋 : ℕ → Domain) (n : ℕ)
    (φ : Formulaₗ l) (x : Domain) (xs : Vec Domain l)
    → r (𝓋 [ x / n ]ᵥ) (φ ↥[ n ] 1) xs ↔ r 𝓋 φ xs
  realize-subst-lift 𝓋 n ⊥ x xs        = id
  realize-subst-lift 𝓋 n (rel R₁) x xs = id
  realize-subst-lift 𝓋 n (appᵣ φ t) x xs
    rewrite realizeₜ-subst-lift 𝓋 n t x [] = realize-subst-lift 𝓋 n φ x _
  realize-subst-lift 𝓋 n (t₁ ≈ t₂) x xs
    rewrite realizeₜ-subst-lift 𝓋 n t₁ x xs
          | realizeₜ-subst-lift 𝓋 n t₂ x xs = id
  realize-subst-lift 𝓋 n (φ₁ ⇒ φ₂) x xs =
    →↔→ (realize-subst-lift 𝓋 n φ₁ x xs) (realize-subst-lift 𝓋 n φ₂ x xs)
  realize-subst-lift 𝓋 n (∀' φ) x xs = Π↔Π $ λ y →   begin
    r (𝓋 [ x / n ]ᵥ [ y / 0 ]ᵥ)     (φ ↥[ suc n ] 1) xs ≈⟨ realize-cong _ _ (//ᵥ 𝓋 y x 0 n) (φ ↥[ suc n ] 1) xs ⟩
    r (𝓋 [ y / 0 ]ᵥ [ x / suc n ]ᵥ) (φ ↥[ suc n ] 1) xs ≈⟨ realize-subst-lift (𝓋 [ y / 0 ]ᵥ) (suc n) φ x xs ⟩
    r (𝓋 [ y / 0 ]ᵥ) φ xs                               ∎

open Realizer 𝒮

realizeₜ-cong : (𝓋 𝓊 : ℕ → Domain) (ext : ∀ n → 𝓋 n ≡ 𝓊 n) (t : Term)
  → realizeₜ 𝓋 t ≡ realizeₜ 𝓊 t
realizeₜ-cong 𝓋 𝓊 ext t = Pre.realizeₜ-cong 𝓋 𝓊 ext t []

realizeₜ-subst : (𝓋 : ℕ → Domain) (n : ℕ) (t : Term) (s : Term)
  → realizeₜ (𝓋 [ realizeₜ 𝓋 (s ↑ n) / n ]ᵥ) t ≡ realizeₜ 𝓋 (t [ s / n ]ₜ)
realizeₜ-subst 𝓋 n t s = Pre.realizeₜ-subst 𝓋 n t s []

realizeₜ-subst-lift : (𝓋 : ℕ → Domain) (n : ℕ) (t : Term) (x : Domain)
  → realizeₜ (𝓋 [ x / n ]ᵥ) (t ↑[ n ] 1) ≡ realizeₜ 𝓋 t
realizeₜ-subst-lift 𝓋 n t x = Pre.realizeₜ-subst-lift 𝓋 n t x []

realize-cong : (𝓋 𝓊 : ℕ → Domain) (ext : ∀ n → 𝓋 n ≡ 𝓊 n) (φ : Formula)
  → realize 𝓋 ∣ φ ∣₂ ≡ realize 𝓊 ∣ φ ∣₂
realize-cong 𝓋 𝓊 ext φ = pathToEq $
  ⇒∶ to   (Pre.realize-cong 𝓋 𝓊 ext φ []) ⟨$⟩_
  ⇐∶ from (Pre.realize-cong 𝓋 𝓊 ext φ []) ⟨$⟩_
