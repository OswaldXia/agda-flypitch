{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Structure.Base using (Structure)
module FOL.Lemmas.Realization (𝒮 : Structure {u} ℒ) where

open import FOL.Base ℒ hiding (⊥-elim; subst; _+_)
open import FOL.Lemmas.Lifting ℒ
open import FOL.Lemmas.Substitution ℒ
open import FOL.Semantics ℒ
open Structure 𝒮

open import Data.Nat
open import Data.Empty using (⊥-elim)
open import Function using (_$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; cong; subst)
open import StdlibExt.Data.Vec using (Vec; []; _∷_; []-refl)
open import StdlibExt.Data.Nat.Properties

module Preₜ where
  open PreRealizer 𝒮 renaming (realizeₜ to rₜ; realize to r) public
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

  realize-cong : (𝓋 𝓊 : ℕ → Domain) (ext : ∀ n → 𝓋 n ≡ 𝓊 n)
    (φ : Formulaₗ l) (xs : Vec Domain l) → {!  r 𝓋 φ xs !}
    --→ r 𝓋 φ xs ≡ r 𝓊 φ xs
  realize-cong 𝓋 𝓊 ext φ xs = {!   !}
