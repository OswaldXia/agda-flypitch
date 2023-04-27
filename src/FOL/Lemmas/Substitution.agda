{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Lemmas.Substitution (ℒ : Language {u}) where
open import FOL.Base ℒ

open import Cubical.Foundations.Prelude using (Type; Level)
open import Data.Empty using (⊥-elim)
open import Data.Vec using (Vec; []; _∷_; map)
open import Function using (_$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans) renaming (subst to ≡-subst)
open import StdlibExt.Data.Nat

private variable
  ℓ : Level
  A : Type ℓ

[≔]ᵥ-cong : {𝓋 𝓊 : ℕ → A} (ext : ∀ n → 𝓋 n ≡ 𝓊 n) (s : A) (n k : ℕ)
  → (𝓋 [ n ≔ s ]ᵥ) k ≡ (𝓊 [ n ≔ s ]ᵥ) k
[≔]ᵥ-cong ext s n k with <-cmp k n
... | tri< _ _ _ = ext k
... | tri≈ _ _ _ = refl
... | tri> _ _ _ = ext (k ∸ 1)

[≔][≔]ᵥ : (𝓋 : ℕ → A) (s₁ s₂ : A) (n₁ n₂ k : ℕ)
  → (𝓋 [ n₁ + n₂ ≔ s₂ ]ᵥ [ n₁ ≔ s₁ ]ᵥ) k ≡ (𝓋 [ n₁ ≔ s₁ ]ᵥ [ suc (n₁ + n₂) ≔ s₂ ]ᵥ) k
[≔][≔]ᵥ 𝓋 s₁ s₂ n₁ n₂ k with <-cmp k n₁ | <-cmp k (suc (n₁ + n₂))
... | tri< _ _ ¬p   | tri≈ _ refl _ = ⊥-elim $ ¬p $ s≤s (m≤m+n _ _)
... | tri≈ _ refl _ | tri≈ ¬p _ _   = ⊥-elim $ ¬p $ s≤s (m≤m+n _ _)
... | tri≈ _ refl _ | tri> ¬p _ _   = ⊥-elim $ ¬p $ s≤s (m≤m+n _ _)
... | tri< p _ _    | tri> ¬q _ _   = ⊥-elim $ ¬q $ <-trans p (s≤s (m≤m+n _ _))
[≔][≔]ᵥ 𝓋 s₁ s₂ n₁ n₂ k | tri≈ _ refl _ | tri< _ _ _ with <-cmp k n₁
... | tri≈ _ _ _  = refl
... | tri< _ ¬p _ = ⊥-elim $ ¬p refl
... | tri> _ ¬p _ = ⊥-elim $ ¬p refl
[≔][≔]ᵥ 𝓋 s₁ s₂ n₁ n₂ k | tri> _ _ _    | tri≈ _ refl _ with <-cmp (k ∸ 1) (n₁ + n₂)
... | tri≈ _ _ _  = refl
... | tri< _ ¬p _ = ⊥-elim $ ¬p $ refl
... | tri> _ ¬p _ = ⊥-elim $ ¬p $ refl
[≔][≔]ᵥ 𝓋 s₁ s₂ n₁ n₂ k | tri< p ¬q _   | tri< _ _ _ with <-cmp k n₁ | <-cmp k (n₁ + n₂)
... | tri< _ _ _    | tri< _ _ _    = refl
... | tri≈ _ refl _ | _             = ⊥-elim $ ¬q $ refl
... | tri> ¬p _ _   | _             = ⊥-elim $ ¬p p
... | _             | tri≈ ¬q _ _   = ⊥-elim $ ¬q $ ≤-trans p (m≤m+n _ _)
... | _             | tri> ¬q _ _   = ⊥-elim $ ¬q $ ≤-trans p (m≤m+n _ _)
[≔][≔]ᵥ 𝓋 s₁ s₂ n₁ n₂ k | tri> _ ¬p q   | tri< r _ _ with <-cmp k n₁ | <-cmp (k ∸ 1) (n₁ + n₂)
... | tri> _ _ _    | tri< _ _ _    = refl
... | tri< _ _ ¬q   | _             = ⊥-elim $ ¬q q
... | tri≈ _ refl _ | _             = ⊥-elim $ ¬p $ refl
... | _             | tri≈ ¬s _ _   = ⊥-elim $ ¬s $ ≡-subst (_≤ _) (n≡1+n∸1 q) (≤-pred r)
... | _             | tri> ¬s _ _   = ⊥-elim $ ¬s $ ≡-subst (_≤ _) (n≡1+n∸1 q) (≤-pred r)
[≔][≔]ᵥ 𝓋 s₁ s₂ n₁ n₂ k | tri> _ _ p    | tri> ¬q ¬r _ with <-cmp (k ∸ 1) (n₁ + n₂) | <-cmp (k ∸ 1) n₁
... | tri> _ _ _    | tri> _ _ _    = refl
... | tri> _ _ s    | tri< _ _ ¬t   = ⊥-elim $ ¬t $ ≤-trans (s≤s $ m≤m+n _ _) s
... | tri< s _ _    | _             = ⊥-elim $ ¬q $ s≤s (≡-subst (_≤ _) (sym $ n≡1+n∸1 p) s)
... | tri≈ _ s _    | _             rewrite sym s = ⊥-elim $ ¬r $ n≡1+n∸1 p
... | tri> ¬s ¬t _  | tri≈ _ u _    with n₂
... | zero   rewrite +-identityʳ n₁ = ⊥-elim $ ¬t $ u
... | suc n₂ rewrite u              = ⊥-elim $ ¬s (m<m+n n₁ (s≤s z≤n))

apps[≔] : (f : Termₗ l) (xs : Vec Term l) (s : Term) (n : ℕ)
  → apps f xs [ n ≔ s ]ₜ ≡ apps (f [ n ≔ s ]ₜ) (map _[ n ≔ s ]ₜ xs)
apps[≔] f [] s n = refl
apps[≔] f (x ∷ xs) s n = apps[≔] (app f x) xs s n

appsᵣ[≔] : (r : Formulaₗ l) (xs : Vec Term l) (s : Term) (n : ℕ)
  → appsᵣ r xs [ n ≔ s ] ≡ appsᵣ (r [ n ≔ s ]) (map _[ n ≔ s ]ₜ xs)
appsᵣ[≔] r [] s n = refl
appsᵣ[≔] r (x ∷ xs) s n = appsᵣ[≔] (appᵣ r x) xs s n
