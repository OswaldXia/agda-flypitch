{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Lemmas.Lifting (ℒ : Language {u}) where
open import FOL.Base ℒ

open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty using (⊥-elim)
open import Function using (_$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; subst; refl; sym; trans)

↑[]0 : (t : Termₗ l) {n : ℕ} → t ↑[ n ] 0 ≡ t
↑[]0 (var k) {n} with k <? n
... | yes p = refl
... | no ¬p = cong var (+-identityʳ k)
↑[]0 (func f) = refl
↑[]0 (app t₁ t₂) = cong₂ app (↑[]0 t₁) (↑[]0 t₂)

↑0 : (t : Termₗ l) → t ↑ 0 ≡ t
↑0 t = ↑[]0 t

↑[]↑[] : (t : Termₗ l) (n₁ m₁ n₂ m₂ : ℕ) → m₁ ≤ m₂ → m₂ ≤ m₁ + n₁
  → (t ↑[ m₁ ] n₁) ↑[ m₂ ] n₂ ≡ t ↑[ m₁ ] (n₁ + n₂)
↑[]↑[] (var k) n₁ m₁ n₂ m₂ ≤₁ ≤₂ with k <? m₁
... | yes p with k <? m₂
... | yes _ = refl
... | no ¬q = ⊥-elim $ ¬q $ ≤-trans p ≤₁
↑[]↑[] (var k) n₁ m₁ n₂ m₂ ≤₁ ≤₂ | no ¬p with k + n₁ <? m₂
... | yes q = ⊥-elim $ ¬p $ +-cancelʳ-≤ n₁ (suc k) m₁ (≤-trans q ≤₂)
... | no  _ = cong var $ +-assoc k _ _
↑[]↑[] (func f)    n₁ m₁ n₂ m₂ ≤₁ ≤₂ = refl
↑[]↑[] (app t₁ t₂) n₁ m₁ n₂ m₂ ≤₁ ≤₂ = cong₂ app
  (↑[]↑[] t₁ n₁ m₁ n₂ m₂ ≤₁ ≤₂)
  (↑[]↑[] t₂ n₁ m₁ n₂ m₂ ≤₁ ≤₂)

↑↑[] : (t : Termₗ l) (n₁ n₂ m₂ : ℕ) → m₂ ≤ n₁
  → (t ↑ n₁) ↑[ m₂ ] n₂ ≡ t ↑ (n₁ + n₂)
↑↑[] t n₁ n₂ m₂ ≤ = ↑[]↑[] t n₁ 0 n₂ m₂ z≤n ≤

↑↑ : (t : Termₗ l) (n₁ n₂ : ℕ) → (t ↑ n₁) ↑ n₂ ≡ t ↑ (n₁ + n₂)
↑↑ t n₁ n₂ = ↑↑[] t n₁ n₂ 0 z≤n

↑↑˘ : (t : Termₗ l) (n₁ n₂ : ℕ) → (t ↑ n₁) ↑ n₂ ≡ t ↑ (n₂ + n₁)
↑↑˘ t n₁ n₂ = trans (↑↑ t n₁ n₂) (cong (t ↑_) (+-comm n₁ n₂))

↑[][≔] : (t : Termₗ l) (s : Term) (n₁ n₂ m : ℕ) → m ≤ n₂ → n₂ ≤ m + n₁
  → (t ↑[ m ] suc n₁) [ n₂ ≔ s ]ₜ ≡ t ↑[ m ] n₁
↑[][≔] (var k) s n₁ n₂ m ≤₁ ≤₂ with k <? m
... | yes k<m with <-cmp k n₂
... | tri< _      _    _ = refl
... | tri≈ 1+k≰k  refl _ = ⊥-elim $ 1+k≰k  (≤-trans k<m ≤₁)
... | tri> 1+k≰n₂ _    _ = ⊥-elim $ 1+k≰n₂ (≤-trans k<m ≤₁)
↑[][≔] (var k) s n₁ n₂ m ≤₁ ≤₂ | no k≮m with <-cmp (k + suc n₁) n₂
... | tri< p _    _ = ⊥-elim $ k≮m $ +-cancelʳ-≤ n₁ _ _ $ ≤-trans (≤-trans (s≤s $ +-monoʳ-≤ k (n≤1+n n₁)) p) ≤₂
... | tri≈ _ refl _ = ⊥-elim $ k≮m $ +-cancelʳ-≤ n₁ _ _ $ subst (_≤ m + n₁) (+-suc k n₁) ≤₂
... | tri> _ _    _ = cong var $ trans (+-∸-assoc k (s≤s z≤n)) (cong (k +_) (m+n∸m≡n 1 n₁))
↑[][≔] (func f)    s n₁ n₂ m ≤₁ ≤₂ = refl
↑[][≔] (app t₁ t₂) s n₁ n₂ m ≤₁ ≤₂ = cong₂ app (↑[][≔] t₁ s n₁ n₂ m ≤₁ ≤₂) (↑[][≔] t₂ s n₁ n₂ m ≤₁ ≤₂)

↑[≔] : (t : Termₗ l) (s : Term) (n₁ n₂ : ℕ) → (t ↑ (suc (n₁ + n₂))) [ n₁ ≔ s ]ₜ ≡ t ↑ (n₁ + n₂)
↑[≔] t s n₁ n₂ = ↑[][≔] t s (n₁ + n₂) n₁ 0 z≤n (m≤m+n n₁ n₂)

↑[]1[≔] : (t : Termₗ l) (s : Term) (n : ℕ) → (t ↑[ n ] 1) [ n ≔ s ]ₜ ≡ t
↑[]1[≔] t s n = trans (↑[][≔] t s 0 n n ≤-refl n≤n+0) (↑[]0 t) where
  n≤n+0 = subst (n ≤_) (sym $ (+-identityʳ n)) ≤-refl

↑1[≔] : (t : Termₗ l) (s : Term) → (t ↑ 1) [ 0 ≔ s ]ₜ ≡ t
↑1[≔] t s = ↑[]1[≔] t s 0

↥[]0 : (φ : Formulaₗ l) {n : ℕ} → (φ ↥[ n ] 0) ≡ φ
↥[]0 ⊥          = refl
↥[]0 (rel R)    = refl
↥[]0 (appᵣ φ t) = cong₂ appᵣ (↥[]0 φ) (↑[]0 t)
↥[]0 (t₁ ≈ t₂)  = cong₂ _≈_ (↑[]0 t₁) (↑[]0 t₂)
↥[]0 (φ₁ ⇒ φ₂)  = cong₂ _⇒_ (↥[]0 φ₁) (↥[]0 φ₂)
↥[]0 (∀' φ)     = cong ∀'_ (↥[]0 φ)

↥0 : (φ : Formulaₗ l) → (φ ↥ 0) ≡ φ
↥0 φ = ↥[]0 φ

↥[][≔] : (φ : Formulaₗ l) (s : Term) (n₁ n₂ m : ℕ) → m ≤ n₂ → n₂ ≤ m + n₁
  → (φ ↥[ m ] suc n₁) [ n₂ ≔ s ] ≡ φ ↥[ m ] n₁
↥[][≔] ⊥          s n₁ n₂ m ≤₁ ≤₂ = refl
↥[][≔] (rel R)    s n₁ n₂ m ≤₁ ≤₂ = refl
↥[][≔] (appᵣ φ t) s n₁ n₂ m ≤₁ ≤₂ = cong₂ appᵣ (↥[][≔] φ s n₁ n₂ m ≤₁ ≤₂) (↑[][≔] t s n₁ n₂ m ≤₁ ≤₂)
↥[][≔] (t₁ ≈ t₂)  s n₁ n₂ m ≤₁ ≤₂ = cong₂ _≈_ (↑[][≔] t₁ s n₁ n₂ m ≤₁ ≤₂) (↑[][≔] t₂ s n₁ n₂ m ≤₁ ≤₂)
↥[][≔] (φ₁ ⇒ φ₂)  s n₁ n₂ m ≤₁ ≤₂ = cong₂ _⇒_ (↥[][≔] φ₁ s n₁ n₂ m ≤₁ ≤₂) (↥[][≔] φ₂ s n₁ n₂ m ≤₁ ≤₂)
↥[][≔] (∀' φ)     s n₁ n₂ m ≤₁ ≤₂ = cong ∀'_ (↥[][≔] φ s n₁ (suc n₂) (suc m) (s≤s ≤₁) (s≤s ≤₂))

↥[≔] : (φ : Formulaₗ l) (s : Term) (n₁ n₂ : ℕ) → (φ ↥ (suc (n₁ + n₂))) [ n₁ ≔ s ] ≡ φ ↥ (n₁ + n₂)
↥[≔] φ s n₁ n₂ = ↥[][≔] φ s (n₁ + n₂) n₁ 0 z≤n (m≤m+n n₁ n₂)

↥[]1[≔] : (φ : Formulaₗ l) (s : Term) (n : ℕ) → (φ ↥[ n ] 1) [ n ≔ s ] ≡ φ
↥[]1[≔] φ s n = trans (↥[][≔] φ s 0 n n ≤-refl n≤n+0) (↥[]0 φ) where
  n≤n+0 = subst (n ≤_) (sym $ (+-identityʳ n)) ≤-refl

↥1[≔] : (φ : Formulaₗ l) (s : Term) → (φ ↥ 1) [ 0 ≔ s ] ≡ φ
↥1[≔] φ s = ↥[]1[≔] φ s 0

↑[≔]-cancel : (t : Termₗ l) (n : ℕ) → (t ↑[ suc n ] 1) [ n ≔ var 0 ]ₜ ≡ t
↑[≔]-cancel (var k) n with k <? suc n
... | yes k<1+n with <-cmp k n
... | tri< _ _ _    = refl
... | tri≈ _ refl _ = refl
... | tri> _ _ n<k  = ⊥-elim $ 1+n≰n $ ≤-trans k<1+n n<k
↑[≔]-cancel (var k) n | no k≮1+n with <-cmp (k + 1) n
... | tri< p _ _   = ⊥-elim $ k≮1+n $ s≤s $ ≤-trans (≤-trans (m≤m+n _ _) (n≤1+n _)) p
... | tri≈ ¬a refl ¬c = ⊥-elim $ k≮1+n $ s≤s $ m≤m+n _ _
... | tri> ¬a ¬b c = cong var (m+n∸n≡m k 1)
↑[≔]-cancel (func f)    n = refl
↑[≔]-cancel (app t₁ t₂) n = cong₂ app (↑[≔]-cancel t₁ n) (↑[≔]-cancel t₂ n)

↥[≔]-cancel : (φ : Formulaₗ l) (n : ℕ) → (φ ↥[ suc n ] 1) [ n ≔ var 0 ] ≡ φ
↥[≔]-cancel ⊥          n = refl
↥[≔]-cancel (rel R)    n = refl
↥[≔]-cancel (appᵣ φ t) n = cong₂ appᵣ (↥[≔]-cancel φ n) (↑[≔]-cancel t n)
↥[≔]-cancel (t₁ ≈ t₂)  n = cong₂ _≈_ (↑[≔]-cancel t₁ n) (↑[≔]-cancel t₂ n)
↥[≔]-cancel (φ₁ ⇒ φ₂)  n = cong₂ _⇒_ (↥[≔]-cancel φ₁ n) (↥[≔]-cancel φ₂ n)
↥[≔]-cancel (∀' φ)     n = cong ∀'_ (↥[≔]-cancel φ (suc n))
