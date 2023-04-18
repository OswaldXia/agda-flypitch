{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Bounded.Substitution (ℒ : Language {u}) where
import FOL.Base ℒ as Free
open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Casting ℒ
open import FOL.Bounded.Lifting ℒ

open import StdlibExt.Data.Fin
  using (Fin; toℕ; fromℕ<; reduce≥; toℕ-fromℕ<; toℕ-reduce≥)
open import StdlibExt.Data.Nat
  using (ℕ; suc; _+_; s≤s; z≤n; _≤_; ≤-trans; <-cmp; m+n≤n+m; m≤m+n)
open import Function using (_$_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂) renaming (subst to ≡-subst)

private variable
  m n : ℕ

substₜ : (n : ℕ) (t : Termₗ (suc n + m) l) (s : Term m) → Termₗ (n + m) l
substₜ {m} n (var k) s with <-cmp (toℕ k) n
... | tri< k<n _ _  = var $ fromℕ< $ ≤-trans k<n (m≤m+n _ _)
... | tri≈ _ _ _    = castₜ (m+n≤n+m m n) (s ↑ n)
... | tri> _ _ n<k  = var (reduce≥ k (≤-trans (s≤s z≤n) n<k))
substₜ _ (func f) s = func f
substₜ _ (app t₁ t₂) s = app (substₜ _ t₁ s) (substₜ _ t₂ s)

syntax substₜ n t s = t [ s / n ]ₜ

subst : (n : ℕ) (φ : Formulaₗ (suc n + m) l) (s : Term m) → Formulaₗ (n + m) l
subst _ ⊥ s = ⊥
subst _ (rel R) s = rel R
subst _ (appᵣ φ t) s = appᵣ (subst _ φ s) (substₜ _ t s)
subst _ (t₁ ≈ t₂) s = substₜ _ t₁ s ≈ substₜ _ t₂ s
subst _ (φ₁ ⇒ φ₂) s = subst _ φ₁ s ⇒ subst _ φ₂ s
subst _ (∀' φ) s = ∀' subst _ φ s

syntax subst n φ s = φ [ s / n ]

-- currently not used
unbound-substₜ : (t : Termₗ (suc n + m) l) (s : Term m) →
  unboundₜ (t [ s / n ]ₜ) ≡ unboundₜ t Free.[ unboundₜ s / n ]ₜ
unbound-substₜ {n} {m} (var k) s with <-cmp (toℕ k) n
... | tri< k<n _ _  = cong Free.var (toℕ-fromℕ< _)
... | tri≈ _ k≡n _  = trans (unbound-castₜ (m+n≤n+m m n) _) (unbound↑ s n)
... | tri> _ _ n<k  = cong Free.var (toℕ-reduce≥ k (≤-trans (s≤s z≤n) n<k))
unbound-substₜ (func f) s    = refl
unbound-substₜ (app t₁ t₂) s = cong₂ Free.app (unbound-substₜ t₁ s) (unbound-substₜ t₂ s)

-- currently not used
unbound-subst : (φ : Formulaₗ (suc n + m) l) (s : Term m) →
  unbound (φ [ s / n ]) ≡ unbound φ Free.[ unboundₜ s / n ]
unbound-subst ⊥ s           = refl
unbound-subst (rel R) s     = refl
unbound-subst (appᵣ r t) s  = cong₂ Free.appᵣ (unbound-subst r s) (unbound-substₜ t s)
unbound-subst (t₁ ≈ t₂) s   = cong₂ Free._≈_ (unbound-substₜ t₁ s) (unbound-substₜ t₂ s)
unbound-subst (φ₁ ⇒ φ₂) s   = cong₂ Free._⇒_ (unbound-subst φ₁ s) (unbound-subst φ₂ s)
unbound-subst (∀' φ) s      = cong Free.∀'_ (unbound-subst φ s)
