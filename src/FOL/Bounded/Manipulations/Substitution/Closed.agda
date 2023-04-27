{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Bounded.Manipulations.Substitution.Closed (ℒ : Language {u}) where
import FOL.Base ℒ as Free
open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Manipulations.Casting ℒ
open import FOL.Bounded.Manipulations.Lifting ℒ

open import StdlibExt.Data.Fin
  using (Fin; toℕ; fromℕ<; reduce≥; toℕ-fromℕ<; toℕ-reduce≥)
open import StdlibExt.Data.Nat
  using (ℕ; suc; _+_; _≤_; s≤s; z≤n; ≤-trans; <-cmp)
open import Function using (_$_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; cong₂)

private variable
  m n : ℕ

substₜ : Termₗ (suc n) l → ClosedTerm → Termₗ n l
substₜ {n} (var k) s with <-cmp (toℕ k) n
... | tri< k<n _ _  = var $ fromℕ< k<n
... | tri≈ _ _ _    = s ↑ n
... | tri> _ _ n<k  = var $ reduce≥ k $ ≤-trans (s≤s z≤n) n<k
substₜ (func f) s = func f
substₜ (app t₁ t₂) s = app (substₜ t₁ s) (substₜ t₂ s)

syntax substₜ t s = t [≔ s ]ₜ

subst : Formulaₗ (suc n) l → ClosedTerm → Formulaₗ n l
subst ⊥ s = ⊥
subst (rel R) s = rel R
subst (appᵣ φ t) s = appᵣ (subst φ s) (substₜ t s)
subst (t₁ ≈ t₂) s = substₜ t₁ s ≈ substₜ t₂ s
subst (φ₁ ⇒ φ₂) s = subst φ₁ s ⇒ subst φ₂ s
subst (∀' φ) s = ∀' subst φ s

syntax subst φ s = φ [≔ s ]

-- currently not used
unbound-substₜ : (t : Termₗ (suc n) l) (s : ClosedTerm) →
  unboundₜ (t [≔ s ]ₜ) ≡ unboundₜ t Free.[ n ≔ unboundₜ s ]ₜ
unbound-substₜ {n} {m} (var k) s with <-cmp (toℕ k) n
... | tri< k<n _ _  = cong Free.var $ toℕ-fromℕ< _
... | tri≈ _ k≡n _  = unbound↑ s n
... | tri> _ _ n<k  = cong Free.var $ toℕ-reduce≥ k (≤-trans (s≤s z≤n) n<k)
unbound-substₜ (func f) s    = refl
unbound-substₜ (app t₁ t₂) s = cong₂ Free.app (unbound-substₜ t₁ s) (unbound-substₜ t₂ s)

-- currently not used
unbound-subst : (φ : Formulaₗ (suc n) l) (s : ClosedTerm) →
  unbound (φ [≔ s ]) ≡ unbound φ Free.[ n ≔ unboundₜ s ]
unbound-subst ⊥ s           = refl
unbound-subst (rel R) s     = refl
unbound-subst (appᵣ r t) s  = cong₂ Free.appᵣ (unbound-subst r s) (unbound-substₜ t s)
unbound-subst (t₁ ≈ t₂) s   = cong₂ Free._≈_ (unbound-substₜ t₁ s) (unbound-substₜ t₂ s)
unbound-subst (φ₁ ⇒ φ₂) s   = cong₂ Free._⇒_ (unbound-subst φ₁ s) (unbound-subst φ₂ s)
unbound-subst (∀' φ) s      = cong Free.∀'_ (unbound-subst φ s)
