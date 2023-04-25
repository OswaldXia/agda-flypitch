{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Lemmas.Sethood (ℒ : Language {u}) where
open import FOL.Base ℒ
open Language ℒ

open import Agda.Builtin.Equality using (_≡_; refl)
open import Cubical.Foundations.Prelude using (isSet)
open import CubicalExt.Relation.Nullary using (yes; no; DiscreteEq; DiscreteEq→isSet)
open import Cubical.Data.Nat using (ℕ; zero; suc)

discreteTerm : DiscreteEq (Termₗ l)
discreteTerm (var zero)     (var zero)      = yes refl
discreteTerm (var zero)     (var (suc _))   = no λ ()
discreteTerm (var (suc _))  (var zero)      = no λ ()
discreteTerm (func _)       (app _ _)       = no λ ()
discreteTerm (app _ _)      (var _)         = no λ ()
discreteTerm (app _ _)      (func _)        = no λ ()
discreteTerm (var _)        (func _)        = no λ ()
discreteTerm (var _)        (app _ _)       = no λ ()
discreteTerm (func _)       (var _)         = no λ ()

discreteTerm (var (suc k₁)) (var (suc k₂)) with discreteTerm (var k₁) (var k₂)
... | yes refl = yes refl
... | no  ¬p   = no λ { refl → ¬p refl }

discreteTerm (func f₁) (func f₂) with discrete𝔉 f₁ f₂
... | yes refl = yes refl
... | no  ¬p   = no λ { refl → ¬p refl }

discreteTerm (app f₁ t₁) (app f₂ t₂) with discreteTerm f₁ f₂ | discreteTerm t₁ t₂
... | yes refl | yes refl = yes refl
... | no  ¬p   | _        = no λ { refl → ¬p refl }
... | _        | no  ¬q   = no λ { refl → ¬q refl }

isSetTerm : isSet (Termₗ l)
isSetTerm = DiscreteEq→isSet discreteTerm

discreteFormula : DiscreteEq (Formulaₗ l)
discreteFormula ⊥           ⊥           = yes refl
discreteFormula ⊥           (rel _)     = no λ ()
discreteFormula ⊥           (appᵣ _ _)  = no λ ()
discreteFormula ⊥           (_ ≈ _)     = no λ ()
discreteFormula ⊥           (_ ⇒ _)     = no λ ()
discreteFormula ⊥           (∀' _)      = no λ ()
discreteFormula (rel _)     ⊥           = no λ ()
discreteFormula (rel _)     (appᵣ _ _)  = no λ ()
discreteFormula (rel _)     (_ ≈ _)     = no λ ()
discreteFormula (rel _)     (_ ⇒ _)     = no λ ()
discreteFormula (rel _)     (∀' _)      = no λ ()
discreteFormula (appᵣ _ _)  ⊥           = no λ ()
discreteFormula (appᵣ _ _)  (rel _)     = no λ ()
discreteFormula (appᵣ _ _)  (_ ≈ _)     = no λ ()
discreteFormula (appᵣ _ _)  (_ ⇒ _)     = no λ ()
discreteFormula (appᵣ _ _)  (∀' _)      = no λ ()
discreteFormula (_ ≈ _)     ⊥           = no λ ()
discreteFormula (_ ≈ _)     (rel _)     = no λ ()
discreteFormula (_ ≈ _)     (appᵣ _ _)  = no λ ()
discreteFormula (_ ≈ _)     (_ ⇒ _)     = no λ ()
discreteFormula (_ ≈ _)     (∀' _)      = no λ ()
discreteFormula (_ ⇒ _)     ⊥           = no λ ()
discreteFormula (_ ⇒ _)     (rel _)     = no λ ()
discreteFormula (_ ⇒ _)     (appᵣ _ _)  = no λ ()
discreteFormula (_ ⇒ _)     (_ ≈ _)     = no λ ()
discreteFormula (_ ⇒ _)     (∀' _)      = no λ ()
discreteFormula (∀' _)      ⊥           = no λ ()
discreteFormula (∀' _)      (rel _)     = no λ ()
discreteFormula (∀' _)      (appᵣ _ _)  = no λ ()
discreteFormula (∀' _)      (_ ≈ _)     = no λ ()
discreteFormula (∀' _)      (_ ⇒ _)     = no λ ()

discreteFormula (rel R₁) (rel R₂) with discreteℜ R₁ R₂
... | yes refl = yes refl
... | no  ¬p   = no λ { refl → ¬p refl }

discreteFormula (appᵣ r₁ t₁) (appᵣ r₂ t₂) with discreteFormula r₁ r₂ | discreteTerm t₁ t₂
... | yes refl | yes refl = yes refl
... | no  ¬p   | _        = no λ { refl → ¬p refl }
... | _        | no  ¬q   = no λ { refl → ¬q refl }

discreteFormula (t₁ ≈ s₁) (t₂ ≈ s₂) with discreteTerm t₁ t₂ | discreteTerm s₁ s₂
... | yes refl | yes refl = yes refl
... | no  ¬p   | _        = no λ { refl → ¬p refl }
... | _        | no  ¬q   = no λ { refl → ¬q refl }

discreteFormula (φ₁ ⇒ ψ₁) (φ₂ ⇒ ψ₂) with discreteFormula φ₁ φ₂ | discreteFormula ψ₁ ψ₂
... | yes refl | yes refl = yes refl
... | no  ¬p   | _        = no λ { refl → ¬p refl }
... | _        | no  ¬q   = no λ { refl → ¬q refl }

discreteFormula (∀' φ₁) (∀' φ₂) with discreteFormula φ₁ φ₂
... | yes refl = yes refl
... | no  ¬p   = no λ { refl → ¬p refl }

isSetFormula : isSet (Formulaₗ l)
isSetFormula = DiscreteEq→isSet discreteFormula
