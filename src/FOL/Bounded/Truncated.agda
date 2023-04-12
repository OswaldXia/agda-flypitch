{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Bounded.Truncated (ℒ : Language {u}) where
open import FOL.Bounded.Base ℒ as Untruncated using (l; Theory) public
open Language ℒ

open import Cubical.Core.Primitives using (Type; ℓ-suc; _,_)
open import Cubical.Foundations.HLevels using (hProp; isSetHProp)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; squash₁)
open import CubicalExt.HITs.SetTruncation using (∥_∥₂; ∣_∣₂; map; map2; elim)

open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec)

Termₗ : ℕ → ℕ → Type u
Termₗ n l = ∥ Untruncated.Termₗ n l ∥₂

Term : ℕ → Type u
Term n = Termₗ n 0

ClosedTermₗ : ℕ → Type u
ClosedTermₗ l = Termₗ 0 l

ClosedTerm : Type u
ClosedTerm = ClosedTermₗ 0

Formulaₗ : ℕ → ℕ → Type u
Formulaₗ n l = ∥ Untruncated.Formulaₗ n l ∥₂

Formula : ℕ → Type u
Formula n = Formulaₗ n 0

Sentenceₗ : ℕ → Type u
Sentenceₗ l = Formulaₗ 0 l

Sentence : Type u
Sentence = Sentenceₗ 0

_⊢_ : Theory → Untruncated.Sentence → hProp (ℓ-suc u)
Γ ⊢ φ = ∥ Γ Untruncated.⊢ φ ∥₁ , squash₁

private variable
  n : ℕ

⊥ : Formula n
⊥ = ∣ Untruncated.⊥ ∣₂

rel : relations l → Formulaₗ n l
rel R = ∣ Untruncated.rel R ∣₂

appᵣ : Formulaₗ n (suc l) → Untruncated.Term n → Formulaₗ n l
appᵣ φ t = map (λ φ → Untruncated.appᵣ φ t) φ

appsᵣ : Formulaₗ n l → Vec (Untruncated.Term n) l → Formula n
appsᵣ φ ts = map (λ φ → Untruncated.appsᵣ φ ts) φ

_≈_ : Untruncated.Term n → Untruncated.Term n → Formula n
t₁ ≈ t₂ = ∣ t₁ Untruncated.≈ t₂ ∣₂

_⇒_ : Formula n → Formula n → Formula n
φ₁ ⇒ φ₂ = map2 Untruncated._⇒_ φ₁ φ₂

∀'_ : Formula (suc n) → Formula n
∀' φ = map Untruncated.∀'_ φ

infix 100 ~_
infix 9 _≈_
infix 8 _⇔_
infix 7 _⇒_
infixr 6 _∧_
infixr 5 _∨_

~_ : Formula n → Formula n
~ φ = φ ⇒ ⊥

⊤ : Formula n
⊤ = ~ ⊥

_∧_ : Formula n → Formula n → Formula n
φ₁ ∧ φ₂ = ~ (φ₁ ⇒ ~ φ₂)

_∨_ : Formula n → Formula n → Formula n
φ₁ ∨ φ₂ = ~ φ₁ ⇒ φ₂

_⇔_ : Formula n → Formula n → Formula n
φ₁ ⇔ φ₂ = φ₁ ⇒ φ₂ ∧ φ₂ ⇒ φ₁

∃'_ : Formula (suc n) → Formula n
∃' φ = ~ (∀' ~ φ)
