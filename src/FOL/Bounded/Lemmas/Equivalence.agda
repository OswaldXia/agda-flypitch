{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Bounded.Base using (Theory)
module FOL.Bounded.Lemmas.Equivalence {ℒ : Language {u}} (T : Theory ℒ) where

open import FOL.Bounded.Base ℒ hiding (_⇒_)
open import CubicalExt.Foundations.Powerset* using (_⟦_⟧)
open import CubicalExt.HITs.SetTruncation using (map)
import FOL.Lemmas.Equivalence (map unbound ⟦ T ⟧) as Free

open import Agda.Primitive using (lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; map)
open import Function using (_$_)
open import Relation.Binary using (_⇒_; Rel; Reflexive; Symmetric; Transitive)
open import StdlibExt.Relation.Binary.PropositionalEquivalence u hiding (map)

private variable
  t t₁ t₂ : ClosedTerm
  f f₁ f₂ : ClosedTermₗ 1
  r r₁ r₂ : Sentenceₗ l

infix 4 _≋_

_≋_ : Rel ClosedTerm (lsuc u)
t₁ ≋ t₂ = T ⊢ t₁ ≈ t₂

≋-refl : Reflexive _≋_
≋-refl = Free.≋-refl

≋-sym : Symmetric _≋_
≋-sym = Free.≋-sym

≋-trans : Transitive _≋_
≋-trans = Free.≋-trans

≋-cong : t₁ ≋ t₂ → app f t₁ ≋ app f t₂
≋-cong t₁≋t₂ = Free.≋-cong t₁≋t₂

_≋ᶠ_ : Rel (ClosedTermₗ l) (lsuc u)
_≋ᶠ_ {l} f₁ f₂ = unboundₜ f₁ Free.≋ᶠ unboundₜ f₂

≋ᶠ-refl : Reflexive $ _≋ᶠ_ {l}
≋ᶠ-refl = Free.≋ᶠ-refl

≋ᶠ-sym : Symmetric $ _≋ᶠ_ {l}
≋ᶠ-sym = Free.≋ᶠ-sym

≋ᶠ-trans : Transitive $ _≋ᶠ_ {l}
≋ᶠ-trans = Free.≋ᶠ-trans

≋-funExt⁻ : f₁ ≋ᶠ f₂ → app f₁ t ≋ app f₂ t
≋-funExt⁻ = Free.≋-funExt⁻

≋-app : f₁ ≋ᶠ f₂ → t₁ ≋ t₂ → app f₁ t₁ ≋ app f₂ t₂
≋-app = Free.≋-app

≋ᶠ-app : {f₁ f₂ : ClosedTermₗ (suc l)} {t₁ t₂ : ClosedTerm}
  → f₁ ≋ᶠ f₂ → t₁ ≋ t₂ → app f₁ t₁ ≋ᶠ app f₂ t₂
≋ᶠ-app = Free.≋ᶠ-app

_⟷_ : Rel Sentence (lsuc u)
φ₁ ⟷ φ₂ = T ⊢ φ₁ ↔ T ⊢ φ₂

⟷-refl : Reflexive _⟷_
⟷-refl = Free.⟷-refl

⟷-sym : Symmetric _⟷_
⟷-sym = Free.⟷-sym

⟷-trans : Transitive _⟷_
⟷-trans = Free.⟷-trans

_⟺_ : Rel Sentence (lsuc u)
φ₁ ⟺ φ₂ = T ⊢ φ₁ ⇔ φ₂

⟺-refl : Reflexive _⟺_
⟺-refl = Free.⟺-refl

⟺-sym : Symmetric _⟺_
⟺-sym = Free.⟺-sym

⟺-trans : Transitive _⟺_
⟺-trans = Free.⟺-trans

⟺⇒⟷ : _⟺_ ⇒ _⟷_
⟺⇒⟷ = Free.⟺⇒⟷

⟺-cong : t₁ ≋ t₂ → appᵣ r t₁ ⟺ appᵣ r t₂
⟺-cong = Free.⟺-cong

⟷-cong : t₁ ≋ t₂ → appᵣ r t₁ ⟷ appᵣ r t₂
⟷-cong = Free.⟷-cong

_≋ʳ_ : Rel (Sentenceₗ l) (lsuc u)
_≋ʳ_ {l} r₁ r₂ = unbound r₁ Free.≋ʳ unbound r₂

≋ʳ-refl : Reflexive $ _≋ʳ_ {l}
≋ʳ-refl = Free.≋ʳ-refl

≋ʳ-sym : Symmetric $ _≋ʳ_ {l}
≋ʳ-sym = Free.≋ʳ-sym

≋ʳ-trans : Transitive $ _≋ʳ_ {l}
≋ʳ-trans = Free.≋ʳ-trans

⟺-relExt⁻ : r₁ ≋ʳ r₂ → appᵣ r₁ t ⟺ appᵣ r₂ t
⟺-relExt⁻ = Free.⟺-relExt⁻

⟺-appᵣ : r₁ ≋ʳ r₂ → t₁ ≋ t₂ → appᵣ r₁ t₁ ⟺ appᵣ r₂ t₂
⟺-appᵣ = Free.⟺-appᵣ

⟷-relExt⁻ : r₁ ≋ʳ r₂ → appᵣ r₁ t ⟷ appᵣ r₂ t
⟷-relExt⁻ = Free.⟷-relExt⁻

⟷-appᵣ : r₁ ≋ʳ r₂ → t₁ ≋ t₂ → appᵣ r₁ t₁ ⟷ appᵣ r₂ t₂
⟷-appᵣ = Free.⟷-appᵣ

≋ʳ-appᵣ : {r₁ r₂ : Sentenceₗ (suc l)} {t₁ t₂ : ClosedTerm}
  → r₁ ≋ʳ r₂ → t₁ ≋ t₂ → appᵣ r₁ t₁ ≋ʳ appᵣ r₂ t₂
≋ʳ-appᵣ = Free.≋ʳ-appᵣ
