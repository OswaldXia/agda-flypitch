{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import FOL.Bounded.Syntactics using (Theory)
module FOL.Constructions.Equivalence.BoundedTruncated {ℒ : Language {u}} (T : Theory ℒ) where

open import CubicalExt.Foundations.Powerset* using (_⟦_⟧)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁; elim; map; map2)
open import CubicalExt.StdlibBridge.Logic using (∥_∥ₚ; propTruncExt)
import Cubical.Relation.Binary as CubicalRel
open CubicalRel.BinaryRelation using (isPropValued; isEquivRel)

open import FOL.Bounded.Base ℒ hiding (_⇒_)
open import FOL.Bounded.Syntactics ℒ
import FOL.Constructions.Equivalence.Base (unbound ⟦ T ⟧) as Free

open import Cubical.Foundations.Prelude
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_; _$_)
open import Relation.Binary using (_⇒_; Rel; Reflexive; Symmetric; Transitive)

private variable
  t t₁ t₂ : ClosedTerm
  f f₁ f₂ : ClosedTermₗ 1
  r r₁ r₂ : Sentenceₗ l

infix 4 _≋_

_≋_ : Rel ClosedTerm (ℓ-suc u)
t₁ ≋ t₂ = ∥ unboundₜ t₁ Free.≋ unboundₜ t₂ ∥₁

≋-refl : Reflexive _≋_
≋-refl = ∣ Free.≋-refl ∣₁

≋-sym : Symmetric _≋_
≋-sym = map Free.≋-sym

≋-trans : Transitive _≋_
≋-trans = map2 Free.≋-trans

isPropValued≋ : isPropValued _≋_
isPropValued≋ _ _ = squash₁

isEquivRel≋ : isEquivRel _≋_
isEquivRel≋ = record
  { reflexive = λ _ → ≋-refl
  ; symmetric = λ _ _ → ≋-sym
  ; transitive = λ _ _ _ → ≋-trans
  }

≋-cong : t₁ ≋ t₂ → app f t₁ ≋ app f t₂
≋-cong = map Free.≋-cong

_≋ᶠ_ : Rel (ClosedTermₗ l) (ℓ-suc u)
_≋ᶠ_ f₁ f₂ = ∥ unboundₜ f₁ Free.≋ᶠ unboundₜ f₂ ∥₁

≋ᶠ-refl : Reflexive $ _≋ᶠ_ {l}
≋ᶠ-refl = ∣ Free.≋ᶠ-refl ∣₁

≋ᶠ-sym : Symmetric $ _≋ᶠ_ {l}
≋ᶠ-sym = map Free.≋ᶠ-sym

≋ᶠ-trans : Transitive $ _≋ᶠ_ {l}
≋ᶠ-trans = map2 Free.≋ᶠ-trans

≋-funExt⁻ : f₁ ≋ᶠ f₂ → app f₁ t ≋ app f₂ t
≋-funExt⁻ = map Free.≋-funExt⁻

≋-app : f₁ ≋ᶠ f₂ → t₁ ≋ t₂ → app f₁ t₁ ≋ app f₂ t₂
≋-app = map2 Free.≋-app

≋ᶠ-app : {f₁ f₂ : ClosedTermₗ (suc l)} {t₁ t₂ : ClosedTerm}
  → f₁ ≋ᶠ f₂ → t₁ ≋ t₂ → app f₁ t₁ ≋ᶠ app f₂ t₂
≋ᶠ-app = map2 Free.≋ᶠ-app

_⟷_ : Rel Sentence (ℓ-suc u)
φ₁ ⟷ φ₂ = ∥ unbound φ₁ Free.⟷ unbound φ₂ ∥₁

⟷-refl : Reflexive _⟷_
⟷-refl = ∣ Free.⟷-refl ∣₁

⟷-sym : Symmetric _⟷_
⟷-sym = map Free.⟷-sym

⟷-trans : Transitive _⟷_
⟷-trans = map2 Free.⟷-trans

_⟺_ : Rel Sentence (ℓ-suc u)
φ₁ ⟺ φ₂ = ∥ unbound φ₁ Free.⟺ unbound φ₂ ∥₁

⟺-refl : Reflexive _⟺_
⟺-refl = ∣ Free.⟺-refl ∣₁

⟺-sym : Symmetric _⟺_
⟺-sym = map Free.⟺-sym

⟺-trans : Transitive _⟺_
⟺-trans = map2 Free.⟺-trans

⟺⇒⟷ : _⟺_ ⇒ _⟷_
⟺⇒⟷ = map Free.⟺⇒⟷

⟺-cong : t₁ ≋ t₂ → appᵣ r t₁ ⟺ appᵣ r t₂
⟺-cong = map Free.⟺-cong

⟷-cong : t₁ ≋ t₂ → appᵣ r t₁ ⟷ appᵣ r t₂
⟷-cong = map Free.⟷-cong

_≋ʳ_ : Rel (Sentenceₗ l) (ℓ-suc u)
_≋ʳ_ {l} r₁ r₂ = ∥ unbound r₁ Free.≋ʳ unbound r₂ ∥₁

≋ʳ-refl : Reflexive $ _≋ʳ_ {l}
≋ʳ-refl = ∣ Free.≋ʳ-refl ∣₁

≋ʳ-sym : Symmetric $ _≋ʳ_ {l}
≋ʳ-sym = map Free.≋ʳ-sym

≋ʳ-trans : Transitive $ _≋ʳ_ {l}
≋ʳ-trans = map2 Free.≋ʳ-trans

⟺-relExt⁻ : r₁ ≋ʳ r₂ → appᵣ r₁ t ⟺ appᵣ r₂ t
⟺-relExt⁻ = map Free.⟺-relExt⁻

⟺-appᵣ : r₁ ≋ʳ r₂ → t₁ ≋ t₂ → appᵣ r₁ t₁ ⟺ appᵣ r₂ t₂
⟺-appᵣ = map2 Free.⟺-appᵣ

⟷-relExt⁻ : r₁ ≋ʳ r₂ → appᵣ r₁ t ⟷ appᵣ r₂ t
⟷-relExt⁻ = map Free.⟷-relExt⁻

⟷-appᵣ : r₁ ≋ʳ r₂ → t₁ ≋ t₂ → appᵣ r₁ t₁ ⟷ appᵣ r₂ t₂
⟷-appᵣ = map2 Free.⟷-appᵣ

≋ʳ-appᵣ : {r₁ r₂ : Sentenceₗ (suc l)} {t₁ t₂ : ClosedTerm}
  → r₁ ≋ʳ r₂ → t₁ ≋ t₂ → appᵣ r₁ t₁ ≋ʳ appᵣ r₂ t₂
≋ʳ-appᵣ = map2 Free.≋ʳ-appᵣ
