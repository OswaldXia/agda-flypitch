{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import FOL.Bounded.Syntactics using (Theory)
module FOL.Constructions.TermModel.Base {ℒ : Language {u}} (T : Theory ℒ) where
open import FOL.Structure.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.PropertiesOfTheory ℒ

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp; isSetHProp)
open import CubicalExt.Functions.Logic.Iff
open import CubicalExt.Data.Vec using (quotientLift)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁; rec)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (fromℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
open import Function using (_$_; _∘_; _∘₂_)

module TermModel where
  open import FOL.Bounded.Base ℒ hiding (func; rel)
  open import FOL.Constructions.Equivalence.BoundedTruncated T
  private
    _≋ₚ_ = Pointwise _≋_
    𝐯₀ = var (fromℕ 0)

  Domain = ClosedTerm / _≋_

  nonempty : hasEnoughConstants T → ∥ Domain ∥₁
  nonempty H = rec squash₁
    (λ { (c , _) → ∣ [ const c ] ∣₁ })
    (H (var (fromℕ 0) ≈ var (fromℕ 0)))

  preFunc : ClosedTermₗ l → Vec ClosedTerm l → Domain
  preFunc f xs = [ apps f xs ]

  preFunc-eq : {f₁ f₂ : ClosedTermₗ (suc l)} {t₁ t₂ : ClosedTerm}
    → f₁ ≋ᶠ f₂ → t₁ ≋ t₂ → ∀ xs → preFunc (app f₁ t₁) xs ≡ preFunc (app f₂ t₂) xs
  preFunc-eq f₁≋f₂ t₁≋t₂ [] = eq/ _ _ $ ≋-app f₁≋f₂ t₁≋t₂
  preFunc-eq f₁≋f₂ t₁≋t₂ (x ∷ xs) = preFunc-eq (≋ᶠ-app f₁≋f₂ t₁≋t₂) ≋-refl xs

  preFunc-pointwiseEq : (f : ClosedTermₗ l) {xs ys : Vec ClosedTerm l} →
    xs ≋ₚ ys → preFunc f xs ≡ preFunc f ys
  preFunc-pointwiseEq f [] = refl
  preFunc-pointwiseEq f (x≋y ∷ xs≋ys) = (preFunc-pointwiseEq (app f _) xs≋ys) ∙ preFunc-eq ≋ᶠ-refl x≋y _

  func : ClosedTermₗ l → Vec Domain l → Domain
  func f = quotientLift ≋-refl squash/ (preFunc f) (preFunc-pointwiseEq f)

  preRel : (r : Sentenceₗ l) → (xs : Vec ClosedTerm l) → Type (ℓ-suc u)
  preRel r xs = T ⊦ (appsᵣ r xs)

  preRel-iff : {r₁ r₂ : Sentenceₗ (suc l)} {t₁ t₂ : ClosedTerm}
    → r₁ ≋ʳ r₂ → t₁ ≋ t₂ → ∀ xs → preRel (appᵣ r₁ t₁) xs ↔ preRel (appᵣ r₂ t₂) xs
  preRel-iff r₁≋r₂ t₁≋t₂ [] = ∥∥-↔ $ ⟷-trans (⟷-cong t₁≋t₂) (⟷-relExt⁻ r₁≋r₂)
  preRel-iff r₁≋r₂ t₁≋t₂ (x ∷ xs) = preRel-iff (≋ʳ-appᵣ r₁≋r₂ t₁≋t₂) ≋-refl xs

  preRel-pointwiseIff : (r : Sentenceₗ l) {xs ys : Vec ClosedTerm l} →
    xs ≋ₚ ys → preRel r xs ↔ preRel r ys
  preRel-pointwiseIff r [] = ∥∥-↔ ⟷-refl
  preRel-pointwiseIff r (x≋y ∷ xs≋ys) = ↔-trans (preRel-iff ≋ʳ-refl x≋y _) (preRel-pointwiseIff (appᵣ r _) xs≋ys)

  rel : Sentenceₗ l → Vec Domain l → hProp (ℓ-suc u)
  rel r = quotientLift ≋-refl isSetHProp (λ xs → preRel r xs , squash₁) (hPropExt ∘ preRel-pointwiseIff r)

termModel : Structure
termModel = record
  { Domain = TermModel.Domain
  ; isSetDomain = squash/
  ; funMap = TermModel.func ∘ func
  ; relMap = TermModel.rel ∘ rel
  }
  where open import FOL.Bounded.Base ℒ using (func; rel)
