{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
import FOL.Bounded.Syntactics as Bounded
module FOL.Constructions.Completion (T : Bounded.Theory ℒ) where

open import FOL.Bounded.Syntactics ℒ
open import FOL.PropertiesOfTheory.Base ℒ

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_; _$_)
open import Cubical.Data.Sigma using (∃-syntax; ΣPathP) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)
open import Cubical.Relation.Binary
open BinaryRelation

open import CubicalExt.Axiom.Choice
open import CubicalExt.Foundations.Powerset*
open import CubicalExt.Logic.Zorn

Extension : Type _
Extension = Σ[ S ∈ Theory ] Con S × T ⊆ S

isPropCon×⊆ : ∀ S → isProp (Con S × T ⊆ S)
isPropCon×⊆ S = isPropΣ isPropCon λ _ → ⊆-isProp _ _

isSetExtension : isSet Extension
isSetExtension = isSetΣ isSet𝒫 λ _ → isProp→isSet $ isPropCon×⊆ _

_⪯_ : Rel Extension Extension _
_⪯_ E₁ E₂ = E₁ .fst ⊆ E₂ .fst

⪯-prop : isPropValued _⪯_
⪯-prop _ _ = ⊆-isProp _ _

⪯-refl : isRefl _⪯_
⪯-refl = ⊆-refl ∘ fst

⪯-antisym : isAntisym _⪯_
⪯-antisym _ _ H₁ H₂ = ΣPathP $ ⊆-antisym _ _ H₁ H₂ , toPathP (isPropCon×⊆ _ _ _)

⪯-trans : isTrans _⪯_
⪯-trans _ _ _ H₁ H₂ x∈ = H₂ $ H₁ x∈

⪯-poset : Order.isPoset _⪯_
⪯-poset = isSetExtension , ⪯-prop , ⪯-refl , ⪯-antisym , ⪯-trans

module _ (ac : ∀ {ℓ ℓ'} → AC ℓ ℓ') where
  open import CubicalExt.Logic.ClassicalChoice ac

  allChainHasUb : Order.allChainHasUb _⪯_
  allChainHasUb E isChainE = let ub = T ∪ (Resize ∘ ⋃ (fst ⟦ E ⟧)) in
    (ub , {!   !}) , {!   !}

  existsMaximalExtension : ∃[ Emax ∈ Extension ] ∀ (E : Extension) → Emax ⪯ E → Emax ≡ E
  existsMaximalExtension = zorn ac ⪯-poset allChainHasUb
