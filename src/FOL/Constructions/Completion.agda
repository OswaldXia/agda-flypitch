{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
import FOL.Bounded.Syntactics as Bounded
import FOL.PropertiesOfTheory as Theory
module FOL.Constructions.Completion {T : Bounded.Theory ℒ} (ConT : Theory.Con ℒ T) where

open import FOL.Bounded.Syntactics ℒ
open import FOL.PropertiesOfTheory.Base ℒ

open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_; _$_)
open import Cubical.Functions.Logic using (inl; inr)
open import Cubical.Data.Sigma using (∃-syntax; ΣPathP) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)
open import Cubical.Relation.Binary
open BinaryRelation

open import CubicalExt.Axiom.Choice
open import CubicalExt.Axiom.ExcludedMiddle
open import CubicalExt.Foundations.Powerset*
open import CubicalExt.Logic.Zorn

private variable
  ℓ ℓ' : Level

Extension : Type _
Extension = Σ[ S ∈ Theory ] Con S × T ⊆ S

isPropCon×⊆ : ∀ S → isProp (Con S × T ⊆ S)
isPropCon×⊆ S = isPropΣ isPropCon λ _ → ⊆-isProp _ _

isSetExtension : isSet Extension
isSetExtension = isSetΣ isSet𝒫 λ _ → isProp→isSet $ isPropCon×⊆ _

_⪯_ : Rel Extension Extension _
_⪯_ e₁ e₂ = e₁ .fst ⊆ e₂ .fst

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

open Order _⪯_

module UB ⦃ em : ∀ {ℓ} → EM ℓ ⦄ (A : 𝒫 Extension ℓ) (isChainA : isChain A) where
  open import CubicalExt.Logic.Classical

  ub : Theory
  ub = T ∪ (Resize ∘ ⋃ (fst ⟦ A ⟧))

  ConUb : Con ub
  ConUb = {!   !}

module _ (ac : ∀ {ℓ ℓ'} → AC ℓ ℓ') where
  open import CubicalExt.Logic.ClassicalChoice ac

  hasUb : allChainHasUb
  hasUb A isChainA = (ub , ConUb , inl) , λ e e∈A x∈e₁ →
    inr $ resize ∣ e .fst , x∈e₁ , ∣ e , e∈A , reflId ∣₁ ∣₁
    where open UB A isChainA

  existsMaximalExtension : ∃[ emax ∈ Extension ] ∀ (e : Extension) → emax ⪯ e → emax ≡ e
  existsMaximalExtension = zorn ac ⪯-poset hasUb
