{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import CubicalExt.Axiom.Choice
open import FOL.Language
import FOL.Bounded.Syntactics as Bounded
import FOL.PropertiesOfTheory as Theory
module FOL.Constructions.Completion (ac : ∀ {ℓ ℓ'} → AC ℓ ℓ')
  {T : Bounded.Theory ℒ} (ConT : Theory.Con ℒ T) where

open import FOL.Syntactics ℒ using (⇒-intro)
open import FOL.Bounded.Base ℒ hiding (_∨_)
open import FOL.Bounded.Syntactics ℒ
open import FOL.PropertiesOfTheory.Base ℒ

open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude hiding (~_; _∨_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_; _$_)
open import Cubical.Data.Sigma using (∃-syntax; ΣPathP; PathPΣ) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁; rec)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Relation.Binary
open BinaryRelation

open import CubicalExt.Axiom.ExcludedMiddle
open import CubicalExt.Foundations.Powerset*
open import CubicalExt.Functions.Logic
open import CubicalExt.Logic.ClassicalChoice ac
open import CubicalExt.Logic.Zorn

open import FOL.Bounded.Lemmas.Sethood ℒ
open SetBased isSetSentence using (_⨭_)

private variable
  ℓ ℓ' : Level
  S : Theory

instance
  isPropImplicitCon : isPropImplicit (Con S)
  isPropImplicitCon = isPropCon _ _

extensible : ∀ φ → Con (T ⨭ φ) ∨ Con (T ⨭ ~ φ)
extensible φ = byContra λ ¬∨ → let (H₁ , H₂) = ¬∨-demorgen ¬∨ in
  {! byContra {A = Con (T ⨭ φ)} ⦃ isPropImplicitCon ⦄  !}

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

module UB {A : 𝒫 Extension ℓ} (isChainA : isChain A) where

  ub : Theory
  ub = T ∪ (Resize ∘ ⋃ (fst ⟦ A ⟧))

  ConUb : Con ub
  ConUb = {!   !}

hasUb : allChainHasUb
hasUb A isChainA = (ub , ConUb , inl) , λ e e∈A x∈e₁ →
  inr $ resize ∣ e .fst , x∈e₁ , ∣ e , e∈A , reflId ∣₁ ∣₁
  where open UB isChainA

maximalExtension = Σ[ max ∈ Extension ] maximum max

maximalExtensionMaximal : (((S , _) , _) : maximalExtension) → maximal S
maximalExtensionMaximal (E@(S , (_ , T⊆S)) , maximum) φ con⨭ = φ∈S where
  E' : Extension
  E' = S ⨭ φ , con⨭ , inl ∘ T⊆S
  E≡E' = maximum E' inl
  S≡S' = PathPΣ E≡E' .fst
  φ∈S = subst (_ ∈_) (sym S≡S') (inr reflId)

maximalExtensionComplete : (((S , _) , _) : maximalExtension) → complete S
maximalExtensionComplete m@((S , _) , _) φ with em ⦃ ∈-isProp S φ _ _ ⦄
... | yes φ∈S = inl φ∈S
... | no  φ∉S = inr $ byContra ⦃ ∈-isProp S (~ φ) _ _ ⦄ λ ~φ∉S →
  {!   !}
  --φ∉S $ maximalExtensionMaximal m φ λ S⨭φ⊢⊥ → ~φ∉S {!   !}
  --⇒-intro $ bound⊢ S⨭φ⊢⊥

existsMaximalExtension : ∥ maximalExtension ∥₁
existsMaximalExtension = zorn ac ⪯-poset hasUb

existsConsistentCompleteExtension : ∃[ S ∈ Theory ] Con S × complete S
existsConsistentCompleteExtension = rec squash₁
  (λ { m@((S , (conS , _)) , _) → ∣ S , conS , maximalExtensionComplete m ∣₁ })
  existsMaximalExtension
