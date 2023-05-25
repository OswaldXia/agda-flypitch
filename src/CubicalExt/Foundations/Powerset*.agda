{- Polymorphic version of "powerset" -}

{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module CubicalExt.Foundations.Powerset* where

open import Cubical.Core.Id renaming (_≡_ to _≡ⁱᵈ_)
open import CubicalExt.Foundations.Id using (path≡Id-termLevel; idToPath; pathToId; ap)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Foundations.Function
open import Cubical.Functions.Logic hiding (¬_)
open import Cubical.Data.Empty using (⊥*; isProp⊥*)
open import Cubical.Data.Unit using (Unit*; isPropUnit*)
open import Cubical.Data.Sigma
import Cubical.Data.Sum as ⊎
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)

private variable
  ℓ ℓ' ℓ'' ℓ₀ ℓ₁ ℓ₂ : Level
  X Y : Type ℓ

------------------------------------------------------------------------
-- Definition

𝒫 : Type ℓ → (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
𝒫 X ℓ' = X → hProp ℓ'

isSet𝒫 : isSet (𝒫 X ℓ)
isSet𝒫 = isSetΠ λ x → isSetHProp

------------------------------------------------------------------------
-- Lifting

liftHProp : hProp ℓ₀ → hProp (ℓ-max ℓ₀ ℓ)
liftHProp {ℓ₀} {ℓ} (A , Aprop) = Lift {ℓ₀} {ℓ} A , isOfHLevelLift 1 Aprop

lift𝒫 : 𝒫 X ℓ₀ → 𝒫 X (ℓ-max ℓ₀ ℓ)
lift𝒫 A x = liftHProp (A x)

------------------------------------------------------------------------
-- Special sets

-- Empty set

∅ : 𝒫 X ℓ-zero
∅ = λ _ → ⊥

∅* : 𝒫 X ℓ
∅* = λ _ → ⊥* , isProp⊥*

-- Universal set

U : 𝒫 X ℓ-zero
U = λ _ → ⊤

U* : 𝒫 X ℓ
U* = λ _ → Unit* , isPropUnit*

------------------------------------------------------------------------
-- Membership

infix 5 _∈_ _∉_ _⊆_

_∈_ : X → 𝒫 X ℓ → Type _
x ∈ A = ⟨ A x ⟩

_∉_ : X → 𝒫 X ℓ → Type _
x ∉ A = ¬ ⟨ A x ⟩

subst-∈ : (A : 𝒫 X ℓ) {x y : X} → x ≡ y → x ∈ A → y ∈ A
subst-∈ A = subst (_∈ A)

∈-isProp : (A : 𝒫 X ℓ) (x : X) → isProp (x ∈ A)
∈-isProp A = snd ∘ A

------------------------------------------------------------------------
-- Subset

_⊆_ : 𝒫 X ℓ₁ → 𝒫 X ℓ₂ → Type _
A ⊆ B = ∀ {x} → x ∈ A → x ∈ B

⊆-isProp : (A : 𝒫 X ℓ) (B : 𝒫 X ℓ') → isProp (A ⊆ B)
⊆-isProp A B = isPropImplicitΠ $ λ x → isPropΠ $ λ _ → ∈-isProp B x

⊆-refl : (A : 𝒫 X ℓ) → A ⊆ A
⊆-refl A {x} = idfun (x ∈ A)

⊆-refl-consequence : (A B : 𝒫 X ℓ) → A ≡ B → (A ⊆ B) × (B ⊆ A)
⊆-refl-consequence A B p = subst (A ⊆_) p (⊆-refl A)
                         , subst (B ⊆_) (sym p) (⊆-refl B)

⊆-extensionality : (A B : 𝒫 X ℓ) → (A ⊆ B) × (B ⊆ A) → A ≡ B
⊆-extensionality A B (φ , ψ) =
  funExt (λ x → TypeOfHLevel≡ 1 (hPropExt (A x .snd) (B x .snd) φ ψ))

⊆-extensionalityEquiv : (A B : 𝒫 X ℓ) → (A ⊆ B) × (B ⊆ A) ≃ (A ≡ B)
⊆-extensionalityEquiv A B = isoToEquiv (iso (⊆-extensionality A B)
                                            (⊆-refl-consequence A B)
                                            (λ _ → isSet𝒫 A B _ _)
                                            (λ _ → isPropΣ (⊆-isProp A B) (λ _ → ⊆-isProp B A) _ _))

⊆-antisym : (A B : 𝒫 X ℓ) → A ⊆ B → B ⊆ A → A ≡ B
⊆-antisym A B A⊆B B⊆A = ⊆-extensionality A B $ A⊆B , B⊆A

⊆-trans : (A : 𝒫 X ℓ) (B : 𝒫 X ℓ') (C : 𝒫 X ℓ'') → A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans A B C A⊆B B⊆C x∈A = B⊆C $ A⊆B x∈A

------------------------------------------------------------------------
-- Operations on sets

-- Union

_∪_ : 𝒫 X ℓ₁ → 𝒫 X ℓ₂ → 𝒫 X _
A ∪ B = λ x → (x ∈ A , ∈-isProp A x) ⊔ (x ∈ B , ∈-isProp B x)

-- Intersection

_∩_ : 𝒫 X ℓ₁ → 𝒫 X ℓ₂ → 𝒫 X _
A ∩ B = λ x → (x ∈ A , ∈-isProp A x) ⊓ (x ∈ B , ∈-isProp B x)

-- Big union

⋃ᵢ_ : (X → 𝒫 Y ℓ) → 𝒫 Y _
(⋃ᵢ Aᵢ) y = (∃[ x ∈ _ ] ⟨ Aᵢ x y ⟩) , squash₁

⋃_ : 𝒫 (𝒫 X ℓ) ℓ' → 𝒫 X _
(⋃ 𝒜) x = (∃[ A ∈ _ ] (x ∈ A) × (A ∈ 𝒜)) , squash₁

⋃∅≡∅ : ⋃ (∅* {X = 𝒫 X ℓ} {ℓ'}) ≡ ∅*
⋃∅≡∅ = ⊆-extensionality _ _ $ (rec (∈-isProp _ _) λ ()) , λ ()

private variable
  A B : 𝒫 X ℓ
  f : X → Y
  x : X

-- Image set

_⟦_⟧ : (X → Y) → 𝒫 X ℓ → 𝒫 Y _
f ⟦ A ⟧ = λ y → (∃[ x ∈ _ ] (x ∈ A) × (y ≡ⁱᵈ f x)) , squash₁

f⟦∅⟧≡∅ : f ⟦ ∅* {ℓ = ℓ} ⟧ ≡ ∅*
f⟦∅⟧≡∅ = ⊆-extensionality _ _ $ (rec (∈-isProp _ _) λ ()) , λ ()

-- Replacement

replacement-syntax : (X : Type ℓ) {Y : Type ℓ'} → (X → Y) → 𝒫 Y _
replacement-syntax X f = f ⟦ U {X = X} ⟧

syntax replacement-syntax A (λ x → B) = ｛ B ∣ x ∈ A ｝

⟦⟧⊆⟦⟧ : A ⊆ B → f ⟦ A ⟧ ⊆ f ⟦ B ⟧
⟦⟧⊆⟦⟧ A⊆B = rec (∈-isProp _ _)
  λ { (x , x∈A , eq) → ∣ x , A⊆B x∈A , eq ∣₁ }

module SetBased (Xset : isSet X) where

  -- Singleton set

  ｛_｝ : X → 𝒫 X _
  ｛ x ｝ = λ y → (x ≡ⁱᵈ y) , subst isProp path≡Id-termLevel (Xset x y)

  _⟦｛_｝⟧ : (f : X → Y) (x : X) → 𝒫 Y _
  f ⟦｛ x ｝⟧ = f ⟦ ｛ x ｝ ⟧

  -- Incusion

  infixl 6 _⨭_

  _⨭_ : (A : 𝒫 X ℓ) (x : X) → 𝒫 X _
  A ⨭ x = A ∪ ｛ x ｝

  ⊆⨭ : A ⊆ A ⨭ x
  ⊆⨭ x∈A = inl x∈A

  ⨭⊆⨭ : A ⊆ B → A ⨭ x ⊆ B ⨭ x
  ⨭⊆⨭ A⊆B = rec (∈-isProp _ _)
    λ { (⊎.inl H) → inl (A⊆B H)
      ; (⊎.inr H) → inr H
      }

module SetBased2 (Xset : isSet X) (Yset : isSet Y) where
  open SetBased Xset using () renaming (｛_｝ to ｛_｝₁; _⟦｛_｝⟧ to _⟦｛_｝⟧₁; _⨭_ to _⨭₁_) public
  open SetBased Yset using () renaming (｛_｝ to ｛_｝₂; _⟦｛_｝⟧ to _⟦｛_｝⟧₂; _⨭_ to _⨭₂_) public

  ⟦｛｝⟧⊆ : f ⟦｛ x ｝⟧₁ ⊆ ｛ f x ｝₂
  ⟦｛｝⟧⊆ = rec (∈-isProp _ _) λ { (x , reflId , reflId) → reflId }

  ⊆⟦｛｝⟧ : ｛ f x ｝₂ ⊆ f ⟦｛ x ｝⟧₁
  ⊆⟦｛｝⟧ reflId = ∣ _ , reflId , reflId ∣₁

  ⟦⨭⟧⊆ : f ⟦ A ⨭₁ x ⟧ ⊆ f ⟦ A ⟧ ⨭₂ f x
  ⟦⨭⟧⊆ {f = f} {A = A} = rec (∈-isProp _ _)
    λ { (y , y∈⨭ , reflId) →
        rec (∈-isProp (f ⟦ A ⟧ ⨭₂ _) _) (
          λ { (⊎.inl y∈A) → inl ∣ y , y∈A , reflId ∣₁
            ; (⊎.inr reflId) → inr reflId
            })
          y∈⨭
      }

  ⊆⟦⨭⟧ : f ⟦ A ⟧ ⨭₂ f x ⊆ f ⟦ A ⨭₁ x ⟧
  ⊆⟦⨭⟧ {f = f} {A = A} = rec (∈-isProp _ _)
    λ { (⊎.inl y∈f) →
        rec (∈-isProp (f ⟦ A ⨭₁ _ ⟧) _) (
          λ { (y , y∈A , reflId) → ∣ y , inl y∈A , reflId ∣₁ })
          y∈f
      ; (⊎.inr reflId) → ∣ _ , inr reflId , reflId ∣₁
      }

  ⟦⨭⟧≡ : f ⟦ A ⨭₁ x ⟧ ≡ f ⟦ A ⟧ ⨭₂ f x
  ⟦⨭⟧≡ = ⊆-extensionality _ _ $ ⟦⨭⟧⊆ , ⊆⟦⨭⟧

module _ {X Y : Type ℓ} (Xset : isSet X) (Yset : isSet Y)
  {f : X → Y} (inj : ∀ x y → f x ≡ f y → x ≡ y)
  (A : 𝒫 Y ℓ) (x : X) where
  open SetBased2 Xset Yset

  ⨭∘⊆ : (A ⨭₂ f x) ∘ f ⊆ (A ∘ f) ⨭₁ x
  ⨭∘⊆ = rec (∈-isProp _ _)
    λ { (⊎.inl fx∈A) → inl fx∈A
      ; (⊎.inr fx≡fy) → inr $ pathToId $ inj _ _ $ idToPath fx≡fy }

  ⊆⨭∘ : (A ∘ f) ⨭₁ x ⊆ (A ⨭₂ f x) ∘ f
  ⊆⨭∘ = rec (∈-isProp _ _)
    λ { (⊎.inl fx∈A) → inl fx∈A
      ; (⊎.inr reflId) → inr $ ap f reflId }

  ⨭∘≡ : (A ⨭₂ f x) ∘ f ≡ (A ∘ f) ⨭₁ x
  ⨭∘≡ = ⊆-extensionality _ _ $ ⨭∘⊆ , ⊆⨭∘
