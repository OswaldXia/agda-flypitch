{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module CubicalExt.Foundations.Powerset*.Finite {ℓ} where
open import CubicalExt.Foundations.Powerset*

open import Cubical.Core.Id renaming (_≡_ to _≡ⁱᵈ_)
open import Cubical.Foundations.Prelude hiding (lift)
open import Cubical.Foundations.Id using (idToPath; pathToId)
open import Cubical.Foundations.Function using (_∘_; _$_)
open import Cubical.Foundations.HLevels using (isSetΣ)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Functions.Embedding
open import Cubical.Functions.Logic
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Sigma renaming (_×_ to infixr 3 _×_)
import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; rec)
open import Cubical.Relation.Nullary

private variable
  X Y : Type ℓ
  x : X
  f : X → Y
  A B : 𝒫 X ℓ

module _ (Xset : isSet X) where
  open SetBased Xset

  data finite : 𝒫 X ℓ → Type (ℓ-suc ℓ) where
    fin∅ : finite ∅*
    fin⨭ : ∀ x A → x ∉ A → finite A → finite (A ⨭ x)

  Finite : Type (ℓ-suc ℓ)
  Finite = Σ[ A ∈ 𝒫 X ℓ ] finite A

  module _ (discrete : Discrete X) (x : X) where
    finite→Dec∈ : finite A → Dec (x ∈ A)
    finite→Dec∈ fin∅ = no λ ()
    finite→Dec∈ (fin⨭ y A y∉A finA) with finite→Dec∈ finA
    ... | yes x∈A = yes $ inl x∈A
    ... | no  x∉A with discrete x y
    ... | yes x≡y = yes $ inr $ pathToId $ sym $ x≡y
    ... | no  x≢y = no $ rec isProp⊥
      λ { (⊎.inl x∈A) → x∉A x∈A
        ; (⊎.inr y≡x) → x≢y $ sym $ idToPath y≡x }

module Embdding (Xset : isSet X) (Yset : isSet Y) ((f , emb) : X ↪ Y) where
  open SetBased2 Xset Yset

  fx∉f⟦A⟧ : x ∉ A → f x ∉ f ⟦ A ⟧
  fx∉f⟦A⟧ {A = A} x∉A = rec isProp⊥ λ { (x , x∈A , id) → x∉A $
    subst (_∈ A) (sym $ isEmbedding→Inj emb _ _ $ idToPath id) x∈A }

  finiteImage : finite Xset A → finite Yset (f ⟦ A ⟧)
  finiteImage fin∅ = subst (finite Yset) (sym f⟦∅⟧≡∅) fin∅
  finiteImage (fin⨭ x A x∉A finA) = subst (finite Yset) (sym ⟦⨭⟧≡) $
    fin⨭ _ _ (fx∉f⟦A⟧ x∉A) (finiteImage finA)

  map : Finite Xset → Finite Yset
  map (.∅* , fin∅) = ∅* , fin∅
  map (.(A ⨭₁ x) , fin⨭ x A x∉A finA) = f ⟦ A ⟧ ⨭₂ f x , fin⨭ _ _ (fx∉f⟦A⟧ x∉A) (finiteImage finA)

module _ (Xset : isSet X)
         (Yset : isSet Y) (discreteY : Discrete Y)
         {a@(A , finA) : Finite Xset}
         {b@(B , finB) : Finite Yset} where

  DomOfSubImg : B ⊆ f ⟦ A ⟧ → Σ[ a'@(A' , _) ∈ Finite Xset ] A' ⊆ A × f ⟦ A' ⟧ ≡ B
  DomOfSubImg {f = f} B⊆f⟦A⟧ = a' , A'⊆A , f⟦A'⟧≡B where
    Z : Type _
    Z = Σ[ x ∈ X ] f x ∈ B
    abstract
      Zset : isSet Z
      Zset = isSetΣ Xset λ _ → isProp→isSet $ ∈-isProp _ _
    Emb : Z ↪ X
    Emb = fst , λ _ _ → isEmbeddingFstΣProp λ _ → ∈-isProp _ _
    open Embdding Zset Xset Emb
    A⁻¹ : 𝒫 Z ℓ
    A⁻¹ = fst ⁻¹⟦ A ⟧
    finA⁻¹ : finite Zset A⁻¹
    finA⁻¹ = helper finA where
      helper : ∀ {A} → finite Xset A → finite Zset (fst ⁻¹⟦ A ⟧)
      helper fin∅ = fin∅
      helper (fin⨭ x A x∉A finA) with finite→Dec∈ Yset discreteY (f x) finB
      ... | yes fx∈B = subst (finite Zset) (sym eq) $ fin⨭ z (fst ⁻¹⟦ A ⟧) x∉A (helper finA) where
        z = x , fx∈B
        open Preimage Zset Xset
        eq : fst ⁻¹⟦ A ⨭₂ x ⟧ ≡ fst ⁻¹⟦ A ⟧ ⨭₁ z
        eq = ⁻¹⟦⨭⟧≡ A z $ isEmbedding→Inj $ snd Emb
      ... | no fx∉B = {!   !}
    a' : Finite Xset
    a' = map $ A⁻¹ , finA⁻¹
    A' = fst a'
    A'⊆A : A' ⊆ A
    A'⊆A x∈A' with finA⁻¹
    ... | fuck = {! fuck  !}
    f⟦A'⟧⊆B : f ⟦ A' ⟧ ⊆ B
    f⟦A'⟧⊆B {y} = rec (∈-isProp _ _) λ { (x , x∈A' , reflId) → {!    !} }
    B⊆f⟦A'⟧ : B ⊆ f ⟦ A' ⟧
    B⊆f⟦A'⟧ {y} y∈B = ∣ {!   !} , {!   !} , {!   !} ∣₁
    f⟦A'⟧≡B = ⊆-extensionality _ _ $ f⟦A'⟧⊆B , B⊆f⟦A'⟧
