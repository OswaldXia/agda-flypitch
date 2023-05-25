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

module _ (Xset : isSet X) {a@(A , finA) : Finite Xset}
         (Yset : isSet Y) {b@(B , finB) : Finite Yset} where

  existsDomOfSubImg : B ⊆ f ⟦ A ⟧ → ∃[ a'@(A' , _) ∈ Finite Xset ] A' ⊆ A × f ⟦ A' ⟧ ≡ B
  existsDomOfSubImg {f = f} B⊆f⟦A⟧ = ∣ a' , A'⊆A , f⟦A'⟧≡B ∣₁ where
    Z : Type _
    Z = Σ[ x ∈ X ] f x ∈ B
    abstract
      Zset : isSet Z
      Zset = isSetΣ Xset λ _ → isProp→isSet $ ∈-isProp _ _
    emb : Z ↪ X
    emb = fst , λ _ _ → isEmbeddingFstΣProp λ _ → ∈-isProp _ _
    open Embdding Zset Xset
    C : 𝒫 Z ℓ
    C = A ∘ fst
    finC : finite Zset C
    finC with finA
    ... | fin∅ = fin∅
    ... | fin⨭ x A x∉A finA = {!    !}
    --with finite→Dec∈ Yset ? (f x) finB
    a' : Finite Xset
    a' = map emb $ C , finC
    A' = fst a'
    A'⊆A : A' ⊆ A
    A'⊆A x∈A' with finC
    ... | fuck = {! fuck  !}
    f⟦A'⟧⊆B : f ⟦ A' ⟧ ⊆ B
    f⟦A'⟧⊆B {y} = rec (∈-isProp _ _) λ { (x , x∈A' , reflId) → {!    !} }
    B⊆f⟦A'⟧ : B ⊆ f ⟦ A' ⟧
    B⊆f⟦A'⟧ {y} y∈B = ∣ {!   !} , {!   !} , {!   !} ∣₁
    f⟦A'⟧≡B = ⊆-extensionality _ _ $ f⟦A'⟧⊆B , B⊆f⟦A'⟧
