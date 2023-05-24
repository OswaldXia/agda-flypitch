{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module CubicalExt.Foundations.Powerset*.Finite {ℓ} where
open import CubicalExt.Foundations.Powerset*

open import Cubical.Core.Id renaming (_≡_ to _≡ⁱᵈ_)
open import Cubical.Foundations.Prelude hiding (lift)
open import Cubical.Foundations.Id using (idToPath)
open import Cubical.Foundations.Function using (_$_)
open import Cubical.Foundations.Structure
open import Cubical.Functions.Embedding
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; rec)

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

module Mapping (Xset : isSet X) (Yset : isSet Y) ((f , emb) : X ↪ Y) where
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

module _ (Xset : isSet X) (Yset : isSet Y) {a@(A , _) : Finite Xset} {b@(B , _) : Finite Yset} where
  foo : B ⊆ f ⟦ A ⟧ → ∃[ a'@(A' , _) ∈ Finite Xset ] A' ⊆ A × f ⟦ A' ⟧ ≡ B
  foo {f = f} B⊆f⟦A⟧ = ∣ map {!   !} b , {!   !} , {!   !} ∣₁
    where image : Type _
          image = Σ[ y ∈ Y ] ⟨ (f ⟦ A ⟧) y ⟩
          imageSet : isSet image
          imageSet = {!   !}
          open Mapping Yset Xset
