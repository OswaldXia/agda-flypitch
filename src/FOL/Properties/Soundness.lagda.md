---
title: Agda一阶逻辑(?) 可靠性
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(?) 可靠性

> 交流Q群: 893531731  
> 本文源码: [Soundness.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Properties/Soundness.lagda.md)  
> 高亮渲染: [Soundness.html](https://choukh.github.io/agda-flypitch/FOL.Properties.Soundness.html)  

```agda
{-# OPTIONS --cubical #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
module FOL.Properties.Soundness (ℒ : Language {u}) where

open import Cubical.Core.Primitives using (_,_)
open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude using (lift)
  renaming (sym to symPath; subst to substPath)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Functions.Logic using (isProp⟨⟩)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.HITs.PropositionalTruncation using (elim)
open import Cubical.HITs.SetTruncation using (∣_∣₂)
open import CubicalExt.Foundations.Powerset* using (_∈_)
open import CubicalExt.Classical using (byContra*)

open import Relation.Binary.PropositionalEquality using (refl; sym)
open import Function using (_∘_; _$_)
```

```agda
module Free where
  open import FOL.Base ℒ
  open import FOL.Semantics ℒ
  open import FOL.Lemmas.Realization
  open Realizer

  soundness : ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨ φ
  soundness (axiom φ∈Γ) _ _ 𝒮⊨Γ = 𝒮⊨Γ _ φ∈Γ
  soundness {_} {φ} (⊥-elim ⊢₀) 𝒮 𝓋 𝒮⊨Γ = byContra* (isProp⟨⟩ $ realize 𝒮 𝓋 ∣ φ ∣₂) $ λ ¬ →
    soundness ⊢₀ 𝒮 𝓋 λ φ → elim (λ _ → isProp⟨⟩ _)
      λ { (inl φ∈Γ) → 𝒮⊨Γ φ φ∈Γ
        ; (inr reflId) → lift ∘ ¬ }
  soundness ≈-refl _ _ _ = refl
  soundness (⇒-intro ⊢₀) 𝒮 𝓋 𝒮⊨Γ realization =
    soundness ⊢₀ 𝒮 𝓋 λ φ → elim (λ _ → isProp⟨⟩ _)
      λ { (inl φ∈Γ) → 𝒮⊨Γ φ φ∈Γ
        ; (inr reflId) → realization }
  soundness (⇒-elim ⊢₁ ⊢₂) 𝒮 𝓋 𝒮⊨Γ = (soundness ⊢₁ 𝒮 𝓋 𝒮⊨Γ) (soundness ⊢₂ 𝒮 𝓋 𝒮⊨Γ)
  soundness (∀-intro ⊢₀) 𝒮 𝓋 𝒮⊨Γ x =
    soundness ⊢₀ 𝒮 _ λ φ → elim (λ _ → isProp⟨⟩ _)
      λ { (ψ , ψ∈Γ , reflId) → substPath ⟨_⟩ (symPath $ realize-subst-lift 𝒮 𝓋 0 x ψ) (𝒮⊨Γ ψ ψ∈Γ) }
  soundness (∀-elim {_} {φ} {t} ⊢₀) 𝒮 𝓋 𝒮⊨Γ =
    substPath ⟨_⟩ (realize-subst0 𝒮 𝓋 t ∣ φ ∣₂) (soundness ⊢₀ 𝒮 𝓋 𝒮⊨Γ _)
  soundness (subst {_} {s} {t} {φ} ⊢₁ ⊢₂) 𝒮 𝓋 𝒮⊨Γ =
    substPath ⟨_⟩ (realize-subst0 𝒮 𝓋 t ∣ φ ∣₂) H where
      H : ⟨ realize 𝒮 (𝓋 [ realizeₜ 𝒮 𝓋 t / 0 ]ᵥ) ∣ φ ∣₂ ⟩
      H rewrite sym $ soundness ⊢₁ 𝒮 𝓋 𝒮⊨Γ =
        substPath ⟨_⟩ (symPath $ realize-subst0 𝒮 𝓋 s ∣ φ ∣₂) (soundness ⊢₂ 𝒮 𝓋 𝒮⊨Γ)
```

```agda
module _ where
  open import FOL.Bounded.Base ℒ using (_⊢_)
  open import FOL.Bounded.Semantics ℒ using (_⊨_)
  open import FOL.Bounded.Lemmas.Semantics ℒ using (bound⊨)

  soundness : ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨ φ
  soundness = bound⊨ ∘ Free.soundness
```
