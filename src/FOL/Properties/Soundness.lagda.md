---
title: Agda一阶逻辑(?) 可靠性
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(?) 可靠性

> 交流Q群: 893531731  
> 本文源码: [Soundness.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Properties/Soundness.lagda.md)  
> 高亮渲染: [Soundness.html](https://choukh.github.io/agda-flypitch/FOL.Properties.Soundness.html)  

```agda
{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Properties.Soundness ⦃ em : ∀ {ℓ} → EM ℓ ⦄ (ℒ : Language {u}) where
open import CubicalExt.Logic.Classical ⦃ em ⦄ using (byContra*)
```

```agda
open import Cubical.Core.Id using (reflId)
open import Cubical.Foundations.Prelude
open import CubicalExt.Foundations.Powerset* using (_∈_)
open import CubicalExt.Functions.Logic.Iff
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Equality using (pathToEq)
open import Cubical.HITs.PropositionalTruncation using (elim)
open import Function using (_∘_; _$_)
```

```agda
module Untruncated where
  module Free {v} where
    open import FOL.Base ℒ
    open import FOL.Syntactics ℒ
    open import FOL.Semantics ℒ
    open import FOL.Lemmas.Realization
    open Implication v using (_⊨_)
    open Realizer
```

```agda
    soundness : ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨ φ
    soundness (axiom φ∈Γ) _ _ 𝒮⊨Γ = 𝒮⊨Γ _ φ∈Γ
    soundness {_} {φ} (⊥-elim ⊢₀) 𝒮 𝓋 𝒮⊨Γ = byContra* λ ¬ →
      soundness ⊢₀ 𝒮 𝓋 λ φ → elim (λ _ → isPropRealize _ _ _)
        λ { (inl φ∈Γ) → 𝒮⊨Γ φ φ∈Γ
          ; (inr reflId) → lift ∘ ¬ }
    soundness ≈-refl _ _ _ = refl
    soundness (⇒-intro ⊢₀) 𝒮 𝓋 𝒮⊨Γ realization =
      soundness ⊢₀ 𝒮 𝓋 λ φ → elim (λ _ → isPropRealize _ _ _)
        λ { (inl φ∈Γ) → 𝒮⊨Γ φ φ∈Γ
          ; (inr reflId) → realization }
    soundness (⇒-elim ⊢₁ ⊢₂) 𝒮 𝓋 𝒮⊨Γ = (soundness ⊢₁ 𝒮 𝓋 𝒮⊨Γ) (soundness ⊢₂ 𝒮 𝓋 𝒮⊨Γ)
    soundness (∀-intro ⊢₀) 𝒮 𝓋 𝒮⊨Γ x =
      soundness ⊢₀ 𝒮 _ λ φ → elim (λ _ → isPropRealize _ _ _)
        λ { (ψ , ψ∈Γ , reflId) → from (realize-subst-lift 𝒮 𝓋 0 ψ x) $ 𝒮⊨Γ ψ ψ∈Γ }
    soundness (∀-elim {_} {φ} {t} ⊢₀) 𝒮 𝓋 𝒮⊨Γ =
      to (realize-subst0 𝒮 𝓋 φ t) $ soundness ⊢₀ 𝒮 𝓋 𝒮⊨Γ _
    soundness (subst {_} {s} {t} {φ} ⊢₁ ⊢₂) 𝒮 𝓋 𝒮⊨Γ =
      to (realize-subst0 𝒮 𝓋 φ t) $ H where
        H : realize 𝒮 (𝓋 [ 0 ≔ realizeₜ 𝒮 𝓋 t ]ᵥ) φ
        H rewrite pathToEq $ sym $ soundness ⊢₁ 𝒮 𝓋 𝒮⊨Γ =
          from (realize-subst0 𝒮 𝓋 φ s) $ (soundness ⊢₂ 𝒮 𝓋 𝒮⊨Γ)
```

```agda
  module _ {v} where
    open import FOL.Bounded.Syntactics ℒ using (_⊢_)
    open import FOL.Bounded.Semantics ℒ
    open Implication v using (_⊨_)
    open import FOL.Bounded.Lemmas.Semantics ℒ v using (bound⊨)

    soundness : ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨ φ
    soundness = bound⊨ ∘ Free.soundness
```

```agda
module _ {v} where
  open import FOL.Bounded.Syntactics ℒ using (_⊦_)
  open import FOL.Bounded.Semantics ℒ
  open Implication v using (_⊨_; isProp-⊨)

  Soundness : Type (ℓ-max (ℓ-suc u) (ℓ-suc v))
  Soundness = ∀ {Γ φ} → Γ ⊦ φ → Γ ⊨ φ

  soundness : Soundness
  soundness = elim (λ _ → isProp-⊨ _ _) Untruncated.soundness
```
 