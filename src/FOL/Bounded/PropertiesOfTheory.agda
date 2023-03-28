{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Bounded.PropertiesOfTheory (ℒ : Language {u}) where

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Substitution ℒ
open import FOL.Bounded.Interpretation ℒ using (_⊨ᵀ_)
open import FOL.Structure.Base
open Language ℒ using (Constant)
open Structure using (Domain)

open import Cubical.Core.Everything using (Type; ℓ-suc; ℓ-max)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; Σ-syntax)
open import Function using (_$_)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (_∈_)

-- 理论的一致性

Con : Theory → Type (ℓ-suc u)
Con T = ¬ T ⊢ ⊥

¬Con : Theory → Type (ℓ-suc u)
¬Con T = T ⊢ ⊥

-- 理论的极大性

maximal : Theory → Type (ℓ-suc u)
maximal T = Σ[ C ∈ (Formula 1 → Constant) ]
  (∀ φ → T ⊢ ∃' φ ⇒ φ [ const (C φ) / 0 ])

-- 理论的完全性

complete : Theory → Type (ℓ-suc u)
complete T = Con T × ∀ φ → φ ∈ T ⊎ ¬ φ ∈ T

-- 理论存在模型

modelExistence : ∀ {v} → Theory → Type (ℓ-max u $ ℓ-suc v)
modelExistence {v} T = Σ[ ℳ ∈ Structure ℒ {v} ] Domain ℳ × ℳ ⊨ᵀ T
