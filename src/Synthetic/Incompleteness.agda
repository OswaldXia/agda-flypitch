{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Synthetic.Axiom.Base
open import Synthetic.FormalSystem using (FormalSystem)
module Synthetic.Incompleteness (epf : EPFᴮ)
  {ℓ} {Sentence : Type ℓ} {~_ : Sentence → Sentence}
  (S : FormalSystem Sentence ~_) where

open import Synthetic.FormalSystem using (_represents_by_; ⊢-dec→repr→dec; ⊑-refl)
open FormalSystem S using (⊢_; complete; complete→⊢-dec)

open import Synthetic.Definitions.Base
open import Synthetic.Definitions.Properties
open import Synthetic.Halting epf

open import Cubical.Foundations.Function
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff

module Weak (fᵣ : ℕ → Sentence) (repr : S represents Kᶿ by fᵣ) where

  ⊢-¬dec : ¬ decidable (⊢_)
  ⊢-¬dec dec = Kᶿ-¬dec $ ⊢-dec→repr→dec ⊑-refl dec (λ _ → squash₁)
    (fᵣ , repr , λ n → repr n .from)

  incompleteness : ¬ complete
  incompleteness compl = ⊢-¬dec $ complete→⊢-dec compl
