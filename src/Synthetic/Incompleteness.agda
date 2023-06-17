{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude
open import Synthetic.FormalSystem
module Synthetic.Incompleteness
  {ℓ} {Sentence : Type ℓ} {¬_ : Sentence → Sentence}
  (S : FormalSystem Sentence ¬_) where
open FormalSystem S

open import Synthetic.Definitions.Base
open import Synthetic.Definitions.Properties

open import Cubical.Foundations.Function
open import Cubical.Data.Bool
open import Cubical.Data.Sum

open import Cubical.HITs.PropositionalTruncation as ∥₁
open import CubicalExt.Functions.Logic.Iff
