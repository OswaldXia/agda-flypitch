{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
open import FOL.Bounded.Syntactics using (Theory)
module FOL.Constructions.HenkinizedTermModel ⦃ em : EM ⦄ {ℒ : Language {u}} (T : Theory ℒ) where

open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Constructions.Henkin.TheoryChain u
open import FOL.Constructions.Henkin.Properties ℒ
open import FOL.Constructions.TermModel.Base (∞-theory T)

open import FOL.Structure.Base ℒ using (Structure)
open import FOL.Structure.Reduction.Base (henkinization ℒ)
open import FOL.Structure.Reduction.Properties (henkinization ℒ) termModel

open import Function using (_$_)

henkinizedTermModel : Structure
henkinizedTermModel = ⟦ termModel ⟧

nonempty : Structure.nonempty henkinizedTermModel
nonempty = reductNonempty $ TermModel.nonempty $ ∞-theory-hasEnoughConstants T
