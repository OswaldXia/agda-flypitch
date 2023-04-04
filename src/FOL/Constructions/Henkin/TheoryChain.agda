{-# OPTIONS --cubical --safe #-}

module FOL.Constructions.Henkin.TheoryChain u where
open import FOL.Constructions.Henkin.Base
open import FOL.Constructions.Henkin.LanguageChain u
open import FOL.Language hiding (u)
open Language {u}

open import FOL.Bounded.Base using (Formula; Sentence; Theory)
import FOL.Language.Homomorphism as LHom

open import Data.Nat using (ℕ; zero; suc)
open import Function using (_$_)
open import StdlibExt.Relation.Unary using (_∪_; _⟦_⟧; ⋃_; replacement-syntax)

witnessOf : Formula ℒ 1 → Constant $ languageStep ℒ
witnessOf = witness

[_witnessing_] : Constant ℒ → Formula ℒ 1 → Sentence ℒ
[_witnessing_] {ℒ} c φ = (∃' φ) ⇒ φ [ const c / 0 ] where
  open import FOL.Bounded.Base ℒ using (∃'_; _⇒_; const)
  open import FOL.Bounded.Substitution ℒ

theoryStep : Theory ℒ → Theory $ languageStep ℒ
theoryStep {ℒ} Γ = theoryMorph Γ ∪ ｛ [ witnessOf φ witnessing formulaMorph φ ] ∣ φ ∈ Formula ℒ 1 ｝
  where open LHom.Bounded languageMorph

[_]-theory : ∀ n → Theory ℒ → Theory $ [ n ]-language ℒ
[ zero ]-theory T = T
[ suc n ]-theory T = theoryStep $ [ n ]-theory T

[_]-∞-theory : ∀ n → Theory ℒ → Theory $ ∞-language ℒ
[ n ]-∞-theory T = sentenceMorph ⟦ [ n ]-theory T ⟧
  where open LHom.Bounded (languageCanonicalMorph n)

∞-theory : Theory ℒ → Theory $ ∞-language ℒ
∞-theory T = ⋃ (λ n → [ n ]-∞-theory T)
