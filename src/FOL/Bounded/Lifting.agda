{-# OPTIONS --cubical --safe #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
module FOL.Bounded.Lifting ⦃ em : EM ⦄ (ℒ : Language {u}) where
import FOL.Base ⦃ em ⦄ ℒ as Free
open import FOL.Bounded.Base ⦃ em ⦄ ℒ

open import Data.Nat using (ℕ; _+_; _<?_)
open import Data.Nat.Properties
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import StdlibExt.Data.Fin using (Fin; toℕ; _↑ˡ_; _↑ʳ_; cast; toℕ-cast-↑ʳ)

private variable
  n : ℕ

_↑[_]_ : (t : Termₗ n l) (m n' : ℕ) → Termₗ (n + n') l
var k     ↑[ m ] n' with toℕ k <? m
... | yes _ = var (k ↑ˡ n')
... | no  _ = var (cast (+-comm n' _) (n' ↑ʳ k))
func f    ↑[ m ] n' = func f
app t₁ t₂ ↑[ m ] n' = app (t₁ ↑[ m ] n') (t₂ ↑[ m ] n')

_↑_ : (t : Termₗ n l) (n' : ℕ) → Termₗ (n + n') l
t ↑ n' = t ↑[ 0 ] n'

unbound↑ : (t : Termₗ n l) (m : ℕ) → unboundₜ (t ↑ m) ≡ unboundₜ t Free.↑ m
unbound↑ (var k)      m = cong Free.var (toℕ-cast-↑ʳ k)
unbound↑ (func f)     m = refl
unbound↑ (app t₁ t₂)  m = cong₂ Free.app (unbound↑ t₁ m) (unbound↑ t₂ m)
