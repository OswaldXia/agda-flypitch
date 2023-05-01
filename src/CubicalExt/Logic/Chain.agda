{-# OPTIONS --cubical --safe #-}

open import Cubical.Foundations.Prelude using (Type)
open import Cubical.Relation.Binary using (Rel)
module CubicalExt.Logic.Chain {ℓ ℓ'} {A : Type ℓ} (_≺_ : Rel A A ℓ') where


