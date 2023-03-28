{-# OPTIONS --cubical --safe #-}

module CubicalExt.Data.Nat where

open import Cubical.Data.Nat using (ℕ; isSetℕ)
open import CubicalExt.Axiom.UniquenessOfIdentity.Loop using (UIP; isSet→UIP)

ℕ-UIP : UIP ℕ
ℕ-UIP = isSet→UIP isSetℕ
