{-# OPTIONS --cubical --safe #-}

open import FOL.Language
module FOL.Structure.Base (ℒ : Language {u}) where
open import FOL.Interpretation ℒ using (Structure) public
