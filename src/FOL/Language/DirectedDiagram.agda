{-# OPTIONS --cubical --safe #-}

module FOL.Language.DirectedDiagram where

open import FOL.Language hiding (u)
open import FOL.Language.Homomorphism renaming (_∘_ to _◯_)
open import Tools.DirectedDiagram

open import Cubical.Core.Primitives using (Type; Level; ℓ-suc; ℓ-max)
open import Cubical.Foundations.HLevels using (isSetΣ)
open import Cubical.HITs.SetQuotients using (_/_; [_]; squash/; rec)

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

private variable
  u v w : Level

record DirectedDiagramLanguage (D : DirectedType {u}) : Type (ℓ-max (ℓ-suc u) (ℓ-suc v)) where
  open DirectedType D
  open Language
  field
    obj : Carrier → Language {ℓ-max u v}
    morph : ∀ {i j} → .(i ~ j) → obj i ⟶ obj j
    functorial : ∀ {i j k} .{f₁ : i ~ j} .{f₂ : j ~ k} .{f₃ : i ~ k}
      → (morph f₃) ≡ (morph f₂) ◯ (morph f₁)

  module _ (n : ℕ) where
    open _⟶_

    functionsᴰ : DirectedDiagram {u} {ℓ-max u v} D
    functionsᴰ = record
      { obj = λ i → obj i .functions n
      ; morph = λ i~j → funMorph (morph i~j)
      ; functorial = cong (λ f → funMorph f) functorial
      }

    relationsᴰ : DirectedDiagram {u} {ℓ-max u v} D
    relationsᴰ = record
      { obj = λ i → obj i .relations n
      ; morph = λ i~j → relMorph (morph i~j)
      ; functorial = cong (λ f → relMorph f) functorial
      }

  CoproductLanguage : Language
  CoproductLanguage = record
    { functions = Coproduct ∘ functionsᴰ
    ; relations = Coproduct ∘ relationsᴰ
    ; isSetFunctions = λ n → isSetΣ isSetCarrier λ i → isSetFunctions (obj i) n
    ; isSetRelations = λ n → isSetΣ isSetCarrier λ i → isSetRelations (obj i) n
    } where open DirectedDiagram using (Coproduct)

  ColimitLanguage : Language
  ColimitLanguage = record
    { functions = λ n → funcs n / _≃_ (functionsᴰ n)
    ; relations = λ n → rels  n / _≃_ (relationsᴰ n)
    ; isSetFunctions = λ _ → squash/
    ; isSetRelations = λ _ → squash/
    } where open DirectedDiagram using (_≃_)
            open Language CoproductLanguage renaming (functions to funcs; relations to rels)

  canonicalMorph : ∀ i → obj i ⟶ ColimitLanguage
  canonicalMorph i = record
    { funMorph = λ {n} f → [ i , morph (functionsᴰ n) ~-refl f ]
    ; relMorph = λ {n} r → [ i , morph (relationsᴰ n) ~-refl r ]
    } where open DirectedDiagram using (morph)

record CoconeLanguage {D} (F : DirectedDiagramLanguage {u} {v} D) : Type (ℓ-max (ℓ-suc u) (ℓ-suc v)) where
  open DirectedType D
  open DirectedDiagramLanguage F

  field
    Vertex : Language {ℓ-max u v}
    map : ∀ i → obj i ⟶ Vertex
    compat : ∀ {i j} (f : i ~ j) → map i ≡ map j ◯ morph f
{--
  universalMap : ColimitLanguage ⟶ Vertex
  universalMap = record
    { funMorph = rec {!   !} {!   !} {!   !}
    ; relMorph = {!   !}
    }
--}
