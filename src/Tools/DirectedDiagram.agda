{-# OPTIONS --cubical --safe #-}

module Tools.DirectedDiagram where

open import Cubical.Core.Primitives hiding (_≡_)
open import Cubical.Foundations.Prelude using (isSet)
open import Cubical.Data.Equality using (eqToPath; pathToEq; funExt)
open import Cubical.HITs.SetQuotients using (_/_; [_]; eq/; squash/; rec)

open import Data.Product using (_×_; ∃-syntax)
open import Function using (_∘_; _$_)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning

private variable
  u v w : Level

record DirectedType : Type (ℓ-suc u) where
  field
    Carrier : Type u
    isSetCarrier : isSet Carrier
    _~_ : Rel Carrier ℓ-zero
    ~-refl : Reflexive _~_
    ~-trans : Transitive _~_
    directed : ∀ x y → ∃[ z ] x ~ z × y ~ z

record DirectedDiagram (D : DirectedType {u}) : Type (ℓ-max u $ ℓ-suc v) where
  open DirectedType D
  field
    obj : Carrier → Type v
    morph : ∀ {i j} → .(i ~ j) → obj i → obj j
    functorial : ∀ {i j k} .{f₁ : i ~ j} .{f₂ : j ~ k} .{f₃ : i ~ k}
      → (morph f₃) ≡ (morph f₂) ∘ (morph f₁)
  
  Coproduct : Type (ℓ-max u v)
  Coproduct = ∃[ i ] obj i

  _≃_ : Rel Coproduct (ℓ-max u v)
  (i , x) ≃ (j , y) = ∃[ k ] Σ[ z ∈ obj k ] Σ[ i~k ∈ i ~ k ] Σ[ j~k ∈ j ~ k ]
    morph i~k x ≡ z × morph j~k y ≡ z

  ≃-refl : Reflexive _≃_
  ≃-refl {i , x} = i , morph ~-refl x , ~-refl , ~-refl , refl , refl

  ≃-sym : Symmetric _≃_
  ≃-sym (k , z , i~k , j~k , eqx , eqy) = k , z , j~k , i~k , eqy , eqx

  ≃-trans : Transitive _≃_
  ≃-trans {i , x} {j , y} {k , z}
    (l₁ , w₁ , i~l₁ , j~l₁ , x₁≡w₁ , y₁≡w₁)
    (l₂ , w₂ , j~l₂ , k~l₂ , y₂≡w₂ , z₂≡w₂) =
    l₃ , (morph j~l₃ y) , i~l₃ , k~l₃ , x₃≡y₃ , z₃≡y₃ where
      l₃ = fst $ directed l₁ l₂
      l₁~l₃ = fst $ snd $ directed l₁ l₂
      l₂~l₃ = snd $ snd $ directed l₁ l₂
      i~l₃ = ~-trans i~l₁ l₁~l₃
      j~l₃ = ~-trans j~l₁ l₁~l₃
      k~l₃ = ~-trans k~l₂ l₂~l₃
      i→l₁→l₃ : morph i~l₃ ≡ morph l₁~l₃ ∘ morph i~l₁
      i→l₁→l₃ = functorial
      j→l₁→l₃ : morph j~l₃ ≡ morph l₁~l₃ ∘ morph j~l₁
      j→l₁→l₃ = functorial
      j→l₂→l₃ : morph j~l₃ ≡ morph l₂~l₃ ∘ morph j~l₂
      j→l₂→l₃ = functorial
      k→l₂→l₃ : morph k~l₃ ≡ morph l₂~l₃ ∘ morph k~l₂
      k→l₂→l₃ = functorial
      x₁≡y₁ : morph i~l₁ x ≡ morph j~l₁ y
      x₁≡y₁ = trans x₁≡w₁ $ sym y₁≡w₁
      z₂≡y₂ : morph k~l₂ z ≡ morph j~l₂ y
      z₂≡y₂ = trans z₂≡w₂ $ sym y₂≡w₂
      x₃≡y₃ : morph i~l₃ x ≡ morph j~l₃ y
      x₃≡y₃ rewrite i→l₁→l₃ | j→l₁→l₃ | x₁≡y₁ = refl
      z₃≡y₃ : morph k~l₃ z ≡ morph j~l₃ y
      z₃≡y₃ rewrite j→l₂→l₃ | k→l₂→l₃ | z₂≡y₂ = refl

  Colimit = Coproduct / _≃_

record Cocone {D} (F : DirectedDiagram {u} {v} D) : Type (ℓ-max u $ ℓ-max v $ ℓ-suc w) where
  open DirectedType D
  open DirectedDiagram F
  field
    Vertex : Type w
    isSetVertex : isSet Vertex
    map : ∀ i → obj i → Vertex
    compat : ∀ {i j} (f : i ~ j) → map i ≡ (map j ∘ morph f)

  universalMap : Colimit → Vertex
  universalMap = rec isSetVertex (λ (i , x) → map i x)
    λ (i , x) (j , y) (k , z , i~k , j~k , H₁ , H₂) → eqToPath $ begin
      map i x             ≡⟨ cong-app (compat i~k) x ⟩
      map k (morph i~k x) ≡⟨ cong (map k) (trans H₁ $ sym $ H₂) ⟩
      map k (morph j~k y) ≡˘⟨ cong-app (compat j~k) y ⟩
      map j y             ∎

coconeOfColimit : ∀ {u v D} (F : DirectedDiagram {u} {v} D) → Cocone F
coconeOfColimit {u} {v} {D} F = record
  { Vertex = Colimit
  ; isSetVertex = squash/
  ; map = λ i x → [ i , x ]
  ; compat = λ {_} {j} f → funExt λ x → pathToEq $
      eq/ _ _ (j , morph f x , f , ~-refl , refl , (sym $ cong-app functorial x))
  } where open DirectedType {u} D
          open DirectedDiagram F
