{-# OPTIONS --cubical --safe #-}

module Tools.DirectedDiagram where

open import Cubical.Core.Primitives renaming (_≡_ to _≡ₚ_)
open import Cubical.Foundations.Prelude using (isProp; isSet; isProp→isSet; toPathP; isPropIsProp)
open import Cubical.Data.Equality using (eqToPath; pathToEq; funExt; reflPath)
open import Cubical.Data.Sigma using (∃-syntax) renaming (_×_ to infixr 3 _×_)
open import Cubical.Data.Nat using (isSetℕ)
open import Cubical.HITs.SetQuotients as Quot using (_/_; [_]; eq/; squash/; rec; []surjective)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; squash₁; elim→Set; elim2→Set)
open import Cubical.Relation.Binary
open BinaryRelation using (isRefl; isSym; isTrans; isEquivRel)

open import StdlibExt.Data.Nat using (ℕ; _+_; _≤₃_; ≤⇒≤₃; ≤₃⇒≤)
open import Data.Nat.Properties
open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning

private variable
  u v w : Level

record DirectedType : Type (ℓ-suc u) where
  field
    Carrier : Type u
    isSetCarrier : isSet Carrier
    _~_ : Rel Carrier Carrier ℓ-zero
    isRefl~ : isRefl _~_
    isTrans~ : isTrans _~_
    directed : ∀ x y → Σ[ z ∈ _ ] x ~ z × y ~ z
  ~-refl = λ {a} → isRefl~ a
  ~-trans = λ {a b c} → isTrans~ a b c

ℕᴰ : DirectedType
ℕᴰ = record
  { Carrier = ℕ
  ; isSetCarrier = isSetℕ
  ; _~_ = _≤₃_
  ; isRefl~ = λ _ → ≤⇒≤₃ ≤-refl
  ; isTrans~ = λ _ _ _ p q → ≤⇒≤₃ $ ≤-trans (≤₃⇒≤ p) (≤₃⇒≤ q)
  ; directed = λ x y → x + y , ≤⇒≤₃ (m≤m+n _ _) , ≤⇒≤₃ (m≤n+m _ _)
  }

record DirectedDiagram (D : DirectedType {u}) : Type (ℓ-max u $ ℓ-suc v) where
  open DirectedType D
  field
    obj : Carrier → Type v
    morph : ∀ {i j} → .(i ~ j) → obj i → obj j
    functorial : ∀ {i j k} .{f₁ : i ~ j} .{f₂ : j ~ k} .{f₃ : i ~ k}
      → (morph f₃) ≡ (morph f₂) ∘ (morph f₁)
  
  Coproduct : Type (ℓ-max u v)
  Coproduct = Σ[ i ∈ _ ] obj i

  _≃_ : Rel Coproduct Coproduct (ℓ-max u v)
  (i , x) ≃ (j , y) = ∃[ k ∈ _ ] Σ[ z ∈ obj k ] Σ[ i~k ∈ i ~ k ] Σ[ j~k ∈ j ~ k ]
    morph i~k x ≡ z × morph j~k y ≡ z

  isRefl≃ : isRefl _≃_
  isRefl≃ (i , x) = ∣ i , morph ~-refl x , ~-refl , ~-refl , refl , refl ∣₁
  ≃-refl = λ {a} → isRefl≃ a

  isSym≃ : isSym _≃_
  isSym≃ _ _ = elim→Set (λ _ → isProp→isSet squash₁)
    (λ (k , z , i~k , j~k , eqx , eqy) → ∣ k , z , j~k , i~k , eqy , eqx ∣₁)
    (λ _ _ → squash₁ _ _)

  isTrans≃ : isTrans _≃_
  isTrans≃ (i , x) (j , y) (k , z) = elim2→Set (λ _ _ → isProp→isSet squash₁) f
    (λ _ _ _ → squash₁ _ _)
    (λ _ _ _ → squash₁ _ _)
    (λ _ _ _ _ → toPathP $ isProp→isSet squash₁ _ _ _ _)
    where
    f : ∀ ix jy → (i , x) ≃ (k , z)
    f (l₁ , w₁ , i~l₁ , j~l₁ , x₁≡w₁ , y₁≡w₁)
      (l₂ , w₂ , j~l₂ , k~l₂ , y₂≡w₂ , z₂≡w₂) =
      ∣ l₃ , morph j~l₃ y , i~l₃ , k~l₃ , x₃≡y₃ , z₃≡y₃ ∣₁
      where
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

  isEquivRel≃ : isEquivRel _≃_
  isEquivRel≃ = record
    { reflexive = isRefl≃
    ; symmetric = isSym≃
    ; transitive = isTrans≃
    }

  Colimit = Coproduct / _≃_

  canonicalMorph : ∀ i → obj i → Colimit
  canonicalMorph i x = [ i , x ]

  representative : (x : Colimit) → ∃[ a ∈ Coproduct ] [ a ] ≡ₚ x
  representative = []surjective

  effective : ∀ {a b} → [ a ] ≡ₚ [ b ] → a ≃ b
  effective = Quot.effective (λ _ _ → squash₁) isEquivRel≃ _ _

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
    λ (i , x) (j , y) → elim→Set (λ _ → isProp→isSet (isSetVertex _ _))
      (λ (k , z , i~k , j~k , H₁ , H₂) → eqToPath $ begin
        map i x             ≡⟨ cong-app (compat i~k) x ⟩
        map k (morph i~k x) ≡⟨ cong (map k) (trans H₁ $ sym $ H₂) ⟩
        map k (morph j~k y) ≡˘⟨ cong-app (compat j~k) y ⟩
        map j y             ∎)
      (λ _ _ → isSetVertex _ _ _ _)

coconeOfColimit : ∀ {u v D} (F : DirectedDiagram {u} {v} D) → Cocone F
coconeOfColimit {u} {v} {D} F = record
  { Vertex = Colimit
  ; isSetVertex = squash/
  ; map = λ i x → [ i , x ]
  ; compat = λ {_} {j} f → funExt λ x → pathToEq $
      eq/ _ _ ∣ j , morph f x , f , ~-refl , refl , (sym $ cong-app functorial x) ∣₁
  } where open DirectedType {u} D
          open DirectedDiagram F
