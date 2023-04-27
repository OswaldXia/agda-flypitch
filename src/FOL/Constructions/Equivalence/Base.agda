{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import FOL.Syntactics using (Theory)
module FOL.Constructions.Equivalence.Base {ℒ : Language {u}} (T : Theory ℒ) where

open import FOL.Base ℒ hiding (_⇒_)
open import FOL.Syntactics ℒ
open import FOL.Lemmas.Lifting ℒ
open import FOL.Lemmas.Substitution ℒ

open import Agda.Primitive using (lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import StdlibExt.Data.Vec using (Vec; []; _∷_; map; map-∘-id)
open import Function using (_$_; _∘_; _∘₂_; flip)
open import Relation.Binary using (_⇒_ ;Rel; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; cong₂; subst₂; refl; sym; trans)
open import CubicalExt.Functions.Logic.Iff

private
  variable
    t t₁ t₂ t₃ : Term
    f f₁ f₂ : Termₗ 1
    r r₁ r₂ : Formulaₗ l
  𝐯₀ = var 0

infix 4 _≋_ _⟷_ _⟺_

_≋_ : Rel Term (lsuc u)
t₁ ≋ t₂ = T ⊢ t₁ ≈ t₂

≋-refl : Reflexive _≋_
≋-refl = ≈-refl

≋-sym : Symmetric _≋_
≋-sym {t₁} {t₂} t₁≋t₂ = ≈-≡-subst (𝐯₀ ≈ t₁ ↑ 1) t₁≋t₂ H₁ H₂ where
  H₁ : T ⊢ (𝐯₀ ≈ t₁ ↑ 1) [ 0 ≔ t₁ ]
  H₁ rewrite ↑1[≔] t₁ t₁ | ↑0 t₁ = ≋-refl
  H₂ : (𝐯₀ ≈ t₁ ↑ 1) [ 0 ≔ t₂ ] ≡ t₂ ≈ t₁
  H₂ rewrite ↑1[≔] t₁ t₂ | ↑0 t₂ = refl

≋-trans : Transitive _≋_
≋-trans {t₁} {t₂} {t₃} t₁≋t₂ t₂≋t₃ = ≈-≡-subst (t₁ ↑ 1 ≈ 𝐯₀) t₂≋t₃ H₁ H₂ where
  H₁ : T ⊢ (t₁ ↑ 1 ≈ 𝐯₀) [ 0 ≔ t₂ ]
  H₁ rewrite ↑1[≔] t₁ t₂ | ↑0 t₂ = t₁≋t₂
  H₂ : (t₁ ↑ 1 ≈ 𝐯₀) [ 0 ≔ t₃ ] ≡ t₁ ≈ t₃
  H₂ rewrite ↑1[≔] t₁ t₃ | ↑0 t₃ = refl

≋-cong/ : (s : Term) → t₁ ≋ t₂ → s [ 0 ≔ t₁ ]ₜ ≋ s [ 0 ≔ t₂ ]ₜ
≋-cong/ {t₁} {t₂} s t₁≋t₂ = ≈-≡-subst (s [ 0 ≔ t₁ ]ₜ ↑ 1 ≈ s) t₁≋t₂ H₁ H₂ where
  H₁ : T ⊢ ((s [ 0 ≔ t₁ ]ₜ) ↑ 1 ≈ s) [ 0 ≔ t₁ ]
  H₁ rewrite ↑1[≔] (s [ 0 ≔ t₁ ]ₜ) t₁ = ≋-refl
  H₂ : ((s [ 0 ≔ t₁ ]ₜ) ↑ 1 ≈ s) [ 0 ≔ t₂ ] ≡ (s [ 0 ≔ t₁ ]ₜ) ≈ (s [ 0 ≔ t₂ ]ₜ)
  H₂ rewrite ↑1[≔] (s [ 0 ≔ t₁ ]ₜ) t₂ = refl

≋-cong : t₁ ≋ t₂ → app f t₁ ≋ app f t₂
≋-cong {t₁} {t₂} {f} t₁≋t₂ =
  subst₂ (λ x y → app f x ≋ app f y) (↑0 t₁) (↑0 t₂) $
  subst₂ (λ f g → app f (t₁ ↑ 0) ≋ app g (t₂ ↑ 0)) (↑1[≔] f t₁) (↑1[≔] f t₂)
    (≋-cong/ (app (f ↑ 1) 𝐯₀) t₁≋t₂)

_≋ᶠ_ : Rel (Termₗ l) (lsuc u)
_≋ᶠ_ {l} f₁ f₂ = ∀ xs → apps f₁ xs ≋ apps f₂ xs

≋ᶠ-refl : Reflexive $ _≋ᶠ_ {l}
≋ᶠ-refl _ = ≋-refl

≋ᶠ-sym : Symmetric $ _≋ᶠ_ {l}
≋ᶠ-sym H xs = ≋-sym $ H xs

≋ᶠ-trans : Transitive $ _≋ᶠ_ {l}
≋ᶠ-trans H₁ H₂ xs = ≋-trans (H₁ xs) (H₂ xs)

≋-funExt⁻ : f₁ ≋ᶠ f₂ → app f₁ t ≋ app f₂ t
≋-funExt⁻ {t = t} f₁≋f₂ = f₁≋f₂ (t ∷ [])

≋-app : f₁ ≋ᶠ f₂ → t₁ ≋ t₂ → app f₁ t₁ ≋ app f₂ t₂
≋-app f₁≋f₂ t₁≋t₂ = ≋-trans (≋-funExt⁻ f₁≋f₂) (≋-cong t₁≋t₂)

≋ᶠ-app : {f₁ f₂ : Termₗ (suc l)} {t₁ t₂ : Term}
  → f₁ ≋ᶠ f₂ → t₁ ≋ t₂ → app f₁ t₁ ≋ᶠ app f₂ t₂
≋ᶠ-app {l} {f₁} {f₂} {t₁} {t₂} f₁≋f₂ t₁≋t₂ xs = ≋-trans (f₁≋f₂ (t₁ ∷ xs)) (
  subst₂ (λ xs₁ xs₂ → apps _ xs₁ ≋ apps _ xs₂)
    (map-∘-id _ _ (λ f → ↑1[≔] f t₁) xs)
    (map-∘-id _ _ (λ f → ↑1[≔] f t₂) xs) $
  subst₂ (λ f g → apps (app f t₁) _ ≋ apps (app g t₂) _)
    (↑1[≔] f₂ t₁) (↑1[≔] f₂ t₂) $
  subst₂ (λ t s → apps (app ((f₂ ↑ 1) [ 0 ≔ t₁ ]ₜ) t) (map (_[ 0 ≔ t₁ ]ₜ) (map (_↑[ 0 ] 1) xs))
                ≋ apps (app ((f₂ ↑ 1) [ 0 ≔ t₂ ]ₜ) s) (map (_[ 0 ≔ t₂ ]ₜ) (map (_↑[ 0 ] 1) xs)))
    (↑0 t₁) (↑0 t₂) $
  subst₂ _≋_
    (apps[≔] (app (f₂ ↑ 1) 𝐯₀) (map (_↑[ 0 ] 1) xs) t₁ 0)
    (apps[≔] (app (f₂ ↑ 1) 𝐯₀) (map (_↑[ 0 ] 1) xs) t₂ 0)
    (≋-cong/ (apps (f₂ ↑ 1) (𝐯₀ ∷ map (_↑ 1) xs)) t₁≋t₂)
  )

_⟷_ : Rel Formula (lsuc u)
φ₁ ⟷ φ₂ = T ⊢ φ₁ ↔ T ⊢ φ₂

⟷-refl : Reflexive _⟷_
⟷-refl = ↔-refl

⟷-sym : Symmetric _⟷_
⟷-sym = ↔-sym

⟷-trans : Transitive _⟷_
⟷-trans = ↔-trans

_⟺_ : Rel Formula (lsuc u)
φ₁ ⟺ φ₂ = T ⊢ φ₁ ⇔ φ₂

⟺-refl : Reflexive _⟺_
⟺-refl = ⇔-refl

⟺-sym : Symmetric _⟺_
⟺-sym = ⇔-sym

⟺-trans : Transitive _⟺_
⟺-trans = ⇔-trans

⟺⇒⟷ : _⟺_ ⇒ _⟷_
⟺⇒⟷ x⟺y = →: (⇒-elim $ ⇒-intro $ ⇔-elimₗ x⟺y) ←: (⇒-elim $ ⇒-intro $ ⇔-elimᵣ x⟺y)

⟺-cong/ : (φ : Formula) → t₁ ≋ t₂ → φ [ 0 ≔ t₁ ] ⟺ φ [ 0 ≔ t₂ ]
⟺-cong/ φ t₁≋t₂ = ⇔-intro (subst (weakening1 t₁≋t₂) axiom1) (subst (weakening1 $ ≋-sym t₁≋t₂) axiom1)

⟺-cong : t₁ ≋ t₂ → appᵣ r t₁ ⟺ appᵣ r t₂
⟺-cong {t₁} {t₂} {r} t₁≋t₂ =
  subst₂ (λ x y → appᵣ r x ⟺ appᵣ r y) (↑0 t₁) (↑0 t₂) $
  subst₂ (λ q r → appᵣ q (t₁ ↑ 0) ⟺ appᵣ r (t₂ ↑ 0)) (↥1[≔] r t₁) (↥1[≔] r t₂)
    (⟺-cong/ (appᵣ (r ↥ 1) 𝐯₀) t₁≋t₂)

⟷-cong/ : (φ : Formula) → t₁ ≋ t₂ → φ [ 0 ≔ t₁ ] ⟷ φ [ 0 ≔ t₂ ]
⟷-cong/ = ⟺⇒⟷ ∘₂ ⟺-cong/

⟷-cong : t₁ ≋ t₂ → appᵣ r t₁ ⟷ appᵣ r t₂
⟷-cong = ⟺⇒⟷ ∘ ⟺-cong

_≋ʳ_ : Rel (Formulaₗ l) (lsuc u)
_≋ʳ_ {l} r₁ r₂ = ∀ xs → appsᵣ r₁ xs ⟺ appsᵣ r₂ xs

≋ʳ-refl : Reflexive $ _≋ʳ_ {l}
≋ʳ-refl _ = ⟺-refl

≋ʳ-sym : Symmetric $ _≋ʳ_ {l}
≋ʳ-sym H xs = ⟺-sym $ H xs

≋ʳ-trans : Transitive $ _≋ʳ_ {l}
≋ʳ-trans H₁ H₂ xs = ⟺-trans (H₁ xs) (H₂ xs)

⟺-relExt⁻ : r₁ ≋ʳ r₂ → appᵣ r₁ t ⟺ appᵣ r₂ t
⟺-relExt⁻ {t = t} r₁≋r₂ = r₁≋r₂ (t ∷ [])

⟺-appᵣ : r₁ ≋ʳ r₂ → t₁ ≋ t₂ → appᵣ r₁ t₁ ⟺ appᵣ r₂ t₂
⟺-appᵣ r₁≋r₂ t₁≋t₂ = ⟺-trans (⟺-relExt⁻ r₁≋r₂) (⟺-cong t₁≋t₂)

⟷-relExt⁻ : r₁ ≋ʳ r₂ → appᵣ r₁ t ⟷ appᵣ r₂ t
⟷-relExt⁻ = ⟺⇒⟷ ∘ ⟺-relExt⁻

⟷-appᵣ : r₁ ≋ʳ r₂ → t₁ ≋ t₂ → appᵣ r₁ t₁ ⟷ appᵣ r₂ t₂
⟷-appᵣ = ⟺⇒⟷ ∘₂ ⟺-appᵣ

≋ʳ-appᵣ : {r₁ r₂ : Formulaₗ (suc l)} {t₁ t₂ : Term}
  → r₁ ≋ʳ r₂ → t₁ ≋ t₂ → appᵣ r₁ t₁ ≋ʳ appᵣ r₂ t₂
≋ʳ-appᵣ {l} {r₁} {r₂} {t₁} {t₂} r₁≋r₂ t₁≋t₂ xs = ⟺-trans (r₁≋r₂ (t₁ ∷ xs)) $
  ≈-≡-subst (appsᵣ (r₂ ↥ 1) (map (_↑ 1) (t₁ ∷ xs)) ⇔ appsᵣ (r₂ ↥ 1) (𝐯₀ ∷ map (_↑ 1) xs)) t₁≋t₂ H₁ H₂ where
    H₁ : T ⊢ (appsᵣ (appᵣ (r₂ ↥ 1) (t₁ ↑ 1)) (map (_↑ 1) xs) ⇔ appsᵣ (appᵣ (r₂ ↥ 1) 𝐯₀) (map (_↑ 1) xs)) [ 0 ≔ t₁ ]
    H₁ rewrite appsᵣ[≔] (appᵣ (r₂ ↥ 1) (t₁ ↑ 1)) (map (_↑ 1) xs) t₁ 0
             | appsᵣ[≔] (appᵣ (r₂ ↥ 1) 𝐯₀) (map (_↑ 1) xs) t₁ 0
             | map-∘-id _[ 0 ≔ t₁ ]ₜ (_↑ 1) (λ f → ↑1[≔] f t₁) xs
             | ↑1[≔] t₁ t₁ | ↑0 t₁
             = ⟺-refl
    H₂ : (appsᵣ (appᵣ (r₂ ↥ 1) (t₁ ↑ 1)) (map (_↑ 1) xs) ⇔ appsᵣ (appᵣ (r₂ ↥ 1) 𝐯₀) (map (_↑ 1) xs)) [ 0 ≔ t₂ ] ≡ appsᵣ (appᵣ r₂ t₁) xs ⇔ appsᵣ (appᵣ r₂ t₂) xs
    H₂ rewrite appsᵣ[≔] (appᵣ (r₂ ↥ 1) (t₁ ↑ 1)) (map (_↑ 1) xs) t₂ 0
             | appsᵣ[≔] (appᵣ (r₂ ↥ 1) 𝐯₀) (map (_↑ 1) xs) t₂ 0
             | map-∘-id _[ 0 ≔ t₂ ]ₜ (_↑ 1) (λ f → ↑1[≔] f t₂) xs
             | ↥1[≔] r₂ t₂ | ↑1[≔] t₁ t₂ | ↑0 t₂
             = refl
