{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Language
open import CubicalExt.Axiom.ExcludedMiddle
open import FOL.Bounded.Syntactics using (Theory)
open import FOL.PropertiesOfTheory using (complete; hasEnoughConstants)
module FOL.Constructions.TermModel.Properties ⦃ em : EM ⦄ {ℒ : Language {u}} {T : Theory ℒ}
  (H₁ : complete ℒ T) (H₂ : hasEnoughConstants ℒ T) where
open import CubicalExt.Classical ⦃ em ⦄ using (byContra)
open Language ℒ

open import FOL.Constructions.TermModel.Base T
open TermModel hiding (Domain; func; rel)

open import FOL.Structure.Base using (Structure)
open Structure termModel using (Domain; relMap)

open import FOL.PropertiesOfTheory ℒ
open Complete H₁ using (⇒-intro; ~-intro)

module Free where
  open import FOL.Base ℒ public
  open import FOL.Syntactics ℒ public
open Free.Formulaₗ public
open Free using (⇒-elim; ∀-elim; ~∀→∃~)

open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Syntactics ℒ
open import FOL.Bounded.Semantics ℒ
open import FOL.Bounded.Lemmas.Realization termModel
open import FOL.Bounded.Lemmas.QuantifierCounting ℒ
open import FOL.Bounded.Manipulations.Substitution.Closed ℒ
open import FOL.Constructions.Equivalence.BoundedTruncated T

open import Cubical.Foundations.Prelude hiding (~_)
  renaming (_,_ to infix 5 _,_) renaming (subst to ≡-subst)
open import Cubical.Foundations.HLevels using (isSetHProp)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import CubicalExt.Foundations.Powerset* using (_∈_)
open import Cubical.Functions.Logic using (∥_∥ₚ)
open import CubicalExt.Functions.Logic.Iff
open import CubicalExt.Data.Vec using (quotientBeta)
open import Cubical.Data.Empty using (isProp⊥)
open import Cubical.Data.Sigma using (∃-syntax)
open import Cubical.HITs.SetQuotients using (eq/; squash/; elimProp; effective)
  renaming ([_] to [_]/)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; elim; elim2; map2)
  renaming (map to map₁)
open import Cubical.Relation.Nullary using (¬_)

open import Data.Nat
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; <-pred)
open import Data.Vec using (Vec; []; _∷_; [_]; map)
open import Function using (_∘_; _∘₂_; _$_)
open import Relation.Binary.PropositionalEquality
  using () renaming (subst to substEq; sym to symEq)

private variable
  n : ℕ

module _ where
  open PreRealizer termModel

  ≡preFunc : (f : ClosedTermₗ l) (xs : Vec ClosedTerm l) →
    realizeₜ [] f (map [_]/ xs) ≡ preFunc f xs
  ≡preFunc (func f) = quotientBeta ≋-refl squash/ (preFunc (func f)) (preFunc-pointwiseEq (func f))
  ≡preFunc (app t₁ t₂) xs =
    realizeₜ [] t₁ (realizeₜ [] t₂ [] ∷ map [_]/ xs) ≡⟨ cong (λ x → realizeₜ [] t₁ (x ∷ _)) (≡preFunc t₂ []) ⟩
    realizeₜ [] t₁ ([ t₂ ]/ ∷ map [_]/ xs)           ≡⟨⟩
    realizeₜ [] t₁ (map [_]/ (t₂ ∷ xs))              ≡⟨ ≡preFunc t₁ (t₂ ∷ xs) ⟩
    [ apps t₁ (t₂ ∷ xs)]/                            ∎

module _ where
  open ClosedRealizer termModel

  ≡preRel : (R : ℜ l) (xs : Vec ClosedTerm l) →
    relMap R (map [_]/ xs) ≡ preRel (rel R) xs , squash₁
  ≡preRel R = quotientBeta ≋-refl isSetHProp _
    λ x → hPropExt $ preRel-pointwiseIff (rel R) x

  ≡[]/ : (t : ClosedTerm) → realizeₜ t ≡ [ t ]/
  ≡[]/ t = ≡preFunc t []

  ≡map[]/ : (xs : Vec ClosedTerm l) → map realizeₜ xs ≡ map [_]/ xs
  ≡map[]/ [] = refl
  ≡map[]/ (x ∷ xs) = cong₂ _∷_ (≡[]/ x) (≡map[]/ xs)

module _ where
  open OpenedRealizer termModel
  open Opened

  ⊨[≔]↔ : (φ : Formula 1) (t : ClosedTerm) →
    termModel ⊨ˢ φ [≔ t ] ↔ realize [ [ t ]/ ] φ
  ⊨[≔]↔ φ t = ≡-subst (λ x → _ ⊨ˢ _ ↔ realize [ x ] φ) (≡[]/ t) (realize-subst-iff [] φ t)

termModelCompleteGuarded : (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  count∀ φ < n → T ⊦ appsᵣ φ xs ↔ termModel ⊨ˢ appsᵣ φ xs
termModelCompleteGuarded ⊥ [] _ =
  →: elim (λ _ → isProp-⊨ˢ termModel ⊥) (lift ∘ H₁ .fst)
  ←: λ ()
termModelCompleteGuarded (rel R) xs _ = hPropExt⁻ $ sym $
  termModel ⊨ˢ appsᵣ (rel R) xs , isProp-⊨ˢ _ _ ≡⟨ hPropExt $ Pre.realize-appsᵣ-iff [] (rel R) _ ⟩
  relMap R (map realizeₜ xs)                    ≡⟨ cong (relMap R) (≡map[]/ _) ⟩
  relMap R (map [_]/ xs)                        ≡⟨ ≡preRel _ _ ⟩
  preRel (rel R) xs , squash₁                   ≡⟨⟩
  ∥ T ⊢ appsᵣ (rel R) xs ∥ₚ                     ∎
  where open ClosedRealizer termModel using (realizeₜ)
termModelCompleteGuarded {_} {n} (appᵣ φ t) xs H with (unbound φ) in eq
... | rel _    = termModelCompleteGuarded φ (t ∷ xs) $ substEq (λ φ → Free.count∀ φ < n) (symEq eq) H
... | appᵣ _ _ = termModelCompleteGuarded φ (t ∷ xs) $ substEq (λ φ → Free.count∀ φ < n) (symEq eq) H
termModelCompleteGuarded (t₁ ≈ t₂) [] _ =
  T ⊦ t₁ ≈ t₂               ↔⟨ →: eq/ _ _ ←: effective isPropValued≋ isEquivRel≋ _ _ ⟩
  [ t₁ ]/ ≡ [ t₂ ]/         ↔≡⟨ subst2 (λ x y → (x ≡ y) ≡ (realizeₜ t₁ ≡ realizeₜ t₂)) (≡[]/ t₁) (≡[]/ t₂) refl ⟩
  realizeₜ t₁ ≡ realizeₜ t₂ ↔⟨⟩
  termModel ⊨ˢ t₁ ≈ t₂      ↔∎
  where open ClosedRealizer termModel using (realizeₜ)
termModelCompleteGuarded (φ₁ ⇒ φ₂) [] H =
  let IH₁ : T ⊦ appsᵣ φ₁ [] ↔ termModel ⊨ˢ appsᵣ φ₁ []
      IH₁ = termModelCompleteGuarded φ₁ [] $ ≤-trans (s≤s (m≤m+n _ _)) H
      IH₂ : T ⊦ appsᵣ φ₂ [] ↔ termModel ⊨ˢ appsᵣ φ₂ []
      IH₂ = termModelCompleteGuarded φ₂ [] $ ≤-trans (s≤s (m≤n+m _ _)) H
  in  →: (λ ⊦ ⊨ → to IH₂ $ map2 ⇒-elim ⊦ $ from IH₁ ⊨)
      ←: (λ ⊨ → ⇒-intro λ ⊦ → from IH₂ $ ⊨ $ to IH₁ ⊦)
termModelCompleteGuarded {_} {suc n} (∀' φ) [] H =
  →: (λ ⊦ → elimProp (λ _ → isPropRealize _ _)
    λ t → to (⊨[≔]↔ φ t)
      $ to (termModelCompleteGuarded (φ [≔ t ]) [] guard)
      $ substEq (_ Free.⊦_) (symEq (unbound-subst φ t))
      $ map₁ ∀-elim ⊦)
  ←: (λ ⊨ → byContra λ ¬⊦∀ → elim2 (λ _ _ → isProp⊥)
    (λ (c , wit) ¬⊢ → elim (λ _ → isProp⊥) (fst H₁ ∘ ⇒-elim (⇒-elim wit (~∀→∃~ ¬⊢)))
      $ from (termModelCompleteGuarded (φ [≔ const c ]) [] guard)
      $ from (⊨[≔]↔ φ (const c)) (⊨ _))
    (H₂ $ ~ φ) (~-intro ¬⊦∀))
  where guard : ∀ {t} → count∀ (φ [≔ t ]) < n
        guard = substEq (_< n) (symEq (count∀OfSubst _ _)) (<-pred H)
        open OpenedRealizer termModel using (isPropRealize)

termModelComplete : (φ : Sentenceₗ l) (xs : Vec ClosedTerm l) →
  T ⊦ appsᵣ φ xs ↔ termModel ⊨ˢ appsᵣ φ xs
termModelComplete φ xs = termModelCompleteGuarded φ xs (s≤s ≤-refl)

termModelWellDefined : termModel ⊨ᵀ T
termModelWellDefined φ φ∈T = to (termModelComplete φ []) ∣ axiom φ∈T ∣₁

-- completeness for complete theories with enough constanxs
open Implication (ℓ-suc u) using (_⊨_)
completeness : (φ : Sentence) → T ⊨ φ → T ⊦ φ
completeness φ T⊨φ = from (termModelComplete φ []) $
  T⊨φ termModel (nonempty H₂) termModelWellDefined
