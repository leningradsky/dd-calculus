{-# OPTIONS --safe --without-K #-}

{-
  DD-Calculus v0.1
  Module: Distinction.Morphisms
  
  Δ-Morphisms: functions preserving indistinguishability
-}

module Distinction.Morphisms where

open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid)
open import Function using (_∘_; id)

open import Distinction.Core
open import Distinction.Axioms
open import Distinction.Types

private
  variable
    ℓ : Level

-- ============================================================
-- 6.1 Δ-Morphisms
-- ============================================================

module _ {U : Set ℓ} (DD : DD-Structure U) where
  open DD-Structure DD
  
  -- A function is Δ-compatible if it preserves ~
  IsΔ-Compatible : (U → U) → Set ℓ
  IsΔ-Compatible f = ∀ {x y} → x ~ y → f x ~ f y
  
  -- Record packaging a Δ-morphism
  record Δ-Morphism : Set ℓ where
    field
      fun : U → U
      preserves-~ : IsΔ-Compatible fun
  
  -- ============================================================
  -- 7.1 Identity is Δ-compatible
  -- ============================================================
  
  id-Δ-compatible : IsΔ-Compatible id
  id-Δ-compatible x~y = x~y
  
  idΔ : Δ-Morphism
  idΔ = record
    { fun = id
    ; preserves-~ = id-Δ-compatible
    }
  
  -- ============================================================
  -- 7.2 Composition preserves Δ-compatibility
  -- ============================================================
  
  ∘-Δ-compatible : ∀ {f g} → 
    IsΔ-Compatible f → IsΔ-Compatible g → IsΔ-Compatible (f ∘ g)
  ∘-Δ-compatible f-ok g-ok x~y = f-ok (g-ok x~y)
  
  _∘Δ_ : Δ-Morphism → Δ-Morphism → Δ-Morphism
  f ∘Δ g = record
    { fun = Δ-Morphism.fun f ∘ Δ-Morphism.fun g
    ; preserves-~ = ∘-Δ-compatible (Δ-Morphism.preserves-~ f) 
                                    (Δ-Morphism.preserves-~ g)
    }

-- ============================================================
-- Morphism equality (setoid morphisms)
-- ============================================================

module _ {U : Set ℓ} (DD : DD-Structure U) where
  open DD-Structure DD
  open Δ-Morphism
  
  -- Two Δ-morphisms are equal if they agree on all inputs up to ~
  _≈Δ_ : Δ-Morphism DD → Δ-Morphism DD → Set ℓ
  f ≈Δ g = ∀ x → fun f x ~ fun g x
