{-# OPTIONS --safe --without-K #-}

{-
  DD-Calculus v0.1
  Module: Distinction.Types
  
  Types as equivalence classes under ~
  Using Setoid approach (quotient-free)
-}

module Distinction.Types where

open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Nullary using (¬_)

open import Distinction.Core
open import Distinction.Axioms

private
  variable
    ℓ : Level

-- ============================================================
-- 5.1 Types as Setoid (U, ~)
-- ============================================================

-- A DD-Type is the carrier U equipped with ~ as equality
-- This is the quotient U/~ represented as a setoid

DD-Setoid : {U : Set ℓ} → DD-Structure U → Setoid ℓ ℓ
DD-Setoid {U = U} DD = record
  { Carrier = U
  ; _≈_ = _~_
  ; isEquivalence = ~-isEquivalence
  }
  where open DD-Structure DD

-- ============================================================
-- 5.2 Equality is Indistinguishability
-- ============================================================

-- [x] =_Δ [y] iff x ~ y
-- In setoid terms: _≈_ IS the equality

module _ {U : Set ℓ} (DD : DD-Structure U) where
  open DD-Structure DD
  
  -- Equality type (just an alias for clarity)
  _=Δ_ : U → U → Set ℓ
  _=Δ_ = _~_
  
  -- refl is immediate from A1
  =Δ-refl : ∀ {x} → x =Δ x
  =Δ-refl = ~-refl
  
  -- sym from A1
  =Δ-sym : ∀ {x y} → x =Δ y → y =Δ x
  =Δ-sym = ~-sym
  
  -- trans from A1
  =Δ-trans : ∀ {x y z} → x =Δ y → y =Δ z → x =Δ z
  =Δ-trans = ~-trans

-- ============================================================
-- Type interpretation: what "being a type" means
-- ============================================================

-- In DD-calculus, there is initially ONE type: U/~
-- Additional types arise from:
-- 1. Subsets of U with restricted distinguishers
-- 2. Products (via A2)
-- 3. Function spaces (Section 6)

-- For STLC v0.1, we work with the single base type
-- and function types built from it.
