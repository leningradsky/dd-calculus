{-# OPTIONS --safe --without-K #-}

{-
  DD-Calculus v0.1
  Module: Distinction.Axioms
  
  A1: Indistinguishability is an equivalence relation
  A2: Distinguishers can be combined (conjunction)
-}

module Distinction.Axioms where

open import Level using (Level; _⊔_)
open import Relation.Binary using (IsEquivalence; Rel)
open import Relation.Nullary using (¬_)
open import Data.Product using (∃; _,_; _×_; proj₁; proj₂)

open import Distinction.Core

private
  variable
    ℓ : Level

-- ============================================================
-- A1: Equivalence of Indistinguishability
-- ============================================================

record A1-Equivalence {U : Set ℓ} (DS : DistinctionStructure U) : Set ℓ where
  open DistinctionStructure DS
  
  field
    -- ~ is reflexive: x ~ x
    ~-refl : ∀ {x} → x ~ x
    
    -- ~ is symmetric: x ~ y → y ~ x
    ~-sym : ∀ {x y} → x ~ y → y ~ x
    
    -- ~ is transitive: x ~ y → y ~ z → x ~ z
    ~-trans : ∀ {x y z} → x ~ y → y ~ z → x ~ z
  
  -- Package as IsEquivalence
  ~-isEquivalence : IsEquivalence _~_
  ~-isEquivalence = record
    { refl = ~-refl
    ; sym = ~-sym
    ; trans = ~-trans
    }

-- ============================================================
-- A2: Conjunction of Distinguishers
-- ============================================================

record A2-Conjunction {U : Set ℓ} (DS : DistinctionStructure U) : Set ℓ where
  open DistinctionStructure DS
  
  field
    -- For any two distinguishers, there exists a combined one
    merge : D → D → D
    
    -- The merged distinguisher is at least as fine
    merge-finer₁ : ∀ d₁ d₂ x y → 
      eval (merge d₁ d₂) x ≡L eval (merge d₁ d₂) y → 
      eval d₁ x ≡L eval d₁ y
    
    merge-finer₂ : ∀ d₁ d₂ x y → 
      eval (merge d₁ d₂) x ≡L eval (merge d₁ d₂) y → 
      eval d₂ x ≡L eval d₂ y

-- ============================================================
-- Complete DD-Structure: Core + A1 + A2
-- ============================================================

record DD-Structure (U : Set ℓ) : Set (Level.suc ℓ) where
  field
    core : DistinctionStructure U
    a1 : A1-Equivalence core
    a2 : A2-Conjunction core
  
  open DistinctionStructure core public
  open A1-Equivalence a1 public
  open A2-Conjunction a2 public
