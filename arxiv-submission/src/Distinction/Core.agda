{-# OPTIONS --safe --without-K #-}

{-
  DD-Calculus v0.1
  Module: Distinction.Core
  
  Primitive notions: U, 𝒟, Labels, eval, #, ~
-}

module Distinction.Core where

open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)
open import Data.Product using (∃; _,_; Σ)

private
  variable
    ℓ ℓ' : Level

-- ============================================================
-- 2.1 Carrier of Entities
-- ============================================================

-- U is a parameter, not defined here.
-- Each instantiation provides its own carrier.

record DistinctionStructure (U : Set ℓ) : Set (Level.suc ℓ) where
  field
    -- --------------------------------------------------------
    -- 2.2 Distinguishers
    -- --------------------------------------------------------
    
    -- Collection of distinguishers (as an index set)
    D : Set ℓ
    
    -- Labels for each distinguisher
    Label : D → Set ℓ
    
    -- Evaluation: apply distinguisher to entity
    eval : (d : D) → U → Label d
    
    -- Equality on labels (propositional)
    _≡L_ : ∀ {d} → Label d → Label d → Set ℓ

  -- ============================================================
  -- 3.1 Distinction
  -- ============================================================
  
  -- x # y: some distinguisher separates x from y
  _#_ : Rel U ℓ
  x # y = ∃ λ d → ¬ (eval d x ≡L eval d y)
  
  -- ============================================================
  -- 3.2 Indistinguishability
  -- ============================================================
  
  -- x ~ y: no distinguisher separates x from y
  _~_ : Rel U ℓ
  x ~ y = ¬ (x # y)

  -- ============================================================
  -- Derived notions
  -- ============================================================
  
  Distinguishable : U → U → Set ℓ
  Distinguishable = _#_
  
  Indistinguishable : U → U → Set ℓ
  Indistinguishable = _~_
