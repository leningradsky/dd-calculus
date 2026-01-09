{-# OPTIONS --safe --without-K #-}

{-
  DD-Calculus v0.1
  Module: Distinction.Collapse
  
  Theorem 9.1 (Collapse): 
  If 𝒟 = ∅, mathematics is trivial.
-}

module Distinction.Collapse where

open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Product using (∃; _,_)

open import Distinction.Core

private
  variable
    ℓ : Level

-- ============================================================
-- Empty distinguisher set
-- ============================================================

-- A structure with no distinguishers
record EmptyDistinguishers (U : Set ℓ) : Set (Level.suc ℓ) where
  field
    DS : DistinctionStructure U
    no-distinguishers : DistinctionStructure.D DS → ⊥

-- ============================================================
-- Theorem 9.1: Collapse
-- ============================================================

module Collapse {U : Set ℓ} (ED : EmptyDistinguishers U) where
  open EmptyDistinguishers ED
  open DistinctionStructure DS
  
  -- (1) All entities are indistinguishable
  total-indistinguishability : ∀ x y → x ~ y
  total-indistinguishability x y (d , _) = no-distinguishers d
  
  -- (2) There is exactly one equivalence class (one type)
  -- All x, y are in the same class since x ~ y for all x, y
  
  -- (3) All Δ-morphisms are "equal" (indistinguishable in their action)
  -- Since f x ~ g x for any f, g, x (by total indistinguishability)
  
  all-morphisms-equal : ∀ (f g : U → U) x → f x ~ g x
  all-morphisms-equal f g x = total-indistinguishability (f x) (g x)
  
  -- (4) No nontrivial distinction can be made
  -- This is immediate from total-indistinguishability

-- ============================================================
-- Interpretation
-- ============================================================

{-
  The Collapse theorem shows:
  
  Δ = ∅  ⟹  Trivial mathematics
  
  Contrapositive:
  
  Nontrivial mathematics  ⟹  Δ ≠ ∅
  
  Therefore: the existence of distinction is NECESSARY
  for mathematics to be possible.
  
  This is not "we assume Δ≠∅ because it's convenient".
  This is "Δ≠∅ is forced by the existence of mathematics".
-}
