{-# OPTIONS --without-K --safe #-}

module Distinction.DistSystem where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    ℓ ℓ' ℓ'' : Level

-- =============================================================================
-- DISTINGUISHER SYSTEM
-- =============================================================================

-- A system of distinguisher configurations with conservative refinement
record DistSystem (ℓ ℓ' : Level) : Set (Level.suc (ℓ ⊔ ℓ')) where
  field
    -- Configurations of distinguishers
    D : Set ℓ
    
    -- Conservative refinement: D' refines D means D' can only split classes, never glue
    _⪯_ : D → D → Set ℓ'
    
    -- Reflexivity: any config refines itself
    ⪯-refl : ∀ (d : D) → d ⪯ d
    
    -- Transitivity: refinement composes
    ⪯-trans : ∀ {d₁ d₂ d₃ : D} → d₁ ⪯ d₂ → d₂ ⪯ d₃ → d₁ ⪯ d₃
    
    -- Directedness: any two configs have common refinement
    ⪯-directed : ∀ (d₁ d₂ : D) → ∃[ d₃ ] (d₁ ⪯ d₃ × d₂ ⪯ d₃)

  -- Derived: antisymmetry would give partial order
  -- We don't require it — refinement is preorder

-- =============================================================================
-- ADMISSIBILITY (observational vs interventional)
-- =============================================================================

-- Admissibility predicate: marks configs that are purely observational
record AdmissibleDistSystem (ℓ ℓ' ℓ'' : Level) : Set (Level.suc (ℓ ⊔ ℓ' ⊔ ℓ'')) where
  field
    base : DistSystem ℓ ℓ'
    
    -- Predicate: is this config admissible (observational)?
    Admissible : DistSystem.D base → Set ℓ''
    
    -- Initial config is admissible
    init : DistSystem.D base
    init-adm : Admissible init
    
  open DistSystem base public

-- =============================================================================
-- REFINEMENT OPERATOR
-- =============================================================================

-- An operator that produces admissible refinements
record RefOp {ℓ ℓ' ℓ'' : Level} (DS : AdmissibleDistSystem ℓ ℓ' ℓ'') : Set (ℓ ⊔ ℓ' ⊔ ℓ'') where
  open AdmissibleDistSystem DS
  
  field
    -- The refinement step
    Φ : D → D
    
    -- Φ always refines
    Φ-refines : ∀ (d : D) → d ⪯ Φ d
    
    -- Φ preserves admissibility
    Φ-preserves-adm : ∀ (d : D) → Admissible d → Admissible (Φ d)
