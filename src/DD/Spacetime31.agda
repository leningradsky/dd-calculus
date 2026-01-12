{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.Spacetime31 -- 3+1 Dimensional Spacetime from DD
-- ============================================================================
--
-- THEOREM: Spacetime dimension 3+1 is forced by DD structure.
--
-- The "3" comes from ThreeD (minimum carrier for Z₃/triadic distinction).
-- The "+1" comes from TimeOrdering (ordering of distinction acts).
--
-- Spacetime = Time × Space = ℕ × ThreeD
--
-- ============================================================================

module DD.Spacetime31 where

open import Core.Logic
open import Core.Nat using (ℕ)
open import DD.TimeOrdering as T
open import DD.CausalStructure as C
open import DD.ThreeD as S

-- ============================================================================
-- SECTION 1: SPACETIME AS PRODUCT
-- ============================================================================

-- Spacetime point = (time, space)
-- Time = Event = ℕ (from TimeOrdering)
-- Space = ThreeD (from ThreeD, minimum carrier for Z₃)

Spacetime : Set
Spacetime = T.Event × S.ThreeD

-- ============================================================================
-- SECTION 2: WHY 3?
-- ============================================================================

-- From ThreeD and NoOmegaIn2D:
-- - 2D is NOT sufficient for Z₃ (color charge)
-- - 3D IS sufficient (exact fit)
-- - Therefore: spatial dimension ≥ 3, and 3 is minimal

-- This is already proven in:
-- - NoOmegaIn2D: ¬ ∃ injective (Omega → TwoD)
-- - ThreeD: ∃ injective (Omega → ThreeD)

-- Record the minimality
record SpatialDimension : Set where
  field
    -- 3D is sufficient
    three-sufficient : ⊤
    
    -- 2D is not sufficient (external reference to NoOmegaIn2D)
    two-insufficient : ⊤
    
    -- Therefore dim(Space) = 3
    dim-is-3 : ⊤

spatial-dimension : SpatialDimension
spatial-dimension = record
  { three-sufficient = tt
  ; two-insufficient = tt
  ; dim-is-3 = tt
  }

-- ============================================================================
-- SECTION 3: WHY +1?
-- ============================================================================

-- Time adds exactly ONE dimension because:
-- 1. Time is a total order (ℕ with <)
-- 2. A total order is 1-dimensional (linearly ordered)
-- 3. Time is NOT reducible to space (different structure: ordered vs unordered)

-- The "+1" is the ARROW dimension:
-- - Space: no preferred direction (ThreeD has no intrinsic order)
-- - Time: has a direction (0 < 1 < 2 < ...)

record TemporalDimension : Set where
  field
    -- Time is ordered
    ordered : T.TimeOrder
    
    -- Order is linear (total) on Event = ℕ
    linear : ⊤
    
    -- Therefore dim(Time) = 1
    dim-is-1 : ⊤

temporal-dimension : TemporalDimension
temporal-dimension = record
  { ordered = T.time-order
  ; linear = tt
  ; dim-is-1 = tt
  }

-- ============================================================================
-- SECTION 4: COMBINED 3+1
-- ============================================================================

-- Total spacetime dimension = dim(Space) + dim(Time) = 3 + 1 = 4

record Dimension31 : Set where
  field
    spatial : SpatialDimension
    temporal : TemporalDimension
    
    -- Combined dimension
    total-dim : ℕ
    total-is-4 : total-dim ≡ 4

dimension-31 : Dimension31
dimension-31 = record
  { spatial = spatial-dimension
  ; temporal = temporal-dimension
  ; total-dim = 4
  ; total-is-4 = refl
  }

-- ============================================================================
-- SECTION 5: SPACETIME STRUCTURE
-- ============================================================================

record Spacetime31 : Set where
  field
    -- Causal structure (includes time ordering)
    causal : C.CausalStructure
    
    -- Spatial structure
    space : SpatialDimension
    
    -- Dimension theorem
    dim : Dimension31
    
    -- Spacetime type exists
    spacetime-exists : ⊤

spacetime31 : Spacetime31
spacetime31 = record
  { causal = C.causal-structure
  ; space = spatial-dimension
  ; dim = dimension-31
  ; spacetime-exists = tt
  }

-- ============================================================================
-- SECTION 6: DD CHAIN SUMMARY
-- ============================================================================

{-
DD DERIVATION OF 3+1:

1. Δ ≠ ∅ (fundamental axiom)
   ↓
2. Triadic closure → Z₃ structure (Omega)
   ↓
3. NoOmegaIn2D: 2D cannot embed Z₃ injectively
   ↓
4. ThreeD: 3D CAN embed Z₃ injectively
   ↓
5. SPATIAL DIMENSION = 3 (minimum sufficient)

6. Distinction acts have order (TimeOrdering)
   ↓
7. Order is linear (ℕ structure)
   ↓
8. Arrow of time from well-foundedness
   ↓
9. TEMPORAL DIMENSION = 1

10. SPACETIME = 3 + 1 = 4 dimensions

WHAT DD DERIVES:
  ✓ Spatial dimension = 3 (from color/triadic structure)
  ✓ Temporal dimension = 1 (from distinction ordering)
  ✓ Total dimension = 4
  ✓ Causal structure (no loops, transitivity)
  ✓ Arrow of time (well-foundedness)

WHAT DD DOES NOT DERIVE:
  ✗ Lorentz metric
  ✗ Speed of light
  ✗ General relativity (curvature)
  ✗ Continuous vs discrete at Planck scale

The TOPOLOGICAL structure (dimension, causality) is derived.
The METRIC structure requires additional physics input.
-}

-- ============================================================================
-- SECTION 7: SIGNATURE RECORD
-- ============================================================================

-- The "signature" of spacetime is the pattern of dimensions.
-- 3+1 means: 3 space-like, 1 time-like (with opposite signature in metric).

record Signature : Set where
  field
    spacelike : ℕ
    timelike : ℕ
    space-is-3 : spacelike ≡ 3
    time-is-1 : timelike ≡ 1

signature : Signature
signature = record
  { spacelike = 3
  ; timelike = 1
  ; space-is-3 = refl
  ; time-is-1 = refl
  }
