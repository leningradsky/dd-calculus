{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.Boundary — The Boundary Between Structure and Dynamics
-- ============================================================================
--
-- DD derives STRUCTURAL constraints, not dynamical choices.
-- This module explicitly marks what is NOT derivable from Δ ≠ ∅.
--
-- KEY PRINCIPLE:
--   Structure = forced by distinction
--   Dynamics  = requires physics beyond DD
--
-- Instead of using ⊤ as placeholder, we use explicit DynamicalChoice type.
-- This makes the boundary between structure and dynamics crystal clear.
--
-- ============================================================================

module DD.Boundary where

open import Core.Logic

-- ============================================================================
-- DYNAMICAL CHOICE TYPE
-- ============================================================================

-- A DynamicalChoice witnesses that something is NOT structurally determined.
-- The choice exists, but DD cannot derive WHICH choice is realized.

record DynamicalChoice (A : Set) : Set where
  constructor dynamical
  field
    -- The space of possible choices
    witness : A
    -- Note: we don't claim which choice is "correct" —
    -- that's determined by dynamics/experiment, not structure

open DynamicalChoice public

-- ============================================================================
-- SPECIFIC DYNAMICAL BOUNDARIES
-- ============================================================================

-- Things DD CANNOT derive (and shouldn't try to):

-- 1. MASS VALUES
-- DD constrains mass STRUCTURE (sectors, hierarchy pattern)
-- but not numerical values (requires Yukawa dynamics)

data MassScale : Set where
  planck : MassScale
  gut    : MassScale
  electroweak : MassScale
  qcd    : MassScale

-- Which scale is "fundamental" is dynamical
mass-scale-choice : DynamicalChoice MassScale
mass-scale-choice = dynamical electroweak  -- realized in our universe

-- 2. NEUTRINO HIERARCHY
-- DD derives 3 generations but not which ordering

data NeutrinoHierarchy : Set where
  normal   : NeutrinoHierarchy  -- m₁ < m₂ < m₃
  inverted : NeutrinoHierarchy  -- m₃ < m₁ < m₂

-- Experiment suggests normal, but DD cannot derive this
neutrino-hierarchy-choice : DynamicalChoice NeutrinoHierarchy
neutrino-hierarchy-choice = dynamical normal  -- current experimental preference

-- 3. CP PHASE VALUES
-- DD derives that CP phases exist (from complex structure)
-- but not their numerical values

data CPPhaseType : Set where
  dirac     : CPPhaseType  -- δ in CKM/PMNS
  majorana  : CPPhaseType  -- α, β in PMNS (if Majorana)

cp-phase-type-choice : DynamicalChoice CPPhaseType
cp-phase-type-choice = dynamical dirac

-- 4. COSMOLOGICAL CONSTANT
-- DD says nothing about Λ — it's purely dynamical

data CosmologicalSign : Set where
  positive : CosmologicalSign  -- de Sitter (our universe)
  zero     : CosmologicalSign  -- Minkowski
  negative : CosmologicalSign  -- anti-de Sitter

cosmological-choice : DynamicalChoice CosmologicalSign
cosmological-choice = dynamical positive

-- ============================================================================
-- BOUNDARY MARKER
-- ============================================================================

-- Use this to mark any theorem that reaches the dynamical boundary
-- Instead of: something : ⊤
-- Use:        something : AtBoundary SomeChoiceType

AtBoundary : Set → Set
AtBoundary A = DynamicalChoice A

-- ============================================================================
-- INTERPRETATION
-- ============================================================================

{-
The DD/Boundary module serves as the explicit interface between:

  STRUCTURAL (derived from Δ ≠ ∅):
  - Gauge groups: SU(3) × SU(2) × U(1)
  - Spacetime: 3+1 dimensions
  - Generations: exactly 3
  - Chirality: left-right asymmetry
  - Anomaly cancellation: forces hypercharges

  DYNAMICAL (NOT derived, marked as DynamicalChoice):
  - Mass values
  - Neutrino hierarchy (normal vs inverted)
  - CP phase values
  - Cosmological constant
  - Initial conditions

This boundary is FUNDAMENTAL:
- DD is a theory of STRUCTURE
- Physics beyond DD determines DYNAMICS
- Confusing these leads to overclaiming

The DynamicalChoice type makes this boundary type-safe.
No more ⊤ placeholders — every gap is explicitly typed.
-}
