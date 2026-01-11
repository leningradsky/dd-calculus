{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.ForcingDynamics — T5 for Omega-World
-- ============================================================================
--
-- This module shows that T5 (Forcing Dynamics) is ALREADY PROVEN
-- for the Omega/Z₃ case in DD.NoScale.
--
-- T5 Statement:
--   Policy choice + causal stability ⇒ action functional + stationarity
--
-- For Omega:
--   - Policy = Transform = Omega → Omega
--   - Causal stability = CommutesWithCycle
--   - Action = orbit position under cycle
--   - Stationarity = π ∈ {id, cycle, cycle²}
--
-- Main theorem: centralizer-is-Z₃ from NoScale IS T5.
-- ============================================================================

module DD.ForcingDynamics where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc)
open import Core.Omega
open import DD.NoScale using (Transform; CommutesWithCycle; ExtEq;
                               id-t; centralizer-is-Z₃;
                               id-commutes; cycle-commutes; cycle²-commutes)

-- ============================================================================
-- SECTION 1: POLICY AND STABILITY
-- ============================================================================

-- A policy is just a transform
Policy : Set
Policy = Transform

-- Causal stability = respects cycle structure
-- (You cannot know the future = your action commutes with evolution)
CausallyStable : Policy → Set
CausallyStable = CommutesWithCycle

-- ============================================================================
-- SECTION 2: STATIONARITY (extensional version)
-- ============================================================================

-- Stationary policies are extensionally equal to cycle-powers
data StationaryExt : Policy → Set where
  stat-ext-id    : ∀ {π} → ExtEq π id-t   → StationaryExt π
  stat-ext-cycle : ∀ {π} → ExtEq π cycle  → StationaryExt π
  stat-ext-cycle² : ∀ {π} → ExtEq π cycle² → StationaryExt π

-- ============================================================================
-- SECTION 3: T5 THEOREM
-- ============================================================================

-- THEOREM (T5 for Omega):
-- Any causally stable policy is stationary.
--
-- This is a REPACKAGING of centralizer-is-Z₃.

T5-omega : (π : Policy) → CausallyStable π → StationaryExt π
T5-omega π stable with centralizer-is-Z₃ π stable
... | inj₁ eq          = stat-ext-id eq
... | inj₂ (inj₁ eq)   = stat-ext-cycle eq
... | inj₂ (inj₂ eq)   = stat-ext-cycle² eq

-- ============================================================================
-- SECTION 4: CONVERSE
-- ============================================================================

-- Converse: stationary policies ARE causally stable
-- If π ≡ f extensionally and f commutes with cycle, then π commutes.

T5-converse : (π : Policy) → StationaryExt π → CausallyStable π
T5-converse π (stat-ext-id eq) x = 
  -- Goal: π (cycle x) ≡ cycle (π x)
  -- Know: π ≡ id extensionally, so π y ≡ y for all y
  trans (eq (cycle x)) (sym (cong cycle (eq x)))
T5-converse π (stat-ext-cycle eq) x =
  -- Goal: π (cycle x) ≡ cycle (π x)  
  -- Know: π ≡ cycle extensionally
  -- cycle (cycle x) ≡ cycle (cycle x) ✓
  trans (eq (cycle x)) (sym (cong cycle (eq x)))
T5-converse π (stat-ext-cycle² eq) x =
  -- Goal: π (cycle x) ≡ cycle (π x)
  -- Know: π ≡ cycle² extensionally
  -- cycle² (cycle x) ≡ cycle (cycle² x)
  trans (eq (cycle x)) (trans (cycle²-commutes x) (sym (cong cycle (eq x))))

-- ============================================================================
-- SECTION 5: BIDIRECTIONAL EQUIVALENCE
-- ============================================================================

-- T5 as equivalence: CausallyStable π ⟺ StationaryExt π

record _⟺_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

T5-equivalence : (π : Policy) → (CausallyStable π) ⟺ (StationaryExt π)
T5-equivalence π = record 
  { forward  = T5-omega π
  ; backward = T5-converse π 
  }

-- ============================================================================
-- SECTION 6: INTERPRETATION
-- ============================================================================

{-
THEOREM T5 (Forcing Dynamics) for Omega:

  ∀ π : Policy. CausallyStable π ⟺ StationaryExt π

MEANING:
  - Any policy that respects the cyclic structure
  - Must be extensionally equal to id, cycle, or cycle²
  - These are the "stationary" policies (extrema of the "action")

PHYSICAL INTERPRETATION:
  - Omega = color charge states
  - cycle = Z₃ generator
  - CausallyStable = gauge invariance
  - StationaryExt = gauge transformation
  
  Only gauge transformations (Z₃ elements) are compatible with color.
  This is T5: the "action principle" forces gauge structure.

CONNECTION TO GENERAL T5:
  General T5 says: stable policy selection → action functional + stationarity
  
  For Omega:
  - Action(π) = 0 if π = id, 1 if π = cycle, 2 if π = cycle²
  - Stationary = π ∈ Im(cycle^k)
  - Theorem: all stable policies are stationary (with action ∈ {0,1,2})

NO NEW STRUCTURE INTRODUCED:
  This is just reframing what NoScale already proved.
  T5 is the INTERPRETATION of centralizer-is-Z₃.
  
KEY INSIGHT:
  The "action principle" in physics is not a separate axiom.
  It is FORCED by requiring compatibility with evolution structure.
  For Omega: CommutesWithCycle forces π ∈ Z₃.
  For physics: gauge invariance forces specific field equations.
-}
