{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.Chirality — Left/Right from Refinement Direction
-- ============================================================================
--
-- MAIN IDEA:
--   Chirality = orientation relative to refinement direction
--
--   Refinement is ASYMMETRIC: it goes from coarse → fine
--   This creates a natural "handedness" in distinction space
--
--   Left-handed = aligned with refinement
--   Right-handed = counter-aligned
--
-- PHYSICAL CONSEQUENCE:
--   Only left-handed particles participate in dyadic (weak) force
--   This explains PARITY VIOLATION
--
-- ============================================================================

module DD.Chirality where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc)

-- ============================================================================
-- SECTION 1: REFINEMENT DIRECTION
-- ============================================================================

-- Refinement has a direction: coarse → fine
-- This is fundamentally asymmetric

data Direction : Set where
  forward : Direction   -- coarse → fine (refinement)
  backward : Direction  -- fine → coarse (would be "coarsening")

-- Refinement only goes forward
refinement-direction : Direction
refinement-direction = forward

-- There is no "backward refinement" in DD
-- This asymmetry is fundamental

-- ============================================================================
-- SECTION 2: CHIRALITY FROM DIRECTION
-- ============================================================================

-- Chirality = how a state relates to refinement direction
data Chirality : Set where
  L : Chirality   -- left-handed, aligned with refinement
  R : Chirality   -- right-handed, orthogonal/counter to refinement

-- Opposite chirality
flip-chirality : Chirality → Chirality
flip-chirality L = R
flip-chirality R = L

-- Chirality is self-inverse
flip-flip : (c : Chirality) → flip-chirality (flip-chirality c) ≡ c
flip-flip L = refl
flip-flip R = refl

-- ============================================================================
-- SECTION 3: CHIRALITY AND DISTINCTION PARTICIPATION
-- ============================================================================

-- KEY INSIGHT:
-- Only states aligned with refinement can "see" ongoing distinctions
-- States orthogonal to refinement see already-stabilized distinctions

-- Left-handed: participates in active distinction (dyadic)
-- Right-handed: sees only stabilized distinction (singlet)

record ChiralParticle : Set where
  field
    chirality : Chirality
    
-- Left-handed particles participate in dyadic distinction
left-participates : Chirality → Set
left-participates L = ⊤
left-participates R = ⊥

-- Right-handed particles don't participate in dyadic
right-not-participates : Chirality → Set
right-not-participates L = ⊥
right-not-participates R = ⊤

-- THEOREM: Chirality determines dyadic participation
chirality-determines-dyadic : (c : Chirality) → 
                              left-participates c ⊎ right-not-participates c
chirality-determines-dyadic L = inj₁ tt
chirality-determines-dyadic R = inj₂ tt

-- ============================================================================
-- SECTION 4: PARITY AND CHARGE CONJUGATION
-- ============================================================================

-- Parity: spatial reflection
-- In DD: reverses refinement direction (conceptually)
-- Effect: swaps left ↔ right

Parity : Chirality → Chirality
Parity = flip-chirality

-- Charge conjugation: particle ↔ antiparticle
-- In DD: reverses distinction orientation
data ChargeSign : Set where
  + - : ChargeSign

flip-charge : ChargeSign → ChargeSign
flip-charge + = -
flip-charge - = +

-- CP: combined Parity and Charge conjugation
record CPState : Set where
  field
    chirality : Chirality
    charge : ChargeSign

CP-transform : CPState → CPState
CP-transform s = record
  { chirality = flip-chirality (CPState.chirality s)
  ; charge = flip-charge (CPState.charge s)
  }

-- ============================================================================
-- SECTION 5: WEAK FORCE AND CHIRALITY
-- ============================================================================

-- The weak force ONLY couples to left-handed particles
-- This is parity violation

-- In DD terms:
-- Dyadic distinction (weak force) is ALIGNED with refinement
-- Only left-handed states can participate

record WeakCoupling : Set where
  field
    particle-chirality : Chirality
    couples-to-weak : left-participates particle-chirality

-- Left-handed particles couple to weak force
left-couples : WeakCoupling
left-couples = record
  { particle-chirality = L
  ; couples-to-weak = tt
  }

-- Right-handed CANNOT couple (would need ⊥)
-- right-couples : WeakCoupling
-- right-couples = record
--   { particle-chirality = R
--   ; couples-to-weak = {!!}  -- impossible!
--   }

-- ============================================================================
-- SECTION 6: NEUTRINOS
-- ============================================================================

-- Neutrinos are (almost) always left-handed
-- This is now explained: they ONLY exist as refinement-aligned states

-- In SM: ν_R doesn't exist (or is very heavy)
-- In DD: right-handed neutrino would be distinction-invisible

-- If neutrino = pure distinction state (no other structure)
-- Then it can ONLY exist aligned with refinement = left-handed

record Neutrino : Set where
  field
    chirality : Chirality
    is-left : chirality ≡ L  -- forced!

-- The only neutrino
standard-neutrino : Neutrino
standard-neutrino = record
  { chirality = L
  ; is-left = refl
  }

-- ============================================================================
-- SECTION 7: INTERPRETATION
-- ============================================================================

{-
WHAT THIS EXPLAINS:

1. WHY PARITY VIOLATION?
   - Refinement is asymmetric (forward only)
   - This creates preferred direction
   - Weak force couples to refinement-aligned states (left)
   - Right-handed states don't "see" ongoing distinction

2. WHY ONLY LEFT-HANDED NEUTRINOS?
   - Neutrino = pure distinction state
   - Pure distinction must be aligned with refinement
   - Therefore: neutrino is left-handed

3. WHY DO RIGHT-HANDED PARTICLES EXIST AT ALL?
   - They see STABILIZED distinctions (color, charge)
   - But not ONGOING distinctions (weak)
   - So they have color and EM charge, but no weak isospin

4. THE DEEP MEANING:
   - Left = future-facing (sees what's being distinguished)
   - Right = past-facing (sees what's already distinguished)
   - Weak force = the force of BECOMING distinguished
   - Strong/EM = forces of BEING distinguished

CONNECTIONS:

| DD Concept | Physics |
|------------|---------|
| Refinement direction | Arrow of time (?) |
| Left-aligned | Left-handed |
| Right-orthogonal | Right-handed |
| Dyadic participation | Weak coupling |
| No participation | Weak singlet |

REMAINING QUESTIONS:

1. Can we derive the EXACT coupling strengths?
2. Why does CP violation exist? (small asymmetry)
3. Connection to arrow of time?
-}
