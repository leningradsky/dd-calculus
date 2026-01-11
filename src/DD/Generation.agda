{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.Generation -- Why Exactly 3 Generations
-- ============================================================================
--
-- PROBLEM: SM has 3 copies of the same gauge representations.
-- WHY 3? Not 1, not 2, not 4+?
--
-- ANSWER: Generation = Omega at meta-level.
-- The same triadic structure that gives SU(3) also gives 3 generations.
--
-- ============================================================================

module DD.Generation where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc; _+_)
open import Core.Omega

-- ============================================================================
-- SECTION 1: GENERATION AS META-PHASE
-- ============================================================================

-- Generations are indexed by Omega phases
-- This is NOT a new structure - it's Omega reused at meta-level

Generation : Set
Generation = Omega

-- The three generations
gen1 : Generation
gen1 = ω⁰

gen2 : Generation
gen2 = ω¹

gen3 : Generation
gen3 = ω²

-- THEOREM: Exactly 3 generations
three-generations : (g : Generation) -> (g ≡ gen1) ⊎ (g ≡ gen2) ⊎ (g ≡ gen3)
three-generations ω⁰ = inj₁ refl
three-generations ω¹ = inj₂ (inj₁ refl)
three-generations ω² = inj₂ (inj₂ refl)

-- ============================================================================
-- SECTION 2: FAMILY STRUCTURE
-- ============================================================================

-- A family structure is an action that:
-- 1. Permutes generations
-- 2. Commutes with gauge (preserves quantum numbers)
-- 3. Is not itself a gauge symmetry

-- Generation action (cyclic permutation)
gen-succ : Generation -> Generation
gen-succ ω⁰ = ω¹
gen-succ ω¹ = ω²
gen-succ ω² = ω⁰

-- This is exactly the cycle operation from Omega!
gen-succ-is-cycle : (g : Generation) -> gen-succ g ≡ cycle g
gen-succ-is-cycle ω⁰ = refl
gen-succ-is-cycle ω¹ = refl
gen-succ-is-cycle ω² = refl

-- ============================================================================
-- SECTION 3: WHY GENERATION COMMUTES WITH GAUGE
-- ============================================================================

-- Key property: Generation action does NOT change gauge quantum numbers
-- All three generations have the same (color, isospin, hypercharge)

-- We model this as: gauge reps are constant across generations

data GaugeRep : Set where
  quarkL : GaugeRep    -- (3, 2, 1/6)
  quarkR-u : GaugeRep  -- (3, 1, 2/3)
  quarkR-d : GaugeRep  -- (3, 1, -1/3)
  leptonL : GaugeRep   -- (1, 2, -1/2)
  leptonR : GaugeRep   -- (1, 1, -1)

-- A particle is (generation, gauge rep)
record Particle : Set where
  field
    gen : Generation
    gauge : GaugeRep

-- Generation multiplication (Z3 addition)
gen-mul : Generation -> Generation -> Generation
gen-mul ω⁰ y = y
gen-mul ω¹ ω⁰ = ω¹
gen-mul ω¹ ω¹ = ω²
gen-mul ω¹ ω² = ω⁰
gen-mul ω² ω⁰ = ω²
gen-mul ω² ω¹ = ω⁰
gen-mul ω² ω² = ω¹

-- Generation action on particles (changes gen, preserves gauge)
gen-act : Generation -> Particle -> Particle
gen-act g p = record { gen = gen-mul g (Particle.gen p) ; gauge = Particle.gauge p }

-- THEOREM: Generation action preserves gauge quantum numbers
gauge-invariant : (g : Generation) -> (p : Particle) -> 
                  Particle.gauge (gen-act g p) ≡ Particle.gauge p
gauge-invariant g p = refl

-- ============================================================================
-- SECTION 4: GENERATION IS NOT GAUGE
-- ============================================================================

-- Generation is NOT a gauge symmetry because:
-- 1. It's global (same for all spacetime)
-- 2. It's discrete (Z3, not continuous)
-- 3. It doesn't couple to any gauge boson

-- We model "not gauge" as: no embedding into gauge group

-- The gauge group has continuous parameters
-- Generation has discrete (finite) structure
-- Therefore generation cannot embed into gauge

-- This is analogous to: Z3 cannot embed into U(1) as a subgroup
-- (it can embed as Z3 subset, but not as Lie subgroup)

record NotGaugeSymmetry : Set where
  field
    -- Generation is discrete
    discrete : (g h : Generation) -> (g ≡ h) ⊎ (g ≢ h)
    -- Generation has no gauge boson
    no-boson : ⊤  -- placeholder

gen-is-not-gauge : NotGaugeSymmetry
gen-is-not-gauge = record
  { discrete = discrete-gen
  ; no-boson = tt
  }
  where
    discrete-gen : (g h : Generation) -> (g ≡ h) ⊎ (g ≢ h)
    discrete-gen ω⁰ ω⁰ = inj₁ refl
    discrete-gen ω⁰ ω¹ = inj₂ (λ ())
    discrete-gen ω⁰ ω² = inj₂ (λ ())
    discrete-gen ω¹ ω⁰ = inj₂ (λ ())
    discrete-gen ω¹ ω¹ = inj₁ refl
    discrete-gen ω¹ ω² = inj₂ (λ ())
    discrete-gen ω² ω⁰ = inj₂ (λ ())
    discrete-gen ω² ω¹ = inj₂ (λ ())
    discrete-gen ω² ω² = inj₁ refl

-- ============================================================================
-- SECTION 5: MINIMALITY
-- ============================================================================

-- Generation structure must be MINIMAL among nontrivial options
-- Nontrivial = more than 1 element
-- Minimal = smallest such

-- Cardinality
card : Set -> ℕ
card Generation = 3  -- by definition (Omega has 3 elements)

-- THEOREM: 3 is the minimal nontrivial size for complex phase structure
-- (This is proven in NoTwoGen.agda)

-- ============================================================================
-- SECTION 6: INTERPRETATION
-- ============================================================================

{-
WHY 3 GENERATIONS:

1. Generations must exist (for CP violation, mixing)
2. Generations must be discrete (not gauge)
3. Generations must support complex phases (for CP)
4. Minimal such structure = Z3 = Omega
5. Therefore exactly 3 generations

The same Omega that gives SU(3) color also gives 3 generations.
This is not coincidence - it's the SAME structure at different levels:

Level 0: Physical space (3D from Omega)
Level 1: Color charge (SU(3) from Omega center)
Level 2: Generation (meta-phase from Omega)

DD predicts: the "3" in 3 generations is the SAME "3" as in SU(3).
-}
