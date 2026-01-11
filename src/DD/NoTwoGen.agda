{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.NoTwoGen -- Why 2 Generations is Insufficient
-- ============================================================================
--
-- THEOREM: 2 generations cannot support CP violation.
--
-- This is analogous to NoOmegaIn2D: you can't fit a 3-cycle into 2 elements.
-- For CP violation, you need an ORIENTED 3-cycle (complex phase).
-- Z2 only has real structure (no cube roots of unity).
--
-- ============================================================================

module DD.NoTwoGen where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc)
open import Core.Omega

-- ============================================================================
-- SECTION 1: TWO-ELEMENT FAMILY STRUCTURE
-- ============================================================================

data TwoGen : Set where
  gen-a gen-b : TwoGen

-- The only nontrivial automorphism of TwoGen is swap
swap : TwoGen -> TwoGen
swap gen-a = gen-b
swap gen-b = gen-a

-- swap is an involution
swap-involution : (g : TwoGen) -> swap (swap g) ≡ g
swap-involution gen-a = refl
swap-involution gen-b = refl

-- ============================================================================
-- SECTION 2: NO ORIENTED 3-CYCLE IN Z2
-- ============================================================================

-- An oriented 3-cycle requires 3 distinct elements: a -> b -> c -> a
-- In Z2 = {0, 1}, we only have 2 elements
-- Therefore: no oriented 3-cycle exists

-- More precisely: any "cycle" in Z2 has order at most 2

-- The key point for CP violation:
-- CKM matrix with 2 generations is REAL (no complex phase)
-- CKM matrix with 3+ generations has COMPLEX phase

-- ============================================================================
-- SECTION 3: PHASE STRUCTURE
-- ============================================================================

-- A phase structure requires primitive roots of unity
-- Z2 has roots: 1, -1 (both real)
-- Z3 has roots: 1, omega, omega^2 (omega complex)

-- For CP violation we need COMPLEX phases
-- Therefore Z2 is insufficient

-- Definition: A structure supports CP if it has a complex phase
record SupportsCPPhase (G : Set) : Set where
  field
    -- There exists a "phase" operation
    phase : G -> G
    -- Phase is nontrivial
    nontrivial : (g : G) -> phase g ≢ g
    -- Phase has order 3 (not 2)
    order-3 : (g : G) -> phase (phase (phase g)) ≡ g
    order-not-2 : (g : G) -> phase (phase g) ≢ g

-- THEOREM: TwoGen does NOT support CP phase
no-cp-in-two : ¬ (SupportsCPPhase TwoGen)
no-cp-in-two cp = helper (phase gen-a) (phase gen-b) refl refl
  where
    open SupportsCPPhase cp
    
    -- Key insight: in a 2-element set, any f with f(f(f(x)))=x
    -- must have f(f(x))=x (pigeonhole) OR f(x)=x
    -- But nontrivial says f(x) != x
    -- And order-not-2 says f(f(x)) != x
    -- These are incompatible in a 2-element set!
    
    helper : (pa pb : TwoGen) -> phase gen-a ≡ pa -> phase gen-b ≡ pb -> ⊥
    -- Case: phase(a) = a -> contradicts nontrivial
    helper gen-a _ eq _ = nontrivial gen-a eq
    -- Case: phase(b) = b -> contradicts nontrivial  
    helper _ gen-b _ eq = nontrivial gen-b eq
    -- Case: phase(a) = b AND phase(b) = a
    -- Then phase(phase(a)) = phase(b) = a
    -- This contradicts order-not-2
    helper gen-b gen-a eq-a eq-b = order-not-2 gen-a ppa≡a
      where
        ppa≡a : phase (phase gen-a) ≡ gen-a
        ppa≡a = trans (cong phase eq-a) eq-b

-- ============================================================================
-- SECTION 4: OMEGA DOES SUPPORT CP PHASE
-- ============================================================================

-- Contrast: Omega (Z3) DOES support CP phase

omega-cp : SupportsCPPhase Omega
omega-cp = record
  { phase = cycle
  ; nontrivial = cycle-nontrivial
  ; order-3 = cycle³≡id
  ; order-not-2 = cycle²-not-id
  }
  where
    cycle-nontrivial : (g : Omega) -> cycle g ≢ g
    cycle-nontrivial ω⁰ ()
    cycle-nontrivial ω¹ ()
    cycle-nontrivial ω² ()
    
    cycle²-not-id : (g : Omega) -> cycle (cycle g) ≢ g
    cycle²-not-id ω⁰ ()
    cycle²-not-id ω¹ ()
    cycle²-not-id ω² ()

-- ============================================================================
-- SECTION 5: PHYSICAL INTERPRETATION
-- ============================================================================

{-
WHY 2 GENERATIONS CANNOT HAVE CP VIOLATION:

The CKM matrix for n generations is n×n unitary.
- n=2: 2×2 unitary has 1 angle, 0 phases (can be made real)
- n=3: 3×3 unitary has 3 angles, 1 phase (irreducibly complex)

The CP-violating phase is the Jarlskog invariant J.
For n=2: J = 0 identically (no CP violation possible)
For n=3: J can be nonzero (CP violation exists)

DD INTERPRETATION:

CP violation requires an ORIENTED cycle in flavor space.
- Oriented cycle needs 3+ elements
- Z2 has no oriented 3-cycle
- Z3 (Omega) is the MINIMAL structure with oriented 3-cycle

Therefore: Generations = Omega, not smaller.
-}

-- ============================================================================
-- SECTION 6: JARLSKOG INVARIANT STRUCTURE
-- ============================================================================

-- The Jarlskog invariant J = Im(V_us V_cb V*_ub V*_cs)
-- This is proportional to the area of the unitarity triangle

-- For J to be nonzero, we need:
-- 1. Complex entries in CKM matrix
-- 2. Non-degenerate mixing angles

-- With 2 generations: V is real, so J = 0
-- With 3 generations: V has one irremovable phase

-- We model this as: J requires a 3-cycle structure

record JarlskogStructure (G : Set) : Set where
  field
    -- Three distinct "vertices" of unitarity triangle
    v1 v2 v3 : G
    distinct12 : v1 ≢ v2
    distinct23 : v2 ≢ v3
    distinct13 : v1 ≢ v3
    -- Cycle connecting them
    cyc : G -> G
    cyc-v1 : cyc v1 ≡ v2
    cyc-v2 : cyc v2 ≡ v3
    cyc-v3 : cyc v3 ≡ v1

-- THEOREM: TwoGen has no Jarlskog structure
no-jarlskog-two : ¬ (JarlskogStructure TwoGen)
no-jarlskog-two js = pigeonhole (JarlskogStructure.v1 js) 
                                 (JarlskogStructure.v2 js) 
                                 (JarlskogStructure.v3 js)
                                 (JarlskogStructure.distinct12 js)
                                 (JarlskogStructure.distinct23 js)
                                 (JarlskogStructure.distinct13 js)
  where
    -- With only 2 elements, v1, v2, v3 can't all be distinct
    -- By pigeonhole: at least two must be equal
    pigeonhole : (x y z : TwoGen) -> x ≢ y -> y ≢ z -> x ≢ z -> ⊥
    pigeonhole gen-a gen-a _ d12 _ _ = d12 refl
    pigeonhole gen-a gen-b gen-a _ _ d13 = d13 refl
    pigeonhole gen-a gen-b gen-b _ d23 _ = d23 refl
    pigeonhole gen-b gen-a gen-a _ d23 _ = d23 refl
    pigeonhole gen-b gen-a gen-b _ _ d13 = d13 refl
    pigeonhole gen-b gen-b _ d12 _ _ = d12 refl

-- THEOREM: Omega HAS Jarlskog structure
omega-jarlskog : JarlskogStructure Omega
omega-jarlskog = record
  { v1 = ω⁰
  ; v2 = ω¹
  ; v3 = ω²
  ; distinct12 = ω⁰≢ω¹
  ; distinct23 = ω¹≢ω²
  ; distinct13 = ω⁰≢ω²
  ; cyc = cycle
  ; cyc-v1 = refl
  ; cyc-v2 = refl
  ; cyc-v3 = refl
  }

-- ============================================================================
-- SECTION 7: CONCLUSION
-- ============================================================================

{-
PROVEN:

1. TwoGen (Z2) cannot support CP phase structure
2. TwoGen has no Jarlskog structure (3-cycle)
3. Omega (Z3) DOES support both

CONSEQUENCE:

If generations are to explain CP violation (matter-antimatter asymmetry),
then |Gen| >= 3.

Combined with minimality (ScaleClosure principle):
|Gen| = 3 exactly.

This is WHY there are 3 generations, not 2.
-}
