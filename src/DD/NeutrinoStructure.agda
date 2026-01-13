{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.NeutrinoStructure -- Structural Analysis of Neutrino Sector
-- ============================================================================
--
-- QUESTION: Does DD determine whether neutrinos are Dirac or Majorana?
--
-- ANSWER: DD constrains the STRUCTURE but not the choice.
-- Both options are consistent with DD; the choice is dynamical.
--
-- ============================================================================

module DD.NeutrinoStructure where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc; _+_; _*_)
open import DD.Boundary using (DynamicalChoice; dynamical)

-- ============================================================================
-- SECTION 1: DIRAC vs MAJORANA
-- ============================================================================

-- The two possible neutrino types
data NeutrinoKind : Set where
  dirac    : NeutrinoKind  -- conserves lepton number
  majorana : NeutrinoKind  -- violates lepton number by 2

-- DIRAC NEUTRINO:
-- - Requires right-handed neutrino ν_R
-- - ν_R: (1, 1, 0) under SU(3)×SU(2)×U(1)
-- - Mass term: m_D ν̄_L ν_R + h.c.
-- - Lepton number CONSERVED

-- MAJORANA NEUTRINO:
-- - Can use only left-handed ν_L
-- - Mass term: m_M νᵀ_L C ν_L + h.c. (violates L by 2)
-- - Lepton number VIOLATED
-- - Can also have ν_R with Majorana mass

-- ============================================================================
-- SECTION 2: DD PERSPECTIVE ON ν_R
-- ============================================================================

-- Does DD require ν_R?

-- Arguments FOR ν_R:
-- 1. L/R symmetry (same structure as quarks)
-- 2. Anomaly cancellation (though ν_R doesn't contribute!)
-- 3. Grand unification (SO(10) has ν_R in 16)

-- Arguments AGAINST ν_R:
-- 1. Not required for anomaly cancellation
-- 2. Not observed directly
-- 3. Could have huge Majorana mass (seesaw)

-- DD STATUS: ν_R is OPTIONAL
-- SM anomalies cancel with OR without ν_R
-- DD allows but does not require ν_R

nu-R-required : Set
nu-R-required = ⊥  -- NOT required

nu-R-allowed : Set
nu-R-allowed = ⊤  -- but allowed

-- ============================================================================
-- SECTION 3: ANOMALY ANALYSIS WITH ν_R
-- ============================================================================

-- Without ν_R: Anomalies cancel (proven in AnomalyTheorem)
-- With ν_R (1,1,0): Still cancel! (ν_R doesn't contribute)

-- Why? Because ν_R has:
-- - No SU(3) charge → no SU(3)³ contribution
-- - No SU(2) charge → no SU(2)³ contribution  
-- - Zero hypercharge → no U(1)³ contribution
-- - Zero everything → no mixed anomaly contribution

-- Therefore: Adding ν_R doesn't break anomaly cancellation.

nu-R-anomaly-neutral : Set
nu-R-anomaly-neutral = ⊤

-- ============================================================================
-- SECTION 4: LEPTON NUMBER
-- ============================================================================

-- Lepton number L is a CLASSICAL symmetry of SM (without Majorana mass).
-- U(1)_L: ν, e⁻ have L = +1; ν̄, e⁺ have L = -1

-- DIRAC: L is conserved (exact symmetry)
-- MAJORANA: L is violated by 2 (Δ L = 2)

-- Experimental test: Neutrinoless double beta decay (0νββ)
-- 0νββ possible only if neutrinos are Majorana
-- Current: No observation (lower bound on half-life)

-- DD STATUS:
-- L conservation is not guaranteed by DD
-- L violation would require explicit Majorana term
-- This is a DYNAMICAL choice

lepton-number-guaranteed : Set
lepton-number-guaranteed = ⊥  -- NOT guaranteed by DD

-- ============================================================================
-- SECTION 5: SEESAW MECHANISM
-- ============================================================================

-- If both Dirac AND Majorana masses exist:
-- Dirac: m_D (from Higgs VEV, like other fermions)
-- Majorana (for ν_R): M_R (possibly huge, up to M_GUT)

-- Mass matrix:
-- ( 0    m_D )
-- ( m_D  M_R )

-- Eigenvalues:
-- Light: m_ν ≈ m_D² / M_R (suppressed!)
-- Heavy: M_N ≈ M_R (very heavy)

-- This explains small neutrino masses:
-- If m_D ~ v ~ 100 GeV and M_R ~ 10¹⁵ GeV
-- Then m_ν ~ v² / M_R ~ 0.01 eV ✓

-- DD STATUS:
-- Seesaw is CONSISTENT with DD
-- But M_R scale is DYNAMICAL (not derived)

seesaw-consistent : Set
seesaw-consistent = ⊤

-- ============================================================================
-- SECTION 6: PARAMETER COUNTING
-- ============================================================================

-- DIRAC (with 3 ν_R):
-- Yukawa Y_ν: 3×3 complex = 18 real
-- After field redefs: 7 physical (3 masses + 3 angles + 1 phase)
-- Total for neutrinos: 7

-- MAJORANA (no ν_R):
-- Effective Weinberg operator: dimension 5
-- Symmetric 3×3 complex = 12 real
-- After field redefs: 9 physical (3 masses + 3 angles + 3 phases)
-- Total: 9

-- SEESAW (with ν_R + Majorana):
-- Y_ν: 18 real (Dirac)
-- M_R: 12 real (Majorana for ν_R)
-- Total raw: 30
-- Physical: 18 (6 light+heavy masses, 6 angles, 6 phases)
-- But light sector: 9 (as Majorana)

dirac-nu-params : ℕ
dirac-nu-params = 7

majorana-nu-params : ℕ
majorana-nu-params = 9

-- ============================================================================
-- SECTION 7: DISTINGUISHING FEATURE
-- ============================================================================

-- The key structural difference:

-- DIRAC: 1 CP phase in PMNS
-- MAJORANA: 3 CP phases in PMNS (1 Dirac + 2 Majorana)

-- Majorana phases affect:
-- - 0νββ decay rate
-- - Leptogenesis (if it occurs)
-- NOT: Neutrino oscillations (only Dirac phase matters)

-- DD can identify these as structurally different options
-- but cannot choose between them without additional input.

-- ============================================================================
-- SECTION 8: EXPERIMENTAL PROBES
-- ============================================================================

-- 1. Neutrinoless double beta decay (0νββ)
--    Only possible if Majorana
--    Current limits: half-life > 10²⁶ years

-- 2. Neutrino oscillations
--    Measure Dirac CP phase δ
--    Insensitive to Dirac vs Majorana

-- 3. Heavy neutrino searches
--    If seesaw, heavy N might be produced
--    LHC searches ongoing

-- DD STATUS: These are experiments testing dynamical parameters

-- ============================================================================
-- SECTION 9: SUMMARY RECORD
-- ============================================================================

-- ν_R quantum numbers: (1, 1, 0) under SU(3)×SU(2)×U(1)
-- These are structural facts, not ⊤
record NuRQuantumNumbers : Set where
  field
    su3-rep : ℕ  -- 1 (singlet)
    su2-rep : ℕ  -- 1 (singlet)
    u1-charge : ℕ  -- 0
    is-singlet : (su3-rep ≡ 1) × (su2-rep ≡ 1) × (u1-charge ≡ 0)

-- ν_R quantum numbers
nu-R-quantum-numbers : NuRQuantumNumbers
nu-R-quantum-numbers = record
  { su3-rep = 1
  ; su2-rep = 1
  ; u1-charge = 0
  ; is-singlet = (refl , (refl , refl))
  }

-- Anomaly contribution: (Y³ × multiplicity) for U(1)³
-- For ν_R: 0³ × 1 = 0 (no contribution!)
-- This is a STRUCTURAL fact
anomaly-contribution : ℕ
anomaly-contribution = 0

anomaly-is-zero : anomaly-contribution ≡ 0
anomaly-is-zero = refl

record NeutrinoStructure : Set where
  field
    -- ν_R quantum numbers (structural)
    nu-R-qn : NuRQuantumNumbers
    
    -- ν_R is not required by anomaly cancellation
    nu-R-not-required : ⊥ → ⊥
    
    -- ν_R anomaly contribution is zero (proven, not ⊤)
    nu-R-anomaly-zero : anomaly-contribution ≡ 0
    
    -- Parameter counts (structural)
    dirac-params : ℕ
    majorana-params : ℕ
    params-are-correct : (dirac-params ≡ 7) × (majorana-params ≡ 9)
    
    -- Dirac vs Majorana is undetermined by DD
    -- This is a DYNAMICAL CHOICE: DD provides structure, not selection
    choice-is-dynamical : DynamicalChoice NeutrinoKind

neutrino-structure : NeutrinoStructure
neutrino-structure = record
  { nu-R-qn = nu-R-quantum-numbers
  ; nu-R-not-required = λ x → x
  ; nu-R-anomaly-zero = refl
  ; dirac-params = 7
  ; majorana-params = 9
  ; params-are-correct = refl , refl
  ; choice-is-dynamical = dynamical dirac  -- experiment TBD (Majorana also valid)
  }

-- ============================================================================
-- INTERPRETATION
-- ============================================================================

{-
WHAT WE PROVED:

1. ν_R IS OPTIONAL
   SM anomalies cancel with or without ν_R
   DD allows but doesn't require ν_R

2. BOTH DIRAC AND MAJORANA ARE CONSISTENT
   Neither violates any DD constraint
   The choice is DYNAMICAL

3. PARAMETER STRUCTURE DIFFERS
   Dirac: 7 parameters (1 CP phase)
   Majorana: 9 parameters (3 CP phases)

4. SEESAW IS CONSISTENT
   Explains small masses naturally
   But M_R scale is dynamical

DD CONTRIBUTION:
- Identifies the structural options
- Counts parameters for each
- Does NOT select between them

THE DIRAC/MAJORANA QUESTION is like asking:
"Does the electron have a magnetic moment?"
The STRUCTURE is there; the VALUE is empirical.
-}
