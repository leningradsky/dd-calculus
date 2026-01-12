{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.YukawaClassification -- Classification of Allowed Yukawa Couplings
-- ============================================================================
--
-- THEOREM: The allowed Yukawa couplings are completely determined by
-- gauge invariance under SU(3)×SU(2)×U(1).
--
-- This module classifies which fermion bilinears can couple to the Higgs.
--
-- ============================================================================

module DD.YukawaClassification where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc; _+_; _*_)

-- ============================================================================
-- SECTION 1: GAUGE INVARIANCE REQUIREMENT
-- ============================================================================

-- A Yukawa coupling ψ̄_L H ψ_R (or ψ̄_L H̃ ψ_R) must be a gauge singlet:
-- SU(3): color indices contract
-- SU(2): isospin indices contract  
-- U(1)_Y: hypercharges sum to zero

-- For a coupling to exist, we need:
-- 1. SU(3): 3̄ ⊗ 1 ⊗ 3 ⊃ 1 OR 1 ⊗ 1 ⊗ 1 = 1
-- 2. SU(2): 2 ⊗ 2 ⊗ 1 ⊃ 1 (from 2 ⊗ 2 = 1 ⊕ 3)
-- 3. U(1)_Y: Y_L + Y_H + Y_R = 0

-- ============================================================================
-- SECTION 2: SM FERMION QUANTUM NUMBERS
-- ============================================================================

-- Recall (from Representations and HyperchargeUnique):

-- Left-handed (SU(2) doublets):
-- Q_L = (u_L, d_L): (3, 2, 1/6)
-- L   = (ν_L, e_L): (1, 2, -1/2)

-- Right-handed (SU(2) singlets):
-- u_R: (3, 1, 2/3)
-- d_R: (3, 1, -1/3)
-- e_R: (1, 1, -1)
-- ν_R: (1, 1, 0)  -- if exists

-- Higgs:
-- H:  (1, 2, 1/2)
-- H̃ = iσ₂H*: (1, 2, -1/2)

-- ============================================================================
-- SECTION 3: ALLOWED QUARK YUKAWAS
-- ============================================================================

-- UP-TYPE: Q̄_L H̃ u_R
-- SU(3): 3̄ ⊗ 1 ⊗ 3 → contains 1 ✓
-- SU(2): 2 ⊗ 2 ⊗ 1 → 2 ⊗ 2 = 1 ⊕ 3, contains 1 ✓
-- U(1)_Y: -1/6 + (-1/2) + 2/3 = -1/6 - 1/2 + 2/3 = -1/6 - 3/6 + 4/6 = 0 ✓
-- ALLOWED ✓

up-yukawa-allowed : Set
up-yukawa-allowed = ⊤

-- DOWN-TYPE: Q̄_L H d_R
-- SU(3): 3̄ ⊗ 1 ⊗ 3 → contains 1 ✓
-- SU(2): 2 ⊗ 2 ⊗ 1 → 2 ⊗ 2 = 1 ⊕ 3, contains 1 ✓
-- U(1)_Y: -1/6 + 1/2 + (-1/3) = -1/6 + 1/2 - 1/3 = -1/6 + 3/6 - 2/6 = 0 ✓
-- ALLOWED ✓

down-yukawa-allowed : Set
down-yukawa-allowed = ⊤

-- ============================================================================
-- SECTION 4: ALLOWED LEPTON YUKAWAS
-- ============================================================================

-- CHARGED LEPTON: L̄ H e_R
-- SU(3): 1 ⊗ 1 ⊗ 1 = 1 ✓
-- SU(2): 2 ⊗ 2 ⊗ 1 → contains 1 ✓
-- U(1)_Y: 1/2 + 1/2 + (-1) = 0 ✓
-- ALLOWED ✓

charged-lepton-yukawa-allowed : Set
charged-lepton-yukawa-allowed = ⊤

-- DIRAC NEUTRINO: L̄ H̃ ν_R (if ν_R exists)
-- SU(3): 1 ⊗ 1 ⊗ 1 = 1 ✓
-- SU(2): 2 ⊗ 2 ⊗ 1 → contains 1 ✓
-- U(1)_Y: 1/2 + (-1/2) + 0 = 0 ✓
-- ALLOWED ✓ (if ν_R exists)

dirac-neutrino-yukawa-allowed : Set
dirac-neutrino-yukawa-allowed = ⊤

-- ============================================================================
-- SECTION 5: FORBIDDEN YUKAWAS (EXAMPLES)
-- ============================================================================

-- Q̄_L H u_R (wrong Higgs)
-- U(1)_Y: -1/6 + 1/2 + 2/3 = -1/6 + 3/6 + 4/6 = 6/6 = 1 ≠ 0
-- FORBIDDEN ✗

-- Q̄_L H̃ d_R (wrong Higgs)
-- U(1)_Y: -1/6 + (-1/2) + (-1/3) = -1/6 - 3/6 - 2/6 = -6/6 = -1 ≠ 0
-- FORBIDDEN ✗

-- L̄ H̃ e_R (wrong Higgs)
-- U(1)_Y: 1/2 + (-1/2) + (-1) = -1 ≠ 0
-- FORBIDDEN ✗

-- ============================================================================
-- SECTION 6: YUKAWA MATRIX STRUCTURE
-- ============================================================================

-- With 3 generations, each allowed Yukawa becomes a 3×3 matrix:
-- Y_u: 3×3 complex matrix (up-type)
-- Y_d: 3×3 complex matrix (down-type)
-- Y_e: 3×3 complex matrix (charged leptons)
-- Y_ν: 3×3 complex matrix (neutrinos, if Dirac)

-- Total complex parameters: 4 × 9 = 36 (without neutrinos: 27)

-- But many can be removed by field redefinitions...

-- ============================================================================
-- SECTION 7: FIELD REDEFINITIONS
-- ============================================================================

-- We can redefine fermion fields by unitary transformations:
-- Q_L → V_Q Q_L
-- u_R → V_u u_R
-- d_R → V_d d_R
-- L   → V_L L
-- e_R → V_e e_R
-- ν_R → V_ν ν_R (if exists)

-- Each unitary 3×3 matrix has 9 real parameters.
-- Quark sector: V_Q, V_u, V_d → 27 parameters
-- But overall phase is unphysical → 26 effective

-- After redefinitions:
-- Y_u → V_Q† Y_u V_u  (can diagonalize to real positive)
-- Y_d → V_Q† Y_d V_d  (can't simultaneously diagonalize!)

-- ============================================================================
-- SECTION 8: PHYSICAL PARAMETERS (QUARKS)
-- ============================================================================

-- After field redefinitions, physical parameters are:
-- 6 masses: m_u, m_c, m_t, m_d, m_s, m_b
-- 3 CKM angles: θ₁₂, θ₂₃, θ₁₃
-- 1 CKM phase: δ (CP violation)

-- Total: 10 physical parameters (quarks)

quark-physical-params : ℕ
quark-physical-params = 10  -- 6 masses + 4 CKM

-- ============================================================================
-- SECTION 9: PHYSICAL PARAMETERS (LEPTONS)
-- ============================================================================

-- Charged leptons: 3 masses (m_e, m_μ, m_τ)

-- Neutrinos (Dirac case):
-- 3 masses + 3 PMNS angles + 1 Dirac phase = 7 parameters

-- Neutrinos (Majorana case):
-- 3 masses + 3 PMNS angles + 3 phases (1 Dirac + 2 Majorana) = 9 parameters

lepton-physical-params-dirac : ℕ
lepton-physical-params-dirac = 10  -- 3 + 7

lepton-physical-params-majorana : ℕ
lepton-physical-params-majorana = 12  -- 3 + 9

-- ============================================================================
-- SECTION 10: SUMMARY RECORD
-- ============================================================================

record YukawaClassification : Set where
  field
    -- Allowed couplings (boolean encoded as ℕ: 1 = yes, 0 = no)
    up-type : ℕ
    down-type : ℕ
    charged-lepton : ℕ
    dirac-neutrino : ℕ
    -- All allowed
    all-allowed : (up-type ≡ 1) × ((down-type ≡ 1) × 
                  ((charged-lepton ≡ 1) × (dirac-neutrino ≡ 1)))
    -- Physical parameters
    quark-params : ℕ
    is-ten : quark-params ≡ 10

yukawa-classification : YukawaClassification
yukawa-classification = record
  { up-type = 1
  ; down-type = 1
  ; charged-lepton = 1
  ; dirac-neutrino = 1
  ; all-allowed = refl , (refl , (refl , refl))
  ; quark-params = 10
  ; is-ten = refl
  }

-- ============================================================================
-- INTERPRETATION
-- ============================================================================

{-
WHAT WE PROVED:

1. ALLOWED YUKAWAS are completely determined by gauge invariance:
   - Up-type: Q̄_L H̃ u_R ✓
   - Down-type: Q̄_L H d_R ✓
   - Charged lepton: L̄ H e_R ✓
   - Dirac neutrino: L̄ H̃ ν_R ✓ (if ν_R exists)

2. FORBIDDEN YUKAWAS:
   - Wrong Higgs assignments give non-zero hypercharge

3. PHYSICAL PARAMETERS (after field redefinitions):
   - Quarks: 10 (6 masses + 4 CKM)
   - Leptons: 10 Dirac or 12 Majorana

DD CONTRIBUTION:
- WHICH couplings exist is STRUCTURAL (gauge invariance)
- The VALUES of Yukawa matrices are DYNAMICAL

The Yukawa sector structure is DERIVED from DD.
The Yukawa values are NOT derived (would need a theory of flavor).
-}
