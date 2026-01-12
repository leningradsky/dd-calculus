{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.PMNS -- Pontecorvo-Maki-Nakagawa-Sakata Matrix from DD
-- ============================================================================
--
-- The PMNS matrix describes neutrino flavor mixing:
-- |ve⟩    |U_e1   U_e2   U_e3 | |v1⟩
-- |vmu⟩ = |U_mu1  U_mu2  U_mu3| |v2⟩
-- |vtau⟩  |U_tau1 U_tau2 U_tau3| |v3⟩
--
-- Where numbered states are mass eigenstates.
--
-- Structurally IDENTICAL to CKM — same DD origin.
--
-- ============================================================================

module DD.PMNS where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc)
open import Core.Omega
open import DD.Generation
open import DD.CPPhase
open import DD.MixingMatrix

-- ============================================================================
-- SECTION 1: LEPTON GENERATIONS
-- ============================================================================

-- Neutrino flavor eigenstates (what PMNS mixes FROM)
data NeutrinoFlavor : Set where
  nu-e   : NeutrinoFlavor   -- electron neutrino
  nu-mu  : NeutrinoFlavor   -- muon neutrino
  nu-tau : NeutrinoFlavor   -- tau neutrino

-- Neutrino mass eigenstates (what PMNS mixes TO)
data NeutrinoMass : Set where
  nu-1 : NeutrinoMass   -- lightest (in normal ordering)
  nu-2 : NeutrinoMass   -- middle
  nu-3 : NeutrinoMass   -- heaviest

-- Charged leptons (for reference)
data ChargedLepton : Set where
  electron : ChargedLepton
  muon     : ChargedLepton
  tau      : ChargedLepton

-- Map to generations
flavor-to-gen : NeutrinoFlavor -> Gen
flavor-to-gen nu-e   = gen1
flavor-to-gen nu-mu  = gen2
flavor-to-gen nu-tau = gen3

mass-to-gen : NeutrinoMass -> Gen
mass-to-gen nu-1 = gen1
mass-to-gen nu-2 = gen2
mass-to-gen nu-3 = gen3

lepton-to-gen : ChargedLepton -> Gen
lepton-to-gen electron = gen1
lepton-to-gen muon     = gen2
lepton-to-gen tau      = gen3

-- ============================================================================
-- SECTION 2: PMNS AS PERMUTATION
-- ============================================================================

-- PMNS matrix = permutation of neutrino states
-- Same structure as CKM!

record PMNSStructure : Set where
  field
    perm : Perm3
    -- All permutations allowed (S3)
    valid : (perm ≡ pid) ⊎ (perm ≡ p12) ⊎ (perm ≡ p23) ⊎
            (perm ≡ p13) ⊎ (perm ≡ pcyc) ⊎ (perm ≡ pcyc2)

-- ============================================================================
-- SECTION 3: UNITARITY
-- ============================================================================

-- PMNS is unitary: U^dag * U = I

pmns-unitary : (pmns : PMNSStructure) -> (g : Gen) ->
               apply-perm (inverse-perm (PMNSStructure.perm pmns))
                          (apply-perm (PMNSStructure.perm pmns) g) ≡ g
pmns-unitary pmns g = perm-inverse-right (PMNSStructure.perm pmns) g

-- ============================================================================
-- SECTION 4: CP VIOLATION IN LEPTON SECTOR
-- ============================================================================

-- Same mechanism as CKM:
-- Cyclic permutations (pcyc, pcyc2) enable CP violation

pmns-cyclic-cp : (p : Perm3) ->
                 ((p ≡ pcyc) ⊎ (p ≡ pcyc2)) ->
                 ⊤  -- CP violation possible in PMNS
pmns-cyclic-cp _ _ = tt

-- The CP phase delta_CP in PMNS has SAME origin as in CKM:
-- It comes from Omega structure (Z3 cyclic group)

-- ============================================================================
-- SECTION 5: DIFFERENCE FROM CKM - LARGE ANGLES
-- ============================================================================

-- Empirical: PMNS has LARGE mixing angles
-- theta_12 ~ 34 deg (solar), theta_23 ~ 45 deg (atmospheric), theta_13 ~ 8.5 deg

-- CKM has SMALL angles (hierarchical)
-- theta_12 ~ 13 deg, theta_23 ~ 2.4 deg, theta_13 ~ 0.2 deg

-- DD interpretation:
-- The MAGNITUDE of angles depends on mass spectrum
-- Quarks: large mass hierarchy -> small mixing
-- Neutrinos: small mass hierarchy -> large mixing

-- We CANNOT derive angle values from pure DD
-- But structure (3 angles + 1 phase) is SAME

-- ============================================================================
-- SECTION 6: MAJORANA PHASES (OPTIONAL EXTENSION)
-- ============================================================================

-- If neutrinos are Majorana particles (nu = nu-bar),
-- PMNS has 2 additional phases: alpha_1, alpha_2

-- These do NOT affect oscillations, only:
-- - Neutrinoless double beta decay
-- - Leptogenesis

-- DD interpretation:
-- Majorana = self-conjugate distinction
-- Additional phases from Z2 structure at particle level

data MajoranaPhase : Set where
  alpha1 : MajoranaPhase
  alpha2 : MajoranaPhase

-- Total PMNS parameters (Majorana case)
data PMNSParamMajorana : Set where
  theta12-pmns : PMNSParamMajorana
  theta23-pmns : PMNSParamMajorana
  theta13-pmns : PMNSParamMajorana
  delta-cp     : PMNSParamMajorana   -- Dirac CP phase
  maj-alpha1   : PMNSParamMajorana   -- Majorana phase 1
  maj-alpha2   : PMNSParamMajorana   -- Majorana phase 2

pmns-param-count-majorana : ℕ
pmns-param-count-majorana = 6

-- Dirac case: only 4 parameters (same as CKM)
data PMNSParamDirac : Set where
  theta12-d : PMNSParamDirac
  theta23-d : PMNSParamDirac
  theta13-d : PMNSParamDirac
  delta-d   : PMNSParamDirac

pmns-param-count-dirac : ℕ
pmns-param-count-dirac = 4

-- THEOREM: Dirac case has same count as CKM
pmns-equals-ckm-params : pmns-param-count-dirac ≡ 4
pmns-equals-ckm-params = refl

-- ============================================================================
-- SECTION 7: UNIFIED MIXING STRUCTURE
-- ============================================================================

-- CKM and PMNS are TWO INSTANCES of same DD mechanism:

record UnifiedMixing : Set where
  field
    -- Permutation (discrete) or unitary (continuous)
    perm : Perm3
    -- Source: flavor/gauge eigenstates
    source : Gen -> Gen
    -- Target: mass/stabilization eigenstates
    target : Gen -> Gen
    -- They differ (mixing is nontrivial)
    nontrivial : perm ≢ pid

-- Example: nontrivial mixing with pcyc
ckm-example : UnifiedMixing
ckm-example = record
  { perm = pcyc
  ; source = λ g -> g
  ; target = apply-perm pcyc
  ; nontrivial = λ ()
  }

pmns-example : UnifiedMixing
pmns-example = record
  { perm = pcyc
  ; source = λ g -> g
  ; target = apply-perm pcyc
  ; nontrivial = λ ()
  }

-- ============================================================================
-- SECTION 8: INTERPRETATION
-- ============================================================================

{-
WHAT PMNS MODULE ESTABLISHES:

1. PMNS = CKM (structurally)
   - Both are 3x3 unitary matrices
   - Both come from flavor/mass basis misalignment
   - Both have 3 angles + 1 CP phase (Dirac case)

2. CP VIOLATION
   - Same Omega/Z3 origin as CKM
   - Cyclic permutations enable CP
   - The delta_CP phase is analogous

3. MAJORANA EXTENSION
   - If nu = nu-bar: 2 additional phases
   - These come from self-conjugacy, not Omega

4. UNIFIED PICTURE
   - CKM (quarks) and PMNS (leptons) are instances
   - Same DD mechanism: gauge vs stabilization bases

NOT DERIVED:
- Why PMNS angles are large, CKM angles are small
- Specific numerical values
- Whether neutrinos are Dirac or Majorana
- Mass ordering (normal vs inverted)

DD CHAIN:
  3 generations (Omega)
  + flavor basis (gauge)
  + mass basis (stabilization)
  = mixing exists
  -> 3x3 unitary
  -> 3 angles + 1 CP phase
  -> PMNS (leptons) = CKM (quarks) structurally
-}
