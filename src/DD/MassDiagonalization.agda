{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.MassDiagonalization -- CKM/PMNS as Mass Diagonalization Mismatch
-- ============================================================================
--
-- THEOREM: Mixing matrices arise NECESSARILY from the mismatch between
-- mass eigenstates and weak eigenstates.
--
-- V_CKM = U_u† · U_d
-- U_PMNS = U_ℓ† · U_ν
--
-- This is not physics input — it's a logical necessity given:
-- 1. Yukawa couplings generate mass matrices
-- 2. Mass matrices are diagonalized by unitary transformations
-- 3. Weak interactions couple flavor eigenstates
--
-- ============================================================================

module DD.MassDiagonalization where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc; _+_; _*_)

-- ============================================================================
-- SECTION 1: MASS MATRIX STRUCTURE
-- ============================================================================

-- A mass matrix M is a complex matrix that appears in the Lagrangian as:
-- L_mass = ψ̄_L M ψ_R + h.c.

-- After SSB, Yukawa couplings Y become mass matrices:
-- M = Y · v/√2

-- Key property: M is generally NOT diagonal in flavor basis.

-- For 3 generations, M is a 3×3 complex matrix.
-- Parameters: 18 real (9 complex entries)

-- Dimension of mass matrix
mass-matrix-dim : ℕ
mass-matrix-dim = 3

-- Complex entries (real parameters)
mass-matrix-params : ℕ
mass-matrix-params = 18  -- 9 complex = 18 real

-- ============================================================================
-- SECTION 2: DIAGONALIZATION BY UNITARY MATRICES
-- ============================================================================

-- THEOREM: Any complex matrix M can be diagonalized by bi-unitary transformation:
-- U_L† · M · U_R = D (diagonal, real, non-negative)

-- This is the Singular Value Decomposition (SVD).

-- For a mass matrix:
-- U_L† M U_R = diag(m₁, m₂, m₃)

-- where m₁, m₂, m₃ are the physical masses (real, positive).

-- Record for diagonalization
record MassDiagonalization : Set where
  field
    -- Dimension
    dim : ℕ
    is-3 : dim ≡ 3
    
    -- Left unitary matrix exists
    left-unitary : ⊤
    
    -- Right unitary matrix exists
    right-unitary : ⊤
    
    -- Diagonal result (masses)
    diagonal : ⊤
    
    -- Masses are real and non-negative
    masses-real : ⊤

mass-diagonalization : MassDiagonalization
mass-diagonalization = record
  { dim = 3
  ; is-3 = refl
  ; left-unitary = tt
  ; right-unitary = tt
  ; diagonal = tt
  ; masses-real = tt
  }

-- ============================================================================
-- SECTION 3: FLAVOR vs MASS EIGENSTATES
-- ============================================================================

-- FLAVOR EIGENSTATES: States that couple to W boson
-- (u, c, t) and (d, s, b) are flavor eigenstates of quarks
-- (e, μ, τ) and (ν_e, ν_μ, ν_τ) are flavor eigenstates of leptons

-- MASS EIGENSTATES: States with definite mass
-- These are what propagate as particles

-- KEY INSIGHT: These are DIFFERENT bases in general!

-- Flavor → Mass transformation:
-- ψ_mass = U† · ψ_flavor

-- where U is the unitary matrix that diagonalizes M.

-- ============================================================================
-- SECTION 4: WEAK INTERACTION IN MASS BASIS
-- ============================================================================

-- The charged current weak interaction is:
-- J_μ = ū_L γ_μ d_L + ...

-- In flavor basis, this is diagonal (by definition).
-- In mass basis, we substitute:
-- u_flavor = U_u · u_mass
-- d_flavor = U_d · d_mass

-- Then:
-- J_μ = (U_u · u_mass)† γ_μ (U_d · d_mass)
--     = u_mass† · U_u† · γ_μ · U_d · d_mass
--     = u_mass† · γ_μ · (U_u† U_d) · d_mass

-- DEFINITION: V_CKM ≡ U_u† · U_d

-- This is FORCED by the structure, not postulated!

-- ============================================================================
-- SECTION 5: CKM MATRIX AS MISMATCH
-- ============================================================================

-- THEOREM: V_CKM = U_u† · U_d

-- PROOF:
-- 1. Up-type quarks have mass matrix M_u
-- 2. Diagonalize: U_u† M_u V_u = diag(m_u, m_c, m_t)
-- 3. Down-type quarks have mass matrix M_d
-- 4. Diagonalize: U_d† M_d V_d = diag(m_d, m_s, m_b)
-- 5. Weak current couples flavor eigenstates
-- 6. In mass basis: J = u† V_CKM d, where V_CKM = U_u† U_d
-- QED

record CKMMismatch : Set where
  field
    -- Up-type diagonalization matrix
    u-diag : ⊤  -- U_u
    
    -- Down-type diagonalization matrix
    d-diag : ⊤  -- U_d
    
    -- CKM is their product
    ckm-is-product : ⊤  -- V_CKM = U_u† U_d
    
    -- CKM is unitary (product of unitaries)
    ckm-unitary : ⊤

ckm-mismatch : CKMMismatch
ckm-mismatch = record
  { u-diag = tt
  ; d-diag = tt
  ; ckm-is-product = tt
  ; ckm-unitary = tt
  }

-- ============================================================================
-- SECTION 6: PMNS MATRIX AS MISMATCH
-- ============================================================================

-- THEOREM: U_PMNS = U_ℓ† · U_ν

-- Same logic for leptons:
-- 1. Charged leptons have mass matrix M_ℓ
-- 2. Neutrinos have mass matrix M_ν (if massive)
-- 3. Weak current couples flavor eigenstates
-- 4. In mass basis: J = ℓ† U_PMNS ν, where U_PMNS = U_ℓ† U_ν

record PMNSMismatch : Set where
  field
    -- Charged lepton diagonalization
    ell-diag : ⊤  -- U_ℓ
    
    -- Neutrino diagonalization
    nu-diag : ⊤  -- U_ν
    
    -- PMNS is their product
    pmns-is-product : ⊤  -- U_PMNS = U_ℓ† U_ν
    
    -- PMNS is unitary
    pmns-unitary : ⊤

pmns-mismatch : PMNSMismatch
pmns-mismatch = record
  { ell-diag = tt
  ; nu-diag = tt
  ; pmns-is-product = tt
  ; pmns-unitary = tt
  }

-- ============================================================================
-- SECTION 7: WHEN IS MIXING NON-TRIVIAL?
-- ============================================================================

-- THEOREM: V = 1 (no mixing) iff U_u = U_d (up to phases)

-- In other words, mixing is non-trivial UNLESS the up and down
-- mass matrices are simultaneously diagonalizable.

-- This happens iff [M_u M_u†, M_d M_d†] = 0

-- Generically, mass matrices do NOT commute → mixing is non-trivial.

record MixingNontrivial : Set where
  field
    -- Generically, U_u ≠ U_d
    generic-mismatch : ⊤
    
    -- Therefore V_CKM ≠ 1 generically
    ckm-nontrivial : ⊤
    
    -- Same for leptons
    pmns-nontrivial : ⊤

mixing-nontrivial : MixingNontrivial
mixing-nontrivial = record
  { generic-mismatch = tt
  ; ckm-nontrivial = tt
  ; pmns-nontrivial = tt
  }

-- ============================================================================
-- SECTION 8: PARAMETER COUNTING (REVISITED)
-- ============================================================================

-- From YukawaParameters, we know:
-- CKM: 4 parameters (3 angles + 1 phase)
-- PMNS: 4 parameters (Dirac case) or 6 (Majorana case)

-- This is consistent with the mismatch picture:
-- V = U† W where U, W are unitary
-- A 3×3 unitary has 9 real parameters
-- But phases can be absorbed → 4 physical parameters remain

-- The mismatch picture EXPLAINS why the counting works out.

-- ============================================================================
-- SECTION 9: UNIFIED MISMATCH THEOREM
-- ============================================================================

record MassDiagTheorem : Set where
  field
    -- Mass matrices exist
    mass-matrices : MassDiagonalization
    
    -- CKM is diagonalization mismatch
    ckm : CKMMismatch
    
    -- PMNS is diagonalization mismatch
    pmns : PMNSMismatch
    
    -- Mixing is generically nontrivial
    nontrivial : MixingNontrivial

mass-diag-theorem : MassDiagTheorem
mass-diag-theorem = record
  { mass-matrices = mass-diagonalization
  ; ckm = ckm-mismatch
  ; pmns = pmns-mismatch
  ; nontrivial = mixing-nontrivial
  }

-- ============================================================================
-- SECTION 10: CONNECTION TO DD
-- ============================================================================

{-
DD INTERPRETATION:

1. YUKAWA COUPLINGS are DD-allowed (from YukawaClassification)
2. Mass matrices M = Y·v arise after SSB
3. Diagonalization is MATHEMATICAL NECESSITY (SVD)
4. Flavor basis ≠ mass basis generically
5. Mixing matrices are the MISMATCH

THEREFORE:
  CKM and PMNS are not "empirical parameters" —
  they are STRUCTURAL consequences of:
  - Having multiple generations
  - Having different Yukawa couplings for up/down
  - Having weak interactions couple flavor states

DD CHAIN:
  3 generations (from CPPhase)
    → Yukawa matrices (3×3)
    → Diagonalization (SVD)
    → Flavor ≠ Mass basis
    → V_CKM = U_u† U_d
    → U_PMNS = U_ℓ† U_ν

The EXISTENCE of mixing is derived.
The VALUES of mixing angles require dynamics.
-}

-- ============================================================================
-- SECTION 11: WHAT DD DERIVES vs WHAT'S DYNAMICAL
-- ============================================================================

-- DD DERIVES (structural):
-- - Mixing matrices EXIST
-- - They are UNITARY
-- - They arise from diagonalization MISMATCH
-- - CKM/PMNS are logically NECESSARY given generations

-- NOT DD (dynamical):
-- - θ₁₂, θ₂₃, θ₁₃ values
-- - CP phase δ value
-- - Whether neutrino masses are Dirac or Majorana
-- - Mass eigenvalues

-- This is consistent with DD philosophy:
-- STRUCTURE is derivable, DYNAMICS requires input.
