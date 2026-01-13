{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.Index -- Central Index of DD Theorems
-- ============================================================================
--
-- This module serves as the master API for the DD→SM derivation.
-- If this module compiles, the entire chain is internally consistent.
--
-- ============================================================================

module DD.Index where

open import Core.Logic
open import Core.Nat using (ℕ)

-- ============================================================================
-- IMPORTS (qualified to avoid clashes)
-- ============================================================================

-- Core structure
import DD.Foundations as Found  -- THE entry point
import DD.Triad as T
import DD.Dyad as D
import DD.Monad as M
import Distinction.ForcingTriad as Forcing
import Distinction.ForcingDyad as ForcingD
import Distinction.ForcingMonad as ForcingM
import Distinction.GaugeFromDistinction as GFD
import Core.OmegaTriadic as OmegaTriadic
import DD.DerivationChain as Chain

-- Gauge group uniqueness
import DD.SU3Unique as SU3
import DD.SU2Unique as SU2
import DD.GaugeStructure as Gauge
import DD.TriadToGauge as T2G
import DD.ForcingToGauge as F2G
import DD.SU3FromForcing as SU3F

-- Representations and anomalies
import DD.Representations as Rep
import DD.Chirality as Chir
import DD.HyperchargeUnique as Hyper
import DD.AnomalyTheorem as Anom

-- Charge quantization
import DD.BaryonCharge as Baryon
import DD.ScaleClosure as Scale

-- Generations and mixing
import DD.ThreeGen as Gen
import DD.CPPhase as CP
import DD.MixingTheorem as Mix
import DD.CKM as CKM
import DD.PMNS as PMNS

-- Weinberg angle and RG
import DD.WeinbergAngle as Weinberg
import DD.Normalization as Norm
import DD.MinimalMultiplet as Mult
import DD.CanonicalTrace as Trace
import DD.BetaCoefficients as Beta
import DD.RGRunning as RG
import DD.RGBounds as RGBnd
import DD.RGIntegration as RGInt
import DD.WeinbergAtMZ as WMZ
import DD.NumericalValidation as NumVal

-- Higgs mechanism
import DD.YukawaInvariance as Yukawa
import DD.HiggsDoubletUnique as Higgs
import DD.ElectricCharge as Charge
import DD.PhotonMassless as Photon
import DD.MassRatio as Mass
import DD.RhoParameter as Rho
import DD.GoldstoneCounting as Goldstone
import DD.CustodialSymmetry as Custodial

-- Yukawa and mass structure
import DD.YukawaClassification as YukClass
import DD.YukawaParameters as YukParam
import DD.MassHierarchy as MassH
import DD.NeutrinoStructure as Neutrino

-- Mass diagonalization (CKM/PMNS as mismatch)
import DD.MassDiagonalization as MassDiag

-- Spacetime structure
import DD.TimeOrdering as Time
import DD.CausalStructure as Causal
import DD.Spacetime31 as ST

-- Complete derivation chain
import DD.DerivationChain as Chain

-- Numerical validation
import DD.Validation as Valid

-- ============================================================================
-- MASTER RECORD: The Complete DD → SM Derivation
-- ============================================================================

record DDtoSM : Set₁ where
  field
    -- WHY 3? (The core DD derivation)
    forcing : Forcing.TriadicClosure Forcing.Three
    
    -- GAUGE GROUP
    su3 : SU3.TriadCompatibleGauge
    su2 : SU2.DyadCompatibleGauge
    
    -- WEINBERG ANGLE
    gut : Weinberg.GUTPrediction
    trace : Trace.CanonicalNorm
    
    -- RG RUNNING
    rg : RG.RGTheorem
    bounds : RGBnd.RGBoundsTheorem
    rgIntegration : RGInt.RGIntegrationTheorem
    weinbergMZ : WMZ.WeinbergAtMZTheorem
    
    -- GENERATIONS
    threegen : Gen.ThreeGenTheorem
    
    -- MIXING
    mixing : Mix.UnifiedMixingTheorem
    
    -- HIGGS
    higgsY : Yukawa.HiggsHypercharge
    higgsRep : Higgs.HiggsRepUnique
    higgsField : Higgs.HiggsField
    rho : Rho.RhoParameter
    goldstone : Goldstone.GoldstoneCounting
    custodial : Custodial.CustodialSymmetry
    charge : Charge.ElectricChargeFormula
    photon : Photon.PhotonMassless
    massRatio : Mass.MassRatioTheorem
    
    -- YUKAWA/MASS
    yukawaClass : YukClass.YukawaClassification
    yukawaParams : YukParam.YukawaParameterCount
    massH : MassH.MassHierarchyTheorem
    neutrino : Neutrino.NeutrinoStructure
    
    -- MASS DIAGONALIZATION (CKM/PMNS as mismatch)
    diagMismatch : MassDiag.MixingMatrixTheorem
    
    -- SPACETIME 3+1
    timeOrder : Time.ArrowOfTime
    spacetime : ST.Spacetime31

-- ============================================================================
-- INSTANTIATION
-- ============================================================================

ddtoSM : DDtoSM
ddtoSM = record
  { forcing = Forcing.Omega-triadic
  ; su3 = SU3.SU3-satisfies
  ; su2 = SU2.SU2-satisfies
  ; gut = Weinberg.gut-prediction
  ; trace = Trace.canonical-norm
  ; rg = RG.rg-theorem
  ; bounds = RGBnd.rg-bounds-theorem
  ; rgIntegration = RGInt.rg-integration-theorem
  ; weinbergMZ = WMZ.weinberg-at-mz-theorem
  ; threegen = Gen.three-gen-theorem
  ; mixing = Mix.unified-mixing-theorem
  ; higgsY = Yukawa.higgs-hypercharge
  ; higgsRep = Higgs.higgs-rep-unique
  ; higgsField = Higgs.higgs-field
  ; rho = Rho.rho-parameter
  ; goldstone = Goldstone.goldstone-counting
  ; custodial = Custodial.custodial-symmetry
  ; charge = Charge.electric-charge-formula
  ; photon = Photon.photon-massless
  ; massRatio = Mass.mass-ratio-theorem
  ; yukawaClass = YukClass.yukawa-classification
  ; yukawaParams = YukParam.yukawa-parameter-count
  ; massH = MassH.mass-hierarchy-theorem
  ; neutrino = Neutrino.neutrino-structure
  ; diagMismatch = MassDiag.mixing-matrix-theorem
  ; timeOrder = Time.arrow-of-time
  ; spacetime = ST.spacetime31
  }

-- ============================================================================
-- RE-EXPORTS
-- ============================================================================

open SU3 public using (TriadCompatibleGauge; SU3-satisfies)
open SU2 public using (DyadCompatibleGauge; SU2-satisfies)
open Weinberg public using (GUTPrediction; gut-prediction)
open Trace public using (CanonicalNorm; canonical-norm)
open RG public using (RGTheorem; rg-theorem)
open RGBnd public using (RGBoundsTheorem; rg-bounds-theorem)
open RGInt public using (RGIntegrationTheorem; rg-integration-theorem)
open WMZ public using (WeinbergAtMZTheorem; weinberg-at-mz-theorem)
open Gen public using (ThreeGenTheorem; three-gen-theorem)
open Mix public using (UnifiedMixingTheorem; unified-mixing-theorem)
open Yukawa public using (HiggsHypercharge; higgs-hypercharge)
open Higgs public using (HiggsRepUnique; higgs-rep-unique; HiggsField; higgs-field)
open Rho public using (RhoParameter; rho-parameter)
open Goldstone public using (GoldstoneCounting; goldstone-counting)
open Custodial public using (CustodialSymmetry; custodial-symmetry)
open Charge public using (ElectricChargeFormula; electric-charge-formula)
open Photon public using (PhotonMassless; photon-massless)
open Mass public using (MassRatioTheorem; mass-ratio-theorem)
open YukClass public using (YukawaClassification; yukawa-classification)
open YukParam public using (YukawaParameterCount; yukawa-parameter-count)
open MassH public using (MassHierarchyTheorem; mass-hierarchy-theorem)
open Neutrino public using (NeutrinoStructure; neutrino-structure)
open MassDiag public using (MixingMatrixTheorem; mixing-matrix-theorem)
open Time public using (ArrowOfTime; arrow-of-time)
open ST public using (Spacetime31; spacetime31)

-- ============================================================================
-- STATISTICS
-- ============================================================================

theorem-count : ℕ
theorem-count = 27

{-
THE DD → SM DERIVATION IS COMPLETE.

If ddtoSM compiles, ALL of these are derived from Δ ≠ ∅:

GAUGE GROUP:
  1. SU(3)_c from triad
  2. SU(2)_L from dyad

WEINBERG ANGLE:
  3. Canonical trace (Tr = 1/2)
  4. sin²θ_W = 3/8 at GUT

RG RUNNING:
  5. Monotonic running theorem
  6. sin²θ_W bounds

GENERATIONS:
  7. 3 generations forced

MIXING:
  8. Unified mixing theorem (CKM/PMNS)

HIGGS MECHANISM:
  9. Y_H = 1/2 (Yukawa invariance)
  10. Higgs = doublet
  11. Higgs field structure
  12. ρ = 1
  13. Goldstone counting
  14. Custodial symmetry
  15. Q = T₃ + Y
  16. Photon massless
  17. m_W/m_Z = cos θ_W

YUKAWA/MASS:
  18. Yukawa classification
  19. Parameter counting
  20. Mass hierarchy structure
  21. Neutrino options

NOT DERIVED (dynamics):
  - v = 246 GeV
  - m_H = 125 GeV
  - Absolute masses
  - Yukawa values
  - M_GUT scale
-}
