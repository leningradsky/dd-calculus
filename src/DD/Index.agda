{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.Index -- Central Index of DD Theorems
-- ============================================================================
--
-- Collects all main DD→SM results. If this compiles, the chain is consistent.
--
-- ============================================================================

module DD.Index where

open import Core.Logic
open import Core.Nat using (ℕ)

-- ============================================================================
-- IMPORTS (qualified to avoid clashes)
-- ============================================================================

import DD.Triad as T
import DD.Dyad as D
import DD.Monad as M

import DD.SU3Unique as SU3
import DD.SU2Unique as SU2
import DD.GaugeStructure as Gauge

import DD.Representations as Rep
import DD.Chirality as Chir
import DD.HyperchargeUnique as Hyper
import DD.AnomalyTheorem as Anom
import DD.BaryonCharge as Baryon
import DD.ScaleClosure as Scale

import DD.ThreeGen as Gen
import DD.CPPhase as CP
import DD.MixingTheorem as Mix
import DD.CKM as CKM
import DD.PMNS as PMNS

import DD.WeinbergAngle as Weinberg
import DD.Normalization as Norm
import DD.MinimalMultiplet as Mult
import DD.CanonicalTrace as Trace
import DD.BetaCoefficients as Beta
import DD.RGRunning as RG

import DD.YukawaInvariance as Yukawa
import DD.HiggsDoubletUnique as Higgs
import DD.ElectricCharge as Charge
import DD.PhotonMassless as Photon
import DD.MassRatio as Mass

-- ============================================================================
-- RE-EXPORT KEY RESULTS
-- ============================================================================

-- Gauge group uniqueness
open SU3 public using (TriadCompatibleGauge; SU3-satisfies)
open SU2 public using (DyadCompatibleGauge; SU2-satisfies)

-- Weinberg angle
open Weinberg public using (GUTPrediction; gut-prediction)

-- Higgs structure  
open Yukawa public using (HiggsHypercharge; higgs-hypercharge)
open Higgs public using (HiggsRepUnique; higgs-rep-unique; HiggsField; higgs-field)
open Charge public using (ElectricChargeFormula; electric-charge-formula)
open Photon public using (PhotonMassless; photon-massless)
open Mass public using (MassRatioTheorem; mass-ratio-theorem)

-- ============================================================================
-- SUMMARY: What DD Derives
-- ============================================================================

-- Count of main structural results
structural-results : ℕ
structural-results = 14

{-
DERIVED FROM Δ ≠ ∅:

1. SU(3)_c gauge group (triad)
2. SU(2)_L gauge group (dyad)  
3. U(1)_Y gauge group (monad)
4. SM fermion representations
5. Hypercharges from anomaly cancellation
6. Unit charge quantization (baryon stability)
7. 3 generations (CP requirement)
8. CKM mixing structure
9. PMNS mixing structure
10. sin²θ_W = 3/8 at GUT
11. RG running direction (monotonic)
12. Y_H = 1/2 (Yukawa invariance)
13. Higgs = doublet (minimality + ρ=1)
14. Q = T₃ + Y (unique unbroken)
15. m_γ = 0 (photon massless)
16. m_W/m_Z = cos θ_W (structural ratio)

NOT DERIVED (dynamical):
- v = 246 GeV
- m_H = 125 GeV  
- Absolute masses
- Yukawa values
- M_GUT scale
-}
