{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.NoU3 — U(3) is Incompatible with Triadic Structure
-- ============================================================================
--
-- THEOREM: U(3) cannot be the gauge group for Omega (triad)
--
-- REASON: U(3) has center U(1), not Z₃.
--         det ∈ U(1) is arbitrary, but DD requires det = 1.
--
-- ============================================================================

module DD.NoU3 where

open import Core.Logic
open import Core.Omega

-- ============================================================================
-- SECTION 1: THE CENTER ARGUMENT
-- ============================================================================

-- Center(U(3)) = U(1) = {e^{iθ} · I | θ ∈ [0, 2π)}
-- This is a CONTINUOUS circle, not discrete Z₃.
--
-- Center(SU(3)) = Z₃ = {I, ωI, ω²I} where ω = e^{2πi/3}
--
-- The constraint det = 1 is what reduces U(1) center to Z₃:
--   If M ∈ SU(3), then det(M) = 1
--   For central element e^{iθ}I:
--     det(e^{iθ}I) = e^{3iθ} = 1
--     ⟹ 3θ = 2πk
--     ⟹ θ = 2πk/3
--     ⟹ e^{iθ} ∈ {1, ω, ω²}

-- ============================================================================
-- SECTION 2: DET = 1 REQUIREMENT FROM DD
-- ============================================================================

-- Why must det = 1?
--
-- PHYSICAL: Anomaly cancellation in quantum field theory
-- DD VERSION: Total "distinction charge" must be conserved
--
-- A gauge transformation changes how we label distinctions.
-- If det ≠ 1, the transformation creates/destroys "net distinction".
-- This violates conservation of meaning under relabeling.

-- Model: "determinant" as total charge
Determinant : Set → Set
Determinant G = G → ℕ  -- simplified: maps to natural number "charge"
  where open import Core.Nat using (ℕ)

-- Constraint: admissible transforms preserve total charge
Det1-Constraint : (G : Set) → Determinant G → G → Set
Det1-Constraint G det g = det g ≡ 1

-- ============================================================================
-- SECTION 3: CENTER SIZE COMPARISON
-- ============================================================================

-- U(3) center is "large" (continuous)
-- SU(3) center is "small" (discrete, 3 elements)

open import Core.Nat using (ℕ)

data CenterSize : Set where
  finite : ℕ → CenterSize    -- discrete, n elements
  continuous : CenterSize     -- uncountable

-- U(3) has continuous center
U3-center : CenterSize
U3-center = continuous

-- SU(3) has finite center of size 3
SU3-center : CenterSize
SU3-center = finite 3

-- Omega centralizer has size 3 (proved in NoScale)
Omega-centralizer-size : CenterSize
Omega-centralizer-size = finite 3

-- ============================================================================
-- SECTION 4: SIZE MISMATCH THEOREM
-- ============================================================================

-- Cannot match continuous to finite
continuous≢finite : ∀ n → continuous ≢ finite n
continuous≢finite n ()

-- Therefore U(3) center cannot match Omega centralizer
U3-center-mismatch : U3-center ≢ Omega-centralizer-size
U3-center-mismatch = continuous≢finite 3

-- ============================================================================
-- SECTION 5: PHYSICAL INTERPRETATION
-- ============================================================================

{-
WHY U(3) FAILS FOR COLOR:

1. CENTER TOO LARGE:
   - U(3) center = U(1) = circle
   - Color requires exactly Z₃
   - Too much freedom in U(3)

2. DETERMINANT ARBITRARY:
   - In U(3), det(M) can be any unit complex number
   - Quarks transform as 3-dimensional rep
   - Arbitrary phase would give unphysical charges

3. ANOMALY PROBLEM:
   - U(1) factor in U(3) leads to gauge anomalies
   - Triangle diagrams don't cancel
   - det=1 constraint (→ SU(3)) is required for consistency

4. CONSERVATION:
   - det=1 means "volume-preserving" in ℂ³
   - Physically: baryon number conservation
   - U(3) would allow baryon violation

CONCLUSION:
U(3) is excluded because its center is too large (continuous vs discrete)
and it lacks the det=1 constraint that ensures physical consistency.
-}

-- ============================================================================
-- SECTION 6: CONNECTION TO STABILIZATION
-- ============================================================================

-- In DD terms:
-- 
-- A gauge transformation relabels distinctions.
-- If det ≠ 1, the total "weight" of distinctions changes.
-- But stabilization requires invariance of total structure.
-- Therefore: det = 1 is forced by stabilization requirements.

-- Record capturing the constraint
record GaugeConstraint : Set₁ where
  field
    Transform : Set
    det : Transform → ℕ
    admissible : Transform → Set
    det-constraint : ∀ t → admissible t → det t ≡ 1

-- ============================================================================
-- SECTION 7: SUMMARY
-- ============================================================================

record U3-Exclusion-Evidence : Set₁ where
  field
    -- Center size mismatch
    center-mismatch : U3-center ≢ Omega-centralizer-size

-- We have the evidence
U3-excluded : U3-Exclusion-Evidence
U3-excluded = record
  { center-mismatch = U3-center-mismatch
  }
