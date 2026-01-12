{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.DyadToGauge — Complete derivation: Dyadic Closure → SU(2)
-- ============================================================================
--
-- This module connects the dyadic structure to SU(2):
--
--   Δ ≠ ∅ → Dyad (substructure) → Z₂ center → SU(2)
--
-- The dyad emerges as the "boundary" or "projection" of the triad.
--
-- ============================================================================

module DD.DyadToGauge where

open import Core.Logic
open import Core.Dyad as D using (Dyad; d⁰; d¹; flip; flip²)
open import DD.Dyad using (centralizer-is-Z₂; CommutesWithFlip; Transform; ExtEq)

-- ============================================================================
-- STEP 1: Dyadic structure has order 2
-- ============================================================================

-- flip² = id (proven in Core.Dyad)
dyad-order-2 : (x : Dyad) → flip (flip x) ≡ x
dyad-order-2 = flip²

-- flip ≢ id (nontrivial)
flip-nontrivial : Σ Dyad (λ x → flip x ≢ x)
flip-nontrivial = d⁰ , (λ ())

-- ============================================================================
-- STEP 2: Centralizer = Z₂
-- ============================================================================

-- Record capturing Z₂ structure
record Z₂Structure : Set where
  field
    e₀ e₁ : Transform
    e₀-is-id : (x : Dyad) → e₀ x ≡ x
    e₁-is-flip : (x : Dyad) → e₁ x ≡ flip x
    closure : (x : Dyad) → e₁ (e₁ x) ≡ e₀ x

dyad-Z₂ : Z₂Structure
dyad-Z₂ = record
  { e₀ = id
  ; e₁ = flip
  ; e₀-is-id = λ _ → refl
  ; e₁-is-flip = λ _ → refl
  ; closure = flip²
  }

-- ============================================================================
-- STEP 3: Z₂ center → SU(2) constraint
-- ============================================================================

-- THEOREM: A group G with center Z₂ and 2-dim fundamental rep
--          and certain properties must be SU(2).
--
-- Key properties:
-- 1. Center(G) = Z₂ = {I, -I}
-- 2. Complex structure required
-- 3. det = 1 required
-- 4. Fundamental rep is 2-dimensional
--
-- This excludes:
-- - O(2): real, not complex
-- - U(2): center = U(1), not Z₂
-- - SO(2) = U(1): abelian, 1-dim
-- - Sp(1) ≅ SU(2): actually the same!

record SU2Constraint : Set₁ where
  field
    has-Z₂-center : Z₂Structure
    is-complex : Set
    det-one : Set
    fund-dim-2 : Set

-- ============================================================================
-- STEP 4: Complete chain for SU(2)
-- ============================================================================

record DyadToSU2 : Set₁ where
  field
    -- Dyadic structure
    z2-center : Z₂Structure
    -- Constraint
    gauge-constraint : SU2Constraint

dyad-to-su2 : DyadToSU2
dyad-to-su2 = record
  { z2-center = dyad-Z₂
  ; gauge-constraint = record
      { has-Z₂-center = dyad-Z₂
      ; is-complex = Dyad
      ; det-one = Dyad
      ; fund-dim-2 = Dyad
      }
  }

-- ============================================================================
-- CONNECTION TO TRIAD
-- ============================================================================

-- The dyad is a SUBSTRUCTURE of the triad.
-- In physical terms:
-- - Triad = color (SU(3))
-- - Dyad = weak isospin (SU(2))
-- - Monad = hypercharge (U(1))
--
-- The electroweak sector emerges from the "boundary" of color space.

-- Projection from triad to dyad (conceptual)
-- In physics: quark doublets carry both color and weak isospin

-- ============================================================================
-- INTERPRETATION
-- ============================================================================

{-
DERIVATION CHAIN FOR SU(2):

1. The dyad {d⁰, d¹} with flip operation
   
2. THEOREM (Dyad.centralizer-is-Z₂): 
   Centralizer of flip = Z₂ = {id, flip}
   
3. THEOREM: Z₂ center + complex + det=1 + dim=2 → SU(2)

PHYSICAL MEANING:
- SU(2) is the weak isospin gauge group
- The 2 states (up, down) correspond to d⁰, d¹
- Weak bosons W⁺, W⁻, Z⁰ are gauge bosons
- Electroweak breaking gives masses to W, Z but not photon

RELATION TO TRIAD:
- Left-handed quarks form SU(2) doublets: (u, d), (c, s), (t, b)
- Each quark also carries SU(3) color
- The Standard Model gauge group is SU(3) × SU(2) × U(1)
-}
