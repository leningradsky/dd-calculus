{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.Dyad — Dyadic Structure and SU(2) Connection
-- ============================================================================
--
-- Analogous to DD.Triad / DD.NoScale for SU(3).
-- Here we show: centralizer(flip) = Z₂ = {id, flip}
--
-- Physical interpretation:
--   Dyad = weak isospin states {up, down}
--   flip = isospin flip (SU(2) generator analogue)
--   Z₂ = center of SU(2)
--
-- ============================================================================

module DD.Dyad where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc)
open import Core.Dyad public

-- ============================================================================
-- TRANSFORMS
-- ============================================================================

Transform : Set
Transform = Dyad → Dyad

id-t : Transform
id-t = id

-- ============================================================================
-- COMMUTATION WITH FLIP
-- ============================================================================

CommutesWithFlip : Transform → Set
CommutesWithFlip f = (x : Dyad) → f (flip x) ≡ flip (f x)

id-commutes : CommutesWithFlip id-t
id-commutes x = refl

flip-commutes : CommutesWithFlip flip
flip-commutes d⁰ = refl
flip-commutes d¹ = refl

-- ============================================================================
-- KEY LEMMA: f is determined by f(d⁰)
-- ============================================================================

f-d¹-determined : (f : Transform) → CommutesWithFlip f → f d¹ ≡ flip (f d⁰)
f-d¹-determined f comm = comm d⁰

-- ============================================================================
-- EXTENSIONAL EQUALITY
-- ============================================================================

ExtEq : Transform → Transform → Set
ExtEq f g = (x : Dyad) → f x ≡ g x

-- ============================================================================
-- CLASSIFICATION BY CASES
-- ============================================================================

-- Case 1: f(d⁰) = d⁰ implies f = id
case-d⁰ : (f : Transform) → CommutesWithFlip f → 
          f d⁰ ≡ d⁰ → ExtEq f id-t
case-d⁰ f comm fd⁰ d⁰ = fd⁰
case-d⁰ f comm fd⁰ d¹ = trans (f-d¹-determined f comm) (cong flip fd⁰)

-- Case 2: f(d⁰) = d¹ implies f = flip
case-d¹ : (f : Transform) → CommutesWithFlip f → 
          f d⁰ ≡ d¹ → ExtEq f flip
case-d¹ f comm fd⁰ d⁰ = fd⁰
case-d¹ f comm fd⁰ d¹ = trans (f-d¹-determined f comm) (cong flip fd⁰)

-- ============================================================================
-- MAIN THEOREM: Centralizer of flip = Z₂
-- ============================================================================

centralizer-is-Z₂ : (f : Transform) → CommutesWithFlip f → 
                    (ExtEq f id-t) ⊎ (ExtEq f flip)
centralizer-is-Z₂ f comm with dyad-cases (f d⁰)
... | inj₁ fd⁰≡d⁰ = inj₁ (case-d⁰ f comm fd⁰≡d⁰)
... | inj₂ fd⁰≡d¹ = inj₂ (case-d¹ f comm fd⁰≡d¹)

-- ============================================================================
-- COUNTER-EXAMPLE: const does NOT commute
-- ============================================================================

const-d⁰ : Transform
const-d⁰ _ = d⁰

const-not-commutes : ¬ (CommutesWithFlip const-d⁰)
const-not-commutes comm = d⁰≢d¹ (comm d⁰)

-- ============================================================================
-- DYAD PRESERVING TRANSFORMS
-- ============================================================================

-- A "proper dyad" is just a pair of distinct elements
record ProperDyad : Set where
  constructor dyad-pair
  field
    p₀ p₁ : Dyad
    distinct : p₀ ≢ p₁

canonical-dyad : ProperDyad
canonical-dyad = dyad-pair d⁰ d¹ d⁰≢d¹

PreservesProper : Transform → Set
PreservesProper f = (pd : ProperDyad) → 
                    f (ProperDyad.p₀ pd) ≢ f (ProperDyad.p₁ pd)

-- id preserves proper dyads
id-preserves : PreservesProper id-t
id-preserves pd = ProperDyad.distinct pd

-- flip preserves proper dyads  
flip-preserves : PreservesProper flip
flip-preserves (dyad-pair d⁰ d⁰ ne) = ⊥-elim (ne refl)
flip-preserves (dyad-pair d⁰ d¹ _) = d¹≢d⁰
flip-preserves (dyad-pair d¹ d⁰ _) = d⁰≢d¹
flip-preserves (dyad-pair d¹ d¹ ne) = ⊥-elim (ne refl)

-- ============================================================================
-- INTERPRETATION
-- ============================================================================

{-
THEOREM: centralizer(flip) = Z₂ = {id, flip}

Any transform that commutes with flip must be id or flip itself.

PHYSICAL INTERPRETATION:

1. Dyad = weak isospin doublet {up, down}
   - Electron neutrino / electron
   - Up quark / down quark

2. flip = SU(2) generator (Pauli σ₁ analogue in discrete)

3. CommutesWithFlip = weak isospin invariance

4. Z₂ = center of SU(2) = {I, -I}
   - In discrete: {id, flip}

5. The theorem says:
   Only Z₂ transformations preserve isospin structure.
   This is the discrete seed of SU(2) gauge symmetry.

COMPARISON WITH TRIAD/SU(3):

| Structure | Generator | Centralizer | Gauge Group |
|-----------|-----------|-------------|-------------|
| Omega     | cycle     | Z₃          | SU(3)       |
| Dyad      | flip      | Z₂          | SU(2)       |

The Standard Model gauge structure emerges:
- SU(3) from triadic color
- SU(2) from dyadic isospin
- U(1) from... monad? (next step)
-}
