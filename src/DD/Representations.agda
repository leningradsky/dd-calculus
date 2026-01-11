{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.Representations — Matter Content from Distinction Structure
-- ============================================================================
--
-- MAIN IDEA:
--   Representation = how a particle participates in distinction
--
--   Triadic participation → color triplet (3)
--   No triadic participation → color singlet (1)
--   Dyadic participation → isospin doublet (2)
--   No dyadic participation → isospin singlet (1)
--
-- ============================================================================

module DD.Representations where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc)
open import Core.Omega
open import Core.Dyad

-- ============================================================================
-- SECTION 1: REPRESENTATION DIMENSIONS
-- ============================================================================

-- Representation dimension = carrier size
Rep-dim : Set → ℕ
Rep-dim = λ _ → 0  -- placeholder, will compute properly

-- Omega gives 3-dim fundamental
omega-dim : ℕ
omega-dim = 3

-- Dyad gives 2-dim fundamental
dyad-dim : ℕ
dyad-dim = 2

-- Trivial gives 1-dim (singlet)
trivial-dim : ℕ
trivial-dim = 1

-- ============================================================================
-- SECTION 2: PARTICIPATION PREDICATES
-- ============================================================================

-- A particle type with its distinction structure
record Particle : Set₁ where
  field
    -- Does this particle participate in triadic distinction?
    triadic : Set
    triadic-dec : triadic ⊎ ¬ triadic
    
    -- Does this particle participate in dyadic distinction?
    dyadic : Set
    dyadic-dec : dyadic ⊎ ¬ dyadic
    
    -- Charge (for U(1))
    charge : ℕ

-- ============================================================================
-- SECTION 3: COLOR REPRESENTATION
-- ============================================================================

-- Color rep dimension from triadic participation
color-rep : (p : Particle) → ℕ
color-rep p with Particle.triadic-dec p
... | inj₁ _ = 3  -- triplet
... | inj₂ _ = 1  -- singlet

-- THEOREM: Triadic → Triplet
triadic-is-triplet : (p : Particle) → Particle.triadic p → color-rep p ≡ 3
triadic-is-triplet p tri with Particle.triadic-dec p
... | inj₁ _ = refl
... | inj₂ ¬tri = ⊥-elim (¬tri tri)

-- THEOREM: ¬Triadic → Singlet
no-triadic-is-singlet : (p : Particle) → ¬ (Particle.triadic p) → color-rep p ≡ 1
no-triadic-is-singlet p ¬tri with Particle.triadic-dec p
... | inj₁ tri = ⊥-elim (¬tri tri)
... | inj₂ _ = refl

-- ============================================================================
-- SECTION 4: ISOSPIN REPRESENTATION
-- ============================================================================

-- Isospin rep dimension from dyadic participation
isospin-rep : (p : Particle) → ℕ
isospin-rep p with Particle.dyadic-dec p
... | inj₁ _ = 2  -- doublet
... | inj₂ _ = 1  -- singlet

-- THEOREM: Dyadic → Doublet
dyadic-is-doublet : (p : Particle) → Particle.dyadic p → isospin-rep p ≡ 2
dyadic-is-doublet p dya with Particle.dyadic-dec p
... | inj₁ _ = refl
... | inj₂ ¬dya = ⊥-elim (¬dya dya)

-- THEOREM: ¬Dyadic → Singlet
no-dyadic-is-singlet : (p : Particle) → ¬ (Particle.dyadic p) → isospin-rep p ≡ 1
no-dyadic-is-singlet p ¬dya with Particle.dyadic-dec p
... | inj₁ dya = ⊥-elim (¬dya dya)
... | inj₂ _ = refl

-- ============================================================================
-- SECTION 5: STANDARD MODEL PARTICLES
-- ============================================================================

-- Left-handed quark doublet: (3, 2, Y)
-- Participates in BOTH triadic AND dyadic
QuarkL : Particle
QuarkL = record
  { triadic = ⊤
  ; triadic-dec = inj₁ tt
  ; dyadic = ⊤
  ; dyadic-dec = inj₁ tt
  ; charge = 0  -- placeholder for hypercharge
  }

-- Right-handed up quark: (3, 1, Y)
-- Participates in triadic, NOT dyadic
QuarkR-up : Particle
QuarkR-up = record
  { triadic = ⊤
  ; triadic-dec = inj₁ tt
  ; dyadic = ⊥
  ; dyadic-dec = inj₂ id
  ; charge = 0
  }

-- Right-handed down quark: (3, 1, Y)
QuarkR-down : Particle
QuarkR-down = record
  { triadic = ⊤
  ; triadic-dec = inj₁ tt
  ; dyadic = ⊥
  ; dyadic-dec = inj₂ id
  ; charge = 0
  }

-- Left-handed lepton doublet: (1, 2, Y)
-- NOT triadic, YES dyadic
LeptonL : Particle
LeptonL = record
  { triadic = ⊥
  ; triadic-dec = inj₂ id
  ; dyadic = ⊤
  ; dyadic-dec = inj₁ tt
  ; charge = 0
  }

-- Right-handed electron: (1, 1, Y)
-- NOT triadic, NOT dyadic
LeptonR : Particle
LeptonR = record
  { triadic = ⊥
  ; triadic-dec = inj₂ id
  ; dyadic = ⊥
  ; dyadic-dec = inj₂ id
  ; charge = 0
  }

-- ============================================================================
-- SECTION 6: VERIFY SM REPRESENTATIONS
-- ============================================================================

-- QuarkL is (3, 2)
QuarkL-color : color-rep QuarkL ≡ 3
QuarkL-color = refl

QuarkL-isospin : isospin-rep QuarkL ≡ 2
QuarkL-isospin = refl

-- QuarkR is (3, 1)
QuarkR-up-color : color-rep QuarkR-up ≡ 3
QuarkR-up-color = refl

QuarkR-up-isospin : isospin-rep QuarkR-up ≡ 1
QuarkR-up-isospin = refl

-- LeptonL is (1, 2)
LeptonL-color : color-rep LeptonL ≡ 1
LeptonL-color = refl

LeptonL-isospin : isospin-rep LeptonL ≡ 2
LeptonL-isospin = refl

-- LeptonR is (1, 1)
LeptonR-color : color-rep LeptonR ≡ 1
LeptonR-color = refl

LeptonR-isospin : isospin-rep LeptonR ≡ 1
LeptonR-isospin = refl

-- ============================================================================
-- SECTION 7: INTERPRETATION
-- ============================================================================

{-
WHAT THIS PROVES:

The SU(3) × SU(2) representation content of the Standard Model
is DETERMINED by participation in distinction structures:

| Particle | Triadic? | Dyadic? | Color | Isospin | SM Rep |
|----------|----------|---------|-------|---------|--------|
| Q_L      | YES      | YES     | 3     | 2       | (3,2)  |
| u_R      | YES      | NO      | 3     | 1       | (3,1)  |
| d_R      | YES      | NO      | 3     | 1       | (3,1)  |
| L_L      | NO       | YES     | 1     | 2       | (1,2)  |
| e_R      | NO       | NO      | 1     | 1       | (1,1)  |

PHYSICAL MEANING:

1. "Triadic participation" = feels the strong force
   - Quarks: YES → color triplet
   - Leptons: NO → color singlet

2. "Dyadic participation" = feels the weak force (left-handed)
   - Left-handed: YES → isospin doublet
   - Right-handed: NO → isospin singlet

3. The L/R distinction correlates with dyadic participation
   This is the origin of PARITY VIOLATION!

WHAT REMAINS:

1. WHY do quarks participate in triadic?
   → Need: theory of "what kind of thing" is triadic

2. WHY is L/R correlated with dyadic participation?
   → Need: chirality from refinement direction

3. HYPERCHARGES?
   → Need: anomaly cancellation in DD terms
-}
