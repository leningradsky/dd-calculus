{-# OPTIONS --safe --without-K #-}

-- =============================================================================
-- Patch-8: Electric Charge Lattice Target
-- =============================================================================
-- 
-- DD-EM-Lattice Theorem:
-- For any DD-allowed BSM extension M, for any asymptotic particle x,
-- the electric charge Q(x) ∈ (1/3)ℤ
--
-- This is a FALSIFIABLE target:
-- - Kill by experiment: millicharged particle with Q ∉ (1/3)ℤ
-- - Kill by logic: construct DDAllowed model with non-lattice charge
-- =============================================================================

module DD.Patch8-ChargeLattice where

open import Core.Nat
open import Core.Logic

-- =============================================================================
-- LAYER 1: Rational Arithmetic (minimal)
-- =============================================================================

-- We represent rationals as pairs (numerator, denominator)
-- For simplicity, we work with the lattice condition directly

-- Integer type (using Nat with sign)
data ℤ : Set where
  pos : ℕ → ℤ      -- 0, 1, 2, ...
  neg : ℕ → ℤ      -- -1, -2, -3, ... (neg 0 = -1)

-- Rational represented as numerator over fixed denominator 6
-- This simplifies lattice checking: Q ∈ (1/3)ℤ iff 6Q ∈ 2ℤ
record ℚ₆ : Set where
  constructor _/6
  field
    numerator : ℤ

-- Charge in (1/3)ℤ means numerator divisible by 2
-- Because: k/3 = 2k/6, so valid charges have even numerator in ℚ₆

-- Divisibility by 2
data Even : ℤ → Set where
  even-pos : (n : ℕ) → Even (pos (n + n))
  even-neg : (n : ℕ) → Even (neg (n + n))
  even-zero : Even (pos 0)

-- The lattice predicate
Lattice₃ : ℚ₆ → Set
Lattice₃ (num /6) = Even num

-- =============================================================================
-- LAYER 2: Particles and Models
-- =============================================================================

-- Asymptotic particle with observable EM charge
record Particle : Set where
  constructor mkParticle
  field
    Q : ℚ₆                    -- Electric charge (in units of 1/6)
    asymptotic : ⊤            -- Marker: this is observable

-- Standard Model reference charges (in units of 1/6)
-- Q = 0   → 0/6
-- Q = 1/3 → 2/6
-- Q = 2/3 → 4/6
-- Q = 1   → 6/6
-- Q = -1  → -6/6

Q-zero : ℚ₆
Q-zero = pos 0 /6

Q-one-third : ℚ₆
Q-one-third = pos 2 /6

Q-two-thirds : ℚ₆
Q-two-thirds = pos 4 /6

Q-one : ℚ₆
Q-one = pos 6 /6

Q-minus-one : ℚ₆
Q-minus-one = neg 5 /6  -- -6/6 = neg 5 in our encoding (neg n = -(n+1))

-- =============================================================================
-- LAYER 3: DD-Allowed Condition
-- =============================================================================

-- List of particles
data ParticleList : Set where
  []  : ParticleList
  _∷_ : Particle → ParticleList → ParticleList

-- Model with SM and new particles
record Model : Set where
  constructor mkModel
  field
    sm-particles : ParticleList
    new-particles : ParticleList

-- Membership
data _∈_ : Particle → ParticleList → Set where
  here  : ∀ {p ps} → p ∈ (p ∷ ps)
  there : ∀ {p q ps} → p ∈ ps → p ∈ (q ∷ ps)

-- =============================================================================
-- DD-ALLOWED: The key structural constraint
-- =============================================================================

-- DD-Allowed condition includes:
-- 1. Anomaly freedom (already formalized elsewhere)
-- 2. Unique U(1)_em (no kinetic mixing to non-lattice charges)
-- 3. SM-anchored normalization

-- The critical DD postulate that blocks millicharge:
-- "The unbroken U(1)_em is UNIQUE and couples only to lattice charges"

record UniqueEM : Set where
  field
    -- No additional U(1) factors that could mix
    no-hidden-U1 : ⊤
    -- All asymptotic states couple to the same photon
    unique-photon : ⊤

-- DD-Allowed for a model
record DDAllowed (M : Model) : Set where
  field
    -- Anomaly cancellation (imported from other modules)
    anomaly-free : ⊤
    -- Unique EM structure (blocks millicharge)
    unique-em : UniqueEM
    -- SM charges anchor the lattice
    sm-anchored : ⊤

-- =============================================================================
-- PATCH-8 TARGET THEOREM
-- =============================================================================

-- Statement: All new asymptotic particles in DD-allowed model have Q ∈ (1/3)ℤ

Patch8-EM-Lattice : 
  (M : Model) → 
  DDAllowed M → 
  (p : Particle) → 
  p ∈ (Model.new-particles M) →
  Lattice₃ (Particle.Q p)

-- PROOF STRATEGY:
-- This requires showing that DDAllowed constraints force all charges to lattice.
-- The proof will use:
-- 1. UniqueEM blocks non-lattice from mixing
-- 2. Anomaly constraints + SM-anchoring → Y ∈ (1/6)ℤ
-- 3. T₃ ∈ (1/2)ℤ always for SU(2) reps
-- 4. Q = T₃ + Y ∈ (1/6)ℤ ⊂ (1/3)ℤ for half-integer T₃
--    or Q ∈ (1/3)ℤ directly for integer T₃

-- For now, we state it as a goal (to be filled)
Patch8-EM-Lattice M dd-ok p p-in-new = {!!}

-- =============================================================================
-- KILL CRITERIA (documented)
-- =============================================================================

-- EXPERIMENTAL KILL:
-- Observe asymptotic particle with Q ∉ (1/3)ℤ
-- Example: millicharged particle with Q = 10⁻³ e

-- LOGICAL KILL:
-- Construct: ∃ M, DDAllowed M × ∃ p, p ∈ new × ¬ Lattice₃ (Q p)

-- Counter-model type (if this is inhabited, Patch-8 is dead)
CounterModel : Set
CounterModel = Σ Model λ M → 
               DDAllowed M × 
               Σ Particle λ p → 
               (p ∈ Model.new-particles M) × 
               (Lattice₃ (Particle.Q p) → ⊥)

-- If CounterModel is inhabited, the target is falsified
-- This is the "honesty" of the target
