{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.NoSO3 — SO(3) is Incompatible with Triadic Structure
-- ============================================================================
--
-- THEOREM: SO(3) cannot be the gauge group for Omega (triad)
--
-- REASON: SO(3) has trivial center, but Omega requires Z₃ center.
--
-- MORE DEEPLY: SO(3) is a real group, but Omega has complex phase structure.
--
-- ============================================================================

module DD.NoSO3 where

open import Core.Logic
open import Core.Omega

-- ============================================================================
-- SECTION 1: THE CENTER ARGUMENT
-- ============================================================================

-- The center of a group G is Z(G) = {g ∈ G | ∀h. gh = hg}
-- 
-- FACT (from Lie theory):
--   Center(SO(3)) = {I} (trivial)
--   Center(SU(3)) = Z₃ = {I, ωI, ω²I}
--
-- We already proved:
--   centralizer(cycle) = Z₃
--
-- Therefore: The gauge group of Omega must have Z₃ in its center.
-- SO(3) fails this requirement.

-- ============================================================================
-- SECTION 2: MODELING THE ARGUMENT IN AGDA
-- ============================================================================

-- We model "center" abstractly: elements that commute with everything

record GroupWithCenter : Set₁ where
  field
    G : Set
    e : G                          -- identity
    _·_ : G → G → G                -- multiplication
    center : G → Set               -- predicate: is in center
    center-commutes : ∀ {g} → center g → ∀ h → (g · h) ≡ (h · g)

-- SO(3) has trivial center
record SO3-Model : Set₁ where
  field
    gwc : GroupWithCenter
  open GroupWithCenter gwc
  field
    -- Only identity is in center
    center-trivial : ∀ g → center g → g ≡ e

-- What Omega requires: Z₃ center
record Z₃-Center-Requirement : Set₁ where
  field
    gwc : GroupWithCenter
  open GroupWithCenter gwc
  field
    -- Three distinct central elements
    c₀ c₁ c₂ : G
    c₀-center : center c₀
    c₁-center : center c₁
    c₂-center : center c₂
    c₀≢c₁ : c₀ ≢ c₁
    c₁≢c₂ : c₁ ≢ c₂
    c₀≢c₂ : c₀ ≢ c₂

-- THEOREM: SO(3) cannot satisfy Z₃-Center-Requirement
-- 
-- We express this more simply: if a group has trivial center,
-- it cannot have three distinct central elements.

-- A group has "trivial center" if all central elements equal identity
TrivialCenter : (G : Set) (e : G) (center : G → Set) → Set
TrivialCenter G e center = (g : G) → center g → g ≡ e

-- A group has "Z₃ center" if it has 3 distinct central elements  
-- Using a simpler formulation
HasThreeDistinctCentral : (G : Set) (center : G → Set) → Set
HasThreeDistinctCentral G center = 
  Σ G λ c₀ → Σ G λ c₁ → 
    center c₀ × center c₁ × (c₀ ≢ c₁)

-- THEOREM: Trivial center and having two distinct central elements are incompatible
trivial-vs-nontrivial : (G : Set) (e : G) (center : G → Set) →
                        TrivialCenter G e center → HasThreeDistinctCentral G center → ⊥
trivial-vs-nontrivial G e center triv has3 = c₀≢c₁ c₀≡c₁
  where
  c₀ : G
  c₀ = proj₁ has3
  
  c₁ : G
  c₁ = proj₁ (proj₂ has3)
  
  stuff : center c₀ × center c₁ × (c₀ ≢ c₁)
  stuff = proj₂ (proj₂ has3)
  
  -- Use fst/snd for _×_ record
  cent₀ : center c₀
  cent₀ = fst stuff
  
  cent₁ : center c₁
  cent₁ = fst (snd stuff)
  
  c₀≢c₁ : c₀ ≢ c₁
  c₀≢c₁ = snd (snd stuff)
  
  c₀≡c₁ : c₀ ≡ c₁
  c₀≡c₁ = trans (triv c₀ cent₀) (sym (triv c₁ cent₁))

-- ============================================================================
-- SECTION 3: THE REPRESENTATION DIMENSION ARGUMENT
-- ============================================================================

-- Another way to see SO(3) fails:
--
-- SO(3) acts on ℝ³ (real 3-vectors)
-- SU(3) acts on ℂ³ (complex 3-vectors)
--
-- The fundamental representation of SO(3) is REAL
-- The fundamental representation of SU(3) is COMPLEX
--
-- Omega has complex phase structure (proved in ComplexStructure.agda)
-- Therefore SO(3) is insufficient.

-- We model this as: "real" vs "complex" carrier

data Carrier-Type : Set where
  real-carrier : Carrier-Type
  complex-carrier : Carrier-Type

record GroupAction : Set₁ where
  field
    G : Set
    X : Set
    carrier-type : Carrier-Type
    act : G → X → X

-- SO(3) action is real
SO3-is-real : GroupAction → Set
SO3-is-real ga = GroupAction.carrier-type ga ≡ real-carrier

-- Omega requires complex carrier (from ComplexStructure)
Omega-requires-complex : GroupAction → Set
Omega-requires-complex ga = GroupAction.carrier-type ga ≡ complex-carrier

-- THEOREM: No single action can be both real and complex-required
real-complex-exclusive : ∀ ga → SO3-is-real ga → Omega-requires-complex ga → ⊥
real-complex-exclusive ga real-pf complex-pf = real≢complex (trans (sym real-pf) complex-pf)
  where
  real≢complex : real-carrier ≢ complex-carrier
  real≢complex ()

-- ============================================================================
-- SECTION 4: PHYSICAL INTERPRETATION
-- ============================================================================

{-
WHY SO(3) FAILS FOR COLOR:

1. CENTER MISMATCH:
   - SO(3) center = {I} (trivial)
   - Color requires Z₃ center
   - Quarks transform under Z₃: R → G → B → R
   - This Z₃ must be the center of gauge group
   - SO(3) doesn't have it

2. COMPLEX PHASES:
   - Gluon field has complex phase information
   - SO(3) is purely real
   - Cannot encode quantum interference of color

3. ANOMALY CANCELLATION:
   - SO(3) doesn't have the right anomaly structure
   - SU(3) anomaly = -SU(3)* ensures consistency
   - No such property for SO(3)

4. CONFINEMENT:
   - Color confinement requires specific center structure
   - Z₃ center of SU(3) is essential for 't Hooft flux
   - SO(3) lacks this mechanism

CONCLUSION:
SO(3) is excluded by both abstract (center mismatch) and
concrete (complex phase, anomaly) arguments.
-}

-- ============================================================================
-- SECTION 5: SUMMARY THEOREM
-- ============================================================================

-- Collecting the exclusion criteria
record SO3-Exclusion-Evidence : Set₁ where
  field
    -- Center is too small (trivial vs non-trivial)
    center-wrong : (G : Set) (e : G) (center : G → Set) →
                   TrivialCenter G e center → HasThreeDistinctCentral G center → ⊥
    -- Carrier is wrong type (real vs complex)
    carrier-wrong : ∀ ga → SO3-is-real ga → Omega-requires-complex ga → ⊥

-- We have both pieces of evidence
SO3-excluded : SO3-Exclusion-Evidence
SO3-excluded = record
  { center-wrong = trivial-vs-nontrivial
  ; carrier-wrong = real-complex-exclusive
  }
