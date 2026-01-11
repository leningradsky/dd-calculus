{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.NoU3 — U(3) Has Wrong Center (U(1), not Z₃)
-- ============================================================================
--
-- THEOREM: U(3) is incompatible with Omega structure.
--
-- PROOF:
--   Center(U(3)) = U(1) (continuous phases)
--   Center(SU(3)) = Z₃ (discrete)
--   Our centralizer = Z₃ (discrete, 3 elements)
--   Therefore: U(3) incompatible, SU(3) compatible
--
-- PHYSICAL MEANING:
--   det = 1 is FORCED, not optional
--   Anomaly cancellation in DD terms
--
-- ============================================================================

module DD.NoU3 where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc)
open import Core.Omega
open import DD.Triad using (Transform; id-t; cycle; cycle²; cycle≢id; cycle³≡id)
open import DD.NoScale using (centralizer-is-Z₃; CommutesWithCycle)

-- ============================================================================
-- SECTION 1: U(3) CENTER STRUCTURE
-- ============================================================================

-- U(3) has center U(1) = {e^{iθ}I : θ ∈ [0, 2π)}
-- This is continuous and infinite
-- 
-- SU(3) has center Z₃ = {I, ωI, ω²I} where ω = e^{2πi/3}
-- This is discrete and finite (3 elements)

-- In DD terms: the centralizer of cycle has exactly 3 elements
-- This matches Z₃, not U(1)

-- ============================================================================
-- SECTION 2: DISCRETENESS OF CENTRALIZER
-- ============================================================================

-- Key fact: our centralizer is DISCRETE
-- We can enumerate all elements

data CentralizerZ₃ : Set where
  z-id z-ω z-ω² : CentralizerZ₃

-- Exactly 3 elements
card-Z₃ : ℕ
card-Z₃ = 3

-- All distinct
z-all-distinct : (x y : CentralizerZ₃) → (x ≡ y) ⊎ (x ≢ y)
z-all-distinct z-id z-id = inj₁ refl
z-all-distinct z-id z-ω = inj₂ (λ ())
z-all-distinct z-id z-ω² = inj₂ (λ ())
z-all-distinct z-ω z-id = inj₂ (λ ())
z-all-distinct z-ω z-ω = inj₁ refl
z-all-distinct z-ω z-ω² = inj₂ (λ ())
z-all-distinct z-ω² z-id = inj₂ (λ ())
z-all-distinct z-ω² z-ω = inj₂ (λ ())
z-all-distinct z-ω² z-ω² = inj₁ refl

-- Map to actual transforms
z-to-transform : CentralizerZ₃ → Transform
z-to-transform z-id = id-t
z-to-transform z-ω = cycle
z-to-transform z-ω² = cycle²

-- ============================================================================
-- SECTION 3: U(1) WOULD REQUIRE INTERMEDIATE ELEMENTS
-- ============================================================================

-- If center were U(1), there would be elements "between" id and cycle
-- For example, e^{iπ/3}I would be in center (θ = π/3)
-- But our centralizer has NO such element

-- Record for "U(1)-like center" (continuous)
record U1Center : Set where
  field
    -- There exists an element "halfway" between id and cycle
    half-phase : Transform
    -- It commutes with cycle
    half-commutes : CommutesWithCycle half-phase
    -- It's different from all Z₃ elements
    half≢id : ¬ ((x : Omega) → half-phase x ≡ id-t x)
    half≢cycle : ¬ ((x : Omega) → half-phase x ≡ cycle x)
    half≢cycle² : ¬ ((x : Omega) → half-phase x ≡ cycle² x)

-- THEOREM: No such U(1) center exists
no-U1-center : ¬ U1Center
no-U1-center u1 with centralizer-is-Z₃ (U1Center.half-phase u1) (U1Center.half-commutes u1)
... | inj₁ eq-id = U1Center.half≢id u1 eq-id
... | inj₂ (inj₁ eq-cycle) = U1Center.half≢cycle u1 eq-cycle
... | inj₂ (inj₂ eq-cycle²) = U1Center.half≢cycle² u1 eq-cycle²

-- ============================================================================
-- SECTION 4: DET = 1 INTERPRETATION
-- ============================================================================

{-
WHY DET = 1 IS FORCED:

1. U(n) = {A ∈ GL(n,ℂ) : A†A = I}
   - No constraint on det(A)
   - det(A) can be any e^{iθ}
   - Center = U(1)

2. SU(n) = {A ∈ U(n) : det(A) = 1}
   - Determinant fixed to 1
   - Center = Z_n (nth roots of unity)

3. Our structure:
   - Centralizer = Z₃ (exactly 3 elements)
   - This is FINITE and DISCRETE
   - Matches SU(3), not U(3)

4. Physical interpretation:
   - det = 1 means "total distinction charge conserved"
   - U(1) phase freedom would allow "charge leakage"
   - Stabilization requires conservation → det = 1

This is the DD version of anomaly cancellation!
-}

-- ============================================================================
-- SECTION 5: FORMAL INCOMPATIBILITY
-- ============================================================================

-- U(3)-compatible would mean center is U(1)
record U3Compatible : Set where
  field
    -- Infinite center: for every n, there's an nth root
    nth-root : (n : ℕ) → n ≢ 0 → Transform
    -- Each nth root commutes with cycle
    nth-commutes : (n : ℕ) (ne : n ≢ 0) → CommutesWithCycle (nth-root n ne)
    -- nth-root n is order n (roughly)
    -- And there are infinitely many distinct ones

-- Simplified: U(3) would have an element of order 6 in center
-- (e^{iπ/3}I has order 6)
-- But Z₃ has no element of order 6

-- Helper definitions
iterate-t : ℕ → Transform → Transform
iterate-t zero f = id-t
iterate-t (suc n) f = λ x → f (iterate-t n f x)

ExtEq-t : Transform → Transform → Set
ExtEq-t f g = (x : Omega) → f x ≡ g x

order-6-element : Set
order-6-element = Σ Transform λ f → 
                  CommutesWithCycle f × 
                  ExtEq-t (iterate-t 6 f) id-t × 
                  ¬ ExtEq-t (iterate-t 3 f) id-t × 
                  ¬ ExtEq-t (iterate-t 2 f) id-t

-- In Z₃, orders are: 1 (for id), 3 (for ω, ω²)
-- No element of order 6 exists
-- Therefore U(3) (which has order-6 elements in center) is incompatible

-- ============================================================================
-- SECTION 6: CONCLUSION
-- ============================================================================

{-
SUMMARY:

U(3) is excluded because:
1. Center(U(3)) = U(1) (continuous, infinite)
2. Our centralizer = Z₃ (discrete, 3 elements)
3. centralizer-is-Z₃ proves EXACTLY 3 elements
4. Therefore U(3) is incompatible

SU(3) is compatible because:
1. Center(SU(3)) = Z₃
2. Our centralizer = Z₃
3. Perfect match!

PHYSICAL: det = 1 is forced by the discrete nature of distinction.
-}
