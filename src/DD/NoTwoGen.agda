{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.NoTwoGen -- Two Generations Cannot Support CP Violation
-- ============================================================================

module DD.NoTwoGen where

open import Core.Logic
open import Core.Omega
open import DD.CPPhase

-- ============================================================================
-- SECTION 1: TWO-ELEMENT STRUCTURE
-- ============================================================================

data Two : Set where
  t1 t2 : Two

two-eq-dec : (x y : Two) -> (x ≡ y) ⊎ (x ≢ y)
two-eq-dec t1 t1 = inj₁ refl
two-eq-dec t1 t2 = inj₂ (λ ())
two-eq-dec t2 t1 = inj₂ (λ ())
two-eq-dec t2 t2 = inj₁ refl

-- ============================================================================
-- SECTION 2: NO THREE IN TWO
-- ============================================================================

no-three-in-two : (x y z : Two) -> (x ≢ y) -> (x ≢ z) -> (y ≢ z) -> ⊥
no-three-in-two t1 t1 _ ne12 _ _ = ne12 refl
no-three-in-two t1 t2 t1 _ ne13 _ = ne13 refl
no-three-in-two t1 t2 t2 _ _ ne23 = ne23 refl
no-three-in-two t2 t1 t1 _ _ ne23 = ne23 refl
no-three-in-two t2 t1 t2 _ ne13 _ = ne13 refl
no-three-in-two t2 t2 _ ne12 _ _ = ne12 refl

-- ============================================================================
-- SECTION 3: NO CP IN TWO
-- ============================================================================

no-cp-in-two : ¬ (CPStructure Two)
no-cp-in-two cp = no-three-in-two 
                    (CPStructure.p0 cp) 
                    (CPStructure.p1 cp) 
                    (CPStructure.p2 cp)
                    (CPStructure.distinct01 cp)
                    (CPStructure.distinct02 cp)
                    (CPStructure.distinct12 cp)

-- ============================================================================
-- SECTION 4: NO OMEGA IN TWO
-- ============================================================================

record OmegaInTwo : Set where
  field
    f : Omega -> Two
    ne01 : f ω⁰ ≢ f ω¹
    ne02 : f ω⁰ ≢ f ω²
    ne12 : f ω¹ ≢ f ω²

no-omega-in-two : ¬ OmegaInTwo
no-omega-in-two oit = no-three-in-two 
                        (OmegaInTwo.f oit ω⁰) 
                        (OmegaInTwo.f oit ω¹) 
                        (OmegaInTwo.f oit ω²)
                        (OmegaInTwo.ne01 oit)
                        (OmegaInTwo.ne02 oit)
                        (OmegaInTwo.ne12 oit)

-- ============================================================================
-- SECTION 5: INTERPRETATION
-- ============================================================================

{-
Two generations CANNOT support CP violation.
This is equivalent to: Omega doesnt fit in Two.

Physical: CKM for 2 generations is real rotation.
DD: Z2 has no complex phase structure.

Therefore: >= 3 generations needed for CP.
-}
