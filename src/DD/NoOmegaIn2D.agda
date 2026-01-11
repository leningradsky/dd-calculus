{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.NoOmegaIn2D — Omega cannot be realized in 2D
-- ============================================================================
-- Pure pigeonhole: 3 elements don't fit injectively into 2.
-- ============================================================================

module DD.NoOmegaIn2D where

open import Core.Logic
open import Core.Omega

-- ============================================================================
-- TWO-ELEMENT CARRIER
-- ============================================================================

data TwoD : Set where
  a b : TwoD

a≢b : a ≢ b
a≢b ()

b≢a : b ≢ a
b≢a ()

-- ============================================================================
-- PIGEONHOLE LEMMA
-- ============================================================================

pigeonhole : (x y z : TwoD) → (x ≡ y) ⊎ (x ≡ z) ⊎ (y ≡ z)
pigeonhole a a _ = inj₁ refl
pigeonhole a b a = inj₂ (inj₁ refl)
pigeonhole a b b = inj₂ (inj₂ refl)
pigeonhole b a a = inj₂ (inj₂ refl)
pigeonhole b a b = inj₂ (inj₁ refl)
pigeonhole b b _ = inj₁ refl

-- ============================================================================
-- MAIN THEOREM
-- ============================================================================

no-inj-omega-to-2D : ¬ (Σ (Omega → TwoD) λ f → 
                         (f ω⁰ ≢ f ω¹) × (f ω⁰ ≢ f ω²) × (f ω¹ ≢ f ω²))
no-inj-omega-to-2D (f , ne01 , ne02 , ne12) with pigeonhole (f ω⁰) (f ω¹) (f ω²)
... | inj₁ eq = ne01 eq
... | inj₂ (inj₁ eq) = ne02 eq
... | inj₂ (inj₂ eq) = ne12 eq

-- ============================================================================
-- ALTERNATIVE FORMULATION
-- ============================================================================

Injective : {A B : Set} → (A → B) → Set
Injective {A} f = ∀ x y → f x ≡ f y → x ≡ y

no-omega-in-2D : ¬ (Σ (Omega → TwoD) Injective)
no-omega-in-2D (f , inj) = no-inj-omega-to-2D (f , ne01 , ne02 , ne12)
  where
  ne01 : f ω⁰ ≢ f ω¹
  ne01 eq = ω⁰≢ω¹ (inj ω⁰ ω¹ eq)
  
  ne02 : f ω⁰ ≢ f ω²
  ne02 eq = ω⁰≢ω² (inj ω⁰ ω² eq)
  
  ne12 : f ω¹ ≢ f ω²
  ne12 eq = ω¹≢ω² (inj ω¹ ω² eq)

-- ============================================================================
-- INTERPRETATION
-- ============================================================================

{-
PROVEN: ¬ ∃ injective f : Omega → TwoD
        (pigeonhole: |Omega| = 3 > 2 = |TwoD|)

CONSEQUENCE: Z₃ cannot be faithfully represented in 2-element carrier.

Physical: Qubits (2-level systems) cannot carry Z₃ charge.
Combined with ThreeD: dim = 3 is the SHARP BOUND.
-}
