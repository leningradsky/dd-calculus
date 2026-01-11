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
-- MAIN THEOREM (using explicit records)
-- ============================================================================

-- Record for injective triple
record InjectiveTriple (f : Omega → TwoD) : Set where
  field
    ne01 : f ω⁰ ≢ f ω¹
    ne02 : f ω⁰ ≢ f ω²
    ne12 : f ω¹ ≢ f ω²

-- Main theorem
no-inj-omega-to-2D : ¬ (Σ (Omega → TwoD) InjectiveTriple)
no-inj-omega-to-2D p = helper (Σ.proj₁ p) (Σ.proj₂ p)
  where
    helper : (f : Omega → TwoD) → InjectiveTriple f → ⊥
    helper f inj with pigeonhole (f ω⁰) (f ω¹) (f ω²)
    ... | inj₁ eq = InjectiveTriple.ne01 inj eq
    ... | inj₂ (inj₁ eq) = InjectiveTriple.ne02 inj eq
    ... | inj₂ (inj₂ eq) = InjectiveTriple.ne12 inj eq

-- ============================================================================
-- ALTERNATIVE FORMULATION
-- ============================================================================

Injective : {A B : Set} → (A → B) → Set
Injective {A} f = ∀ x y → f x ≡ f y → x ≡ y

no-omega-in-2D : ¬ (Σ (Omega → TwoD) Injective)
no-omega-in-2D p = no-inj-omega-to-2D (Σ.proj₁ p , record { ne01 = ne01 ; ne02 = ne02 ; ne12 = ne12 })
  where
    f = Σ.proj₁ p
    inj = Σ.proj₂ p
    
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
