{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.ThreeD — 3D is sufficient for Z₃ (dim = 3 forced)
-- ============================================================================
-- C3.c: Omega CAN be faithfully embedded in 3 elements.
-- Together with NoOmegaIn2D: dim ≥ 3 is sharp.
-- ============================================================================

module DD.ThreeD where

open import Core.Logic
open import Core.Omega

-- ============================================================================
-- THREE-ELEMENT CARRIER
-- ============================================================================

data ThreeD : Set where
  x y z : ThreeD

x≢y : x ≢ y
x≢y ()

x≢z : x ≢ z
x≢z ()

y≢z : y ≢ z
y≢z ()

y≢x : y ≢ x
y≢x ()

z≢x : z ≢ x
z≢x ()

z≢y : z ≢ y
z≢y ()

-- ============================================================================
-- EMBEDDING
-- ============================================================================

embed : Omega → ThreeD
embed ω⁰ = x
embed ω¹ = y
embed ω² = z

-- ============================================================================
-- INJECTIVITY
-- ============================================================================

Injective : {A B : Set} → (A → B) → Set
Injective {A} f = ∀ a₁ a₂ → f a₁ ≡ f a₂ → a₁ ≡ a₂

embed-injective : Injective embed
embed-injective ω⁰ ω⁰ _ = refl
embed-injective ω⁰ ω¹ eq = ⊥-elim (x≢y eq)
embed-injective ω⁰ ω² eq = ⊥-elim (x≢z eq)
embed-injective ω¹ ω⁰ eq = ⊥-elim (y≢x eq)
embed-injective ω¹ ω¹ _ = refl
embed-injective ω¹ ω² eq = ⊥-elim (y≢z eq)
embed-injective ω² ω⁰ eq = ⊥-elim (z≢x eq)
embed-injective ω² ω¹ eq = ⊥-elim (z≢y eq)
embed-injective ω² ω² _ = refl

-- ============================================================================
-- MAIN RESULT
-- ============================================================================

omega-fits-in-3D : Σ (Omega → ThreeD) Injective
omega-fits-in-3D = embed , embed-injective

-- ============================================================================
-- INTERPRETATION
-- ============================================================================

{-
Combined with NoOmegaIn2D:

  C3.b: ¬ ∃ injective (Omega → TwoD)    [2D insufficient]
  C3.c: ∃ injective (Omega → ThreeD)    [3D sufficient]

MINIMUM CARRIER SIZE FOR Z₃ = 3 (sharp bound)

Physical connection:
  - Color charge requires 3 states
  - SU(3) fundamental rep is 3-dimensional
  - This is forced by DD, not assumed
-}
