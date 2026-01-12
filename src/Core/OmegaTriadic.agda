{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- Core.OmegaTriadic — Core.Omega satisfies ForcingTriad
-- ============================================================================
--
-- This module bridges Core.Omega and Distinction.ForcingTriad,
-- showing that the triadic structure of Omega is FORCED, not arbitrary.
--
-- ============================================================================

module Core.OmegaTriadic where

open import Core.Logic
open import Core.Omega as O using (Omega; ω⁰; ω¹; ω²; cycle; cycle³≡id)
open import Distinction.ForcingTriad as F using (Automorphism; TriadicClosure; iterate)

-- ============================================================================
-- OMEGA AS AUTOMORPHISM
-- ============================================================================

-- cycle² is the inverse of cycle
cycle² : Omega → Omega
cycle² x = cycle (cycle x)

cycle-inverse-left : (x : Omega) → cycle² (cycle x) ≡ x
cycle-inverse-left ω⁰ = refl
cycle-inverse-left ω¹ = refl
cycle-inverse-left ω² = refl

cycle-inverse-right : (x : Omega) → cycle (cycle² x) ≡ x
cycle-inverse-right ω⁰ = refl
cycle-inverse-right ω¹ = refl
cycle-inverse-right ω² = refl

-- Omega cycle as Automorphism
omega-auto : Automorphism Omega
omega-auto = record
  { fun = cycle
  ; inv = cycle²
  ; left-inv = cycle-inverse-left
  ; right-inv = cycle-inverse-right
  }

-- ============================================================================
-- OMEGA SATISFIES TRIADIC CLOSURE
-- ============================================================================

-- cycle is nontrivial
cycle≢id : Σ Omega (λ x → cycle x ≢ x)
cycle≢id = ω⁰ , (λ ())

-- cycle² is nontrivial (order is not 2)
cycle²≢id : Σ Omega (λ x → iterate cycle 2 x ≢ x)
cycle²≢id = ω⁰ , (λ ())

-- iterate cycle 3 = id
iterate-cycle-3 : (x : Omega) → iterate cycle 3 x ≡ x
iterate-cycle-3 ω⁰ = refl
iterate-cycle-3 ω¹ = refl
iterate-cycle-3 ω² = refl

-- MAIN THEOREM: Omega has triadic closure
omega-triadic : TriadicClosure Omega
omega-triadic = record
  { auto = omega-auto
  ; order3 = iterate-cycle-3
  ; not-id = cycle≢id
  ; not-order2 = cycle²≢id
  }

-- ============================================================================
-- ISOMORPHISM WITH ForcingTriad.Three
-- ============================================================================

-- Forward map
Omega→Three : Omega → F.Three
Omega→Three ω⁰ = F.ω⁰
Omega→Three ω¹ = F.ω¹
Omega→Three ω² = F.ω²

-- Backward map
Three→Omega : F.Three → Omega
Three→Omega F.ω⁰ = ω⁰
Three→Omega F.ω¹ = ω¹
Three→Omega F.ω² = ω²

-- Isomorphism proofs
Omega→Three→Omega : (x : Omega) → Three→Omega (Omega→Three x) ≡ x
Omega→Three→Omega ω⁰ = refl
Omega→Three→Omega ω¹ = refl
Omega→Three→Omega ω² = refl

Three→Omega→Three : (x : F.Three) → Omega→Three (Three→Omega x) ≡ x
Three→Omega→Three F.ω⁰ = refl
Three→Omega→Three F.ω¹ = refl
Three→Omega→Three F.ω² = refl

-- Cycle commutes with isomorphism
cycle-commutes : (x : Omega) → Omega→Three (cycle x) ≡ F.cycle₃ (Omega→Three x)
cycle-commutes ω⁰ = refl
cycle-commutes ω¹ = refl
cycle-commutes ω² = refl

-- ============================================================================
-- CONCLUSION
-- ============================================================================

{-
This module proves:

1. Core.Omega.Omega has triadic closure (omega-triadic)
2. Core.Omega.Omega ≅ ForcingTriad.Three (isomorphism)
3. The cycle operations correspond (cycle-commutes)

Combined with ForcingTriad's proofs that:
- One cannot have triadic closure
- Two cannot have triadic closure
- Three is the minimum

This establishes: |Omega| = 3 is FORCED by the axioms, not postulated.
-}
