{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.NoScale — Centralizer of cycle is exactly Z₃
-- ============================================================================
-- C4.a: Aut_DD(Omega) = {id, cycle, cycle²} = Z₃
-- 
-- This file imports from Core.* instead of duplicating definitions.
-- ============================================================================

module DD.NoScale where

open import Core.Logic
open import Core.Omega

-- ============================================================================
-- TRANSFORMS
-- ============================================================================

Transform : Set
Transform = Omega → Omega

id-t : Transform
id-t = id

-- ============================================================================
-- COMMUTATION WITH CYCLE
-- ============================================================================

CommutesWithCycle : Transform → Set
CommutesWithCycle f = (x : Omega) → f (cycle x) ≡ cycle (f x)

id-commutes : CommutesWithCycle id-t
id-commutes x = refl

cycle-commutes : CommutesWithCycle cycle
cycle-commutes x = refl

cycle²-commutes : CommutesWithCycle cycle²
cycle²-commutes ω⁰ = refl
cycle²-commutes ω¹ = refl
cycle²-commutes ω² = refl

-- ============================================================================
-- KEY LEMMAS: f is determined by f(ω⁰)
-- ============================================================================

f-ω¹-determined : (f : Transform) → CommutesWithCycle f → f ω¹ ≡ cycle (f ω⁰)
f-ω¹-determined f comm = comm ω⁰

f-ω²-determined : (f : Transform) → CommutesWithCycle f → f ω² ≡ cycle² (f ω⁰)
f-ω²-determined f comm = trans (comm ω¹) (cong cycle (comm ω⁰))

-- ============================================================================
-- CLASSIFICATION BY CASES
-- ============================================================================

case-ω⁰ : (f : Transform) → CommutesWithCycle f → 
          f ω⁰ ≡ ω⁰ → (x : Omega) → f x ≡ id-t x
case-ω⁰ f comm fω⁰ ω⁰ = fω⁰
case-ω⁰ f comm fω⁰ ω¹ = trans (f-ω¹-determined f comm) (cong cycle fω⁰)
case-ω⁰ f comm fω⁰ ω² = trans (f-ω²-determined f comm) (cong cycle² fω⁰)

case-ω¹ : (f : Transform) → CommutesWithCycle f → 
          f ω⁰ ≡ ω¹ → (x : Omega) → f x ≡ cycle x
case-ω¹ f comm fω⁰ ω⁰ = fω⁰
case-ω¹ f comm fω⁰ ω¹ = trans (f-ω¹-determined f comm) (cong cycle fω⁰)
case-ω¹ f comm fω⁰ ω² = trans (f-ω²-determined f comm) (cong cycle² fω⁰)

case-ω² : (f : Transform) → CommutesWithCycle f → 
          f ω⁰ ≡ ω² → (x : Omega) → f x ≡ cycle² x
case-ω² f comm fω⁰ ω⁰ = fω⁰
case-ω² f comm fω⁰ ω¹ = trans (f-ω¹-determined f comm) (cong cycle fω⁰)
case-ω² f comm fω⁰ ω² = trans (f-ω²-determined f comm) (cong cycle² fω⁰)

-- ============================================================================
-- MAIN THEOREM
-- ============================================================================

ExtEq : Transform → Transform → Set
ExtEq f g = (x : Omega) → f x ≡ g x

omega-cases : (x : Omega) → (x ≡ ω⁰) ⊎ ((x ≡ ω¹) ⊎ (x ≡ ω²))
omega-cases ω⁰ = inj₁ refl
omega-cases ω¹ = inj₂ (inj₁ refl)
omega-cases ω² = inj₂ (inj₂ refl)

-- THEOREM: Centralizer of cycle = Z₃
centralizer-is-Z₃ : (f : Transform) → CommutesWithCycle f → 
                    (ExtEq f id-t) ⊎ ((ExtEq f cycle) ⊎ (ExtEq f cycle²))
centralizer-is-Z₃ f comm with omega-cases (f ω⁰)
... | inj₁ fω⁰≡ω⁰ = inj₁ (case-ω⁰ f comm fω⁰≡ω⁰)
... | inj₂ (inj₁ fω⁰≡ω¹) = inj₂ (inj₁ (case-ω¹ f comm fω⁰≡ω¹))
... | inj₂ (inj₂ fω⁰≡ω²) = inj₂ (inj₂ (case-ω² f comm fω⁰≡ω²))

-- ============================================================================
-- COUNTER-EXAMPLE: swap does NOT commute
-- ============================================================================

swap01 : Transform
swap01 ω⁰ = ω¹
swap01 ω¹ = ω⁰
swap01 ω² = ω²

swap01-not-commutes : ¬ (CommutesWithCycle swap01)
swap01-not-commutes comm = ω⁰≢ω² (trans (sym refl) (comm ω⁰))

-- ============================================================================
-- INTERPRETATION
-- ============================================================================

{-
THEOREM SUMMARY:

The centralizer of cycle in Aut(Omega) is EXACTLY {id, cycle, cycle²} = Z₃

IMPLICATIONS:
1. Any transformation preserving omega-structure must be a POWER OF CYCLE
2. Connection to SU(3): Center(SU(3)) = Z₃ = {I, ωI, ω²I} where ω = e^{2πi/3}
3. The det=1 condition forces scalars to be cube roots of unity
4. DD derives this constraint from pure structure

CODE REDUCTION: This file now imports Core.Logic and Core.Omega
instead of duplicating 60+ lines of basic definitions.
-}
