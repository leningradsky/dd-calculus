{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.Generation -- Why Exactly 3 Generations
-- ============================================================================

module DD.Generation where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc; _+_)
open import Core.Omega

-- ============================================================================
-- SECTION 1: GENERATION INDEX
-- ============================================================================

data Gen : Set where
  gen1 : Gen  -- (u, d, e, ve)
  gen2 : Gen  -- (c, s, mu, vmu)
  gen3 : Gen  -- (t, b, tau, vtau)

gen-count : ℕ
gen-count = 3

-- ============================================================================
-- SECTION 2: GENERATION = OMEGA ISOMORPHISM
-- ============================================================================

gen-to-omega : Gen -> Omega
gen-to-omega gen1 = ω⁰
gen-to-omega gen2 = ω¹
gen-to-omega gen3 = ω²

omega-to-gen : Omega -> Gen
omega-to-gen ω⁰ = gen1
omega-to-gen ω¹ = gen2
omega-to-gen ω² = gen3

gen-omega-gen : (g : Gen) -> omega-to-gen (gen-to-omega g) ≡ g
gen-omega-gen gen1 = refl
gen-omega-gen gen2 = refl
gen-omega-gen gen3 = refl

omega-gen-omega : (w : Omega) -> gen-to-omega (omega-to-gen w) ≡ w
omega-gen-omega ω⁰ = refl
omega-gen-omega ω¹ = refl
omega-gen-omega ω² = refl

-- Isomorphism record
record Iso (A B : Set) : Set where
  field
    to : A -> B
    from : B -> A
    to-from : (x : A) -> from (to x) ≡ x
    from-to : (y : B) -> to (from y) ≡ y

Gen-iso-Omega : Iso Gen Omega
Gen-iso-Omega = record
  { to = gen-to-omega
  ; from = omega-to-gen
  ; to-from = gen-omega-gen
  ; from-to = omega-gen-omega
  }

-- ============================================================================
-- SECTION 3: GENERATION ACTION (CYCLIC)
-- ============================================================================

next-gen : Gen -> Gen
next-gen gen1 = gen2
next-gen gen2 = gen3
next-gen gen3 = gen1

next-gen-three : (g : Gen) -> next-gen (next-gen (next-gen g)) ≡ g
next-gen-three gen1 = refl
next-gen-three gen2 = refl
next-gen-three gen3 = refl

-- ============================================================================
-- SECTION 4: DISTINCTNESS
-- ============================================================================

gen1-ne-gen2 : gen1 ≢ gen2
gen1-ne-gen2 ()

gen1-ne-gen3 : gen1 ≢ gen3
gen1-ne-gen3 ()

gen2-ne-gen3 : gen2 ≢ gen3
gen2-ne-gen3 ()

-- ============================================================================
-- SECTION 5: INTERPRETATION
-- ============================================================================

{-
WHY GENERATIONS = OMEGA:

The same structure (Omega/triad) appears at TWO levels:
- Level 1: Color charge (SU(3) from triadic closure)
- Level 2: Generation index (family replication)

Both layers inherit the same fundamental structure (Omega)
because thats what DD produces at any level.

Gen = Omega at meta-level (distinction of distinctions)
-}
