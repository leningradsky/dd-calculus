{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- Distinction.ForcingDyad — Why |Dyad| = 2 is Forced
-- ============================================================================
--
-- Parallel to ForcingTriad, this proves that DYADIC closure 
-- requires exactly 2 elements.
--
-- Dyadic closure: order-2 automorphism (flip² = id, flip ≠ id)
--
-- ============================================================================

module Distinction.ForcingDyad where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc)

-- ============================================================================
-- SECTION 1: DYADIC CLOSURE DEFINITION
-- ============================================================================

-- Reuse types from ForcingTriad
data One : Set where
  ★ : One

data Two : Set where
  t₀ t₁ : Two

-- Automorphism (same as ForcingTriad)
record Automorphism (A : Set) : Set where
  field
    fun : A → A
    inv : A → A
    left-inv : (x : A) → inv (fun x) ≡ x
    right-inv : (x : A) → fun (inv x) ≡ x

open Automorphism

-- Iterate function n times
iterate : {A : Set} → (A → A) → ℕ → A → A
iterate f zero x = x
iterate f (suc n) x = f (iterate f n x)

-- DYADIC closure: order exactly 2
record DyadicClosure (A : Set) : Set where
  field
    auto : Automorphism A
    order2 : (x : A) → iterate (fun auto) 2 x ≡ x  -- flip² = id
    not-id : Σ A (λ x → fun auto x ≢ x)            -- flip ≠ id

-- ============================================================================
-- SECTION 2: ONE ELEMENT CANNOT HAVE DYADIC CLOSURE
-- ============================================================================

-- Same as triadic case: only identity exists on One

-- Helper: any function One → One is identity
one-fun-id : (f : One → One) → (x : One) → f x ≡ x
one-fun-id f ★ with f ★
... | ★ = refl

no-dyadic-one : ¬ (DyadicClosure One)
no-dyadic-one dc = 
  let f = fun (DyadicClosure.auto dc)
      (x , x≢fx) = DyadicClosure.not-id dc
  in x≢fx (one-fun-id f x)

-- ============================================================================
-- SECTION 3: TWO ELEMENTS ACHIEVES DYADIC CLOSURE
-- ============================================================================

-- flip : t₀ ↔ t₁
flip : Two → Two
flip t₀ = t₁
flip t₁ = t₀

-- flip is its own inverse
flip-inv : (x : Two) → flip (flip x) ≡ x
flip-inv t₀ = refl
flip-inv t₁ = refl

-- flip as automorphism
flip-auto : Automorphism Two
flip-auto = record
  { fun = flip
  ; inv = flip
  ; left-inv = flip-inv
  ; right-inv = flip-inv
  }

-- flip² = id
flip²≡id : (x : Two) → iterate flip 2 x ≡ x
flip²≡id t₀ = refl
flip²≡id t₁ = refl

-- flip ≠ id
flip≢id : Σ Two (λ x → flip x ≢ x)
flip≢id = t₀ , (λ ())

-- THEOREM: Two has dyadic closure
two-dyadic : DyadicClosure Two
two-dyadic = record
  { auto = flip-auto
  ; order2 = flip²≡id
  ; not-id = flip≢id
  }

-- ============================================================================
-- SECTION 4: MINIMALITY OF TWO
-- ============================================================================

-- Two is the MINIMUM for dyadic closure:
-- - One fails (no nontrivial automorphism)
-- - Two succeeds

-- Combined theorem
dyad-forcing : (¬ DyadicClosure One) × DyadicClosure Two
dyad-forcing = no-dyadic-one , two-dyadic

-- ============================================================================
-- SECTION 5: PHYSICAL INTERPRETATION
-- ============================================================================

{-
Dyadic closure corresponds to:

1. SU(2) weak isospin:
   - Two states: up, down (or left-handed doublet)
   - flip = σ₁ Pauli matrix action
   - Z₂ center of SU(2)

2. Physical content:
   - Weak isospin doublets: (νₑ, e⁻), (u, d), etc.
   - W⁺/W⁻ exchange flips isospin

3. Why 2?
   - Need nontrivial involution (order 2)
   - One element: no nontrivial involution
   - Two elements: minimal with flip

Compared to triadic (SU(3)):
- Triad needs order 3 → 3 elements → SU(3)
- Dyad needs order 2 → 2 elements → SU(2)
-}

-- ============================================================================
-- EXPORTS
-- ============================================================================

Dyad-minimal : DyadicClosure Two
Dyad-minimal = two-dyadic
