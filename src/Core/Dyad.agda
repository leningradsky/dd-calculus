{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- Core.Dyad — Two-element structure (Z₂)
-- ============================================================================
--
-- Dyad = {d⁰, d¹} with flip operation
-- This is the seed for SU(2) (weak isospin)
-- Analogous to how Omega seeds SU(3) (color)
--
-- ============================================================================

module Core.Dyad where

open import Core.Logic

-- ============================================================================
-- DYAD TYPE
-- ============================================================================

data Dyad : Set where
  d⁰ d¹ : Dyad

-- ============================================================================
-- FLIP OPERATION
-- ============================================================================

flip : Dyad → Dyad
flip d⁰ = d¹
flip d¹ = d⁰

-- flip² = id
flip² : (x : Dyad) → flip (flip x) ≡ x
flip² d⁰ = refl
flip² d¹ = refl

-- flip ≠ id
flip≢id : ¬ ((x : Dyad) → flip x ≡ x)
flip≢id eq with eq d⁰
... | ()

-- ============================================================================
-- DISTINCTNESS
-- ============================================================================

d⁰≢d¹ : d⁰ ≢ d¹
d⁰≢d¹ ()

d¹≢d⁰ : d¹ ≢ d⁰
d¹≢d⁰ ()

-- ============================================================================
-- CASE ANALYSIS
-- ============================================================================

dyad-cases : (x : Dyad) → (x ≡ d⁰) ⊎ (x ≡ d¹)
dyad-cases d⁰ = inj₁ refl
dyad-cases d¹ = inj₂ refl

-- Decidable equality
dyad-eq : (x y : Dyad) → (x ≡ y) ⊎ (x ≢ y)
dyad-eq d⁰ d⁰ = inj₁ refl
dyad-eq d⁰ d¹ = inj₂ d⁰≢d¹
dyad-eq d¹ d⁰ = inj₂ d¹≢d⁰
dyad-eq d¹ d¹ = inj₁ refl

-- ============================================================================
-- ITERATION
-- ============================================================================

open import Core.Nat using (ℕ; zero; suc)

iterate-flip : ℕ → Dyad → Dyad
iterate-flip zero x = x
iterate-flip (suc n) x = flip (iterate-flip n x)

-- iterate-flip 2 = id
iterate-flip-2 : (x : Dyad) → iterate-flip 2 x ≡ x
iterate-flip-2 = flip²

-- Any element reachable from any other
flip-reaches : (x y : Dyad) → ∃ λ n → iterate-flip n x ≡ y
flip-reaches d⁰ d⁰ = 0 , refl
flip-reaches d⁰ d¹ = 1 , refl
flip-reaches d¹ d⁰ = 1 , refl
flip-reaches d¹ d¹ = 0 , refl
