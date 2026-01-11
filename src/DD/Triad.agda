{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.Triad — Triadic Structure and Gauge Group Derivation
-- ============================================================================
-- Integrated with Core.Logic and Core.Omega (unified codebase)
-- ============================================================================

module DD.Triad where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc)
open import Core.Omega public  -- re-export Omega, Phase, cycle, etc.

-- ============================================================================
-- PHASE EQUALITY DECISION
-- ============================================================================

phase-eq : (p q : Phase) → (p ≡ q) ⊎ (p ≢ q)
phase-eq φ₀ φ₀ = inj₁ refl
phase-eq φ₀ φ₁ = inj₂ φ₀≢φ₁
phase-eq φ₀ φ₂ = inj₂ φ₀≢φ₂
phase-eq φ₁ φ₀ = inj₂ φ₁≢φ₀
phase-eq φ₁ φ₁ = inj₁ refl
phase-eq φ₁ φ₂ = inj₂ φ₁≢φ₂
phase-eq φ₂ φ₀ = inj₂ φ₂≢φ₀
phase-eq φ₂ φ₁ = inj₂ φ₂≢φ₁
phase-eq φ₂ φ₂ = inj₁ refl

-- ============================================================================
-- TRIADIC CLOSURE
-- ============================================================================

record Triad : Set where
  constructor triad
  field
    t₀ t₁ t₂ : Phase

open Triad public

canonical : Triad
canonical = triad φ₀ φ₁ φ₂

IsProper : Triad → Set
IsProper t = (t₀ t ≢ t₁ t) × ((t₀ t ≢ t₂ t) × (t₁ t ≢ t₂ t))

canonical-proper : IsProper canonical
canonical-proper = φ₀≢φ₁ , (φ₀≢φ₂ , φ₁≢φ₂)

-- ============================================================================
-- TRANSFORMS
-- ============================================================================

Transform : Set
Transform = Phase → Phase

id-t : Transform
id-t p = p

-- cycle³ p ≡ p (already proven in Core.Omega as cycle³≡id)
cycle³-phase : ∀ p → cycle (cycle (cycle p)) ≡ p
cycle³-phase = cycle³≡id

cycle≢id : ¬ (∀ p → cycle p ≡ p)
cycle≢id eq = φ₀≢φ₁ (sym (eq φ₀))

cycle≢id-fun : ¬ (cycle ≡ id-t)
cycle≢id-fun eq = φ₁≢φ₀ (cong (λ f → f φ₀) eq)

-- ============================================================================
-- STRUCTURE PRESERVATION
-- ============================================================================

PreservesProper : Transform → Set
PreservesProper f = ∀ t → IsProper t → IsProper (triad (f (t₀ t)) (f (t₁ t)) (f (t₂ t)))

id-preserves : PreservesProper id-t
id-preserves _ proper = proper

-- Cycle preserves proper triads (exhaustive)
cycle-preserves : PreservesProper cycle
cycle-preserves (triad φ₀ φ₀ _) (ne01 , _) = ⊥-elim (ne01 refl)
cycle-preserves (triad φ₀ φ₁ φ₀) (_ , (ne02 , _)) = ⊥-elim (ne02 refl)
cycle-preserves (triad φ₀ φ₁ φ₁) (_ , (_ , ne12)) = ⊥-elim (ne12 refl)
cycle-preserves (triad φ₀ φ₁ φ₂) _ = φ₁≢φ₂ , (φ₁≢φ₀ , φ₂≢φ₀)
cycle-preserves (triad φ₀ φ₂ φ₀) (_ , (ne02 , _)) = ⊥-elim (ne02 refl)
cycle-preserves (triad φ₀ φ₂ φ₁) _ = φ₁≢φ₀ , (φ₁≢φ₂ , φ₀≢φ₂)
cycle-preserves (triad φ₀ φ₂ φ₂) (_ , (_ , ne12)) = ⊥-elim (ne12 refl)
cycle-preserves (triad φ₁ φ₀ φ₀) (_ , (_ , ne12)) = ⊥-elim (ne12 refl)
cycle-preserves (triad φ₁ φ₀ φ₁) (_ , (ne02 , _)) = ⊥-elim (ne02 refl)
cycle-preserves (triad φ₁ φ₀ φ₂) _ = φ₂≢φ₁ , (φ₂≢φ₀ , φ₁≢φ₀)
cycle-preserves (triad φ₁ φ₁ _) (ne01 , _) = ⊥-elim (ne01 refl)
cycle-preserves (triad φ₁ φ₂ φ₀) _ = φ₂≢φ₀ , (φ₂≢φ₁ , φ₀≢φ₁)
cycle-preserves (triad φ₁ φ₂ φ₁) (_ , (ne02 , _)) = ⊥-elim (ne02 refl)
cycle-preserves (triad φ₁ φ₂ φ₂) (_ , (_ , ne12)) = ⊥-elim (ne12 refl)
cycle-preserves (triad φ₂ φ₀ φ₀) (_ , (_ , ne12)) = ⊥-elim (ne12 refl)
cycle-preserves (triad φ₂ φ₀ φ₁) _ = φ₀≢φ₁ , (φ₀≢φ₂ , φ₁≢φ₂)
cycle-preserves (triad φ₂ φ₀ φ₂) (_ , (ne02 , _)) = ⊥-elim (ne02 refl)
cycle-preserves (triad φ₂ φ₁ φ₀) _ = φ₀≢φ₂ , (φ₀≢φ₁ , φ₂≢φ₁)
cycle-preserves (triad φ₂ φ₁ φ₁) (_ , (_ , ne12)) = ⊥-elim (ne12 refl)
cycle-preserves (triad φ₂ φ₁ φ₂) (_ , (ne02 , _)) = ⊥-elim (ne02 refl)
cycle-preserves (triad φ₂ φ₂ _) (ne01 , _) = ⊥-elim (ne01 refl)

-- ============================================================================
-- U(1) INSUFFICIENCY
-- ============================================================================

const-transform : Phase → Transform
const-transform p _ = p

const-destroys : ∀ p → ¬ PreservesProper (const-transform p)
const-destroys p pres = 
  let (ne01 , _) = pres canonical canonical-proper
  in ne01 refl

-- ============================================================================
-- ITERATION
-- ============================================================================

iterate : ℕ → Transform → Transform
iterate zero _ p = p
iterate (suc n) f p = f (iterate n f p)

-- ============================================================================
-- TRANSITIVITY
-- ============================================================================

cycle-reaches : ∀ p q → ∃[ n ] (iterate n cycle p ≡ q)
cycle-reaches φ₀ φ₀ = 0 , refl
cycle-reaches φ₀ φ₁ = 1 , refl
cycle-reaches φ₀ φ₂ = 2 , refl
cycle-reaches φ₁ φ₀ = 2 , refl
cycle-reaches φ₁ φ₁ = 0 , refl
cycle-reaches φ₁ φ₂ = 1 , refl
cycle-reaches φ₂ φ₀ = 1 , refl
cycle-reaches φ₂ φ₁ = 2 , refl
cycle-reaches φ₂ φ₂ = 0 , refl
