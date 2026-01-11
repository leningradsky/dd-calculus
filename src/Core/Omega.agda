{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- Core.Omega — The fundamental triadic structure
-- ============================================================================
-- Omega = {ω⁰, ω¹, ω²} with cycle: ω⁰ → ω¹ → ω² → ω⁰
-- This is the minimal structure forced by closure (T1).
-- 
-- Key results:
--   - cycle³ = id (triadic closure)
--   - All elements distinct
--   - Centralizer(cycle) = Z₃
-- ============================================================================

module Core.Omega where

open import Core.Logic

-- ============================================================================
-- OMEGA TYPE
-- ============================================================================

data Omega : Set where
  ω⁰ ω¹ ω² : Omega

-- Alternative names for DD/* compatibility
w0 w1 w2 : Omega
w0 = ω⁰
w1 = ω¹
w2 = ω²

-- ============================================================================
-- DISTINCTNESS
-- ============================================================================

ω⁰≢ω¹ : ω⁰ ≢ ω¹
ω⁰≢ω¹ ()

ω⁰≢ω² : ω⁰ ≢ ω²
ω⁰≢ω² ()

ω¹≢ω⁰ : ω¹ ≢ ω⁰
ω¹≢ω⁰ ()

ω¹≢ω² : ω¹ ≢ ω²
ω¹≢ω² ()

ω²≢ω⁰ : ω² ≢ ω⁰
ω²≢ω⁰ ()

ω²≢ω¹ : ω² ≢ ω¹
ω²≢ω¹ ()

-- DD/* compatibility names
w0≢w1 : w0 ≢ w1
w0≢w1 = ω⁰≢ω¹

w0≢w2 : w0 ≢ w2
w0≢w2 = ω⁰≢ω²

w1≢w0 : w1 ≢ w0
w1≢w0 = ω¹≢ω⁰

w1≢w2 : w1 ≢ w2
w1≢w2 = ω¹≢ω²

w2≢w0 : w2 ≢ w0
w2≢w0 = ω²≢ω⁰

w2≢w1 : w2 ≢ w1
w2≢w1 = ω²≢ω¹

-- ============================================================================
-- DECIDABLE EQUALITY
-- ============================================================================

_≟_ : (x y : Omega) → Dec (x ≡ y)
ω⁰ ≟ ω⁰ = yes refl
ω⁰ ≟ ω¹ = no ω⁰≢ω¹
ω⁰ ≟ ω² = no ω⁰≢ω²
ω¹ ≟ ω⁰ = no ω¹≢ω⁰
ω¹ ≟ ω¹ = yes refl
ω¹ ≟ ω² = no ω¹≢ω²
ω² ≟ ω⁰ = no ω²≢ω⁰
ω² ≟ ω¹ = no ω²≢ω¹
ω² ≟ ω² = yes refl

-- ============================================================================
-- CYCLE OPERATION
-- ============================================================================

cycle : Omega → Omega
cycle ω⁰ = ω¹
cycle ω¹ = ω²
cycle ω² = ω⁰

-- ============================================================================
-- TRIADIC CLOSURE: cycle³ = id
-- ============================================================================

cycle² : Omega → Omega
cycle² = cycle ∘ cycle

cycle³ : Omega → Omega
cycle³ = cycle ∘ cycle²

-- Point-wise proofs
cycle³-ω⁰ : cycle³ ω⁰ ≡ ω⁰
cycle³-ω⁰ = refl

cycle³-ω¹ : cycle³ ω¹ ≡ ω¹
cycle³-ω¹ = refl

cycle³-ω² : cycle³ ω² ≡ ω²
cycle³-ω² = refl

-- Main theorem: cycle³ = id (extensionally)
cycle³≡id : ∀ (x : Omega) → cycle³ x ≡ x
cycle³≡id ω⁰ = refl
cycle³≡id ω¹ = refl
cycle³≡id ω² = refl

-- ============================================================================
-- CYCLE IS INJECTIVE
-- ============================================================================

cycle-injective : ∀ {x y} → cycle x ≡ cycle y → x ≡ y
cycle-injective {ω⁰} {ω⁰} _ = refl
cycle-injective {ω⁰} {ω¹} ()
cycle-injective {ω⁰} {ω²} ()
cycle-injective {ω¹} {ω⁰} ()
cycle-injective {ω¹} {ω¹} _ = refl
cycle-injective {ω¹} {ω²} ()
cycle-injective {ω²} {ω⁰} ()
cycle-injective {ω²} {ω¹} ()
cycle-injective {ω²} {ω²} _ = refl

-- ============================================================================
-- CYCLE IS SURJECTIVE (hence bijective)
-- ============================================================================

cycle-surjective : ∀ y → ∃[ x ] (cycle x ≡ y)
cycle-surjective ω⁰ = ω² , refl
cycle-surjective ω¹ = ω⁰ , refl
cycle-surjective ω² = ω¹ , refl

-- ============================================================================
-- INVERSE OF CYCLE
-- ============================================================================

cycle⁻¹ : Omega → Omega
cycle⁻¹ = cycle²  -- cycle² = cycle⁻¹ because cycle³ = id

cycle⁻¹-left : ∀ x → cycle⁻¹ (cycle x) ≡ x
cycle⁻¹-left ω⁰ = refl
cycle⁻¹-left ω¹ = refl
cycle⁻¹-left ω² = refl

cycle⁻¹-right : ∀ x → cycle (cycle⁻¹ x) ≡ x
cycle⁻¹-right ω⁰ = refl
cycle⁻¹-right ω¹ = refl
cycle⁻¹-right ω² = refl

-- ============================================================================
-- Z₃ AS AUTOMORPHISM GROUP
-- ============================================================================

-- The only automorphisms of Omega preserving cycle are: id, cycle, cycle²
-- This is proven in DD/NoScale.agda (centralizer = Z₃)

data Z₃ : Set where
  z₀ z₁ z₂ : Z₃

-- Z₃ action on Omega
z₃-act : Z₃ → Omega → Omega
z₃-act z₀ = id
z₃-act z₁ = cycle
z₃-act z₂ = cycle²

-- Z₃ addition
_+z₃_ : Z₃ → Z₃ → Z₃
z₀ +z₃ y = y
z₁ +z₃ z₀ = z₁
z₁ +z₃ z₁ = z₂
z₁ +z₃ z₂ = z₀
z₂ +z₃ z₀ = z₂
z₂ +z₃ z₁ = z₀
z₂ +z₃ z₂ = z₁

-- Action is homomorphism: z₃-act (a + b) = z₃-act a ∘ z₃-act b
z₃-act-homo : ∀ a b x → z₃-act (a +z₃ b) x ≡ z₃-act a (z₃-act b x)
z₃-act-homo z₀ _ _ = refl
z₃-act-homo z₁ z₀ x = refl
z₃-act-homo z₁ z₁ ω⁰ = refl
z₃-act-homo z₁ z₁ ω¹ = refl
z₃-act-homo z₁ z₁ ω² = refl
z₃-act-homo z₁ z₂ x = sym (cycle³≡id x)
z₃-act-homo z₂ z₀ x = refl
z₃-act-homo z₂ z₁ x = sym (cycle³≡id x)
z₃-act-homo z₂ z₂ x = cong cycle (sym (cycle³≡id x))

-- ============================================================================
-- OMEGA MULTIPLICATION (Z₃ group operation)
-- ============================================================================

-- This is the group operation on Z₃ embedded in Omega
-- ω^a · ω^b = ω^(a+b mod 3)
_·ω_ : Omega → Omega → Omega
ω⁰ ·ω x = x
ω¹ ·ω ω⁰ = ω¹
ω¹ ·ω ω¹ = ω²
ω¹ ·ω ω² = ω⁰
ω² ·ω ω⁰ = ω²
ω² ·ω ω¹ = ω⁰
ω² ·ω ω² = ω¹

infixl 7 _·ω_

-- ω⁰ is identity
·ω-identityˡ : ∀ x → ω⁰ ·ω x ≡ x
·ω-identityˡ _ = refl

·ω-identityʳ : ∀ x → x ·ω ω⁰ ≡ x
·ω-identityʳ ω⁰ = refl
·ω-identityʳ ω¹ = refl
·ω-identityʳ ω² = refl

-- Multiplication is associative
·ω-assoc : ∀ x y z → (x ·ω y) ·ω z ≡ x ·ω (y ·ω z)
·ω-assoc ω⁰ _ _ = refl
·ω-assoc ω¹ ω⁰ _ = refl
·ω-assoc ω¹ ω¹ ω⁰ = refl
·ω-assoc ω¹ ω¹ ω¹ = refl
·ω-assoc ω¹ ω¹ ω² = refl
·ω-assoc ω¹ ω² ω⁰ = refl
·ω-assoc ω¹ ω² ω¹ = refl
·ω-assoc ω¹ ω² ω² = refl
·ω-assoc ω² ω⁰ _ = refl
·ω-assoc ω² ω¹ ω⁰ = refl
·ω-assoc ω² ω¹ ω¹ = refl
·ω-assoc ω² ω¹ ω² = refl
·ω-assoc ω² ω² ω⁰ = refl
·ω-assoc ω² ω² ω¹ = refl
·ω-assoc ω² ω² ω² = refl

-- Connection: cycle x = ω¹ ·ω x
cycle-is-mult : ∀ x → cycle x ≡ ω¹ ·ω x
cycle-is-mult ω⁰ = refl
cycle-is-mult ω¹ = refl
cycle-is-mult ω² = refl

-- ============================================================================
-- PHASE ALIAS (for compatibility with DD.Triad)
-- ============================================================================

Phase : Set
Phase = Omega

pattern φ₀ = ω⁰
pattern φ₁ = ω¹
pattern φ₂ = ω²

-- Phase distinctness (aliases for Triad compatibility)
φ₀≢φ₁ : φ₀ ≢ φ₁
φ₀≢φ₁ = ω⁰≢ω¹

φ₀≢φ₂ : φ₀ ≢ φ₂
φ₀≢φ₂ = ω⁰≢ω²

φ₁≢φ₀ : φ₁ ≢ φ₀
φ₁≢φ₀ = ω¹≢ω⁰

φ₁≢φ₂ : φ₁ ≢ φ₂
φ₁≢φ₂ = ω¹≢ω²

φ₂≢φ₀ : φ₂ ≢ φ₀
φ₂≢φ₀ = ω²≢ω⁰

φ₂≢φ₁ : φ₂ ≢ φ₁
φ₂≢φ₁ = ω²≢ω¹

-- ============================================================================
-- INTERPRETATION
-- ============================================================================

{-
Core.Omega captures the fundamental triadic structure:

1. EXISTENCE: Omega = {ω⁰, ω¹, ω²} - three distinct phases
2. CYCLE: ω⁰ → ω¹ → ω² → ω⁰ - the minimal non-trivial permutation
3. CLOSURE: cycle³ = id - triadic closure (forced by T1)
4. SYMMETRY: Aut(Omega) = Z₃ - minimal symmetry group

This structure is:
- Forced by the existence of distinction (Δ ≠ ∅)
- The seed of SU(3) gauge symmetry
- The basis for 3-dimensional space

Connection to physics:
- Omega ↔ color charge (r, g, b)
- cycle ↔ cyclic permutation of colors
- Z₃ ↔ center of SU(3)
-}
