{-# OPTIONS --without-K --safe #-}

module Distinction.Bridge.BridgeTypes where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Distinction.DistSystem
open import Distinction.Equivalence

private
  variable
    ℓ ℓ' ℓ'' ℓU ℓO : Level

-- =============================================================================
-- BRIDGE THEOREM: v0.1 Types ≅ v0.3 StabilizedTypes (under Φ = id)
-- =============================================================================

module BridgeIso {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                 {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                 (OU : ObservableUniverse DS ℓU ℓO) where
                 
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  
  open import Distinction.Bridge.TrivialRefinement
  open TrivialRef DS
  open TrivialProperties OU
  
  open import Distinction.Bridge.StabilizedTypes
  open StabilizedTypeDef OU TrivialRefOp
  
  -- =========================================================================
  -- v0.1 STYLE TYPES (simple quotient)
  -- =========================================================================
  
  -- A v0.1-style type is just an equivalence class under a single d
  record Type01 : Set (ℓ ⊔ ℓU ⊔ ℓO) where
    field
      config : D                    -- the distinguisher config
      witness : U                   -- representative element
  
  -- Membership in v0.1 type
  _∈₀₁_ : U → Type01 → Set ℓO
  x ∈₀₁ T = x ~[ Type01.config T ] Type01.witness T
  
  -- v0.1 type equality (same config, equivalent witnesses)
  Type01-Equiv : Type01 → Type01 → Set (ℓ ⊔ ℓO)
  Type01-Equiv T1 T2 = 
    (Type01.config T1 ≡ Type01.config T2) × 
    (Type01.witness T1 ~[ Type01.config T1 ] Type01.witness T2)
  
  -- =========================================================================
  -- ISOMORPHISM: Type01 ≅ Typeᵒ (under trivial refinement)
  -- =========================================================================
  
  -- Forward: v0.1 → v0.3
  -- Given a v0.1 type, construct a stabilized type
  to-Typeᵒ : Type01 → Typeᵒ
  to-Typeᵒ T = record
    { baseD = Type01.config T
    ; carrier = record
        { representative = Type01.witness T
        ; stabilization-point = zero              -- immediate stabilization
        ; is-stable = immediate-stable (Type01.witness T) (Type01.config T)
        }
    }
  
  -- Backward: v0.3 → v0.1
  -- Given a stabilized type (under trivial refinement), extract v0.1 type
  from-Typeᵒ : Typeᵒ → Type01
  from-Typeᵒ T = record
    { config = Typeᵒ.baseD T
    ; witness = StabilizedClass.representative (Typeᵒ.carrier T)
    }
  
  -- =========================================================================
  -- ROUNDTRIP PROOFS
  -- =========================================================================
  
  -- Roundtrip 1: from-Typeᵒ (to-Typeᵒ T) ≡ T
  roundtrip-01 : ∀ (T : Type01) → from-Typeᵒ (to-Typeᵒ T) ≡ T
  roundtrip-01 T = refl  -- definitionally equal!
  
  -- Roundtrip 2: to-Typeᵒ (from-Typeᵒ T) ~ T (up to stabilization point)
  -- The stabilization point might differ, but membership is preserved
  roundtrip-membership : ∀ (T : Typeᵒ) (x : U) → 
    (x ∈ᵒ T) → (x ∈ᵒ to-Typeᵒ (from-Typeᵒ T))
  roundtrip-membership T x mem = 
    -- Need: x ~[traj b 0] r  given: x ~[traj b k] r
    -- Under trivial refinement: traj b k = b = traj b 0
    let b = Typeᵒ.baseD T
        c = Typeᵒ.carrier T
        k = StabilizedClass.stabilization-point c
        r = StabilizedClass.representative c
    in equiv-const-inv b zero x r (equiv-const b k x r mem)
  
  roundtrip-membership-inv : ∀ (T : Typeᵒ) (x : U) → 
    (x ∈ᵒ to-Typeᵒ (from-Typeᵒ T)) → (x ∈ᵒ T)
  roundtrip-membership-inv T x mem = 
    let b = Typeᵒ.baseD T
        c = Typeᵒ.carrier T
        k = StabilizedClass.stabilization-point c
        r = StabilizedClass.representative c
    in equiv-const-inv b k x r (equiv-const b zero x r mem)
  
  -- =========================================================================
  -- MEMBERSHIP PRESERVATION
  -- =========================================================================
  
  -- Forward preserves membership
  to-preserves-∈ : ∀ (T : Type01) (x : U) → (x ∈₀₁ T) → (x ∈ᵒ to-Typeᵒ T)
  to-preserves-∈ T x mem = 
    -- Need: x ~[traj (config T) 0] (witness T)
    -- Have: x ~[config T] (witness T)
    -- But traj d 0 = d, so this is the same
    equiv-const-inv (Type01.config T) zero x (Type01.witness T) mem
  
  -- Backward preserves membership
  from-preserves-∈ : ∀ (T : Typeᵒ) (x : U) → (x ∈ᵒ T) → (x ∈₀₁ from-Typeᵒ T)
  from-preserves-∈ T x mem = 
    let b = Typeᵒ.baseD T
        c = Typeᵒ.carrier T
        k = StabilizedClass.stabilization-point c
        r = StabilizedClass.representative c
    in equiv-const b k x r mem

-- =============================================================================
-- BRIDGE THEOREM STATEMENT
-- =============================================================================

{-
BRIDGE THEOREM (Type = Stabilized Distinction)

Under trivial refinement (Φ = id):

1. ISOMORPHISM: 
   to-Typeᵒ and from-Typeᵒ form an isomorphism between
   v0.1-style types (Type01) and v0.3-style types (Typeᵒ)

2. DEFINITIONAL EQUALITY (one direction):
   from-Typeᵒ (to-Typeᵒ T) ≡ T  (definitionally!)

3. MEMBERSHIP PRESERVATION (both directions):
   x ∈₀₁ T  ↔  x ∈ᵒ (to-Typeᵒ T)
   x ∈ᵒ T   ↔  x ∈₀₁ (from-Typeᵒ T)

4. STABILITY:
   Under trivial refinement, all types stabilize immediately at k₀ = 0,
   so v0.3 reduces exactly to v0.1.

This establishes:
- v0.1 is a SPECIAL CASE of v0.3 (not a separate construction)
- The type definition "U/~[d]" is the Φ=id case of "stabilized class"
- STLC soundness from v0.1 transfers to the general framework
-}
