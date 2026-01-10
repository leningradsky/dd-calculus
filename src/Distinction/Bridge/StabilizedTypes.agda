{-# OPTIONS --without-K --safe #-}

module Distinction.Bridge.StabilizedTypes where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)

open import Distinction.DistSystem
open import Distinction.Equivalence

private
  variable
    ℓ ℓ' ℓ'' ℓU ℓO : Level

-- =============================================================================
-- STABILIZED TYPES: Type = Stabilized Distinction
-- =============================================================================

module StabilizedTypeDef {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                         {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                         (OU : ObservableUniverse DS ℓU ℓO)
                         (RO : RefOp DS) where
                         
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  open RefOp RO
  
  open import Distinction.Stabilization
  open Trajectory RO
  
  -- =========================================================================
  -- STABILIZATION POINT
  -- =========================================================================
  
  -- x stabilizes at k₀ under trajectory from d₀
  StableAt : U → D → ℕ → Set (ℓU ⊔ ℓO)
  StableAt x d₀ k₀ = ∀ (k : ℕ) → ∀ (y : U) → 
    x ~[ traj d₀ k₀ ] y → x ~[ traj d₀ (k₀ + k) ] y
  
  -- x stabilizes somewhere (existential)
  Stabilizes : U → D → Set (ℓU ⊔ ℓO)
  Stabilizes x d₀ = ∃[ k₀ ] StableAt x d₀ k₀
  
  -- =========================================================================
  -- STABILIZED EQUIVALENCE CLASS (the carrier of a type)
  -- =========================================================================
  
  -- The stabilized class of x at d₀ after k₀
  -- This is the equivalence class [x] under ~[traj d₀ k₀]
  -- that remains unchanged for all future refinements
  
  record StabilizedClass (d₀ : D) : Set (ℓU ⊔ ℓO) where
    field
      representative : U                    -- witness element
      stabilization-point : ℕ               -- k₀
      is-stable : StableAt representative d₀ stabilization-point
  
  -- Two stabilized classes are equivalent if their representatives
  -- are equivalent at the max of their stabilization points
  StabClassEquiv : (d₀ : D) → StabilizedClass d₀ → StabilizedClass d₀ → Set ℓO
  StabClassEquiv d₀ c1 c2 = 
    let open StabilizedClass
        k = stabilization-point c1 + stabilization-point c2
    in representative c1 ~[ traj d₀ k ] representative c2
  
  -- =========================================================================
  -- ONTOLOGICAL TYPE (Typeᵒ)
  -- =========================================================================
  
  -- An ontological type is a stabilized equivalence class
  -- This is THE definition: Type = Stabilized Distinction
  
  record Typeᵒ : Set (ℓ ⊔ ℓU ⊔ ℓO) where
    field
      baseD : D                             -- starting distinguisher config
      carrier : StabilizedClass baseD       -- the stabilized class
  
  -- Membership in a type
  _∈ᵒ_ : U → Typeᵒ → Set ℓO
  x ∈ᵒ T = 
    let b = Typeᵒ.baseD T
        c = Typeᵒ.carrier T
        k = StabilizedClass.stabilization-point c
        r = StabilizedClass.representative c
    in x ~[ traj b k ] r
  
  -- =========================================================================
  -- TYPE EQUALITY (setoid-style)
  -- =========================================================================
  
  -- Two types are equal if they have same base and equivalent carriers
  -- (representatives are equivalent at combined stabilization point)
  TypeEquiv : Typeᵒ → Typeᵒ → Set (ℓ ⊔ ℓO)
  TypeEquiv T1 T2 = 
    let b1 = Typeᵒ.baseD T1
        b2 = Typeᵒ.baseD T2
        c1 = Typeᵒ.carrier T1
        c2 = Typeᵒ.carrier T2
        k = StabilizedClass.stabilization-point c1 + StabilizedClass.stabilization-point c2
        r1 = StabilizedClass.representative c1
        r2 = StabilizedClass.representative c2
    in (b1 ≡ b2) × (r1 ~[ traj b1 k ] r2)

-- =============================================================================
-- INTERPRETATION
-- =============================================================================

{-
Type = Stabilized Distinction

This module defines the core bridge concept:
- A type is NOT just U/~[d] (single distinguisher)
- A type IS a stabilized equivalence class under refinement trajectory

Key structures:
- StableAt x d₀ k₀: x's class doesn't change after step k₀
- StabilizedClass: carrier with witness, stabilization point, proof
- Typeᵒ: ontological type = base + stabilized class

This will be shown isomorphic to v0.1 Types when Φ = id.
-}
