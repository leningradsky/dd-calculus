{-# OPTIONS --without-K --safe #-}

module Distinction.Bridge.TrivialRefinement where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Distinction.DistSystem
open import Distinction.Equivalence

private
  variable
    ℓ ℓ' ℓ'' ℓU ℓO : Level

-- =============================================================================
-- TRIVIAL REFINEMENT: Φ = id
-- =============================================================================

-- When Φ = id, refinement does nothing.
-- This is the v0.1 case: no dynamics, static distinguisher.

module TrivialRef {ℓ ℓ' ℓ'' : Level}
                  (DS : AdmissibleDistSystem ℓ ℓ' ℓ'') where
                  
  open AdmissibleDistSystem DS
  
  -- The trivial refinement operator: Φ = id
  TrivialΦ : D → D
  TrivialΦ d = d
  
  -- Proof that id refines (trivially: d ⪯ d always holds by refl)
  TrivialΦ-refines : ∀ d → d ⪯ d
  TrivialΦ-refines d = ⪯-refl d
  
  -- Proof that id preserves admissibility (trivially)
  TrivialΦ-preserves-adm : ∀ d → Admissible d → Admissible d
  TrivialΦ-preserves-adm d adm = adm
  
  -- Package as RefOp
  TrivialRefOp : RefOp DS
  TrivialRefOp = record 
    { Φ = TrivialΦ 
    ; Φ-refines = TrivialΦ-refines
    ; Φ-preserves-adm = TrivialΦ-preserves-adm
    }

-- =============================================================================
-- PROPERTIES OF TRIVIAL REFINEMENT
-- =============================================================================

module TrivialProperties {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                         {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                         (OU : ObservableUniverse DS ℓU ℓO) where
                         
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  open TrivialRef DS
  
  open import Distinction.Stabilization
  open Trajectory TrivialRefOp
  
  -- =========================================================================
  -- KEY LEMMA: Trivial trajectory is constant
  -- =========================================================================
  
  -- traj d₀ k = d₀ for all k
  traj-const : ∀ (d₀ : D) (k : ℕ) → traj d₀ k ≡ d₀
  traj-const d₀ zero = refl
  traj-const d₀ (suc k) = traj-const d₀ k  -- Φ (traj d₀ k) = traj d₀ k = d₀
  
  -- =========================================================================
  -- COROLLARY: Equivalence is constant along trajectory
  -- =========================================================================
  
  -- ~[traj d₀ k] = ~[d₀] for all k
  equiv-const : ∀ (d₀ : D) (k : ℕ) (x y : U) → 
                x ~[ traj d₀ k ] y → x ~[ d₀ ] y
  equiv-const d₀ k x y eq = subst (λ d → x ~[ d ] y) (traj-const d₀ k) eq
    where open import Relation.Binary.PropositionalEquality using (subst)
  
  equiv-const-inv : ∀ (d₀ : D) (k : ℕ) (x y : U) → 
                    x ~[ d₀ ] y → x ~[ traj d₀ k ] y
  equiv-const-inv d₀ k x y eq = subst (λ d → x ~[ d ] y) (sym (traj-const d₀ k)) eq
    where open import Relation.Binary.PropositionalEquality using (subst)
  
  -- =========================================================================
  -- IMMEDIATE STABILIZATION
  -- =========================================================================
  
  open import Distinction.Bridge.StabilizedTypes
  open StabilizedTypeDef OU TrivialRefOp
  
  -- Under trivial refinement, everything stabilizes immediately at k₀ = 0
  immediate-stable : ∀ (x : U) (d₀ : D) → StableAt x d₀ zero
  immediate-stable x d₀ k y eq = 
    -- Need: x ~[traj d₀ 0] y → x ~[traj d₀ (0+k)] y
    -- But traj d₀ 0 = d₀ and traj d₀ k = d₀
    -- So this is: x ~[d₀] y → x ~[d₀] y
    equiv-const-inv d₀ k x y (equiv-const d₀ zero x y eq)
  
  -- Everything stabilizes under trivial refinement
  all-stabilize : ∀ (x : U) (d₀ : D) → Stabilizes x d₀
  all-stabilize x d₀ = zero , immediate-stable x d₀

-- =============================================================================
-- INTERPRETATION
-- =============================================================================

{-
Trivial Refinement (Φ = id)

This is the v0.1 case:
- No refinement dynamics: Φ d = d
- Trajectory is constant: traj d₀ k = d₀ for all k
- Equivalence is constant: ~[traj d₀ k] = ~[d₀]
- Immediate stabilization: everything stabilizes at k₀ = 0

This means:
- StabilizedClass under trivial refinement ≅ plain equivalence class under d₀
- Typeᵒ under trivial refinement ≅ v0.1 Type (U/~[d₀])

The bridge isomorphism will use these lemmas.
-}
