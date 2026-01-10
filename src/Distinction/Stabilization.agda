{-# OPTIONS --without-K --safe #-}

module Distinction.Stabilization where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Distinction.DistSystem
open import Distinction.Equivalence

private
  variable
    ℓ ℓ' ℓ'' ℓU ℓO : Level

-- =============================================================================
-- TRAJECTORY (iteration of refinement operator)
-- =============================================================================

module Trajectory {ℓ ℓ' ℓ'' : Level} 
                  {DS : AdmissibleDistSystem ℓ ℓ' ℓ''} 
                  (RO : RefOp DS) where
         
  open AdmissibleDistSystem DS
  open RefOp RO
  
  -- Trajectory: iterate Φ from initial config
  traj : D → ℕ → D
  traj d₀ zero = d₀
  traj d₀ (suc n) = Φ (traj d₀ n)
  
  -- Trajectory is monotone: earlier configs are coarser
  traj-mono : ∀ (d₀ : D) (n : ℕ) → traj d₀ n ⪯ traj d₀ (suc n)
  traj-mono d₀ n = Φ-refines (traj d₀ n)
  
  -- Trajectory preserves admissibility
  traj-adm : ∀ (d₀ : D) → Admissible d₀ → ∀ (n : ℕ) → Admissible (traj d₀ n)
  traj-adm d₀ a₀ zero = a₀
  traj-adm d₀ a₀ (suc n) = Φ-preserves-adm (traj d₀ n) (traj-adm d₀ a₀ n)

-- =============================================================================
-- STABILIZATION
-- =============================================================================

module StabilizationDef {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                        {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                        (OU : ObservableUniverse DS ℓU ℓO)
                        (RO : RefOp DS) where
                        
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  open RefOp RO
  open Trajectory RO
  
  -- Stable at step k: equivalence class doesn't change at next step
  -- Specifically: if x ~[traj k] y then x ~[traj (suc k)] y
  -- The reverse follows from monotonicity
  StableAt : U → D → ℕ → Set (ℓU ⊔ ℓO)
  StableAt x d₀ k = ∀ (y : U) → x ~[ traj d₀ k ] y → x ~[ traj d₀ (suc k) ] y
  
  -- x stabilizes from d₀ under Φ if there exists k where class stops changing
  Stabilizes : U → D → Set (ℓU ⊔ ℓO)
  Stabilizes x d₀ = ∃[ k ] StableAt x d₀ k
  
  -- Ontological: x is ontological if it stabilizes from some admissible d₀
  Onto : U → Set (ℓ ⊔ ℓ'' ⊔ ℓU ⊔ ℓO)
  Onto x = ∃[ d₀ ] (Admissible d₀ × Stabilizes x d₀)
  
  -- Nominal: x is nominal if it never stabilizes
  Nominal : U → Set (ℓ ⊔ ℓ'' ⊔ ℓU ⊔ ℓO)
  Nominal x = ¬ (Onto x)

-- =============================================================================
-- COLLAPSE THEOREM (to be proven)
-- =============================================================================

-- Sketch: If everything is nominal, there are no stable predictions
-- 
-- AllNominal : Set
-- AllNominal = ∀ x → Nominal x
-- 
-- This would mean: for every x and every admissible d₀,
-- there is no k where the class stabilizes.
-- Consequence: knowledge cannot accumulate.
