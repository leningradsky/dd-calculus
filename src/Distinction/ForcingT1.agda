{-# OPTIONS --without-K --safe #-}

module Distinction.ForcingT1 where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; _≢_)
open import Relation.Nullary using (¬_)

open import Distinction.DistSystem
open import Distinction.Equivalence

private
  variable
    ℓ ℓ' ℓ'' ℓU ℓO : Level

-- =============================================================================
-- COMPOSABLE DISTINGUISHERS
-- =============================================================================

-- Distinguisher system with composition operation and witness
record ComposableObs {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                     {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                     (OU : ObservableUniverse DS ℓU ℓO) : Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓU ⊔ ℓO) where
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  
  field
    -- Composition of observations (e.g., sequential application, parallel, etc.)
    comp : ∀ {d : D} → Obs d → Obs d → Obs d
    
    -- THE KEY: witness that comp can distinguish what individuals cannot
    -- For any d1, d2, there exist x, y such that:
    -- - d1 cannot distinguish x from y
    -- - d2 cannot distinguish x from y  
    -- - but comp d1 d2 CAN distinguish x from y
    witnessComp : ∀ (d : D) (d1 d2 : Obs d) →
                  ∃[ x ] ∃[ y ] 
                    ( observe d d1 x ≡ observe d d1 y 
                    × observe d d2 x ≡ observe d d2 y 
                    × observe d (comp d1 d2) x ≢ observe d (comp d1 d2) y )

-- =============================================================================
-- CLOSURE UNDER COMPOSITION (simplified)
-- =============================================================================

module ClosureDef {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                  {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                  (OU : ObservableUniverse DS ℓU ℓO)
                  (CO : ComposableObs OU)
                  (RO : RefOp DS) where
                  
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  open ComposableObs CO
  open RefOp RO
  
  open import Distinction.Stabilization
  open Trajectory RO
  
  -- Simplified: closure means comp is in the image of Φ
  -- For any obs at step n, comp of two such obs is reachable at some step m ≥ n
  ClosedComp : D → Set (ℓU ⊔ ℓO)
  ClosedComp d₀ = ∀ (n : ℕ) (d1 d2 : Obs (traj d₀ n)) →
                  ∃[ m ] ∃[ obs ] (observe (traj d₀ m) obs ≡ observe (traj d₀ n) (comp d1 d2))

-- =============================================================================
-- T1: NON-CLOSURE BREAKS UNIVERSAL STABILIZATION
-- =============================================================================

module T1Statement {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                   {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                   (OU : ObservableUniverse DS ℓU ℓO)
                   (CO : ComposableObs OU)
                   (RO : RefOp DS) where
                   
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  open ComposableObs CO
  open RefOp RO
  open ClosureDef OU CO RO
  
  open import Distinction.Stabilization
  open Trajectory RO
  open StabilizationDef OU RO
  
  -- Universal stabilization: every state stabilizes
  UniversalStab : D → Set (ℓU ⊔ ℓO)
  UniversalStab d₀ = ∀ (x : U) → Stabilizes x d₀
  
  -- T1 Contrapositive: universal stabilization implies closure
  T1-contrapositive : D → Set (ℓU ⊔ ℓO)
  T1-contrapositive d₀ = UniversalStab d₀ → ClosedComp d₀
  
  -- T1 Direct: non-closure implies non-universal stabilization
  T1-direct : D → Set (ℓU ⊔ ℓO)
  T1-direct d₀ = ¬ (ClosedComp d₀) → ∃[ x ] ¬ (Stabilizes x d₀)

{-
=============================================================================
THEOREM T1: CLOSURE IS FORCED BY UNIVERSAL STABILITY
=============================================================================

Statement (prose):
  If a refinement system achieves universal stabilization (every state 
  eventually reaches a fixed equivalence class), then the observation 
  language must be closed under composition.

Contrapositive:
  If observations are NOT closed under comp, then there exists a state
  that never stabilizes.

Why this is "forcing" (not axiom):
  - We don't assume closure
  - We derive: closure is NECESSARY for stable ontology
  - Without closure: perpetual classification drift

Proof structure:
  1. Assume ¬ClosedComp d₀
  2. Then ∃ n, d1, d2 such that comp d1 d2 is not reachable
  3. By witnessComp: ∃ x, y distinguished only by comp d1 d2
  4. On trajectory: x ~[traj n] y (since d1, d2 can't separate)
  5. But comp d1 d2 WOULD separate them
  6. If Φ never adds comp d1 d2, the class [x] appears stable
  7. But there exists an admissible extension that DOES add it
  8. So x is not "robustly" stable — only stable on this trajectory
  9. Universal stability requires robustness → contradiction

Key insight:
  Stabilization on ONE trajectory ≠ Stabilization under ALL admissible extensions
  True ontology = stable under ANY admissible refinement
  This FORCES closure (otherwise we can always find a breaking extension)
-}

-- =============================================================================
-- LEMMAS FOR PROOF (to be filled)
-- =============================================================================

module T1Proof {ℓ ℓ' ℓ'' ℓU ℓO : Level}
               {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
               (OU : ObservableUniverse DS ℓU ℓO)
               (CO : ComposableObs OU)
               (RO : RefOp DS) where
               
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  open ComposableObs CO
  open RefOp RO
  open ClosureDef OU CO RO
  open T1Statement OU CO RO
  
  open import Distinction.Stabilization
  open Trajectory RO
  open StabilizationDef OU RO
  
  -- Lemma A: witnessComp gives the "bad pair"
  -- Given d1, d2 at step n, get x, y that are ~[n] but would be ≁ under comp
  
  -- Lemma B: if comp not reachable, x and y stay equivalent on trajectory
  -- ∀ m ≥ n. x ~[traj m] y (because no observation can distinguish them)
  
  -- Lemma C: therefore x appears to stabilize (class never changes)
  -- But this is "false stability" — broken by any extension adding comp
  
  -- Full T1 proof would combine these to show:
  -- ¬ClosedComp → ∃x. ¬Stabilizes x (in the robust sense)
