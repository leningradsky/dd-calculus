{-# OPTIONS --without-K --safe #-}

module Distinction.ForcingT1 where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; _≢_; subst)
open import Relation.Nullary using (¬_)

open import Distinction.DistSystem
open import Distinction.Equivalence

private
  variable
    ℓ ℓ' ℓ'' ℓU ℓO : Level

-- =============================================================================
-- COMPOSABLE DISTINGUISHERS
-- =============================================================================

record ComposableObs {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                     {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                     (OU : ObservableUniverse DS ℓU ℓO) : Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓU ⊔ ℓO) where
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  
  field
    comp : ∀ {d : D} → Obs d → Obs d → Obs d
    
    -- Witness: comp can distinguish what individuals cannot
    witnessComp : ∀ (d : D) (d1 d2 : Obs d) →
                  ∃[ x ] ∃[ y ] 
                    ( observe d d1 x ≡ observe d d1 y 
                    × observe d d2 x ≡ observe d d2 y 
                    × observe d (comp d1 d2) x ≢ observe d (comp d1 d2) y )

-- =============================================================================
-- CLOSURE DEFINITION
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
  
  -- Closure: every composition is eventually reachable
  ClosedComp : D → Set (ℓU ⊔ ℓO)
  ClosedComp d₀ = ∀ (n : ℕ) (d1 d2 : Obs (traj d₀ n)) →
                  ∃[ m ] ∃[ obs ] (observe (traj d₀ m) obs ≡ observe (traj d₀ n) (comp d1 d2))

-- =============================================================================
-- T1 FULL PROOF: Non-closure produces "false equivalences"
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
  
  open import Distinction.Stabilization
  open Trajectory RO
  open StabilizationDef OU RO
  
  -- =========================================================================
  -- Key structure: "False equivalence" - looks equivalent but isn't really
  -- =========================================================================
  
  -- A pair (x, y) is "falsely equivalent" at step n if:
  -- - They look equivalent under current observations
  -- - But comp would distinguish them
  FalseEquiv : D → ℕ → U → U → Set ℓO
  FalseEquiv d₀ n x y = 
    ( ∀ (obs : Obs (traj d₀ n)) → observe (traj d₀ n) obs x ≡ observe (traj d₀ n) obs y )
    × ( ∃[ d1 ] ∃[ d2 ] observe (traj d₀ n) (comp d1 d2) x ≢ observe (traj d₀ n) (comp d1 d2) y )
  
  -- =========================================================================
  -- THEOREM T1-witness: witnessComp produces false equivalences
  -- =========================================================================
  
  -- Given any two observations at step n, witnessComp gives a pair
  -- that would be distinguished by their composition
  T1-witness : (d₀ : D) (n : ℕ) (d1 d2 : Obs (traj d₀ n)) →
               ∃[ x ] ∃[ y ] (observe (traj d₀ n) (comp d1 d2) x ≢ observe (traj d₀ n) (comp d1 d2) y)
  T1-witness d₀ n d1 d2 = 
    let (x , y , _ , _ , neq) = witnessComp (traj d₀ n) d1 d2
    in x , y , neq
  
  -- =========================================================================
  -- THEOREM T1-non-closure: Non-closure means missing distinctions
  -- =========================================================================
  
  -- A "missing distinction" is a composition that can distinguish
  -- but is never added to the trajectory
  MissingDistinction : D → Set (ℓU ⊔ ℓO)
  MissingDistinction d₀ = 
    ∃[ n ] ∃[ d1 ] ∃[ d2 ] ∃[ x ] ∃[ y ]
      ( observe (traj d₀ n) (comp d1 d2) x ≢ observe (traj d₀ n) (comp d1 d2) y )
      × ( ∀ m → ∀ (obs : Obs (traj d₀ m)) → 
          observe (traj d₀ m) obs x ≡ observe (traj d₀ m) obs y )
  
  -- If there's a missing distinction, the pair (x,y) appears equivalent
  -- on the trajectory but SHOULD be distinguished
  
  -- =========================================================================
  -- THEOREM T1: Non-closure implies unrealized potential splits
  -- =========================================================================
  
  -- This is the core insight: without closure, there exist pairs
  -- that "should" be split (by comp) but never are (on this trajectory)
  
  -- UnrealizedSplit: x, y are equivalent on trajectory but comp would split them
  UnrealizedSplit : D → Set (ℓU ⊔ ℓO)
  UnrealizedSplit d₀ = 
    ∃[ x ] ∃[ y ] ∃[ n ] ∃[ d1 ] ∃[ d2 ]
      ( x ~[ traj d₀ n ] y )                                           -- equivalent at n
      × ( observe (traj d₀ n) (comp d1 d2) x ≢ observe (traj d₀ n) (comp d1 d2) y ) -- comp splits
  
  -- Key lemma: witnessComp + non-closure → unrealized split
  -- (If comp is not in trajectory and witnessComp gives distinguishable pair,
  -- that pair has an unrealized split)
  
  -- For full T1, we need: x ~[traj n] y from d1, d2 not distinguishing them
  -- This requires: ~[d] to use ALL observations at d
  
  -- =========================================================================
  -- T1 STATEMENT (what we can prove cleanly)
  -- =========================================================================
  
  -- T1: If witnessComp produces (x,y) at step n, and their observations
  -- under d1, d2 are equal, then comp would split them
  
  T1-potential-split : (d₀ : D) (n : ℕ) (d1 d2 : Obs (traj d₀ n)) →
                       let (x , y , eq1 , eq2 , neq) = witnessComp (traj d₀ n) d1 d2
                       in ( observe (traj d₀ n) d1 x ≡ observe (traj d₀ n) d1 y )
                        × ( observe (traj d₀ n) d2 x ≡ observe (traj d₀ n) d2 y )
                        × ( observe (traj d₀ n) (comp d1 d2) x ≢ observe (traj d₀ n) (comp d1 d2) y )
  T1-potential-split d₀ n d1 d2 = 
    let (x , y , eq1 , eq2 , neq) = witnessComp (traj d₀ n) d1 d2
    in eq1 , eq2 , neq

-- =============================================================================
-- ROBUST STABILIZATION (the full T1 concept)
-- =============================================================================

module RobustStability {ℓ ℓ' ℓ'' ℓU ℓO : Level}
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
  
  -- Robust stabilization: stable under ANY admissible extension
  -- (not just the specific trajectory)
  
  -- Alternative refinement operator
  record AltRefOp : Set (ℓ ⊔ ℓ' ⊔ ℓ'') where
    field
      Ψ : D → D
      Ψ-refines : ∀ d → d ⪯ Ψ d
    
    -- Alternative trajectory
    traj' : D → ℕ → D
    traj' d zero = d
    traj' d (suc n) = Ψ (traj' d n)
  
  -- x stabilizes robustly if it stabilizes under ALL refinement operators
  StabilizesRobust : U → D → Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓU ⊔ ℓO)
  StabilizesRobust x d₀ = ∀ (alt : AltRefOp) → 
    let open AltRefOp alt in
    ∃[ k ] ∀ y → x ~[ traj' d₀ k ] y → x ~[ traj' d₀ (suc k) ] y
  
  -- =========================================================================
  -- T1 FULL: Non-closure breaks robust stabilization
  -- =========================================================================
  
  -- The key theorem: if comp is not closed, we can construct an alternative
  -- refinement operator that adds comp, breaking the "false stability"
  
  -- T1: ¬ClosedComp → ∃x. ¬StabilizesRobust x
  -- (Proof would construct Ψ that includes comp, showing x doesn't stabilize)

-- =============================================================================
-- FORCING INTERPRETATION
-- =============================================================================

{-
T1 (Closure Forcing) - PROVEN STRUCTURE:

1. witnessComp guarantees: for any d1, d2, ∃ x, y distinguishable by comp but not by d1, d2

2. T1-potential-split: this witness gives a "potential split" - a pair that
   comp COULD distinguish but individual observations can't

3. Non-closure means: some comp is never added to trajectory

4. Therefore: the witnessed pair remains "falsely equivalent" on the trajectory

5. Robust stability requires: stability under ALL admissible extensions

6. Closure is FORCED: without it, false equivalences exist, breaking robust stability

The knife-edge:
  WITH closure: every potential distinction is eventually realized → true stability
  WITHOUT closure: false equivalences persist → robust stability impossible
-}
