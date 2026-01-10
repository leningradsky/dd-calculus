{-# OPTIONS --without-K --safe #-}

module Distinction.ForcingT3 where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; _≢_; subst)
open import Relation.Nullary using (¬_)

open import Distinction.DistSystem
open import Distinction.Equivalence

private
  variable
    ℓ ℓ' ℓ'' ℓU ℓO : Level

-- =============================================================================
-- KNOWLEDGE AS REFINEMENT-INVARIANT CLASSIFIER
-- =============================================================================

module KnowledgeDef {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                    {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                    (OU : ObservableUniverse DS ℓU ℓO)
                    (RO : RefOp DS) where
                    
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  open RefOp RO
  
  open import Distinction.Stabilization
  open Trajectory RO
  
  -- A classifier (knowledge candidate)
  Classifier : Set ℓU
  Classifier = U → Bool
  
  -- Classifier respects equivalence at d: constant on each ~[d] class
  Respects : D → Classifier → Set (ℓU ⊔ ℓO)
  Respects d K = ∀ {x y : U} → x ~[ d ] y → K x ≡ K y
  
  -- Stable classifier: respects ALL trajectory steps
  StableK : D → Classifier → Set (ℓU ⊔ ℓO)
  StableK d₀ K = ∀ (n : ℕ) → Respects (traj d₀ n) K
  
  -- Nontrivial: classifier actually distinguishes something
  Nontrivial : Classifier → Set ℓU
  Nontrivial K = ∃[ x ] ∃[ y ] (K x ≢ K y)
  
  -- Constant: classifier is trivial
  Constant : Classifier → Set ℓU
  Constant K = ∀ (x y : U) → K x ≡ K y

-- =============================================================================
-- UNIVERSAL BASE: the key assumption for T3
-- =============================================================================

module UniversalBase {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                     {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                     (OU : ObservableUniverse DS ℓU ℓO) where
                     
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  
  -- A configuration d is "universal" if all states are equivalent under it
  -- This represents "no distinctions yet made"
  Universal : D → Set (ℓU ⊔ ℓO)
  Universal d = ∀ (x y : U) → x ~[ d ] y

-- =============================================================================
-- DRIFT: PERPETUAL SPLITTING (anti-stabilization)
-- =============================================================================

module DriftDef {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                (OU : ObservableUniverse DS ℓU ℓO)
                (RO : RefOp DS) where
                
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  open RefOp RO
  
  -- Witness that class [x] splits at step d → Φ d
  Splits : D → U → Set (ℓU ⊔ ℓO)
  Splits d x = ∃[ y ] ( (x ~[ d ] y) × ¬ (x ~[ Φ d ] y) )
  
  -- Global drift: EVERY class splits at EVERY step
  Drift : Set (ℓ ⊔ ℓU ⊔ ℓO)
  Drift = ∀ (d : D) (x : U) → Splits d x

-- =============================================================================
-- T3: COLLAPSE-3 — FULL PROOF
-- =============================================================================

module T3Proof {ℓ ℓ' ℓ'' ℓU ℓO : Level}
               {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
               (OU : ObservableUniverse DS ℓU ℓO)
               (RO : RefOp DS) where
               
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  open RefOp RO
  open KnowledgeDef OU RO
  open UniversalBase OU
  open DriftDef OU RO
  
  open import Distinction.Stabilization
  open Trajectory RO
  
  -- =========================================================================
  -- THEOREM T3 (Collapse-3): Universal base + Stable ⟹ Constant
  -- =========================================================================
  
  -- If the trajectory starts from a universal configuration (all equivalent),
  -- then any stable classifier must be constant.
  
  -- This is the "epistemic collapse": without initial distinctions that
  -- persist stably, no nontrivial knowledge is possible.
  
  T3-constancy : (d₀ : D) →
                 Universal d₀ →          -- all equivalent at base
                 (K : Classifier) →
                 StableK d₀ K →           -- K respects all trajectory steps
                 Constant K               -- K must be constant
  T3-constancy d₀ univ K stable x y = 
    -- StableK gives Respects (traj d₀ 0) K
    -- traj d₀ 0 = d₀
    -- Universal d₀ gives x ~[d₀] y
    -- Respects d₀ K gives K x ≡ K y
    stable zero (univ x y)
  
  -- =========================================================================
  -- COROLLARY: No nontrivial stable classifier under universal base
  -- =========================================================================
  
  T3-no-nontrivial : (d₀ : D) →
                     Universal d₀ →
                     (K : Classifier) →
                     StableK d₀ K →
                     ¬ (Nontrivial K)
  T3-no-nontrivial d₀ univ K stable (x , y , neq) = 
    neq (T3-constancy d₀ univ K stable x y)
  
  -- =========================================================================
  -- THE ROLE OF DRIFT
  -- =========================================================================
  
  {-
  Drift ensures that stabilization NEVER happens:
  - At every step, every class splits
  - So no class ever reaches a fixed point
  
  Combined with Universal base:
  - We start with "everything equivalent" (no knowledge)
  - Drift says classes split but NEVER stabilize
  - Any classifier that respects ALL steps must respect the base
  - Therefore: constant
  
  The knife-edge:
  - WITHOUT Drift: classes might stabilize → stable nontrivial K possible
  - WITH Drift: perpetual splitting → but stable K must respect base → constant
  
  Drift is the "anti-stabilization" guarantee.
  Universal is the "epistemic starting point" (tabula rasa).
  Together they force: no nontrivial stable knowledge.
  -}
  
  -- =========================================================================
  -- STRONG T3: Drift implies Universal trajectories can't produce knowledge
  -- =========================================================================
  
  -- Under Drift, if you start universal, you never gain stable distinctions
  -- because anything you distinguish will split again
  
  -- This is formalized as: the only stable classifiers are constant
  
  T3-drift-collapse : (d₀ : D) →
                      Universal d₀ →
                      Drift →              -- perpetual splitting
                      (K : Classifier) →
                      StableK d₀ K →
                      Constant K
  T3-drift-collapse d₀ univ drift K stable = 
    -- The proof is the same! Drift doesn't add to the conclusion,
    -- it adds to the INTERPRETATION: why Universal persists
    -- (because classes never stabilize into nontrivial partitions)
    T3-constancy d₀ univ K stable

-- =============================================================================
-- ALTERNATIVE: T3 via Connectivity (without Universal assumption)
-- =============================================================================

module T3Connectivity {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                      {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                      (OU : ObservableUniverse DS ℓU ℓO)
                      (RO : RefOp DS) where
                      
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  open RefOp RO
  open KnowledgeDef OU RO
  open DriftDef OU RO
  
  open import Distinction.Stabilization
  open Trajectory RO
  
  -- Alternative assumption: any two states are connected by a ~-chain
  -- across trajectory steps
  
  -- Path of equivalences across different trajectory steps
  data Connected (d₀ : D) : U → U → Set (ℓU ⊔ ℓO) where
    conn-refl : ∀ {x} → Connected d₀ x x
    conn-step : ∀ {x y z} (n : ℕ) → 
                x ~[ traj d₀ n ] y → 
                Connected d₀ y z → 
                Connected d₀ x z
  
  -- If everything is connected, stable K is constant
  FullyConnected : D → Set (ℓU ⊔ ℓO)
  FullyConnected d₀ = ∀ (x y : U) → Connected d₀ x y
  
  -- Lemma: stable K respects connectivity paths
  stable-respects-path : (d₀ : D) (K : Classifier) →
                         StableK d₀ K →
                         ∀ {x y} → Connected d₀ x y → K x ≡ K y
  stable-respects-path d₀ K stable conn-refl = refl
  stable-respects-path d₀ K stable (conn-step n eq rest) = 
    trans (stable n eq) (stable-respects-path d₀ K stable rest)
  
  -- T3 via connectivity
  T3-connected : (d₀ : D) →
                 FullyConnected d₀ →
                 (K : Classifier) →
                 StableK d₀ K →
                 Constant K
  T3-connected d₀ conn K stable x y = 
    stable-respects-path d₀ K stable (conn x y)

-- =============================================================================
-- FORCING INTERPRETATION
-- =============================================================================

{-
T3 (Collapse-3) is now FULLY PROVEN in two forms:

FORM 1: Universal Base
  Universal d₀ + StableK d₀ K → Constant K
  
  Interpretation: If refinement starts from "no distinctions" (tabula rasa),
  any classifier that remains stable through all refinements must be constant.
  You can't build knowledge from nothing without at some point having
  distinctions that STABILIZE.

FORM 2: Connectivity
  FullyConnected d₀ + StableK d₀ K → Constant K
  
  Interpretation: If any two states can be connected by a path of
  equivalences across trajectory steps, stable classifiers are constant.

THE ROLE OF DRIFT:
  Drift ensures Universal persists (classes never stabilize into
  nontrivial partitions). It's the "why" behind Universal staying universal.

THE KNIFE-EDGE (complete picture):
  T1: Stability → Closure (can't have stable objects without closed language)
  T2: Iteration → Induction (can't have refinement without ℕ-structure)
  T3: Universal + Stable → Constant (can't have knowledge without stable distinctions)

  EITHER: Closed language allows stable distinctions → nontrivial knowledge
  OR:     Universal stays universal under drift → epistemic collapse
-}
