{-# OPTIONS --without-K --safe #-}

module Distinction.ForcingT3 where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; _≢_)
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
  -- There exists y that was equivalent but becomes distinguishable
  Splits : D → U → Set (ℓU ⊔ ℓO)
  Splits d x = ∃[ y ] ( (x ~[ d ] y) × ¬ (x ~[ Φ d ] y) )
  
  -- Global drift: EVERY class splits at EVERY step
  -- This is the "anti-stabilization" condition
  Drift : Set (ℓ ⊔ ℓU ⊔ ℓO)
  Drift = ∀ (d : D) (x : U) → Splits d x

-- =============================================================================
-- T3: COLLAPSE-3 (no stable nontrivial knowledge under drift)
-- =============================================================================

module T3Statement {ℓ ℓ' ℓ'' ℓU ℓO : Level}
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
  
  -- T3 (Collapse-3): Drift implies no nontrivial stable knowledge
  -- "If refinement always splits classes, then any stable classifier is trivial"
  
  T3-statement : Set (ℓ ⊔ ℓU ⊔ ℓO)
  T3-statement = Drift → ∀ (d₀ : D) (K : Classifier) → StableK d₀ K → ¬ (Nontrivial K)

{-
=============================================================================
THEOREM T3 (Collapse-3): PROOF SKETCH
=============================================================================

Claim: Drift → ∀ d₀ K. StableK d₀ K → ¬ Nontrivial K

Proof sketch:

1. Assume Drift and StableK d₀ K
2. Suppose for contradiction: Nontrivial K, i.e., ∃ x y. K x ≢ K y
3. Take such x, y with K x ≢ K y

4. Case A: x ~[d₀] y
   - StableK d₀ K gives Respects (traj d₀ 0) K = Respects d₀ K
   - So x ~[d₀] y → K x ≡ K y
   - Contradiction with K x ≢ K y ✓

5. Case B: ¬(x ~[d₀] y)
   - Drift says: for any z, there exists w such that z ~[d] w but ¬(z ~[Φ d] w)
   - This means classes perpetually split
   - We need to show this eventually connects x and y (via chain of splits)
   - OR: we construct a direct contradiction
   
   Alternative approach for Case B:
   - If K is Respects for ALL trajectory steps
   - And classes always split
   - Then K cannot "use" any distinction (each distinction existed only for finite steps)
   - So K must be constant
   
Key insight:
  StableK means K "predates" every distinction in the trajectory.
  Drift means new distinctions always appear.
  Therefore K cannot rely on ANY distinction → K is constant.

The full proof requires either:
(a) Showing Drift makes U "connected" via ~-chains across time
(b) Or showing that StableK + Drift → K factors through "empty observation"

For the skeleton, we state the theorem; full proof needs auxiliary lemmas.
-}

-- =============================================================================
-- T3 PROOF STRUCTURE
-- =============================================================================

module T3Proof {ℓ ℓ' ℓ'' ℓU ℓO : Level}
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
  
  -- Lemma: If x ~[d] y and K respects d, then K x ≡ K y
  -- (this is immediate from Respects definition)
  respects-apply : ∀ (d : D) (K : Classifier) →
                   Respects d K →
                   ∀ {x y : U} → x ~[ d ] y → K x ≡ K y
  respects-apply d K resp eq = resp eq
  
  -- Lemma: StableK gives Respects at any trajectory step
  stableK-at-step : ∀ (d₀ : D) (K : Classifier) →
                    StableK d₀ K →
                    ∀ (n : ℕ) → Respects (traj d₀ n) K
  stableK-at-step d₀ K stable n = stable n
  
  -- Key observation: Under Drift, for each step n, there's a split witness
  drift-at-step : Drift →
                  ∀ (d₀ : D) (n : ℕ) (x : U) →
                  Splits (traj d₀ n) x
  drift-at-step drift d₀ n x = drift (traj d₀ n) x
  
  -- The core argument (stated, not fully proven):
  -- If K is stable and drift holds, any "distinction" K uses
  -- must have been present at step 0, but drift ensures
  -- that distinction gets "washed away" at some step
  
  -- For now: T3 as axiom (to be proven with more structure)
  -- The statement IS the content; proof requires ~-connectivity lemmas

-- =============================================================================
-- FORCING INTERPRETATION
-- =============================================================================

{-
T3 completes the v0.3 triple:

T1 (Closure Forcing):
  Stability → Closed language of distinguishers
  "You can't have stable objects without compositional observations"

T2 (Induction Forcing):  
  Iteration → ℕ-structure → Induction principle
  "You can't reason about trajectories without induction"

T3 (Collapse-3):
  ¬Stability → ¬Knowledge
  "Without stable objects, no invariant classification is possible"

Together they say:
  EITHER your observation language is closed (T1) 
         AND admits inductive reasoning (T2)
         AND produces stable objects
  OR     you have perpetual drift (T3)
         AND no nontrivial knowledge
         AND science is impossible

This is the "knife-edge" of DD:
  Stable ontology exists IFF observation language has right structure
  Otherwise: epistemic collapse
-}
