{-# OPTIONS --without-K --safe #-}

module Distinction.ForcingT2 where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Distinction.DistSystem
open import Distinction.Equivalence using (ObservableUniverse)

private
  variable
    ℓ ℓ' ℓ'' : Level

-- =============================================================================
-- ITERATION STRUCTURE (free monoid of refinement steps)
-- =============================================================================

-- Iter is NOT "ℕ as ontology" but "syntax of finite iteration"
-- This makes explicit: induction arises from ITERATION, not from "assuming ℕ"

data Iter : Set where
  ε    : Iter           -- zero steps (identity)
  step : Iter → Iter    -- one more refinement step

-- Iter is isomorphic to ℕ, but the conceptual framing matters:
-- ℕ appears as the UNIQUE way to index finite iteration chains

-- encode at top level (before module that uses it)
encode : ℕ → Iter
encode zero    = ε
encode (suc n) = step (encode n)

-- =============================================================================
-- SEMANTICS: applying iterations to refinement operator
-- =============================================================================

module IterSemantics {ℓ ℓ' ℓ'' : Level}
                     {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                     (RO : RefOp DS) where
                     
  open AdmissibleDistSystem DS
  open RefOp RO
  
  -- Apply i iterations of Φ starting from d
  apply : D → Iter → D
  apply d ε        = d
  apply d (step i) = Φ (apply d i)
  
  -- Import trajectory for comparison
  open import Distinction.Stabilization
  open Trajectory RO
  
  -- Theorem: apply and traj coincide (using top-level encode)
  apply-traj : ∀ (d₀ : D) (n : ℕ) → apply d₀ (encode n) ≡ traj d₀ n
  apply-traj d₀ zero    = refl
  apply-traj d₀ (suc n) = cong Φ (apply-traj d₀ n)

-- =============================================================================
-- T2: REFINEMENT-INDUCTION (induction over Iter)
-- =============================================================================

-- This is the FORCING theorem: 
-- As soon as you have iterable refinement, you MUST have induction
-- to reason about stabilization/limits

-- Induction principle for Iter (completely constructive, no postulates)
iter-induction : (P : Iter → Set) →
                 P ε →
                 (∀ i → P i → P (step i)) →
                 ∀ i → P i
iter-induction P base step-case ε        = base
iter-induction P base step-case (step i) = step-case i (iter-induction P base step-case i)

-- Dependent version
iter-induction-dep : ∀ {ℓ} (P : Iter → Set ℓ) →
                     P ε →
                     (∀ i → P i → P (step i)) →
                     ∀ i → P i
iter-induction-dep P base step-case ε        = base
iter-induction-dep P base step-case (step i) = step-case i (iter-induction-dep P base step-case i)

-- =============================================================================
-- FORCING INTERPRETATION
-- =============================================================================

{-
THEOREM T2 (Refinement-Induction Forcing):

Any system that formalizes "stabilization as limit of trajectory" is FORCED
to have:
  (i)  A notion of finite iteration (Iter / ℕ)
  (ii) Proofs by iteration (induction principle)

Why this is FORCING, not axiom:
  - We don't "assume ℕ exists as foundation"
  - We show: if you want to talk about trajectories d₀, Φ(d₀), Φ²(d₀), ...
    then you MUST have indexing structure
  - The ONLY indexing structure for finite sequences is ℕ (up to iso)
  - Therefore: ℕ-like structure is FORCED by iteration
  - And: induction is FORCED as the proof principle for finite iteration

Connection to v0.1:
  - Types arise from Δ≠∅ (static)
  - Induction arises from "process of refinement" (dynamic)
  
Connection to T1:
  - T1: Closure is forced by stability demand
  - T2: Induction is forced by iteration demand
  - Together: stable ontology requires closed language + inductive reasoning
-}

-- =============================================================================
-- PROPERTIES OF ITER (demonstrating induction works)
-- =============================================================================

-- Length of iteration
length : Iter → ℕ
length ε        = zero
length (step i) = suc (length i)

-- encode and length are inverses (one direction)
length-encode : ∀ n → length (encode n) ≡ n
length-encode zero    = refl
length-encode (suc n) = cong suc (length-encode n)

-- decode (the other direction)
decode : Iter → ℕ
decode = length

-- Full isomorphism Iter ≅ ℕ
iter-nat-iso₁ : ∀ n → decode (encode n) ≡ n
iter-nat-iso₁ = length-encode

encode-decode : ∀ i → encode (decode i) ≡ i
encode-decode ε        = refl
encode-decode (step i) = cong step (encode-decode i)

-- This isomorphism is the CONTENT of T2:
-- ℕ is not "assumed", it's the UNIQUE (up to iso) structure for finite iteration

-- =============================================================================
-- T2 STATEMENT (formal)
-- =============================================================================

-- The "theorem" is simply: iter-induction exists and works
-- The FORCING is in the interpretation:

T2-statement : Set₁
T2-statement = ∀ (P : Iter → Set) →
               P ε →
               (∀ i → P i → P (step i)) →
               ∀ i → P i

T2-proof : T2-statement
T2-proof = iter-induction

-- The content is: you CANNOT avoid this structure if you want trajectories

-- =============================================================================
-- APPLICATION: Stabilization proofs require induction
-- =============================================================================

module StabilizationInduction {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                              {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                              (OU : ObservableUniverse DS ℓU ℓO)
                              (RO : RefOp DS) where
                              
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  open RefOp RO
  open IterSemantics RO
  
  -- Any property about "all steps of trajectory" requires induction
  -- Example: monotonicity along entire trajectory
  
  open import Distinction.Stabilization
  open Trajectory RO
  
  -- Prove property for all iteration steps using iter-induction
  -- (Formulated directly over apply, which equals traj by apply-traj)
  all-apply-steps : (P : D → Set) →
                    (d₀ : D) →
                    P d₀ →
                    (∀ d → P d → P (Φ d)) →
                    ∀ i → P (apply d₀ i)
  all-apply-steps P d₀ base step-case = 
    iter-induction 
      (λ i → P (apply d₀ i))
      base
      (λ i ih → step-case (apply d₀ i) ih)
  
  -- Corollary: same for traj (via transport)
  -- all-traj-steps would use subst with apply-traj
