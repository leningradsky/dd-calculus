{-# OPTIONS --safe --without-K #-}

-- =============================================================================
-- Tier 1, Line 3: Consistency Implies Acyclicity
-- =============================================================================
--
-- CLAIM: If distinctions can be consistently evaluated (no paradox),
-- then the dependency graph must be acyclic.
--
-- INTUITION: If d₁ depends on d₂ and d₂ depends on d₁, then neither
-- can be evaluated first → contradiction with consistent evaluation.
--
-- This is the formal backbone of "order from consistency".
-- =============================================================================

module DD.ConsistencyImpliesAcyclic where

-- =============================================================================
-- Basic Types
-- =============================================================================

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

¬_ : Set → Set
¬ A = A → ⊥

-- Strict ordering on ℕ
_<_ : ℕ → ℕ → Set
zero < zero = ⊥
zero < suc n = ⊤
suc m < zero = ⊥
suc m < suc n = m < n

-- =============================================================================
-- < Lemmas
-- =============================================================================

<-irrefl : (n : ℕ) → ¬ (n < n)
<-irrefl zero ()
<-irrefl (suc n) = <-irrefl n

<-trans : (a b c : ℕ) → a < b → b < c → a < c
<-trans zero (suc _) (suc _) _ _ = tt
<-trans (suc a) (suc b) (suc c) a<b b<c = <-trans a b c a<b b<c

-- =============================================================================
-- Parametric Module for Any Distinction Type
-- =============================================================================

module AcyclicityTheorem (Dist : Set) (Dep : Dist → Dist → Set) where

  -- Paths in Dependency Graph
  data Path : Dist → Dist → Set where
    step : {a b : Dist} → Dep a b → Path a b
    _∙_ : {a b c : Dist} → Path a b → Path b c → Path a c

  -- A cycle is a path from d to itself
  Cycle : Dist → Set
  Cycle d = Path d d

  -- The graph is acyclic if no distinction has a cycle
  Acyclic : Set
  Acyclic = (d : Dist) → ¬ (Cycle d)

  -- Consistent evaluation: rank function respecting dependencies
  record ConsistentEval : Set where
    field
      rank : Dist → ℕ
      rank-respects-dep : {a b : Dist} → Dep a b → rank b < rank a

  -- Path implies rank inequality
  path-implies-rank-lt : (eval : ConsistentEval) → 
                         {a b : Dist} → Path a b → 
                         ConsistentEval.rank eval b < ConsistentEval.rank eval a
  path-implies-rank-lt eval (step dep) = ConsistentEval.rank-respects-dep eval dep
  path-implies-rank-lt eval {a} {c} (_∙_ {a} {b} {c} p₁ p₂) = 
    <-trans (ConsistentEval.rank eval c) 
            (ConsistentEval.rank eval b) 
            (ConsistentEval.rank eval a)
            (path-implies-rank-lt eval p₂) 
            (path-implies-rank-lt eval p₁)

  -- MAIN THEOREM
  consistency-implies-acyclic : ConsistentEval → Acyclic
  consistency-implies-acyclic eval d cycle = 
    <-irrefl (ConsistentEval.rank eval d) (path-implies-rank-lt eval cycle)

  -- COROLLARY
  cycle-breaks-consistency : {d : Dist} → Cycle d → ¬ ConsistentEval
  cycle-breaks-consistency cycle eval = consistency-implies-acyclic eval _ cycle

-- =============================================================================
-- SUMMARY
-- =============================================================================
--
-- For any type Dist and relation Dep, we proved:
--
--   ConsistentEval → Acyclic
--   Cycle d → ¬ ConsistentEval
--
-- This is Line 3 of the backbone:
--   "Consistency of distinctions requires acyclic dependency"
--
-- No physics. No geometry. Pure logic of evaluation order.
--
-- KILL CRITERIA:
-- - Show consistent evaluation scheme that tolerates cycles
-- - Show meaningful notion of "distinction" without dependency order
-- =============================================================================
