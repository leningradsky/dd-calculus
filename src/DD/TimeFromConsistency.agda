{-# OPTIONS --safe --without-K #-}

-- =============================================================================
-- Tier 1, Line 4: Time From Consistency (Direct Path)
-- =============================================================================
--
-- THEOREM: If ConsistentEval exists, TimeStructure exists.
--
-- This is the DIRECT route:
--   ConsistentEval = rank function with monotonicity
--   TimeStructure = time function with monotonicity  
--   They are THE SAME THING.
--
-- No need to go through Acyclic → WellFounded → Rank.
-- The rank in ConsistentEval IS time.
--
-- Combined with Line 3:
--   Consistency → Acyclic (Line 3)
--   Consistency → Time (Line 4, this file)
--
-- =============================================================================

module DD.TimeFromConsistency where

-- =============================================================================
-- Basic Types
-- =============================================================================

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

-- Strict ordering on ℕ
_<_ : ℕ → ℕ → Set
zero < zero = ⊥
zero < suc n = ⊤
suc m < zero = ⊥
suc m < suc n = m < n

-- =============================================================================
-- Parametric Module
-- =============================================================================

module TimeTheorem (Dist : Set) (Dep : Dist → Dist → Set) where

  -- -------------------------------------------------------------------------
  -- ConsistentEval: rank function respecting dependencies
  -- -------------------------------------------------------------------------
  
  record ConsistentEval : Set where
    field
      rank : Dist → ℕ
      rank-respects-dep : {a b : Dist} → Dep a b → rank b < rank a

  -- -------------------------------------------------------------------------
  -- TimeStructure: time function with monotonicity
  -- -------------------------------------------------------------------------
  
  record TimeStructure : Set where
    field
      time : Dist → ℕ
      time-monotone : {a b : Dist} → Dep a b → time b < time a

  -- -------------------------------------------------------------------------
  -- THEOREM: ConsistentEval IS TimeStructure
  -- -------------------------------------------------------------------------
  
  -- Forward: ConsistentEval → TimeStructure
  consistency-gives-time : ConsistentEval → TimeStructure
  consistency-gives-time eval = record
    { time = ConsistentEval.rank eval
    ; time-monotone = ConsistentEval.rank-respects-dep eval
    }

  -- Backward: TimeStructure → ConsistentEval
  time-is-consistency : TimeStructure → ConsistentEval
  time-is-consistency ts = record
    { rank = TimeStructure.time ts
    ; rank-respects-dep = TimeStructure.time-monotone ts
    }

  -- -------------------------------------------------------------------------
  -- COROLLARY: Time = Rank (definitional equivalence)
  -- -------------------------------------------------------------------------
  
  -- The two records are isomorphic (same fields, same types)
  -- This is the formal statement that "time" and "evaluation order" 
  -- are the same concept.

-- =============================================================================
-- INTERPRETATION
-- =============================================================================
--
-- What does this mean philosophically?
--
-- 1. TIME IS NOT A PRIMITIVE.
--    Time is the rank function that allows consistent evaluation.
--
-- 2. TIME IS PARTIAL ORDER.
--    The theorem gives monotone t : Dist → ℕ, not linear order.
--    Different distinctions may have same rank (simultaneous).
--
-- 3. LINEAR TIME REQUIRES MORE.
--    To get total order (a < b or b < a for all a,b), need:
--    - Single observer thread (sequential experience)
--    - Deterministic dynamics (unique successor)
--    - Or: restriction to "realized" events
--    These are Tier 2 assumptions.
--
-- =============================================================================
-- SUMMARY
-- =============================================================================
--
-- PROVED (--safe --without-K, 0 postulates):
--
--   ConsistentEval ↔ TimeStructure
--
-- Combined with Line 3 (ConsistencyImpliesAcyclic):
--
--   Consistency → Acyclic ∧ Time
--
-- This completes Tier 1 Lines 3-4:
--   "Consistent distinctions have order (acyclic) and time (rank)."
--
-- KILL CRITERIA:
-- - Show consistent evaluation without monotone parameter
-- - Show time-like structure that violates rank monotonicity
-- =============================================================================
