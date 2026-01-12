{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.CausalStructure -- Causality from Time Ordering
-- ============================================================================
--
-- THEOREM: Causality is induced by the time ordering.
--
-- Key concepts:
-- - Causal relation: a ≺ b iff a < b (a can influence b)
-- - Spacelike separation: neither a ≺ b nor b ≺ a
-- - Causal structure = time order + locality
--
-- ============================================================================

module DD.CausalStructure where

open import Core.Logic
open import Core.Nat
open import DD.TimeOrdering as T

-- ============================================================================
-- SECTION 1: CAUSAL RELATION
-- ============================================================================

-- The causal relation is directly inherited from time ordering.
-- Event a can causally influence event b iff a < b.

infix 4 _≺_

_≺_ : T.Event → T.Event → Set
a ≺ b = a < b

-- ============================================================================
-- SECTION 2: CAUSAL PROPERTIES
-- ============================================================================

-- Causality inherits all properties from time ordering.

-- No self-causation
≺-irrefl : ∀ {e} → ¬ (e ≺ e)
≺-irrefl = T.<-irrefl

-- Causal transitivity
≺-trans : ∀ {a b c} → a ≺ b → b ≺ c → a ≺ c
≺-trans = T.<-trans

-- No causal loops (if a causes b, b doesn't cause a)
≺-asym : ∀ {a b} → a ≺ b → ¬ (b ≺ a)
≺-asym = T.<-asym

-- ============================================================================
-- SECTION 3: SPACELIKE SEPARATION
-- ============================================================================

-- Two events are spacelike separated if neither can causally influence the other.
-- This is the negation of causal connection in both directions.

Spacelike : T.Event → T.Event → Set
Spacelike a b = (¬ (a ≺ b)) × (¬ (b ≺ a))

-- For discrete time (ℕ), only simultaneous events are spacelike.
-- a and b are spacelike iff a ≡ b (in discrete model).

-- This is actually a limitation of the discrete model.
-- In continuous spacetime, spacelike events can be distinct.
-- Here we just establish the STRUCTURE.

-- ============================================================================
-- SECTION 4: CAUSAL FUTURE AND PAST
-- ============================================================================

-- Causal future of event e: all events that e can influence
CausalFuture : T.Event → T.Event → Set
CausalFuture e x = e ≺ x

-- Causal past of event e: all events that can influence e
CausalPast : T.Event → T.Event → Set
CausalPast e x = x ≺ e

-- ============================================================================
-- SECTION 5: CAUSALITY RECORD
-- ============================================================================

record Causality : Set where
  field
    -- Underlying time order
    arrow : T.ArrowOfTime
    
    -- Causal relation is transitive
    causal-trans : ∀ {a b c} → a ≺ b → b ≺ c → a ≺ c
    
    -- No causal loops
    no-loops : ∀ {a b} → a ≺ b → ¬ (b ≺ a)

causality : Causality
causality = record
  { arrow = T.arrow-of-time
  ; causal-trans = ≺-trans
  ; no-loops = ≺-asym
  }

-- ============================================================================
-- SECTION 6: CAUSAL STRUCTURE THEOREM
-- ============================================================================

-- The full causal structure combines:
-- 1. Time ordering (ArrowOfTime)
-- 2. Causality properties (no loops, transitivity)
-- 3. Separation concepts (spacelike)

record CausalStructure : Set where
  field
    causal : Causality
    
    -- Spacelike: example witness (two equal events are trivially spacelike)
    spacelike-example : ∀ e → Spacelike e e
    
    -- Future is non-empty for any event (there's always a next event)
    future-nonempty : ∀ e → CausalFuture e (suc e)

-- Helper: reflexive spacelike (e is spacelike to itself in discrete model)
self-spacelike : ∀ e → Spacelike e e
self-spacelike e = (λ p → ≺-irrefl p) , (λ p → ≺-irrefl p)

-- Helper: next event is in causal future
next-in-future : ∀ e → CausalFuture e (suc e)
next-in-future e = s≤s (≤-refl e)
  where
    ≤-refl : ∀ n → n ≤ n
    ≤-refl zero = z≤n
    ≤-refl (suc n) = s≤s (≤-refl n)

causal-structure : CausalStructure
causal-structure = record
  { causal = causality
  ; spacelike-example = self-spacelike
  ; future-nonempty = next-in-future
  }

-- ============================================================================
-- SECTION 7: INTERPRETATION
-- ============================================================================

{-
DD INTERPRETATION:

Causality is NOT a separate axiom — it's DERIVED from time ordering.

The structure is:
  Time Order → Causal Relation → Light Cone Structure

In discrete DD model (Event = ℕ):
- Causal future of n = {n+1, n+2, n+3, ...}
- Causal past of n = {0, 1, ..., n-1}
- Spacelike to n = {} (only n itself is "simultaneous")

The discrete model captures the TOPOLOGICAL structure of causality:
- Transitivity ✓
- No cycles ✓
- Past/future distinction ✓

The METRIC structure (light cones, Lorentz invariance) requires
additional input (spatial coordinates + speed limit).

DD provides: CAUSAL STRUCTURE
Dynamics adds: METRIC STRUCTURE
-}
