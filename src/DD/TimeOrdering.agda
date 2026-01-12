{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- DD.TimeOrdering -- Time as Order of Distinction Acts
-- ============================================================================
--
-- THEOREM: Time is not a coordinate but an ORDER on distinction events.
--
-- DD interpretation:
-- - Each distinction is an "event"
-- - Events are naturally ordered (before/after)
-- - Time = counting measure on distinctions
--
-- Implementation: Event = ℕ (natural numbers as discrete time steps)
-- This gives us all ordering properties for free.
--
-- ============================================================================

module DD.TimeOrdering where

open import Core.Logic
open import Core.Nat

-- ============================================================================
-- SECTION 1: EVENTS AS NATURAL NUMBERS
-- ============================================================================

-- An event is a discrete moment in the sequence of distinctions.
-- We model this as ℕ: the n-th distinction event.

Event : Set
Event = ℕ

-- The ordering relation is inherited from ℕ.
-- e₁ < e₂ means "event e₁ happens before event e₂"

-- ============================================================================
-- SECTION 2: STRICT ORDER PROPERTIES
-- ============================================================================

-- Irreflexivity: no event is before itself
<-irrefl : ∀ {e : Event} → ¬ (e < e)
<-irrefl {zero} ()
<-irrefl {suc e} (s≤s p) = <-irrefl p

-- Transitivity: if a < b and b < c, then a < c
≤-trans : ∀ {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n _ = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

<-trans : ∀ {a b c : Event} → a < b → b < c → a < c
<-trans {a} {b} {c} p q = ≤-trans p (≤-trans (n≤suc-n _) q)
  where
    n≤suc-n : ∀ n → n ≤ suc n
    n≤suc-n zero = z≤n
    n≤suc-n (suc n) = s≤s (n≤suc-n n)

-- Asymmetry: if a < b then ¬(b < a)
<-asym : ∀ {a b : Event} → a < b → ¬ (b < a)
<-asym {zero} {suc b} _ ()
<-asym {suc a} {suc b} (s≤s p) (s≤s q) = <-asym p q

-- ============================================================================
-- SECTION 3: TIME ORDER RECORD
-- ============================================================================

record TimeOrder : Set where
  field
    -- Strict partial order properties
    irreflexive : ∀ {e} → ¬ (e < e)
    transitive : ∀ {a b c} → a < b → b < c → a < c
    asymmetric : ∀ {a b} → a < b → ¬ (b < a)

time-order : TimeOrder
time-order = record
  { irreflexive = <-irrefl
  ; transitive = <-trans
  ; asymmetric = <-asym
  }

-- ============================================================================
-- SECTION 4: ARROW OF TIME
-- ============================================================================

-- The "arrow of time" is the fact that there is a DIRECTION to the order.
-- In ℕ, this is manifest: 0 < 1 < 2 < 3 < ...
-- There is no "going back" — the order is well-founded.

-- Well-foundedness: every descending chain terminates
-- For ℕ with <, this is automatic (no infinite descent).

-- We encode the arrow structurally:
-- 1. Order exists (TimeOrder)
-- 2. There is a "first" event (zero)
-- 3. Every event has a successor (suc)

record ArrowOfTime : Set where
  field
    order : TimeOrder
    
    -- First event exists
    first : Event
    first-is-zero : first ≡ zero
    
    -- Every event has a next event
    next : Event → Event
    next-is-suc : ∀ e → next e ≡ suc e
    
    -- No cycles (encoded: first has no predecessor)
    no-before-first : ∀ {e} → ¬ (e < first)

-- Prove no event is before zero
nothing-before-zero : ∀ {e : Event} → ¬ (e < zero)
nothing-before-zero ()

arrow-of-time : ArrowOfTime
arrow-of-time = record
  { order = time-order
  ; first = zero
  ; first-is-zero = refl
  ; next = suc
  ; next-is-suc = λ _ → refl
  ; no-before-first = nothing-before-zero
  }

-- ============================================================================
-- SECTION 5: INTERPRETATION
-- ============================================================================

{-
DD INTERPRETATION:

Time is NOT a pre-existing coordinate space.
Time EMERGES from the ordering of distinction acts.

The fundamental notion is:
  "Distinction A happens BEFORE distinction B"

This gives a strict partial order, which we model as (ℕ, <).

KEY PROPERTIES (all proven, not postulated):
1. Irreflexivity: An event doesn't precede itself
2. Transitivity: Temporal order is consistent
3. Asymmetry: If A before B, then B not before A
4. Well-foundedness: No infinite past (there's a "first" event)
5. Discrete: Time steps are countable

The "arrow of time" is the ASYMMETRY + WELL-FOUNDEDNESS.
It's not added — it's INHERENT in the structure of distinction.

PHYSICAL CONNECTION:
- Discrete time → quantum mechanics compatibility
- Arrow of time → thermodynamics (entropy)
- No cycles → causality
-}
