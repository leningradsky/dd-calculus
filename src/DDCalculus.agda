{-# OPTIONS --safe --without-K #-}

{-
  DD-Calculus v0.1
  
  Distinction-Based Foundations of Simply Typed Lambda Calculus
  
  Main module: imports all components
  
  Structure:
    Core      → Primitive notions (U, D, #, ~)
    Axioms    → A1 (equivalence), A2 (conjunction)
    Types     → Types as U/~ (setoid)
    Morphisms → Δ-morphisms (~ preserving functions)
    Category  → DD₀ category laws
    Collapse  → Theorem 9.1 (𝒟=∅ ⟹ trivial)
    STLC      → STLC syntax and partial interpretation
    Soundness → Theorem 8.5 (FULL soundness proof)
  
  Key results:
    - Types are DERIVED from indistinguishability
    - Equality is DERIVED from ~ (not primitive)
    - Functions are FORCED by Δ-compatibility
    - STLC is SOUND w.r.t. DD-semantics (PROVEN)
    - Collapse shows Δ≠∅ is NECESSARY
-}

module DDCalculus where

-- Core definitions
open import Distinction.Core public

-- Structural axioms
open import Distinction.Axioms public

-- Types as equivalence classes
open import Distinction.Types public

-- Δ-morphisms
open import Distinction.Morphisms public

-- Category DD₀
open import Distinction.Category public

-- Collapse theorem
open import Distinction.Collapse public

-- STLC interpretation
open import Distinction.STLC public

-- Full soundness proof (not re-exported to avoid name conflicts)
import Distinction.Soundness
