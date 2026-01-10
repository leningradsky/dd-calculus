{-# OPTIONS --safe --without-K #-}

{-
  DD-Calculus v0.1
  Module: Distinction.Category
  
  Theorem 7.3: Types and Δ-morphisms form a category DD₀
-}

module Distinction.Category where

open import Level using (Level; _⊔_)
open import Function using (_∘_; id)

open import Distinction.Core
open import Distinction.Axioms
open import Distinction.Types
import Distinction.Morphisms as Mor

private
  variable
    ℓ : Level

-- ============================================================
-- Theorem 7.3: Category DD₀
-- ============================================================

module DD₀ {U : Set ℓ} (DD : DD-Structure U) where
  open DD-Structure DD
  
  -- Morphism types and operations
  Δ-Mor : Set ℓ
  Δ-Mor = Mor.Δ-Morphism DD
  
  idΔ : Δ-Mor
  idΔ = Mor.idΔ DD
  
  _∘Δ_ : Δ-Mor → Δ-Mor → Δ-Mor
  f ∘Δ g = Mor._∘Δ_ DD f g
  
  _≈Δ_ : Δ-Mor → Δ-Mor → Set ℓ
  f ≈Δ g = Mor._≈Δ_ DD f g
  
  -- Objects: U/~ (represented as setoid, single object for now)
  -- Morphisms: Δ-Morphisms
  
  -- Identity law (left)
  id-left : ∀ (f : Δ-Mor) → (idΔ ∘Δ f) ≈Δ f
  id-left f x = ~-refl
  
  -- Identity law (right)
  id-right : ∀ (f : Δ-Mor) → (f ∘Δ idΔ) ≈Δ f
  id-right f x = ~-refl
  
  -- Associativity
  ∘-assoc : ∀ (f g h : Δ-Mor) → 
    ((f ∘Δ g) ∘Δ h) ≈Δ (f ∘Δ (g ∘Δ h))
  ∘-assoc f g h x = ~-refl

-- ============================================================
-- Category laws are satisfied
-- ============================================================

-- This establishes that DD₀ is a well-defined category.
-- 
-- Objects: The single type U/~
-- Morphisms: Δ-Morphisms (U → U preserving ~)
-- Identity: idΔ
-- Composition: ∘Δ
-- Laws: id-left, id-right, ∘-assoc (all proven above)
--
-- This is a monoid viewed as a one-object category,
-- but the structure generalizes to multiple types in v0.2.
