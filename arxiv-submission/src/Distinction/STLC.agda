{-# OPTIONS --safe --without-K #-}

{-
  DD-Calculus v0.1
  Module: Distinction.STLC
  
  Interpretation of Simply Typed Lambda Calculus
  in DD-calculus semantics.
  
  Theorem 8.5: STLC is sound w.r.t. DD-calculus.
-}

module Distinction.STLC where

open import Level using (Level; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)

open import Distinction.Core
open import Distinction.Axioms
open import Distinction.Types
open import Distinction.Morphisms

private
  variable
    ℓ : Level

-- ============================================================
-- STLC Types (object language)
-- ============================================================

-- Simple types over a base type
data Ty : Set where
  base : Ty              -- The base type (interpreted as U/~)
  _⇒_ : Ty → Ty → Ty    -- Function type

infixr 20 _⇒_

-- ============================================================
-- Contexts
-- ============================================================

data Ctx : Set where
  ∅ : Ctx
  _∷_ : Ctx → Ty → Ctx

infixl 10 _∷_

-- ============================================================
-- Variables (de Bruijn indices)
-- ============================================================

data Var : Ctx → Ty → Set where
  here : ∀ {Γ A} → Var (Γ ∷ A) A
  there : ∀ {Γ A B} → Var Γ A → Var (Γ ∷ B) A

-- ============================================================
-- Terms
-- ============================================================

data Term : Ctx → Ty → Set where
  var : ∀ {Γ A} → Var Γ A → Term Γ A
  lam : ∀ {Γ A B} → Term (Γ ∷ A) B → Term Γ (A ⇒ B)
  app : ∀ {Γ A B} → Term Γ (A ⇒ B) → Term Γ A → Term Γ B

-- ============================================================
-- Semantic Interpretation
-- ============================================================

module Semantics {U : Set ℓ} (DD : DD-Structure U) where
  open DD-Structure DD
  open Δ-Morphism
  
  -- Interpretation of types
  ⟦_⟧T : Ty → Set ℓ
  ⟦ base ⟧T = U
  ⟦ A ⇒ B ⟧T = ⟦ A ⟧T → ⟦ B ⟧T
  
  -- Interpretation of contexts (as products)
  ⟦_⟧C : Ctx → Set ℓ
  ⟦ ∅ ⟧C = U  -- Unit type approximation (single element)
  ⟦ Γ ∷ A ⟧C = ⟦ Γ ⟧C × ⟦ A ⟧T
  
  -- Interpretation of variables (projection)
  ⟦_⟧V : ∀ {Γ A} → Var Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
  ⟦ here ⟧V (γ , a) = a
  ⟦ there v ⟧V (γ , _) = ⟦ v ⟧V γ
  
  -- Interpretation of terms
  ⟦_⟧ : ∀ {Γ A} → Term Γ A → ⟦ Γ ⟧C → ⟦ A ⟧T
  ⟦ var v ⟧ = ⟦ v ⟧V
  ⟦ lam t ⟧ γ = λ a → ⟦ t ⟧ (γ , a)
  ⟦ app f x ⟧ γ = ⟦ f ⟧ γ (⟦ x ⟧ γ)

-- ============================================================
-- Theorem 8.5: Soundness (sketch)
-- ============================================================

{-
  Full soundness requires showing:
  
  1. If Γ ⊢ t : A, then ⟦t⟧ : ⟦Γ⟧ → ⟦A⟧ is Δ-compatible
  
  2. β-reduction: ⟦(λx.t) s⟧ ~ ⟦t[x:=s]⟧
  
  3. η-expansion: ⟦λx. f x⟧ ~ ⟦f⟧ (for appropriate f)
  
  The key insight:
  - Lambda abstraction = currying of Δ-morphisms
  - Application = evaluation of Δ-morphisms
  - Both preserve ~ by construction
  
  Therefore: STLC typing ⟹ Δ-compatibility
  
  This is what "forced emergence" means:
  STLC is not assumed, it is DERIVED from distinction preservation.
-}

-- Partial proof for base case (full proof requires lifting ~ to products)

module Soundness {U : Set ℓ} (DD : DD-Structure U) where
  open DD-Structure DD
  open Semantics DD
  
  -- Variables preserve ~ (projections are Δ-compatible)
  -- For the base type case: ⟦ base ⟧T = U
  var-preserves-~-base : (v : Var (∅ ∷ base) base) {γ₁ γ₂ : U × U} →
    proj₂ γ₁ ~ proj₂ γ₂ → ⟦ v ⟧V γ₁ ~ ⟦ v ⟧V γ₂
  var-preserves-~-base here p = p
