{-# OPTIONS --without-K --safe #-}

module Distinction.Equivalence where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)

open import Distinction.DistSystem

private
  variable
    ℓ ℓ' ℓ'' ℓU ℓO : Level

-- =============================================================================
-- UNIVERSE AND OBSERVABLES
-- =============================================================================

-- A universe with observable structure relative to a distinguisher system
record ObservableUniverse {ℓ ℓ' ℓ'' : Level} (DS : AdmissibleDistSystem ℓ ℓ' ℓ'') 
                          (ℓU ℓO : Level) : Set (Level.suc (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓU ⊔ ℓO)) where
  open AdmissibleDistSystem DS
  
  field
    -- Universe of states
    U : Set ℓU
    
    -- Observable values
    O : Set ℓO
    
    -- For each config d, a family of observations
    Obs : D → Set ℓO
    
    -- Each observation is a function U → O
    observe : ∀ (d : D) → Obs d → U → O

  -- Two states are equivalent under d if all observations agree
  _~[_]_ : U → D → U → Set ℓO
  x ~[ d ] y = ∀ (obs : Obs d) → observe d obs x ≡ observe d obs y
  
  -- Equivalence is reflexive
  ~-refl : ∀ (d : D) (x : U) → x ~[ d ] x
  ~-refl d x obs = refl
  
  -- Equivalence is symmetric
  ~-sym : ∀ (d : D) {x y : U} → x ~[ d ] y → y ~[ d ] x
  ~-sym d p obs = sym (p obs)
  
  -- Equivalence is transitive
  ~-trans : ∀ (d : D) {x y z : U} → x ~[ d ] y → y ~[ d ] z → x ~[ d ] z
  ~-trans d p q obs = trans (p obs) (q obs)

-- =============================================================================
-- MONOTONICITY (key theorem)
-- =============================================================================

-- For monotonicity, we need refinement to mean "more observations"
-- This requires structure on how Obs grows with refinement

record MonotonicObs {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                    {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                    (OU : ObservableUniverse DS ℓU ℓO) : Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓU ⊔ ℓO) where
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  
  field
    -- If d ⪯ d', then every observation in d is also in d'
    -- (d' has at least as many observations)
    lift-obs : ∀ {d d' : D} → d ⪯ d' → Obs d → Obs d'
    
    -- Lifted observation agrees with original
    lift-coherent : ∀ {d d' : D} (r : d ⪯ d') (obs : Obs d) (x : U) →
                    observe d obs x ≡ observe d' (lift-obs r obs) x

  -- Monotonicity theorem: refinement shrinks equivalence classes
  -- If x ~[d'] y and d ⪯ d', then x ~[d] y
  -- (finer equivalence implies coarser equivalence)
  mono : ∀ {d d' : D} → d ⪯ d' → ∀ (x y : U) → x ~[ d' ] y → x ~[ d ] y
  mono {d} {d'} r x y eq obs = 
    trans (lift-coherent r obs x) 
          (trans (eq (lift-obs r obs)) 
                 (sym (lift-coherent r obs y)))
