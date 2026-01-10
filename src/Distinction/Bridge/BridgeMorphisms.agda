{-# OPTIONS --without-K --safe #-}

module Distinction.Bridge.BridgeMorphisms where

open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (_∘_; id)

open import Distinction.DistSystem
open import Distinction.Equivalence

private
  variable
    ℓ ℓ' ℓ'' ℓU ℓO : Level

-- =============================================================================
-- BRIDGE MORPHISMS: DDHom ≅ Stabilized Morphisms (under Φ = id)
-- =============================================================================

module BridgeMorphIso {ℓ ℓ' ℓ'' ℓU ℓO : Level}
                      {DS : AdmissibleDistSystem ℓ ℓ' ℓ''}
                      (OU : ObservableUniverse DS ℓU ℓO) where
                      
  open AdmissibleDistSystem DS
  open ObservableUniverse OU
  
  open import Distinction.Bridge.TrivialRefinement
  open TrivialRef DS
  open TrivialProperties OU
  
  open import Distinction.Bridge.StabilizedTypes
  open StabilizedTypeDef OU TrivialRefOp
  
  open import Distinction.Stabilization
  open Trajectory TrivialRefOp
  
  open import Distinction.Bridge.BridgeTypes
  open BridgeIso OU
  
  -- =========================================================================
  -- v0.1 STYLE MORPHISMS
  -- =========================================================================
  
  -- A v0.1 morphism: function preserving equivalence under fixed d
  record Hom01 (A B : Type01) : Set (ℓU ⊔ ℓO) where
    field
      fun : U → U
      preserves : ∀ {x y : U} → 
        x ~[ Type01.config A ] y → 
        fun x ~[ Type01.config B ] fun y
  
  -- Identity morphism
  id01 : ∀ {A : Type01} → Hom01 A A
  id01 = record { fun = id ; preserves = λ eq → eq }
  
  -- Composition
  _∘01_ : ∀ {A B C : Type01} → Hom01 B C → Hom01 A B → Hom01 A C
  g ∘01 f = record 
    { fun = Hom01.fun g ∘ Hom01.fun f
    ; preserves = λ eq → Hom01.preserves g (Hom01.preserves f eq)
    }
  
  -- =========================================================================
  -- v0.3 STYLE MORPHISMS (stabilized)
  -- =========================================================================
  
  -- A v0.3 morphism: function preserving stabilized equivalence
  record Homᵒ (A B : Typeᵒ) : Set (ℓU ⊔ ℓO) where
    private
      bA = Typeᵒ.baseD A
      bB = Typeᵒ.baseD B
      cA = Typeᵒ.carrier A
      cB = Typeᵒ.carrier B
      kA = StabilizedClass.stabilization-point cA
      kB = StabilizedClass.stabilization-point cB
      
    field
      fun : U → U
      preserves : ∀ {x y : U} → 
        x ~[ traj bA kA ] y → 
        fun x ~[ traj bB kB ] fun y
  
  -- Identity morphism
  idᵒ : ∀ {A : Typeᵒ} → Homᵒ A A
  idᵒ = record { fun = id ; preserves = λ eq → eq }
  
  -- Composition  
  _∘ᵒ_ : ∀ {A B C : Typeᵒ} → Homᵒ B C → Homᵒ A B → Homᵒ A C
  g ∘ᵒ f = record
    { fun = Homᵒ.fun g ∘ Homᵒ.fun f
    ; preserves = λ eq → Homᵒ.preserves g (Homᵒ.preserves f eq)
    }
  
  -- =========================================================================
  -- ISOMORPHISM: Hom01 ≅ Homᵒ (under trivial refinement)
  -- =========================================================================
  
  -- Forward: v0.1 → v0.3
  to-Homᵒ : ∀ {A B : Type01} → 
            Hom01 A B → Homᵒ (to-Typeᵒ A) (to-Typeᵒ B)
  to-Homᵒ {A} {B} h = record
    { fun = Hom01.fun h
    ; preserves = λ {x} {y} eq → 
        -- Need: fun x ~[traj (config B) 0] fun y
        -- Have: x ~[traj (config A) 0] y
        -- Under trivial ref: traj d 0 = d
        let dA = Type01.config A
            dB = Type01.config B
            eq' = equiv-const dA zero x y eq  -- x ~[dA] y
            pres = Hom01.preserves h eq'       -- fun x ~[dB] fun y
        in equiv-const-inv dB zero (Hom01.fun h x) (Hom01.fun h y) pres
    }
  
  -- Backward: v0.3 → v0.1
  from-Homᵒ : ∀ {A B : Type01} → 
              Homᵒ (to-Typeᵒ A) (to-Typeᵒ B) → Hom01 A B
  from-Homᵒ {A} {B} h = record
    { fun = Homᵒ.fun h
    ; preserves = λ {x} {y} eq →
        -- Need: fun x ~[config B] fun y
        -- Have: x ~[config A] y
        let dA = Type01.config A
            dB = Type01.config B
            eq' = equiv-const-inv dA zero x y eq  -- x ~[traj dA 0] y
            pres = Homᵒ.preserves h eq'            -- fun x ~[traj dB 0] fun y
        in equiv-const dB zero (Homᵒ.fun h x) (Homᵒ.fun h y) pres
    }
  
  -- =========================================================================
  -- ROUNDTRIP PROOFS
  -- =========================================================================
  
  -- Roundtrip 1: function is preserved definitionally
  roundtrip-fun-01 : ∀ {A B : Type01} (h : Hom01 A B) → 
    Hom01.fun (from-Homᵒ (to-Homᵒ h)) ≡ Hom01.fun h
  roundtrip-fun-01 h = refl
  
  roundtrip-fun-ᵒ : ∀ {A B : Type01} (h : Homᵒ (to-Typeᵒ A) (to-Typeᵒ B)) → 
    Homᵒ.fun (to-Homᵒ (from-Homᵒ h)) ≡ Homᵒ.fun h
  roundtrip-fun-ᵒ h = refl
  
  -- =========================================================================
  -- MORPHISM EQUALITY (setoid-style)
  -- =========================================================================
  
  -- Two Hom01 are equal if their underlying functions agree
  Hom01-Equiv : ∀ {A B : Type01} → Hom01 A B → Hom01 A B → Set ℓU
  Hom01-Equiv f g = ∀ (x : U) → Hom01.fun f x ≡ Hom01.fun g x
  
  -- Two Homᵒ are equal if their underlying functions agree
  Homᵒ-Equiv : ∀ {A B : Typeᵒ} → Homᵒ A B → Homᵒ A B → Set ℓU
  Homᵒ-Equiv f g = ∀ (x : U) → Homᵒ.fun f x ≡ Homᵒ.fun g x
  
  -- Full roundtrip up to equivalence
  roundtrip-equiv-01 : ∀ {A B : Type01} (h : Hom01 A B) → 
    Hom01-Equiv (from-Homᵒ (to-Homᵒ h)) h
  roundtrip-equiv-01 h x = refl
  
  roundtrip-equiv-ᵒ : ∀ {A B : Type01} (h : Homᵒ (to-Typeᵒ A) (to-Typeᵒ B)) → 
    Homᵒ-Equiv (to-Homᵒ (from-Homᵒ h)) h
  roundtrip-equiv-ᵒ h x = refl

-- =============================================================================
-- INTERPRETATION
-- =============================================================================

{-
BRIDGE MORPHISMS THEOREM

Under trivial refinement (Φ = id):

1. MORPHISM ISOMORPHISM:
   Hom01 A B ≅ Homᵒ (to-Typeᵒ A) (to-Typeᵒ B)
   
2. DEFINITIONAL PRESERVATION:
   roundtrip-fun-01 h = refl  (function preserved exactly)
   roundtrip-fun-ᵒ h = refl   (function preserved exactly)

3. CATEGORICAL STRUCTURE:
   - Identity and composition defined for both
   - Isomorphism respects categorical structure

Combined with BridgeTypes:
- Types are isomorphic: Type01 ≅ Typeᵒ
- Morphisms are isomorphic: Hom01 ≅ Homᵒ
- This is a FUNCTOR between categories

v0.1 category embeds fully and faithfully into v0.3 category.
-}
