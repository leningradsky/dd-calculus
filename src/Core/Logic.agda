{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- Core.Logic — Foundational logical primitives
-- ============================================================================
-- Single source of truth for basic logic used by both:
--   - Distinction/* (dd-calculus)
--   - DD/* (physics derivations)
-- ============================================================================

module Core.Logic where

-- ============================================================================
-- EMPTY TYPE (Falsity)
-- ============================================================================

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

-- Alternative names for compatibility with DD/*
Empty : Set
Empty = ⊥

Empty-elim : {A : Set} → Empty → A
Empty-elim = ⊥-elim

-- ============================================================================
-- UNIT TYPE (Truth)
-- ============================================================================

data ⊤ : Set where
  tt : ⊤

Unit : Set
Unit = ⊤

-- ============================================================================
-- NEGATION
-- ============================================================================

¬_ : Set → Set
¬ A = A → ⊥

Not : Set → Set
Not = ¬_

-- ============================================================================
-- EQUALITY
-- ============================================================================

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≡_

-- Synonyms for DD/* compatibility
_==_ : {A : Set} → A → A → Set
_==_ = _≡_

-- Inequality
_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

-- ============================================================================
-- EQUALITY LEMMAS
-- ============================================================================

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} {x₁ x₂ : A} {y₁ y₂ : B} (f : A → B → C) → 
        x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂ f refl refl = refl

subst : {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

-- ============================================================================
-- SUM TYPE (Disjunction)
-- ============================================================================

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_

-- DD/* compatibility
_Plus_ : Set → Set → Set
_Plus_ = _⊎_

pattern left x = inj₁ x
pattern right x = inj₂ x

-- ============================================================================
-- PRODUCT TYPE (Conjunction)
-- ============================================================================

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

infixr 2 _×_

-- DD/* compatibility
_And_ : Set → Set → Set
_And_ = _×_

-- ============================================================================
-- DEPENDENT SUM (Σ-type)
-- ============================================================================

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

∃ : {A : Set} → (A → Set) → Set
∃ {A} B = Σ A B

syntax ∃ (λ x → B) = ∃[ x ] B

-- ============================================================================
-- DECIDABILITY
-- ============================================================================

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : ¬ A → Dec A

-- ============================================================================
-- FUNCTION COMPOSITION
-- ============================================================================

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

infixr 9 _∘_

-- Identity
id : {A : Set} → A → A
id x = x
