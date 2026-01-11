{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- Core.Nat — Natural numbers
-- ============================================================================

module Core.Nat where

open import Core.Logic

-- ============================================================================
-- NATURAL NUMBERS
-- ============================================================================

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- DD/* compatibility
Nat : Set
Nat = ℕ

-- ============================================================================
-- BASIC OPERATIONS
-- ============================================================================

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

infixl 6 _+_
infixl 7 _*_

-- ============================================================================
-- ORDERING
-- ============================================================================

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

infix 4 _≤_ _<_

-- ============================================================================
-- BASIC LEMMAS
-- ============================================================================

+-identityʳ : ∀ n → n + zero ≡ n
+-identityʳ zero    = refl
+-identityʳ (suc n) = cong suc (+-identityʳ n)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym (+-identityʳ n)
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

-- ============================================================================
-- DECIDABLE EQUALITY
-- ============================================================================

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

_≟ℕ_ : (m n : ℕ) → Dec (m ≡ n)
zero  ≟ℕ zero  = yes refl
zero  ≟ℕ suc n = no (λ ())
suc m ≟ℕ zero  = no (λ ())
suc m ≟ℕ suc n with m ≟ℕ n
... | yes p = yes (cong suc p)
... | no ¬p = no (λ eq → ¬p (suc-injective eq))

-- ============================================================================
-- FINITE SETS
-- ============================================================================

data Fin : ℕ → Set where
  fzero : ∀ {n} → Fin (suc n)
  fsuc  : ∀ {n} → Fin n → Fin (suc n)
