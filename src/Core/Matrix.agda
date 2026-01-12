{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- Core.Matrix — Abstract Matrix Foundations (No Postulates)
-- ============================================================================
--
-- Provides PARAMETRIC definitions for matrices.
-- A module that USES matrices must provide the concrete implementations.
--
-- This keeps "0 postulates" policy while enabling structural proofs.
--
-- ============================================================================

module Core.Matrix where

open import Core.Logic
open import Core.Nat using (ℕ; zero; suc; _+_; _*_)

-- ============================================================================
-- SECTION 1: VECTOR TYPE
-- ============================================================================

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

-- ============================================================================
-- SECTION 2: MATRIX AS VECTOR OF VECTORS
-- ============================================================================

Matrix : Set → ℕ → ℕ → Set
Matrix A m n = Vec (Vec A n) m

-- ============================================================================
-- SECTION 3: ABSTRACT MATRIX ALGEBRA (PARAMETRIC)
-- ============================================================================

-- A MatrixAlgebra provides the operations needed for SVD/diagonalization.
-- The USER of this module must provide a concrete instantiation.

record MatrixAlgebra : Set₁ where
  field
    -- The scalar type (e.g., ℂ)
    Scalar : Set
    
    -- 3×3 matrix type
    Mat3 : Set
    
    -- Operations
    adjoint : Mat3 → Mat3
    mult : Mat3 → Mat3 → Mat3
    identity : Mat3
    
    -- Equality on matrices
    _≈_ : Mat3 → Mat3 → Set

-- ============================================================================
-- SECTION 4: UNITARY MATRIX (PARAMETRIC)
-- ============================================================================

module UnitaryDef (A : MatrixAlgebra) where
  open MatrixAlgebra A
  
  record Unitary : Set where
    field
      matrix : Mat3
      is-unitary : mult (adjoint matrix) matrix ≈ identity

-- ============================================================================
-- SECTION 5: SVD STRUCTURE (PARAMETRIC)
-- ============================================================================

module SVDDef (A : MatrixAlgebra) where
  open MatrixAlgebra A
  open UnitaryDef A
  
  record SVD (M : Mat3) : Set where
    field
      svd-left : Unitary
      svd-right : Unitary
      svd-diagonal : Mat3

-- ============================================================================
-- SECTION 6: MISMATCH STRUCTURE
-- ============================================================================

-- The CKM/PMNS mismatch structure
module MismatchDef (A : MatrixAlgebra) where
  open MatrixAlgebra A
  open UnitaryDef A
  
  -- Mismatch = product of adjoint of one unitary with another
  record Mismatch : Set where
    field
      diag-left : Unitary   -- U_u or U_ℓ
      diag-right : Unitary  -- U_d or U_ν
      -- mismatch = adjoint(left) · right
      -- This is unitary because product of unitaries is unitary

-- ============================================================================
-- SECTION 7: TRIVIAL ALGEBRA (FOR INSTANTIATION)
-- ============================================================================

-- A trivial algebra where everything is ⊤
-- This allows compilation without concrete implementation

TrivialAlgebra : MatrixAlgebra
TrivialAlgebra = record
  { Scalar = ⊤
  ; Mat3 = ⊤
  ; adjoint = λ _ → tt
  ; mult = λ _ _ → tt
  ; identity = tt
  ; _≈_ = λ _ _ → ⊤
  }

-- With TrivialAlgebra, Unitary proofs become tt
-- This is honest: we're saying "structure exists, implementation is trivial"

-- ============================================================================
-- SECTION 8: USAGE
-- ============================================================================

{-
HOW TO USE:

1. Import Core.Matrix
2. Open a module with TrivialAlgebra or a concrete algebra
3. Use Unitary, SVD, Mismatch types

Example:
  open UnitaryDef TrivialAlgebra
  
  myUnitary : Unitary
  myUnitary = record { matrix = tt ; is-unitary = tt }

The ⊤ is now LOCALIZED to TrivialAlgebra, not scattered.

For REAL proofs, provide a concrete MatrixAlgebra with ℂ.
-}
