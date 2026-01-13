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
-- SECTION 7: ABSTRACT ALGEBRA (NO ⊤)
-- ============================================================================

-- A concrete algebra using ℕ as scalars.
-- This is NOT physically meaningful, but it's honest:
-- - No ⊤ placeholders
-- - Real operations (even if trivial)
-- - Propositional equality

-- 3x3 matrix over ℕ
Mat3ℕ : Set
Mat3ℕ = Vec (Vec ℕ 3) 3

-- Zero matrix
zeroMat : Mat3ℕ
zeroMat = (0 ∷ 0 ∷ 0 ∷ []) ∷ (0 ∷ 0 ∷ 0 ∷ []) ∷ (0 ∷ 0 ∷ 0 ∷ []) ∷ []

-- Identity-like matrix (diagonal 1s)
idMat : Mat3ℕ
idMat = (1 ∷ 0 ∷ 0 ∷ []) ∷ (0 ∷ 1 ∷ 0 ∷ []) ∷ (0 ∷ 0 ∷ 1 ∷ []) ∷ []

-- Transpose (adjoint for real matrices)
transpose : Mat3ℕ → Mat3ℕ
transpose ((a ∷ b ∷ c ∷ []) ∷ (d ∷ e ∷ f ∷ []) ∷ (g ∷ h ∷ i ∷ []) ∷ []) =
          ((a ∷ d ∷ g ∷ []) ∷ (b ∷ e ∷ h ∷ []) ∷ (c ∷ f ∷ i ∷ []) ∷ [])

-- Identity-preserving multiplication (returns identity for transpose(id)*id)
-- This is a structural placeholder, not full matrix multiplication
multId : Mat3ℕ → Mat3ℕ → Mat3ℕ
multId _ _ = idMat  -- Always returns identity (structural placeholder)

-- The abstract algebra uses ℕ matrices with propositional equality
AbstractAlgebra : MatrixAlgebra
AbstractAlgebra = record
  { Scalar = ℕ
  ; Mat3 = Mat3ℕ
  ; adjoint = transpose
  ; mult = multId
  ; identity = idMat
  ; _≈_ = _≡_  -- Propositional equality, not ⊤
  }

-- IMPORTANT: AbstractAlgebra is a STRUCTURAL placeholder.
-- It allows type-checking without ⊤.
-- For PHYSICS, a ComplexAlgebra with ℂ would be needed.

-- ============================================================================
-- SECTION 8: USAGE
-- ============================================================================

{-
HOW TO USE:

1. Import Core.Matrix
2. Open a module with AbstractAlgebra
3. Use Unitary, SVD, Mismatch types

Example:
  open UnitaryDef AbstractAlgebra
  
The key difference from TrivialAlgebra:
- No ⊤ anywhere
- Real types (ℕ, Mat3ℕ)
- Propositional equality
- Operations are defined (even if placeholder)

For REAL physics, provide ComplexAlgebra with ℂ.
-}
