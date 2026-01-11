{-# OPTIONS --safe --without-K #-}

-- ============================================================================
-- Core — Re-exports all core modules
-- ============================================================================
-- This is the single import point for foundational definitions.
-- Both Distinction/* and DD/* should import from here.
-- ============================================================================

module Core where

open import Core.Logic public
open import Core.Nat public
open import Core.Omega public
open import Core.Dyad public
