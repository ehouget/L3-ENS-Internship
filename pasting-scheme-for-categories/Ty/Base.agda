------------------------------------------------------------------------
-- Pasting scheme for plain categories
--
-- Types
------------------------------------------------------------------------

module Ty.Base where

open import Data.Nat
open import Data.Fin
open import Data.Product renaming (_×_ to _∧_) public

------------------------------------------------------------------------
-- Types are reduce to n variables Xᵢ

data Ty (n : ℕ) : Set where
  X : Fin n → Ty n

------------------------------------------------------------------------
-- Types weakening

WkTy : {n : ℕ} → Ty n → Ty (suc n)
WkTy (X x) = X (suc x)

------------------------------------------------------------------------
-- Arrows

Arr : ℕ → Set
Arr n = Ty n ∧ Ty n

------------------------------------------------------------------------
-- Arrows weakening

WkArr : {n : ℕ} → Arr n → Arr (suc n)
WkArr (A , B) = (WkTy A , WkTy B)

