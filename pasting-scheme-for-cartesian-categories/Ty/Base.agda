------------------------------------------------------------------------
-- Pasting scheme for cartesian categories
--
-- Types
------------------------------------------------------------------------

module Ty.Base where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin
open import Data.Fin.Properties
open import Data.Product renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Types

infixr 6 _×_

-- Types
data Ty (n : ℕ) : Set where
  X   : Fin n → Ty n
  𝟙   : Ty n
  _×_ : (A B : Ty n) → Ty n

------------------------------------------------------------------------
-- Types weakening

WkTy : {n : ℕ} → Ty n → Ty (suc n)
WkTy (X x) = X (suc x)
WkTy 𝟙 = 𝟙
WkTy (A × B) = WkTy A × WkTy B

------------------------------------------------------------------------
-- Presence of a simple type

infixr 5 _►_

data _►_ {n : ℕ} : Ty n → Fin n → Set where
  ►-here  : {k : Fin n} {l : Fin n} → l ≡ k → X l ► k
  ►-left  : {k : Fin n} {A B : Ty n} → A ► k → A × B ► k
  ►-right : {k : Fin n} {A B : Ty n} → B ► k → A × B ► k

------------------------------------------------------------------------
-- Presence weakening

Wk► : {n : ℕ} {A : Ty n} {k : Fin n} → A ► k → WkTy A ► suc k
Wk► (►-here eq) = (►-here (cong suc eq))
Wk► (►-left x) = ►-left (Wk► x)
Wk► (►-right x) = ►-right (Wk► x)

Wk►⁻¹ : {n : ℕ} {A : Ty n} {k : Fin n} → WkTy A ► suc k →  A ► k
Wk►⁻¹ {A = X _} (►-here refl) = ►-here refl
Wk►⁻¹ {A = _ × _} (►-left x) = ►-left (Wk►⁻¹ x)
Wk►⁻¹ {A = _ × _} (►-right x) = ►-right (Wk►⁻¹ x)

Wk►-Wk►⁻¹ : {n : ℕ} {A : Ty n} {k : Fin n} {x : WkTy A ► suc k} → Wk► (Wk►⁻¹ x) ≡ x
Wk►-Wk►⁻¹ {A = X _}   {x = ►-here refl} = refl
Wk►-Wk►⁻¹ {A = _ × _} {x = ►-left x}    = cong ►-left Wk►-Wk►⁻¹
Wk►-Wk►⁻¹ {A = _ × _} {x = ►-right x}   = cong ►-right Wk►-Wk►⁻¹

------------------------------------------------------------------------
-- Arrow

Arr : ℕ → Set
Arr n = Ty n ∧ Ty n

------------------------------------------------------------------------
-- Arrow weakening

WkArr : {n : ℕ} → Arr n → Arr (suc n)
WkArr (A , B) = (WkTy A , WkTy B)

------------------------------------------------------------------------
-- Linear types

data LinearTy : {n : ℕ} → Ty n → Set where
  -- void  : LinearTy {n = 0} 𝟙
  point : LinearTy {n = 1} (X (# 0))
  left  : {n : ℕ} {A : Ty n} → LinearTy A → LinearTy {n = suc n} (WkTy A × X (# 0))
  right : {n : ℕ} {A : Ty n} → LinearTy A → LinearTy {n = suc n} (X (# 0) × WkTy A)
  weak  : {n : ℕ} {A : Ty n} → LinearTy A → LinearTy {n = suc n} (WkTy A)
