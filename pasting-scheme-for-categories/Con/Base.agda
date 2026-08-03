------------------------------------------------------------------------
-- Pasting scheme for plain categories
--
-- Context
------------------------------------------------------------------------

module Con.Base where

open import Ty.Base
open import Data.Nat
open import Data.Fin

------------------------------------------------------------------------
-- Context

infixl 5 _▹_

data Con (n : ℕ) : Set where
  ε : Con n
  _▹_ : (Γ : Con n) (A : Arr n) → Con n

------------------------------------------------------------------------
-- Context weakening

WkCon : {n : ℕ} → Con n → Con (suc n)
WkCon ε = ε
WkCon (Γ ▹ (A , B)) = WkCon Γ ▹ (WkTy A , WkTy B)

------------------------------------------------------------------------
-- Presence in context

data _∈_ {n : ℕ} (A : Arr n) : Con n → Set where
  here : {Γ : Con n} → A ∈ (Γ ▹ A)
  drop : {Γ : Con n} {B : Arr n} → A ∈ Γ → A ∈ (Γ ▹ B)

------------------------------------------------------------------------
-- Presence weakening

Wk∈ : {n : ℕ} {Γ : Con n} {A B : Ty n} → (A , B) ∈ Γ → (WkTy A , WkTy B) ∈ WkCon Γ
Wk∈ here = here
Wk∈ (drop x) = drop (Wk∈ x)

Wk∈⁻¹ : {n : ℕ} {Γ : Con n} {A B : Ty n} → (WkTy A , WkTy B) ∈ WkCon Γ → (A , B) ∈ Γ
Wk∈⁻¹ {Γ = Γ ▹ (X i , X j)} {A = X .i} {B = X .j} here = here
Wk∈⁻¹ {Γ = Γ ▹ (X i , X j)} {A = X x} {B = X y} (drop k) = drop (Wk∈⁻¹ k)

------------------------------------------------------------------------
-- Presence extension (weakening + fresh arrow append to the context)

Ext∈⁻¹ : {n : ℕ} {Γ : Con (suc n)} {A B : Ty (suc n)} → (WkTy A , WkTy B) ∈ (WkCon Γ ▹ (X (# 1) , X (# 0))) → (A , B) ∈ Γ
Ext∈⁻¹ {Γ = ε} {B = X y} (drop ())
Ext∈⁻¹ {Γ = Γ ▹ (X i , X j)} {A = X x} {B = X y} (drop k) = Wk∈⁻¹ k
