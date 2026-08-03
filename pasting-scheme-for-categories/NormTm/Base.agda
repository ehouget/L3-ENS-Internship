------------------------------------------------------------------------
-- Pasting Schemes for plain categories
--
-- Normal Terms
------------------------------------------------------------------------

module NormTm.Base where

open import Ty
open import Con
open import Tm
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary public
open import Data.Nat
open import Data.Fin
open import Data.Product

------------------------------------------------------------------------
-- Normal terms

data NormTm {n : ℕ} (Γ : Con n) : Arr n → Set where
  norm-id : {A : Ty n} → NormTm Γ (A , A)
  _▸_     : {A B C : Ty n} → NormTm Γ (A , B) → (B , C) ∈ Γ → NormTm Γ (A , C)

------------------------------------------------------------------------
-- Normal terms weakening

WkNormTm⁻¹ : {n : ℕ} {Γ : Con (suc n)} {A B : Ty (suc n)} (t : NormTm (WkCon Γ ▹ (X (# 1) , X (# 0))) (WkTy A , WkTy B)) → NormTm Γ (A , B)
WkNormTm⁻¹ {A = X i} {B = X .i} norm-id = norm-id
WkNormTm⁻¹ {A = X i} {B = X j} (_▸_ {B = X zero} t (drop x)) = contradiction x no-arrow-from-0-in-WkCon
WkNormTm⁻¹ {A = X i} {B = X j} (_▸_ {B = X (suc k)} t x) = WkNormTm⁻¹ t ▸ Ext∈⁻¹ x

------------------------------------------------------------------------
-- Normal terms merging
merge-NormTm : {n : ℕ} {Γ : Con n} {A B C : Ty n} (t : NormTm Γ (A , B)) (u : NormTm Γ (B , C)) → NormTm Γ (A , C)
merge-NormTm t norm-id = t
merge-NormTm t (u ▸ x) = (merge-NormTm t u) ▸ x

------------------------------------------------------------------------
-- Normalization

normalize : {n : ℕ} {Γ : Con n} {A : Arr n} (t : Tm Γ A) → NormTm Γ A
normalize (var x)  = norm-id ▸ x
normalize id       = norm-id
normalize (t · t') = merge-NormTm (normalize t) (normalize t')

------------------------------------------------------------------------
-- Denormalization

denormalize : {n : ℕ} {Γ : Con n} {A : Arr n} (t : NormTm Γ A) → Tm Γ A
denormalize norm-id = id
denormalize (t ▸ x) = (denormalize t) · var x
