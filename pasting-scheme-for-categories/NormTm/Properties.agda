------------------------------------------------------------------------
-- Pasting scheme for plain categories
--
-- Properties related to NormTm
------------------------------------------------------------------------

module NormTm.Properties where

open import Ty
open import Con
open import Tm
open import NormTm.Base
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin
open import Data.Product

------------------------------------------------------------------------
-- NormTm constructors injectivity

▸-injectiveˡ : {n : ℕ} {Γ : Con n} {A B C : Ty n} {t u : NormTm Γ (A , B)} {x y : (B , C) ∈ Γ}
             → t ▸ x ≡ u ▸ y → t ≡ u
▸-injectiveˡ refl = refl

------------------------------------------------------------------------
-- Associativity of normal term merging

merge-NormTm-assoc : {n : ℕ} {Γ : Con n} {A B C D : Ty n} (t : NormTm Γ (A , B)) (u : NormTm Γ (B , C)) (v : NormTm Γ (C , D)) → merge-NormTm t (merge-NormTm u v) ≡ merge-NormTm (merge-NormTm t u) v
merge-NormTm-assoc t u norm-id = refl
merge-NormTm-assoc t u (v ▸ x) = cong (_▸ x) (merge-NormTm-assoc t u v)

------------------------------------------------------------------------
-- ∀ t, (denormalize (normalize t)) ∼ t

denormalize-normalize∼ : {n : ℕ} {Γ : Con n} {A : Arr n} (t : Tm Γ A) → denormalize (normalize t) ∼ t
denormalize-normalize∼ (var x)  = unitl (var x)
denormalize-normalize∼ id       = ∼refl
denormalize-normalize∼ (t · t') = ∼trans (lem-denormalize-normalize∼ (normalize t) (normalize t')) (∼· (denormalize-normalize∼ t) (denormalize-normalize∼ t'))
  where
  lem-denormalize-normalize∼ : {n : ℕ} {Γ : Con n} {A B C : Ty n} (t : NormTm Γ (A , B)) (t' : NormTm Γ (B , C)) → denormalize (merge-NormTm t t') ∼ (denormalize t) · (denormalize t')
  lem-denormalize-normalize∼ t norm-id  = ∼sym (unitr (denormalize t))
  lem-denormalize-normalize∼ t (t' ▸ x) = ∼trans (∼· (lem-denormalize-normalize∼ t t') ∼refl) (assoc (denormalize t) (denormalize t') (var x))

------------------------------------------------------------------------
-- if two term have the same normalization, then there are similar

≡NormTm→∼Tm : {n : ℕ} {Γ : Con n} {A : Arr n} (t u : Tm Γ A) → (normalize t ≡ normalize u) → t ∼ u
≡NormTm→∼Tm t u eq = ∼trans (∼sym (denormalize-normalize∼ t)) (∼trans (≡→∼ (cong denormalize eq)) (denormalize-normalize∼ u))
