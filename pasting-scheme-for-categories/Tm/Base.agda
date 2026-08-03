------------------------------------------------------------------------
-- Pasting Schemes for plain categories
--
-- Terms and terms equivalence
------------------------------------------------------------------------

module Tm.Base where

open import Ty
open import Con
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin
open import Data.Product

------------------------------------------------------------------------
-- Terms

infixl 6 _·_

data Tm {n : ℕ} (Γ : Con n) : Arr n → Set where
  var : {A : Arr n} → A ∈ Γ → Tm Γ A
  id  : {A : Ty n} → Tm Γ (A , A)
  _·_ : {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (B , C) → Tm Γ (A , C)

------------------------------------------------------------------------
-- weakening

WkTmTy : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A , B) → Tm (WkCon Γ) (WkTy A , WkTy B)
WkTmTy (var x) = var (Wk∈ x)
WkTmTy id = id
WkTmTy (f · g) = WkTmTy f · WkTmTy g

WkTmTm : {n : ℕ} {Γ : Con n} {A : Arr n} {B : Arr n} → Tm Γ A → Tm (Γ ▹ B) A
WkTmTm (var x) = var (drop x)
WkTmTm id = id
WkTmTm (f · g) = WkTmTm f · WkTmTm g

------------------------------------------------------------------------
-- Terms equivalence

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Set where
  unitl  : {A B : Ty n} (f : Tm Γ (A , B)) → id · f ∼ f
  unitr  : {A B : Ty n} (f : Tm Γ (A , B)) → f · id ∼ f
  assoc  : {A B C D : Ty n} (f : Tm Γ (A , B)) (g : Tm Γ (B , C)) (h : Tm Γ (C , D)) → (f · g) · h ∼ f · (g · h)
  ∼·     : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (B , C)} → f ∼ f' → g ∼ g' → f · g ∼ f' · g'
  ∼refl  : {A : Arr n} {f : Tm Γ A} → f ∼ f
  ∼sym   : {A : Arr n} {f g : Tm Γ A} → f ∼ g → g ∼ f
  ∼trans : {A : Arr n} {f g h : Tm Γ A} → f ∼ g → g ∼ h → f ∼ h
