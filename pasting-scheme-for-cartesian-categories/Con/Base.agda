------------------------------------------------------------------------
-- Pasting scheme for cartesian categories
--
-- Context
------------------------------------------------------------------------

module Con.Base where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Ty.Base
open import Ty.Properties
open import Data.Product renaming (_×_ to _∧_)
open import Data.Product.Properties

------------------------------------------------------------------------
-- Context

infixl 5 _▹_

data Con (n : ℕ) : Set where
  ε : Con n
  _▹_ :  (Γ : Con n) → (A : Arr n) → Con n

------------------------------------------------------------------------
-- Context weakening

WkCon : {n : ℕ} → Con n → Con (suc n)
WkCon ε = ε
WkCon (Γ ▹ (A , B)) = WkCon Γ ▹ (WkTy A , WkTy B)

------------------------------------------------------------------------
-- Presence in context

data _∈_ {n : ℕ} (A : Arr n) : Con n → Set where
  ∈-here : {Γ : Con n} {B : Arr n} → A ≡ B → A ∈ (Γ ▹ B)
  ∈-drop : {Γ : Con n} {B : Arr n} → A ∈ Γ → A ∈ (Γ ▹ B)

------------------------------------------------------------------------
-- Presence weakening

Wk∈ : {n : ℕ} {Γ : Con n} {A B : Ty n} → (A , B) ∈ Γ → (WkTy A , WkTy B) ∈ WkCon Γ
Wk∈ (∈-here refl) = ∈-here refl
Wk∈ (∈-drop k) = ∈-drop (Wk∈ k)

Wk∈⁻¹ : {n : ℕ} {Γ : Con n} {A B : Ty n} → (WkTy A , WkTy B) ∈ WkCon Γ → (A , B) ∈ Γ
Wk∈⁻¹ {Γ = Γ ▹ A} (∈-here x) = ∈-here (WkArr-injective x)
Wk∈⁻¹ {Γ = Γ ▹ A} (∈-drop k) = ∈-drop (Wk∈⁻¹ k)

-- Wk∈-Wk∈⁻¹ : {n : ℕ} {Γ : Con n} {A B : Ty n} {k : (WkTy A , WkTy B) ∈ WkCon Γ} → Wk∈ (Wk∈⁻¹ k) ≡ k
-- Wk∈-Wk∈⁻¹ {Γ = Γ ▹ (A' , B')} {A} {B} {k = ∈-here eq} = {!!}
-- Wk∈-Wk∈⁻¹ {Γ = Γ ▹ A} {k = ∈-drop k} = cong ∈-drop Wk∈-Wk∈⁻¹
