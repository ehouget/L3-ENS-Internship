------------------------------------------------------------------------
-- Pasting Schemes for cartesian categories
--
-- Terms and terms equivalence
------------------------------------------------------------------------

module Tm.Base where

open import Ty
open import Con
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin
open import Data.Product renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Terms

infixl 6 _·_

data Tm {n : ℕ} (Γ : Con n) : Arr n → Set where
  var  : {A : Arr n} → A ∈ Γ → Tm Γ A
  id   : {A : Ty n} → Tm Γ (A , A)
  _·_  : {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (B , C) → Tm Γ (A , C)
  term : {A : Ty n} → Tm Γ (A , 𝟙)
  pair : {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (A , C) → Tm Γ (A , B × C)
  fst  : {A B : Ty n} → Tm Γ (A × B , A)
  snd  : {A B : Ty n} → Tm Γ (A × B , B)

------------------------------------------------------------------------
-- weakening

WkTmTy : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A , B) → Tm (WkCon Γ) (WkTy A , WkTy B)
WkTmTy (var x) = var (Wk∈ x)
WkTmTy id = id
WkTmTy (f · g) = WkTmTy f · WkTmTy g
WkTmTy term = term
WkTmTy (pair f g) = pair (WkTmTy f) (WkTmTy g)
WkTmTy fst = fst
WkTmTy snd = snd

WkTmCon : {n : ℕ} {Γ : Con n} {A : Arr n} {B : Arr n} → Tm Γ A → Tm (Γ ▹ B) A
WkTmCon (var x) = var (∈-drop x)
WkTmCon id = id
WkTmCon (f · g) = WkTmCon f · WkTmCon g
WkTmCon term = term
WkTmCon (pair f g) = pair (WkTmCon f) (WkTmCon g)
WkTmCon fst = fst
WkTmCon snd = snd

------------------------------------------------------------------------
-- Terms equivalence

infix 5 _∼_

data _∼_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Set where
  pfst : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · fst ∼ f
  psnd : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pair f g · snd ∼ g
  pnat : {A' A B C : Ty n} (f : Tm Γ (A' , A)) (g : Tm Γ (A , B)) (h : Tm Γ (A , C)) → f · pair g h ∼ pair (f · g) (f · h)
  -- NOTE: both pext are equivalent in presence of naturality
  -- pext : {X A B : Ty n} (f : Tm Γ (X , A × B)) → pair (f · fst) (f · snd) ∼ f
  pext : {A B : Ty n} → pair fst snd ∼ id {A = A × B}
  text : {A : Ty n} (f : Tm Γ (A , 𝟙)) → f ∼ term
  unitl : {A B : Ty n} (f : Tm Γ (A , B)) → id · f ∼ f
  unitr : {A B : Ty n} (f : Tm Γ (A , B)) → f · id ∼ f
  assoc : {A B C D : Ty n} (f : Tm Γ (A , B)) (g : Tm Γ (B , C)) (h : Tm Γ (C , D)) → (f · g) · h ∼ f · (g · h)
  ∼· : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (B , C)} → f ∼ f' → g ∼ g' → f · g ∼ f' · g'
  ∼pair : {X A B : Ty n} {f f' : Tm Γ (X , A)} {g g' : Tm Γ (X , B)} → f ∼ f' → g ∼ g' → pair f g ∼ pair f' g'
  ∼refl : {A : Arr n} {f : Tm Γ A} → f ∼ f
  ∼sym  : {A : Arr n} {f g : Tm Γ A} → f ∼ g → g ∼ f
  ∼trans : {A : Arr n} {f g h : Tm Γ A} → f ∼ g → g ∼ h → f ∼ h

------------------------------------------------------------------------
-- projection terms

projTm : {n : ℕ} {Γ : Con n} {A : Ty n} {k : Fin n} (x : A ► k) → Tm Γ (A , X k)
projTm (►-here refl) = id
projTm (►-left x) = fst · projTm x
projTm (►-right x) = snd · projTm x
