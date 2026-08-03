------------------------------------------------------------------------
-- Pasting scheme for cartesian categories
--
-- Properties related to Terms
------------------------------------------------------------------------

module Tm.Properties where

open import Ty
open import Con
open import Tm.Base
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_×_ to _∧_)
open import Data.Nat

------------------------------------------------------------------------
-- Propositional equality weakening to equivalence

≡→∼ : {n : ℕ} {Γ : Con n} {A : Arr n} {f g : Tm Γ A} → f ≡ g → f ∼ g
≡→∼ refl = ∼refl

