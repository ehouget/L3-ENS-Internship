------------------------------------------------------------------------
-- Pasting Schemes for cartesian categories
--
-- Pasting Scheme are inhabited
------------------------------------------------------------------------

open import Ty
open import Con
open import Tm
open import PS
open import NormTm
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product renaming (_×_ to _∧_)

--------------------------------------------------------------------------------
-- Pasting scheme are inhabited

PSTm : {n : ℕ} {Γ : Con n} {A B : Ty n} → PS Γ (A , B) → Tm Γ (A , B)
PSTm (ps-term _) = term
PSTm (ps-proj k pred x) = projTm x
PSTm (ps-ext ps) = WkTmCon (WkTmTy (PSTm ps)) · var (∈-here refl)
PSTm (ps-const ps) = term · var (∈-here refl)
PSTm (ps-pair ps₁ ps₂) = pair (PSTm ps₁) (PSTm ps₂)
PSTm (ps-weak ps) = WkTmCon (WkTmTy (PSTm ps))
