------------------------------------------------------------------------
-- Pasting Schemes for plain categories
--
-- Pasting Scheme are inhabited
------------------------------------------------------------------------

open import Ty
open import Con
open import Tm
open import PS
open import Data.Nat

--------------------------------------------------------------------------------
-- Pasting scheme are inhabited

PSTm : {n : ℕ} {Γ : Con n} {A : Arr n} → PS Γ A → Tm Γ A
PSTm start = id
PSTm (ext ps) = WkTmTm (WkTmTy (PSTm ps)) · var here
