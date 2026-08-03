------------------------------------------------------------------------
-- Pasting scheme for plain categories
--
-- Pasting scheme
------------------------------------------------------------------------

module PS.Base where

open import Ty
open import Con
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin
open import Data.Product

------------------------------------------------------------------------
-- Pasting schemes

data PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set where
   start : PS {n = 1} ε (X (# 0) , X (# 0))
   ext   : {k : ℕ}
           {Γ : Con (suc k)} -- context with at least one object
         → PS {n = suc k} Γ (X (fromℕ< {m = k} (s≤s ≤-refl)) , X (# 0))
        -- PS Γ (X (# k) , X (# 0))
         → PS {n = suc (suc k)}
           (WkCon Γ ▹ (X (# 1) , X (# 0)))
           (X (fromℕ< {m = suc k} (s≤s (s≤s ≤-refl))) , X (# 0))
        -- PS (WkCon Γ ▹ (X (# 1) , X (# 0))) (X (# k+1) , X (# 0))


------------------------------------------------------------------------
-- Examples of pasting schemes

PS⊢X⇒X : PS {n = 1} ε (X (# 0) , X (# 0))
PS⊢X⇒X = start

PSX⇒Y⊢X⇒Y : PS {n = 2} (ε ▹ (X (# 1) , X (# 0))) (X (# 1) , X (# 0))
PSX⇒Y⊢X⇒Y = ext start

PSX⇒Y,Y⇒Z⊢X⇒Z : PS {n = 3} (ε ▹ ((X (# 2)) , (X (# 1))) ▹ (X (# 1) , X (# 0))) (X (# 2) , X (# 0))
PSX⇒Y,Y⇒Z⊢X⇒Z = ext (ext start)

