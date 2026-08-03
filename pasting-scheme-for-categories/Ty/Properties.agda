------------------------------------------------------------------------
-- Pasting scheme for plain categories
--
-- Properties related to Ty
------------------------------------------------------------------------

module Ty.Properties where

open import Ty.Base
open import Relation.Binary.PropositionalEquality
open import Data.Nat

------------------------------------------------------------------------
-- Arrow weakening injectivity
WkArr-injective : {n : ℕ} {A B : Arr n} → WkArr A ≡ WkArr B → A ≡ B
WkArr-injective {A = X i , X j} {B = X .i , X .j} refl = refl
