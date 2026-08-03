------------------------------------------------------------------------
-- Pasting scheme for cartesian categories
--
-- Properties related to Context
------------------------------------------------------------------------

module Con.Properties where

open import Ty
open import Con.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary public
open import Data.Nat
open import Data.Fin

------------------------------------------------------------------------
-- Presence constuctors injectivity

drop-injective : {n : ℕ} {Γ : Con n} {A B : Arr n} {x y : A ∈ Γ}
               → drop {B = B} x ≡ drop {B = B} y → x ≡ y
drop-injective refl = refl

------------------------------------------------------------------------
-- Presence weakening injectivity

Wk∈⁻¹-injective : {n : ℕ} {Γ : Con n} {A B : Ty n} {x y : (WkTy A , WkTy B) ∈ WkCon Γ}
                → Wk∈⁻¹ x ≡ Wk∈⁻¹ y → x ≡ y
Wk∈⁻¹-injective {Γ = Γ ▹ (X i , X j)} {A = X .i} {B = X .j} {x = here} {y = here} eq = refl
Wk∈⁻¹-injective {Γ = Γ ▹ (X i , X j)} {A = X k} {B = X l} {x = drop x} {y = drop y} eq = cong drop (Wk∈⁻¹-injective (drop-injective eq))

------------------------------------------------------------------------
-- If a arrow is contain in a weak context, then it's a weak arrow

Ty∈WkCon→WkTy∈Con : {n : ℕ} {B : Arr (suc n)} {Γ : Con n} → B ∈ (WkCon Γ) → ∃[ A ] (WkArr A ≡ B ∧ A ∈ Γ)
Ty∈WkCon→WkTy∈Con {Γ = Γ ▹ head} here = head , refl , here
Ty∈WkCon→WkTy∈Con {Γ = Γ ▹ _} (drop k) = proj₁ (Ty∈WkCon→WkTy∈Con k) , proj₁ (proj₂ (Ty∈WkCon→WkTy∈Con k)) , drop (proj₂ (proj₂ (Ty∈WkCon→WkTy∈Con k)))

------------------------------------------------------------------------
-- There is no X₀ in the weakening of a context

no-0-in-WkCon : {n : ℕ} {Γ : Con n} {A : Ty (suc n)} → ¬ ((A , X (# 0)) ∈ WkCon Γ)
no-0-in-WkCon {Γ = Γ ▹ (_ , X _)} (drop k) = no-0-in-WkCon k

------------------------------------------------------------------------
-- No arrow in a weak context has X₀ as source

no-arrow-from-0-in-WkCon : {n : ℕ} {Γ : Con n} {B : Ty (suc n)} → ¬((X (# 0) , B) ∈  WkCon Γ)
no-arrow-from-0-in-WkCon {Γ = Γ ▹ (X i , X j)} (drop k) = no-arrow-from-0-in-WkCon k
