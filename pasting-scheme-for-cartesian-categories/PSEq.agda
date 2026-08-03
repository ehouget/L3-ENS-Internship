------------------------------------------------------------------------
-- Pasting Schemes for cartesian categories
--
-- A pasting scheme is inhabited by at most one term
------------------------------------------------------------------------

open import Ty
open import Con
open import Tm
open import PS
open import NormTm
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product renaming (_×_ to _∧_)
open import Prelude

--------------------------------------------------------------------------------
-- WkNormTm⁻¹ restriction to pasting scheme normal term is injective

postulate
  WkNormTm⁻¹-injective-in-PS : {n : ℕ} {Γ : Con n} {A B : Ty n} {k : Fin n}
                             → (ps : PS (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc k)))
                             → (f g : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc k)))
                             → WkNormTm⁻¹ f ≡ WkNormTm⁻¹ g → f ≡ g

--------------------------------------------------------------------------------
-- extNormTm⁻¹ restriction to pasting scheme normal term is injective

postulate
  extNormTm⁻¹-injective-in-PS : {n : ℕ} {Γ : Con n} {A B : Ty n}
                                (ps : PS (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (# 0)))
                                (f g : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (# 0)))
                              → extNormTm⁻¹ f ≡ extNormTm⁻¹ g → f ≡ g

--------------------------------------------------------------------------------
-- Main lemma
--------------------------------------------------------------------------------

lem-PSEq : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) (f g : NormTm Γ A) → f ≡ g

-- -- ps-term
lem-PSEq (ps-term _) norm-term norm-term = refl

-- ps-proj
lem-PSEq (ps-proj k pred x) (norm-proj y) (norm-proj z) = cong norm-proj (linTyProj pred y z)

-- ps-ext
lem-PSEq (ps-ext ps) f g = extNormTm⁻¹-injective-in-PS (ps-ext ps) f g (lem-PSEq ps (extNormTm⁻¹ f) (extNormTm⁻¹ g))

-- ps-const
lem-PSEq (ps-const ps) (norm-proj x) (norm-proj y) = cong norm-proj (linTyProj (ps-src-are-linear (ps-const ps)) x y)
lem-PSEq (ps-const ps) (norm-proj x) (norm-comp _ _ _) = contradiction x no-0-in-WkTy
lem-PSEq (ps-const ps) (norm-comp _ _ _) (norm-proj y) = contradiction y no-0-in-WkTy
lem-PSEq (ps-const ps) (norm-comp norm-term (∈-here refl) (►-here refl)) (norm-comp norm-term (∈-here refl) (►-here refl)) = refl
lem-PSEq (ps-const ps) _ (norm-comp g (∈-drop l) y) = contradiction (l , y) no-0-producer-in-WkCon
lem-PSEq (ps-const ps) (norm-comp f (∈-drop k) x) _ = contradiction (k , x) no-0-producer-in-WkCon
lem-PSEq (ps-const ps) (norm-comp (norm-proj x) (∈-here ()) x₂) (norm-comp g (∈-here x₃) x₄)
lem-PSEq (ps-const ps) (norm-comp (norm-comp f x x₁) (∈-here ()) x₃) (norm-comp g (∈-here x₄) x₅)
lem-PSEq (ps-const ps) (norm-comp (norm-pair f f₁) (∈-here ()) x₁) (norm-comp g (∈-here x₂) x₃)

-- ps-pair
lem-PSEq (ps-pair ps₁ ps₂) (norm-pair f f') (norm-pair g g') = cong₂ norm-pair (lem-PSEq ps₁ f g) (lem-PSEq ps₂ f' g')

-- ps-weak
lem-PSEq (ps-weak ps) f g = WkNormTm⁻¹-injective-in-PS (ps-weak ps) f g (lem-PSEq ps (WkNormTm⁻¹ f) (WkNormTm⁻¹ g))

--------------------------------------------------------------------------------
-- Main theoreme

PSEq : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) (f g : Tm Γ A) → f ∼ g
PSEq ps f g = ≡NormTm→∼Tm f g (lem-PSEq ps (normalize f) (normalize g))
