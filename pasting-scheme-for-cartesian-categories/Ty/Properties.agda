------------------------------------------------------------------------
-- Pasting scheme for cartesian categories
--
-- Properties related to Ty
------------------------------------------------------------------------

module Ty.Properties where

open import Ty.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary public
open import Data.Nat
open import Data.Fin
open import Data.Product renaming (_×_ to _∧_)
open import Data.Product.Properties

------------------------------------------------------------------------
-- Ty constructors injectivity

×-injectiveˡ : {n : ℕ} {A B C D : Ty n} → A × B ≡ C × D → A ≡ C
×-injectiveˡ refl = refl

×-injectiveʳ : {n : ℕ} {A B C D : Ty n} → A × B ≡ C × D → B ≡ D
×-injectiveʳ refl = refl

------------------------------------------------------------------------
-- Ty weakening injectivity

WkTy-injective : {n : ℕ} {A B : Ty n} → WkTy A ≡ WkTy B → A ≡ B
WkTy-injective {A = X x} {B = X .x} refl = refl
WkTy-injective {A = 𝟙} {B = 𝟙} eq = refl
WkTy-injective {A = A × B} {B = C × D} eq = cong₂ _×_ (WkTy-injective (×-injectiveˡ eq)) (WkTy-injective (×-injectiveʳ eq))

------------------------------------------------------------------------
-- Presence constructor injectivity

►-left-injective : {n : ℕ} {A B : Ty n} {k : Fin n} {x y : A ► k}
                 → ►-left {B = B} x ≡ ►-left y → x ≡ y
►-left-injective refl = refl

►-right-injective : {n : ℕ} {A B : Ty n} {k : Fin n} {x y : A ► k}
                  → ►-right {A = B} x ≡ ►-right y → x ≡ y
►-right-injective refl = refl

------------------------------------------------------------------------
-- Presence weakening injectivity

Wk►-injective : {n : ℕ} {A : Ty n} {k : Fin n} {x y : A ► k}
                → Wk► x ≡ Wk► y → x ≡ y
Wk►-injective {x = ►-here refl} {y = ►-here refl} _ = refl
Wk►-injective {x = ►-left x} {y = ►-left y} eq = cong ►-left (Wk►-injective (►-left-injective eq))
Wk►-injective {x = ►-right x} {y = ►-right y} eq = cong ►-right (Wk►-injective (►-right-injective eq))


Wk►⁻¹-injective : {n : ℕ} {A : Ty n} {k : Fin n} {x y : WkTy A ► (suc k)}
                → Wk►⁻¹ x ≡ Wk►⁻¹ y → x ≡ y
Wk►⁻¹-injective {A = X _} {x = ►-here refl} {y = ►-here refl} _ = refl
Wk►⁻¹-injective {A = _ × _} {x = ►-left x} {y = ►-left y} eq = cong ►-left (Wk►⁻¹-injective (►-left-injective eq))
Wk►⁻¹-injective {A = _ × _} {x = ►-right x} {y = ►-right y} eq = cong ►-right (Wk►⁻¹-injective (►-right-injective eq))

Wk►⁻¹-Wk► : {n : ℕ} {A : Ty (suc n)} {k : Fin n} {x : A ► (suc k)}
          → Wk►⁻¹ (Wk► x) ≡ x
Wk►⁻¹-Wk► {x = ►-here refl} = refl
Wk►⁻¹-Wk► {x = ►-left x} = cong ►-left Wk►⁻¹-Wk►
Wk►⁻¹-Wk► {x = ►-right x} = cong ►-right Wk►⁻¹-Wk►

{-# REWRITE Wk►⁻¹-Wk► #-}

------------------------------------------------------------------------
-- Arrow weakening injectivity

WkArr-injective : {n : ℕ} {A B : Arr n} → WkArr A ≡ WkArr B → A ≡ B
WkArr-injective eq = cong₂ _,_ (WkTy-injective (,-injectiveˡ eq)) (WkTy-injective (,-injectiveʳ eq))

WkArr-injective-injective : {n : ℕ} {A B : Arr n} {x y : WkArr A ≡ WkArr B}
                          → WkArr-injective x ≡ WkArr-injective y → x ≡ y
WkArr-injective-injective {A = srcA , tgtA} {B = srcB , tgtB} {x = x} {y = y} eq = lem-WkArr-injective-injective x y eq refl refl (WkArr-injective x)
  where
  lem-WkArr-injective-injective : (x' y' : WkArr (srcA , tgtA) ≡ WkArr (srcB , tgtB)) → (eq' : WkArr-injective x ≡ WkArr-injective y)
                                → (eqx : x' ≡ x) → (eqx : y' ≡ y) → (srcA , tgtA) ≡ (srcB , tgtB) → x ≡ y
  lem-WkArr-injective-injective refl refl refl refl refl refl = refl

------------------------------------------------------------------------
-- X₀ can't be a sub-type of a weak term
no-0-in-WkTy : {n : ℕ} {A : Ty n} → ¬(WkTy A ► (# 0))
no-0-in-WkTy {A = X _} (►-here ())
no-0-in-WkTy {A = _ × _} (►-left x) = no-0-in-WkTy x
no-0-in-WkTy {A = _ × _} (►-right x) = no-0-in-WkTy x

------------------------------------------------------------------------
-- there is a unique projection for each Xₖ in a linear term
linTyProj : {n : ℕ} {A : Ty n} {k : Fin n} (pred : LinearTy A) → (x y : A ► k) → x ≡ y
linTyProj {k = zero} point (►-here refl) (►-here refl) = refl
linTyProj {k = zero} (left pred₁) (►-left x) _ = contradiction x no-0-in-WkTy
linTyProj {k = zero} (left pred₁) _ (►-left y) = contradiction y no-0-in-WkTy
linTyProj {k = zero} (left _) (►-right (►-here refl)) (►-right (►-here refl)) = refl
linTyProj {k = zero} (right _) (►-left (►-here refl)) (►-left (►-here refl)) = refl
linTyProj {k = zero} (right pred₁) _ (►-right y) = contradiction y no-0-in-WkTy
linTyProj {k = zero} (right pred₁) (►-right x) _ = contradiction x no-0-in-WkTy
linTyProj {k = zero} (weak _) x _ = contradiction x no-0-in-WkTy
linTyProj {n = suc .(suc _)} {k = suc zero} (left pred₁) (►-left x) (►-left y) = cong (λ z → ►-left z) {!x!}
linTyProj {n = suc .(suc _)} {k = suc (suc k)} (left pred₁) (►-left x) (►-left y) = cong (λ z → ►-left z) {!(Wk►⁻¹-injective (linTyProj pred₁ (Wk►⁻¹ x) (Wk►⁻¹ y)))!}
linTyProj {k = suc k} (left _) _ (►-right (►-here ()))
linTyProj {k = suc k} (left _) (►-right (►-here ())) _
linTyProj {k = suc k} (right _) (►-left (►-here ())) _
linTyProj {k = suc k} (right _) _ (►-left (►-here ()))
linTyProj {k = suc k} (right pred₁) (►-right x) (►-right y) = cong (λ z → ►-right z) {!!} -- (Wk►⁻¹-injective (linTyProj pred₁ (Wk►⁻¹ x) (Wk►⁻¹ y)))
linTyProj {k = suc k} (weak pred₁) x y = {!!} -- Wk►⁻¹-injective (linTyProj pred₁ (Wk►⁻¹ x) (Wk►⁻¹ y))
