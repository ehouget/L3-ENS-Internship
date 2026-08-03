------------------------------------------------------------------------
-- Pasting Schemes for plain categories
--
-- A pasting scheme is inhabited by at most one term
------------------------------------------------------------------------

open import Ty
open import Con
open import PS
open import Tm
open import NormTm
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin

------------------------------------------------------------------------
-- Important lemma : there is an unique normal term for an arrow in a pasting scheme
lem-PSEq : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) (t u : NormTm Γ A) → t ≡ u
lem-PSEq start norm-id norm-id = refl
lem-PSEq (ext ps) (_▸_ {B = X zero} t x) _  = ⊥-elim (no-loop-in-PSCon (ext ps) {eq = refl} x)
lem-PSEq (ext ps) _ (_▸_ {B = X zero} u y) = ⊥-elim (no-loop-in-PSCon (ext ps) {eq = refl} y)
lem-PSEq (ext ps) (_▸_ {B = X (suc (suc k))} t x) _ = ⊥-elim (no-long-arrow-to-0-in-PSCon (ext ps) x)
lem-PSEq (ext ps) _ (_▸_ {B = X (suc (suc l))} u y) = ⊥-elim (no-long-arrow-to-0-in-PSCon (ext ps) y)
lem-PSEq (ext ps) (_▸_ {B = X (suc zero)} t x) (_▸_ {B = X (suc zero)} u y) = subst (λ z → t ▸ x ≡ u ▸ z) (no-repetition-in-PSCon (ext ps) x y) (cong (_▸ x) (WkNormTm⁻¹-injective-in-PS ps (lem-PSEq ps (WkNormTm⁻¹ t) (WkNormTm⁻¹ u))))

------------------------------------------------------------------------
-- Theoreme : pasting scheme are contractible
PSEq : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) (t u : Tm Γ A) → t ∼ u
PSEq ps t u = ≡NormTm→∼Tm t u (lem-PSEq ps (normalize t) (normalize u))
