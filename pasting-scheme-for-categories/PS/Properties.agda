------------------------------------------------------------------------
-- Pasting scheme for plain categories
--
-- Properties about pasting scheme
------------------------------------------------------------------------

module PS.Properties where

open import Ty
open import Con
open import PS.Base
open import NormTm
open import Relation.Binary.PropositionalEquality
open import Data.Empty public
open import Data.Nat
open import Data.Nat.Properties hiding (≤-antisym ; suc-injective)
open import Data.Fin renaming (_≥_ to _≥Fin_)
open import Data.Fin.Properties using (inject₁-injective ; ≤-antisym ; suc-injective)
open import Data.Product

------------------------------------------------------------------------
-- There is no loop in the context of a pasting scheme

no-loop-in-PSCon : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) {x y : Ty n} {eq : x ≡ y} → ¬ ((x , y) ∈ Γ)
no-loop-in-PSCon ps {eq = refl} = lem-no-loop-in-PSCon ps
  where
  lem-no-loop-in-PSCon : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) {B : Ty n} → ¬ ((B , B) ∈ Γ)
  lem-no-loop-in-PSCon (ext ps) (drop k) = (lem-WkCon-dont-add-loop (lem-no-loop-in-PSCon ps)) k
    where
    lem-WkCon-dont-add-loop : {n : ℕ} {Γ : Con n} {A : Ty (suc n)} → ({B : Ty n} → (¬((B , B) ∈ Γ))) → (¬((A , A) ∈ (WkCon Γ)))
    lem-WkCon-dont-add-loop {Γ = ε ▹ (X x , X x)}               f here     = f here
    lem-WkCon-dont-add-loop {Γ = Γ ▹ (X w , X x) ▹ (X y , X y)} f here     = f here
    lem-WkCon-dont-add-loop {Γ = Γ ▹ (X w , X x) ▹ (X y , X z)} f (drop k) = (lem-WkCon-dont-add-loop (λ t → f (drop t))) k

------------------------------------------------------------------------
-- There is no long arrow to 0 in the context of pasting scheme
no-long-arrow-to-0-in-PSCon : {n : ℕ} {Γ : Con (suc (suc n))} {A : Arr (suc (suc n))} (ps : PS Γ A) {k : Fin n} → ¬((X (suc (suc k)) , (X (# 0))) ∈ Γ)
no-long-arrow-to-0-in-PSCon {suc n} (ext ps) (drop k) = (lem-WkCon-dont-add-long-arrow-to-0 ((no-long-arrow-to-0-in-PSCon ps))) k
  where
  lem-WkCon-dont-add-long-arrow-to-0 : {n : ℕ} {Γ : Con (suc (suc n))}
                                     → ({k : Fin n} → ¬((X (suc (suc k)) , (X (# 0))) ∈ Γ))
                                     → ({k : Fin (suc n)} → ¬((X (suc (suc k)) , (X (# 0))) ∈ (WkCon Γ)))
  lem-WkCon-dont-add-long-arrow-to-0 {Γ = ε ▹ (X x₁ , X y₁)} f (drop ())
  lem-WkCon-dont-add-long-arrow-to-0 {Γ = Γ ▹ (X x₂ , X y₂) ▹ (X x₁ , X y₁)} f (drop k) = (lem-WkCon-dont-add-long-arrow-to-0 (λ x → f (drop x))) k

------------------------------------------------------------------------
-- Source of a arrow in a pasting scheme is greater than its target
Arr-in-PSCon-are-forward : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) {x y : Fin n} → (X x , X y) ∈ Γ → x ≥Fin y
Arr-in-PSCon-are-forward (ext start)    here     = z≤n
Arr-in-PSCon-are-forward (ext (ext ps)) here     = z≤n
Arr-in-PSCon-are-forward (ext (ext ps)) (drop k) = (lem-WkCon-keep-Arr-forward (Arr-in-PSCon-are-forward (ext ps)))  k
  where
  lem-WkCon-keep-Arr-forward : {n : ℕ} {Γ : Con n}
                             → ({x₁ y₁ : Fin n} → (X x₁ , X y₁) ∈ Γ → x₁ ≥Fin y₁)
                             → ({x₂ y₂ : Fin (suc n)} → (X x₂ , X y₂) ∈ WkCon Γ → x₂ ≥Fin y₂)
  lem-WkCon-keep-Arr-forward {Γ = ε ▹ (X i , X j)}        f {x₂ = .(suc i)} {y₂ = .(suc j)} here     = s≤s (f here)
  lem-WkCon-keep-Arr-forward {Γ = Γ ▹ neck ▹ (X i , X j)} f {x₂ = .(suc i)} {y₂ = .(suc j)} here     = s≤s (f here)
  lem-WkCon-keep-Arr-forward {Γ = Γ ▹ neck ▹ (X i , X j)} f {x₂ = x₂}       {y₂ = y₂}       (drop k) = (lem-WkCon-keep-Arr-forward λ l → f (drop l)) k

------------------------------------------------------------------------
-- The source of a normal term is greater than its target
Arr-of-NormTm-in-PSCon-are-forward : {n : ℕ} {Γ : Con n} {A : Arr n} (ps : PS Γ A) {x y : Fin n} → (t : NormTm Γ (X x , X y)) → x ≥Fin y
Arr-of-NormTm-in-PSCon-are-forward start    norm-id             = ≤-refl
Arr-of-NormTm-in-PSCon-are-forward (ext ps) norm-id             = ≤-refl
Arr-of-NormTm-in-PSCon-are-forward (ext ps) (_▸_ {B = X k} t x) = ≤-trans (Arr-in-PSCon-are-forward (ext ps) x) (Arr-of-NormTm-in-PSCon-are-forward (ext ps) t)


------------------------------------------------------------------------
-- Each arrow in a pasting scheme context is different of all the other one
no-repetition-in-PSCon' : {n : ℕ} {Γ : Con n} {A B C : Arr n} (ps : PS (Γ ▹ B) A) → C ∈ Γ → B ≢ C
no-repetition-in-PSCon' (ext (ext start)) here ()
no-repetition-in-PSCon' (ext (ext start)) (drop ()) eq
no-repetition-in-PSCon' (ext {Γ = Γ} ps) k eq = contradiction ((subst (λ x → x ∈ WkCon Γ) (sym eq) k)) no-0-in-WkCon

------------------------------------------------------------------------
-- Each arrow in a pasting scheme context appears only once
no-repetition-in-PSCon : {n : ℕ} {Γ : Con n} {A B : Arr n} (ps : PS Γ A) (x y : B ∈ Γ) → x ≡ y
no-repetition-in-PSCon ps here here = refl
no-repetition-in-PSCon ps here (drop y) = contradiction refl (no-repetition-in-PSCon' ps y)
no-repetition-in-PSCon ps (drop x) here = contradiction refl (no-repetition-in-PSCon' ps x)
no-repetition-in-PSCon (ext ps) (drop x) (drop y) = cong drop ((lem-WkCon-dont-add-repetition (no-repetition-in-PSCon ps)) x y)
  where
  lem-WkCon-dont-add-repetition : {n : ℕ} {Γ : Con n}
                              → ({B : Arr n} (x₁ y₁ : B ∈ Γ) → x₁ ≡ y₁)
                              → ({B : Arr (suc n)} (x₂ y₂ : B ∈ WkCon Γ) → x₂ ≡ y₂)
  lem-WkCon-dont-add-repetition {Γ = Γ} f {B = B} x₂ y₂ = aux (Ty∈WkCon→WkTy∈Con x₂) (Ty∈WkCon→WkTy∈Con y₂)
    where
    aux : (∃-syntax (λ Ax → WkArr Ax ≡ B ∧ (Ax ∈ Γ))) → (∃-syntax (λ Ay → WkArr Ay ≡ B ∧ (Ay ∈ Γ))) → x₂ ≡ y₂
    aux (ax , refl , zx) (ay , eqy , zy) = aux2 (sym (WkArr-injective eqy))
      where
      aux2 : (eqaxay : ax ≡ ay) → x₂ ≡ y₂
      aux2 refl = Wk∈⁻¹-injective (f (Wk∈⁻¹ x₂) (Wk∈⁻¹ y₂))


------------------------------------------------------------------------
-- Arrows in pasting scheme have the form x_i+1 → x_i

form-of-arrow-in-PSCon : {n : ℕ} {Γ : Con n} {A : Arr n} {x y : Fin n} (ps : PS Γ A)
                       → (X x , X y) ∈ Γ → inject₁ x ≡ suc y
form-of-arrow-in-PSCon {x = zero}        {y = zero}  ps       k        = ⊥-elim (no-loop-in-PSCon ps {eq = refl} k)
form-of-arrow-in-PSCon {x = zero}        {y = suc y} ps       k        = contradiction (Arr-in-PSCon-are-forward ps k) (<⇒≱ (s≤s z≤n))
form-of-arrow-in-PSCon {x = suc zero}    {y = zero}  ps       k        = refl
form-of-arrow-in-PSCon {x = suc (suc x)} {y = zero}  ps       k        = ⊥-elim (no-long-arrow-to-0-in-PSCon ps k)
form-of-arrow-in-PSCon {x = suc x}       {y = suc y} (ext ps) (drop k) = cong suc (form-of-arrow-in-PSCon ps (suc∈WkCon→∈ k))
  where
  suc∈WkCon→∈ : {n : ℕ} {Γ : Con n} {x y : Fin n} → (X (suc x) , X (suc y)) ∈ WkCon Γ → (X x , X y) ∈ Γ
  suc∈WkCon→∈ {Γ = Γ ▹ (X i , X j)} here = here
  suc∈WkCon→∈ {Γ = Γ ▹ (X i , X j)} (drop k) = drop (suc∈WkCon→∈ k)

------------------------------------------------------------------------
-- The restriction of WkNormTm⁻¹ in pasting scheme is injective

WkNormTm⁻¹-injective-in-PS : {n : ℕ} {Γ : Con (suc n)} {A B : Ty (suc n)} (ps : PS Γ (A , X (# 0))) {t u : NormTm (WkCon Γ ▹ (X (# 1) , X (# 0))) (WkTy A , WkTy B)} → WkNormTm⁻¹ t ≡ WkNormTm⁻¹ u → t ≡ u
WkNormTm⁻¹-injective-in-PS {A = .(X (# 0))} {B = X zero} start {norm-id} {norm-id} eq = refl
WkNormTm⁻¹-injective-in-PS {A = .(X (# 0))} {B = X zero} start {_} {u ▸ drop ()} _
WkNormTm⁻¹-injective-in-PS {A = .(X (# 0))} {B = X zero} start {t ▸ drop ()} {_} _
WkNormTm⁻¹-injective-in-PS {A = X _} {B = X _} (ext ps) {norm-id} {norm-id} _ = refl
WkNormTm⁻¹-injective-in-PS {A = _} {B = X .(fromℕ< (s≤s (s≤s ≤-refl)))} (ext ps) {norm-id} {_▸_ {B = X zero} u y} eq = ⊥-elim (no-loop-in-PSCon (ext (ext ps) ) {eq = cong (λ x → X x) (≤-antisym (Arr-of-NormTm-in-PSCon-are-forward (ext (ext ps)) u) (Arr-in-PSCon-are-forward (ext (ext ps)) y))} y)
WkNormTm⁻¹-injective-in-PS {A = _} {B = X .(fromℕ< (s≤s (s≤s ≤-refl)))} (ext ps) {_▸_ {B = X zero} t x} {norm-id} eq = ⊥-elim (no-loop-in-PSCon (ext (ext ps) ) {eq = cong (λ x → X x) (≤-antisym (Arr-of-NormTm-in-PSCon-are-forward (ext (ext ps)) t) (Arr-in-PSCon-are-forward (ext (ext ps)) x))} x)
WkNormTm⁻¹-injective-in-PS {B = X j} (ext ps) {_▸_ {B = X zero} t x} {_} _ = contradiction (Arr-in-PSCon-are-forward (ext (ext ps)) x) (<⇒≱ (s≤s z≤n))
WkNormTm⁻¹-injective-in-PS {B = X j} (ext ps) {_} {_▸_ {B = X zero} u y} eq = contradiction (Arr-in-PSCon-are-forward (ext (ext ps)) y) (<⇒≱ (s≤s z≤n))
WkNormTm⁻¹-injective-in-PS {B = X j} (ext ps) {_▸_ {B = X (suc k)} t x} {_▸_ {B = X (suc l)} u y} eq = aux (form-of-arrow-in-PSCon (ext (ext ps)) x) (form-of-arrow-in-PSCon (ext (ext ps)) y)
  where
  aux : (eqk : inject₁ (suc k) ≡ suc (suc j)) (eqlm : inject₁ (suc l) ≡ suc (suc j)) → (t ▸ x) ≡ (u ▸ y)
  aux eqk eql = aux1 (inject₁-injective (trans (suc-injective eqk) (sym (suc-injective eql))))
    where
    aux1 : (eqlk : k ≡ l) → t ▸ x ≡ u ▸ y
    aux1 refl = aux2 (no-repetition-in-PSCon (ext (ext ps)) x y)
      where
      aux2 : (eq : x ≡ y) → t ▸ x ≡ u ▸ y
      aux2 refl = cong (_▸ x) (WkNormTm⁻¹-injective-in-PS (ext ps) (▸-injectiveˡ eq))
