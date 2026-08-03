------------------------------------------------------------------------
-- Pasting Schemes for cartesian categories
--
-- Normal Terms
------------------------------------------------------------------------

module NormTm.Base where

open import Ty
open import Con
open import Tm
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary public
open import Data.Nat
open import Data.Fin
open import Data.Product renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Normal terms

data NormTm {n : ℕ} (Γ : Con n) : Arr n → Set where
  norm-proj : {A : Ty n} {k : Fin n} → A ► k → NormTm Γ (A , X k)
  norm-comp : {A B C : Ty n} {k : Fin n} → NormTm Γ (A , B) → (B , C) ∈ Γ → C ► k → NormTm Γ (A , X k)
  norm-term : {A : Ty n} → NormTm Γ (A , 𝟙)
  norm-pair : {X A B : Ty n} → NormTm Γ (X , A) → NormTm Γ (X , B) → NormTm Γ (X , A × B)

------------------------------------------------------------------------
-- Normal terms weakening Ty

WkNormTmTy : {n : ℕ} {Γ : Con n} {A B : Ty n} (f : NormTm Γ (A , B)) → NormTm (WkCon Γ) (WkTy A , WkTy B)
WkNormTmTy (norm-proj x) = norm-proj (Wk► x)
WkNormTmTy (norm-comp f k x) = norm-comp (WkNormTmTy f) (Wk∈ k) (Wk► x)
WkNormTmTy norm-term = norm-term
WkNormTmTy (norm-pair f f') = norm-pair (WkNormTmTy f) (WkNormTmTy f')

postulate
  WkNormTmTy⁻¹ : {n : ℕ} {Γ : Con n} {A B : Ty n} (f : NormTm (WkCon Γ) (WkTy A , WkTy B)) → NormTm Γ (A , B)

------------------------------------------------------------------------
-- Normal Terms weakening context

WkNormTmCon : {n : ℕ} {Γ : Con n} {A B : Arr n} (f : NormTm Γ A) → NormTm (Γ ▹ B) A
WkNormTmCon (norm-proj x) = norm-proj x
WkNormTmCon (norm-comp f k x) = norm-comp (WkNormTmCon f) (∈-drop k) x
WkNormTmCon norm-term = norm-term
WkNormTmCon (norm-pair f f') = norm-pair (WkNormTmCon f) (WkNormTmCon f')

------------------------------------------------------------------------
-- Normal Terms weakening

mutual
  WkNormTm : {n : ℕ} {Γ : Con n} {A B : Ty n} {k : Fin n} (f : NormTm Γ (A , X k)) → NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc k))
  WkNormTm (norm-proj x) = norm-proj (Wk► x)
  WkNormTm (norm-comp f k x) = norm-comp (WkNormTm-aux f) (∈-drop (Wk∈ k)) (Wk► x)

  WkNormTm-aux : {n : ℕ} {Γ : Con n} {A B C : Ty n} (f : NormTm Γ (A , B)) → NormTm (WkCon Γ ▹ (WkTy C , X (# 0))) (WkTy A , WkTy B)
  WkNormTm-aux (norm-proj x) = WkNormTm (norm-proj x)
  WkNormTm-aux (norm-comp f k y) = WkNormTm (norm-comp f k y)
  WkNormTm-aux norm-term = norm-term
  WkNormTm-aux (norm-pair f f') = norm-pair (WkNormTm-aux f) (WkNormTm-aux f')

postulate
  WkNormTm⁻¹ : {n : ℕ} {Γ : Con n} {A B : Ty n} {m : Fin n} (f : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc m))) → NormTm Γ (A , X m)

-- ------------------------------------------------------------------------
-- -- Normal Terms extension

extNormTm : {n : ℕ} {Γ : Con n} {A B : Ty n} (f : NormTm Γ (A , B)) → NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (# 0))
extNormTm (norm-proj x) = norm-comp (WkNormTm (norm-proj x)) (∈-here refl) (►-here refl)
extNormTm (norm-comp f k x) = norm-comp (WkNormTm (norm-comp f k x)) (∈-here refl) (►-here refl)
extNormTm norm-term = norm-comp norm-term (∈-here refl) (►-here refl)
extNormTm (norm-pair f f') = norm-comp (norm-pair (WkNormTm-aux f) (WkNormTm-aux f')) (∈-here refl) (►-here refl)

postulate
  extNormTm⁻¹ : {n : ℕ} {Γ : Con n} {A B : Ty n} (f : NormTm (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (# 0))) → NormTm Γ (A , B)

------------------------------------------------------------------------
-- Normal Terms merging

merge-NormTm : {n : ℕ} {Γ : Con n} {A B C : Ty n} → NormTm Γ (A , B) → NormTm Γ (B , C) → NormTm Γ (A , C)
merge-NormTm f (norm-proj (►-here refl)) = f
merge-NormTm (norm-pair f g) (norm-proj (►-left x)) = merge-NormTm f (norm-proj x)
merge-NormTm (norm-pair f g) (norm-proj (►-right x)) = merge-NormTm g (norm-proj x)
merge-NormTm f (norm-comp g k x) = norm-comp (merge-NormTm f g) k x
merge-NormTm f norm-term = norm-term
merge-NormTm f (norm-pair g h) = norm-pair (merge-NormTm f g) (merge-NormTm f h)

------------------------------------------------------------------------
-- Normal id term

WkNormTmLeft : {n : ℕ} {Γ : Con n} {A B C : Ty n} → NormTm Γ (A , C) → NormTm Γ (A × B , C)
WkNormTmLeft (norm-proj x) = norm-proj (►-left x)
WkNormTmLeft (norm-comp f k x) = norm-comp (WkNormTmLeft f) k x
WkNormTmLeft norm-term = norm-term
WkNormTmLeft (norm-pair f g) = norm-pair (WkNormTmLeft f) (WkNormTmLeft g)

WkNormTmRight : {n : ℕ} {Γ : Con n} {A B C : Ty n} → NormTm Γ (B , C) → NormTm Γ (A × B , C)
WkNormTmRight (norm-proj x) = norm-proj (►-right x)
WkNormTmRight (norm-comp f k x) = norm-comp (WkNormTmRight f) k x
WkNormTmRight norm-term = norm-term
WkNormTmRight (norm-pair f g) = norm-pair (WkNormTmRight f) (WkNormTmRight g)

norm-id : {n : ℕ} {Γ : Con n} {A : Ty n} → NormTm Γ (A , A)
norm-id {A = (X k)} = norm-proj (►-here refl)
norm-id {A = 𝟙} = norm-term
norm-id {A = (A × B)} = norm-pair (WkNormTmLeft norm-id) (WkNormTmRight norm-id)

------------------------------------------------------------------------
-- Normal fst and snd terms

norm-fst : {n : ℕ} {Γ : Con n} {A B : Ty n} → NormTm Γ (A × B , A)
norm-fst = WkNormTmLeft norm-id

norm-snd : {n : ℕ} {Γ : Con n} {A B : Ty n} → NormTm Γ (A × B , B)
norm-snd = (WkNormTmRight norm-id)

------------------------------------------------------------------------
-- Normal var term

postulate
  norm-var : {n : ℕ} {Γ : Con n} {A B : Ty n} → (A , B) ∈ Γ → NormTm Γ (A , B)

------------------------------------------------------------------------
-- Normalize

normalize : {n : ℕ} {Γ : Con n} {A : Arr n} → Tm Γ A → NormTm Γ A
normalize (var x) = norm-var x
normalize id = norm-id
normalize (f · g) = merge-NormTm (normalize f) (normalize g)
normalize term = norm-term
normalize (pair f g) = norm-pair (normalize f) (normalize g)
normalize fst = norm-fst
normalize snd = norm-snd

------------------------------------------------------------------------
-- Denormalize

norm-proj→Tm : {n : ℕ} {Γ : Con n} {A : Ty n} {k : Fin n} → A ► k → Tm Γ (A , X k)
norm-proj→Tm (►-here refl) = id
norm-proj→Tm (►-left x) = fst · norm-proj→Tm x
norm-proj→Tm (►-right x) = snd · norm-proj→Tm x

denormalize : {n : ℕ} {Γ : Con n} {A : Arr n} → NormTm Γ A → Tm Γ A
denormalize (norm-proj x) = norm-proj→Tm x
denormalize (norm-comp f k x) = denormalize f · ((var k) · norm-proj→Tm x)
denormalize norm-term = term
denormalize (norm-pair f g) = pair (denormalize f) (denormalize g)
