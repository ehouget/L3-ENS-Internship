------------------------------------------------------------------------
-- Pasting scheme for cartesian categories
--
-- Pasting scheme
------------------------------------------------------------------------

module PS.Base where

open import Ty
open import Con
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin
open import Data.Fin.Properties
open import Data.Product renaming (_×_ to _∧_)

------------------------------------------------------------------------
-- Inductive definition of cartesian pasting scheme

data PS : {n : ℕ} (Γ : Con n) (A : Arr n) → Set where
  ps-term  : {n : ℕ} {A : Ty n} → LinearTy A → PS ε (A , 𝟙)
  ps-proj  : {n : ℕ} {A : Ty n} (k : Fin n) → LinearTy A → A ► k → PS ε (A , X k)
  ps-ext   : {n : ℕ} {Γ : Con n} {A B : Ty n} → PS Γ (A , B) → PS (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (# 0))
  ps-const : {n : ℕ} {Γ : Con n} {A B : Ty n} → PS Γ (A , B) → PS (WkCon Γ ▹ (𝟙 , X (# 0))) (WkTy A , X (# 0))
  ps-pair  : {n : ℕ} {Γ : Con n} {A B C : Ty n} → PS Γ (A , B) → PS Γ (A , C) → PS Γ (A , B × C)
  ps-weak  : {n : ℕ} {Γ : Con n} {A B : Ty n} {k : Fin n} → PS Γ (A , X k) → PS {n = suc n} (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc k))

------------------------------------------------------------------------
-- ps-weak⁻¹

-- ps-weak⁻¹ : {n : ℕ} {Γ : Con n} {A B : Ty n} {k : Fin n} (ps : PS {n = suc n} (WkCon Γ ▹ (WkTy B , X (# 0))) (WkTy A , X (suc k))) → PS Γ (A , X k)

------------------------------------------------------------------------
-- Examples of cartesian pasting scheme

PS⊢X⇒X : PS {n = 1} ε (X (# 0) , X (# 0))
PS⊢X⇒X = ps-proj zero point (►-here refl)

PSX⇒Y⊢X⇒Y : PS {n = 2} (ε ▹ (X (# 1) , X (# 0))) (X (# 1) , X (# 0))
PSX⇒Y⊢X⇒Y = ps-ext (ps-proj zero point (►-here refl))

PSX⇒Y,Y⇒Z⊢X⇒Z : PS {n = 3} (ε ▹ (X (# 2) , X (# 1)) ▹ (X (# 1) , X (# 0))) (X (# 2) , X (# 0))
PSX⇒Y,Y⇒Z⊢X⇒Z = ps-ext (ps-ext (ps-proj zero point (►-here refl)))

PS⊢X⇒𝟙 : PS {n = 1} ε (X (# 0) , 𝟙)
PS⊢X⇒𝟙 = ps-term point

PSX⇒Y,X⇒Z⊢X⇒Y×Z : PS {n = 3}  (ε ▹ (X (# 2) , X (# 1)) ▹ (X (# 2) , X (# 0))) (X (# 2) , X (# 1) × X (# 0))
PSX⇒Y,X⇒Z⊢X⇒Y×Z = ps-pair (ps-weak (ps-ext (ps-proj zero point (►-here refl)))) (ps-ext (ps-weak (ps-proj zero point (►-here refl))))

PS⊢X×Y⇒X : PS {n = 2} ε (X (# 0) × X (# 1) , X (# 0))
PS⊢X×Y⇒X = ps-proj zero (right point) (►-left (►-here refl))

PS⊢X×Y⇒Y : PS {n = 2} ε ((X (# 0) × X (# 1)) , X (# 1))
PS⊢X×Y⇒Y = ps-proj (suc zero) (right point) (►-right (►-here refl))

------------------------------------------------------------------------
-- Other examples of cartesian pasting scheme

PSA⇒B,A⇒D,B⇒C,D⇒E⊢A⇒C×E : PS {n = 5} (ε ▹ (X (# 4) , X (# 3)) ▹ (X (# 3) , X (# 2)) ▹ (X (# 4) , X (# 1)) ▹ (X (# 1) , X (# 0))) (X (# 4) , X (# 2) × X (# 0))
PSA⇒B,A⇒D,B⇒C,D⇒E⊢A⇒C×E = ps-pair (ps-weak (ps-weak (ps-ext (ps-ext (ps-proj zero point (►-here refl)))))) (ps-ext (ps-ext (ps-weak (ps-weak (ps-proj zero point (►-here refl))))))

PSX×Y⇒Z,X×Z⇒W⊢X×Y⇒W : PS {n = 4} (ε ▹ (X (# 3) × X (# 2), X (# 1)) ▹ (X (# 3) × X (# 1), X (# 0))) (X (# 3) × X (# 2) , X (# 0))
PSX×Y⇒Z,X×Z⇒W⊢X×Y⇒W = ps-ext (ps-pair (ps-weak (ps-proj (suc zero) (left point) (►-left (►-here refl)))) (ps-ext (ps-pair (ps-proj (suc zero) (left point) (►-left (►-here refl))) (ps-proj zero (left point) (►-right (►-here refl))))))

------------------------------------------------------------------------
-- Examples of diagram that are not cartesian pasting scheme

-- not a pasting scheme because it's the weakening of a pasting scheme
-- PSX⇒1⊢X⇒1 : PS {n = 1} (ε ▹ (X (# 0) , 𝟙)) (X (# 0) , 𝟙)

-- PS⊢X×Y⇒X×Y : PS {n = 2} ε ((X (# 1) × X (# 0)) , X (# 1) × X (# 0))

-- PS⊢X×Y×Z⇒X : PS {n = 3} {!!} {!X ? × X ? × X ? , X ?!}
-- PS⊢X×Y×Z⇒X = pair fst fst

-- PSA⇒B,B⇒C,B⇒D⊢A⇒C×D : PS {n = 4} (ε ▹ (X (# 3) , X (# 2)) ▹ (X (# 2) , X (# 1)) ▹ (X (# 2) , X (# 0))) (X (# 3) , X (# 1) × X (# 0))

-- not pasting scheme because it's the weakening of a pasting scheme
-- PSX⇒Y,X⇒Z⊢X⇒Y : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) , X (# 1))
-- PSX⇒Y,X⇒Z⊢X⇒Z : PS {n = 3} (ε ▹ (X (# 0) , X (# 1)) ▹ (X (# 0) , X (# 2))) (X (# 0) , X (# 2))

-- PS⊢𝟙⇒1 : PS {n = 0} ε (𝟙 , 𝟙)
-- PS⊢𝟙⇒1 = ps-term
