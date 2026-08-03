------------------------------------------------------------------------
-- Pasting scheme for cartesian categories
--
-- Properties about pasting scheme
------------------------------------------------------------------------

module PS.Properties where

open import Ty
open import Con
open import PS.Base
open import Relation.Binary.PropositionalEquality
open import Data.Empty public
open import Data.Nat
open import Data.Fin
open import Data.Fin.Properties
open import Data.Product renaming (_×_ to _∧_)


------------------------------------------------------------------------
-- Pasting schemes are defined to have a linear source

ps-src-are-linear : {n : ℕ} {Γ : Con n} {A B : Ty n} (ps : PS Γ (A , B)) → LinearTy A
ps-src-are-linear (ps-term pred) = pred
ps-src-are-linear (ps-proj k pred x) = pred
ps-src-are-linear (ps-ext ps) = weak (ps-src-are-linear ps)
ps-src-are-linear (ps-const ps) = weak (ps-src-are-linear ps)
ps-src-are-linear (ps-pair ps₁ ps₂) = ps-src-are-linear ps₁
ps-src-are-linear (ps-weak ps) = weak (ps-src-are-linear ps)


------------------------------------------------------------------------
-- all morphisms in the context of a pasting scheme has a simple typed target

ps-con-tgt-are-simple : {n : ℕ} {Γ : Con n} {A : Arr n} {B C : Ty n} (ps : PS Γ A) → (k : (B , C) ∈ Γ)  → ∃[ l ] (C ≡ X l)
ps-con-tgt-are-simple (ps-ext ps) (∈-here refl) = zero , refl
ps-con-tgt-are-simple {B = B} {C = C} (ps-ext ps) (∈-drop k) = lem-ps-con-tgt-are-simple (∈WkCon→∃Wk∈WkCon k)
  where
  lem-ps-con-tgt-are-simple : (∃[ A' ] ((B , C) ≡ WkArr A')) → ∃[ l ] (C ≡ X l)
  lem-ps-con-tgt-are-simple ((src , tgt) , refl) = suc (proj₁ (ps-con-tgt-are-simple ps (Wk∈⁻¹ k))) , cong WkTy (proj₂ (ps-con-tgt-are-simple ps (Wk∈⁻¹ k)))
ps-con-tgt-are-simple (ps-const ps) (∈-here refl) = zero , refl
ps-con-tgt-are-simple {B = B} {C = C} (ps-const ps) (∈-drop k) = lem-ps-con-tgt-are-simple (∈WkCon→∃Wk∈WkCon k)
  where
  lem-ps-con-tgt-are-simple : (∃[ A' ] ((B , C) ≡ WkArr A')) → ∃[ l ] (C ≡ X l)
  lem-ps-con-tgt-are-simple ((src , tgt) , refl) = suc (proj₁ (ps-con-tgt-are-simple ps (Wk∈⁻¹ k))) , cong WkTy (proj₂ (ps-con-tgt-are-simple ps (Wk∈⁻¹ k)))
ps-con-tgt-are-simple (ps-pair ps₁ ps₂) k = ps-con-tgt-are-simple ps₁ k
ps-con-tgt-are-simple (ps-weak ps) (∈-here refl) = zero , refl
ps-con-tgt-are-simple {B = B} {C = C} (ps-weak ps) (∈-drop k) = lem-ps-con-tgt-are-simple (∈WkCon→∃Wk∈WkCon k)
  where
  lem-ps-con-tgt-are-simple : (∃[ A' ] ((B , C) ≡ WkArr A')) → ∃[ l ] (C ≡ X l)
  lem-ps-con-tgt-are-simple ((src , tgt) , refl) = suc (proj₁ (ps-con-tgt-are-simple ps (Wk∈⁻¹ k))) , cong WkTy (proj₂ (ps-con-tgt-are-simple ps (Wk∈⁻¹ k)))


------------------------------------------------------------------------
-- Pasting schemes target can't be voided

-- ps-tgt-not-term : {n : ℕ} {Γ : Con n} {A : Ty n} → ¬(PS Γ (A , 𝟙))
-- ps-tgt-not-term ()

------------------------------------------------------------------------
--

producer-unicity : {n : ℕ} {Γ : Con n} {A B C : Ty n} {k : Fin n} {ps : PS Γ (A , B)} → ¬(A ► k ∧ (C , X k) ∈ Γ)
producer-unicity {k = zero}  {ps = ps-ext ps} (x , l) = contradiction x no-0-in-WkTy
producer-unicity {k = zero}  {ps = ps-const ps} (x , l) = contradiction x no-0-in-WkTy
producer-unicity {k = zero}  {ps = ps-weak ps} (x , l) = contradiction x no-0-in-WkTy
producer-unicity {C = C} {k = suc k} {ps = ps-ext ps} (x , ∈-drop l) = lem-producer-unicity (∈WkCon→∃WkSrc∈WkCon l)
  where
  lem-producer-unicity : ∃[ C' ] (C ≡ WkTy C') → ⊥
  lem-producer-unicity (src , refl) = producer-unicity {ps = ps} (Wk►⁻¹ x , Wk∈⁻¹ l)
producer-unicity {C = C} {k = suc k} {ps = ps-const ps} (x , ∈-drop l) = lem-producer-unicity (∈WkCon→∃WkSrc∈WkCon l)
  where
  lem-producer-unicity : ∃[ C' ] (C ≡ WkTy C') → ⊥
  lem-producer-unicity (src , refl) = producer-unicity {ps = ps} (Wk►⁻¹ x , Wk∈⁻¹ l)
producer-unicity {C = C} {k = suc k} {ps = ps-weak ps} (x , ∈-drop l) = lem-producer-unicity (∈WkCon→∃WkSrc∈WkCon l)
  where
  lem-producer-unicity : ∃[ C' ] (C ≡ WkTy C') → ⊥
  lem-producer-unicity (src , refl) = producer-unicity {ps = ps} (Wk►⁻¹ x , Wk∈⁻¹ l)
producer-unicity {ps = ps-pair ps₁ ps₂} (x , l) = producer-unicity {ps = ps₁} (x , l)

------------------------------------------------------------------------
--

no-term-tgt-in-PSCon : {n : ℕ} {Γ : Con n} {A : Arr n} {B : Ty n} (ps : PS Γ A) → ¬((B , 𝟙) ∈ Γ)
no-term-tgt-in-PSCon {B = B} (ps-ext ps) (∈-drop x) = lem-no-term-tgt-in-PSCon (∈WkCon→∃WkSrc∈WkCon x)
  where
  lem-no-term-tgt-in-PSCon : ∃[ C' ] (B ≡ WkTy C') → ⊥
  lem-no-term-tgt-in-PSCon (src , refl) = no-term-tgt-in-PSCon ps (Wk∈⁻¹ x)
no-term-tgt-in-PSCon {B = B} (ps-const ps) (∈-drop x) = lem-no-term-tgt-in-PSCon (∈WkCon→∃WkSrc∈WkCon x)
  where
  lem-no-term-tgt-in-PSCon : ∃[ C' ] (B ≡ WkTy C') → ⊥
  lem-no-term-tgt-in-PSCon (src , refl) = no-term-tgt-in-PSCon ps (Wk∈⁻¹ x)
no-term-tgt-in-PSCon (ps-pair ps₁ ps₂) x = no-term-tgt-in-PSCon ps₁ x
no-term-tgt-in-PSCon {B = B} (ps-weak ps) (∈-drop x) = lem-no-term-tgt-in-PSCon (∈WkCon→∃WkSrc∈WkCon x)
  where
  lem-no-term-tgt-in-PSCon : ∃[ C' ] (B ≡ WkTy C') → ⊥
  lem-no-term-tgt-in-PSCon (src , refl) = no-term-tgt-in-PSCon ps (Wk∈⁻¹ x)

------------------------------------------------------------------------
--

no-pair-tgt-in-PSCon : {n : ℕ} {Γ : Con n} {A : Arr n} {B C D : Ty n} (ps : PS Γ A) → ¬((B , C × D) ∈ Γ)
no-pair-tgt-in-PSCon {B = B} {C = C} {D = D} (ps-ext ps) (∈-drop x) = lem-no-pair-tgt-in-PSCon (∈WkCon→∃Wk∈WkCon x)
  where
  lem-no-pair-tgt-in-PSCon : ∃[ A' ] ((B , C × D) ≡ WkArr A') → ⊥
  lem-no-pair-tgt-in-PSCon ((src , tgt × tgt') , refl) = no-pair-tgt-in-PSCon ps (Wk∈⁻¹ x)
no-pair-tgt-in-PSCon {B = B} {C = C} {D = D} (ps-const ps) (∈-drop x) = lem-no-pair-tgt-in-PSCon (∈WkCon→∃Wk∈WkCon x)
  where
  lem-no-pair-tgt-in-PSCon : ∃[ A' ] ((B , C × D) ≡ WkArr A') → ⊥
  lem-no-pair-tgt-in-PSCon ((src , tgt × tgt') , refl) = no-pair-tgt-in-PSCon ps (Wk∈⁻¹ x)
no-pair-tgt-in-PSCon (ps-pair ps₁ ps₂) x = no-pair-tgt-in-PSCon ps₁ x
no-pair-tgt-in-PSCon {B = B} {C = C} {D = D} (ps-weak ps) (∈-drop x) = lem-no-pair-tgt-in-PSCon (∈WkCon→∃Wk∈WkCon x)
  where
  lem-no-pair-tgt-in-PSCon : ∃[ A' ] ((B , C × D) ≡ WkArr A') → ⊥
  lem-no-pair-tgt-in-PSCon ((src , tgt × tgt') , refl) = no-pair-tgt-in-PSCon ps (Wk∈⁻¹ x)

------------------------------------------------------------------------
--

no-src-repetition-in-PSCon : {n : ℕ} {Γ : Con n} {A : Arr n} {B C : Ty n} {k : Fin n} (ps : PS Γ A) (x : (B , X k) ∈ Γ) (y : (C , X k) ∈ Γ) → B ≡ C
no-src-repetition-in-PSCon {k = zero} (ps-ext ps) (∈-here refl) (∈-here refl) = refl
no-src-repetition-in-PSCon {k = zero} (ps-ext ps) (∈-drop x) _ = contradiction x no-0-in-WkCon
no-src-repetition-in-PSCon {k = zero} (ps-ext ps) _ (∈-drop y) = contradiction y no-0-in-WkCon
no-src-repetition-in-PSCon {k = zero} (ps-const ps) (∈-here refl) (∈-here refl) = refl
no-src-repetition-in-PSCon {k = zero} (ps-const ps) (∈-drop x) _ = contradiction x no-0-in-WkCon
no-src-repetition-in-PSCon {k = zero} (ps-const ps) _ (∈-drop y) = contradiction y no-0-in-WkCon
no-src-repetition-in-PSCon {k = zero} (ps-weak ps) (∈-here refl) (∈-here refl) = refl
no-src-repetition-in-PSCon {k = zero} (ps-weak ps) (∈-drop x) _ = contradiction x no-0-in-WkCon
no-src-repetition-in-PSCon {k = zero} (ps-weak ps) _ (∈-drop y) = contradiction y no-0-in-WkCon
no-src-repetition-in-PSCon {B = B} {C = C} {k = suc k} (ps-ext ps) (∈-drop x) (∈-drop y) = lem-no-src-repetition-in-PSCon (∈WkCon→∃WkSrc∈WkCon x) (∈WkCon→∃WkSrc∈WkCon y)
  where
  lem-no-src-repetition-in-PSCon : (∃[ B' ] (B ≡ WkTy B')) → (∃[ C' ] (C ≡ WkTy C')) → B ≡ C
  lem-no-src-repetition-in-PSCon (B' , refl) (C' , refl) = cong WkTy (no-src-repetition-in-PSCon ps (Wk∈⁻¹ x) (Wk∈⁻¹ y))
no-src-repetition-in-PSCon {B = B} {C = C} {k = suc k} (ps-const ps) (∈-drop x) (∈-drop y) = lem-no-src-repetition-in-PSCon (∈WkCon→∃WkSrc∈WkCon x) (∈WkCon→∃WkSrc∈WkCon y)
  where
  lem-no-src-repetition-in-PSCon : (∃[ B' ] (B ≡ WkTy B')) → (∃[ C' ] (C ≡ WkTy C')) → B ≡ C
  lem-no-src-repetition-in-PSCon (B' , refl) (C' , refl) = cong WkTy (no-src-repetition-in-PSCon ps (Wk∈⁻¹ x) (Wk∈⁻¹ y))
no-src-repetition-in-PSCon {B = B} {C = C} {k = suc k} (ps-weak ps) (∈-drop x) (∈-drop y) = lem-no-src-repetition-in-PSCon (∈WkCon→∃WkSrc∈WkCon x) (∈WkCon→∃WkSrc∈WkCon y)
  where
  lem-no-src-repetition-in-PSCon : (∃[ B' ] (B ≡ WkTy B')) → (∃[ C' ] (C ≡ WkTy C')) → B ≡ C
  lem-no-src-repetition-in-PSCon (B' , refl) (C' , refl) = cong WkTy (no-src-repetition-in-PSCon ps (Wk∈⁻¹ x) (Wk∈⁻¹ y))
no-src-repetition-in-PSCon (ps-pair ps₁ ps₂) x y = no-src-repetition-in-PSCon ps₁ x y

no-repetition-in-PSCon : {n : ℕ} {Γ : Con n} {A B : Arr n} (ps : PS Γ A) (x y : B ∈ Γ) → x ≡ y
no-repetition-in-PSCon {B = .(WkTy _) , X zero} (ps-ext ps) (∈-here refl) (∈-here refl) = refl
no-repetition-in-PSCon {B = src , X zero} (ps-ext ps) (∈-drop x) _ = contradiction x no-0-in-WkCon
no-repetition-in-PSCon {B = src , X zero} (ps-ext ps) _ (∈-drop y) = contradiction y no-0-in-WkCon
no-repetition-in-PSCon {B = .(WkTy _) , X zero} (ps-const ps) (∈-here refl) (∈-here refl) = refl
no-repetition-in-PSCon {B = src , X zero} (ps-const ps) (∈-drop x) _ = contradiction x no-0-in-WkCon
no-repetition-in-PSCon {B = src , X zero} (ps-const ps) _ (∈-drop y) = contradiction y no-0-in-WkCon
no-repetition-in-PSCon {B = .(WkTy _) , X zero} (ps-weak ps) (∈-here refl) (∈-here refl) = refl
no-repetition-in-PSCon {B = src , X zero} (ps-weak ps) (∈-drop x) _ = contradiction x no-0-in-WkCon
no-repetition-in-PSCon {B = src , X zero} (ps-weak ps) _ (∈-drop y) = contradiction y no-0-in-WkCon
no-repetition-in-PSCon {B = src , X (suc k)} (ps-ext ps) (∈-drop x) (∈-drop y) = lem-no-repetition-in-PSCon (∈WkCon→∃WkSrc∈WkCon x)
  where
  lem-no-repetition-in-PSCon : (∃[ A' ] (src ≡ WkTy A')) → ∈-drop x ≡ ∈-drop y
  lem-no-repetition-in-PSCon (_ , refl) = cong ∈-drop (Wk∈⁻¹-injective (no-repetition-in-PSCon ps (Wk∈⁻¹ x) (Wk∈⁻¹ y)))
no-repetition-in-PSCon {B = src , X (suc k)} (ps-const ps) (∈-drop x) (∈-drop y) = lem-no-repetition-in-PSCon (∈WkCon→∃WkSrc∈WkCon x)
  where
  lem-no-repetition-in-PSCon : (∃[ A' ] (src ≡ WkTy A')) → ∈-drop x ≡ ∈-drop y
  lem-no-repetition-in-PSCon (_ , refl) = cong ∈-drop (Wk∈⁻¹-injective (no-repetition-in-PSCon ps (Wk∈⁻¹ x) (Wk∈⁻¹ y)))
no-repetition-in-PSCon {B = src , X (suc k)} (ps-weak ps) (∈-drop x) (∈-drop y) = lem-no-repetition-in-PSCon (∈WkCon→∃WkSrc∈WkCon x)
  where
  lem-no-repetition-in-PSCon : (∃[ A' ] (src ≡ WkTy A')) → ∈-drop x ≡ ∈-drop y
  lem-no-repetition-in-PSCon (_ , refl) = cong ∈-drop (Wk∈⁻¹-injective (no-repetition-in-PSCon ps (Wk∈⁻¹ x) (Wk∈⁻¹ y)))
no-repetition-in-PSCon {B = src , 𝟙} ps x y = contradiction x (no-term-tgt-in-PSCon ps)
no-repetition-in-PSCon {B = src , _ × _} ps x y = contradiction x (no-pair-tgt-in-PSCon ps)
no-repetition-in-PSCon (ps-pair ps₁ ps₂) x y = no-repetition-in-PSCon ps₁ x y
