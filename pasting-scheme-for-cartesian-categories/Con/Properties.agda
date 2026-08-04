------------------------------------------------------------------------
-- Pasting scheme for cartesian categories
--
-- Properties related to Context
------------------------------------------------------------------------

module Con.Properties where

open import Con.Base
open import Ty
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin
open import Data.Fin.Properties
open import Data.Product renaming (_×_ to _∧_)
open import Data.Product.Properties

------------------------------------------------------------------------
-- Context constructors injectivity

▹-injectiveˡ : {n : ℕ} {Γ Γ' : Con n} {A A' : Arr n} →  Γ ▹ A ≡ Γ' ▹ A' → Γ ≡ Γ'
▹-injectiveˡ refl = refl

▹-injectiveʳ : {n : ℕ} {Γ Γ' : Con n} {A A' : Arr n} →  Γ ▹ A ≡ Γ' ▹ A' → A ≡ A'
▹-injectiveʳ refl = refl

------------------------------------------------------------------------
-- Context weakening injectivity

WkCon-injective : {n : ℕ} {Γ Γ' : Con n} → WkCon Γ ≡ WkCon Γ' → Γ ≡ Γ'
WkCon-injective {Γ = ε} {Γ' = ε} eq = refl
WkCon-injective {Γ = Γ ▹ A} {Γ' = Γ' ▹ A₁} eq = cong₂ _▹_ (WkCon-injective (▹-injectiveˡ eq)) (WkArr-injective (▹-injectiveʳ eq))

------------------------------------------------------------------------
-- Presence constuctors injectivity

∈-drop-injective : {n : ℕ} {Γ : Con n} {A B : Arr n} {k l : A ∈ Γ}
               → ∈-drop {B = B} k ≡ ∈-drop l → k ≡ l
∈-drop-injective refl = refl

------------------------------------------------------------------------
-- Context weakening injectivity

Wk∈-injective : {n : ℕ} {Γ : Con n} {A B : Ty n} {k l : (A , B) ∈ Γ}
              → Wk∈ k ≡ Wk∈ l → k ≡ l
Wk∈-injective {k = ∈-here refl} {l = ∈-here refl} _  = refl
Wk∈-injective {k = ∈-drop k} {∈-here refl} ()
Wk∈-injective {k = ∈-drop k}    {l = ∈-drop l}    eq = cong ∈-drop (Wk∈-injective (∈-drop-injective eq))

Wk∈⁻¹-injective : {n : ℕ} {Γ : Con n} {A B : Ty n} {k l : (WkTy A , WkTy B) ∈ (WkCon Γ)}
                → Wk∈⁻¹ k ≡ Wk∈⁻¹ l → k ≡ l
Wk∈⁻¹-injective {Γ = Γ ▹ (A , B)} {C} {D} {k = ∈-here x} {l = ∈-here y} eq = cong ∈-here (Wk∈⁻¹-injective-lem (WkTy-injective (,-injectiveˡ x)) (WkTy-injective (,-injectiveʳ y)) x y refl refl)
  where
  Wk∈⁻¹-injective-lem : C ≡ A → D ≡ B
                      → (x' y' : (WkTy C , WkTy D) ≡ (WkTy A , WkTy B))
                      → (eqx : x' ≡ x) → (eqy : y' ≡ y)
                      → x ≡ y
  Wk∈⁻¹-injective-lem refl refl refl refl refl refl = refl
Wk∈⁻¹-injective {Γ = Γ ▹ A} {k = ∈-drop k} {l = ∈-drop l} eq = cong ∈-drop (Wk∈⁻¹-injective (∈-drop-injective eq))

------------------------------------------------------------------------
-- Arrow in weak context

∈WkCon→∃Wk∈WkCon : {n : ℕ} {Γ : Con n} {A : Arr (suc n)}
                 → A ∈ WkCon Γ → ∃[ A' ] (A ≡ WkArr A')
∈WkCon→∃Wk∈WkCon {n} {Γ ▹ B} {A} k = lem-∈WkCon→∃Wk∈WkCon refl k
  where
  lem-∈WkCon→∃Wk∈WkCon : {Γ' : Con (suc n)} (eqΓ : Γ' ≡ WkCon (Γ ▹ B)) (k' : A ∈ Γ')
                       → ∃[ A' ] (A ≡ WkArr A')
  lem-∈WkCon→∃Wk∈WkCon refl (∈-here refl) = B , refl
  lem-∈WkCon→∃Wk∈WkCon refl (∈-drop k') = ∈WkCon→∃Wk∈WkCon k'

∈WkCon→∃WkSrc∈WkCon : {n : ℕ} {Γ : Con n} {A B : Ty (suc n)}
                 → (A , B) ∈ WkCon Γ → ∃[ A' ] (A ≡ WkTy A')
∈WkCon→∃WkSrc∈WkCon k = proj₁ (proj₁ (∈WkCon→∃Wk∈WkCon k)) , ,-injectiveˡ (proj₂ (∈WkCon→∃Wk∈WkCon k))

------------------------------------------------------------------------
-- Properties about X₀ in weak context

no-0-in-WkCon : {n : ℕ} {Γ : Con n} {A : Ty (suc n)} → ¬((A , X (# 0)) ∈ WkCon Γ)
no-0-in-WkCon {Γ = Γ ▹ (_ , X _)} (∈-drop k) = no-0-in-WkCon k
no-0-in-WkCon {Γ = Γ ▹ (_ , 𝟙)} (∈-drop k) = no-0-in-WkCon k
no-0-in-WkCon {Γ = Γ ▹ (_ , _ × _)} (∈-drop k) = no-0-in-WkCon k

no-0-producer-in-WkCon : {n : ℕ} {Γ : Con n} {A B : Ty (suc n)} → ¬((A , B) ∈ WkCon Γ ∧ B ► zero)
no-0-producer-in-WkCon {Γ = Γ ▹ (fst₁ , X x)} (∈-here refl , ►-here ())
no-0-producer-in-WkCon {Γ = Γ ▹ (_ , 𝟙)} (∈-here refl , ())
no-0-producer-in-WkCon {Γ = Γ ▹ (_ , X _)} (∈-drop k , x) = no-0-producer-in-WkCon (k , x)
no-0-producer-in-WkCon {Γ = Γ ▹ (_ , 𝟙)} (∈-drop k , x) = no-0-producer-in-WkCon (k , x)
no-0-producer-in-WkCon {Γ = Γ ▹ (_ , _ × _)} (∈-here refl , x) = no-0-in-WkTy x
no-0-producer-in-WkCon {Γ = Γ ▹ (_ , _ × _)} (∈-drop k , x) = no-0-producer-in-WkCon (k , x)
