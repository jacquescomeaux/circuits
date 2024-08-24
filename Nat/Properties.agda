{-# OPTIONS --without-K --safe #-}
module Nat.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; #_; toℕ)
open import Data.Fin.Properties using (¬Fin0)
open import Data.Nat using (ℕ; s≤s)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Nat using (Nat; Coprod)
open import Categories.Diagram.Coequalizer Nat using (IsCoequalizer; Coequalizer)
open import Categories.Diagram.Pushout Nat using (Pushout)
open import Categories.Diagram.Pushout.Properties Nat using (Coproduct×Coequalizer⇒Pushout)
open import Categories.Object.Coproduct Nat using (Coproduct; IsCoproduct; IsCoproduct⇒Coproduct)

open import Coeq Nat using (coequalizer-on-coproduct)
open import FinMerge using (glue-iter; glue-unglue-once)
open import FinMerge.Properties using (lemma₂; merge-unmerge; unmerge-merge)
open import Util using (compare; less; equal; greater; _<_<_)

open Category Nat


makeZeroCoequalizer : {B : ℕ} {f g : 0 ⇒ B} → Coequalizer f g
makeZeroCoequalizer = record
    { arr = id
    ; isCoequalizer = record
        { equality = λ()
        ; coequalize = λ {_} {h} _ → h
        ; universal = λ _ → refl
        ; unique = λ h≈i∘id → Equiv.sym h≈i∘id
        }
    }

makeSimpleCoequalizer : {B : ℕ} {f g : 1 ⇒ B} → Coequalizer f g
makeSimpleCoequalizer {ℕ.zero} {f} = ⊥-elim (¬Fin0 (f (# 0)))
makeSimpleCoequalizer {ℕ.suc B} {f} {g} = record
    { arr = proj₂ (glue-iter f g id)
    ; isCoequalizer = record
        { equality = λ { Fin.zero → lemma₂ f g }
        ; coequalize = λ {_} {h} h∘f≈h∘g → h ∘ proj₂ (proj₂ (glue-unglue-once (compare (f (# 0)) (g (# 0)))))
        ; universal = λ { {C} {h} {eq} → univ {C} {h} {eq} }
        ; unique = λ { {C} {h} {i} {eq} h≈i∘m → uniq {C} {h} {i} {eq} h≈i∘m }
        }
    }
  where
    univ
        : {C : Obj} {h : ℕ.suc B ⇒ C} {eq : h ∘ f ≈ h ∘ g}
        → ∀ x
        → h x
        ≡ h ((proj₂ (proj₂ (glue-unglue-once (compare (f (# 0)) (g (# 0))))))
            (proj₂ (glue-iter f g id) x))
    univ {C} {h} {eq} x with compare (f ( # 0)) (g (# 0))
    ... | less (f0<g0 , s≤s g0≤n) =
            sym (merge-unmerge (f0<g0 , g0≤n) h (eq (# 0)))
    ... | equal f0≡g0 = refl
    ... | greater (g0<f0 , s≤s f0≤n) =
            sym (merge-unmerge (g0<f0 , f0≤n) h (sym (eq (# 0))))
    uniq
        : {C : Obj}
          {h : ℕ.suc B ⇒ C}
          {i : Fin (proj₁ (glue-iter f g id)) → Fin C}
          {eq : h ∘ f ≈ h ∘ g}
        → (h≈i∘m : h ≈ i ∘ proj₂ (glue-iter f g id))
        → ∀ x
        → i x ≡ h (proj₂ (proj₂ (glue-unglue-once (compare (f (# 0)) (g (# 0))))) x)
    uniq {C} {h} {i} {eq} h≈i∘m x with compare (f ( # 0)) (g (# 0))
    ... | less (f0<g0 , s≤s g0≤n) =
            let
              open ≡-Reasoning
              m = proj₁ (proj₂ (glue-unglue-once (less (f0<g0 , s≤s g0≤n))))
              u = proj₂ (proj₂ (glue-unglue-once (less (f0<g0 , s≤s g0≤n))))
            in
              begin
                i x         ≡⟨ cong i (sym (unmerge-merge (f0<g0 , g0≤n))) ⟩
                i (m (u x)) ≡⟨ sym (h≈i∘m (u x)) ⟩
                h (u x)     ∎
    ... | equal f0≡g0 = sym (h≈i∘m x)
    ... | greater (g0<f0 , s≤s f0≤n) =
            let
              open ≡-Reasoning
              m = proj₁ (proj₂ (glue-unglue-once (greater (g0<f0 , s≤s f0≤n))))
              u = proj₂ (proj₂ (glue-unglue-once (greater (g0<f0 , s≤s f0≤n))))
            in
              begin
                i x         ≡⟨ cong i (sym (unmerge-merge (g0<f0 , f0≤n))) ⟩
                i (m (u x)) ≡⟨ sym (h≈i∘m (u x)) ⟩
                h (u x)     ∎

split : {n : ℕ} → IsCoproduct {1} {n} {ℕ.suc n} (λ _ → Fin.zero) Fin.suc
split = record
    { [_,_] = λ
        { z _ Fin.zero → z Fin.zero
        ; _ s (Fin.suc x) → s x
        }
    ; inject₁ = λ { Fin.zero → refl }
    ; inject₂ = λ { _ → refl }
    ; unique = λ { h∘i₁≈f _ Fin.zero → (Equiv.sym h∘i₁≈f) Fin.zero
                 ; h∘i₁≈f h∘i₂≈g (Fin.suc x) → (Equiv.sym h∘i₂≈g) x }
    }

-- Coequalizers for Nat
Coeq : {A B : ℕ} (f g : A ⇒ B) → Coequalizer f g
Coeq {ℕ.zero} _ _ = makeZeroCoequalizer
Coeq {ℕ.suc A} f g = record
    { arr = Q₂.arr ∘ Q₁.arr
    ; isCoequalizer = coequalizer-on-coproduct
        split
        Q₁.isCoequalizer
        Q₂.isCoequalizer
    }
  where
    simpleCoeq : Coequalizer (λ _ → f (# 0)) (λ _ → g (# 0))
    simpleCoeq = makeSimpleCoequalizer
    module Q₁ = Coequalizer simpleCoeq
    recursiveCoeq : Coequalizer (Q₁.arr ∘ f ∘ Fin.suc) (Q₁.arr ∘ g ∘ Fin.suc)
    recursiveCoeq = Coeq _ _
    module Q₂ = Coequalizer recursiveCoeq

-- Pushouts for Nat
Push : {A B C : ℕ} (f : A ⇒ B) (g : A ⇒ C) → Pushout f g
Push {A} {B} {C} f g =
    Coproduct×Coequalizer⇒Pushout B+C (Coeq (B+C.i₁ ∘ f) (B+C.i₂ ∘ g))
  where
    B+C : Coproduct B C
    B+C = Coprod B C
    module B+C = Coproduct B+C
