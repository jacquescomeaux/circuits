{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Category.Monoidal.Instance.Posets {c ℓ₁ ℓ₂ : Level} where

open import Categories.Category.Instance.Posets using (Posets)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Morphism (Posets c ℓ₁ ℓ₂) using (_≅_)
open import Data.Product using (_,_; map; proj₁; proj₂; assocʳ′; assocˡ′)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-poset)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary using (Poset)
open import Relation.Binary.Morphism.Bundles using (PosetHomomorphism; mkPosetHomo)

open Poset using (module Eq)
open PosetHomomorphism using (⟦_⟧; mono)

private

  ⊗ : Bifunctor (Posets c ℓ₁ ℓ₂) (Posets c ℓ₁ ℓ₂) (Posets c ℓ₁ ℓ₂)
  ⊗ = record
      { F₀ = λ (P , Q) → ×-poset P Q
      ; F₁ = λ (f , g) → mkPosetHomo _ _ (map ⟦ f ⟧ ⟦ g ⟧) (map (mono f) (mono g))
      ; identity = λ { {x , y} → Eq.refl x , Eq.refl y }
      ; homomorphism = λ { {_} {_} {e , f} → Eq.refl e , Eq.refl f }
      ; F-resp-≈ = λ (x , y) → x , y
      }

  unit : Poset c ℓ₁ ℓ₂
  unit = record
      { Carrier = ⊤
      ; _≈_ = λ _ _ → ⊤
      ; _≤_ = λ _ _ → ⊤
      ; isPartialOrder = _
      }

  unitorˡ : {X : Poset c ℓ₁ ℓ₂} → ×-poset unit X ≅ X
  unitorˡ {X} = record
      { from = mkPosetHomo _ _ proj₂ proj₂
      ; to = mkPosetHomo _ _ (tt ,_) (tt ,_)
      ; iso = record
          { isoˡ = tt , Eq.refl X
          ; isoʳ = Eq.refl X
          }
      }

  unitorʳ : {X : Poset c ℓ₁ ℓ₂} → ×-poset X unit ≅ X
  unitorʳ {X} = record
      { from = mkPosetHomo _ _ proj₁ proj₁
      ; to = mkPosetHomo _ _ (_, tt) (_, tt)
      ; iso = record
          { isoˡ = Eq.refl X , tt
          ; isoʳ = Eq.refl X
          }
      }

  associator : {X Y Z : Poset c ℓ₁ ℓ₂} → ×-poset (×-poset X Y) Z ≅ ×-poset X (×-poset Y Z)
  associator {X} {Y} {Z} = record
      { from = mkPosetHomo _ _ assocʳ′ assocʳ′
      ; to = mkPosetHomo _ _ assocˡ′ assocˡ′
      ; iso = record
          { isoˡ = (Eq.refl X , Eq.refl Y) , Eq.refl Z
          ; isoʳ = Eq.refl X , (Eq.refl Y , Eq.refl Z)
          }
      }

Posets-Monoidal : Monoidal (Posets c ℓ₁ ℓ₂)
Posets-Monoidal = record
    { ⊗ = ⊗
    ; unit = unit
    ; unitorˡ = unitorˡ
    ; unitorʳ = unitorʳ
    ; associator = associator
    ; unitorˡ-commute-from = λ {_ X} → Eq.refl X
    ; unitorˡ-commute-to = λ {_ Y} → tt , Eq.refl Y
    ; unitorʳ-commute-from = λ {_ X} → Eq.refl X
    ; unitorʳ-commute-to = λ {_ Y} → Eq.refl Y , tt
    ; assoc-commute-from = λ {_ A _ _ B _ _ C} → Eq.refl A , Eq.refl B , Eq.refl C
    ; assoc-commute-to = λ {_ A _ _ B _ _ C} → (Eq.refl A , Eq.refl B) , Eq.refl C
    ; triangle = λ {X Y} → Eq.refl X , Eq.refl Y
    ; pentagon = λ {W X Y Z} → Eq.refl W , Eq.refl X , Eq.refl Y , Eq.refl Z
    }
