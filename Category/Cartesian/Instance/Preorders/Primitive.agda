{-# OPTIONS --without-K --safe #-}

module Category.Cartesian.Instance.Preorders.Primitive where

open import Categories.Category.Cartesian using (Cartesian)
open import Level using (Level; suc; _⊔_)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Category.Instance.Preorder.Primitive.Preorders using (Preorders)
open import Preorder.Primitive using (Preorder; module Isomorphism)
open import Preorder.Primitive.MonotoneMap using (MonotoneMap; _≃_; module ≃)
open import Preorder.Primitive.Monoidal using (_×ₚ_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product using (proj₁; proj₂; <_,_>; _,_)


module _ (c ℓ : Level) where

  private module _ (A B : Preorder c ℓ) where

    π₁ : MonotoneMap (A ×ₚ B) A
    π₁ = record
        { map = proj₁
        ; mono = proj₁
        }

    π₂ : MonotoneMap (A ×ₚ B) B
    π₂ = record
        { map = proj₂
        ; mono = proj₂
        }

    pair
        : {C : Preorder c ℓ}
        → MonotoneMap C A
        → MonotoneMap C B
        → MonotoneMap C (A ×ₚ B)
    pair f g = let open MonotoneMap in record
        { map = < map f , map g >
        ; mono = < mono f , mono g >
        }

  ⊤ₚ : Preorder c ℓ
  ⊤ₚ = record
      { Carrier = ⊤
      ; _≲_ = λ _ _ → ⊤
      }

  Preorders-Cartesian : Cartesian (Preorders c ℓ)
  Preorders-Cartesian = record
      { terminal = record { ⊤ = ⊤ₚ }
      ; products = record
          { product = λ {A} {B} → record
              { A×B = A ×ₚ B
              ; π₁ = π₁ A B
              ; π₂ = π₂ A B
              ; ⟨_,_⟩ = pair A B
              ; project₁ = λ {h = h} → ≃.refl {x = h}
              ; project₂ = λ {i = i} → ≃.refl {x = i}
              ; unique = λ π₁∘j≃h π₂∘j≃i x → let open Isomorphism._≅_ in record
                    { from = to (π₁∘j≃h x) , to (π₂∘j≃i x)
                    ; to = from (π₁∘j≃h x) , from (π₂∘j≃i x)
                    }
              }
          }
      }

  Preorders-CC : CartesianCategory (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
  Preorders-CC = record { cartesian = Preorders-Cartesian }
