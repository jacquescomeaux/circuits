{-# OPTIONS --without-K --safe #-}

module Functor.Cartesian.Instance.InducedSetoid where

-- The induced setoid functor is cartesian

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-CartesianCategory)
open import Categories.Functor.Cartesian using (CartesianF)
open import Categories.Object.Product using (IsProduct)
open import Category.Cartesian.Instance.Preorders.Primitive using (Preorders-CC)
open import Data.Product using (<_,_>; _,_)
open import Function using (Func)
open import Functor.Free.Instance.InducedSetoid using () renaming (InducedSetoid to IS)
open import Level using (Level)
open import Preorder.Primitive using (Preorder; module Isomorphism)

module _ {c ℓ : Level} where

  private
    module Preorders-CC = CartesianCategory (Preorders-CC c ℓ)
    module BP = BinaryProducts (Preorders-CC.products)

    IS-resp-×
        : {A B : Preorder c ℓ}
        → IsProduct (Setoids c ℓ) (IS.₁ {B = A} (BP.π₁ {B = B})) (IS.₁ BP.π₂)
    IS-resp-× {A} {B} = record
        { ⟨_,_⟩ = λ {S} S⟶ₛIS₀A S⟶ₛIS₀B → let open Func in record
            { to = < to S⟶ₛIS₀A , to S⟶ₛIS₀B >
            ; cong = λ x≈y → let open Isomorphism._≅_ in record
                { from = from (cong S⟶ₛIS₀A x≈y) , from (cong S⟶ₛIS₀B x≈y)
                ; to = to (cong S⟶ₛIS₀A x≈y) , to (cong S⟶ₛIS₀B x≈y)
                }
            }
        ; project₁ = Isomorphism.≅.refl A
        ; project₂ = Isomorphism.≅.refl B
        ; unique = λ {S} {h} {i} {j} π₁∙h≈i π₂∙h≈j {x} → let open Isomorphism._≅_ in record
            { from = to (π₁∙h≈i {x}) , to (π₂∙h≈j {x})
            ; to = from (π₁∙h≈i {x}) , from (π₂∙h≈j {x})
            }
        }

  InducedSetoid : CartesianF (Preorders-CC c ℓ) (Setoids-CartesianCategory c ℓ)
  InducedSetoid = record
      { F = IS
      ; isCartesian = record
          { F-resp-⊤ = _
          ; F-resp-× = IS-resp-×
          }
      }

  module InducedSetoid = CartesianF InducedSetoid
