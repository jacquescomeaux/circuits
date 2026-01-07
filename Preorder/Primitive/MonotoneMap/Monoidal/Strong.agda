{-# OPTIONS --without-K --safe #-}

module Preorder.Primitive.MonotoneMap.Monoidal.Strong where

open import Level using (Level; _⊔_)
open import Preorder.Primitive using (module Isomorphism)
open import Preorder.Primitive.Monoidal using (MonoidalPreorder; SymmetricMonoidalPreorder)
open import Preorder.Primitive.MonotoneMap using (MonotoneMap)

record MonoidalMonotone
    {c₁ c₂ ℓ₁ ℓ₂ : Level}
    (P : MonoidalPreorder c₁ ℓ₁)
    (Q : MonoidalPreorder c₂ ℓ₂)
  : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂) where

  private
    module P = MonoidalPreorder P
    module Q = MonoidalPreorder Q

  field
    F : MonotoneMap P.U Q.U

  open MonotoneMap F public
  open Isomorphism Q.U using (_≅_)

  field
    ε : Q.unit ≅ map P.unit
    ⊗-homo : (p₁ p₂ : P.Carrier) → map p₁ Q.⊗ map p₂ ≅ map (p₁ P.⊗ p₂)

record SymmetricMonoidalMonotone
    {c₁ c₂ ℓ₁ ℓ₂ : Level}
    (P : SymmetricMonoidalPreorder c₁ ℓ₁)
    (Q : SymmetricMonoidalPreorder c₂ ℓ₂)
  : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂) where

  private
    module P = SymmetricMonoidalPreorder P
    module Q = SymmetricMonoidalPreorder Q

  field
    monoidalMonotone : MonoidalMonotone P.monoidalPreorder Q.monoidalPreorder

  open MonoidalMonotone monoidalMonotone public
