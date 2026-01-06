{-# OPTIONS --without-K --safe #-}

module Preorder.Primitive.Monoidal where

open import Level using (Level; _⊔_; suc)
open import Preorder.Primitive using (Preorder; module Isomorphism)
open import Preorder.Primitive.MonotoneMap using (MonotoneMap)
open import Data.Product using (_×_; _,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise; ×-refl; ×-transitive)

private

  _×ₚ_
      : {c₁ c₂ ℓ₁ ℓ₂ : Level}
      → Preorder c₁ ℓ₁
      → Preorder c₂ ℓ₂
      → Preorder (c₁ ⊔ c₂) (ℓ₁ ⊔ ℓ₂)
  _×ₚ_ P Q = record
      { Carrier = P.Carrier × Q.Carrier
      ; _≲_ = Pointwise P._≲_ Q._≲_
      ; refl = ×-refl {R = P._≲_} {S = Q._≲_} P.refl Q.refl
      ; trans = ×-transitive {R = P._≲_} {S = Q._≲_} P.trans Q.trans
      }
    where
      module P = Preorder P
      module Q = Preorder Q

  infixr 2 _×ₚ_

record Monoidal {c ℓ : Level} (P : Preorder c ℓ) : Set (c ⊔ ℓ) where

  open Preorder P
  open Isomorphism P

  field
    unit : Carrier
    tensor : MonotoneMap (P ×ₚ P) P

  open MonotoneMap tensor using (map)

  _⊗_ : Carrier → Carrier → Carrier
  _⊗_ x y = map (x , y)

  infixr 10 _⊗_

  field
    unitaryˡ : (x : Carrier) → unit ⊗ x ≅ x
    unitaryʳ : (x : Carrier) → x ⊗ unit ≅ x
    associative : (x y z : Carrier) → (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z)

record Symmetric {c ℓ : Level} {P : Preorder c ℓ} (M : Monoidal P) : Set (c ⊔ ℓ) where

  open Monoidal M
  open Preorder P

  field
    symmetric : (x y : Carrier) → x ⊗ y ≲ y ⊗ x

record MonoidalPreorder (c ℓ : Level) : Set (suc (c ⊔ ℓ)) where

  field
    U : Preorder c ℓ
    monoidal : Monoidal U

  open Preorder U public
  open Monoidal monoidal public

record SymmetricMonoidalPreorder (c ℓ : Level) : Set (suc (c ⊔ ℓ)) where

  field
    U : Preorder c ℓ
    monoidal : Monoidal U
    symmetric : Symmetric monoidal

  monoidalPreorder : MonoidalPreorder c ℓ
  monoidalPreorder = record { monoidal = monoidal }

  open Preorder U public
  open Monoidal monoidal public
  open Symmetric symmetric public

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

  field
    ε : Q.unit Q.≲ map P.unit
    ⊗-homo : (p₁ p₂ : P.Carrier) → map p₁ Q.⊗ map p₂ Q.≲ map (p₁ P.⊗ p₂)

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
