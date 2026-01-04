{-# OPTIONS --without-K --safe #-}

module Preorder.Monoidal where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Preorder)
open import Relation.Binary.Morphism using (PreorderHomomorphism)
open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-preorder)

private

  _×ₚ_
      : {c₁ c₂ ℓ₁ ℓ₂ e₁ e₂ : Level}
      → Preorder c₁ ℓ₁ e₁
      → Preorder c₂ ℓ₂ e₂
      → Preorder (c₁ ⊔ c₂) (ℓ₁ ⊔ ℓ₂) (e₁ ⊔ e₂)
  _×ₚ_ P Q = ×-preorder P Q

  infixr 2 _×ₚ_

record Monoidal {c ℓ e : Level} (P : Preorder c ℓ e) : Set (c ⊔ ℓ ⊔ e) where

  open Preorder P

  field
    unit : Carrier
    tensor : PreorderHomomorphism (P ×ₚ P) P

  open PreorderHomomorphism tensor using (⟦_⟧)

  _⊗_ : Carrier → Carrier → Carrier
  _⊗_ x y = ⟦ x , y ⟧

  infixr 10 _⊗_

  field
    unitaryˡ-≲ : (x : Carrier) → unit ⊗ x ≲ x
    unitaryˡ-≳ : (x : Carrier) → x ≲ unit ⊗ x
    unitaryʳ-≲ : (x : Carrier) → x ⊗ unit ≲ x
    unitaryʳ-≳ : (x : Carrier) → x ≲ x ⊗ unit
    associative-≲ : (x y z : Carrier) → (x ⊗ y) ⊗ z ≲ x ⊗ (y ⊗ z)
    associative-≳ : (x y z : Carrier) → x ⊗ (y ⊗ z) ≲ (x ⊗ y) ⊗ z

record Symmetric {c ℓ e : Level} {P : Preorder c ℓ e} (M : Monoidal P) : Set (c ⊔ e) where

  open Monoidal M
  open Preorder P
  open PreorderHomomorphism tensor

  field
    symmetric : (x y : Carrier) → ⟦ x , y ⟧ ≲ ⟦ y , x ⟧

record MonoidalPreorder (c ℓ e : Level) : Set (suc (c ⊔ ℓ ⊔ e)) where

  field
    U : Preorder c ℓ e
    monoidal : Monoidal U

  open Preorder U public
  open Monoidal monoidal public

record SymmetricMonoidalPreorder (c ℓ e : Level) : Set (suc (c ⊔ ℓ ⊔ e)) where

  field
    U : Preorder c ℓ e
    monoidal : Monoidal U
    symmetric : Symmetric monoidal

  monoidalPreorder : MonoidalPreorder c ℓ e
  monoidalPreorder = record { monoidal = monoidal }

  open Preorder U public
  open Monoidal monoidal public
  open Symmetric symmetric public

record MonoidalMonotone
    {c₁ c₂ ℓ₁ ℓ₂ e₁ e₂ : Level}
    (P : MonoidalPreorder c₁ ℓ₁ e₁)
    (Q : MonoidalPreorder c₂ ℓ₂ e₂)
  : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ e₁ ⊔ e₂) where

  private
    module P = MonoidalPreorder P
    module Q = MonoidalPreorder Q

  field
    F : PreorderHomomorphism P.U Q.U

  open PreorderHomomorphism F public

  field
    ε : Q.unit Q.≲ ⟦ P.unit ⟧
    ⊗-homo : (p₁ p₂ : P.Carrier) → ⟦ p₁ ⟧ Q.⊗ ⟦ p₂ ⟧ Q.≲ ⟦ p₁ P.⊗ p₂ ⟧

record SymmetricMonoidalMonotone
    {c₁ c₂ ℓ₁ ℓ₂ e₁ e₂ : Level}
    (P : SymmetricMonoidalPreorder c₁ ℓ₁ e₁)
    (Q : SymmetricMonoidalPreorder c₂ ℓ₂ e₂)
  : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ e₁ ⊔ e₂) where

  private
    module P = SymmetricMonoidalPreorder P
    module Q = SymmetricMonoidalPreorder Q

  field
    monoidalMonotone : MonoidalMonotone P.monoidalPreorder Q.monoidalPreorder

  open MonoidalMonotone monoidalMonotone public
