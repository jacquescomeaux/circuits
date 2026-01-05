{-# OPTIONS --without-K --safe #-}

module Preorder.Primitive.MonotoneMap where

open import Level using (Level; _⊔_)
open import Preorder.Primitive using (Preorder; module Isomorphism)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; IsEquivalence)

-- Monotone (order preserving) maps betweeen primitive preorders

record MonotoneMap {c₁ c₂ ℓ₁ ℓ₂ : Level} (P : Preorder c₁ ℓ₁) (Q : Preorder c₂ ℓ₂) : Set (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂) where

  private
    module P = Preorder P
    module Q = Preorder Q

  field
    map : P.Carrier → Q.Carrier
    mono : {x y : P.Carrier} → x P.≲ y → map x Q.≲ map y

-- Pointwise isomorphism of monotone maps

module _ {c₁ c₂ ℓ₁ ℓ₂ : Level} {P : Preorder c₁ ℓ₁} {Q : Preorder c₂ ℓ₂} where

  private
    module P where
      open Preorder P public
      open Isomorphism P public
    module Q = Isomorphism Q

  open MonotoneMap using (map)

  _≃_ : Rel (MonotoneMap P Q) (c₁ ⊔ ℓ₂)
  _≃_ f g = (x : P.Carrier) → map f x Q.≅ map g x

  infix 4 _≃_

  private

    ≃-refl : Reflexive _≃_
    ≃-refl {f} x = Q.≅.refl {map f x}

    ≃-sym : Symmetric _≃_
    ≃-sym f≃g x = Q.≅.sym (f≃g x)

    ≃-trans : Transitive _≃_
    ≃-trans f≃g g≃h x = Q.≅.trans (f≃g x) (g≃h x)

  ≃-isEquivalence : IsEquivalence _≃_
  ≃-isEquivalence = record
      { refl = λ {f} → ≃-refl {f}
      ; sym = λ {f g} → ≃-sym {f} {g}
      ; trans = λ {f g h} → ≃-trans {f} {g} {h}
      }

  module ≃ = IsEquivalence ≃-isEquivalence

  map-resp-≅ : (f : MonotoneMap P Q) {x y : P.Carrier} → x P.≅ y → map f x Q.≅ map f y
  map-resp-≅ f x≅y = record
      { from = mono from
      ; to = mono to
      }
    where
      open P._≅_ x≅y
      open MonotoneMap f
