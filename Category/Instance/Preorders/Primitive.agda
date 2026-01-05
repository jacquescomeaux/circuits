{-# OPTIONS --without-K --safe #-}

module Category.Instance.Preorders.Primitive where

open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Function using (id; _∘_)
open import Level using (Level; _⊔_; suc)
open import Preorder.Primitive using (Preorder; module Isomorphism)
open import Preorder.Primitive.MonotoneMap using (MonotoneMap; _≃_; ≃-isEquivalence; module ≃; map-resp-≅)

-- The category of primitive preorders and monotone maps

private

  module _ {c ℓ : Level} where

    identity : {A : Preorder c ℓ} → MonotoneMap A A
    identity = record
        { map = id
        ; mono = id
        }

    compose : {A B C : Preorder c ℓ} → MonotoneMap B C → MonotoneMap A B → MonotoneMap A C
    compose f g = record
        { map = f.map ∘ g.map
        ; mono = f.mono ∘ g.mono
        }
      where
        module f = MonotoneMap f
        module g = MonotoneMap g

    compose-resp-≃
        : {A B C : Preorder c ℓ}
          {f h : MonotoneMap B C}
          {g i : MonotoneMap A B}
        → f ≃ h
        → g ≃ i
        → compose f g ≃ compose h i
    compose-resp-≃ {C = C} {h = h} {g} f≃h g≃i x = ≅.trans (f≃h (map g x)) (map-resp-≅ h (g≃i x))
      where
        open MonotoneMap using (map; mono)
        open Preorder C
        open Isomorphism C

Preorders : (c ℓ : Level) → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Preorders c ℓ = categoryHelper record
    { Obj = Preorder c ℓ
    ; _⇒_ = MonotoneMap
    ; _≈_ = _≃_
    ; id = identity
    ; _∘_ = compose
    ; assoc = λ {f = f} {g h} → ≃.refl {x = compose (compose h g) f}
    ; identityˡ = λ {f = f} → ≃.refl {x = f}
    ; identityʳ = λ {f = f} → ≃.refl {x = f}
    ; equiv = ≃-isEquivalence
    ; ∘-resp-≈ = λ {f = f} {g h i} → compose-resp-≃ {f = f} {g} {h} {i}
    }
