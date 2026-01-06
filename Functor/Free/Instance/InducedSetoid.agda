{-# OPTIONS --without-K --safe #-}

module Functor.Free.Instance.InducedSetoid where

-- The induced setoid of a (primitive) preorder

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Category.Instance.Preorders.Primitive using (Preorders)
open import Function using (Func)
open import Level using (Level)
open import Preorder.Primitive using (Preorder; module Isomorphism)
open import Preorder.Primitive.MonotoneMap using (MonotoneMap)
open import Relation.Binary using (Setoid)

module _ {c ℓ : Level} where

  module _ (P : Preorder c ℓ) where

    open Preorder P
    open Isomorphism P using (_≅_; ≅-isEquivalence)

    ≅-setoid : Setoid c ℓ
    ≅-setoid = record
        { Carrier = Carrier
        ; _≈_ = _≅_
        ; isEquivalence = ≅-isEquivalence
        }

  func : {A B : Preorder c ℓ} → MonotoneMap A B → Func (≅-setoid A) (≅-setoid B)
  func {A} {B} f = let open MonotoneMap f in record
      { to = map
      ; cong = map-resp-≅
      }

  open Isomorphism using (module ≅)

  InducedSetoid : Functor (Preorders c ℓ) (Setoids c ℓ)
  InducedSetoid = record
      { F₀ = ≅-setoid
      ; F₁ = func
      ; identity = λ {P} → ≅.refl P
      ; homomorphism = λ {Z = Z} → ≅.refl Z
      ; F-resp-≈ = λ f≃g {x} → f≃g x
      }

  module InducedSetoid = Functor InducedSetoid
