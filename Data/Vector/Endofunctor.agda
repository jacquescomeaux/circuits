{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Level using (Level; _⊔_)

-- The endofunctor in setoids sending A to Vector A n for a fixed n
module Data.Vector.Endofunctor (n : ℕ) {c ℓ : Level} where

import Data.Vec as Vec

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Data.Vec.Properties using (map-id; map-∘)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (map⁺)
open import Data.Vector.Core as Core using (Vector; Vectorₛ; module ≊)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Composition using () renaming (function to compose)
open import Function.Construct.Identity using () renaming (function to Id)
open import Relation.Binary using (Setoid)

open Func

opaque
  unfolding Vector
  map : {c ℓ : Level} {A B : Setoid c ℓ} → A ⟶ₛ B → Vectorₛ A n ⟶ₛ Vectorₛ B n
  map f .to = Vec.map (to f)
  map f .cong = map⁺ (cong f)

abstract opaque

  unfolding map

  identity
      : {A : Setoid c ℓ}
        {V : Vector A n}
        (open Core A using (_≊_))
      → map (Id A) ⟨$⟩ V ≊ V
  identity {A} {V} = ≊.reflexive A (map-id V)

  homomorphism
      : {X Y Z : Setoid c ℓ}
        {f : X ⟶ₛ Y}
        {g : Y ⟶ₛ Z}
        {V : Vector X n}
        (open Core Z using (_≊_))
      → map (compose f g) ⟨$⟩ V ≊ map g ⟨$⟩ (map f ⟨$⟩ V)
  homomorphism {_} {_} {Z} {f} {g} {V} = ≊.reflexive Z (map-∘ (to g) (to f) V)

  F-resp-≈
      : {A B : Setoid c ℓ}
        {f g : A ⟶ₛ B}
      → ({x : Setoid.Carrier A} → (B Setoid.≈ to f x) (to g x))
      → {V : Vector A n}
        (open Core B using (_≊_))
      → map f ⟨$⟩ V ≊ map g ⟨$⟩ V
  F-resp-≈ {A} {B} {_} {g} f≈g {V} = map⁺ (λ x≈y → B.trans f≈g (cong g x≈y)) (≊.refl A)
    where
      module B = Setoid B

-- only a true endofunctor when c ≤ ℓ
Vec : Functor (Setoids c ℓ) (Setoids c (c ⊔ ℓ))
Vec = record
    { F₀ = λ A → Vectorₛ A n
    ; F₁ = map
    ; identity = identity
    ; homomorphism = homomorphism
    ; F-resp-≈ = F-resp-≈
    }
