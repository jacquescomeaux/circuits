{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Level using (Level; _⊔_)

-- The endofunctor in setoids sending A to Vector A n for a fixed n
module Data.Vector.Endofunctor.Setoid (n : ℕ) {c ℓ : Level} where

import Data.Vec as Vec

open import Categories.Category using (_[_≈_])
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Data.Setoid using (∣_∣)
open import Data.Vec.Properties using (map-id; map-∘)
open import Data.Vec.Relation.Binary.Equality.Setoid using () renaming (_≋_ to _[_≋_])
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using (map⁺; Pointwise)
open import Data.Vector.Core as Core using (Vector; Vectorₛ; module ≊)
open import Data.Vector.Raw using (R-zipWith)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Composition using () renaming (function to compose)
open import Function.Construct.Identity using () renaming (function to Id)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Func
open ℕ
open Vec.Vec
open Pointwise

mapₛ : {A B : Setoid c ℓ} → A ⟶ₛ B → Vectorₛ A n ⟶ₛ Vectorₛ B n
mapₛ f .to = Vec.map (to f)
mapₛ f .cong = map⁺ (cong f)

abstract

  identity
      : {A : Setoid c ℓ}
        {V : Vector A n}
        (open Core A using (_≊_))
      → mapₛ (Id A) ⟨$⟩ V ≊ V
  identity {A} {V} = ≊.reflexive A (map-id V)

  homomorphism
      : {X Y Z : Setoid c ℓ}
        {f : X ⟶ₛ Y}
        {g : Y ⟶ₛ Z}
        {V : Vector X n}
        (open Core Z using (_≊_))
      → mapₛ (compose f g) ⟨$⟩ V ≊ mapₛ g ⟨$⟩ (mapₛ f ⟨$⟩ V)
  homomorphism {_} {_} {Z} {f} {g} {V} = ≊.reflexive Z (map-∘ (to g) (to f) V)

  F-resp-≈
      : {A B : Setoid c ℓ}
        {f g : A ⟶ₛ B}
      → Setoids c ℓ [ f ≈ g ]
      → Setoids c (c ⊔ ℓ) [ mapₛ f ≈ mapₛ g ]
  F-resp-≈ {A} {B} {_} {g} f≈g {V} = map⁺ (λ x≈y → B.trans f≈g (cong g x≈y)) (≊.refl A)
    where
      module B = Setoid B

-- only a true endofunctor when c ≤ ℓ
Vec : Functor (Setoids c ℓ) (Setoids c (c ⊔ ℓ))
Vec = record
    { F₀ = λ A → Vectorₛ A n
    ; F₁ = mapₛ
    ; identity = λ {A} → identity {A}
    ; homomorphism = λ {f = f} {g} → homomorphism {f = f} {g}
    ; F-resp-≈ = λ {f = f} {g} → F-resp-≈ {f = f} {g}
    }

zipWith-cong
    : {A B : Set c}
      (C : Setoid c ℓ)
      (let module C = Setoid C)
      {f g : A → B → ∣ C ∣}
    → (∀ x y → f x y C.≈ g x y)
    → (xs : Vec.Vec A n)
      (ys : Vec.Vec B n)
    → C [ Vec.zipWith f xs ys ≋ Vec.zipWith g xs ys ]
zipWith-cong C f≈g xs ys = R-zipWith {R = _≡_} {S = _≡_} (λ { ≡.refl ≡.refl → f≈g _ _}) (PW.refl ≡.refl) (PW.refl ≡.refl)
