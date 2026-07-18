{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Level using (Level; _⊔_)

module Morphism.Zero {o ℓ e : Level} (𝒞 : Category o ℓ e) where

open Category 𝒞

record IsZero⇒ {A B : Obj} (z : A ⇒ B) : Set (o ⊔ ℓ ⊔ e) where
  field
    constant : {C : Obj} (f g : C ⇒ A) → z ∘ f ≈ z ∘ g
    coconstant : {C : Obj} (f g : B ⇒ C) → f ∘ z ≈ g ∘ z
