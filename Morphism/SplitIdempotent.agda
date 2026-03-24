{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Categories.Category using (Category)

module Morphism.SplitIdempotent {o ℓ e : Level} (𝒞 : Category o ℓ e) where

open Category 𝒞

record IsSplitIdempotent {A : Obj} (i : A ⇒ A) : Set (o ⊔ ℓ ⊔ e) where
  field
    B : Obj
    r : A ⇒ B
    s : B ⇒ A
    s∘r : s ∘ r ≈ i
    r∘s : r ∘ s ≈ id

record SplitIdempotent : Set (o ⊔ ℓ ⊔ e) where
  field
    {A} : Obj
    i : A ⇒ A
    isSplitIdempotent : IsSplitIdempotent i
