{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Level using (Level; suc; _⊔_)

module Category.KaroubiComplete {o ℓ e : Level} (𝒞 : Category o ℓ e) where

open import Categories.Morphism.Idempotent 𝒞 using (IsSplitIdempotent)

open Category 𝒞

-- A Karoubi complete category is one in which all idempotents split
record KaroubiComplete : Set (suc (o ⊔ ℓ ⊔ e)) where

  field
    split : {A : Obj} {f : A ⇒ A} → f ∘ f ≈ f → IsSplitIdempotent f
