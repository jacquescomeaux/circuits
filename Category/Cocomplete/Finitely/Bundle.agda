{-# OPTIONS --without-K --safe #-}
module Category.Cocomplete.Finitely.Bundle where

open import Categories.Category.Cocartesian.Bundle using (CocartesianCategory)
open import Categories.Category.Core using (Category)
open import Categories.Category.Cocomplete.Finitely using (FinitelyCocomplete)
open import Category.Cocomplete.Finitely.SymmetricMonoidal using (module FinitelyCocompleteSymmetricMonoidal)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Level using (_⊔_; suc)

record FinitelyCocompleteCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where

  field
    U     : Category o ℓ e
    finCo : FinitelyCocomplete U

  open Category U public
  open FinitelyCocomplete finCo public

  open FinitelyCocompleteSymmetricMonoidal finCo
    using ()
    renaming (+-monoidal to monoidal; +-symmetric to symmetric)
    public

  symmetricMonoidalCategory : SymmetricMonoidalCategory o ℓ e
  symmetricMonoidalCategory = record
      { U = U
      ; monoidal = monoidal
      ; symmetric = symmetric
      }
  {-# INJECTIVE_FOR_INFERENCE symmetricMonoidalCategory #-}

  cocartesianCategory : CocartesianCategory o ℓ e
  cocartesianCategory = record
      { U = U
      ; cocartesian = cocartesian
      }
