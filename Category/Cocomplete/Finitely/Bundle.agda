{-# OPTIONS --without-K --safe #-}
module Category.Cocomplete.Finitely.Bundle where

open import Level
open import Categories.Category.Core using (Category)
open import Categories.Category.Cocomplete.Finitely using (FinitelyCocomplete)
open import Category.Cocomplete.Finitely.SymmetricMonoidal using (module FinitelyCocompleteSymmetricMonoidal)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)


record FinitelyCocompleteCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where

  field
    U     : Category o ℓ e
    finCo : FinitelyCocomplete U

  open Category U public
  open FinitelyCocomplete finCo public

  open FinitelyCocompleteSymmetricMonoidal finCo using (+-monoidal; +-symmetric)

  symmetricMonoidalCategory : SymmetricMonoidalCategory o ℓ e
  symmetricMonoidalCategory = record
      { U = U
      ; monoidal = +-monoidal
      ; symmetric = +-symmetric
      }
