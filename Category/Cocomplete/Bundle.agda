{-# OPTIONS --without-K --safe #-}
module Category.Cocomplete.Bundle where

open import Level

open import Categories.Category.Cocomplete.Finitely using (FinitelyCocomplete)
open import Categories.Category.Core using (Category)


record FinitelyCocompleteCategory o ℓ e : Set (suc (o ⊔ ℓ ⊔ e)) where
  field
    U     : Category o ℓ e
    finCo : FinitelyCocomplete U

  open Category U public
  open FinitelyCocomplete finCo public
