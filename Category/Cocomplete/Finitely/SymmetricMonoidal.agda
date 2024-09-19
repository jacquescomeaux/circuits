{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

module Category.Cocomplete.Finitely.SymmetricMonoidal {o ℓ e} {𝒞 : Category o ℓ e} where

open import Categories.Category.Cocomplete.Finitely using (FinitelyCocomplete)
open import Categories.Category.Cocartesian 𝒞 using (module CocartesianMonoidal; module CocartesianSymmetricMonoidal)


module FinitelyCocompleteSymmetricMonoidal (finCo : FinitelyCocomplete 𝒞) where

  open FinitelyCocomplete finCo using (cocartesian)
  open CocartesianMonoidal cocartesian using (+-monoidal) public
  open CocartesianSymmetricMonoidal cocartesian using (+-symmetric) public
