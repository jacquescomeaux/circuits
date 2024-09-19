{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Cocomplete.Finitely using (FinitelyCocomplete)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Categories.Functor.Monoidal.Symmetric using (module Strong)
open Strong using (SymmetricMonoidalFunctor)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Category.Instance.Setoids.SymmetricMonoidal using (Setoids-×)

open FinitelyCocompleteCategory using () renaming (symmetricMonoidalCategory to smc)

module Cospan.Decorated
    {o ℓ e}
    (C : FinitelyCocompleteCategory o ℓ e)
    (F : SymmetricMonoidalFunctor (smc C) (Setoids-× {ℓ}))
  where

open FinitelyCocompleteCategory C

open import Category.Instance.Cospans C using (Cospan)
open import Level using (_⊔_)
open import Relation.Binary.Bundles using (Setoid)

open Setoid using () renaming (Carrier to ∣_∣)


record DecoratedCospan (A B : Obj) : Set (o ⊔ ℓ) where

  open SymmetricMonoidalFunctor F using (F₀)

  field
    cospan : Cospan A B

  open Cospan cospan public

  field
    decoration : ∣ F₀ N ∣
