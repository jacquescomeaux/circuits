{-# OPTIONS --without-K --safe #-}

open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

open FinitelyCocompleteCategory using () renaming (symmetricMonoidalCategory to smc)
open Lax using (SymmetricMonoidalFunctor)

module Cospan.Decorated
    {o o′ ℓ ℓ′ e e′}
    (C : FinitelyCocompleteCategory o ℓ e)
    {D : SymmetricMonoidalCategory o′ ℓ′ e′}
    (F : SymmetricMonoidalFunctor (smc C) D)
  where

module C = FinitelyCocompleteCategory C
module D = SymmetricMonoidalCategory D

open import Category.Diagram.Cospan C using (Cospan)
open import Level using (_⊔_)


record DecoratedCospan (A B : C.Obj) : Set (o ⊔ ℓ ⊔ ℓ′) where

  open SymmetricMonoidalFunctor F using (F₀)

  field
    cospan : Cospan A B

  open Cospan cospan public

  field
    decoration : D.unit D.⇒ F₀ N
