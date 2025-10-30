{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Functor.Instance.Endo.List {ℓ : Level} where

import Functor.Instance.List {ℓ} {ℓ} as List

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Endofunctor)

-- List is only an endofunctor when the carrier sets and 
-- equivalence relations live at the same level
List : Endofunctor (Setoids ℓ ℓ)
List = List.List
