{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Category.Cartesian.Instance.SymMonCat {o ℓ e : Level} where

open import Category.Instance.SymMonCat {o} {ℓ} {e} using (module Lax)
open import Category.Instance.Properties.SymMonCat {o} {ℓ} {e} using (SymMonCat-Cartesian)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)

open Lax using (SymMonCat)

SymMonCat-CC : CartesianCategory (suc (o ⊔ ℓ ⊔ e)) (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e)
SymMonCat-CC = record
    { U = SymMonCat
    ; cartesian = SymMonCat-Cartesian
    }

