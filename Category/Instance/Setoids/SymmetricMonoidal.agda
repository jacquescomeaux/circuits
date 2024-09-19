{-# OPTIONS --without-K --safe #-}

module Category.Instance.Setoids.SymmetricMonoidal {ℓ} where

open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Instance.Setoids
    using (Setoids-Cartesian; Setoids-Cocartesian)
    renaming (Setoids-Monoidal to ×-monoidal)
open import Categories.Category.Cartesian.SymmetricMonoidal (Setoids ℓ ℓ) Setoids-Cartesian
    using ()
    renaming (symmetric to ×-symmetric)
open import Level using (suc)
open import Categories.Category.Cocartesian (Setoids ℓ ℓ)
    using (module CocartesianMonoidal; module CocartesianSymmetricMonoidal)
open CocartesianMonoidal (Setoids-Cocartesian {ℓ} {ℓ}) using (+-monoidal)
open CocartesianSymmetricMonoidal (Setoids-Cocartesian {ℓ} {ℓ}) using (+-symmetric)


Setoids-× : SymmetricMonoidalCategory (suc ℓ) ℓ ℓ
Setoids-× = record
    { U = Setoids ℓ ℓ
    ; monoidal = ×-monoidal
    ; symmetric = ×-symmetric
    }

Setoids-+ : SymmetricMonoidalCategory (suc ℓ) ℓ ℓ
Setoids-+ = record
    { U = Setoids ℓ ℓ
    ; monoidal = +-monoidal
    ; symmetric = +-symmetric
    }
