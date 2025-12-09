{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; suc)
module Category.Instance.Setoids.SymmetricMonoidal {c ℓ : Level} where

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Instance.Setoids
    using (Setoids-Cartesian; Setoids-Cocartesian)
    renaming (Setoids-Monoidal to ×-monoidal)
open import Categories.Category.Cartesian.SymmetricMonoidal (Setoids c ℓ) Setoids-Cartesian
    using ()
    renaming (symmetric to ×-symmetric)
open import Categories.Category.Cocartesian (Setoids c (c ⊔ ℓ))
    using (module CocartesianMonoidal; module CocartesianSymmetricMonoidal)

open CocartesianMonoidal (Setoids-Cocartesian {c} {ℓ}) using (+-monoidal)
open CocartesianSymmetricMonoidal (Setoids-Cocartesian {c} {ℓ}) using (+-symmetric)

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

opaque

  ×-monoidal′ : Monoidal (Setoids c ℓ)
  ×-monoidal′ = ×-monoidal {c} {ℓ}

  ×-symmetric′ : Symmetric ×-monoidal′
  ×-symmetric′ = ×-symmetric

Setoids-× : SymmetricMonoidalCategory (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Setoids-× = record
    { U = Setoids c ℓ
    ; monoidal = ×-monoidal′
    ; symmetric = ×-symmetric′
    }

Setoids-+ : SymmetricMonoidalCategory (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Setoids-+ = record
    { U = Setoids c (c ⊔ ℓ)
    ; monoidal = +-monoidal
    ; symmetric = +-symmetric
    }

module Setoids-× = SymmetricMonoidalCategory Setoids-×
module Setoids-+ = SymmetricMonoidalCategory Setoids-+
