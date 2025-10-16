{-# OPTIONS --without-K --safe #-}

module Category.Monoidal.Instance.Nat where

open import Level using (0ℓ)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Category.Instance.Nat using (Nat; Nat-Cartesian; Nat-Cocartesian; Natop)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cocartesian using (Cocartesian; module CocartesianMonoidal; module CocartesianSymmetricMonoidal)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Duality using (coCartesian⇒Cocartesian; Cocartesian⇒coCartesian)

import Categories.Category.Cartesian.SymmetricMonoidal as CartesianSymmetricMonoidal

Natop-Cartesian : Cartesian Natop
Natop-Cartesian = Cocartesian⇒coCartesian Nat Nat-Cocartesian

Natop-Cocartesian : Cocartesian Natop
Natop-Cocartesian = coCartesian⇒Cocartesian Natop Nat-Cartesian

module Monoidal where

  open MonoidalCategory
  open CartesianMonoidal using () renaming (monoidal to ×-monoidal)
  open CocartesianMonoidal using (+-monoidal)

  Nat,+,0 : MonoidalCategory 0ℓ 0ℓ 0ℓ
  Nat,+,0 .U = Nat
  Nat,+,0 .monoidal = +-monoidal Nat Nat-Cocartesian

  Nat,×,1 : MonoidalCategory 0ℓ 0ℓ 0ℓ
  Nat,×,1 .U = Nat
  Nat,×,1 .monoidal = ×-monoidal Nat-Cartesian

  Natop,+,0 : MonoidalCategory 0ℓ 0ℓ 0ℓ
  Natop,+,0 .U = Natop
  Natop,+,0 .monoidal = ×-monoidal Natop-Cartesian

  Natop,×,1 : MonoidalCategory 0ℓ 0ℓ 0ℓ
  Natop,×,1 .U = Natop
  Natop,×,1 .monoidal = +-monoidal Natop Natop-Cocartesian

module Symmetric where

  open SymmetricMonoidalCategory
  open CartesianMonoidal using () renaming (monoidal to ×-monoidal)
  open CocartesianMonoidal using (+-monoidal)
  open CartesianSymmetricMonoidal using () renaming (symmetric to ×-symmetric)
  open CocartesianSymmetricMonoidal using (+-symmetric)

  Nat,+,0 : SymmetricMonoidalCategory 0ℓ 0ℓ 0ℓ
  Nat,+,0 .U = Nat
  Nat,+,0 .monoidal = +-monoidal Nat Nat-Cocartesian
  Nat,+,0 .symmetric = +-symmetric Nat Nat-Cocartesian

  Nat,×,1 : SymmetricMonoidalCategory 0ℓ 0ℓ 0ℓ
  Nat,×,1 .U = Nat
  Nat,×,1 .monoidal = ×-monoidal Nat-Cartesian
  Nat,×,1 .symmetric = ×-symmetric Nat Nat-Cartesian

  Natop,+,0 : SymmetricMonoidalCategory 0ℓ 0ℓ 0ℓ
  Natop,+,0 .U = Natop
  Natop,+,0 .monoidal = ×-monoidal Natop-Cartesian
  Natop,+,0 .symmetric = ×-symmetric Natop Natop-Cartesian

  Natop,×,1 : SymmetricMonoidalCategory 0ℓ 0ℓ 0ℓ
  Natop,×,1 .U = Natop
  Natop,×,1 .monoidal = +-monoidal Natop Natop-Cocartesian
  Natop,×,1 .symmetric = +-symmetric Natop Natop-Cocartesian

open Symmetric public
