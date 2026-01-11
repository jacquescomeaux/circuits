{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Cocartesian using (Cocartesian)

module Functor.Instance.CMonoidalize
    {o o′ ℓ ℓ′ e e′ : Level}
    {C : Category o ℓ e}
    (cocartesian : Cocartesian C)
    (D : SymmetricMonoidalCategory o′ ℓ′ e′)
  where

open import Categories.Category.Cocartesian using (module CocartesianSymmetricMonoidal)
open import Categories.Functor using (Functor)
open import Category.Construction.CMonoids using (CMonoids)
open import Categories.Category.Construction.Functors using (Functors)
open import Category.Construction.SymmetricMonoidalFunctors using (module Lax)
open import Functor.Monoidal.Construction.CMonoidValued cocartesian {D} using () renaming (F,⊗,ε,σ to SMFOf)
open import NaturalTransformation.Monoidal.Construction.CMonoidValued cocartesian {D} using () renaming (β,⊗,ε,σ to SMNTOf)

private

  open CocartesianSymmetricMonoidal C cocartesian

  C-SMC : SymmetricMonoidalCategory o ℓ e
  C-SMC = record { symmetric = +-symmetric }

  module C = SymmetricMonoidalCategory C-SMC
  module D = SymmetricMonoidalCategory D

open Functor

CMonoidalize : Functor (Functors C.U (CMonoids D.symmetric)) (Lax.SymmetricMonoidalFunctors C-SMC D)
CMonoidalize .F₀ = SMFOf
CMonoidalize .F₁ α = SMNTOf α
CMonoidalize .identity = D.Equiv.refl
CMonoidalize .homomorphism = D.Equiv.refl
CMonoidalize .F-resp-≈ x = x

module CMonoidalize = Functor CMonoidalize
