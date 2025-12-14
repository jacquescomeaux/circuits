{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Category.Cocartesian using (Cocartesian)

module Functor.Instance.Monoidalize
    {o o′ ℓ ℓ′ e e ′ : Level}
    {C : Category o ℓ e}
    (cocartesian : Cocartesian C)
    (D : MonoidalCategory o ℓ e)
  where

open import Categories.Category.Cocartesian using (module CocartesianMonoidal)

open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal using (MonoidalFunctor)
open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.Construction.MonoidalFunctors using (module Lax)
open import Functor.Monoidal.Construction.MonoidValued cocartesian {D} using () renaming (F,⊗,ε to MonoidalFunctorOf)
open import NaturalTransformation.Monoidal.Construction.MonoidValued cocartesian {D} using () renaming (β,⊗,ε to MonoidalNaturalTransformationOf)

C-MC : MonoidalCategory o ℓ e
C-MC = record { monoidal = +-monoidal }
  where
    open CocartesianMonoidal C cocartesian

module C = MonoidalCategory C-MC
module D = MonoidalCategory D

open Lax using (MonoidalFunctors)
open Functor

Monoidalize : Functor (Functors C.U (Monoids D.monoidal)) (MonoidalFunctors C-MC D)
Monoidalize .F₀ = MonoidalFunctorOf
Monoidalize .F₁ α = MonoidalNaturalTransformationOf α
Monoidalize .identity = D.Equiv.refl
Monoidalize .homomorphism = D.Equiv.refl
Monoidalize .F-resp-≈ x = x

module Monoidalize = Functor Monoidalize
