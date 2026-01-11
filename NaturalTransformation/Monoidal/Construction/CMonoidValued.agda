{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Category.Construction.CMonoids using (CMonoids)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor using (Functor) renaming (_∘F_ to _∙_)
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ˡ_)
open import Level using (Level)

-- A natural transformation between functors F, G
-- from a cocartesian category 𝒞 to CMonoids[S]
-- can be turned into a symmetric monoidal natural transformation
-- between symmetric monoidal functors F′ G′ from 𝒞 to S

module NaturalTransformation.Monoidal.Construction.CMonoidValued
    {o o′ ℓ ℓ′ e e′ : Level}
    {𝒞 : Category o ℓ e}
    (𝒞-+ : Cocartesian 𝒞)
    {S : SymmetricMonoidalCategory o′ ℓ′ e′}
    (let module S = SymmetricMonoidalCategory S)
    {M N : Functor 𝒞 (CMonoids S.symmetric)}
    (α : NaturalTransformation M N)
  where

import Functor.Monoidal.Construction.CMonoidValued 𝒞-+ {S = S} as FamilyOfCMonoids
import NaturalTransformation.Monoidal.Construction.MonoidValued as MonoidValued

open import Categories.Category.Construction.Monoids using (Monoids)
open import Functor.Forgetful.Instance.CMonoid S.symmetric using (Forget)

module _ where
  open import Categories.NaturalTransformation.Monoidal using (module Lax)
  open Lax using (MonoidalNaturalTransformation) public

module _ where
  open import Categories.NaturalTransformation.Monoidal.Symmetric using (module Lax)
  open Lax using (SymmetricMonoidalNaturalTransformation) public

private

  module M = Functor M
  module N = Functor N
  open FamilyOfCMonoids M using (F,⊗,ε,σ)
  open FamilyOfCMonoids N using () renaming (F,⊗,ε,σ to G,⊗,ε,σ)

  F : Functor 𝒞 (Monoids S.monoidal)
  F = Forget ∙ M

  G : Functor 𝒞 (Monoids S.monoidal)
  G = Forget ∙ N

  β : NaturalTransformation F G
  β = Forget ∘ˡ α

open MonoidValued 𝒞-+ β using (β,⊗,ε)

β,⊗,ε,σ : SymmetricMonoidalNaturalTransformation F,⊗,ε,σ G,⊗,ε,σ
β,⊗,ε,σ = record { MonoidalNaturalTransformation β,⊗,ε }

module β,⊗,ε,σ = SymmetricMonoidalNaturalTransformation β,⊗,ε,σ
