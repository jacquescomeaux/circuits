{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)

open Lax using (SymmetricMonoidalFunctor)
open FinitelyCocompleteCategory
  using ()
  renaming (symmetricMonoidalCategory to smc)

module Category.Monoidal.Instance.DecoratedCospans.Products
    {o o′ ℓ ℓ′ e e′}
    (𝒞 : FinitelyCocompleteCategory o ℓ e)
    {𝒟 : SymmetricMonoidalCategory o′ ℓ′ e′}
    (F : SymmetricMonoidalFunctor (smc 𝒞) 𝒟) where

import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Categories.Category using (_[_,_]; _[_≈_]; _[_∘_]; Category)
open import Categories.Category.Core using (Category)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Monoidal.Symmetric.Properties using (∘-SymmetricMonoidal)
open import Categories.Functor.Monoidal.Construction.Product using (⁂-SymmetricMonoidalFunctor)
open import Categories.NaturalTransformation.Core using (NaturalTransformation; _∘ᵥ_; ntHelper)
open import Category.Instance.Properties.SymMonCat {o} {ℓ} {e} using (SymMonCat-Cartesian)
open import Category.Instance.Properties.SymMonCat {o′} {ℓ′} {e′} using () renaming (SymMonCat-Cartesian to SymMonCat-Cartesian′)
open import Category.Cartesian.Instance.FinitelyCocompletes {o} {ℓ} {e} using (FinitelyCocompletes-CC)
open import Category.Cartesian.Instance.SymMonCat {o} {ℓ} {e} using (SymMonCat-CC)
open import Data.Product.Base using (_,_)
open import Categories.Functor.Cartesian using (CartesianF)
open import Functor.Cartesian.Instance.Underlying.SymmetricMonoidal.FinitelyCocomplete {o} {ℓ} {e} using (Underlying)

module SMC = CartesianF Underlying
module SymMonCat-CC = CartesianCategory SymMonCat-CC

module 𝒞 = FinitelyCocompleteCategory 𝒞
module 𝒟 = SymmetricMonoidalCategory 𝒟

module _ where

  open CartesianCategory FinitelyCocompletes-CC using (_×_)

  𝒞×𝒞 : FinitelyCocompleteCategory o ℓ e
  𝒞×𝒞 = 𝒞 × 𝒞

  [𝒞×𝒞]×𝒞 : FinitelyCocompleteCategory o ℓ e
  [𝒞×𝒞]×𝒞 = (𝒞 × 𝒞) × 𝒞

module _ where

  module _ where

    open Cartesian SymMonCat-Cartesian′ using (_×_)

    𝒟×𝒟 : SymmetricMonoidalCategory o′ ℓ′ e′
    𝒟×𝒟 = 𝒟 × 𝒟
    module 𝒟×𝒟 = SymmetricMonoidalCategory 𝒟×𝒟

    [𝒟×𝒟]×𝒟 : SymmetricMonoidalCategory o′ ℓ′ e′
    [𝒟×𝒟]×𝒟 = (𝒟 × 𝒟) × 𝒟
    module [𝒟×𝒟]×𝒟 = SymmetricMonoidalCategory [𝒟×𝒟]×𝒟

  module _ where

    open Cartesian SymMonCat-Cartesian using (_×_)

    smc𝒞×𝒞 : SymmetricMonoidalCategory o ℓ e
    smc𝒞×𝒞 = smc 𝒞 × smc 𝒞

    smc[𝒞×𝒞]×𝒞 : SymmetricMonoidalCategory o ℓ e
    smc[𝒞×𝒞]×𝒞 = (smc 𝒞×𝒞) × smc 𝒞

  F×F′ : SymmetricMonoidalFunctor smc𝒞×𝒞 𝒟×𝒟
  F×F′ = ⁂-SymmetricMonoidalFunctor {o′} {ℓ′} {e′} {o′} {ℓ′} {e′} {𝒟} {𝒟} {o} {ℓ} {e} {o} {ℓ} {e} {smc 𝒞} {smc 𝒞} F F

  F×F : SymmetricMonoidalFunctor (smc 𝒞×𝒞) 𝒟×𝒟
  F×F = ∘-SymmetricMonoidal F×F′ from
    where
      open Morphism SymMonCat-CC.U using (_≅_)
      ≅ : smc 𝒞×𝒞 ≅ smc𝒞×𝒞
      ≅ = SMC.×-iso 𝒞 𝒞
      open _≅_ ≅
  module F×F = SymmetricMonoidalFunctor F×F

  [F×F]×F′ : SymmetricMonoidalFunctor smc[𝒞×𝒞]×𝒞 [𝒟×𝒟]×𝒟
  [F×F]×F′ = ⁂-SymmetricMonoidalFunctor {o′} {ℓ′} {e′} {o′} {ℓ′} {e′} {𝒟×𝒟} {𝒟} {o} {ℓ} {e} {o} {ℓ} {e} {smc 𝒞×𝒞} {smc 𝒞} F×F F

  [F×F]×F : SymmetricMonoidalFunctor (smc [𝒞×𝒞]×𝒞) [𝒟×𝒟]×𝒟
  [F×F]×F = ∘-SymmetricMonoidal [F×F]×F′ from
    where
      open Morphism SymMonCat-CC.U using (_≅_)
      ≅ : smc [𝒞×𝒞]×𝒞 ≅ smc[𝒞×𝒞]×𝒞
      ≅ = SMC.×-iso 𝒞×𝒞 𝒞
      open _≅_ ≅
  module [F×F]×F = SymmetricMonoidalFunctor [F×F]×F
