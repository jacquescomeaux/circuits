{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Dagger.Semiadditive using (IdempotentSemiadditiveDagger)
open import Level using (Level)

module Data.WiringDiagram.Balanced
    {o ℓ e : Level}
    {𝒞 : Category o ℓ e}
    (S : IdempotentSemiadditiveDagger 𝒞)
  where

open import Categories.Functor using (Functor)
open import Data.WiringDiagram.Core S using (WiringDiagram; _□_)
open import Data.WiringDiagram.Directed S using (DWD)
open import Function using (id)

open Category 𝒞 using (Obj)

-- The category of balanced wiring diagrams
BWD : Category o ℓ e
BWD = record
    { Obj = Obj
    ; _⇒_ = λ A B → WiringDiagram (A □ A) (B □ B)
    ; Category DWD
    }

-- Inclusion functor from BWD to DWD
Include : Functor BWD DWD
Include = record
    { F₀ = λ A → A □ A
    ; F₁ = id
    ; identity = Equiv.refl
    ; homomorphism = Equiv.refl
    ; F-resp-≈ = id
    }
  where
    open Category DWD using (module Equiv)
