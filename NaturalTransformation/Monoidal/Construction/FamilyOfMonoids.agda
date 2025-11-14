{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Cocartesian.Bundle using (CocartesianCategory)
open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor using (Functor) renaming (_∘F_ to _∙_)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper; _∘ˡ_)
open import Level using (Level)

-- A natural transformation between functors F, G
-- from a cocartesian category 𝒞 to Monoids[S]
-- can be turned into a monoidal natural transformation
-- between monoidal functors F′ G′ from 𝒞 to S

module NaturalTransformation.Monoidal.Construction.FamilyOfMonoids
    {o o′ ℓ ℓ′ e e′ : Level}
    {𝒞 : Category o ℓ e}
    {𝒞-+ : Cocartesian 𝒞}
    {S : MonoidalCategory o′ ℓ′ e′}
    (let module S = MonoidalCategory S)
    (M N : Functor 𝒞 (Monoids S.monoidal))
    (α : NaturalTransformation M N)
  where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Categories.Object.Monoid as MonoidObject
import Functor.Monoidal.Construction.FamilyOfMonoids 𝒞-+ {S = S} as FamilyOfMonoids

open import Categories.Category using (module Definitions)
open import Categories.Functor.Properties using ([_]-resp-square)
open import Categories.NaturalTransformation.Monoidal using (module Lax)
open import Data.Product using (_,_)
open import Functor.Forgetful.Instance.Monoid S using (Forget)

private

  module α = NaturalTransformation α
  module M = Functor M
  module N = Functor N
  module 𝒞 = CocartesianCategory (record { cocartesian = 𝒞-+ })

  open 𝒞 using (⊥; i₁; i₂; _+_)
  open S

  open MonoidObject monoidal using (Monoid; Monoid⇒)
  open Definitions U using (CommutativeSquare)
  open FamilyOfMonoids M using (F,⊗,ε)
  open FamilyOfMonoids N using () renaming (F,⊗,ε to G,⊗,ε)
  open Monoid using (μ; η)
  open Monoid⇒
  open ⇒-Reasoning U using (glue′)
  open ⊗-Reasoning monoidal

  F : Functor 𝒞 U
  F = Forget ∙ M

  G : Functor 𝒞 U
  G = Forget ∙ N

  β : NaturalTransformation F G
  β = Forget ∘ˡ α

  module F = Functor F
  module G = Functor G
  module β = NaturalTransformation β

  module _ {A : 𝒞.Obj} where

    εₘ : unit ⇒ F.₀ A
    εₘ = η (M.₀ A)

    ⊲ₘ : F.₀ A ⊗₀ F.₀ A ⇒ F.₀ A
    ⊲ₘ = μ (M.₀ A)

    εₙ : unit ⇒ G.₀ A
    εₙ = η (N.₀ A)

    ⊲ₙ : G.₀ A ⊗₀ G.₀ A ⇒ G.₀ A
    ⊲ₙ = μ (N.₀ A)

  ε-compat : β.η ⊥ ∘ εₘ ≈ εₙ
  ε-compat = preserves-η (α.η ⊥)

  module _ {n m : 𝒞.Obj} where

    square : CommutativeSquare ⊲ₘ (β.η (n + m) ⊗₁ β.η (n + m)) (β.η (n + m)) ⊲ₙ
    square = preserves-μ (α.η (n + m))

    comm₁ : CommutativeSquare (F.₁ i₁) (β.η n) (β.η (n + m)) (G.₁ i₁)
    comm₁ = β.commute i₁

    comm₂ : CommutativeSquare (F.₁ i₂) (β.η m) (β.η (n + m)) (G.₁ i₂)
    comm₂ = β.commute i₂

    ⊗-homo-compat : CommutativeSquare (⊲ₘ ∘ F.₁ i₁ ⊗₁ F.₁ i₂) (β.η n ⊗₁ β.η m) (β.η (n + m)) (⊲ₙ ∘ G.₁ i₁ ⊗₁ G.₁ i₂)
    ⊗-homo-compat = glue′ square (parallel comm₁ comm₂)

open Lax.MonoidalNaturalTransformation hiding (ε-compat; ⊗-homo-compat)

β,⊗,ε : Lax.MonoidalNaturalTransformation F,⊗,ε G,⊗,ε
β,⊗,ε .U = β
β,⊗,ε .isMonoidal = record
    { ε-compat = ε-compat
    ; ⊗-homo-compat = ⊗-homo-compat
    }

module β,⊗,ε = Lax.MonoidalNaturalTransformation β,⊗,ε
