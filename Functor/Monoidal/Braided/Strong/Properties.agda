{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Categories.Category.Monoidal using (BraidedMonoidalCategory)
open import Categories.Functor.Monoidal.Braided using (module Strong)
open Strong using (BraidedMonoidalFunctor)

module Functor.Monoidal.Braided.Strong.Properties
  {o o′ ℓ ℓ′ e e′ : Level}
  {C : BraidedMonoidalCategory o ℓ e}
  {D : BraidedMonoidalCategory o′ ℓ′ e′}
  (F,φ,ε : BraidedMonoidalFunctor C D) where

import Categories.Category.Construction.Core as Core
import Categories.Category.Monoidal.Utilities as ⊗-Utilities
import Functor.Monoidal.Strong.Properties as MonoidalProp

open import Categories.Functor.Properties using ([_]-resp-≅)

private

  module C = BraidedMonoidalCategory C
  module D = BraidedMonoidalCategory D

open D
open Core.Shorthands U using (_∘ᵢ_; idᵢ; _≈ᵢ_; ⌞_⌟; to-≈; _≅_; module HomReasoningᵢ)
open ⊗-Utilities monoidal using (_⊗ᵢ_)
open BraidedMonoidalFunctor F,φ,ε
open MonoidalProp monoidalFunctor public

private

  variable
    A B : Obj
    X Y : C.Obj

  σ : A ⊗₀ B ≅ B ⊗₀ A
  σ = braiding.FX≅GX

  σ⇐ : B ⊗₀ A ⇒ A ⊗₀ B
  σ⇐ = braiding.⇐.η _

  Fσ : F₀ (X C.⊗₀ Y) ≅ F₀ (Y C.⊗₀ X)
  Fσ = [ F ]-resp-≅ C.braiding.FX≅GX

  Fσ⇐ : F₀ (Y C.⊗₀ X) ⇒ F₀ (X C.⊗₀ Y)
  Fσ⇐ = F₁ (C.braiding.⇐.η _)

  φ : F₀ X ⊗₀ F₀ Y ≅ F₀ (X C.⊗₀ Y)
  φ = ⊗-homo.FX≅GX

open HomReasoning
open Shorthands using (φ⇐)

braiding-compatᵢ : Fσ {X} {Y} ∘ᵢ φ ≈ᵢ φ ∘ᵢ σ
braiding-compatᵢ = ⌞ braiding-compat ⌟

braiding-compat-inv : φ⇐ ∘ Fσ⇐ {X} {Y} ≈ σ⇐ ∘ φ⇐
braiding-compat-inv = to-≈ braiding-compatᵢ
