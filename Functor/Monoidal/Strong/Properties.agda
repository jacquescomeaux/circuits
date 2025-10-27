{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)

module Functor.Monoidal.Strong.Properties
  {o o′ ℓ ℓ′ e e′ : Level}
  {C : MonoidalCategory o ℓ e}
  {D : MonoidalCategory o′ ℓ′ e′}
  (F,φ,ε : StrongMonoidalFunctor C D) where

import Categories.Category.Monoidal.Utilities as ⊗-Utilities
import Categories.Category.Construction.Core as Core

open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Categories.Functor.Properties using ([_]-resp-≅)

module C where
  open MonoidalCategory C public
  open ⊗-Utilities.Shorthands monoidal public using (α⇐)

module D where
  open MonoidalCategory D public
  open ⊗-Utilities.Shorthands monoidal using (α⇐) public
  open Core.Shorthands U using (_∘ᵢ_; idᵢ; _≈ᵢ_; ⌞_⌟; to-≈; _≅_; module HomReasoningᵢ) public
  open ⊗-Utilities monoidal using (_⊗ᵢ_) public

open D

open StrongMonoidalFunctor F,φ,ε

private

  variable
    X Y Z : C.Obj

  Fα : F₀ ((X C.⊗₀ Y) C.⊗₀ Z) ≅ F₀ (X C.⊗₀ (Y C.⊗₀ Z))
  Fα = [ F ]-resp-≅ C.associator

  α : {A B C : D.Obj} → (A ⊗₀ B) ⊗₀ C ≅ A ⊗₀ (B ⊗₀ C)
  α = associator

  φ : F₀ X ⊗₀ F₀ Y ≅ F₀ (X C.⊗₀ Y)
  φ = ⊗-homo.FX≅GX

  φ⇒ : F₀ X ⊗₀ F₀ Y ⇒ F₀ (X C.⊗₀ Y)
  φ⇒ = ⊗-homo.⇒.η _

  φ⇐ : F₀ (X C.⊗₀ Y) ⇒ F₀ X ⊗₀ F₀ Y
  φ⇐ = ⊗-homo.⇐.η _

associativityᵢ : Fα {X} {Y} {Z} ∘ᵢ φ ∘ᵢ φ ⊗ᵢ idᵢ ≈ᵢ φ ∘ᵢ idᵢ ⊗ᵢ φ ∘ᵢ α
associativityᵢ = ⌞ associativity ⌟

associativity-inv : φ⇐ ⊗₁ id ∘ φ⇐ ∘ F₁ (C.α⇐ {X} {Y} {Z}) ≈ α⇐ ∘ id ⊗₁ φ⇐ ∘ φ⇐
associativity-inv = begin
    φ⇐ ⊗₁ id ∘ φ⇐ ∘ F₁ C.α⇐   ≈⟨ sym-assoc ⟩
    (φ⇐ ⊗₁ id ∘ φ⇐) ∘ F₁ C.α⇐ ≈⟨ to-≈ associativityᵢ ⟩
    (α⇐ ∘ id ⊗₁ φ⇐) ∘ φ⇐      ≈⟨ assoc ⟩
    α⇐ ∘ id ⊗₁ φ⇐ ∘ φ⇐        ∎
  where
    open HomReasoning
