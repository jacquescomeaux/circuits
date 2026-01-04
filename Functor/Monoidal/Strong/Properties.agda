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

private

  module C where
    open MonoidalCategory C public
    open ⊗-Utilities.Shorthands monoidal public using (α⇐; λ⇐; ρ⇐)

  module D where
    open MonoidalCategory D public
    open ⊗-Utilities.Shorthands monoidal using (α⇐; λ⇐; ρ⇐) public
    open Core.Shorthands U using (_∘ᵢ_; idᵢ; _≈ᵢ_; ⌞_⌟; to-≈; _≅_; module HomReasoningᵢ) public
    open ⊗-Utilities monoidal using (_⊗ᵢ_) public

open D

open StrongMonoidalFunctor F,φ,ε

private

  variable
    X Y Z : C.Obj

  α : {A B C : Obj} → (A ⊗₀ B) ⊗₀ C ≅ A ⊗₀ (B ⊗₀ C)
  α = associator

  Fα : F₀ ((X C.⊗₀ Y) C.⊗₀ Z) ≅ F₀ (X C.⊗₀ (Y C.⊗₀ Z))
  Fα = [ F ]-resp-≅ C.associator

  λ- : {A : Obj} → unit ⊗₀ A ≅ A
  λ- = unitorˡ

  Fλ : F₀ (C.unit C.⊗₀ X) ≅ F₀ X
  Fλ = [ F ]-resp-≅ C.unitorˡ

  ρ : {A : Obj} → A ⊗₀ unit ≅ A
  ρ = unitorʳ

  Fρ : F₀ (X C.⊗₀ C.unit) ≅ F₀ X
  Fρ = [ F ]-resp-≅ C.unitorʳ

  φ : F₀ X ⊗₀ F₀ Y ≅ F₀ (X C.⊗₀ Y)
  φ = ⊗-homo.FX≅GX

module Shorthands where

  φ⇒ : F₀ X ⊗₀ F₀ Y ⇒ F₀ (X C.⊗₀ Y)
  φ⇒ = ⊗-homo.⇒.η _

  φ⇐ : F₀ (X C.⊗₀ Y) ⇒ F₀ X ⊗₀ F₀ Y
  φ⇐ = ⊗-homo.⇐.η _

  ε⇒ : unit ⇒ F₀ C.unit
  ε⇒ = ε.from

  ε⇐ : F₀ C.unit ⇒ unit
  ε⇐ = ε.to

open Shorthands
open HomReasoning

associativity-inv : φ⇐ ⊗₁ id ∘ φ⇐ ∘ F₁ (C.α⇐ {X} {Y} {Z}) ≈ α⇐ ∘ id ⊗₁ φ⇐ ∘ φ⇐
associativity-inv = begin
    φ⇐ ⊗₁ id ∘ φ⇐ ∘ F₁ C.α⇐   ≈⟨ sym-assoc ⟩
    (φ⇐ ⊗₁ id ∘ φ⇐) ∘ F₁ C.α⇐ ≈⟨ to-≈ associativityᵢ ⟩
    (α⇐ ∘ id ⊗₁ φ⇐) ∘ φ⇐      ≈⟨ assoc ⟩
    α⇐ ∘ id ⊗₁ φ⇐ ∘ φ⇐        ∎

unitaryˡ-inv : ε⇐ ⊗₁ id ∘ φ⇐ ∘ F₁ (C.λ⇐ {X}) ≈ λ⇐
unitaryˡ-inv = begin
    ε⇐ ⊗₁ id ∘ φ⇐ ∘ F₁ C.λ⇐   ≈⟨ sym-assoc ⟩
    (ε⇐ ⊗₁ id ∘ φ⇐) ∘ F₁ C.λ⇐ ≈⟨ to-≈ unitaryˡᵢ ⟩
    λ⇐                        ∎

unitaryʳ-inv : id ⊗₁ ε⇐ ∘ φ⇐ ∘ F₁ (C.ρ⇐ {X}) ≈ ρ⇐
unitaryʳ-inv = begin
    id ⊗₁ ε⇐ ∘ φ⇐ ∘ F₁ C.ρ⇐   ≈⟨ sym-assoc ⟩
    (id ⊗₁ ε⇐ ∘ φ⇐) ∘ F₁ C.ρ⇐ ≈⟨ to-≈ unitaryʳᵢ ⟩
    ρ⇐                        ∎
