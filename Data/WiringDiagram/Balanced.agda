{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Dagger.Semiadditive using (IdempotentSemiadditiveDagger)
open import Level using (Level)

module Data.WiringDiagram.Balanced
    {o ℓ e : Level}
    {𝒞 : Category o ℓ e}
    (S : IdempotentSemiadditiveDagger 𝒞)
  where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Categories.Functor using (Functor)
open import Data.WiringDiagram.Core S using (WiringDiagram; _□_; _⌸_; push)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Categories.Category.Monoidal using (Monoidal)
open import Data.WiringDiagram.Directed S using (DWD)
open import Function using () renaming (id to idf)

module 𝒞 = Category 𝒞
module DWD = Category DWD

-- The category of balanced wiring diagrams
BWD : Category o ℓ e
BWD = record
    { Obj = 𝒞.Obj
    ; _⇒_ = λ A B → WiringDiagram (A □ A) (B □ B)
    ; DWD
    }

-- Inclusion functor from BWD to DWD
Include : Functor BWD DWD
Include = record
    { F₀ = λ A → A □ A
    ; F₁ = idf
    ; identity = Equiv.refl
    ; homomorphism = Equiv.refl
    ; F-resp-≈ = idf
    }
  where
    open DWD using (module Equiv)

-- Covariant functor from underlying category to BWD
Push : Functor 𝒞 BWD
Push = record
    { F₀ = idf
    ; F₁ = push
    ; identity = elimˡ †-identity ⌸ Equiv.refl
    ; homomorphism = λ {A B C f g} → homoᵢ f g ⌸ Equiv.refl
    ; F-resp-≈ = λ f≈g → (†-resp-≈ f≈g ⟩∘⟨refl) ⌸ f≈g
    }
  where
    open Category 𝒞
    open IdempotentSemiadditiveDagger S
      using (+-monoidal; _†; p₂; _⊕₁_; △; !; p₁; p₂-⊕; ⇒!; ⇒△; ρ⇒≈p₁; p₁∘△; †-homomorphism; †-identity; †-resp-≈)
    open Monoidal +-monoidal using (assoc-commute-from; unitorˡ-commute-from; triangle)
    open Shorthands +-monoidal using (α⇒; λ⇒; ρ⇒)
    open ⇒-Reasoning 𝒞
    open ⊗-Reasoning +-monoidal
    homoᵢ
        : {A B C : Obj}
          (f : A ⇒ B)
          (g : B ⇒ C)
        → (g ∘ f) † ∘ p₂
        ≈ (f † ∘ p₂) ∘ id ⊕₁ ((g † ∘ p₂) ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
    homoᵢ f g = begin
        (g ∘ f) † ∘ p₂                                                        ≈⟨ pushˡ †-homomorphism ⟩
        f † ∘ g † ∘ p₂                                                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ p₂-⊕ ⟩
        f † ∘ g † ∘ λ⇒ ∘ ! ⊕₁ id                                              ≈⟨ refl⟩∘⟨ extendʳ unitorˡ-commute-from ⟨
        f † ∘ λ⇒ ∘ id ⊕₁ (g †) ∘ ! ⊕₁ id                                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ insertˡ p₁∘△ ⟩⊗⟨refl ⟩
        f † ∘ λ⇒ ∘ id ⊕₁ (g †) ∘ (p₁ ∘ △ ∘ !) ⊕₁ id                           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (ρ⇒≈p₁ ⟩∘⟨refl) ⟩⊗⟨refl ⟨
        f † ∘ λ⇒ ∘ id ⊕₁ (g †) ∘ (ρ⇒ ∘ △ ∘ !) ⊕₁ id                           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
        f † ∘ λ⇒ ∘ id ⊕₁ (g †) ∘ ρ⇒ ⊕₁ id ∘ (△ ∘ !) ⊕₁ id                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⇒△ ⟩⊗⟨refl ⟩
        f † ∘ λ⇒ ∘ id ⊕₁ (g †) ∘ ρ⇒ ⊕₁ id ∘ (! ⊕₁ ! ∘ △) ⊕₁ id                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
        f † ∘ λ⇒ ∘ id ⊕₁ (g †) ∘ ρ⇒ ⊕₁ id ∘ (! ⊕₁ !) ⊕₁ id ∘ △ ⊕₁ id          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (Equiv.sym triangle) ⟩
        f † ∘ λ⇒ ∘ id ⊕₁ (g †) ∘ id ⊕₁ λ⇒ ∘ α⇒ ∘ (! ⊕₁ !) ⊕₁ id ∘ △ ⊕₁ id     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
        f † ∘ λ⇒ ∘ id ⊕₁ (g † ∘ λ⇒) ∘ α⇒ ∘ (! ⊕₁ !) ⊕₁ id ∘ △ ⊕₁ id           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
        f † ∘ λ⇒ ∘ id ⊕₁ (g † ∘ λ⇒) ∘ ! ⊕₁ ! ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
        f † ∘ λ⇒ ∘ ! ⊕₁ ((g † ∘ λ⇒) ∘ ! ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                 ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ (pullʳ (refl⟩∘⟨ (Equiv.sym ⇒! ⟩⊗⟨refl))) ⟩∘⟨refl ⟩
        f † ∘ λ⇒ ∘ ! ⊕₁ (g † ∘ λ⇒ ∘ (! ∘ f) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ (pushʳ split₁ˡ)) ⟩∘⟨refl ⟩
        f † ∘ λ⇒ ∘ ! ⊕₁ (g † ∘ (λ⇒ ∘ ! ⊕₁ id) ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ (pullˡ (refl⟩∘⟨ Equiv.sym p₂-⊕)) ⟩∘⟨refl ⟩
        f † ∘ λ⇒ ∘ ! ⊕₁ ((g † ∘ p₂) ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                 ≈⟨ pushʳ (extendʳ (pushʳ serialize₁₂)) ⟩
        (f † ∘ (λ⇒ ∘ ! ⊕₁ id)) ∘ id ⊕₁ ((g † ∘ p₂) ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id  ≈⟨ (refl⟩∘⟨ p₂-⊕) ⟩∘⟨refl ⟨
        (f † ∘ p₂) ∘ id ⊕₁ ((g † ∘ p₂) ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id              ∎
