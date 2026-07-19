{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Dagger.Semiadditive using (SemiadditiveDagger)
open import Level using (Level)

module Data.WiringDiagram.Balanced
    {o ℓ e : Level}
    {𝒞 : Category o ℓ e}
    (S : SemiadditiveDagger 𝒞)
  where

import Categories.Morphism.Reasoning 𝒞 as ⇒-Reasoning

open import Categories.Functor using (Functor)
open import Data.WiringDiagram.Core S using (WiringDiagram; _□_; _⌸_; push; pull)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Categories.Category.Monoidal using (Monoidal)
open import Data.WiringDiagram.Directed S using (DWD)
open import Function using () renaming (id to idf)

open Category 𝒞
module DWD = Category DWD

-- The category of balanced wiring diagrams
BWD : Category o ℓ e
BWD = record
    { Obj = Obj
    ; _⇒_ = λ A B → WiringDiagram (A □ A) (B □ B)
    ; DWD
    }

-- Inclusion functor from BWD to DWD
Include : Functor BWD DWD
Include = record
    { F₀ = λ A → A □ A
    ; F₁ = idf
    ; identity = DWD.Equiv.refl
    ; homomorphism = DWD.Equiv.refl
    ; F-resp-≈ = idf
    }

-- Covariant functor from underlying category to BWD
Push : Functor 𝒞 BWD
Push = record
    { F₀ = idf
    ; F₁ = push
    ; identity = elimˡ †-identity ⌸ Equiv.refl
    ; homomorphism = λ {A B C f g} → homoᵢ f g ⌸ Equiv.refl
    ; F-resp-≈ = λ f≈g → (⟨ f≈g ⟩† ⟩∘⟨refl) ⌸ f≈g
    }
  where
    open SemiadditiveDagger S
    open ⇒-Reasoning
    open HomReasoning
    open Equiv
    homoᵢ
        : {A B C : Obj}
          (f : A ⇒ B)
          (g : B ⇒ C)
        → (g ∘ f) † ∘ π₂
        ≈ (f † ∘ π₂) ∘ ⟨ π₁ , ((g † ∘ π₂) ∘ f ×₁ id) ⟩
    homoᵢ f g = begin
        (g ∘ f) † ∘ π₂                              ≈⟨ pushˡ †-homomorphism ⟩
        f † ∘ g † ∘ π₂                              ≈⟨ refl⟩∘⟨ pushʳ (sym π₂∘first) ⟩
        f † ∘ (g † ∘ π₂) ∘ f ×₁ id                  ≈⟨ pushʳ (sym project₂) ⟩
        (f † ∘ π₂) ∘ ⟨ π₁ , (g † ∘ π₂) ∘ f ×₁ id ⟩  ∎

-- Contravariant functor from underlying category to BWD
Pull : Functor op BWD
Pull = record
    { F₀ = idf
    ; F₁ = pull
    ; identity = identityˡ ⌸ †-identity
    ; homomorphism = λ {A B C f g} → homoᵢ f g ⌸ †-homomorphism
    ; F-resp-≈ = λ f≈g → (f≈g ⟩∘⟨refl) ⌸ ⟨ f≈g ⟩†
    }
  where
    open SemiadditiveDagger S
    open HomReasoning
    open ⇒-Reasoning
    open Equiv
    homoᵢ
        : {A B C : Obj}
          (f : B ⇒ A)
          (g : C ⇒ B)
        → (f ∘ g) ∘ π₂
        ≈ (f ∘ π₂) ∘ ⟨ π₁ , (g ∘ π₂) ∘ (f †) ×₁ id ⟩
    homoᵢ f g = begin
        (f ∘ g) ∘ π₂                                ≈⟨ pullʳ (pushʳ (sym π₂∘first)) ⟩
        f ∘ (g ∘ π₂) ∘ (f †) ×₁ id                  ≈⟨ pushʳ (sym project₂) ⟩
        (f ∘ π₂) ∘ ⟨ π₁ , (g ∘ π₂) ∘ (f †) ×₁ id ⟩  ∎
