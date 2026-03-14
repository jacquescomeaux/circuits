{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Dagger.Semiadditive using (IdempotentSemiadditiveDagger)
open import Level using (Level)

module Data.WiringDiagram.Directed
    {o ℓ e : Level}
    {𝒞 : Category o ℓ e}
    (S : IdempotentSemiadditiveDagger 𝒞)
  where

import Categories.Category.Monoidal.Properties as ⊗-Properties
import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Data.Product using (_,_)
open import Data.WiringDiagram.Core S using (Box; WiringDiagram; _≈-⧈_; _□_; _⧈_; _⌸_; id-⧈; _⌻_; ≈-isEquiv; pulsh)

open Category 𝒞
open IdempotentSemiadditiveDagger S
open Monoidal +-monoidal
open Shorthands +-monoidal using (α⇒; α⇐; λ⇒; λ⇐; ρ⇒; ρ⇐)
open ⊗-Properties +-monoidal using (coherence₁)

private

  ⌻-resp-≈ : {A B C : Box} {f h : WiringDiagram B C} {g i : WiringDiagram A B} → f ≈-⧈ h → g ≈-⧈ i → f ⌻ g ≈-⧈ h ⌻ i
  ⌻-resp-≈ {A} {B} {C} {fᵢ ⧈ fₒ} {hᵢ ⧈ hₒ} {gᵢ ⧈ gₒ} {iᵢ ⧈ iₒ} (fᵢ≈hᵢ ⌸ fₒ≈hₒ) (gᵢ≈iᵢ ⌸ gₒ≈iₒ) = ≈ᵢ ⌸ ∘-resp-≈ fₒ≈hₒ gₒ≈iₒ
    where
      open ⊗-Reasoning +-monoidal
      ≈ᵢ : gᵢ ∘ id ⊕₁ (fᵢ ∘ gₒ ⊕₁ id) ∘ α⇒ ∘ △ {Box.ₒ A} ⊕₁ id
         ≈ iᵢ ∘ id ⊕₁ (hᵢ ∘ iₒ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
      ≈ᵢ = gᵢ≈iᵢ ⟩∘⟨ refl⟩⊗⟨ (fᵢ≈hᵢ ⟩∘⟨ gₒ≈iₒ ⟩⊗⟨refl) ⟩∘⟨refl

  ⌻-assoc : {A B C D : Box} {f : WiringDiagram A B} {g : WiringDiagram B C} {h : WiringDiagram C D} → (h ⌻ g) ⌻ f ≈-⧈ h ⌻ (g ⌻ f)
  ⌻-assoc {Aᵢ □ Aₒ} {Bᵢ □ Bₒ} {Cᵢ □ Cₒ} {Dᵢ □ Dₒ} {fᵢ ⧈ fₒ} {gᵢ ⧈ gₒ} {hᵢ ⧈ hₒ} = ≈ᵢ ⌸ assoc
    where
      open ⊗-Reasoning +-monoidal

      term₁ : Aₒ ⊕₀ Dᵢ ⇒ Cᵢ
      term₁ = hᵢ ∘ (gₒ ∘ fₒ) ⊕₁ id

      term₂ : Bₒ ⊕₀ Dᵢ ⇒ Cᵢ
      term₂ = hᵢ ∘ gₒ ⊕₁ id

      term₃ : Aₒ ⊕₀ Cᵢ ⇒ Bᵢ
      term₃ = gᵢ ∘ fₒ ⊕₁ id
      open ⇒-Reasoning 𝒞

      lemma₁ : α⇒ {Aₒ ⊕₀ Aₒ} {Aₒ} {Dᵢ} ∘ (α⇐ ∘ id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id ≈ △ ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id
      lemma₁ = begin
          α⇒ ∘ (α⇐ ∘ id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id       ≈⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
          α⇒ ∘ α⇐ ⊕₁ id ∘ (id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ˡ ⟩
          α⇒ ∘ α⇐ ⊕₁ id ∘ (id ⊕₁ △ ∘ △) ⊕₁ id       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ △-assoc ⟩⊗⟨refl ⟩
          α⇒ ∘ α⇐ ⊕₁ id ∘ (α⇒ ∘ △ ⊕₁ id ∘ △) ⊕₁ id  ≈⟨ refl⟩∘⟨ merge₁ʳ ⟩
          α⇒ ∘ (α⇐ ∘ α⇒ ∘ △ ⊕₁ id ∘ △) ⊕₁ id        ≈⟨ refl⟩∘⟨ cancelˡ associator.isoˡ ⟩⊗⟨refl ⟩
          α⇒ ∘ (△ ⊕₁ id ∘ △) ⊕₁ id                  ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
          α⇒ ∘ (△ ⊕₁ id) ⊕₁ id ∘ △ ⊕₁ id            ≈⟨ extendʳ assoc-commute-from ⟩
          △ ⊕₁ id ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id              ≈⟨ refl⟩⊗⟨ ⊕.identity ⟩∘⟨refl ⟩
          △ ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id                    ∎

      lemma₂ :  △ ⊕₁ id {Dᵢ} ∘ fₒ ⊕₁ id ≈ (fₒ ⊕₁ fₒ) ⊕₁ id ∘ △ ⊕₁ id
      lemma₂ = begin
          △ ⊕₁ id ∘ fₒ ⊕₁ id          ≈⟨ merge₁ʳ ⟩
          (△ ∘ fₒ) ⊕₁ id              ≈⟨ ⇒△ ⟩⊗⟨refl ⟩
          (fₒ ⊕₁ fₒ ∘ △) ⊕₁ id        ≈⟨ split₁ʳ ⟩
          (fₒ ⊕₁ fₒ) ⊕₁ id ∘ △ ⊕₁ id  ∎

      ≈ᵢ : fᵢ ∘ id ⊕₁ ((gᵢ ∘ id ⊕₁ (hᵢ ∘ gₒ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id) ∘ fₒ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
        ≈ (fᵢ ∘ id ⊕₁ (gᵢ ∘ fₒ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id) ∘ id ⊕₁ (hᵢ ∘ (gₒ ∘ fₒ) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
      ≈ᵢ = begin
          fᵢ ∘ id ⊕₁ ((gᵢ ∘ id ⊕₁ term₂ ∘ α⇒ ∘ △ ⊕₁ id) ∘ fₒ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ extendˡ (extendˡ assoc) ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ ((gᵢ ∘ id ⊕₁ term₂ ∘ α⇒) ∘ △ ⊕₁ id ∘ fₒ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ lemma₂) ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ ((gᵢ ∘ id ⊕₁ term₂ ∘ α⇒) ∘ (fₒ ⊕₁ fₒ) ⊕₁ id ∘ △ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ extendˡ assoc ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ ((gᵢ ∘ id ⊕₁ term₂) ∘ α⇒ ∘ (fₒ ⊕₁ fₒ) ⊕₁ id ∘ △ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ extendʳ assoc-commute-from ) ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ ((gᵢ ∘ id ⊕₁ term₂) ∘ fₒ ⊕₁ fₒ ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ (gᵢ ∘ id ⊕₁ term₂ ∘ fₒ ⊕₁ fₒ ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ pullˡ merge₂ˡ ) ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ (gᵢ ∘ fₒ ⊕₁ (term₂ ∘ fₒ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ refl⟩⊗⟨ pullʳ merge₁ʳ ⟩∘⟨refl) ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ (gᵢ ∘ fₒ ⊕₁ term₁ ∘ α⇒ ∘ △ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ assoc ⟩∘⟨refl ⟨
          fᵢ ∘ id ⊕₁ ((gᵢ ∘ fₒ ⊕₁ term₁) ∘ α⇒ ∘ △ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ extendˡ assoc ⟩∘⟨refl ⟨
          fᵢ ∘ id ⊕₁ ((gᵢ ∘ fₒ ⊕₁ term₁ ∘ α⇒) ∘ △ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
          fᵢ ∘ id ⊕₁ (gᵢ ∘ fₒ ⊕₁ term₁ ∘ α⇒) ∘ id ⊕₁ △ ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟨
          fᵢ ∘ id ⊕₁ (gᵢ ∘ fₒ ⊕₁ term₁ ∘ α⇒) ∘ α⇒ ∘ (id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ extendʳ (refl⟩⊗⟨ assoc ⟩∘⟨refl) ⟨
          fᵢ ∘ id ⊕₁ ((gᵢ ∘ fₒ ⊕₁ term₁) ∘ α⇒) ∘ α⇒ ∘ (id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
          fᵢ ∘ id ⊕₁ (gᵢ ∘ fₒ ⊕₁ term₁) ∘ id ⊕₁ α⇒ ∘ α⇒ ∘ (id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ insertˡ associator.isoʳ ⟩⊗⟨refl ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ (gᵢ ∘ fₒ ⊕₁ term₁) ∘ id ⊕₁ α⇒ ∘ α⇒ ∘ (α⇒ ∘ α⇐ ∘ id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ʳ ⟩
          fᵢ ∘ id ⊕₁ (gᵢ ∘ fₒ ⊕₁ term₁) ∘ id ⊕₁ α⇒ ∘ α⇒ ∘ α⇒ ⊕₁ id ∘ (α⇐ ∘ id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟨
          fᵢ ∘ id ⊕₁ (gᵢ ∘ fₒ ⊕₁ term₁) ∘ id ⊕₁ α⇒ ∘ (α⇒ ∘ α⇒ ⊕₁ id) ∘ (α⇐ ∘ id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ pentagon ⟩
          fᵢ ∘ id ⊕₁ (gᵢ ∘ fₒ ⊕₁ term₁) ∘ α⇒ ∘ α⇒ ∘ (α⇐ ∘ id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ pushʳ serialize₁₂ ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ (term₃ ∘ id ⊕₁ term₁) ∘ α⇒ ∘ α⇒ ∘ (α⇐ ∘ id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
          fᵢ ∘ id ⊕₁ term₃ ∘ id ⊕₁ id ⊕₁ term₁ ∘ α⇒ ∘ α⇒ ∘ (α⇐ ∘ id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟨
          fᵢ ∘ id ⊕₁ term₃ ∘ α⇒ ∘ (id ⊕₁ id) ⊕₁ term₁ ∘ α⇒ ∘ (α⇐ ∘ id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊕.identity ⟩⊗⟨refl ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ term₃ ∘ α⇒ ∘ id ⊕₁ term₁ ∘ α⇒ ∘ (α⇐ ∘ id ⊕₁ △) ⊕₁ id ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ lemma₁ ⟩
          fᵢ ∘ id ⊕₁ term₃ ∘ α⇒ ∘ id ⊕₁ term₁ ∘ △ ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (Equiv.sym serialize₂₁ ○ serialize₁₂) ⟩
          fᵢ ∘ id ⊕₁ term₃ ∘ α⇒ ∘ △ ⊕₁ id ∘ id ⊕₁ term₁ ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟨
          fᵢ ∘ id ⊕₁ term₃ ∘ (α⇒ ∘ △ ⊕₁ id) ∘ id ⊕₁ term₁ ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ refl⟩∘⟨ assoc ⟨
          fᵢ ∘ (id ⊕₁ term₃ ∘ α⇒ ∘ △ ⊕₁ id) ∘ id ⊕₁ term₁ ∘ α⇒ ∘ △ ⊕₁ id
              ≈⟨ assoc ⟨
          (fᵢ ∘ id ⊕₁ term₃ ∘ α⇒ ∘ △ ⊕₁ id) ∘ id ⊕₁ term₁ ∘ α⇒ ∘ △ ⊕₁ id ∎

  ⌻-identityˡ : {A B : Box} {f : WiringDiagram A B} → id-⧈ ⌻ f ≈-⧈ f
  ⌻-identityˡ {Aᵢ □ Aₒ} {Bᵢ □ Bₒ} {fᵢ ⧈ fₒ} = ≈ᵢ ⌸ identityˡ
    where
      open ⇒-Reasoning 𝒞
      open ⊗-Reasoning +-monoidal
      ≈ᵢ : fᵢ ∘ id ⊕₁ (p₂ ∘ fₒ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id ≈ fᵢ
      ≈ᵢ = begin
          fᵢ ∘ id ⊕₁ (p₂ ∘ fₒ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id             ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (p₂-⊕ ⟩∘⟨refl) ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ ((λ⇒ ∘ ! ⊕₁ id) ∘ fₒ ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ pullʳ merge₁ʳ ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ (λ⇒ ∘ (! ∘ fₒ) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id       ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ ⇒! ⟩⊗⟨refl) ⟩∘⟨refl ⟩
          fᵢ ∘ id ⊕₁ (λ⇒ ∘ ! ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id              ≈⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
          fᵢ ∘ id ⊕₁ λ⇒ ∘ id ⊕₁ ! ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟨
          fᵢ ∘ id ⊕₁ λ⇒ ∘ α⇒ ∘ (id ⊕₁ !) ⊕₁ id ∘ △ ⊕₁ id        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ˡ ⟩
          fᵢ ∘ id ⊕₁ λ⇒ ∘ α⇒ ∘ (id ⊕₁ ! ∘ △) ⊕₁ id              ≈⟨ refl⟩∘⟨ pullˡ triangle ⟩
          fᵢ ∘ ρ⇒ ⊕₁ id ∘ (id ⊕₁ ! ∘ △) ⊕₁ id                   ≈⟨ refl⟩∘⟨ merge₁ʳ ⟩
          fᵢ ∘ (ρ⇒ ∘ id ⊕₁ ! ∘ △) ⊕₁ id                         ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ △-identityʳ ) ⟩⊗⟨refl ⟩
          fᵢ ∘ (ρ⇒ ∘ ρ⇐) ⊕₁ id                                  ≈⟨ refl⟩∘⟨ unitorʳ.isoʳ ⟩⊗⟨refl  ⟩
          fᵢ ∘ id ⊕₁ id                                         ≈⟨ elimʳ ⊕.identity ⟩
          fᵢ                                                    ∎

  ⌻-identityʳ : {A B : Box} {f : WiringDiagram A B} → f ⌻ id-⧈ ≈-⧈ f
  ⌻-identityʳ {Aᵢ □ Aₒ} {Bᵢ □ Bₒ} {fᵢ ⧈ fₒ} = ≈ᵢ ⌸ identityʳ
    where
      open ⇒-Reasoning 𝒞
      open ⊗-Reasoning +-monoidal
      ≈ᵢ : p₂ ∘ id ⊕₁ (fᵢ ∘ id ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id ≈ fᵢ
      ≈ᵢ = begin
          p₂ ∘ id ⊕₁ (fᵢ ∘ id ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id             ≈⟨ p₂-⊕ ⟩∘⟨refl ⟩
          (λ⇒ ∘ ! ⊕₁ id) ∘ id ⊕₁ (fᵢ ∘ id ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ elimʳ ⊕.identity ⟩∘⟨refl ⟩
          (λ⇒ ∘ ! ⊕₁ id) ∘ id ⊕₁ fᵢ ∘ α⇒ ∘ △ ⊕₁ id              ≈⟨ pullˡ (pullʳ (Equiv.sym serialize₁₂)) ⟩
          (λ⇒ ∘ ! ⊕₁ fᵢ) ∘ α⇒ ∘ △ ⊕₁ id                         ≈⟨ pullʳ (pushˡ serialize₂₁) ⟩
          λ⇒ ∘ id ⊕₁ fᵢ ∘ ! ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ ⊕.identity ⟩∘⟨refl ⟨
          λ⇒ ∘ id ⊕₁ fᵢ ∘ ! ⊕₁ id ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟨
          λ⇒ ∘ id ⊕₁ fᵢ ∘ α⇒ ∘ (! ⊕₁ id) ⊕₁ id ∘ △ ⊕₁ id        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ʳ ⟩
          λ⇒ ∘ id ⊕₁ fᵢ ∘ α⇒ ∘ (! ⊕₁ id ∘ △) ⊕₁ id              ≈⟨ extendʳ unitorˡ-commute-from ⟩
          fᵢ ∘ λ⇒ ∘ α⇒ ∘ (! ⊕₁ id ∘ △) ⊕₁ id                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ △-identityˡ ⟩⊗⟨refl ⟩
          fᵢ ∘ λ⇒ ∘ α⇒ ∘ λ⇐ ⊕₁ id                               ≈⟨ refl⟩∘⟨ pullˡ coherence₁ ⟩
          fᵢ ∘ λ⇒ ⊕₁ id ∘ λ⇐ ⊕₁ id                              ≈⟨ refl⟩∘⟨ merge₁ʳ ⟩
          fᵢ ∘ (λ⇒ ∘ λ⇐) ⊕₁ id                                  ≈⟨ refl⟩∘⟨ unitorˡ.isoʳ ⟩⊗⟨refl ⟩
          fᵢ ∘ id ⊕₁ id                                         ≈⟨ elimʳ ⊕.identity ⟩
          fᵢ                                                    ∎

-- The category of directed wiring diagrams
DWD : Category o ℓ e
DWD = categoryHelper record
    { Obj = Box
    ; _⇒_ = WiringDiagram
    ; _≈_ = _≈-⧈_
    ; id = id-⧈
    ; _∘_ = _⌻_
    ; assoc = ⌻-assoc
    ; identityˡ = ⌻-identityˡ
    ; identityʳ = ⌻-identityʳ
    ; equiv = ≈-isEquiv
    ; ∘-resp-≈ = ⌻-resp-≈
    }

-- Every pair of morphisms in 𝒞 gives a wiring diagram
Pulsh : Bifunctor op 𝒞 DWD
Pulsh = record
    { F₀ = λ (A , B) → A □ B
    ; F₁ = λ (f , g) → pulsh f g
    ; identity = elimˡ Equiv.refl ⌸ Equiv.refl
    ; homomorphism = λ { {A} {B} {C} {f , g} {f′ , g′} → homoᵢ g g′ f f′ ⌸ Equiv.refl }
    ; F-resp-≈ = λ (f≈f′ , g≈g′) → (f≈f′ ⟩∘⟨refl) ⌸ g≈g′
    }
  where
    open ⇒-Reasoning 𝒞
    open ⊗-Reasoning +-monoidal
    homoᵢ : {A B C D E F : Obj} (g : A ⇒ B) (g′ : B ⇒ C) (f : E ⇒ F) (f′ : D ⇒ E)
        → (f ∘ f′) ∘ p₂
        ≈ (f ∘ p₂) ∘ (id ⊕₁ ((f′ ∘ p₂) ∘ g ⊕₁ id)) ∘ α⇒ ∘ (△ ⊕₁ id)
    homoᵢ g g′ f f′ = begin
        (f ∘ f′) ∘ p₂                                                     ≈⟨ refl⟩∘⟨ p₂-⊕ ⟩
        (f ∘ f′) ∘ λ⇒ ∘ ! ⊕₁ id                                           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ insertˡ p₁∘△ ⟩⊗⟨refl  ⟩
        (f ∘ f′) ∘ λ⇒ ∘ (p₁ ∘ △ ∘ !) ⊕₁ id                                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (ρ⇒≈p₁ ⟩∘⟨refl) ⟩⊗⟨refl ⟨
        (f ∘ f′) ∘ λ⇒ ∘ (ρ⇒ ∘ △ ∘ !) ⊕₁ id                                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ ⇒△) ⟩⊗⟨refl ⟩
        (f ∘ f′) ∘ λ⇒ ∘ (ρ⇒ ∘ ! ⊕₁ ! ∘ △) ⊕₁ id                           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩
        (f ∘ f′) ∘ λ⇒ ∘ ρ⇒ ⊕₁ id ∘ (! ⊕₁ ! ∘ △) ⊕₁ id                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ʳ ⟩
        (f ∘ f′) ∘ λ⇒ ∘ ρ⇒ ⊕₁ id ∘ (! ⊕₁ !) ⊕₁ id ∘ △ ⊕₁ id               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (Equiv.sym triangle) ⟩
        (f ∘ f′) ∘ λ⇒ ∘ id ⊕₁ λ⇒ ∘ α⇒ ∘ (! ⊕₁ !) ⊕₁ id ∘ △ ⊕₁ id          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
        (f ∘ f′) ∘ λ⇒ ∘ id ⊕₁ λ⇒ ∘ ! ⊕₁ ! ⊕₁ id ∘ α⇒ ∘ (△ ⊕₁ id)          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
        (f ∘ f′) ∘ λ⇒ ∘ ! ⊕₁ (λ⇒ ∘ ! ⊕₁ id) ∘ α⇒ ∘ (△ ⊕₁ id)              ≈⟨ pullʳ (extendʳ (Equiv.sym unitorˡ-commute-from)) ⟩
        f ∘ λ⇒ ∘ id ⊕₁ f′ ∘ ! ⊕₁ (λ⇒ ∘ ! ⊕₁ id) ∘ α⇒ ∘ (△ ⊕₁ id)          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
        f ∘ λ⇒ ∘ ! ⊕₁ (f′ ∘ λ⇒ ∘ ! ⊕₁ id) ∘ α⇒ ∘ (△ ⊕₁ id)                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ refl⟩∘⟨ ⇒! ⟩⊗⟨refl) ⟩∘⟨refl ⟨
        f ∘ λ⇒ ∘ ! ⊕₁ (f′ ∘ λ⇒ ∘ (! ∘ g) ⊕₁ id) ∘ α⇒ ∘ (△ ⊕₁ id)          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ pushʳ split₁ˡ) ⟩∘⟨refl ⟩
        f ∘ λ⇒ ∘ ! ⊕₁ (f′ ∘ (λ⇒ ∘ ! ⊕₁ id) ∘ g ⊕₁ id) ∘ α⇒ ∘ (△ ⊕₁ id)    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ pushˡ (refl⟩∘⟨ p₂-⊕) ⟩∘⟨refl ⟨
        f ∘ λ⇒ ∘ ! ⊕₁ ((f′ ∘ p₂) ∘ g ⊕₁ id) ∘ α⇒ ∘ (△ ⊕₁ id)              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
        f ∘ λ⇒ ∘ ! ⊕₁ id ∘ (id ⊕₁ ((f′ ∘ p₂) ∘ g ⊕₁ id)) ∘ α⇒ ∘ (△ ⊕₁ id) ≈⟨ pushʳ (pullˡ (Equiv.sym p₂-⊕)) ⟩
        (f ∘ p₂) ∘ (id ⊕₁ ((f′ ∘ p₂) ∘ g ⊕₁ id)) ∘ α⇒ ∘ (△ ⊕₁ id)         ∎
