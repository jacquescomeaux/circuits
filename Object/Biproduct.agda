{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

module Object.Biproduct {o ℓ e} (𝒞 : Category o ℓ e) where

import Categories.Morphism.Reasoning 𝒞 as ⇒-Reasoning

open import Categories.Object.Biproduct 𝒞 using () renaming (module Biproduct to Biproduct′)
open import Categories.Object.Biproduct 𝒞 public hiding (module Biproduct)
open import Morphism.Zero 𝒞 using (IsZero⇒)

open Category 𝒞

module Biproduct {A B : Obj} (BP : Biproduct A B) where

  open Biproduct′ BP public

  open ⇒-Reasoning
  open HomReasoning

  private

    permute⟩∘⟨refl : {C : Obj} {f : C ⇒ A⊕B} → i₁ ∘ π₁ ∘ i₂ ∘ π₂ ∘ f ≈ i₂ ∘ π₂ ∘ i₁ ∘ π₁ ∘ f
    permute⟩∘⟨refl = refl⟩∘⟨ assoc²εβ ○ extendʳ permute ○ refl⟩∘⟨ assoc²βε

    π₁i₂-constant : {C : Obj} (f g : C ⇒ B) → (π₁ ∘ i₂) ∘ f ≈ (π₁ ∘ i₂) ∘ g
    π₁i₂-constant f g = begin
        (π₁ ∘ i₂) ∘ f                                 ≈⟨ assoc ⟩
        π₁ ∘ i₂ ∘ f                                   ≈⟨ insertˡ π₁∘i₁≈id ⟩
        π₁ ∘ i₁ ∘ π₁ ∘ i₂ ∘ f                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ project₂ ⟨
        π₁ ∘ i₁ ∘ π₁ ∘ i₂ ∘ π₂ ∘ ⟨ π₁ ∘ i₂ ∘ g , f ⟩  ≈⟨ refl⟩∘⟨ permute⟩∘⟨refl ⟩
        π₁ ∘ i₂ ∘ π₂ ∘ i₁ ∘ π₁ ∘ ⟨ π₁ ∘ i₂ ∘ g , f ⟩  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ project₁ ⟩
        π₁ ∘ i₂ ∘ π₂ ∘ i₁ ∘ π₁ ∘ i₂ ∘ g               ≈⟨ refl⟩∘⟨ permute⟩∘⟨refl ⟨
        π₁ ∘ i₁ ∘ π₁ ∘ i₂ ∘ π₂ ∘ i₂ ∘ g               ≈⟨ cancelˡ π₁∘i₁≈id ⟩
        π₁ ∘ i₂ ∘ π₂ ∘ i₂ ∘ g                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ π₂∘i₂≈id ⟩
        π₁ ∘ i₂ ∘ g                                   ≈⟨ sym-assoc ⟩
        (π₁ ∘ i₂) ∘ g                                 ∎

    π₁i₂-coconstant : {C : Obj} (f g : A ⇒ C) → f ∘ π₁ ∘ i₂ ≈ g ∘ π₁ ∘ i₂
    π₁i₂-coconstant f g = begin
        f ∘ π₁ ∘ i₂                                   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ introʳ π₂∘i₂≈id ⟩
        f ∘ π₁ ∘ i₂ ∘ π₂ ∘ i₂                         ≈⟨ pushˡ (Equiv.sym inject₁) ⟩
        [ f , g ∘ π₁ ∘ i₂ ] ∘ i₁ ∘ π₁ ∘ i₂ ∘ π₂ ∘ i₂  ≈⟨ refl⟩∘⟨ permute⟩∘⟨refl ⟩
        [ f , g ∘ π₁ ∘ i₂ ] ∘ i₂ ∘ π₂ ∘ i₁ ∘ π₁ ∘ i₂  ≈⟨ extendʳ inject₂ ⟩
        g ∘ (π₁ ∘ i₂) ∘ π₂ ∘ i₁ ∘ π₁ ∘ i₂             ≈⟨ refl⟩∘⟨ pullʳ (Equiv.sym permute⟩∘⟨refl) ⟩
        g ∘ π₁ ∘ i₁ ∘ π₁ ∘ i₂ ∘ π₂ ∘ i₂               ≈⟨ refl⟩∘⟨ cancelˡ π₁∘i₁≈id ⟩
        g ∘ π₁ ∘ i₂ ∘ π₂ ∘ i₂                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimʳ π₂∘i₂≈id ⟩
        g ∘ π₁ ∘ i₂                                   ∎

    π₂i₁-coconstant : {C : Obj} (f g : B ⇒ C) → f ∘ π₂ ∘ i₁ ≈ g ∘ π₂ ∘ i₁
    π₂i₁-coconstant f g = begin
        f ∘ π₂ ∘ i₁                                   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ introʳ π₁∘i₁≈id ⟩
        f ∘ π₂ ∘ i₁ ∘ π₁ ∘ i₁                         ≈⟨ pushˡ (Equiv.sym inject₂) ⟩
        [ g ∘ π₂ ∘ i₁ , f ] ∘ i₂ ∘ π₂ ∘ i₁ ∘ π₁ ∘ i₁  ≈⟨ refl⟩∘⟨ permute⟩∘⟨refl ⟨
        [ g ∘ π₂ ∘ i₁ , f ] ∘ i₁ ∘ π₁ ∘ i₂ ∘ π₂ ∘ i₁  ≈⟨ extendʳ inject₁ ⟩
        g ∘ (π₂ ∘ i₁) ∘ π₁ ∘ i₂ ∘ π₂ ∘ i₁             ≈⟨ refl⟩∘⟨ pullʳ permute⟩∘⟨refl ⟩
        g ∘ π₂ ∘ i₂ ∘ π₂ ∘ i₁ ∘ π₁ ∘ i₁               ≈⟨ refl⟩∘⟨ cancelˡ π₂∘i₂≈id ⟩
        g ∘ π₂ ∘ i₁ ∘ π₁ ∘ i₁                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimʳ π₁∘i₁≈id ⟩
        g ∘ π₂ ∘ i₁                                   ∎

    π₂i₁-constant : {C : Obj} (f g : C ⇒ A) → (π₂ ∘ i₁) ∘ f ≈ (π₂ ∘ i₁) ∘ g
    π₂i₁-constant f g = begin
        (π₂ ∘ i₁) ∘ f                                 ≈⟨ assoc ⟩
        π₂ ∘ i₁ ∘ f                                   ≈⟨ insertˡ π₂∘i₂≈id ⟩
        π₂ ∘ i₂ ∘ π₂ ∘ i₁ ∘ f                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ project₁ ⟨
        π₂ ∘ i₂ ∘ π₂ ∘ i₁ ∘ π₁ ∘ ⟨ f , π₂ ∘ i₁ ∘ g ⟩  ≈⟨ refl⟩∘⟨ permute⟩∘⟨refl ⟨
        π₂ ∘ i₁ ∘ π₁ ∘ i₂ ∘ π₂ ∘ ⟨ f , π₂ ∘ i₁ ∘ g ⟩  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ project₂ ⟩
        π₂ ∘ i₁ ∘ π₁ ∘ i₂ ∘ π₂ ∘ i₁ ∘ g               ≈⟨ refl⟩∘⟨ permute⟩∘⟨refl ⟩
        π₂ ∘ i₂ ∘ π₂ ∘ i₁ ∘ π₁ ∘ i₁ ∘ g               ≈⟨ cancelˡ π₂∘i₂≈id ⟩
        π₂ ∘ i₁ ∘ π₁ ∘ i₁ ∘ g                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ π₁∘i₁≈id ⟩
        π₂ ∘ i₁ ∘ g                                   ≈⟨ sym-assoc ⟩
        (π₂ ∘ i₁) ∘ g                                 ∎

  𝟎⇒ : A ⇒ B
  𝟎⇒ = π₂ ∘ i₁

  𝟎⇐ : B ⇒ A
  𝟎⇐ = π₁ ∘ i₂

  π₁∘i₂-isZero : IsZero⇒ (π₁ ∘ i₂)
  π₁∘i₂-isZero = record
      { constant = π₁i₂-constant
      ; coconstant = π₁i₂-coconstant
      }

  π₂∘i₁-isZero : IsZero⇒ (π₂ ∘ i₁)
  π₂∘i₁-isZero = record
      { constant = π₂i₁-constant
      ; coconstant = π₂i₁-coconstant
      }
