{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Dagger.Semiadditive using (SemiadditiveDagger)
open import Level using (Level)

module Data.WiringDiagram.Directed
    {o ℓ e : Level}
    {𝒞 : Category o ℓ e}
    (S : SemiadditiveDagger 𝒞)
  where

import Categories.Morphism.Reasoning 𝒞 as ⇒-Reasoning

open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Data.Product using (_,_)
open import Data.WiringDiagram.Core S using (Box; WiringDiagram; _≈-⧈_; _□_; _⧈_; _⌸_; id-⧈; _⌻_; ≈-isEquiv; pulsh)

open Category 𝒞
open SemiadditiveDagger S

private

  ⌻-resp-≈ : {A B C : Box} {f h : WiringDiagram B C} {g i : WiringDiagram A B} → f ≈-⧈ h → g ≈-⧈ i → f ⌻ g ≈-⧈ h ⌻ i
  ⌻-resp-≈ {A} {B} {C} {fᵢ ⧈ fₒ} {hᵢ ⧈ hₒ} {gᵢ ⧈ gₒ} {iᵢ ⧈ iₒ} (fᵢ≈hᵢ ⌸ fₒ≈hₒ) (gᵢ≈iᵢ ⌸ gₒ≈iₒ) = ≈ᵢ ⌸ ∘-resp-≈ fₒ≈hₒ gₒ≈iₒ
    where
      open HomReasoning
      ≈ᵢ : gᵢ ∘ ⟨ π₁ , fᵢ ∘ gₒ ×₁ id ⟩
         ≈ iᵢ ∘ ⟨ π₁ , hᵢ ∘ iₒ ×₁ id ⟩
      ≈ᵢ = gᵢ≈iᵢ ⟩∘⟨ ⟨⟩-congˡ (fᵢ≈hᵢ ⟩∘⟨ first-cong gₒ≈iₒ)

  ⌻-assoc : {A B C D : Box} {f : WiringDiagram A B} {g : WiringDiagram B C} {h : WiringDiagram C D} → (h ⌻ g) ⌻ f ≈-⧈ h ⌻ (g ⌻ f)
  ⌻-assoc {Aᵢ □ Aₒ} {Bᵢ □ Bₒ} {Cᵢ □ Cₒ} {Dᵢ □ Dₒ} {fᵢ ⧈ fₒ} {gᵢ ⧈ gₒ} {hᵢ ⧈ hₒ} = ≈ᵢ ⌸ assoc
    where
      open HomReasoning
      open ⇒-Reasoning
      open Equiv
      ≈ᵢ  : fᵢ ∘ ⟨ π₁ , (gᵢ ∘ ⟨ π₁ , hᵢ ∘ gₒ ×₁ id ⟩) ∘ fₒ ×₁ id ⟩
          ≈ (fᵢ ∘ ⟨ π₁ , gᵢ ∘ fₒ ×₁ id ⟩) ∘ ⟨ π₁ , hᵢ ∘ (gₒ ∘ fₒ) ×₁ id ⟩
      ≈ᵢ = begin
          fᵢ ∘ ⟨ π₁ , (gᵢ ∘ ⟨ π₁ , hᵢ ∘ gₒ ×₁ id ⟩) ∘ fₒ ×₁ id ⟩            ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ (pullʳ ⟨⟩∘) ⟩
          fᵢ ∘ ⟨ π₁ , gᵢ ∘ ⟨ π₁ ∘ fₒ ×₁ id , (hᵢ ∘ gₒ ×₁ id) ∘ fₒ ×₁ id ⟩ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ (refl⟩∘⟨ ⟨⟩-cong₂ π₁∘×₁ (pullʳ first∘first)) ⟩
          fᵢ ∘ ⟨ π₁ , gᵢ ∘ ⟨ fₒ ∘ π₁ , hᵢ ∘ (gₒ ∘ fₒ) ×₁ id ⟩ ⟩             ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ project₁ (pullʳ first∘⟨⟩) ⟨
          fᵢ ∘ ⟨ π₁ ∘ ⟨ π₁ , _ ⟩ , (gᵢ ∘ fₒ ×₁ id) ∘ ⟨ π₁ , _ ⟩ ⟩           ≈⟨ pushʳ (sym ⟨⟩∘) ⟩
          (fᵢ ∘ ⟨ π₁ , gᵢ ∘ fₒ ×₁ id ⟩) ∘ ⟨ π₁ , hᵢ ∘ (gₒ ∘ fₒ) ×₁ id ⟩     ∎

  ⌻-identityˡ : {A B : Box} {f : WiringDiagram A B} → id-⧈ ⌻ f ≈-⧈ f
  ⌻-identityˡ {Aᵢ □ Aₒ} {Bᵢ □ Bₒ} {fᵢ ⧈ fₒ} = ≈ᵢ ⌸ identityˡ
    where
      open HomReasoning
      open ⇒-Reasoning
      ≈ᵢ : fᵢ ∘ ⟨ π₁ , π₂ ∘ fₒ ×₁ id ⟩ ≈ fᵢ
      ≈ᵢ = begin
          fᵢ ∘ ⟨ π₁ , π₂ ∘ fₒ ×₁ id ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ π₂∘first ⟩
          fᵢ ∘ ⟨ π₁ , π₂ ⟩            ≈⟨ elimʳ η ⟩
          fᵢ ∎

  ⌻-identityʳ : {A B : Box} {f : WiringDiagram A B} → f ⌻ id-⧈ ≈-⧈ f
  ⌻-identityʳ {Aᵢ □ Aₒ} {Bᵢ □ Bₒ} {fᵢ ⧈ fₒ} = ≈ᵢ ⌸ identityʳ
    where
      open HomReasoning
      open ⇒-Reasoning
      ≈ᵢ : π₂ ∘ ⟨ π₁ , fᵢ ∘ id ×₁ id ⟩  ≈ fᵢ
      ≈ᵢ = begin
          π₂ ∘ ⟨ π₁ , fᵢ ∘ id ×₁ id ⟩ ≈⟨ project₂ ⟩
          fᵢ ∘ id ×₁ id               ≈⟨ elimʳ id×₁id ⟩
          fᵢ ∎

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
    open HomReasoning
    open ⇒-Reasoning
    open Equiv
    homoᵢ
        : {A B C D E F : Obj} (g : A ⇒ B) (g′ : B ⇒ C) (f : E ⇒ F) (f′ : D ⇒ E)
        → (f ∘ f′) ∘ π₂ ≈ (f ∘ π₂) ∘ ⟨ π₁ , (f′ ∘ π₂) ∘ g ×₁ id ⟩
    homoᵢ g g′ f f′ = begin
        (f ∘ f′) ∘ π₂                           ≈⟨ pullʳ (pushʳ (sym π₂∘first)) ⟩
        f ∘ (f′ ∘ π₂) ∘ g ×₁ id                 ≈⟨ pushʳ (sym project₂) ⟩
        (f ∘ π₂) ∘ ⟨ π₁ , (f′ ∘ π₂) ∘ g ×₁ id ⟩ ∎
