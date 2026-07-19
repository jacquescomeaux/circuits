{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Dagger.Semiadditive using (SemiadditiveDagger; IdempotentSemiadditiveDagger)
open import Level using (Level)

module Data.WiringDiagram.Equalities {o ℓ e : Level} {𝒞 : Category o ℓ e} (S : IdempotentSemiadditiveDagger 𝒞) where

module S = IdempotentSemiadditiveDagger S

import Categories.Morphism.Reasoning 𝒞 as ⇒-Reasoning

open import Categories.Category.Monoidal using (module Monoidal)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Data.WiringDiagram.Core S.semiadditiveDagger using (_⌸_; _⌻_; _≈-⧈_; ≈-trans; loop; push; pull; merge; split)

open Category 𝒞

open Equiv
open HomReasoning
open IdempotentSemiadditiveDagger S
open ⇒-Reasoning

⟨π₁,id⟩ : {A B : Obj} → ⟨ π₁ {A} {B} , id ⟩ ≈ assocˡ ∘ Δ ×₁ id
⟨π₁,id⟩ = begin
    ⟨ π₁ , id ⟩                   ≈⟨ ⟨⟩-congˡ η ⟨
    ⟨ π₁ , ⟨ π₁ , π₂ ⟩ ⟩          ≈⟨ assocˡ∘⟨⟩ ⟨
    assocˡ ∘ ⟨ ⟨ π₁ , π₁ ⟩ , π₂ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ Δ∘ identityˡ ⟨
    assocˡ ∘ Δ ×₁ id              ∎

loop∘loop : {A : Obj} → loop ⌻ loop ≈-⧈ loop {A}
loop∘loop {A} = ≈ᵢ ⌸ identity²
  where
    ≈ᵢ : ∇ ∘ ⟨ π₁ , (∇ ∘ id ×₁ id) ⟩ ≈ ∇
    ≈ᵢ = begin
        ∇ ∘ ⟨ π₁ , ∇ ∘ id ×₁ id ⟩         ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (sym identityˡ) (refl⟩∘⟨ id×₁id) ⟩
        ∇ ∘ ⟨ id ∘ π₁ , ∇ ∘ id ⟩          ≈⟨ refl⟩∘⟨ ×₁∘⟨⟩ ⟨
        ∇ ∘ id ×₁ ∇ ∘ ⟨ π₁ , id ⟩         ≈⟨ refl⟩∘⟨ pushʳ ⟨π₁,id⟩ ⟩
        ∇ ∘ (id ×₁ ∇ ∘ assocˡ) ∘ Δ ×₁ id  ≈⟨ extendʳ ∇-assoc-×₁ ⟨
        ∇ ∘ ∇ ×₁ id ∘ Δ ×₁ id             ≈⟨ refl⟩∘⟨ first∘first ⟩
        ∇ ∘ (∇ ∘ Δ) ×₁ id                 ≈⟨ refl⟩∘⟨ first-cong ∇∘Δ ⟩
        ∇ ∘ id ×₁ id                      ≈⟨ elimʳ id×₁id ⟩
        ∇                                 ∎

loop∘push∘loop≈merge : {A B : Obj} (f : A ⇒ B) → id ≤ ((f †) ∘ f) → loop ⌻ push f ⌻ loop ≈-⧈ merge f
loop∘push∘loop≈merge f id≤f†∘f = ≈ᵢ ⌸ (identityˡ ○ identityʳ)
  where
    ≈ᵢ  : (∇ ∘ ⟨ π₁ , (f † ∘ π₂) ∘ id ×₁ id ⟩) ∘ ⟨ π₁ , ∇ ∘ (f ∘ id) ×₁ id ⟩
        ≈ f † ∘ ∇ ∘ f ×₁ id
    ≈ᵢ = begin
        (∇ ∘ ⟨ π₁ , (f † ∘ π₂) ∘ id ×₁ id ⟩) ∘ ⟨ π₁ , ∇ ∘ (f ∘ id) ×₁ id ⟩    ≈⟨ pullʳ (⟨⟩-congˡ (elimʳ id×₁id) ⟩∘⟨ ⟨⟩-congˡ (refl⟩∘⟨ first-cong identityʳ)) ⟩
        ∇ ∘ ⟨ π₁ , f † ∘ π₂ ⟩ ∘ ⟨ π₁ , ∇ ∘ f ×₁ id ⟩                          ≈⟨ refl⟩∘⟨ ⟨⟩∘ ⟩
        ∇ ∘ ⟨ π₁ ∘ ⟨ π₁ , ∇ ∘ f ×₁ id ⟩ , (f † ∘ π₂) ∘ ⟨ π₁ , ∇ ∘ f ×₁ id ⟩ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ project₁ (pullʳ project₂) ⟩
        ∇ ∘ ⟨ π₁ , f † ∘ ∇ ∘ f ×₁ id ⟩                                        ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ (extendʳ ⇒∇-×₁) ⟩
        ∇ ∘ ⟨ π₁ , ∇ ∘ (f †) ×₁ (f †) ∘ f ×₁ id ⟩                             ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ (refl⟩∘⟨ ×₁∘first) ⟩
        ∇ ∘ ⟨ π₁ , ∇ ∘ (f † ∘ f) ×₁ (f †) ⟩                                   ≈⟨ refl⟩∘⟨ second∘⟨⟩ ⟨
        ∇ ∘ id ×₁ ∇ ∘ ⟨ π₁ , (f † ∘ f) ×₁ (f †) ⟩                             ≈⟨ refl⟩∘⟨ pushʳ (sym assocˡ∘⟨⟩) ⟩
        ∇ ∘ (id ×₁ ∇ ∘ assocˡ) ∘ ⟨ ⟨ π₁ , (f † ∘ f) ∘ π₁ ⟩ , f † ∘ π₂ ⟩       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-congʳ (⟨⟩-congʳ identityˡ) ⟨
        ∇ ∘ (id ×₁ ∇ ∘ assocˡ) ∘ ⟨ ⟨ id ∘ π₁ , (f † ∘ f) ∘ π₁ ⟩ , f † ∘ π₂ ⟩  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟨
        ∇ ∘ (id ×₁ ∇ ∘ assocˡ) ∘ ⟨ id , f † ∘ f ⟩ ×₁ (f †)                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ×₁-congʳ ×₁∘Δ ⟨
        ∇ ∘ (id ×₁ ∇ ∘ assocˡ) ∘ (id ×₁ (f † ∘ f) ∘ Δ) ×₁ (f †)               ≈⟨ extendʳ ∇-assoc-×₁ ⟨
        ∇ ∘ (∇ ×₁ id) ∘ (id ×₁ (f † ∘ f) ∘ Δ) ×₁ (f †)                        ≈⟨ refl⟩∘⟨ first∘×₁ ⟩
        ∇ ∘ (id + (f † ∘ f)) ×₁ (f †)                                         ≈⟨ refl⟩∘⟨ ×₁-congʳ id≤f†∘f ⟩
        ∇ ∘ (f † ∘ f) ×₁ (f †)                                                ≈⟨ refl⟩∘⟨ ×₁∘first ⟨
        ∇ ∘ (f †) ×₁ (f †) ∘ f ×₁ id                                          ≈⟨ extendʳ ⇒∇-×₁ ⟨
        f † ∘ ∇ ∘ f ×₁ id                                                     ∎

merge≈loop∘push : {A B : Obj} (f : A ⇒ B) → merge f ≈-⧈ loop ⌻ push f
merge≈loop∘push f = ≈ᵢ ⌸ Equiv.sym identityˡ
  where
    ≈ᵢ  : f † ∘ ∇ ∘ f ×₁ id ≈ (f † ∘ π₂) ∘ ⟨ π₁ , ∇ ∘ f ×₁ id ⟩
    ≈ᵢ = begin
        f † ∘ ∇ ∘ f ×₁ id                 ≈⟨ pushʳ (sym project₂)  ⟩
        (f † ∘ π₂) ∘ ⟨ π₁ , ∇ ∘ f ×₁ id ⟩ ∎

loop∘pull∘loop≈split : {A B : Obj} (f : A ⇒ B) → (f ∘ (f †)) ≤ id → loop ⌻ pull f ⌻ loop ≈-⧈ split f
loop∘pull∘loop≈split f f∘f†≤id = ≈ᵢ ⌸ (identityˡ ○ identityʳ)
  where
    ≈ᵢ  : (∇ ∘ ⟨ π₁ , (f ∘ π₂) ∘ id ×₁ id ⟩) ∘ ⟨ π₁ , ∇ ∘ (f † ∘ id) ×₁ id ⟩ ≈ ∇ ∘ id ×₁ f
    ≈ᵢ = begin
        (∇ ∘ ⟨ π₁ , (f ∘ π₂) ∘ id ×₁ id ⟩) ∘ ⟨ π₁ , ∇ ∘ (f † ∘ id) ×₁ id ⟩          ≈⟨ pullʳ (⟨⟩-congˡ (elimʳ id×₁id) ⟩∘⟨ ⟨⟩-congˡ (refl⟩∘⟨ first-cong identityʳ)) ⟩
        ∇ ∘ ⟨ π₁ , (f ∘ π₂) ⟩ ∘ ⟨ π₁ , ∇ ∘ (f †) ×₁ id ⟩                            ≈⟨ refl⟩∘⟨ ⟨⟩∘ ⟩
        ∇ ∘ ⟨ π₁ ∘ ⟨ π₁ , ∇ ∘ (f †) ×₁ id ⟩ , (f ∘ π₂) ∘ ⟨ π₁ , ∇ ∘ (f †) ×₁ id ⟩ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ project₁ (pullʳ project₂) ⟩
        ∇ ∘ ⟨ π₁ , f ∘ ∇ ∘ (f †) ×₁ id ⟩                                            ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ (extendʳ ⇒∇-×₁) ⟩
        ∇ ∘ ⟨ π₁ , ∇ ∘ f ×₁ f ∘ (f †) ×₁ id ⟩                                       ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ (refl⟩∘⟨ ×₁∘first) ⟩
        ∇ ∘ ⟨ π₁ , ∇ ∘ (f ∘ f †) ×₁ f ⟩                                             ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ identityʳ ⟨
        ∇ ∘ ⟨ π₁ , (∇ ∘ (f ∘ f †) ×₁ f) ∘ id ⟩                                      ≈⟨ refl⟩∘⟨ second∘⟨⟩ ⟨
        ∇ ∘ id ×₁ (∇ ∘ (f ∘ f †) ×₁ f) ∘ ⟨ π₁ , id ⟩                                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-congˡ η ⟨
        ∇ ∘ id ×₁ (∇ ∘ (f ∘ f †) ×₁ f) ∘ ⟨ π₁ , ⟨ π₁ , π₂ ⟩ ⟩                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⟨⟩ ⟨
        ∇ ∘ id ×₁ (∇ ∘ (f ∘ f †) ×₁ f) ∘ assocˡ ∘ ⟨ ⟨ π₁ , π₁ ⟩ , π₂ ⟩              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-cong₂ Δ∘ identityˡ ⟨
        ∇ ∘ id ×₁ (∇ ∘ (f ∘ f †) ×₁ f) ∘ assocˡ ∘ Δ ×₁ id                           ≈⟨ refl⟩∘⟨ pushˡ (sym second∘×₁) ⟩
        ∇ ∘ id ×₁ ∇ ∘ id ×₁ (f ∘ f †) ×₁ f ∘ assocˡ ∘ Δ ×₁ id                       ≈⟨ refl⟩∘⟨ pushʳ (extendʳ (sym assocˡ∘×₁)) ⟩
        ∇ ∘ (id ×₁ ∇ ∘ assocˡ) ∘ (id ×₁ (f ∘ f †)) ×₁ f ∘ Δ ×₁ id                   ≈⟨ extendʳ ∇-assoc-×₁ ⟨
        ∇ ∘ ∇ ×₁ id ∘ (id ×₁ (f ∘ f †)) ×₁ f ∘ Δ ×₁ id                              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ×₁∘first ⟩
        ∇ ∘ ∇ ×₁ id ∘ (id ×₁ (f ∘ f †) ∘ Δ) ×₁ f                                    ≈⟨ refl⟩∘⟨ first∘×₁ ⟩
        ∇ ∘ (id + (f ∘ f †)) ×₁ f                                                   ≈⟨ refl⟩∘⟨ ×₁-congʳ (+-comm id (f ∘ f †)) ⟩
        ∇ ∘ ((f ∘ f †) + id) ×₁ f                                                   ≈⟨ refl⟩∘⟨ ×₁-congʳ f∘f†≤id ⟩
        ∇ ∘ id ×₁ f                                                                 ∎

split≈pull∘loop : {A B : Obj} (f : A ⇒ B) → split f ≈-⧈ pull f ⌻ loop
split≈pull∘loop f = ≈ᵢ ⌸ Equiv.sym identityʳ
  where
    ≈ᵢ  : ∇ ∘ id ×₁ f
        ≈ ∇ ∘ ⟨ π₁ , (f ∘ π₂) ∘ id ×₁ id ⟩
    ≈ᵢ = begin
        ∇ ∘ id ×₁ f                       ≈⟨ refl⟩∘⟨ ⟨⟩-congʳ identityˡ ⟩
        ∇ ∘ ⟨ π₁ , f ∘ π₂ ⟩               ≈⟨ refl⟩∘⟨ ⟨⟩-congˡ (introʳ id×₁id) ⟩
        ∇ ∘ ⟨ π₁ , (f ∘ π₂) ∘ id ×₁ id ⟩  ∎

loop∘push∘loop : {A B : Obj} (f : A ⇒ B) → id ≤ ((f †) ∘ f) → loop ⌻ push f ⌻ loop ≈-⧈ loop ⌻ push f
loop∘push∘loop f id≤f†∘f = ≈-trans (loop∘push∘loop≈merge f id≤f†∘f) (merge≈loop∘push f)

loop∘pull∘loop : {A B : Obj} → (f : A ⇒ B) → (f ∘ (f †)) ≤ id → loop ⌻ pull f ⌻ loop ≈-⧈ pull f ⌻ loop
loop∘pull∘loop f f∘f†≤id = ≈-trans (loop∘pull∘loop≈split f f∘f†≤id) (split≈pull∘loop f)
