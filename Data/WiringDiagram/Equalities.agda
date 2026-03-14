{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Dagger.Semiadditive using (IdempotentSemiadditiveDagger)
open import Level using (Level)

module Data.WiringDiagram.Equalities {o ℓ e : Level} {𝒞 : Category o ℓ e} (S : IdempotentSemiadditiveDagger 𝒞) where

import Categories.Category.Monoidal.Properties as ⊗-Properties
import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Categories.Category.Monoidal using (module Monoidal)
open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Data.WiringDiagram.Core S using (_⌸_; _⌻_; _≈-⧈_; ≈-trans; loop; push; pull; merge; split)

open Category 𝒞
open IdempotentSemiadditiveDagger S
open Monoidal +-monoidal using (module unitorˡ; module unitorʳ; triangle; assoc-commute-from; unitorˡ-commute-from)
open Shorthands +-monoidal using (α⇒; α⇐; λ⇒; λ⇐; ρ⇒; ρ⇐)
open ⊗-Properties +-monoidal using (coherence₁)

loop∘loop : {A : Obj} → loop ⌻ loop ≈-⧈ loop {A}
loop∘loop {A} = ≈ᵢ ⌸ identity²
  where
    open ⇒-Reasoning 𝒞
    open ⊗-Reasoning +-monoidal
    ≈ᵢ : ▽ ∘ id ⊕₁ (▽ ∘ id ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id ≈ ▽
    ≈ᵢ = begin
        ▽ ∘ id ⊕₁ (▽ ∘ id ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ elimʳ ⊕.identity ⟩∘⟨refl ⟩
        ▽ ∘ id ⊕₁ ▽ ∘ α⇒ ∘ △ ⊕₁ id              ≈⟨ refl⟩∘⟨ assoc ⟨
        ▽ ∘ (id ⊕₁ ▽ ∘ α⇒) ∘ △ ⊕₁ id            ≈⟨ extendʳ ▽-assoc ⟨
        ▽ ∘ ▽ ⊕₁ id ∘ △ ⊕₁ id                   ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
        ▽ ∘ (▽ ∘ △) ⊕₁ id                       ≈⟨ refl⟩∘⟨ ▽∘△ ⟩⊗⟨refl ⟩
        ▽ ∘ id ⊕₁ id                            ≈⟨ elimʳ ⊕.identity ⟩
        ▽                                       ∎

loop∘push∘loop≈merge : {A B : Obj} (f : A ⇒ B) → id ≤ ((f †) ∘ f) → loop ⌻ push f ⌻ loop ≈-⧈ merge f
loop∘push∘loop≈merge f id≤f†∘f = ≈ᵢ ⌸ (identityˡ ○ identityʳ)
  where
    open ⇒-Reasoning 𝒞
    open ⊗-Reasoning +-monoidal
    ≈ᵢ  : (▽ ∘ (id ⊕₁ ((f † ∘ p₂) ∘ id ⊕₁ id)) ∘ α⇒ ∘ △ ⊕₁ id) ∘ id ⊕₁ (▽ ∘ (f ∘ id) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
        ≈ f † ∘ ▽ ∘ f ⊕₁ id
    ≈ᵢ = begin
        (▽ ∘ id ⊕₁ ((f † ∘ p₂) ∘ id ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id) ∘ id ⊕₁ (▽ ∘ (f ∘ id) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id  ≈⟨ (refl⟩∘⟨ refl⟩⊗⟨ elimʳ ⊕.identity ⟩∘⟨refl) ⟩∘⟨refl ⟩
        (▽ ∘ id ⊕₁ (f † ∘ p₂) ∘ α⇒ ∘ △ ⊕₁ id) ∘ id ⊕₁ (▽ ∘ (f ∘ id) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id               ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ (identityʳ ⟩⊗⟨refl)) ⟩∘⟨refl ⟩
        (▽ ∘ id ⊕₁ (f † ∘ p₂) ∘ α⇒ ∘ △ ⊕₁ id) ∘ id ⊕₁ (▽ ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                      ≈⟨ pushˡ (refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ p₂-⊕) ⟩∘⟨refl) ⟩
        ▽ ∘ (id ⊕₁ (f † ∘ λ⇒ ∘ ! ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id) ∘ id ⊕₁ (▽ ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id            ≈⟨ refl⟩∘⟨ extendʳ (pullʳ (pullʳ (Equiv.sym serialize₁₂))) ⟩
        ▽ ∘ id ⊕₁ (f † ∘ λ⇒ ∘ ! ⊕₁ id) ∘ (α⇒ ∘ △ ⊕₁ (▽ ∘ f ⊕₁ id)) ∘ α⇒ ∘ △ ⊕₁ id                       ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
        ▽ ∘ id ⊕₁ (f †) ∘ id ⊕₁ (λ⇒ ∘ ! ⊕₁ id) ∘ (α⇒ ∘ △ ⊕₁ (▽ ∘ f ⊕₁ id)) ∘ α⇒ ∘ △ ⊕₁ id               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
        ▽ ∘ id ⊕₁ (f †) ∘ id ⊕₁ λ⇒ ∘ id ⊕₁ ! ⊕₁ id ∘ (α⇒ ∘ △ ⊕₁ (▽ ∘ f ⊕₁ id)) ∘ α⇒ ∘ △ ⊕₁ id           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (pullˡ (Equiv.sym assoc-commute-from)) ⟩
        ▽ ∘ id ⊕₁ (f †) ∘ id ⊕₁ λ⇒ ∘ (α⇒ ∘ (id ⊕₁ !) ⊕₁ id) ∘ △ ⊕₁ (▽ ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ (pullˡ triangle)  ⟩
        ▽ ∘ id ⊕₁ (f †) ∘ ρ⇒ ⊕₁ id ∘ (id ⊕₁ !) ⊕₁ id ∘ △ ⊕₁ (▽ ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₁ˡ ⟩
        ▽ ∘ id ⊕₁ (f †) ∘ (ρ⇒ ∘ id ⊕₁ !) ⊕₁ id ∘ △ ⊕₁ (▽ ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₁ˡ ⟩
        ▽ ∘ id ⊕₁ (f †) ∘ ((ρ⇒ ∘ id ⊕₁ !) ∘ △) ⊕₁ (▽ ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullʳ △-identityʳ ⟩⊗⟨refl ⟩∘⟨refl ⟩
        ▽ ∘ id ⊕₁ (f †) ∘ (ρ⇒ ∘ ρ⇐) ⊕₁ (▽ ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorʳ.isoʳ ⟩⊗⟨refl ⟩∘⟨refl ⟩
        ▽ ∘ id ⊕₁ (f †) ∘ id ⊕₁ (▽ ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                                            ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
        ▽ ∘ id ⊕₁ (f † ∘ ▽ ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                                                    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ extendʳ ⇒▽ ⟩∘⟨refl ⟩
        ▽ ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ (f †) ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                                         ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ merge₁ʳ) ⟩∘⟨refl ⟩
        ▽ ∘ id ⊕₁ (▽ ∘ (f † ∘ f) ⊕₁ (f †)) ∘ α⇒ ∘ △ ⊕₁ id                                               ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
        ▽ ∘ id ⊕₁ ▽ ∘ id ⊕₁ (f † ∘ f) ⊕₁ (f †) ∘ α⇒ ∘ △ ⊕₁ id                                           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟨
        ▽ ∘ id ⊕₁ ▽ ∘ α⇒ ∘ (id ⊕₁ (f † ∘ f)) ⊕₁ (f †) ∘ △ ⊕₁ id                                         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ʳ ⟩
        ▽ ∘ id ⊕₁ ▽ ∘ α⇒ ∘ (id ⊕₁ (f † ∘ f) ∘ △) ⊕₁ (f †)                                               ≈⟨ refl⟩∘⟨ sym-assoc ⟩
        ▽ ∘ (id ⊕₁ ▽ ∘ α⇒) ∘ (id ⊕₁ (f † ∘ f) ∘ △) ⊕₁ (f †)                                             ≈⟨ extendʳ ▽-assoc ⟨
        ▽ ∘ ▽ ⊕₁ id ∘ (id ⊕₁ (f † ∘ f) ∘ △) ⊕₁ (f †)                                                    ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
        ▽ ∘ (id + (f † ∘ f)) ⊕₁ (f †)                                                                   ≈⟨ refl⟩∘⟨ id≤f†∘f ⟩⊗⟨refl ⟩
        ▽ ∘ (f † ∘ f) ⊕₁ (f †)                                                                          ≈⟨ refl⟩∘⟨ split₁ʳ ⟩
        ▽ ∘ (f †) ⊕₁ (f †) ∘ f ⊕₁ id                                                                    ≈⟨ extendʳ ⇒▽ ⟨
        f † ∘ ▽ ∘ f ⊕₁ id                                                                               ∎

merge≈loop∘push : {A B : Obj} (f : A ⇒ B) → merge f ≈-⧈ loop ⌻ push f
merge≈loop∘push f = ≈ᵢ ⌸ Equiv.sym identityˡ
  where
    open ⇒-Reasoning 𝒞
    open ⊗-Reasoning +-monoidal
    ≈ᵢ  : f † ∘ ▽ ∘ f ⊕₁ id
        ≈ (f † ∘ p₂) ∘ id ⊕₁ (▽ ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
    ≈ᵢ = begin
        f † ∘ ▽ ∘ f ⊕₁ id                                           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ introʳ unitorˡ.isoʳ ⟩⊗⟨refl ⟩
        f † ∘ ▽ ∘ (f ∘ λ⇒ ∘ λ⇐) ⊕₁ id                               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ refl⟩∘⟨ △-identityˡ ) ⟩⊗⟨refl ⟨
        f † ∘ ▽ ∘ (f ∘ λ⇒ ∘ ! ⊕₁ id ∘ △) ⊕₁ id                      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ unitorˡ-commute-from ⟩⊗⟨refl ⟨
        f † ∘ ▽ ∘ (λ⇒ ∘ id ⊕₁ f ∘ ! ⊕₁ id ∘ △) ⊕₁ id                ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ pullˡ (Equiv.sym serialize₂₁)) ⟩⊗⟨refl ⟩
        f † ∘ ▽ ∘ (λ⇒ ∘ ! ⊕₁ f ∘ △) ⊕₁ id                           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
        f † ∘ ▽ ∘ λ⇒ ⊕₁ id ∘ (! ⊕₁ f ∘ △) ⊕₁ id                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
        f † ∘ ▽ ∘ λ⇒ ⊕₁ id ∘ (! ⊕₁ f) ⊕₁ id ∘ △ ⊕₁ id               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (Equiv.sym coherence₁) ⟩
        f † ∘ ▽ ∘ λ⇒ ∘ α⇒ ∘ (! ⊕₁ f) ⊕₁ id ∘ △ ⊕₁ id                ≈⟨ refl⟩∘⟨ extendʳ unitorˡ-commute-from ⟨
        f † ∘ λ⇒ ∘ id ⊕₁ ▽ ∘ α⇒ ∘ (! ⊕₁ f) ⊕₁ id ∘ △ ⊕₁ id          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
        f † ∘ λ⇒ ∘ id ⊕₁ ▽ ∘ ! ⊕₁ f ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
        f † ∘ λ⇒ ∘ ! ⊕₁ (▽ ∘ (f ⊕₁ id)) ∘ α⇒ ∘ △ ⊕₁ id              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
        f † ∘ λ⇒ ∘ ! ⊕₁ ▽ ∘ id ⊕₁ f ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
        f † ∘ λ⇒ ∘ ! ⊕₁ id ∘ id ⊕₁ ▽ ∘ id ⊕₁ f ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id ≈⟨ pushʳ (pullˡ (Equiv.sym p₂-⊕)) ⟩
        (f † ∘ p₂) ∘ id ⊕₁ ▽ ∘ id ⊕₁ f ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id         ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
        (f † ∘ p₂) ∘ id ⊕₁ (▽ ∘ f ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id             ∎

loop∘pull∘loop≈split : {A B : Obj} (f : A ⇒ B) → (f ∘ (f †)) ≤ id → loop ⌻ pull f ⌻ loop ≈-⧈ split f
loop∘pull∘loop≈split f f∘f†≤id = ≈ᵢ ⌸ (identityˡ ○ identityʳ)
  where
    open ⇒-Reasoning 𝒞
    open ⊗-Reasoning +-monoidal
    ≈ᵢ  : (▽ ∘ (id ⊕₁ ((f ∘ p₂) ∘ id ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id)) ∘ id ⊕₁ (▽ ∘ (f † ∘ id) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
        ≈ ▽ ∘ id ⊕₁ f
    ≈ᵢ = begin
        (▽ ∘ (id ⊕₁ ((f ∘ p₂) ∘ id ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id)) ∘ id ⊕₁ (▽ ∘ (f † ∘ id) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id  ≈⟨ (refl⟩∘⟨ refl⟩⊗⟨ elimʳ ⊕.identity ⟩∘⟨refl) ⟩∘⟨refl ⟩
        (▽ ∘ (id ⊕₁ (f ∘ p₂) ∘ α⇒ ∘ △ ⊕₁ id)) ∘ id ⊕₁ (▽ ∘ (f † ∘ id) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id               ≈⟨ pullʳ (pullʳ (pullʳ (refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ identityʳ ⟩⊗⟨refl) ⟩∘⟨refl)))⟩ 
        ▽ ∘ id ⊕₁ (f ∘ p₂) ∘ α⇒ ∘ △ ⊕₁ id ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                        ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ p₂ ∘ α⇒ ∘ △ ⊕₁ id ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ p₂-⊕ ⟩∘⟨refl ⟩
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ (λ⇒ ∘ ! ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ λ⇒ ∘ id ⊕₁ ! ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟨
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ λ⇒ ∘ α⇒ ∘ (id ⊕₁ !) ⊕₁ id ∘ △ ⊕₁ id ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ triangle ⟩
        ▽ ∘ id ⊕₁ f ∘ ρ⇒ ⊕₁ id ∘ (id ⊕₁ !) ⊕₁ id ∘ △ ⊕₁ id ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₁ˡ ⟩
        ▽ ∘ id ⊕₁ f ∘ ρ⇒ ⊕₁ id ∘ (id ⊕₁ ! ∘ △) ⊕₁ id ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ △-identityʳ ⟩⊗⟨refl ⟩∘⟨refl ⟩
        ▽ ∘ id ⊕₁ f ∘ ρ⇒ ⊕₁ id ∘ ρ⇐ ⊕₁ id ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₁ˡ ⟩
        ▽ ∘ id ⊕₁ f ∘ (ρ⇒ ∘ ρ⇐) ⊕₁ id ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorʳ.isoʳ ⟩⊗⟨refl ⟩∘⟨refl ⟩
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ id ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                                   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimˡ ⊕.identity ⟩
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ (▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                                              ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
        ▽ ∘ id ⊕₁ (f ∘ ▽ ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                                                    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ extendʳ ⇒▽ ⟩∘⟨refl ⟩
        ▽ ∘ id ⊕₁ (▽ ∘ f ⊕₁ f ∘ (f †) ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id                                               ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ merge₁ʳ) ⟩∘⟨refl ⟩
        ▽ ∘ id ⊕₁ (▽ ∘ (f ∘ f †) ⊕₁ f) ∘ α⇒ ∘ △ ⊕₁ id                                                     ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
        ▽ ∘ id ⊕₁ ▽ ∘ id ⊕₁ (f ∘ f †) ⊕₁ f ∘ α⇒ ∘ △ ⊕₁ id                                                 ≈⟨ refl⟩∘⟨ pushʳ (extendʳ (Equiv.sym assoc-commute-from)) ⟩
        ▽ ∘ (id ⊕₁ ▽ ∘ α⇒) ∘ (id ⊕₁ (f ∘ f †)) ⊕₁ f ∘ △ ⊕₁ id                                             ≈⟨ extendʳ ▽-assoc ⟨
        ▽ ∘ ▽ ⊕₁ id ∘ (id ⊕₁ (f ∘ f †)) ⊕₁ f ∘ △ ⊕₁ id                                                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge₁ʳ ⟩
        ▽ ∘ ▽ ⊕₁ id ∘ (id ⊕₁ (f ∘ f †) ∘ △) ⊕₁ f                                                          ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
        ▽ ∘ id + (f ∘ f †) ⊕₁ f                                                                           ≈⟨ refl⟩∘⟨ +-commutative ⟩⊗⟨refl ⟩
        ▽ ∘ (f ∘ f †) + id ⊕₁ f                                                                           ≈⟨ refl⟩∘⟨ f∘f†≤id ⟩⊗⟨refl ⟩
        ▽ ∘ id ⊕₁ f                                                                                       ∎

split≈pull∘loop : {A B : Obj} (f : A ⇒ B) → split f ≈-⧈ pull f ⌻ loop
split≈pull∘loop f = ≈ᵢ ⌸ Equiv.sym identityʳ
  where
    open ⇒-Reasoning 𝒞
    open ⊗-Reasoning +-monoidal
    ≈ᵢ  : ▽ ∘ id ⊕₁ f
        ≈ ▽ ∘ id ⊕₁ ((f ∘ p₂) ∘ id ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id
    ≈ᵢ = begin
        ▽ ∘ id ⊕₁ f                                             ≈⟨ refl⟩∘⟨ introʳ ⊕.identity ⟩
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ id                                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorʳ.isoʳ ⟩⊗⟨refl ⟨
        ▽ ∘ id ⊕₁ f ∘ (ρ⇒ ∘ ρ⇐) ⊕₁ id                           ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
        ▽ ∘ id ⊕₁ f ∘ ρ⇒ ⊕₁ id ∘ ρ⇐ ⊕₁ id                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ △-identityʳ ⟩⊗⟨refl ⟨
        ▽ ∘ id ⊕₁ f ∘ ρ⇒ ⊕₁ id ∘ (id ⊕₁ ! ∘ △) ⊕₁ id            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (Equiv.sym triangle) ⟩
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ λ⇒ ∘ α⇒ ∘ (id ⊕₁ ! ∘ △) ⊕₁ id       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ λ⇒ ∘ α⇒ ∘ (id ⊕₁ !) ⊕₁ id ∘ △ ⊕₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ λ⇒ ∘ id ⊕₁ ! ⊕₁ id ∘ α⇒ ∘ △ ⊕₁ id   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ (λ⇒ ∘ ! ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ p₂-⊕ ⟩∘⟨refl ⟨
        ▽ ∘ id ⊕₁ f ∘ id ⊕₁ p₂ ∘ α⇒ ∘ △ ⊕₁ id                   ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
        ▽ ∘ id ⊕₁ (f ∘ p₂) ∘ α⇒ ∘ △ ⊕₁ id                       ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (pushʳ (introʳ ⊕.identity)) ⟩∘⟨refl ⟩
        ▽ ∘ id ⊕₁ ((f ∘ p₂) ∘ id ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id          ∎

loop∘push∘loop : {A B : Obj} (f : A ⇒ B) → id ≤ ((f †) ∘ f) → loop ⌻ push f ⌻ loop ≈-⧈ loop ⌻ push f
loop∘push∘loop f id≤f†∘f = ≈-trans (loop∘push∘loop≈merge f id≤f†∘f) (merge≈loop∘push f)

loop∘pull∘loop : {A B : Obj} → (f : A ⇒ B) → (f ∘ (f †)) ≤ id → loop ⌻ pull f ⌻ loop ≈-⧈ pull f ⌻ loop
loop∘pull∘loop f f∘f†≤id = ≈-trans (loop∘pull∘loop≈split f f∘f†≤id) (split≈pull∘loop f)
