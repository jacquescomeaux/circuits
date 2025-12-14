{-# OPTIONS --without-K --safe #-}

module Functor.Properties where

import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Categories.Category using (Category; _[_,_])
open import Level using (Level)
open import Categories.Morphism.Notation using (_[_≅_])
open import Categories.Morphism using (_≅_)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; niHelper)
open import Data.Product using (Σ-syntax; _,_)

module _
    {o o′ ℓ ℓ′ e e′ : Level}
    {𝒞 : Category o ℓ e}
    {𝒟 : Category o′ ℓ′ e′}
  where

  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟

  define-by-pw-iso
      : (F : Functor 𝒞 𝒟)
        (G₀ : 𝒞.Obj → 𝒟.Obj)
      → (let module F = Functor F)
      → ((X : 𝒞.Obj) → 𝒟 [ F.₀ X ≅ G₀ X ])
      → Σ[ G ∈ Functor 𝒞 𝒟 ] F ≃ G
  define-by-pw-iso F G₀ α = G , F≃G
    where
      open Functor
      module F = Functor F
      open 𝒟
      open _≅_
      open HomReasoning
      open ⇒-Reasoning 𝒟

      G-homo
          : {X Y Z : 𝒞.Obj}
          → (f : 𝒞 [ X , Y ])
          → (g : 𝒞 [ Y , Z ])
          → from (α Z) ∘ F.₁ (g 𝒞.∘ f) ∘ to (α X)
          ≈ (from (α Z) ∘ F.₁ g ∘ to (α Y)) ∘ from (α Y) ∘ F.₁ f ∘ to (α X)
      G-homo {X} {Y} {Z} f g = begin
          from (α Z) ∘ F.₁ (g 𝒞.∘ f) ∘ to (α X)                           ≈⟨ extendʳ (pushʳ F.homomorphism) ⟩
          (from (α Z) ∘ F.₁ g) ∘ F.₁ f ∘ to (α X)                         ≈⟨ extendˡ (pushˡ (insertʳ (isoˡ (α Y)))) ⟩
          (from (α Z) ∘ F.₁ g ∘ to (α Y)) ∘ from (α Y) ∘ F.₁ f ∘ to (α X) ∎

      G-resp-≈
        : {X Y : 𝒞.Obj}
        → {f g : 𝒞 [ X , Y ]}
        → f 𝒞.≈ g
        → from (α Y) ∘ F.₁ f ∘ to (α X)
        ≈ from (α Y) ∘ F.₁ g ∘ to (α X)
      G-resp-≈ f≈g = refl⟩∘⟨ F.F-resp-≈ f≈g ⟩∘⟨refl

      G-identity : {X : 𝒞.Obj} → from (α X) ∘ F.₁ 𝒞.id ∘ to (α X) ≈ id
      G-identity {X} = refl⟩∘⟨ (F.identity ⟩∘⟨refl ○ identityˡ) ○ isoʳ (α X)

      G : Functor 𝒞 𝒟
      G .F₀ = G₀
      G .F₁ {X} {Y} f = from (α Y) ∘ F.₁ f ∘ to (α X)
      G .identity {X} = G-identity
      G .homomorphism {f = f} {g} = G-homo f g
      G .F-resp-≈ = G-resp-≈

      commute : {X Y : 𝒞.Obj} (f : 𝒞 [ X , Y ]) → from (α Y) ∘ F.F₁ f ≈ (from (α Y) ∘ F.₁ f ∘ to (α X)) ∘ from (α X)
      commute {X} {Y} f = pushʳ (insertʳ (isoˡ (α X)))

      F≃G : F ≃ G
      F≃G = niHelper record
          { η = λ X → from (α X)
          ; η⁻¹ = λ X → to (α X)
          ; commute = commute
          ; iso = λ X → iso (α X)
          }
