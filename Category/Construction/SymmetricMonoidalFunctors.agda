{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Category.Construction.SymmetricMonoidalFunctors
    {o ℓ e o′ ℓ′ e′}
    (C : SymmetricMonoidalCategory o ℓ e)
    (D : SymmetricMonoidalCategory o′ ℓ′ e′)
  where

-- The functor category for a given pair of symmetric monoidal categories

open import Level using (_⊔_)
open import Relation.Binary.Construct.On using (isEquivalence)
open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Functor.Monoidal.Symmetric using () renaming (module Lax to Lax₁; module Strong to Strong₁)
open import Categories.NaturalTransformation.Monoidal.Symmetric using () renaming (module Lax to Lax₂; module Strong to Strong₂)
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)

open SymmetricMonoidalCategory D

module Lax where

  open Lax₂.SymmetricMonoidalNaturalTransformation using (U)

  SymmetricMonoidalFunctors
      : Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
  SymmetricMonoidalFunctors = categoryHelper record
      { Obj = Lax₁.SymmetricMonoidalFunctor C D
      ; _⇒_ = Lax₂.SymmetricMonoidalNaturalTransformation
      ; _≈_ = λ α β → U α ≃ U β
      ; id  = Lax₂.id
      ; _∘_ = Lax₂._∘ᵥ_
      ; assoc = assoc
      ; identityˡ = identityˡ
      ; identityʳ = identityʳ
      ; equiv = isEquivalence U ≃-isEquivalence
      ; ∘-resp-≈ = λ α₁≈β₁ α₂≈β₂ → ∘-resp-≈ α₁≈β₁ α₂≈β₂
      }

module Strong where

  open Strong₂.SymmetricMonoidalNaturalTransformation using (U)

  SymmetricMonoidalFunctors
      : Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
  SymmetricMonoidalFunctors = categoryHelper record
      { Obj = Strong₁.SymmetricMonoidalFunctor C D
      ; _⇒_ = Strong₂.SymmetricMonoidalNaturalTransformation
      ; _≈_ = λ α β → U α ≃ U β
      ; id = Strong₂.id
      ; _∘_ = Strong₂._∘ᵥ_
      ; assoc = assoc
      ; identityˡ = identityˡ
      ; identityʳ = identityʳ
      ; equiv = isEquivalence U ≃-isEquivalence
      ; ∘-resp-≈ = λ α₁≈β₁ α₂≈β₂ → ∘-resp-≈ α₁≈β₁ α₂≈β₂
      }
