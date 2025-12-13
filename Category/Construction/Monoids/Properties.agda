{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Level using (Level; _⊔_)

module Category.Construction.Monoids.Properties
    {o ℓ e : Level}
    {𝒞 : Category o ℓ e}
    (monoidal : Monoidal 𝒞)
  where

import Categories.Category.Monoidal.Reasoning monoidal as ⊗-Reasoning
import Categories.Morphism.Reasoning 𝒞 as ⇒-Reasoning

open import Categories.Category using (_[_,_])
open import Categories.Category.Construction.Monoids monoidal using (Monoids)
open import Categories.Category.Monoidal.Utilities monoidal using (module Shorthands; _⊗ᵢ_)
open import Categories.Morphism using (_≅_)
open import Categories.Morphism.Notation using (_[_≅_])
open import Categories.Object.Monoid monoidal using (Monoid)
open import Data.Product using (Σ-syntax; _,_)

module 𝒞 = Category 𝒞

open Monoid using () renaming (Carrier to ∣_∣)

transport-by-iso
    : {X : 𝒞.Obj}
    → (M : Monoid)
    → 𝒞 [ ∣ M ∣ ≅ X ]
    → Σ[ Xₘ ∈ Monoid ] Monoids [ M ≅ Xₘ ]
transport-by-iso {X} M ∣M∣≅X = Xₘ , M≅Xₘ
  where
    open _≅_ ∣M∣≅X
    open Monoid M
    open 𝒞 using (_∘_; id; _≈_; module Equiv)
    open Monoidal monoidal
      using (_⊗₀_; _⊗₁_; assoc-commute-from; unitorˡ-commute-from; unitorʳ-commute-from)
    open Shorthands
    open ⊗-Reasoning
    open ⇒-Reasoning
    as
        : (from ∘ μ ∘ to ⊗₁ to)
        ∘ (from ∘ μ ∘ to ⊗₁ to) ⊗₁ id
        ≈ (from ∘ μ ∘ to ⊗₁ to)
        ∘ id ⊗₁ (from ∘ μ ∘ to ⊗₁ to)
        ∘ α⇒
    as = extendˡ (begin
        (μ ∘ to ⊗₁ to) ∘ (from ∘ μ ∘ to ⊗₁ to) ⊗₁ id      ≈⟨ pullʳ merge₁ʳ ⟩
        μ ∘ (to ∘ from ∘ μ ∘ to ⊗₁ to) ⊗₁ to              ≈⟨ refl⟩∘⟨ cancelˡ isoˡ ⟩⊗⟨refl ⟩
        μ ∘ (μ ∘ to ⊗₁ to) ⊗₁ to                          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
        μ ∘ μ ⊗₁ id ∘ (to ⊗₁ to) ⊗₁ to                    ≈⟨ extendʳ assoc ⟩
        μ ∘ (id ⊗₁ μ ∘ α⇒) ∘ (to ⊗₁ to) ⊗₁ to             ≈⟨ pushʳ (pullʳ assoc-commute-from) ⟩
        (μ ∘ id ⊗₁ μ) ∘ to ⊗₁ (to ⊗₁ to) ∘ α⇒             ≈⟨ extendˡ (pullˡ merge₂ˡ) ⟩
        (μ ∘ to ⊗₁ (μ ∘ to ⊗₁ to)) ∘ α⇒                   ≈⟨ (refl⟩∘⟨ refl⟩⊗⟨ insertˡ isoˡ) ⟩∘⟨refl ⟩
        (μ ∘ to ⊗₁ (to ∘ from ∘ μ ∘ to ⊗₁ to)) ∘ α⇒       ≈⟨ pushˡ (pushʳ split₂ʳ) ⟩
        (μ ∘ to ⊗₁ to) ∘ id ⊗₁ (from ∘ μ ∘ to ⊗₁ to) ∘ α⇒ ∎)
    idˡ : λ⇒ ≈ (from ∘ μ ∘ to ⊗₁ to) ∘ (from ∘ η) ⊗₁ id
    idˡ = begin
        λ⇒                                        ≈⟨ insertˡ isoʳ ⟩
        from ∘ to ∘ λ⇒                            ≈⟨ refl⟩∘⟨ unitorˡ-commute-from ⟨
        from ∘ λ⇒ ∘ id ⊗₁ to                      ≈⟨ refl⟩∘⟨ pushˡ identityˡ ⟩
        from ∘ μ ∘ η ⊗₁ id ∘ id ⊗₁ to             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ serialize₁₂ ⟨
        from ∘ μ ∘ η ⊗₁ to                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ insertˡ isoˡ ⟩⊗⟨refl ⟩
        from ∘ μ ∘ (to ∘ from ∘ η) ⊗₁ to          ≈⟨ pushʳ (pushʳ split₁ʳ) ⟩
        (from ∘ μ ∘ to ⊗₁ to) ∘ (from ∘ η) ⊗₁ id  ∎
    idʳ : ρ⇒ ≈ (from ∘ μ ∘ to ⊗₁ to) ∘ id ⊗₁ (from ∘ η)
    idʳ = begin
        ρ⇒                                        ≈⟨ insertˡ isoʳ ⟩
        from ∘ to ∘ ρ⇒                            ≈⟨ refl⟩∘⟨ unitorʳ-commute-from ⟨
        from ∘ ρ⇒ ∘ to ⊗₁ id                      ≈⟨ refl⟩∘⟨ pushˡ identityʳ ⟩
        from ∘ μ ∘ id ⊗₁ η ∘ to ⊗₁ id             ≈⟨ refl⟩∘⟨ refl⟩∘⟨ serialize₂₁ ⟨
        from ∘ μ ∘ to ⊗₁ η                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ insertˡ isoˡ ⟩
        from ∘ μ ∘ to ⊗₁ (to ∘ from ∘ η)          ≈⟨ pushʳ (pushʳ split₂ʳ) ⟩
        (from ∘ μ ∘ to ⊗₁ to) ∘ id ⊗₁ (from ∘ η)  ∎
    Xₘ : Monoid
    Xₘ = record
        { Carrier = X
        ; isMonoid = record
            { μ = from ∘ μ ∘ to ⊗₁ to
            ; η = from ∘ η
            ; assoc = as
            ; identityˡ = idˡ
            ; identityʳ = idʳ 
            }
        }
    M⇒Xₘ : Monoids [ M , Xₘ ]
    M⇒Xₘ = record
        { arr = from
        ; preserves-μ = pushʳ (insertʳ (_≅_.isoˡ (∣M∣≅X ⊗ᵢ ∣M∣≅X)))
        ; preserves-η = Equiv.refl
        }
    Xₘ⇒M : Monoids [ Xₘ , M ]
    Xₘ⇒M = record
        { arr = to
        ; preserves-μ = cancelˡ isoˡ
        ; preserves-η = cancelˡ isoˡ
        }
    M≅Xₘ : Monoids [ M ≅ Xₘ ]
    M≅Xₘ = record
        { from = M⇒Xₘ
        ; to = Xₘ⇒M
        ; iso = record
            { isoˡ = isoˡ
            ; isoʳ = isoʳ
            }
        }
