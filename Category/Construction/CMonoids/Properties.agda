{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Level using (Level; _⊔_)

module Category.Construction.CMonoids.Properties
    {o ℓ e : Level}
    {𝒞 : Category o ℓ e}
    {monoidal : Monoidal 𝒞}
    (symmetric : Symmetric monoidal)
  where

import Categories.Category.Monoidal.Reasoning monoidal as ⊗-Reasoning
import Categories.Morphism.Reasoning 𝒞 as ⇒-Reasoning
import Category.Construction.Monoids.Properties {o} {ℓ} {e} {𝒞} monoidal as Monoids

open import Categories.Category using (_[_,_])
open import Categories.Category.Monoidal.Symmetric.Properties symmetric using (module Shorthands)
open import Categories.Morphism using (_≅_)
open import Categories.Morphism.Notation using (_[_≅_])
open import Categories.Object.Monoid monoidal using (Monoid)
open import Category.Construction.CMonoids symmetric using (CMonoids)
open import Data.Product using (Σ-syntax; _,_)
open import Object.Monoid.Commutative symmetric using (CommutativeMonoid)

module 𝒞 = Category 𝒞

open CommutativeMonoid using (monoid) renaming (Carrier to ∣_∣)

transport-by-iso
    : {X : 𝒞.Obj}
    → (M : CommutativeMonoid)
    → 𝒞 [ ∣ M ∣ ≅ X ]
    → Σ[ Xₘ ∈ CommutativeMonoid ] CMonoids [ M ≅ Xₘ ]
transport-by-iso {X} M ∣M∣≅X
  using (Xₘ′ , M≅Xₘ′) ← Monoids.transport-by-iso {X} (monoid M) ∣M∣≅X = Xₘ , M≅Xₘ
  where
    module M≅Xₘ′ = _≅_ M≅Xₘ′
    open _≅_ ∣M∣≅X
    module Xₘ′ = Monoid Xₘ′
    open CommutativeMonoid M
    open 𝒞 using (_≈_; _∘_)
    open Shorthands
    open ⊗-Reasoning
    open ⇒-Reasoning
    open Symmetric symmetric using (_⊗₁_; module braiding)
    comm : from ∘ μ ∘ to ⊗₁ to ≈ (from ∘ μ ∘ to ⊗₁ to) ∘ σ⇒
    comm = begin
        from ∘ μ ∘ to ⊗₁ to         ≈⟨ push-center (commutative) ⟩
        from ∘ μ ∘ σ⇒ ∘ to ⊗₁ to    ≈⟨ pushʳ (pushʳ (braiding.⇒.commute (to , to))) ⟩
        (from ∘ μ ∘ to ⊗₁ to) ∘ σ⇒  ∎
    Xₘ : CommutativeMonoid
    Xₘ = record
        { Carrier = X
        ; isCommutativeMonoid = record
            { isMonoid = Xₘ′.isMonoid
            ; commutative = comm
            }
        }
    M⇒Xₘ : CMonoids [ M , Xₘ ]
    M⇒Xₘ = record { monoid⇒ = M≅Xₘ′.from }
    Xₘ⇒M : CMonoids [ Xₘ , M ]
    Xₘ⇒M = record { monoid⇒ = M≅Xₘ′.to }
    M≅Xₘ : CMonoids [ M ≅ Xₘ ]
    M≅Xₘ = record
        { from = M⇒Xₘ
        ; to = Xₘ⇒M
        ; iso = record
            { isoˡ = isoˡ
            ; isoʳ = isoʳ
            }
        }
