{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)

module Category.Monoidal.Coherence {o ℓ e} {𝒞 : Category o ℓ e} (monoidal : Monoidal 𝒞) where

import Categories.Morphism as Morphism
import Categories.Morphism.IsoEquiv as IsoEquiv
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning

open import Categories.Functor.Properties using ([_]-resp-≅)

open Monoidal monoidal
open Category 𝒞

open ⇒-Reasoning 𝒞
open ⊗-Reasoning monoidal
open Morphism 𝒞 using (_≅_)
open IsoEquiv 𝒞 using (to-unique)

open Equiv

𝟏 : Obj
𝟏 = unit

module α≅ = associator
module λ≅ = unitorˡ
module ρ≅ = unitorʳ

private
  variable
    A B C D : Obj

α⇒ : (A ⊗₀ B) ⊗₀ C ⇒ A ⊗₀ B ⊗₀ C
α⇒ = α≅.from

α⇐ : A ⊗₀ B ⊗₀ C ⇒ (A ⊗₀ B) ⊗₀ C
α⇐ = α≅.to

λ⇒ : 𝟏 ⊗₀ A ⇒ A
λ⇒ = λ≅.from

λ⇐ : A ⇒ 𝟏 ⊗₀ A
λ⇐ = λ≅.to

ρ⇒ : A ⊗₀ 𝟏 ⇒ A
ρ⇒ = ρ≅.from

ρ⇐ : A ⇒ A ⊗₀ 𝟏
ρ⇐ = ρ≅.to

α⊗id : ((A ⊗₀ B) ⊗₀ C) ⊗₀ D ≅ (A ⊗₀ B ⊗₀ C) ⊗₀ D
α⊗id {A} {B} {C} {D} = [ -⊗ D ]-resp-≅ (associator {A} {B} {C})

module α⊗id {A} {B} {C} {D} = _≅_ (α⊗id {A} {B} {C} {D})

perimeter
    : α⇒ {𝟏} {A} {B} ∘ (ρ⇒ {𝟏} ⊗₁ id {A}) ⊗₁ id {B}
    ≈ id {𝟏} ⊗₁ λ⇒ {A ⊗₀ B} ∘ id {𝟏} ⊗₁ α⇒ {𝟏} {A} {B} ∘ α⇒ {𝟏} {𝟏 ⊗₀ A} {B} ∘ α⇒ {𝟏} {𝟏} {A} ⊗₁ id {B}
perimeter = begin
    α⇒ ∘ (ρ⇒ ⊗₁ id) ⊗₁ id               ≈⟨ assoc-commute-from ⟩
    ρ⇒ ⊗₁ id ⊗₁ id ∘ α⇒                 ≈⟨ refl⟩⊗⟨ ⊗.identity ⟩∘⟨refl ⟩
    ρ⇒ ⊗₁ id ∘ α⇒                       ≈⟨ pullˡ triangle ⟨
    id ⊗₁ λ⇒ ∘ α⇒ ∘ α⇒                  ≈⟨ refl⟩∘⟨ pentagon ⟨
    id ⊗₁ λ⇒ ∘ id ⊗₁ α⇒ ∘ α⇒ ∘ α⇒ ⊗₁ id ∎

perimeter-triangle
    : α⇒ {𝟏} {A} {C} ∘ (id {𝟏} ⊗₁ λ⇒ {A}) ⊗₁ id {C}
    ≈ id {𝟏} ⊗₁ λ⇒ {A ⊗₀ C} ∘ id {𝟏} ⊗₁ α⇒ {𝟏} {A} {C} ∘ α⇒ {𝟏} {𝟏 ⊗₀ A} {C}
perimeter-triangle = begin
    α⇒ ∘ (id ⊗₁ λ⇒) ⊗₁ id                            ≈⟨ refl⟩∘⟨ identityʳ ⟨
    α⇒ ∘ (id ⊗₁ λ⇒) ⊗₁ id ∘ id                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⊗id.isoʳ ⟨
    α⇒ ∘ (id ⊗₁ λ⇒) ⊗₁ id ∘ α⇒ ⊗₁ id ∘ α⇐ ⊗₁ id      ≈⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟨
    α⇒ ∘ (id ⊗₁ λ⇒ ∘ α⇒) ⊗₁ id ∘ α⇐ ⊗₁ id            ≈⟨ refl⟩∘⟨ triangle ⟩⊗⟨refl ⟩∘⟨refl ⟩
    α⇒ ∘ (ρ⇒ ⊗₁ id) ⊗₁ id ∘ α⇐ ⊗₁ id                 ≈⟨ extendʳ perimeter ⟩
    id ⊗₁ λ⇒ ∘ (id ⊗₁ α⇒ ∘ α⇒ ∘ α⇒ ⊗₁ id) ∘ α⇐ ⊗₁ id ≈⟨ refl⟩∘⟨ assoc ⟩
    id ⊗₁ λ⇒ ∘ id ⊗₁ α⇒ ∘ (α⇒ ∘ α⇒ ⊗₁ id) ∘ α⇐ ⊗₁ id ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    id ⊗₁ λ⇒ ∘ id ⊗₁ α⇒ ∘ α⇒ ∘ α⇒ ⊗₁ id ∘ α⇐ ⊗₁ id   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ α⊗id.isoʳ ⟩
    id ⊗₁ λ⇒ ∘ id ⊗₁ α⇒ ∘ α⇒ ∘ id                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ identityʳ ⟩
    id ⊗₁ λ⇒ ∘ id ⊗₁ α⇒ ∘ α⇒                         ∎

perimeter-triangle-square
    : ∀ {A C : Obj}
    → id {𝟏} ⊗₁ λ⇒ {A} ⊗₁ id {C}
    ≈ id {𝟏} ⊗₁ λ⇒ {A ⊗₀ C} ∘ id {𝟏} ⊗₁ α⇒ {𝟏} {A} {C}
perimeter-triangle-square = begin
    id ⊗₁ λ⇒ ⊗₁ id                  ≈⟨ identityʳ ⟨
    id ⊗₁ λ⇒ ⊗₁ id ∘ id             ≈⟨ refl⟩∘⟨ associator.isoʳ ⟨
    id ⊗₁ λ⇒ ⊗₁ id ∘ α⇒ ∘ α⇐        ≈⟨ extendʳ assoc-commute-from ⟨
    α⇒ ∘ (id ⊗₁ λ⇒) ⊗₁ id ∘ α⇐      ≈⟨ extendʳ perimeter-triangle ⟩
    id ⊗₁ λ⇒ ∘ (id ⊗₁ α⇒ ∘ α⇒) ∘ α⇐ ≈⟨ refl⟩∘⟨ assoc ⟩
    id ⊗₁ λ⇒ ∘ id ⊗₁ α⇒ ∘ α⇒ ∘ α⇐   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ associator.isoʳ ⟩
    id ⊗₁ λ⇒ ∘ id ⊗₁ α⇒ ∘ id        ≈⟨ refl⟩∘⟨ identityʳ ⟩
    id ⊗₁ λ⇒ ∘ id ⊗₁ α⇒             ∎

λₕi≈λₕᵢ∘α₁ₕᵢ : λ⇒ {A} ⊗₁ id {C} ≈ λ⇒ {A ⊗₀ C} ∘ α⇒ {𝟏} {A} {C}
λₕi≈λₕᵢ∘α₁ₕᵢ = begin
    λ⇒ ⊗₁ id                          ≈⟨ insertʳ unitorˡ.isoʳ ⟩
    (λ⇒ ⊗₁ id ∘ λ⇒) ∘ λ⇐              ≈⟨ unitorˡ-commute-from ⟩∘⟨refl ⟨
    (λ⇒ ∘ id ⊗₁ λ⇒ ⊗₁ id) ∘ λ⇐        ≈⟨ (refl⟩∘⟨ perimeter-triangle-square) ⟩∘⟨refl ⟩
    (λ⇒ ∘ id ⊗₁ λ⇒ ∘ id ⊗₁ α⇒) ∘ λ⇐   ≈⟨ (refl⟩∘⟨ merge₂ˡ) ⟩∘⟨refl ⟩
    (λ⇒ ∘ id ⊗₁ (λ⇒ ∘ α⇒)) ∘ λ⇐       ≈⟨ unitorˡ-commute-from ⟩∘⟨refl ⟩
    ((λ⇒ ∘ α⇒) ∘ λ⇒) ∘ λ⇐             ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
    λ⇒ ∘ α⇒                           ∎

1λ₁≈λ₁₁ : id {𝟏} ⊗₁ λ⇒ {𝟏} ≈ λ⇒ {𝟏 ⊗₀ 𝟏}
1λ₁≈λ₁₁ = begin
    id ⊗₁ λ⇒            ≈⟨ insertˡ unitorˡ.isoˡ ⟩
    λ⇐ ∘ λ⇒ ∘ id ⊗₁ λ⇒  ≈⟨ refl⟩∘⟨ unitorˡ-commute-from ⟩
    λ⇐ ∘ λ⇒ ∘ λ⇒        ≈⟨ cancelˡ unitorˡ.isoˡ ⟩
    λ⇒                  ∎

λ₁𝟏≈ρ₁𝟏 : λ⇒ {𝟏} ⊗₁ id {𝟏} ≈ ρ⇒ {𝟏} ⊗₁ id {𝟏}
λ₁𝟏≈ρ₁𝟏 = begin
    λ⇒ ⊗₁ id      ≈⟨ λₕi≈λₕᵢ∘α₁ₕᵢ ⟩
    λ⇒ ∘ α⇒       ≈⟨ 1λ₁≈λ₁₁ ⟩∘⟨refl ⟨
    id ⊗₁ λ⇒ ∘ α⇒ ≈⟨ triangle ⟩
    ρ⇒ ⊗₁ id      ∎

λ₁≅ρ₁⇒ : λ⇒ {𝟏} ≈ ρ⇒ {𝟏}
λ₁≅ρ₁⇒ = begin
    λ⇒                    ≈⟨ insertʳ unitorʳ.isoʳ ⟩
    (λ⇒ ∘ ρ⇒) ∘ ρ⇐        ≈⟨ unitorʳ-commute-from ⟩∘⟨refl ⟨
    (ρ⇒ ∘ λ⇒ ⊗₁ id) ∘ ρ⇐  ≈⟨ (refl⟩∘⟨ λ₁𝟏≈ρ₁𝟏) ⟩∘⟨refl ⟩
    (ρ⇒ ∘ ρ⇒ ⊗₁ id) ∘ ρ⇐  ≈⟨ unitorʳ-commute-from ⟩∘⟨refl ⟩
    (ρ⇒ ∘ ρ⇒) ∘ ρ⇐        ≈⟨ cancelʳ unitorʳ.isoʳ ⟩
    ρ⇒                    ∎

λ₁≅ρ₁⇐ : λ⇐ {𝟏} ≈ ρ⇐ {𝟏}
λ₁≅ρ₁⇐ = to-unique λ≅.iso ρ≅.iso λ₁≅ρ₁⇒
