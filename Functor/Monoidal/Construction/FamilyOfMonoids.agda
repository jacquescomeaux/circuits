{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Category.Cocartesian.Bundle using (CocartesianCategory)
open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor using (Functor) renaming (_∘F_ to _∙_)
open import Level using (Level; _⊔_)

-- A functor from a cocartesian category 𝒞 to Monoids[S]
-- can be turned into a monoidal functor from 𝒞 to S

module Functor.Monoidal.Construction.FamilyOfMonoids
    {o o′ ℓ ℓ′ e e′ : Level}
    {𝒞 : Category o ℓ e}
    (𝒞-+ : Cocartesian 𝒞)
    {S : MonoidalCategory o′ ℓ′ e′}
    (let module S = MonoidalCategory S)
    (M : Functor 𝒞 (Monoids S.monoidal))
  where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Category.Monoidal.Utilities as ⊗-Util
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Categories.Object.Monoid as MonoidObject

open import Categories.Category using (module Definitions)
open import Categories.Category.Cocartesian using (module CocartesianMonoidal)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor.Monoidal using (MonoidalFunctor; IsMonoidalFunctor)
open import Categories.Functor.Properties using ([_]-resp-square; [_]-resp-∘)
open import Categories.Morphism using (_≅_)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Data.Product using (_,_)
open import Functor.Forgetful.Instance.Monoid S using (Forget)

private

  G : Functor 𝒞 S.U
  G = Forget ∙ M

  module 𝒞 = CocartesianCategory (record { cocartesian = 𝒞-+ })
  module 𝒞-M = CocartesianMonoidal 𝒞 𝒞-+

  𝒞-MC : MonoidalCategory o ℓ e
  𝒞-MC = record { monoidal = 𝒞-M.+-monoidal }

  module +-assoc {n} {m} {o} = _≅_ (𝒞.+-assoc {n} {m} {o})
  module +-λ {n} = _≅_ (𝒞-M.⊥+A≅A {n})
  module +-ρ {n} = _≅_ (𝒞-M.A+⊥≅A {n})

  module G = Functor G
  module M = Functor M

  open MonoidObject S.monoidal using (Monoid; Monoid⇒)
  open Monoid renaming (assoc to μ-assoc; identityˡ to μ-identityˡ; identityʳ to μ-identityʳ)
  open Monoid⇒

  open 𝒞 using (-+-; _+_; _+₁_; i₁; i₂; inject₁; inject₂)

  module _ where

    open Category 𝒞
    open ⇒-Reasoning 𝒞
    open ⊗-Reasoning 𝒞-M.+-monoidal

    module _ {n m o : Obj} where

      private

        +-α : (n + m) + o 𝒞.⇒ n + (m + o)
        +-α = +-assoc.to {n} {m} {o}

      +-α∘i₂ : +-α ∘ i₂ ≈ i₂ ∘ i₂
      +-α∘i₂ = inject₂

      +-α∘i₁∘i₁ : (+-α ∘ i₁) ∘ i₁ ≈ i₁
      +-α∘i₁∘i₁ = inject₁ ⟩∘⟨refl ○ inject₁

      +-α∘i₁∘i₂ : (+-α ∘ i₁) ∘ i₂ ≈ i₂ ∘ i₁
      +-α∘i₁∘i₂ = inject₁ ⟩∘⟨refl ○ inject₂

    module _ {n : Obj} where

      +-ρ∘i₁ : +-ρ.from {n} ∘ i₁ ≈ id
      +-ρ∘i₁ = inject₁

      +-λ∘i₂ : +-λ.from {n} ∘ i₂ ≈ id
      +-λ∘i₂ = inject₂

  open S
  open ⇒-Reasoning U
  open ⊗-Reasoning monoidal
  open ⊗-Util.Shorthands monoidal

  ⊲ : {A : 𝒞.Obj} → G.₀ A ⊗₀ G.₀ A ⇒ G.₀ A
  ⊲ {A} = μ (M.₀ A)

  ⇒⊲ : {A B : 𝒞.Obj} (f : A 𝒞.⇒ B) → G.₁ f ∘ ⊲ ≈ ⊲ ∘ G.₁ f ⊗₁ G.₁ f
  ⇒⊲ f = preserves-μ (M.₁ f)

  ε : {A : 𝒞.Obj} → unit ⇒ G.₀ A
  ε {A} = η (M.₀ A)

  ⇒ε : {A B : 𝒞.Obj} (f : A 𝒞.⇒ B) → G.₁ f ∘ ε ≈ ε
  ⇒ε f = preserves-η (M.₁ f)

  ⊲-⊗ : {n m : 𝒞.Obj} → G.₀ n ⊗₀ G.₀ m ⇒ G.₀ (n + m)
  ⊲-⊗ = ⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂

  module _ {n n′ m m′ : 𝒞.Obj} (f : n 𝒞.⇒ n′) (g : m 𝒞.⇒ m′) where

    open Definitions S.U using (CommutativeSquare)

    left₁ : CommutativeSquare (G.₁ i₁) (G.₁ f) (G.₁ (f +₁ g)) (G.₁ i₁)
    left₁ = [ G ]-resp-square inject₁

    left₂ : CommutativeSquare (G.₁ i₂) (G.₁ g) (G.₁ (f +₁ g)) (G.₁ i₂)
    left₂ = [ G ]-resp-square inject₂

    right : CommutativeSquare ⊲ (G.₁ (f +₁ g) ⊗₁ G.₁ (f +₁ g)) (G.₁ (f +₁ g)) ⊲
    right = ⇒⊲ (f +₁ g)

    ⊲-⊗-commute :
        CommutativeSquare
            (⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂)
            (G.₁ f ⊗₁ G.₁ g)
            (G.₁ (f +₁ g))
            (⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂)
    ⊲-⊗-commute = glue′ right (parallel left₁ left₂)

  ⊲-⊗-homo : NaturalTransformation (⊗ ∙ (G ⁂ G)) (G ∙ -+-)
  ⊲-⊗-homo = ntHelper record
      { η = λ (n , m) → ⊲-⊗ {n} {m}
      ; commute = λ (f , g) → Equiv.sym (⊲-⊗-commute f g)
      }

  ⊲-⊗-α
      : {n m o : 𝒞.Obj}
      → G.₁ (+-assoc.to {n} {m} {o})
      ∘ (μ (M.₀ ((n + m) + o)) ∘ G.₁ i₁ ⊗₁ G.₁ i₂)
      ∘ (μ (M.₀ (n + m)) ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ⊗₁ id
      ≈ (μ (M.₀ (n + m + o)) ∘ G.₁ i₁ ⊗₁ G.₁ i₂)
      ∘ id ⊗₁ (μ (M.₀ (m + o)) ∘ G.₁ i₁ ⊗₁ G.₁ i₂)
      ∘ α⇒
  ⊲-⊗-α {n} {m} {o} = begin
      G.₁ +-α ∘ (⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ∘ (⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ⊗₁ id         ≈⟨ refl⟩∘⟨ pullʳ merge₁ʳ ⟩
      G.₁ +-α ∘ ⊲ ∘ (G.₁ i₁ ∘ ⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ⊗₁ G.₁ i₂                 ≈⟨ extendʳ (⇒⊲ +-α) ⟩
      ⊲ ∘ G.₁ +-α ⊗₁ G.₁ +-α ∘ (G.₁ i₁ ∘ ⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ⊗₁ G.₁ i₂      ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟨
      ⊲ ∘ (G.₁ +-α ∘ G.₁ i₁ ∘ ⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ⊗₁ (G.₁ +-α ∘ G.₁ i₂)     ≈⟨ refl⟩∘⟨ pullˡ (Equiv.sym G.homomorphism) ⟩⊗⟨ [ G ]-resp-square +-α∘i₂ ⟩
      ⊲ ∘ (G.₁ (+-α 𝒞.∘ i₁) ∘ ⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ⊗₁ (G.₁ i₂ ∘ G.₁ i₂)      ≈⟨ refl⟩∘⟨ extendʳ (⇒⊲ (+-α 𝒞.∘ i₁)) ⟩⊗⟨refl ⟩
      ⊲ ∘ (⊲ ∘ G.₁ (+-α 𝒞.∘ i₁) ⊗₁ G.₁ (+-α 𝒞.∘ i₁) ∘ _) ⊗₁ (G.₁ i₂ ∘ G.₁ i₂) ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ⊗-distrib-over-∘) ⟩⊗⟨refl ⟨
      ⊲ ∘ (⊲ ∘ _ ⊗₁ (G.₁ (+-α 𝒞.∘ i₁) ∘ G.₁ i₂)) ⊗₁ (G.₁ i₂ ∘ G.₁ i₂)         ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ [ G ]-resp-∘ +-α∘i₁∘i₁ ⟩⊗⟨ [ G ]-resp-square +-α∘i₁∘i₂) ⟩⊗⟨refl ⟩
      ⊲ ∘ (⊲ ∘ G.₁ i₁ ⊗₁ (G.₁ i₂ ∘ G.₁ i₁)) ⊗₁ (G.₁ i₂ ∘ G.₁ i₂)              ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
      ⊲ ∘ ⊲ ⊗₁ id ∘ (G.₁ i₁ ⊗₁ (G.₁ i₂ ∘ G.₁ i₁)) ⊗₁ (G.₁ i₂ ∘ G.₁ i₂)        ≈⟨ extendʳ (μ-assoc (M.₀ (n + (m + o)))) ⟩
      ⊲ ∘ (id ⊗₁ ⊲ ∘ α⇒) ∘ (G.₁ i₁ ⊗₁ (G.₁ i₂ ∘ G.₁ i₁)) ⊗₁ (G.₁ i₂ ∘ G.₁ i₂) ≈⟨ refl⟩∘⟨ assoc ⟩
      ⊲ ∘ id ⊗₁ ⊲ ∘ α⇒ ∘ (G.₁ i₁ ⊗₁ (G.₁ i₂ ∘ G.₁ i₁)) ⊗₁ (G.₁ i₂ ∘ G.₁ i₂)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
      ⊲ ∘ id ⊗₁ ⊲ ∘ G.₁ i₁ ⊗₁ ((G.₁ i₂ ∘ G.₁ i₁) ⊗₁ (G.₁ i₂ ∘ G.₁ i₂)) ∘ α⇒   ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      ⊲ ∘ G.₁ i₁ ⊗₁ (⊲ ∘ (G.₁ i₂ ∘ G.₁ i₁) ⊗₁ (G.₁ i₂ ∘ G.₁ i₂)) ∘ α⇒         ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (refl⟩∘⟨ ⊗-distrib-over-∘) ⟩∘⟨refl ⟩
      ⊲ ∘ G.₁ i₁ ⊗₁ (⊲ ∘ G.₁ i₂ ⊗₁ G.₁ i₂ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ∘ α⇒            ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (extendʳ (⇒⊲ i₂)) ⟩∘⟨refl ⟨
      ⊲ ∘ G.₁ i₁ ⊗₁ (G.₁ i₂ ∘ ⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ∘ α⇒                      ≈⟨ pushʳ (pushˡ split₂ʳ) ⟩
      (⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ∘ id ⊗₁ (⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ∘ α⇒              ∎
    where
      +-α : (n + m) + o 𝒞.⇒ n + (m + o)
      +-α = +-assoc.to {n} {m} {o}

  module _ {A B : 𝒞.Obj} (f : A 𝒞.⇒ B) where

    ⊲-εʳ : ⊲ ∘ G.₁ f ⊗₁ ε ≈ G.₁ f ∘ ρ⇒
    ⊲-εʳ = begin
        ⊲ ∘ G.₁ f ⊗₁ ε            ≈⟨ refl⟩∘⟨ serialize₂₁ ⟩
        ⊲ ∘ id ⊗₁ ε ∘ G.₁ f ⊗₁ id ≈⟨ pullˡ (Equiv.sym (μ-identityʳ (M.₀ B))) ⟩
        ρ⇒ ∘ G.₁ f ⊗₁ id          ≈⟨ unitorʳ-commute-from ⟩
        G.₁ f ∘ ρ⇒                ∎

    ⊲-εˡ : ⊲ ∘ ε ⊗₁ G.₁ f ≈ G.₁ f ∘ λ⇒
    ⊲-εˡ = begin
        ⊲ ∘ ε ⊗₁ G.₁ f            ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩
        ⊲ ∘ ε ⊗₁ id ∘ id ⊗₁ G.₁ f ≈⟨ pullˡ (Equiv.sym (μ-identityˡ (M.₀ B))) ⟩
        λ⇒ ∘ id ⊗₁ G.₁ f          ≈⟨ unitorˡ-commute-from ⟩
        G.₁ f ∘ λ⇒                ∎

  module _ {n : 𝒞.Obj} where

    ⊲-⊗-λ : G.₁ (+-λ.from {n}) ∘ ⊲-⊗ ∘ ε ⊗₁ id ≈ λ⇒
    ⊲-⊗-λ = begin
        G.₁ +-λ.from ∘ (⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ∘ ε ⊗₁ id ≈⟨ refl⟩∘⟨ pullʳ merge₁ʳ ⟩
        G.₁ +-λ.from ∘ ⊲ ∘ (G.₁ i₁ ∘ ε) ⊗₁ G.₁ i₂       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⇒ε i₁ ⟩⊗⟨refl ⟩
        G.₁ +-λ.from ∘ ⊲ ∘ ε ⊗₁ G.₁ i₂                  ≈⟨ refl⟩∘⟨ ⊲-εˡ i₂ ⟩
        G.₁ +-λ.from ∘ G.₁ i₂ ∘ λ⇒                      ≈⟨ cancelˡ ([ G ]-resp-∘ +-λ∘i₂ ○ G.identity) ⟩
        λ⇒                                              ∎

    ⊲-⊗-ρ : G.₁ (+-ρ.from {n}) ∘ ⊲-⊗ ∘ id ⊗₁ ε ≈ ρ⇒
    ⊲-⊗-ρ = begin
        G.₁ +-ρ.from ∘ (⊲ ∘ G.₁ i₁ ⊗₁ G.₁ i₂) ∘ id ⊗₁ ε ≈⟨ refl⟩∘⟨ pullʳ merge₂ʳ ⟩
        G.₁ +-ρ.from ∘ ⊲ ∘ G.₁ i₁ ⊗₁ (G.₁ i₂ ∘ ε)       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ ⇒ε i₂ ⟩
        G.₁ +-ρ.from ∘ ⊲ ∘ G.₁ i₁ ⊗₁ ε                  ≈⟨ refl⟩∘⟨ ⊲-εʳ i₁ ⟩
        G.₁ +-ρ.from ∘ G.₁ i₁ ∘ ρ⇒                      ≈⟨ cancelˡ ([ G ]-resp-∘ +-ρ∘i₁ ○ G.identity) ⟩
        ρ⇒                                              ∎

F,⊗,ε : MonoidalFunctor 𝒞-MC S
F,⊗,ε = record
    { F = G
    ; isMonoidal = record
        { ε = ε
        ; ⊗-homo = ⊲-⊗-homo
        ; associativity = ⊲-⊗-α
        ; unitaryˡ = ⊲-⊗-λ
        ; unitaryʳ = ⊲-⊗-ρ 
        }
    }

module F,⊗,ε = MonoidalFunctor F,⊗,ε
