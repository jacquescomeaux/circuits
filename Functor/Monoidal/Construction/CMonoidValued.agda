{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Cocartesian using (Cocartesian)
open import Category.Construction.CMonoids using (CMonoids)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor using (Functor) renaming (_∘F_ to _∙_)
open import Level using (Level; _⊔_)

-- A functor from a cocartesian category 𝒞 to CMonoids[S]
-- can be turned into a symmetric monoidal functor from 𝒞 to S

module Functor.Monoidal.Construction.CMonoidValued
    {o o′ ℓ ℓ′ e e′ : Level}
    {𝒞 : Category o ℓ e}
    (𝒞-+ : Cocartesian 𝒞)
    {S : SymmetricMonoidalCategory o′ ℓ′ e′}
    (let module S = SymmetricMonoidalCategory S)
    (M : Functor 𝒞 (CMonoids S.symmetric))
  where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Object.Monoid.Commutative as CommutativeMonoidObject
import Functor.Monoidal.Construction.MonoidValued as MonoidValued

open import Categories.Category.Cocartesian.SymmetricMonoidal using (module CocartesianSymmetricMonoidal)
open import Categories.Category.Cocartesian.Bundle using (CocartesianCategory)
open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Category.Monoidal.Symmetric.Properties using (module Shorthands)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Categories.Functor.Properties using ([_]-resp-∘)
open import Data.Product using (_,_)
open import Functor.Forgetful.Instance.CMonoid S.symmetric using (Forget)
open import Functor.Forgetful.Instance.Monoid S.monoidal using () renaming (Forget to Forgetₘ)

private

  G : Functor 𝒞 (Monoids S.monoidal)
  G = Forget ∙ M

  H : Functor 𝒞 S.U
  H = Forgetₘ ∙ G

  module 𝒞 = CocartesianCategory (record { cocartesian = 𝒞-+ })
  module 𝒞-SM = CocartesianSymmetricMonoidal 𝒞 𝒞-+

  𝒞-SMC : SymmetricMonoidalCategory o ℓ e
  𝒞-SMC = record { symmetric = 𝒞-SM.+-symmetric }

  module H = Functor H
  module M = Functor M

  open CommutativeMonoidObject S.symmetric using (CommutativeMonoid; CommutativeMonoid⇒)
  open CommutativeMonoid using (μ; Carrier) renaming (commutative to μ-commutative)
  open CommutativeMonoid⇒
  open 𝒞 using (_+_; i₁; i₂; inject₁; inject₂; +-swap)
  open S
  open ⇒-Reasoning U
  open ⊗-Reasoning monoidal
  open Shorthands symmetric

  ⊲ : {A : 𝒞.Obj} → H.₀ A ⊗₀ H.₀ A ⇒ H.₀ A
  ⊲ {A} = μ (M.₀ A)

  ⇒⊲ : {A B : 𝒞.Obj} (f : A 𝒞.⇒ B) → H.₁ f ∘ ⊲ ≈ ⊲ ∘ H.₁ f ⊗₁ H.₁ f
  ⇒⊲ f = preserves-μ (M.₁ f)

  ⊲-⊗ : {n m : 𝒞.Obj} → H.₀ n ⊗₀ H.₀ m ⇒ H.₀ (n + m)
  ⊲-⊗ = ⊲ ∘ H.₁ i₁ ⊗₁ H.₁ i₂

  ⊲-σ : {n : 𝒞.Obj} → ⊲ {n} ≈ ⊲ ∘ σ⇒
  ⊲-σ {A} = μ-commutative (M.₀ A)

  braiding-compat
      : {n m : 𝒞.Obj}
      → H.₁ +-swap ∘ ⊲-⊗ {n} {m}
      ≈ ⊲-⊗ ∘ σ⇒ {H.₀ n} {H.₀ m}
  braiding-compat {n} {m} = begin
      H.₁ +-swap ∘ ⊲-⊗ {n} {m}                                    ≡⟨⟩
      H.₁ +-swap ∘ ⊲ {n + m} ∘ H.₁ i₁ ⊗₁ H.₁ i₂                   ≈⟨ extendʳ (⇒⊲ +-swap) ⟩
      ⊲ {m + n} ∘ H.₁ +-swap ⊗₁ H.₁ +-swap ∘ H.₁ i₁ ⊗₁ H.₁ i₂     ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟨
      ⊲ {m + n} ∘ (H.₁ +-swap ∘ H.₁ i₁) ⊗₁ (H.₁ +-swap ∘ H.₁ i₂)  ≈⟨ refl⟩∘⟨ [ H ]-resp-∘ inject₁ ⟩⊗⟨ [ H ]-resp-∘ inject₂ ⟩
      ⊲ {m + n} ∘ H.₁ i₂ ⊗₁ H.₁ i₁                                ≈⟨ ⊲-σ ⟩∘⟨refl ⟩
      (⊲ {m + n} ∘ σ⇒) ∘ H.₁ i₂ ⊗₁ H.₁ i₁                         ≈⟨ extendˡ (braiding.⇒.commute (H.₁ i₂ , H.₁ i₁)) ⟩
      (⊲ {m + n} ∘ H.₁ i₁ ⊗₁ H.₁ i₂) ∘ σ⇒                         ≡⟨⟩
      ⊲-⊗ {m} {n} ∘ σ⇒ {H.₀ n} {H.₀ m}                            ∎

open MonoidValued 𝒞-+ G using (F,⊗,ε)

F,⊗,ε,σ : Lax.SymmetricMonoidalFunctor 𝒞-SMC S
F,⊗,ε,σ = record
    { F,⊗,ε
    ; isBraidedMonoidal = record
        { F,⊗,ε
        ; braiding-compat = braiding-compat
        }
    }

module F,⊗,ε,σ = Lax.SymmetricMonoidalFunctor F,⊗,ε,σ
