{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Cocartesian.Bundle using (CocartesianCategory)
open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor using (Functor) renaming (_∘F_ to _∙_)
open import Category.Construction.CMonoids using (CMonoids)

open import Level using (Level)

module Functor.Monoidal.Construction.MultisetOf
    {o ℓ e : Level}
    {𝒞 : CocartesianCategory o ℓ e}
    {S : SymmetricMonoidalCategory o ℓ e}
    (let module 𝒞 = CocartesianCategory 𝒞)
    (let module S = SymmetricMonoidalCategory S)
    (G : Functor 𝒞.U S.U)
    (M : Functor S.U (CMonoids S.symmetric))
  where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Category.Monoidal.Utilities as ⊗-Util
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Object.Monoid.Commutative as CMonoidObject

open import Categories.Category.Cocartesian using (module CocartesianSymmetricMonoidal)
open import Categories.Category.Monoidal.Symmetric.Properties using (module Shorthands)
open import Categories.Functor.Monoidal using (MonoidalFunctor)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Categories.Functor.Properties using ([_]-resp-∘)
open import Data.Product using (_,_)

module G = Functor G
module M = Functor M
module 𝒞-SM = CocartesianSymmetricMonoidal 𝒞.U 𝒞.cocartesian

open 𝒞 using (⊥; -+-; _+_; _+₁_; i₁; i₂; inject₁; inject₂; +-swap)
open Lax using (SymmetricMonoidalFunctor)

open S
open Functor
open CMonoidObject symmetric using (CommutativeMonoid; CommutativeMonoid⇒)
open CommutativeMonoid renaming (assoc to μ-assoc; identityˡ to μ-identityˡ; identityʳ to μ-identityʳ; commutative to μ-commutative)
open CommutativeMonoid⇒

Forget : Functor (CMonoids symmetric) (Monoids monoidal)
Forget .F₀ = monoid
Forget .F₁ = monoid⇒
Forget .identity = Equiv.refl
Forget .homomorphism = Equiv.refl
Forget .F-resp-≈ x = x

𝒞-SMC : SymmetricMonoidalCategory o ℓ e
𝒞-SMC = record { symmetric = 𝒞-SM.+-symmetric }

open import Functor.Monoidal.Construction.ListOf {𝒞 = 𝒞} G (Forget ∙ M)
    using (List∘G; ListOf,++,[]; module LG; ++; module List; ++⇒)

open Shorthands symmetric

++-swap : {A : Obj} → ++ {A} ≈ ++ ∘ σ⇒
++-swap {A} = μ-commutative (M.₀ A)

open ⇒-Reasoning U
open ⊗-Reasoning monoidal

++-⊗-σ
    : {X Y : 𝒞.Obj}
    → LG.₁ (+-swap {X} {Y}) ∘ ++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂
    ≈ (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ∘ σ⇒
++-⊗-σ {X} {Y} = begin
    LG.₁ +-swap ∘ ++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂                   ≈⟨ extendʳ (++⇒ (G.₁ +-swap)) ⟩
    ++ ∘ LG.₁ +-swap ⊗₁ LG.₁ +-swap ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂    ≈⟨ refl⟩∘⟨ ⊗-distrib-over-∘ ⟨
    ++ ∘ (LG.₁ +-swap ∘ LG.₁ i₁) ⊗₁ (LG.₁ +-swap ∘ LG.₁ i₂) ≈⟨ refl⟩∘⟨ [ List∘G ]-resp-∘ inject₁ ⟩⊗⟨ [ List∘G ]-resp-∘ inject₂ ⟩
    ++ ∘ LG.₁ i₂ ⊗₁ LG.₁ i₁                                 ≈⟨ pushˡ ++-swap ⟩
    ++ ∘ σ⇒ ∘ LG.₁ i₂ ⊗₁ LG.₁ i₁                            ≈⟨ pushʳ (braiding.⇒.commute (LG.₁ i₂ , LG.₁ i₁ )) ⟩
    (++ ∘ LG.₁ i₁ ⊗₁ LG.₁ i₂) ∘ σ⇒                          ∎

open SymmetricMonoidalFunctor

module ListOf,++,[] = MonoidalFunctor ListOf,++,[]

BagOf,++,[] : SymmetricMonoidalFunctor 𝒞-SMC S
BagOf,++,[] .F = List∘G
BagOf,++,[] .isBraidedMonoidal = record
    { isMonoidal = ListOf,++,[].isMonoidal
    ; braiding-compat = ++-⊗-σ
    }
