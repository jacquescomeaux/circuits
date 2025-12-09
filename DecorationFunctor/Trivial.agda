{-# OPTIONS --without-K --safe #-}

module DecorationFunctor.Trivial where

open import Level using (0ℓ)

open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using (Functor) renaming (_∘F_ to _∘_)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Category.Instance.Nat.FinitelyCocomplete using (Nat-FinitelyCocomplete)
open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} {0ℓ} using (Setoids-×; ×-symmetric′)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid.Unit {0ℓ} {0ℓ} using (⊤ₛ)
open import Data.Unit using (tt)
open import Data.Unit.Properties using () renaming (≡-setoid to ⊤-≡ₛ)
open import Function using (Func; const)
open import Function.Construct.Constant using () renaming (function to Const)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using (products)
open BinaryProducts products using (-×-)
open FinitelyCocompleteCategory Nat-FinitelyCocomplete
  using (-+-)
  renaming (symmetricMonoidalCategory to Nat-smc)
open Lax using (SymmetricMonoidalFunctor)

F : Functor Nat (Setoids 0ℓ 0ℓ)
F = record
    { F₀ = const ⊤-≡ₛ
    ; F₁ = const (Const ⊤-≡ₛ ⊤-≡ₛ tt)
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = const refl
    }

ε : Func ⊤ₛ ⊤-≡ₛ
ε = Const ⊤ₛ ⊤-≡ₛ tt

⊗-homomorphism : NaturalTransformation (-×- ∘ (F ⁂ F)) (F ∘ -+-)
⊗-homomorphism = ntHelper record
    { η = const (Const (⊤-≡ₛ ×ₛ ⊤-≡ₛ) ⊤-≡ₛ tt)
    ; commute = const refl
    }

opaque
  unfolding ×-symmetric′

  trivial : SymmetricMonoidalFunctor Nat-smc Setoids-×
  trivial = record
      { F = F
      ; isBraidedMonoidal = record
          { isMonoidal = record
              { ε = ε
              ; ⊗-homo = ⊗-homomorphism
              ; associativity = refl
              ; unitaryˡ = refl
              ; unitaryʳ = refl
              }
          ; braiding-compat = refl
          }
      }

and-gate : Func ⊤ₛ ⊤-≡ₛ
and-gate = Const ⊤ₛ ⊤-≡ₛ tt
