{-# OPTIONS --without-K --safe #-}

module DecorationFunctor.Trivial where

import Categories.Morphism as Morphism

open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cocartesian using (Cocartesian; module BinaryCoproducts)
open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Nat using (Nat-Cocartesian)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Product using (_⁂_)
open import Categories.Functor using () renaming (_∘F_ to _∘_)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Category.Instance.Setoids.SymmetricMonoidal using (Setoids-×)
open import Category.Instance.Nat.FinitelyCocomplete using (Nat-FinitelyCocomplete)
open import Data.Nat using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Unit using (tt)
open import Data.Unit.Properties using () renaming (≡-setoid to ⊤-setoid)
open import Function.Base using (const)
open import Function.Bundles using (Func)
open import Level using (0ℓ; suc; lift)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core using (refl)

open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using (products)
open Cocartesian Nat-Cocartesian using (coproducts)
open FinitelyCocompleteCategory Nat-FinitelyCocomplete
    using ()
    renaming (symmetricMonoidalCategory to Nat-smc)
open Morphism (Setoids 0ℓ 0ℓ) using (_≅_)
open Lax using (SymmetricMonoidalFunctor)

open BinaryProducts products using (-×-)
open BinaryCoproducts coproducts using (-+-)


F : Functor Nat (Setoids 0ℓ 0ℓ)
F = record
    { F₀ = const (⊤-setoid)
    ; F₁ = const (record { to = const tt ; cong = const refl })
    ; identity = const refl
    ; homomorphism = const refl
    ; F-resp-≈ = const (const refl)
    }

ε : Func (SingletonSetoid {0ℓ} {0ℓ}) ⊤-setoid
ε = record
    { to = const tt
    ; cong = const refl
    }

⊗-homomorphism : NaturalTransformation (-×- ∘ (F ⁂ F)) (F ∘ -+-)
⊗-homomorphism = record
    { η = const (record { to = const tt ; cong = const refl })
    ; commute = const (const refl)
    ; sym-commute = const (const refl)
    }

trivial : SymmetricMonoidalFunctor Nat-smc (Setoids-× {0ℓ})
trivial = record
    { F = F
    ; isBraidedMonoidal = record
        { isMonoidal = record
            { ε = ε
            ; ⊗-homo = ⊗-homomorphism
            ; associativity = const refl
            ; unitaryˡ = const refl
            ; unitaryʳ = const refl
            }
        ; braiding-compat = const refl
        }
    }

and-gate : Func (SingletonSetoid {0ℓ} {0ℓ}) ⊤-setoid
and-gate = record
    { to = const tt
    ; cong = const refl
    }
