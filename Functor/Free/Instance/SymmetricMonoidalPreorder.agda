{-# OPTIONS --without-K --safe #-}

module Functor.Free.Instance.SymmetricMonoidalPreorder where

import Functor.Free.Instance.MonoidalPreorder as MP

open import Categories.Category using (Category)
open import Category.Instance.SymMonCat using (SymMonCat)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal.Symmetric using () renaming (module Lax to Lax₁)
open import Categories.Functor.Monoidal.Symmetric.Properties using (∘-SymmetricMonoidal)
open import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric using () renaming (module Lax to Lax₂)
open import Category.Instance.SymMonPre.Primitive using (SymMonPre; _≃_; module ≃)
open import Data.Product using (_,_)
open import Level using (Level)
open import Preorder.Primitive.Monoidal using (MonoidalPreorder; SymmetricMonoidalPreorder; SymmetricMonoidalMonotone)

open Lax₁ using (SymmetricMonoidalFunctor)
open Lax₂ using (SymmetricMonoidalNaturalIsomorphism)
 
-- The free symmetric monoidal preorder of a symmetric monoidal category

module _ {o ℓ e : Level} where

  symmetricMonoidalPreorder : SymmetricMonoidalCategory o ℓ e → SymmetricMonoidalPreorder o ℓ
  symmetricMonoidalPreorder C = record
      { M
      ; symmetric = record
          { symmetric = λ x y → braiding.⇒.η (x , y)
          }
      }
    where
      open SymmetricMonoidalCategory C
      module M = MonoidalPreorder (MP.Free.₀ monoidalCategory)

  module _ {A B : SymmetricMonoidalCategory o ℓ e} where

    symmetricMonoidalMonotone
        : SymmetricMonoidalFunctor A B
        → SymmetricMonoidalMonotone (symmetricMonoidalPreorder A) (symmetricMonoidalPreorder B)
    symmetricMonoidalMonotone F = record
        { monoidalMonotone = MP.Free.₁ F.monoidalFunctor
        }
      where
        module F = SymmetricMonoidalFunctor F

    open SymmetricMonoidalNaturalIsomorphism using (⌊_⌋)

    pointwiseIsomorphism
        : {F G : SymmetricMonoidalFunctor A B}
        → SymmetricMonoidalNaturalIsomorphism F G
        → symmetricMonoidalMonotone F ≃ symmetricMonoidalMonotone G
    pointwiseIsomorphism F≃G = MP.Free.F-resp-≈ ⌊ F≃G ⌋

Free : {o ℓ e : Level} → Functor (SymMonCat {o} {ℓ} {e}) (SymMonPre o ℓ)
Free = record
    { F₀ = symmetricMonoidalPreorder
    ; F₁ = symmetricMonoidalMonotone
    ; identity = λ {A} → ≃.refl {A = symmetricMonoidalPreorder A} {x = id}
    ; homomorphism = λ {f = f} {h} → ≃.refl {x = symmetricMonoidalMonotone (∘-SymmetricMonoidal h f)}
    ; F-resp-≈ = pointwiseIsomorphism
    }
  where
    open Category (SymMonPre _ _) using (id)

module Free {o ℓ e} = Functor (Free {o} {ℓ} {e})
