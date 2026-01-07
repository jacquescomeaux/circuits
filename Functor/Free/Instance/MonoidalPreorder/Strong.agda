{-# OPTIONS --without-K --safe #-}

module Functor.Free.Instance.MonoidalPreorder.Strong where

import Categories.Category.Monoidal.Utilities as ⊗-Util
import Functor.Free.Instance.Preorder as Preorder

open import Categories.Category using (Category)
open import Categories.Category.Instance.Monoidals using (StrongMonoidals)
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Categories.Functor.Monoidal.Properties using (∘-StrongMonoidal)
open import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal using (module Strong)
open import Category.Instance.Preorder.Primitive.Monoidals.Strong using (_≃_; module ≃) renaming (Monoidals to Monoidalsₚ)
open import Data.Product using (_,_)
open import Level using (Level)
open import Preorder.Primitive using (module Isomorphism)
open import Preorder.Primitive.MonotoneMap using (MonotoneMap)
open import Preorder.Primitive.Monoidal using (MonoidalPreorder)
open import Preorder.Primitive.MonotoneMap.Monoidal.Strong using (MonoidalMonotone)

open Strong using (MonoidalNaturalIsomorphism)
 
-- The free monoidal preorder of a monoidal category

module _ {o ℓ e : Level} where

  monoidalPreorder : MonoidalCategory o ℓ e → MonoidalPreorder o ℓ
  monoidalPreorder C = record
      { U = Preorder.Free.₀ U
      ; monoidal = record
          { unit = unit
          ; tensor = Preorder.Free.₁ ⊗
          ; unitaryˡ = Preorder.Free.F-resp-≈ unitorˡ-naturalIsomorphism
          ; unitaryʳ = Preorder.Free.F-resp-≈ unitorʳ-naturalIsomorphism
          ; associative = λ x y z → record
              { from = associator.from {x} {y} {z}
              ; to = associator.to {x} {y} {z}
              }
          }
      }
    where
      open MonoidalCategory C
      open ⊗-Util monoidal

  module _ {A B : MonoidalCategory o ℓ e} where

    monoidalMonotone : StrongMonoidalFunctor A B → MonoidalMonotone (monoidalPreorder A) (monoidalPreorder B)
    monoidalMonotone F = record
        { F = Preorder.Free.₁ F.F
        ; ε = record { F.ε }
        ; ⊗-homo = λ p₁ p₂ → Preorder.Free.F-resp-≈ F.⊗-homo (p₁ , p₂)
        }
      where
        module F = StrongMonoidalFunctor F

    open MonoidalNaturalIsomorphism using (U)

    pointwiseIsomorphism
        : {F G : StrongMonoidalFunctor A B}
        → MonoidalNaturalIsomorphism F G
        → monoidalMonotone F ≃ monoidalMonotone G
    pointwiseIsomorphism F≃G = Preorder.Free.F-resp-≈ (U F≃G)

Free : {o ℓ e : Level} → Functor (StrongMonoidals o ℓ e) (Monoidalsₚ o ℓ)
Free = record
    { F₀ = monoidalPreorder
    ; F₁ = monoidalMonotone
    ; identity = λ {A} → ≃.refl {A = monoidalPreorder A} {x = id}
    ; homomorphism = λ {f = f} {h} → ≃.refl {x = monoidalMonotone (∘-StrongMonoidal h f)}
    ; F-resp-≈ = pointwiseIsomorphism
    }
  where
    open Category (Monoidalsₚ _ _) using (id)

module Free {o ℓ e} = Functor (Free {o} {ℓ} {e})
