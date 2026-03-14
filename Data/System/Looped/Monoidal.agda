{-# OPTIONS --without-K --safe #-}

open import Level using (Level; 0ℓ; suc)

module Data.System.Looped.Monoidal {ℓ : Level} where

import Categories.Morphism as Morphism
import Data.System.Monoidal {ℓ} as Unlooped

open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Functor.Bifunctor using (Bifunctor; flip-bifunctor)
open import Data.Nat using (ℕ)
open import Data.System.Core {ℓ} using (System)
open import Data.System.Looped {ℓ} using (Systems[_])

module _ (n : ℕ) where

  private

    module Systems-MC = MonoidalCategory (Unlooped.Systems-MC n n)

    ⊗ : Bifunctor Systems[ n ] Systems[ n ] Systems[ n ]
    ⊗ = record
        { F₀ = Systems-MC.⊗.₀
        ; F₁ = Systems-MC.⊗.₁
        ; identity = λ {X} → Systems-MC.⊗.identity {X}
        ; homomorphism = λ {f = f} {g} → Systems-MC.⊗.homomorphism {f = f} {g}
        ; F-resp-≈ = λ {f = f} {g} → Systems-MC.⊗.F-resp-≈ {f = f} {g}
        }

    module _ {X : System n n} where

      open Morphism Systems[ n ] using (_≅_; module Iso)
      open Systems-MC using (_⊗₀_)

      unitorˡ : Systems-MC.unit ⊗₀ X ≅ X
      unitorˡ = record
          { from = Systems-MC.unitorˡ.from
          ; to = Systems-MC.unitorˡ.to
          ; iso = record
              { isoˡ = Systems-MC.unitorˡ.isoˡ {X}
              ; isoʳ = Systems-MC.unitorˡ.isoʳ {X}
              }
          }

      unitorʳ : X ⊗₀ Systems-MC.unit ≅ X
      unitorʳ = record
          { from = Systems-MC.unitorʳ.from
          ; to = Systems-MC.unitorʳ.to
          ; iso = record
              { isoˡ = Systems-MC.unitorʳ.isoˡ {X}
              ; isoʳ = Systems-MC.unitorʳ.isoʳ {X}
              }
          }

    module _ {X Y Z : System n n} where

      module X = System X
      module Y = System Y
      module Z = System Z

      open Morphism Systems[ n ] using (_≅_; module Iso)
      open Systems-MC using (_⊗₀_)

      associator : (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)
      associator = record
          { from = Systems-MC.associator.from
          ; to = Systems-MC.associator.to
          ; iso = record
              { isoˡ = Systems-MC.associator.isoˡ {X} {Y} {Z}
              ; isoʳ = Systems-MC.associator.isoʳ {X} {Y} {Z}
              }
          }

  Systems-Monoidal : Monoidal Systems[ n ]
  Systems-Monoidal = record
      { ⊗ = ⊗
      ; unit = Systems-MC.unit
      ; unitorˡ = unitorˡ
      ; unitorʳ = unitorʳ
      ; associator = associator
      ; unitorˡ-commute-from = λ {f = f} → Systems-MC.unitorˡ-commute-from {f = f}
      ; unitorˡ-commute-to = λ {f = f} → Systems-MC.unitorˡ-commute-to {f = f}
      ; unitorʳ-commute-from = λ {f = f} → Systems-MC.unitorʳ-commute-from {f = f}
      ; unitorʳ-commute-to = λ {f = f} → Systems-MC.unitorʳ-commute-to {f = f}
      ; assoc-commute-from = λ {f = f} {g = g} {h = h} → Systems-MC.assoc-commute-from {f = f} {g = g} {h = h}
      ; assoc-commute-to = λ {f = f} {g = g} {h = h} → Systems-MC.assoc-commute-to {f = f} {g = g} {h = h}
      ; triangle = λ {X Y} → Systems-MC.triangle {X} {Y}
      ; pentagon = λ {X Y Z W} → Systems-MC.pentagon {X} {Y} {Z} {W}
      }

  private

    module Systems-SMC = SymmetricMonoidalCategory (Unlooped.Systems-SMC n n)

    braiding : ⊗ ≃ flip-bifunctor ⊗
    braiding = record
        { F⇒G = record { Systems-SMC.braiding.⇒ }
        ; F⇐G = record { Systems-SMC.braiding.⇐ }
        ; iso = λ X → record { Systems-SMC.braiding.iso X }
        }

  Systems-Symmetric : Symmetric Systems-Monoidal
  Systems-Symmetric = record
      { braided = record
          { braiding = braiding
          ; hexagon₁ = λ {X Y Z} → Systems-SMC.hexagon₁ {X} {Y} {Z}
          ; hexagon₂ = λ {X Y Z} → Systems-SMC.hexagon₂ {X} {Y} {Z}
          }
      ; commutative = λ {X Y} → Systems-SMC.commutative {X} {Y}
      }

  Systems-MC : MonoidalCategory (suc 0ℓ) ℓ 0ℓ
  Systems-MC = record { monoidal = Systems-Monoidal }

  Systems-SMC : SymmetricMonoidalCategory (suc 0ℓ) ℓ 0ℓ
  Systems-SMC = record { symmetric = Systems-Symmetric }
