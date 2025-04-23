{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Level using (Level)

module Functor.Cartesian.Instance.Underlying.SymmetricMonoidal.FinitelyCocomplete {o ℓ e : Level} where

import Categories.Morphism.Reasoning as ⇒-Reasoning
import Categories.Category.Monoidal.Utilities as ⊗-Util

open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Product using (_※_)
open import Categories.Category.Product.Properties using () renaming (project₁ to p₁; project₂ to p₂; unique to u)
open import Categories.Functor.Core using (Functor)
open import Categories.Functor.Cartesian using (CartesianF)
open import Categories.Functor.Monoidal.Symmetric using (module Lax)
open import Categories.NaturalTransformation.Core using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric using (module Lax)
open import Categories.Object.Product using (IsProduct)
open import Categories.Object.Terminal using (IsTerminal)
open import Data.Product.Base using (_,_; <_,_>; proj₁; proj₂)

open import Category.Cartesian.Instance.FinitelyCocompletes {o} {ℓ} {e} using (FinitelyCocompletes-CC)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Category.Cartesian.Instance.SymMonCat {o} {ℓ} {e} using (SymMonCat-CC)
open import Functor.Instance.Underlying.SymmetricMonoidal.FinitelyCocomplete {o} {ℓ} {e} using () renaming (Underlying to U)

module CartesianCategory′ {o ℓ e : Level} (C : CartesianCategory o ℓ e) where
  module CC = CartesianCategory C
  open import Categories.Object.Terminal using (Terminal)
  open Terminal CC.terminal public
  open import Categories.Category.BinaryProducts using (BinaryProducts)
  open BinaryProducts CC.products public
  open CC public

module FC = CartesianCategory′ FinitelyCocompletes-CC
module SMC = CartesianCategory′ SymMonCat-CC
module U = Functor U

F-resp-⊤ : IsTerminal SMC.U (U.₀ FC.⊤)
F-resp-⊤ = _

F-resp-× : {A B : FC.Obj} → IsProduct SMC.U (U.₁ (FC.π₁ {A} {B})) (U.₁ (FC.π₂ {A} {B}))
F-resp-× {A} {B} = record
    { ⟨_,_⟩ = pairing
    ; project₁ = λ { {C} {F} {G} → project₁ {C} F G }
    ; project₂ = λ { {C} {F} {G} → project₂ {C} F G }
    ; unique = λ { {C} {H} {F} {G} ≃₁ ≃₂ → unique {C} F G H ≃₁ ≃₂ }
    }
  where
    module _ {C : SMC.Obj} (F : Lax.SymmetricMonoidalFunctor C (U.₀ A)) (G : Lax.SymmetricMonoidalFunctor C (U.₀ B)) where
      module F = Lax.SymmetricMonoidalFunctor F
      module G = Lax.SymmetricMonoidalFunctor G
      pairing : Lax.SymmetricMonoidalFunctor C (U.₀ (A FC.× B))
      pairing = record
          { F = F.F ※ G.F
          ; isBraidedMonoidal = record
              { isMonoidal = record
                  { ε = F.ε , G.ε
                  ; ⊗-homo = ntHelper record
                      { η = < F.⊗-homo.η , G.⊗-homo.η >
                      ; commute = < F.⊗-homo.commute , G.⊗-homo.commute >
                      }
                  ; associativity = F.associativity , G.associativity
                  ; unitaryˡ = F.unitaryˡ , G.unitaryˡ
                  ; unitaryʳ = F.unitaryʳ , G.unitaryʳ
                  }
              ; braiding-compat = F.braiding-compat , G.braiding-compat
              }
          }
      module pairing = Lax.SymmetricMonoidalFunctor pairing
      module A = FinitelyCocompleteCategory A
      module B = FinitelyCocompleteCategory B
      module C = SymmetricMonoidalCategory C
      module A′ = SymmetricMonoidalCategory (U.₀ A)
      module B′ = SymmetricMonoidalCategory (U.₀ B)
      project₁ : Lax.SymmetricMonoidalNaturalIsomorphism ((U.₁ (FC.π₁ {A} {B})) SMC.∘ pairing) F
      project₁ = record
          { U = p₁ {o} {ℓ} {e} {o} {ℓ} {e} {o} {ℓ} {e} {A.U} {B.U} {C.U} {F.F} {G.F}
          ; F⇒G-isMonoidal = record
              { ε-compat = ¡-unique₂ (id ∘ F.ε ∘ ¡) F.ε
              ; ⊗-homo-compat = λ { {X} {Y} → identityˡ ○ refl⟩∘⟨ sym ([]-cong₂ identityʳ identityʳ) }
              }
          }
        where
          open FinitelyCocompleteCategory A
          open HomReasoning
          open Equiv
          open ⇒-Reasoning A.U
      project₂ : Lax.SymmetricMonoidalNaturalIsomorphism (U.₁ {A FC.× B} {B} FC.π₂ SMC.∘ pairing) G
      project₂ = record
          { U = p₂ {o} {ℓ} {e} {o} {ℓ} {e} {o} {ℓ} {e} {A.U} {B.U} {C.U} {F.F} {G.F}
          ; F⇒G-isMonoidal = record
              { ε-compat = ¡-unique₂ (id ∘ G.ε ∘ ¡) G.ε
              ; ⊗-homo-compat = λ { {X} {Y} → identityˡ ○ refl⟩∘⟨ sym ([]-cong₂ identityʳ identityʳ) }
              }
          }
        where
          open FinitelyCocompleteCategory B
          open HomReasoning
          open Equiv
          open ⇒-Reasoning B.U
      unique
          : (H : Lax.SymmetricMonoidalFunctor C (U.F₀ (A FC.× B)))
          → Lax.SymmetricMonoidalNaturalIsomorphism (U.₁ {A FC.× B} {A} FC.π₁ SMC.∘ H) F
          → Lax.SymmetricMonoidalNaturalIsomorphism (U.₁ {A FC.× B} {B} FC.π₂ SMC.∘ H) G
          → Lax.SymmetricMonoidalNaturalIsomorphism pairing H
      unique H ≃₁ ≃₂ = record
          { U = u {o} {ℓ} {e} {o} {ℓ} {e} {o} {ℓ} {e} {A.U} {B.U} {C.U} {F.F} {G.F} {H.F} ≃₁.U ≃₂.U
          ; F⇒G-isMonoidal = record
              { ε-compat = ε-compat₁ , ε-compat₂
              ; ⊗-homo-compat =
                  λ { {X} {Y} → ⊗-homo-compat₁ {X} {Y} , ⊗-homo-compat₂ {X} {Y} }
              }
          }
        where
          module H = Lax.SymmetricMonoidalFunctor H
          module ≃₁ = Lax.SymmetricMonoidalNaturalIsomorphism ≃₁
          module ≃₂ = Lax.SymmetricMonoidalNaturalIsomorphism ≃₂
          ε-compat₁ : ≃₁.⇐.η C.unit A.∘ F.ε A.≈ proj₁ H.ε
          ε-compat₁ = refl⟩∘⟨ sym ≃₁.ε-compat ○ cancelˡ (≃₁.iso.isoˡ C.unit) ○ ¡-unique₂ (proj₁ H.ε ∘ ¡) (proj₁ H.ε)
            where
              open A
              open HomReasoning
              open ⇒-Reasoning A.U
              open Equiv
          ε-compat₂ : ≃₂.⇐.η C.unit B.∘ G.ε B.≈ proj₂ H.ε
          ε-compat₂ = refl⟩∘⟨ sym ≃₂.ε-compat ○ cancelˡ (≃₂.iso.isoˡ C.unit) ○ ¡-unique₂ (proj₂ H.ε ∘ ¡) (proj₂ H.ε)
            where
              open B
              open HomReasoning
              open ⇒-Reasoning B.U
              open Equiv
          ⊗-homo-compat₁
              : {X Y : C.Obj}
              → ≃₁.⇐.η (C.⊗.₀ (X , Y))
              A.∘ F.⊗-homo.η (X , Y)
              A.≈ proj₁ (H.⊗-homo.η (X , Y))
              A.∘ (≃₁.⇐.η X A.+₁ ≃₁.⇐.η Y)
          ⊗-homo-compat₁ {X} {Y} = switch-fromtoʳ (≃₁.FX≅GX ⊗ᵢ ≃₁.FX≅GX) (assoc ○ sym (switch-fromtoˡ ≃₁.FX≅GX (refl⟩∘⟨ introʳ A.+-η ○ ≃₁.⊗-homo-compat)))
            where
              open A
              open HomReasoning
              open Equiv
              open ⇒-Reasoning A.U
              open ⊗-Util A′.monoidal
          ⊗-homo-compat₂
              : {X Y : C.Obj}
              → ≃₂.⇐.η (C.⊗.₀ (X , Y))
              B.∘ G.⊗-homo.η (X , Y)
              B.≈ proj₂ (H.⊗-homo.η (X , Y))
              B.∘ (≃₂.⇐.η X B.+₁ ≃₂.⇐.η Y)
          ⊗-homo-compat₂ = switch-fromtoʳ (≃₂.FX≅GX ⊗ᵢ ≃₂.FX≅GX) (assoc ○ sym (switch-fromtoˡ ≃₂.FX≅GX (refl⟩∘⟨ introʳ B.+-η ○ ≃₂.⊗-homo-compat)))
            where
              open B
              open HomReasoning
              open Equiv
              open ⇒-Reasoning B.U
              open ⊗-Util B′.monoidal

Underlying : CartesianF FinitelyCocompletes-CC SymMonCat-CC
Underlying = record
    { F = U
    ; isCartesian = record
        { F-resp-⊤ = F-resp-⊤
        ; F-resp-× = F-resp-×
        }
    }
