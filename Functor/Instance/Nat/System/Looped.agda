{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --hidden-argument-puns #-}
{-# OPTIONS --lossy-unification #-}

module Functor.Instance.Nat.System.Looped where

open import Level using (suc; 0ℓ)

import Data.System.Monoidal as System-⊗
import Functor.Instance.Nat.System as Unlooped
import Categories.Morphism as Morphism
import Functor.Free.Instance.SymmetricMonoidalPreorder.Strong as SymmetricMonoidalPreorder

open import Category.Instance.Setoids.SymmetricMonoidal using (Setoids-×)

open import Categories.Category.Instance.Cats using (Cats)
open import Categories.Category.Instance.Monoidals using (StrongMonoidals)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Categories.Functor.Monoidal.Properties using (idF-StrongMonoidal; ∘-StrongMonoidal)
open import Categories.Functor.Monoidal.Symmetric using () renaming (module Strong to Strong₃)
open import Categories.Functor.Monoidal.Symmetric.Properties using (idF-StrongSymmetricMonoidal; ∘-StrongSymmetricMonoidal)
open import Categories.NaturalTransformation.NaturalIsomorphism using (_≃_; NaturalIsomorphism)
open import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal using () renaming (module Strong to Strong₂)
open import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric using () renaming (module Strong to Strong₄)
open import Category.Construction.CMonoids (Setoids-×.symmetric {suc 0ℓ} {0ℓ}) using (CMonoids)
open import Category.Instance.SymMonCat using () renaming (module Strong to Strong₁)
open import Data.Circuit.Value using (monoid)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.System using (System; _≤_; _≈_; Systems[_]; ≤-refl; ≤-trans; discrete)
open import Data.System.Looped.Monoidal using (Systems-MC; Systems-SMC)
open import Data.Values monoid using (module ≋; module Algebra; Values; ≋-isEquiv)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; _∘_; id)
open import Function.Construct.Setoid using (_∙_)
open import Functor.Free.Instance.InducedCMonoid using (InducedCMonoid)
open import Functor.Instance.Nat.Pull using (Pull)
open import Functor.Instance.Nat.Push using (Push)
open import Object.Monoid.Commutative (Setoids-×.symmetric {0ℓ} {0ℓ}) using (CommutativeMonoid; CommutativeMonoid⇒)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

open Functor
open Strong₁ using (SymMonCat)
open Strong₂ using (MonoidalNaturalIsomorphism)
open Strong₃ using (SymmetricMonoidalFunctor)
open Strong₄ using (SymmetricMonoidalNaturalIsomorphism)
open Algebra using (Valuesₘ)

private
  variable A B C : ℕ

opaque

  unfolding ≋-isEquiv

  Sys₁ : (Fin A → Fin B) → Functor Systems[ Valuesₘ A ] Systems[ Valuesₘ B ]
  Sys₁ f = record { Functor (Unlooped.NatCat.Sys.₁ f) }

  Sys-identity : Sys₁ {A} id ≃ idF
  Sys-identity {A} = record
      { F⇒G = record { NI.⇒ }
      ; F⇐G = record { NI.⇐ }
      ; iso = λ X → record { NI.iso X }
      }
    where
      module NI = NaturalIsomorphism (Unlooped.NatCat.Sys.identity {A})

  Sys-homo
      : (f : Fin A → Fin B)
        (g : Fin B → Fin C)
      → Sys₁ (g ∘ f) ≃ Sys₁ g ∘F Sys₁ f
  Sys-homo {A} f g = record
      { F⇒G = record { NI.⇒ }
      ; F⇐G = record { NI.⇐ }
      ; iso = λ X → record { NI.iso X }
      }
    where
      module NI = NaturalIsomorphism (Unlooped.NatCat.Sys.homomorphism {f = f} {g})

  Sys-resp-≈ : {f g : Fin A → Fin B} → f ≗ g → Sys₁ f ≃ Sys₁ g
  Sys-resp-≈ f≗g = record
      { F⇒G = record { NI.⇒ }
      ; F⇐G = record { NI.⇐ }
      ; iso = λ X → record { NI.iso X }
      }
    where
      module NI = NaturalIsomorphism (Unlooped.NatCat.Sys.F-resp-≈ f≗g)

module NatCat where

  Sys : Functor Nat (Cats (suc 0ℓ) 0ℓ 0ℓ)
  Sys .F₀ = λ n → Systems[ Valuesₘ n ]
  Sys .F₁ = Sys₁
  Sys .identity = Sys-identity
  Sys .homomorphism = Sys-homo _ _
  Sys .F-resp-≈ = Sys-resp-≈

  module Sys = Functor Sys

module NatMC where

  module _ (f : Fin A → Fin B) where

    -- module A = System-⊗ A A
    -- module B = System-⊗ B B

    module MF = StrongMonoidalFunctor (Unlooped.NatMC.Sys.₁ f)

    open Morphism using (_≅_; Iso)

    opaque

      unfolding Sys₁ ≋-isEquiv

      Sys-MC₁ : StrongMonoidalFunctor (Systems-MC (Valuesₘ A)) (Systems-MC (Valuesₘ B))
      Sys-MC₁ = record
          { F = Sys₁ f
          ; isStrongMonoidal = record
              { ε = record
                  { _≅_ MF.ε
                  ; iso = record { Iso MF.ε.iso }
                  }
              ; ⊗-homo = record
                  { F⇒G = record { MF.⊗-homo.⇒ }
                  ; F⇐G = record { MF.⊗-homo.⇐ }
                  ; iso = λ X → record { MF.⊗-homo.iso X }
                  }
              ; associativity = λ {X Y Z} → MF.associativity {X} {Y} {Z}
              ; unitaryˡ = λ {X} → MF.unitaryˡ {X}
              ; unitaryʳ = λ {X} → MF.unitaryʳ {X}
              }
          }

  opaque

    unfolding Sys-MC₁

    Sys-MC-identity : MonoidalNaturalIsomorphism (Sys-MC₁ id) (idF-StrongMonoidal (Systems-MC (Valuesₘ A)))
    Sys-MC-identity {A} = record
        { U = record
            { F⇒G = record { ⇒ }
            ; F⇐G = record { ⇐ }
            ; iso = λ X → record { iso X}
            }
        ; F⇒G-isMonoidal = record
            { ε-compat = ε-compat
            ; ⊗-homo-compat = λ {X Y} → ⊗-homo-compat {X} {Y}
            }
        }
      where
        open MonoidalNaturalIsomorphism (Unlooped.NatMC.Sys.identity {A})

    Sys-MC-homomorphism
        : {g : Fin B → Fin C}
          {f : Fin A → Fin B}
        → MonoidalNaturalIsomorphism (Sys-MC₁ (g ∘ f)) (∘-StrongMonoidal (Sys-MC₁ g) (Sys-MC₁ f))
    Sys-MC-homomorphism {g} {f} = record
        { U = record
            { F⇒G = record { ⇒ }
            ; F⇐G = record { ⇐ }
            ; iso = λ X → record { iso X}
            }
        ; F⇒G-isMonoidal = record
            { ε-compat = ε-compat
            ; ⊗-homo-compat = λ {X Y} → ⊗-homo-compat {X} {Y}
            }
        }
      where
        open MonoidalNaturalIsomorphism (Unlooped.NatMC.Sys.homomorphism {f = f} {g})

    Sys-MC-resp-≈
        : {f g : Fin A → Fin B}
        → f ≗ g
        → MonoidalNaturalIsomorphism (Sys-MC₁ f) (Sys-MC₁ g)
    Sys-MC-resp-≈ f≗g = record
        { U = record
            { F⇒G = record { ⇒ }
            ; F⇐G = record { ⇐ }
            ; iso = λ X → record { iso X}
            }
        ; F⇒G-isMonoidal = record
            { ε-compat = ε-compat
            ; ⊗-homo-compat = λ {X Y} → ⊗-homo-compat {X} {Y}
            }
        }
      where
        open MonoidalNaturalIsomorphism (Unlooped.NatMC.Sys.F-resp-≈ f≗g)

  Sys : Functor Nat (StrongMonoidals (suc 0ℓ) 0ℓ 0ℓ)
  Sys .F₀ = λ n → Systems-MC (Valuesₘ n)
  Sys .F₁ = Sys-MC₁
  Sys .identity = Sys-MC-identity
  Sys .homomorphism = Sys-MC-homomorphism
  Sys .F-resp-≈ = Sys-MC-resp-≈

  module Sys = Functor Sys

module NatSMC where

  module _ (f : Fin A → Fin B) where

    F-MF : StrongMonoidalFunctor (Systems-MC (Valuesₘ A)) (Systems-MC (Valuesₘ B))
    F-MF = NatMC.Sys.₁ f
    module F-MF = StrongMonoidalFunctor F-MF

    module SMF = SymmetricMonoidalFunctor (Unlooped.NatSMC.Sys.₁ f)

    opaque

      unfolding NatMC.Sys-MC₁

      Sys-SMC₁ : SymmetricMonoidalFunctor (Systems-SMC (Valuesₘ A)) (Systems-SMC (Valuesₘ B))
      Sys-SMC₁ = record
          { F-MF
          ; isBraidedMonoidal = record
              { F-MF
              ; braiding-compat = λ {X Y} → SMF.braiding-compat {X} {Y}
              }
          }

  opaque

    unfolding Sys-SMC₁

    Sys-SMC-identity : SymmetricMonoidalNaturalIsomorphism (Sys-SMC₁ id) (idF-StrongSymmetricMonoidal (Systems-SMC (Valuesₘ A)))
    Sys-SMC-identity = record { MonoidalNaturalIsomorphism NatMC.Sys.identity }

    Sys-SMC-homomorphism
        : {g : Fin B → Fin C}
          {f : Fin A → Fin B}
        → SymmetricMonoidalNaturalIsomorphism (Sys-SMC₁ (g ∘ f)) (∘-StrongSymmetricMonoidal (Sys-SMC₁ g) (Sys-SMC₁ f))
    Sys-SMC-homomorphism = record { MonoidalNaturalIsomorphism NatMC.Sys.homomorphism }

    Sys-SMC-resp-≈
        : {f g : Fin A → Fin B}
        → f ≗ g
        → SymmetricMonoidalNaturalIsomorphism (Sys-SMC₁ f) (Sys-SMC₁ g)
    Sys-SMC-resp-≈ f≗g = record { MonoidalNaturalIsomorphism (NatMC.Sys.F-resp-≈ f≗g) }

    Sys : Functor Nat (SymMonCat {suc 0ℓ} {0ℓ} {0ℓ})
    Sys .F₀ = λ n → Systems-SMC (Valuesₘ n)
    Sys .F₁ = Sys-SMC₁
    Sys .identity = Sys-SMC-identity
    Sys .homomorphism = Sys-SMC-homomorphism
    Sys .F-resp-≈ = Sys-SMC-resp-≈

  module Sys = Functor Sys

module NatCMon where

  Sys : Functor Nat CMonoids
  Sys = InducedCMonoid ∘F SymmetricMonoidalPreorder.Free ∘F NatSMC.Sys

  module Sys = Functor Sys
