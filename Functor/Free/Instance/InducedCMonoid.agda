{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Functor.Free.Instance.InducedCMonoid {c ℓ : Level} where

-- The induced commutative monoid of a symmetric monoidal preorder

open import Category.Instance.Setoids.SymmetricMonoidal {c} {ℓ} using (Setoids-×; ×-symmetric′)

open import Categories.Functor using (Functor)
open import Categories.Object.Monoid Setoids-×.monoidal using (Monoid)
open import Category.Construction.CMonoids Setoids-×.symmetric using (CMonoids)
open import Category.Instance.Preorder.Primitive.Monoidals.Symmetric.Strong using (SymMonPre)
open import Data.Product using (_,_)
open import Data.Setoid using (∣_∣)
open import Function.Construct.Setoid using (_∙_)
open import Functor.Free.Instance.InducedMonoid using (μ) renaming (module InducedMonoid to IM)
open import Functor.Free.Instance.InducedSetoid using () renaming (module InducedSetoid to IS)
open import Object.Monoid.Commutative Setoids-×.symmetric using (CommutativeMonoid; CommutativeMonoid⇒)
open import Preorder.Primitive using (module Isomorphism)
open import Preorder.Primitive.Monoidal using (SymmetricMonoidalPreorder)
open import Preorder.Primitive.MonotoneMap.Monoidal.Strong using (SymmetricMonoidalMonotone)

open Setoids-× using (_⊗₀_; _⊗₁_; _≈_; module braiding)

module _ (P : SymmetricMonoidalPreorder c ℓ) where

  open SymmetricMonoidalPreorder P

  private module M = Monoid (IM.₀ monoidalPreorder)

  opaque
    unfolding μ
    commutative : M.μ ≈ M.μ ∙ braiding.⇒.η (IS.₀ U , IS.₀ U)
    commutative {x , y} = record { from = symmetry x y ; to = symmetry y x }

  ≅-cmonoid : CommutativeMonoid
  ≅-cmonoid = record
      { M
      ; isCommutativeMonoid = record
          { M
          ; commutative = commutative
          }
      }

cmonoid⇒
    : {A B : SymmetricMonoidalPreorder c ℓ}
    → SymmetricMonoidalMonotone A B
    → CommutativeMonoid⇒ (≅-cmonoid A) (≅-cmonoid B)
cmonoid⇒ f = let open SymmetricMonoidalMonotone f in record
    { monoid⇒ = IM.₁ monoidalMonotone
    }

InducedCMonoid : Functor (SymMonPre c ℓ) CMonoids
InducedCMonoid = record
    { F₀ = ≅-cmonoid
    ; F₁ = cmonoid⇒
    ; identity = λ {A} {x} → ≅.refl (U A)
    ; homomorphism = λ {Z = Z} → ≅.refl (U Z)
    ; F-resp-≈ = λ f≃g {x} → f≃g x
    }
  where
    open SymmetricMonoidalPreorder using (U)
    open Isomorphism using (module ≅)

module InducedCMonoid = Functor InducedCMonoid
