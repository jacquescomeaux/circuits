{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Level using (Level; _⊔_)

module Object.Monoid.Commutative {o ℓ e : Level} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞} (sym : Symmetric M) where

open import Categories.Object.Monoid M using (IsMonoid; Monoid; Monoid⇒)

-- a commutative monoid object in a symmetric monoidal category

open Category 𝒞
open Symmetric sym using (module braiding; _⊗₁_)

record IsCommutativeMonoid (M : Obj) : Set (ℓ ⊔ e) where

  field
    isMonoid : IsMonoid M

  open IsMonoid isMonoid public

  field
    commutative : μ ≈ μ ∘ braiding.⇒.η _

record CommutativeMonoid : Set (o ⊔ ℓ ⊔ e) where

  field
    Carrier : Obj
    isCommutativeMonoid : IsCommutativeMonoid Carrier

  open IsCommutativeMonoid isCommutativeMonoid public

  monoid : Monoid
  monoid = record { isMonoid = isMonoid }

open CommutativeMonoid

record CommutativeMonoid⇒ (M M′ : CommutativeMonoid) : Set (ℓ ⊔ e) where

  module M = CommutativeMonoid M
  module M′ = CommutativeMonoid M′

  field
    monoid⇒ : Monoid⇒ M.monoid M′.monoid

  open Monoid⇒ monoid⇒ public
