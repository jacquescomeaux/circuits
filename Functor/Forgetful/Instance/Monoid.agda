{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Level using (Level)

module Functor.Forgetful.Instance.Monoid {o ℓ e : Level} {S : Category o ℓ e} (monoidal : Monoidal S) where

open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Functor using (Functor)
open import Categories.Object.Monoid using (Monoid; Monoid⇒)
open import Function using (id)

private
  module S = Category S

open Monoid
open Monoid⇒
open S.Equiv using (refl)
open Functor

Forget : Functor (Monoids monoidal) S
Forget .F₀ = Carrier
Forget .F₁ = arr
Forget .identity = refl
Forget .homomorphism = refl
Forget .F-resp-≈ = id

module Forget = Functor Forget
