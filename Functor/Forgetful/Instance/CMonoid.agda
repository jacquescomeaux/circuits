{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Level using (Level)

module Functor.Forgetful.Instance.CMonoid
    {o ℓ e : Level}
    {S : Category o ℓ e}
    {monoidal : Monoidal S}
    (symmetric : Symmetric monoidal)
  where

open import Categories.Category.Construction.Monoids monoidal using (Monoids)
open import Categories.Functor using (Functor)
open import Category.Construction.CMonoids symmetric using (CMonoids)
open import Function using (id)
open import Object.Monoid.Commutative using (CommutativeMonoid; CommutativeMonoid⇒)

private
  module S = Category S

open CommutativeMonoid
open CommutativeMonoid⇒
open Functor
open S.Equiv using (refl)

Forget : Functor CMonoids Monoids
Forget .F₀ = monoid
Forget .F₁ = monoid⇒
Forget .identity = refl
Forget .homomorphism = refl
Forget .F-resp-≈ = id

module Forget = Functor Forget
