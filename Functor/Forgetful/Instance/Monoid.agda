{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Monoidal using (MonoidalCategory)
open import Level using (Level)

module Functor.Forgetful.Instance.Monoid {o ℓ e : Level} (S : MonoidalCategory o ℓ e) where

open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Functor using (Functor)
open import Categories.Object.Monoid using (Monoid; Monoid⇒)
open import Function using (id)

module S = MonoidalCategory S

open Monoid
open Monoid⇒
open S.Equiv using (refl)
open Functor

Forget : Functor (Monoids S.monoidal) S.U
Forget .F₀ = Carrier
Forget .F₁ = arr
Forget .identity = refl
Forget .homomorphism = refl
Forget .F-resp-≈ = id

module Forget = Functor Forget
