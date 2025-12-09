{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module Functor.Instance.Multiset {c ℓ : Level} where

import Data.Opaque.List as L
import Data.List.Properties as ListProps
import Data.List.Relation.Binary.Pointwise as PW

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Data.List.Relation.Binary.Permutation.Setoid using (↭-setoid; ↭-reflexive-≋)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties using (map⁺)
open import Data.Opaque.Multiset using (Multisetₛ; mapₛ)
open import Data.Setoid using (∣_∣; _⇒ₛ_)
open import Function.Base using (_∘_; id)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)
open import Relation.Binary using (Setoid)

open Functor
open Setoid using (reflexive)
open Func

private
  variable
    A B C : Setoid c ℓ

-- the Multiset functor takes a carrier A to lists of A
-- and the equivalence on A to permutation equivalence on lists of A

-- Multiset on morphisms applies the same function to every element of a multiset

opaque
  unfolding mapₛ

  map-id
      : (xs : ∣ Multisetₛ A ∣)
      → (open Setoid (Multisetₛ A))
      → mapₛ (Id A) ⟨$⟩ xs ≈ xs
  map-id {A} = reflexive (Multisetₛ A) ∘ ListProps.map-id

opaque
  unfolding mapₛ

  Multiset-homo
      : (f : A ⟶ₛ B)
        (g : B ⟶ₛ C)
      → (xs : ∣ Multisetₛ A ∣)
      → (open Setoid (Multisetₛ C))
      → mapₛ (g ∙ f) ⟨$⟩ xs ≈ mapₛ g ⟨$⟩ (mapₛ f ⟨$⟩ xs)
  Multiset-homo {C = C} f g = reflexive (Multisetₛ C) ∘ ListProps.map-∘

opaque
  unfolding mapₛ

  Multiset-resp-≈
      : (f g : A ⟶ₛ B)
      → (let open Setoid (A ⇒ₛ B) in f ≈ g)
      → (let open Setoid (Multisetₛ A ⇒ₛ Multisetₛ B) in mapₛ f ≈ mapₛ g)
  Multiset-resp-≈ {A} {B} f g f≈g = ↭-reflexive-≋ B (PW.map⁺ (to f) (to g) (PW.refl f≈g))

Multiset : Functor (Setoids c ℓ) (Setoids c (c ⊔ ℓ))
Multiset .F₀ = Multisetₛ
Multiset .F₁ = mapₛ
Multiset .identity {A} {xs} = map-id {A} xs
Multiset .homomorphism {f = f} {g} {xs} = Multiset-homo f g xs
Multiset .F-resp-≈ {A} {B} {f} {g} f≈g = Multiset-resp-≈ f g f≈g

module Multiset = Functor Multiset
