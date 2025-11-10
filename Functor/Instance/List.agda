{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module Functor.Instance.List {c ℓ : Level} where

import Data.List.Properties as ListProps
import Data.List.Relation.Binary.Pointwise as PW

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Data.Setoid using (∣_∣; _⇒ₛ_)
open import Function.Base using (_∘_; id)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Relation.Binary using (Setoid)

open Functor
open Setoid using (reflexive)
open Func

open import Data.Opaque.List as List hiding (List)

private
  variable
    A B C : Setoid c ℓ

open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)

opaque

  unfolding List.List

  map-id
      : (xs : ∣ Listₛ A ∣)
      → (open Setoid (Listₛ A))
      → mapₛ (Id _) ⟨$⟩ xs ≈ xs
  map-id {A} = reflexive (Listₛ A) ∘ ListProps.map-id

  List-homo
      : (f : A ⟶ₛ B)
        (g : B ⟶ₛ C)
      → (xs : ∣ Listₛ A ∣)
      → (open Setoid (Listₛ C))
      → mapₛ (g ∙ f) ⟨$⟩ xs ≈ mapₛ g ⟨$⟩ (mapₛ f ⟨$⟩ xs)
  List-homo {C = C} f g = reflexive (Listₛ C) ∘ ListProps.map-∘

  List-resp-≈
      : (f g : A ⟶ₛ B)
      → (let open Setoid (A ⇒ₛ B) in f ≈ g)
      → (let open Setoid (Listₛ A ⇒ₛ Listₛ B) in mapₛ f ≈ mapₛ g)
  List-resp-≈ f g f≈g = PW.map⁺ (to f) (to g) (PW.refl f≈g)

-- the List functor takes a carrier A to lists of A
-- and the equivalence on A to pointwise equivalence on lists of A

-- List on morphisms is the familiar map operation
-- which applies the same function to every element of a list

List : Functor (Setoids c ℓ) (Setoids c (c ⊔ ℓ))
List .F₀ = List.Listₛ
List .F₁ = List.mapₛ
List .identity {_} {xs} = map-id xs
List .homomorphism {f = f} {g} {xs} = List-homo f g xs
List .F-resp-≈ {f = f} {g} f≈g = List-resp-≈ f g f≈g
