{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module Functor.Instance.List {c ℓ : Level} where

import Data.List as List
import Data.List.Properties as ListProps
import Data.List.Relation.Binary.Pointwise as PW

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Data.Setoid using (∣_∣)
open import Function.Base using (_∘_; id)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Relation.Binary using (Setoid)

open Functor
open Setoid using (reflexive)
open Func

private
  variable
    A B C : Setoid c ℓ

-- the List functor takes a carrier A to lists of A
-- and the equivalence on A to pointwise equivalence on lists of A

Listₛ : Setoid c ℓ → Setoid c (c ⊔ ℓ)
Listₛ = PW.setoid

-- List on morphisms is the familiar map operation
-- which applies the same function to every element of a list

mapₛ : A ⟶ₛ B → Listₛ A ⟶ₛ Listₛ B
mapₛ f .to = List.map (to f)
mapₛ f .cong = PW.map⁺ (to f) (to f) ∘ PW.map (cong f)

map-id
    : (xs : ∣ Listₛ A ∣)
    → (open Setoid (Listₛ A))
    → List.map id xs ≈ xs
map-id {A} = reflexive (Listₛ A) ∘ ListProps.map-id

List-homo
    : (f : A ⟶ₛ B)
      (g : B ⟶ₛ C)
    → (xs : ∣ Listₛ A ∣)
    → (open Setoid (Listₛ C))
    → List.map (to g ∘ to f) xs ≈ List.map (to g) (List.map (to f) xs)
List-homo {C = C} f g = reflexive (Listₛ C) ∘ ListProps.map-∘

List : Functor (Setoids c ℓ) (Setoids c (c ⊔ ℓ))
List .F₀ = Listₛ
List .F₁ = mapₛ
List .identity {A} {xs} = map-id {A} xs
List .homomorphism {f = f} {g} {xs} = List-homo f g xs
List .F-resp-≈ {A} {B} {f} {g} f≈g = PW.map⁺ (to f) (to g) (PW.refl f≈g)
