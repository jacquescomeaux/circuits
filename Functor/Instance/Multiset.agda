{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module Functor.Instance.Multiset {c ℓ : Level} where

import Data.List as List
import Data.List.Properties as ListProps
import Data.List.Relation.Binary.Pointwise as PW

open import Data.List.Relation.Binary.Permutation.Setoid using (↭-setoid; ↭-reflexive-≋)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties using (map⁺)

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

-- the Multiset functor takes a carrier A to lists of A
-- and the equivalence on A to permutation equivalence on lists of A

Multisetₛ : Setoid c ℓ → Setoid c (c ⊔ ℓ)
Multisetₛ x = ↭-setoid x

-- Multiset on morphisms applies the same function to every element of a multiset

mapₛ : A ⟶ₛ B → Multisetₛ A ⟶ₛ Multisetₛ B
mapₛ f .to = List.map (to f)
mapₛ {A} {B} f .cong = map⁺ A B (cong f)

map-id
    : (xs : ∣ Multisetₛ A ∣)
    → (open Setoid (Multisetₛ A))
    → List.map id xs ≈ xs
map-id {A} = reflexive (Multisetₛ A) ∘ ListProps.map-id

Multiset-homo
    : (f : A ⟶ₛ B)
      (g : B ⟶ₛ C)
    → (xs : ∣ Multisetₛ A ∣)
    → (open Setoid (Multisetₛ C))
    → List.map (to g ∘ to f) xs ≈ List.map (to g) (List.map (to f) xs)
Multiset-homo {C = C} f g = reflexive (Multisetₛ C) ∘ ListProps.map-∘

Multiset : Functor (Setoids c ℓ) (Setoids c (c ⊔ ℓ))
Multiset .F₀ = Multisetₛ
Multiset .F₁ = mapₛ
Multiset .identity {A} {xs} = map-id {A} xs
Multiset .homomorphism {f = f} {g} {xs} = Multiset-homo f g xs
Multiset .F-resp-≈ {A} {B} {f} {g} f≈g = ↭-reflexive-≋ B (PW.map⁺ (to f) (to g) (PW.refl f≈g))
