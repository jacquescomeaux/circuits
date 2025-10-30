{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module Functor.Instance.FreeMonoid {c ℓ : Level} where

import Categories.Object.Monoid as MonoidObject

open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Category.Instance.Setoids.SymmetricMonoidal {c} {c ⊔ ℓ} using (Setoids-×)
open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ)
open import Data.Product using (_,_)
open import Function using (_⟶ₛ_)
open import Functor.Instance.List {c} {ℓ} using (List)
open import NaturalTransformation.Instance.EmptyList {c} {ℓ} using (⊤⇒[])
open import NaturalTransformation.Instance.ListAppend {c} {ℓ} using (++)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

module List = Functor List
module Setoids-× = SymmetricMonoidalCategory Setoids-×
module ++ = NaturalTransformation ++
module ⊤⇒[] = NaturalTransformation ⊤⇒[]

open Functor
open MonoidObject Setoids-×.monoidal using (Monoid; IsMonoid; Monoid⇒)
open IsMonoid

module _ (X : Setoid c ℓ) where

  private
    module X = Setoid X
    module ListX = Setoid (List.₀ X)

  ListMonoid : IsMonoid (List.₀ X)
  ListMonoid .μ = ++.η X
  ListMonoid .η = ⊤⇒[].η X
  ListMonoid .assoc {(x , y) , z} = ListX.reflexive (++-assoc x y z)
  ListMonoid .identityˡ {_ , x} = ListX.reflexive (++-identityˡ x)
  ListMonoid .identityʳ {x , _} = ListX.reflexive (≡.sym (++-identityʳ x))

FreeMonoid₀ : (X : Setoid c ℓ) → Monoid
FreeMonoid₀ X = record { isMonoid = ListMonoid X }

FreeMonoid₁
    : {A B : Setoid c ℓ}
      (f : A ⟶ₛ B)
    → Monoid⇒ (FreeMonoid₀ A) (FreeMonoid₀ B)
FreeMonoid₁ f = record
    { arr = List.₁ f
    ; preserves-μ = λ {x,y} → ++.sym-commute f {x,y}
    ; preserves-η = ⊤⇒[].commute f
    }

FreeMonoid : Functor (Setoids c ℓ) (Monoids Setoids-×.monoidal)
FreeMonoid .F₀ = FreeMonoid₀
FreeMonoid .F₁ = FreeMonoid₁
FreeMonoid .identity {X} = List.identity {X}
FreeMonoid .homomorphism {X} {Y} {Z} {f} {g} = List.homomorphism {X} {Y} {Z} {f} {g}
FreeMonoid .F-resp-≈ {A} {B} {f} {g} = List.F-resp-≈ {A} {B} {f} {g}
