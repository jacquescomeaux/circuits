{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module Functor.Free.Instance.Monoid {c ℓ : Level} where

import Categories.Object.Monoid as MonoidObject

open import Categories.Category.Construction.Monoids using (Monoids)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)
open import Category.Instance.Setoids.SymmetricMonoidal {c} {c ⊔ ℓ} using (Setoids-×)
open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ)
open import Data.Opaque.List using ([]ₛ; Listₛ; ++ₛ; mapₛ)
open import Data.Product using (_,_)
open import Data.Setoid using (∣_∣)
open import Function using (_⟶ₛ_; _⟨$⟩_)
open import Functor.Instance.List {c} {ℓ} using (List)
open import NaturalTransformation.Instance.EmptyList {c} {ℓ} using (⊤⇒[])
open import NaturalTransformation.Instance.ListAppend {c} {ℓ} using (++)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

module Setoids-× = SymmetricMonoidalCategory Setoids-×
module ++ = NaturalTransformation ++
module ⊤⇒[] = NaturalTransformation ⊤⇒[]

open Functor
open MonoidObject Setoids-×.monoidal using (Monoid; IsMonoid; Monoid⇒)
open IsMonoid

-- the functor sending a setoid A to the monoid List A

module _ (X : Setoid c ℓ) where

  open Setoid (List.₀ X)

  opaque

    unfolding []ₛ

    ++ₛ-assoc
        : (x y z : ∣ Listₛ X ∣)
        → ++ₛ ⟨$⟩ (++ₛ ⟨$⟩ (x , y) , z)
        ≈ ++ₛ ⟨$⟩ (x , ++ₛ ⟨$⟩ (y , z))
    ++ₛ-assoc x y z = reflexive (++-assoc x y z)

    ++ₛ-identityˡ
        : (x : ∣ Listₛ X ∣)
        → x ≈ ++ₛ ⟨$⟩ ([]ₛ ⟨$⟩ _ , x)
    ++ₛ-identityˡ x = reflexive (++-identityˡ x)

    ++ₛ-identityʳ
        : (x : ∣ Listₛ X ∣)
        → x ≈ ++ₛ ⟨$⟩ (x , []ₛ ⟨$⟩ _)
    ++ₛ-identityʳ x = sym (reflexive (++-identityʳ x))

  ListMonoid : IsMonoid (List.₀ X)
  ListMonoid .μ = ++.η X
  ListMonoid .η = ⊤⇒[].η X
  ListMonoid .assoc {(x , y) , z} = ++ₛ-assoc x y z
  ListMonoid .identityˡ {bro , x} = ++ₛ-identityˡ x
  ListMonoid .identityʳ {x , _} = ++ₛ-identityʳ x

Listₘ : Setoid c ℓ → Monoid
Listₘ X = record { isMonoid = ListMonoid X }

mapₘ
    : {Aₛ Bₛ : Setoid c ℓ}
      (f : Aₛ ⟶ₛ Bₛ)
    → Monoid⇒ (Listₘ Aₛ) (Listₘ Bₛ)
mapₘ f = record
    { arr = List.₁ f
    ; preserves-μ = λ {x,y} → ++.sym-commute f {x,y}
    ; preserves-η = ⊤⇒[].sym-commute f
    }

Free : Functor (Setoids c ℓ) (Monoids Setoids-×.monoidal)
Free .F₀ = Listₘ
Free .F₁ = mapₘ
Free .identity {X} = List.identity {X}
Free .homomorphism {X} {Y} {Z} {f} {g} = List.homomorphism {X} {Y} {Z} {f} {g}
Free .F-resp-≈ {A} {B} {f} {g} = List.F-resp-≈ {A} {B} {f} {g}
