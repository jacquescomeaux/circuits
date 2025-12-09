{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module NaturalTransformation.Instance.EmptyList {c ℓ : Level} where

open import Categories.Functor using (Functor)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Data.Opaque.List using (Listₛ; []ₛ; mapₛ)
open import Data.Setoid using (_⇒ₛ_)
open import Data.Setoid.Unit using (⊤ₛ)
open import Function using (_⟶ₛ_)
open import Function.Construct.Constant using () renaming (function to Const)
open import Function.Construct.Setoid using (_∙_)
open import Functor.Instance.List {c} {ℓ} using (List)
open import Relation.Binary using (Setoid)

opaque

  unfolding []ₛ

  map-[]ₛ : {A B : Setoid c ℓ}
      → (f : A ⟶ₛ B)
      → (open Setoid (⊤ₛ ⇒ₛ Listₛ B))
      → []ₛ ≈ mapₛ f ∙ []ₛ
  map-[]ₛ {_} {B} f = refl
    where
      open Setoid (List.₀ B)

⊤⇒[] : NaturalTransformation (const ⊤ₛ) List
⊤⇒[] = ntHelper record
    { η = λ X → []ₛ
    ; commute = map-[]ₛ
    }
