{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module NaturalTransformation.Instance.EmptyMultiset {c ℓ : Level} where

import Function.Construct.Constant as Const

open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Functor using (Functor)
open import Data.Setoid.Unit {c} {c ⊔ ℓ} using (⊤ₛ)
open import Categories.Functor.Construction.Constant using (const)
open import Data.Opaque.Multiset using (Multisetₛ; []ₛ; mapₛ)
open import Functor.Instance.Multiset {c} {ℓ} using (Multiset)
open import Function.Construct.Constant using () renaming (function to Const)
open import Relation.Binary using (Setoid)
open import Data.Setoid using (_⇒ₛ_)
open import Function using (Func; _⟶ₛ_)
open import Function.Construct.Setoid using (_∙_)

opaque
  unfolding mapₛ
  map-[]ₛ
      : {A B : Setoid c ℓ}
      → (f : A ⟶ₛ B)
      → (open Setoid (⊤ₛ ⇒ₛ Multisetₛ B))
      → []ₛ ≈ mapₛ f ∙ []ₛ
  map-[]ₛ {B = B} f = Setoid.refl (Multisetₛ B)

⊤⇒[] : NaturalTransformation (const ⊤ₛ) Multiset
⊤⇒[] = ntHelper record
    { η = λ X → []ₛ {Aₛ = X}
    ; commute = map-[]ₛ
    }
