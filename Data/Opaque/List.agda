{-# OPTIONS --without-K --safe #-}

module Data.Opaque.List where

import Data.List as L
import Function.Construct.Constant as Const

open import Level using (Level; _⊔_)
open import Data.List.Relation.Binary.Pointwise as PW using (++⁺; map⁺)
open import Data.Product using (uncurry′)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Unit.Polymorphic using (⊤)
open import Function using (_⟶ₛ_; Func)
open import Relation.Binary using (Setoid)

open Func

private

  variable
    a c ℓ : Level
    A B : Set a
    Aₛ Bₛ : Setoid c ℓ

  ⊤ₛ : Setoid c ℓ
  ⊤ₛ = record { Carrier = ⊤ ; _≈_ = λ _ _ → ⊤ }

opaque

  List : Set a → Set a
  List = L.List

  [] : List A
  [] = L.[]

  _∷_ : A → List A → List A
  _∷_ = L._∷_

  map : (A → B) → List A → List B
  map = L.map

  _++_ : List A → List A → List A
  _++_ = L._++_

  Listₛ : Setoid c ℓ → Setoid c (c ⊔ ℓ)
  Listₛ = PW.setoid

  []ₛ : ⊤ₛ {c} {c ⊔ ℓ} ⟶ₛ Listₛ {c} {ℓ} Aₛ
  []ₛ = Const.function ⊤ₛ (Listₛ _) []

  ∷ₛ : Aₛ ×ₛ Listₛ Aₛ ⟶ₛ Listₛ Aₛ
  ∷ₛ .to = uncurry′ _∷_
  ∷ₛ .cong = uncurry′ PW._∷_

  mapₛ : (Aₛ ⟶ₛ Bₛ) → Listₛ Aₛ ⟶ₛ Listₛ Bₛ
  mapₛ f .to = map (to f)
  mapₛ f .cong xs≈ys = map⁺ (to f) (to f) (PW.map (cong f) xs≈ys)

  ++ₛ : Listₛ Aₛ ×ₛ Listₛ Aₛ ⟶ₛ Listₛ Aₛ
  ++ₛ .to = uncurry′ _++_
  ++ₛ .cong = uncurry′ ++⁺
