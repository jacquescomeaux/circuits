{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Data.Opaque.Multiset where

import Data.List as L

open import Data.List.Relation.Binary.Permutation.Setoid as ↭ using (↭-setoid; prep)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties using (map⁺; ++⁺; ++-comm)
open import Data.Product using (_,_)
open import Data.Product using (uncurry′)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid.Unit using (⊤ₛ)
open import Function using (_⟶ₛ_; Func; _⟨$⟩_)
open import Function.Construct.Constant using () renaming (function to Const)
open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid)

open Func

private

  variable
    a c ℓ : Level
    A B : Set a
    Aₛ Bₛ : Setoid c ℓ

opaque

  Multiset : Set a → Set a
  Multiset = L.List

  [] : Multiset A
  [] = L.[]

  _∷_ : A → Multiset A → Multiset A
  _∷_ = L._∷_

  map : (A → B) → Multiset A → Multiset B
  map = L.map

  _++_ : Multiset A → Multiset A → Multiset A
  _++_ = L._++_

  Multisetₛ : Setoid c ℓ → Setoid c (c ⊔ ℓ)
  Multisetₛ = ↭-setoid

  []ₛ : ⊤ₛ {c} {c ⊔ ℓ} ⟶ₛ Multisetₛ {c} {ℓ} Aₛ
  []ₛ {Aₛ} = Const ⊤ₛ (Multisetₛ Aₛ) []

  ∷ₛ : Aₛ ×ₛ Multisetₛ Aₛ ⟶ₛ Multisetₛ Aₛ
  ∷ₛ .to = uncurry′ _∷_
  ∷ₛ .cong = uncurry′ prep

  mapₛ : (Aₛ ⟶ₛ Bₛ) → Multisetₛ Aₛ ⟶ₛ Multisetₛ Bₛ
  mapₛ f .to = map (to f)
  mapₛ {Aₛ} {Bₛ} f .cong xs≈ys = map⁺ Aₛ Bₛ (cong f) xs≈ys

  ++ₛ : Multisetₛ Aₛ ×ₛ Multisetₛ Aₛ ⟶ₛ Multisetₛ Aₛ
  ++ₛ .to = uncurry′ _++_
  ++ₛ {Aₛ} .cong = uncurry′ (++⁺ Aₛ)

  ++ₛ-comm
      : (open Setoid (Multisetₛ Aₛ))
      → (xs ys : Carrier)
      → ++ₛ ⟨$⟩ (xs , ys) ≈ ++ₛ ⟨$⟩ (ys , xs)
  ++ₛ-comm {Aₛ} xs ys = ++-comm Aₛ xs ys
