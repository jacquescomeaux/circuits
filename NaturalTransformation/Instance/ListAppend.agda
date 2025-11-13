{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module NaturalTransformation.Instance.ListAppend {c ℓ : Level} where

open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Category.Product using (_※_)
open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Functor using (Functor; _∘F_)
open import Data.Opaque.List as L using (mapₛ; ++ₛ)
open import Data.List.Properties using (map-++)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Product using (_,_)
open import Functor.Instance.List {c} {ℓ} using (List)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_)
open import Relation.Binary using (Setoid)

open Cartesian (Setoids-Cartesian {c} {c ⊔ ℓ}) using (products)
open BinaryProducts products using (-×-)
open Func

opaque

  unfolding ++ₛ

  map-++ₛ
    : {A B : Setoid c ℓ}
      (f : Func A B)
      (xs ys : Setoid.Carrier (L.Listₛ A))
      (open Setoid (L.Listₛ B))
    → ++ₛ ⟨$⟩ (mapₛ f ⟨$⟩ xs , mapₛ f ⟨$⟩ ys) ≈ mapₛ f ⟨$⟩ (++ₛ ⟨$⟩ (xs , ys))
  map-++ₛ {_} {B} f xs ys = sym (reflexive (map-++ (to f) xs ys))
    where
      open Setoid (List.₀ B)

++ : NaturalTransformation (-×- ∘F (List ※ List)) List
++ = ntHelper record
    { η = λ X → ++ₛ {c} {ℓ} {X}
    ; commute = λ { {A} {B} f {xs , ys} → map-++ₛ f xs ys }
    }
