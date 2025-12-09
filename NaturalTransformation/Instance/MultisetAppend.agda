{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module NaturalTransformation.Instance.MultisetAppend {c ℓ : Level} where

import Data.Opaque.List as L

open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Product using (_※_)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties using (++⁺)
open import Data.Opaque.Multiset using (Multisetₛ; mapₛ; ++ₛ)
open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_)
open import Functor.Instance.Multiset {c} {ℓ} using (Multiset)
open import Relation.Binary using (Setoid)

open Cartesian (Setoids-Cartesian {c} {c ⊔ ℓ}) using (products)
open BinaryProducts products using (-×-)
open Func

opaque
  unfolding ++ₛ mapₛ

  map-++ₛ
    : {A B : Setoid c ℓ}
      (f : Func A B)
      (xs ys : Setoid.Carrier (Multiset.₀ A))
    → (open Setoid (Multiset.₀ B))
    → ++ₛ ⟨$⟩ (mapₛ f ⟨$⟩ xs , mapₛ f ⟨$⟩ ys) ≈ mapₛ f ⟨$⟩ (++ₛ ⟨$⟩ (xs , ys))
  map-++ₛ {A} {B} f xs ys = sym (reflexive (map-++ (to f) xs ys))
    where
      open Setoid (Multiset.₀ B)

++ : NaturalTransformation (-×- ∘F (Multiset ※ Multiset)) Multiset
++ = ntHelper record
    { η = λ X → ++ₛ
    ; commute = λ { {A} {B} f {xs , ys} → map-++ₛ f xs ys }
    }
