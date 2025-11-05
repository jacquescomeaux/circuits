{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)

module NaturalTransformation.Instance.MultisetAppend {c ℓ : Level} where

open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Category.Product using (_※_)
open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Functor using (Functor; _∘F_)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Binary.Permutation.Setoid.Properties using (++⁺)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Product using (_,_)
open import Functor.Instance.Multiset {c} {ℓ} using (Multiset)
open import Function using (Func; _⟶ₛ_)
open import Relation.Binary using (Setoid)

module Multiset = Functor Multiset

open Cartesian (Setoids-Cartesian {c} {c ⊔ ℓ}) using (products)
open BinaryProducts products using (-×-)
open Func

++ₛ : {X : Setoid c ℓ} → Multiset.₀ X ×ₛ Multiset.₀ X ⟶ₛ Multiset.₀ X
++ₛ .to (xs , ys) = xs ++ ys
++ₛ {A} .cong (≈xs , ≈ys) = ++⁺ A ≈xs ≈ys

map-++ₛ
  : {A B : Setoid c ℓ}
    (f : Func A B)
    (xs ys : List (Setoid.Carrier A))
  → (open Setoid (Multiset.₀ B))
  → map (to f) xs ++ map (to f) ys ≈ map (to f) (xs ++ ys)
map-++ₛ {_} {B} f xs ys =  sym (reflexive (map-++ (to f) xs ys))
  where
    open Setoid (Multiset.₀ B)

++ : NaturalTransformation (-×- ∘F (Multiset ※ Multiset)) Multiset
++ = ntHelper record
    { η = λ X → ++ₛ {X}
    ; commute = λ { {A} {B} f {xs , ys} → map-++ₛ f xs ys }
    }
