{-# OPTIONS --without-K --safe #-}

module NaturalTransformation.Instance.ListAppend where

open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Category.Product using (_※_)
open import Categories.Category.BinaryProducts using (module BinaryProducts)
open import Categories.Category.Monoidal.Instance.Setoids using (Setoids-Cartesian)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Functor using (Functor; _∘F_)
open import Data.List using (_++_)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; ++⁺; refl; reflexive; symmetric; ≡⇒Pointwise-≡)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Product using (_,_)
open import Functor.Instance.List using (List)
open import Function using (Func; _⟶ₛ_)
open import Level using (0ℓ)
open import Relation.Binary using (Setoid)

module List = Functor (List {0ℓ} {0ℓ})

open Cartesian (Setoids-Cartesian {0ℓ} {0ℓ}) using (products)
open BinaryProducts products using (-×-)
open Func

++ₛ : {X : Setoid 0ℓ 0ℓ} → List.₀ X ×ₛ List.₀ X ⟶ₛ List.₀ X
++ₛ .to (xs , ys) = xs ++ ys
++ₛ .cong (≈xs , ≈ys)  = ++⁺ ≈xs ≈ys

map-++ₛ
  : {A B : Setoid 0ℓ 0ℓ}
    (f : Func A B)
    (xs ys : Data.List.List (Setoid.Carrier A))
  → (open Setoid B)
  → Pointwise _≈_ (Data.List.map (to f) xs ++ Data.List.map (to f) ys) (Data.List.map (to f) (xs ++ ys))
map-++ₛ {_} {B} f xs ys = symmetric B.sym (reflexive B.reflexive (≡⇒Pointwise-≡ (map-++ (to f) xs ys)))
    where
      module B = Setoid B

++ : NaturalTransformation (-×- ∘F (List ※ List)) List
++ = ntHelper record
    { η = λ X → ++ₛ {X}
    ; commute = λ { {A} {B} f {xs , ys} → map-++ₛ f xs ys }
    }
