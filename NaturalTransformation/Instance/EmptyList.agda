{-# OPTIONS --without-K --safe #-}

module NaturalTransformation.Instance.EmptyList where

import Function.Construct.Constant as Const

open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Functor using (Functor)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid)
open import Categories.Functor.Construction.Constant using (const)
open import Data.List.Relation.Binary.Pointwise using (refl)
open import Data.List using ([])
open import Level using (0ℓ)
open import Functor.Instance.List {0ℓ} {0ℓ} using (List)
open import Relation.Binary using (Setoid)

module List = Functor List

⊤⇒[] : NaturalTransformation (const SingletonSetoid) List
⊤⇒[] = ntHelper record
    { η = λ X → Const.function SingletonSetoid (List.₀ X) []
    ; commute = λ {_} {B} f → let module B = Setoid B in refl B.refl
    }
