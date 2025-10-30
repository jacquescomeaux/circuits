{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module NaturalTransformation.Instance.EmptyList {c ℓ : Level} where

import Function.Construct.Constant as Const

open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Functor using (Functor)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid)
open import Categories.Functor.Construction.Constant using (const)
open import Data.List using ([])
open import Functor.Instance.List {c} {ℓ} using (List)
open import Relation.Binary using (Setoid)

module List = Functor List

⊤⇒[] : NaturalTransformation (const SingletonSetoid) List
⊤⇒[] = ntHelper record
    { η = λ X → Const.function SingletonSetoid (List.₀ X) []
    ; commute = λ {_} {B} f → Setoid.refl (List.₀ B)
    }
