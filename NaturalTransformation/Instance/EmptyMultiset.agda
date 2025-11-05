{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module NaturalTransformation.Instance.EmptyMultiset {c ℓ : Level} where

import Function.Construct.Constant as Const

open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Functor using (Functor)
open import Categories.Category.Instance.SingletonSet using (SingletonSetoid)
open import Categories.Functor.Construction.Constant using (const)
open import Data.List using ([])
open import Functor.Instance.Multiset {c} {ℓ} using (Multiset)
open import Relation.Binary using (Setoid)

module Multiset = Functor Multiset

⊤⇒[] : NaturalTransformation (const SingletonSetoid) Multiset
⊤⇒[] = ntHelper record
    { η = λ X → Const.function SingletonSetoid (Multiset.₀ X) []
    ; commute = λ {_} {B} f → Setoid.refl (Multiset.₀ B)
    }
