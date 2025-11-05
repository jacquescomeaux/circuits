{-# OPTIONS --without-K --safe #-}
module Data.Hypergraph.Label where

open import Data.Castable using (IsCastable)
open import Data.Nat.Base using (ℕ)
open import Data.String using (String)
open import Level using (Level; 0ℓ)
open import Relation.Binary using (Rel; IsDecTotalOrder)
open import Relation.Binary.Bundles using (DecTotalOrder; StrictTotalOrder)
open import Relation.Binary.Properties.DecTotalOrder using (<-strictTotalOrder; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_)

record HypergraphLabel : Set₁ where

  field
    Label : ℕ → Set
    showLabel : (n : ℕ) → Label n → String
    isCastable : IsCastable Label
    _[_≤_] : (n : ℕ) → Rel (Label n) 0ℓ
    isDecTotalOrder : (n : ℕ) → IsDecTotalOrder _≡_ (n [_≤_])

  decTotalOrder : (n : ℕ) → DecTotalOrder 0ℓ 0ℓ 0ℓ
  decTotalOrder n = record
      { Carrier = Label n
      ; _≈_ = _≡_
      ; _≤_ = n [_≤_]
      ; isDecTotalOrder = isDecTotalOrder n
      }

  _[_<_] : (n : ℕ) → Rel (Label n) 0ℓ
  _[_<_] n =  _<_ (decTotalOrder n)

  strictTotalOrder : (n : ℕ) → StrictTotalOrder 0ℓ 0ℓ 0ℓ
  strictTotalOrder n = <-strictTotalOrder (decTotalOrder n)

  open IsCastable isCastable public
