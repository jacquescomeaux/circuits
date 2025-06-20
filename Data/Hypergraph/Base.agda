{-# OPTIONS --without-K --safe #-}

module Data.Hypergraph.Base where

open import Data.Castable using (IsCastable)
open import Data.Nat.Base using (ℕ)
open import Data.Fin using (Fin)

import Data.Vec.Base as VecBase
import Data.Vec.Relation.Binary.Equality.Cast as VecCast
import Relation.Binary.PropositionalEquality as ≡

open import Relation.Binary using (Rel; IsDecTotalOrder)
open import Data.Nat.Base using (ℕ)
open import Level using (Level; suc; _⊔_)

record HypergraphLabel {ℓ : Level} : Set (suc ℓ) where
  field
    Label : ℕ → Set ℓ
    isCastable : IsCastable Label
    _[_≈_] : (n : ℕ) → Rel (Label n) ℓ
    _[_≤_] : (n : ℕ) → Rel (Label n) ℓ
    decTotalOrder : (n : ℕ) → IsDecTotalOrder (n [_≈_]) (n [_≤_])
  open IsCastable isCastable public

module Edge (HL : HypergraphLabel) where

  open HypergraphLabel HL using (Label; cast)
  open VecBase using (Vec)

  record Edge (v : ℕ) : Set where
    field
      {arity} : ℕ
      label : Label arity
      ports : Vec (Fin v) arity

  open ≡ using (_≡_)
  open VecCast using (_≈[_]_)

  record ≈-Edge {n : ℕ} (E E′ : Edge n) : Set where
    module E = Edge E
    module E′ = Edge E′
    field
      ≡arity : E.arity ≡ E′.arity
      ≡label : cast ≡arity E.label ≡ E′.label
      ≡ports : E.ports ≈[ ≡arity ] E′.ports

module HypergraphList (HL : HypergraphLabel) where

  open import Data.List.Base using (List)
  open Edge HL using (Edge)

  record Hypergraph (v : ℕ) : Set where
    field
      edges : List (Edge v)
