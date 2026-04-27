{-# OPTIONS --without-K --safe #-}

module Lattice.Bundle.BoundedDistributive where

open import Algebra using (Op₂)
open import Lattice.Structure.IsBoundedDistributive using (IsBoundedDistributiveLattice)
open import Level using (suc; _⊔_)
open import Relation.Binary using (Rel)
open import Relation.Binary.Lattice using (BoundedLattice; DistributiveLattice)

record BoundedDistributiveLattice c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  4 _≈_ _≤_
  infixr 6 _∨_
  infixr 7 _∧_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ₁  -- The underlying equality.
    _≤_     : Rel Carrier ℓ₂  -- The partial order.
    _∨_     : Op₂ Carrier     -- The join operation.
    _∧_     : Op₂ Carrier     -- The meet operation.
    ⊤       : Carrier         -- The maximum
    ⊥       : Carrier         -- The minimum
    isBoundedDistributiveLattice : IsBoundedDistributiveLattice _≈_ _≤_ _∨_ _∧_ ⊤ ⊥

  open IsBoundedDistributiveLattice isBoundedDistributiveLattice public

  boundedLattice : BoundedLattice c ℓ₁ ℓ₂
  boundedLattice = record
      { isBoundedLattice = isBoundedLattice
      }

  distributiveLattice : DistributiveLattice c ℓ₁ ℓ₂
  distributiveLattice = record
      { isDistributiveLattice = isDistributiveLattice
      }

  open BoundedLattice boundedLattice public
    using (lattice; joinSemilattice; meetSemilattice; poset; preorder; setoid)
