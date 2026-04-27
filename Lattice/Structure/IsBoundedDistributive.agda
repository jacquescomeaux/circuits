{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)

module Lattice.Structure.IsBoundedDistributive
   {a ℓ₁ ℓ₂} {A : Set a}
   (_≈_ : Rel A ℓ₁) -- The underlying equality.
   (_≤_ : Rel A ℓ₂) -- The partial order.
  where

open import Algebra using (Op₂)
open import Algebra.Definitions using (_DistributesOverˡ_)
open import Level using (suc; _⊔_)
open import Relation.Binary.Definitions using (Minimum; Maximum)
open import Relation.Binary.Lattice.Structures _≈_ _≤_ using (IsLattice; IsDistributiveLattice; IsBoundedLattice)

record IsBoundedDistributiveLattice
    (_∨_ : Op₂ A)    -- The join operation.
    (_∧_ : Op₂ A)    -- The meet operation.
    (⊤   : A)        -- The maximum.
    (⊥   : A)        -- The minimum.
  : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where

  field
    isLattice     : IsLattice _∨_ _∧_
    maximum       : Maximum _≤_ ⊤
    minimum       : Minimum _≤_ ⊥
    ∧-distribˡ-∨  : _DistributesOverˡ_ _≈_ _∧_ _∨_

  open IsLattice isLattice public

  isBoundedLattice : IsBoundedLattice _∨_ _∧_ ⊤ ⊥
  isBoundedLattice = record
      { isLattice = isLattice
      ; maximum = maximum
      ; minimum = minimum
      }

  isDistributiveLattice : IsDistributiveLattice _∨_ _∧_
  isDistributiveLattice = record
      { isLattice = isLattice
      ; ∧-distribˡ-∨ = ∧-distribˡ-∨
      }
