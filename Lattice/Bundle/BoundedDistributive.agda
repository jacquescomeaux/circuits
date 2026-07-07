{-# OPTIONS --without-K --safe #-}

module Lattice.Bundle.BoundedDistributive where

import Relation.Binary.Lattice.Properties.BoundedJoinSemilattice as BJS
import Relation.Binary.Lattice.Properties.BoundedLattice as BL
import Relation.Binary.Lattice.Properties.BoundedMeetSemilattice as BMS
import Relation.Binary.Lattice.Properties.DistributiveLattice as DL
import Relation.Binary.Lattice.Properties.JoinSemilattice as JS
import Relation.Binary.Lattice.Properties.MeetSemilattice as MS

open import Algebra using (Op₂)
open import Algebra.Bundles using (Semiring)
open import Data.Product using (_,_)
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
    using (lattice; boundedJoinSemilattice; boundedMeetSemilattice; joinSemilattice; meetSemilattice; poset; preorder; setoid)

  semiring : Semiring c ℓ₁
  semiring = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _+_ = _∨_
      ; _*_ = _∧_
      ; 0# = ⊥
      ; 1# = ⊤
      ; isSemiring = record
          { isSemiringWithoutAnnihilatingZero = record
              { +-isCommutativeMonoid = record
                  { isMonoid = record
                      { isSemigroup = record
                          { isMagma = record
                              { isEquivalence = isEquivalence
                              ; ∙-cong = ∨-cong
                              }
                          ; assoc = ∨-assoc
                          }
                      ; identity = ∨-identity
                      }
                  ; comm = ∨-comm
                  }
              ; *-cong = ∧-cong
              ; *-assoc = ∧-assoc
              ; *-identity = ∧-identity
              ; distrib = ∧-distribˡ-∨ , ∧-distribʳ-∨
              }
          ; zero = ∧-zero
          }
      }
    where
      open BJS boundedJoinSemilattice using () renaming (identity to ∨-identity)
      open BL boundedLattice using (∧-zero)
      open BMS boundedMeetSemilattice using () renaming (identity to ∧-identity)
      open DL distributiveLattice using (∧-distribʳ-∨)
      open JS joinSemilattice using (∨-comm; ∨-cong; ∨-assoc)
      open MS meetSemilattice using (∧-comm; ∧-cong; ∧-assoc)
