{-# OPTIONS --without-K --safe #-}

module Data.Boolean.BoundedDistributiveLattice where

import Algebra.Lattice.Bundles as Algebra
import Relation.Binary.Lattice.Bundles as Relation
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Algebra.Lattice.Properties.BooleanAlgebra as BA

open import Algebra.Bundles using (Semiring)
open import Algebra.Lattice.Properties.Lattice using (∧-semilattice; ∨-semilattice)
open import Algebra.Lattice.Properties.Lattice using (∨-∧-isOrderTheoreticLattice)
open import Data.Bool using (Bool; not)
open import Data.Bool.Properties using (∨-∧-booleanAlgebra)
open import Data.Product using (_,_)
open import Lattice.Bundle.BoundedDistributive using (BoundedDistributiveLattice)
open import Lattice.Properties.BooleanAlgebra using (boundedDistributiveLattice)
open import Level using (0ℓ)
open import Relation.Binary.Lattice.Properties.Lattice using (isAlgLattice)

open Algebra.BooleanAlgebra ∨-∧-booleanAlgebra
open BA ∨-∧-booleanAlgebra using (∧-identityˡ; ∧-identityʳ; ∧-zeroˡ; ∨-identityˡ)

booleanAlgebra : Relation.BooleanAlgebra 0ℓ 0ℓ 0ℓ
booleanAlgebra = record
    { Carrier = Carrier
    ; _≈_ = _≈_
    ; _≤_ = λ x y → x ≈ x ∧ y
    ; _∨_ = _∨_
    ; _∧_ = _∧_
    ; ¬_ = ¬_
    ; ⊤ = ⊤
    ; ⊥ = ⊥
    ; isBooleanAlgebra = record
        { isHeytingAlgebra = record
            { isBoundedLattice = record
                { isLattice = ∨-∧-isOrderTheoreticLattice lattice
                ; maximum = λ x → sym (∧-identityʳ x)
                ; minimum = λ x → sym (∧-zeroˡ x)
                }
            ; exponential = λ w x y → to w x y , from w x y
            }

        }
    }
  where
    open ≈-Reasoning setoid
    to : (w x y : Bool) → w ∧ x ≈ (w ∧ x) ∧ y → w ≈ w ∧ (¬ x ∨ y)
    to w x y wx≈wxy = begin
        w                           ≈⟨ ∧-identityʳ w ⟨
        w ∧ ⊤                       ≈⟨ ∧-congˡ {w} (∨-complementˡ x) ⟨
        w ∧ (¬ x ∨ x)               ≈⟨ ∧-congˡ {w} (∨-comm (¬ x) x) ⟩
        w ∧ (x ∨ ¬ x)               ≈⟨ ∧-distribˡ-∨ w x (¬ x) ⟩
        w ∧ x ∨ w ∧ ¬ x             ≈⟨ ∨-congʳ wx≈wxy ⟩
        ((w ∧ x) ∧ y) ∨ w ∧ ¬ x     ≈⟨ ∨-congʳ (∧-assoc w x y) ⟩
        w ∧ (x ∧ y) ∨ w ∧ ¬ x       ≈⟨ ∧-distribˡ-∨ w (x ∧ y) (¬ x) ⟨
        w ∧ (x ∧ y ∨ ¬ x)           ≈⟨ ∧-congˡ (∨-distribʳ-∧ (¬ x) x y) ⟩
        w ∧ ((x ∨ ¬ x) ∧ (y ∨ ¬ x)) ≈⟨ ∧-congˡ {w} (∧-congʳ (∨-complementʳ x)) ⟩
        w ∧ (⊤ ∧ (y ∨ ¬ x))         ≈⟨ ∧-congˡ (∧-identityˡ (y ∨ ¬ x)) ⟩
        w ∧ (y ∨ ¬ x)               ≈⟨ ∧-congˡ (∨-comm y (¬ x)) ⟩
        w ∧ (¬ x ∨ y)               ∎
    from : (w x y : Bool) → w ≈ w ∧ (¬ x ∨ y) → w ∧ x ≈ (w ∧ x) ∧ y
    from w x y w≈¬x∨y = begin
        w ∧ x                 ≈⟨ ∧-congʳ w≈¬x∨y ⟩
        (w ∧ (¬ x ∨ y)) ∧ x   ≈⟨ ∧-assoc w (¬ x ∨ y) x ⟩
        w ∧ (¬ x ∨ y) ∧ x     ≈⟨ ∧-congˡ (∧-distribʳ-∨ x (¬ x) y) ⟩
        w ∧ (¬ x ∧ x ∨ y ∧ x) ≈⟨ ∧-congˡ (∨-congʳ (∧-complementˡ x)) ⟩
        w ∧ (⊥ ∨ y ∧ x)       ≈⟨ ∧-congˡ {w} (∨-identityˡ (y ∧ x)) ⟩
        w ∧ y ∧ x             ≈⟨ ∧-congˡ {w} (∧-comm y x) ⟩
        w ∧ x ∧ y             ≈⟨ ∧-assoc w x y ⟨
        (w ∧ x) ∧ y           ∎

𝔹 : BoundedDistributiveLattice 0ℓ 0ℓ 0ℓ
𝔹 = boundedDistributiveLattice booleanAlgebra

module 𝔹 = BoundedDistributiveLattice 𝔹
