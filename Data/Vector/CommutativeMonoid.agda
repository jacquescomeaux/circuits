{-# OPTIONS --without-K --safe #-}

open import Algebra using (Monoid; CommutativeMonoid)
open import Level using (Level; _⊔_)

module Data.Vector.CommutativeMonoid {c ℓ : Level} (CM : CommutativeMonoid c ℓ) where

module CM = CommutativeMonoid CM

import Data.Vec.Relation.Binary.Pointwise.Inductive as PW

open import Data.Vector.Core CM.setoid using (Vector; _≊_; module ≊)
open import Data.Vector.Monoid CM.monoid as M using (_⊕_)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)

open CM
open Vec

private
  variable
    n : ℕ

opaque

  unfolding _⊕_

  ⊕-comm : (V W : Vector n) → V ⊕ W ≊ W ⊕ V
  ⊕-comm [] [] = ≊.refl
  ⊕-comm (v ∷ V) (w ∷ W) = comm v w PW.∷ ⊕-comm V W

-- A commutative monoid of vectors for each natural number
Vectorₘ : ℕ → CommutativeMonoid c (c ⊔ ℓ)
Vectorₘ n = record
    { Monoid (M.Vectorₘ n)
    ; isCommutativeMonoid = record
        { Monoid (M.Vectorₘ n)
        ; comm = ⊕-comm
        }
    }
