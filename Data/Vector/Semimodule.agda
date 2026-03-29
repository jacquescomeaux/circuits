{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeSemiring)
open import Level using (Level; _⊔_)

module Data.Vector.Semimodule {c ℓ : Level} (R : CommutativeSemiring c ℓ) where

module R = CommutativeSemiring R

import Data.Vec.Relation.Binary.Pointwise.Inductive as PW

open import Algebra.Module using (Bisemimodule; Semimodule)
open import Data.Nat using (ℕ)
open import Data.Vector.Core R.setoid using (Vector; _≊_)
open import Data.Vec using (Vec)
open import Data.Vector.Bisemimodule R.semiring using (⟨_⟩_; _⟨_⟩; Vector-Bisemimodule)

open R
open Vec

private
  variable
    n : ℕ

opaque

  unfolding ⟨_⟩_ _⟨_⟩

  -- scaling on left equals scaling on right
  ⟨-⟩-comm : (r : Carrier) (V : Vector n) → r ⟨ V ⟩ ≊ ⟨ V ⟩ r
  ⟨-⟩-comm r [] = PW.[]
  ⟨-⟩-comm r (x ∷ V) = *-comm r x PW.∷ ⟨-⟩-comm r V

Vector-Semimodule : ℕ → Semimodule R c (c ⊔ ℓ)
Vector-Semimodule n = record
    { Bisemimodule (Vector-Bisemimodule n)
    ; isSemimodule = record
        { isBisemimodule = record { Bisemimodule (Vector-Bisemimodule n) }
        ; *ₗ-*ᵣ-coincident = ⟨-⟩-comm
        }
    }
