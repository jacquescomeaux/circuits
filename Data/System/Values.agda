{-# OPTIONS --without-K --safe #-}

module Data.System.Values (A : Set) where

open import Data.Nat.Base using (ℕ)
open import Data.Vec.Functional using (Vector)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Setoid)
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid using (≋-setoid)

import Relation.Binary.PropositionalEquality as ≡

Values : ℕ → Setoid 0ℓ 0ℓ
Values = ≋-setoid (≡.setoid A)

_≋_ : {n : ℕ} → Rel (Vector A n) 0ℓ
_≋_ {n} = Setoid._≈_ (Values n)

infix 4 _≋_

module ≋ {n : ℕ} = Setoid (Values n)
