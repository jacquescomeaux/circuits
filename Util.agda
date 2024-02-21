module Util where

open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; _≤_; _<_ ; z<s; s≤s)
open import Data.Product using (_×_)


_<_≤_ : ℕ → ℕ → ℕ → Set
_<_≤_ i j k = (i < j) × (j ≤ k)

_<_<_ : ℕ → ℕ → ℕ → Set
_<_<_ i j k = (i < j) × (j < k)

toℕ< : {n : ℕ} → (i : Fin n) → toℕ i < n
toℕ< Fin.zero = z<s
toℕ< (Fin.suc i) = s≤s (toℕ< i)
