{-# OPTIONS --without-K --safe #-}
module Util where

open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; _≤_; _<_ ; z<s; s≤s)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)


_<_≤_ : ℕ → ℕ → ℕ → Set
_<_≤_ i j k = (i < j) × (j ≤ k)

_<_<_ : ℕ → ℕ → ℕ → Set
_<_<_ i j k = (i < j) × (j < k)

toℕ< : {n : ℕ} → (i : Fin n) → toℕ i < n
toℕ< Fin.zero = z<s
toℕ< (Fin.suc i) = s≤s (toℕ< i)

data Ordering {n : ℕ} : Fin n → Fin n → Set where
  less : ∀ {i j} → toℕ i < toℕ j < n → Ordering i j
  equal : ∀ {i j} → i ≡ j → Ordering i j
  greater : ∀ {i j} → toℕ j < toℕ i < n → Ordering i j

compare : ∀ {n : ℕ} (i j : Fin n) → Ordering i j
compare Fin.zero Fin.zero = equal refl
compare Fin.zero j@(Fin.suc _) = less (z<s , toℕ< j)
compare i@(Fin.suc _) Fin.zero = greater (z<s , toℕ< i)
compare (Fin.suc i) (Fin.suc j) with compare i j
... | less (i<j , j<n) = less (s≤s i<j , s≤s j<n)
... | equal i≡j = equal (cong Fin.suc i≡j)
... | greater (j<i , i<n) = greater (s≤s j<i , s≤s i<n)
