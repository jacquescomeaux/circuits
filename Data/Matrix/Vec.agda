{-# OPTIONS --without-K --safe #-}

module Data.Matrix.Vec where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; replicate; zipWith)

private
  variable
    a : Level
    A : Set a
    n m : ℕ

open Vec

transpose : Vec (Vec A n) m → Vec (Vec A m) n
transpose [] = replicate _ []
transpose (row ∷ mat) = zipWith _∷_ row (transpose mat)
