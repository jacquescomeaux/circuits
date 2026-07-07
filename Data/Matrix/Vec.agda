{-# OPTIONS --without-K --safe #-}

module Data.Matrix.Vec where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; replicate; zipWith)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a
    n m : ℕ

open Vec

transpose : Vec (Vec A n) m → Vec (Vec A m) n
transpose [] = replicate _ []
transpose (row ∷ mat) = zipWith _∷_ row (transpose mat)
