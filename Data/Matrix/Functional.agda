{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Algebra using (Semiring)

module Data.Matrix.Functional {c ℓ : Level} (R : Semiring c ℓ) where

open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.Vec.Functional using (Vector; head; tail)
open import Function using (flip)
open import Relation.Nullary.Decidable using (⌊_⌋)

open Semiring R
open ℕ

Matrix : ℕ → ℕ → Set c
Matrix n m = Vector (Vector Carrier m) n

sum : {n : ℕ} → Vector Carrier n → Carrier
sum {zero} _ = 0#
sum {suc n} v = head v + sum (tail v)

_⟨*⟩_ : {n : ℕ} → Vector Carrier n → Vector Carrier n → Vector Carrier n
_⟨*⟩_ v w i = v i * w i

_⟨+⟩_ : {n : ℕ} → Vector Carrier n → Vector Carrier n → Vector Carrier n
_⟨+⟩_ v w i = v i + w i

_[+]_ : {n m : ℕ} → Matrix n m → Matrix n m → Matrix n m
_[+]_ v w i = v i ⟨+⟩ w i

_∙_ : {n : ℕ} → Vector Carrier n → Vector Carrier n → Carrier
_∙_ v w = sum (v ⟨*⟩ w)

_·_ : {n m o : ℕ} → Matrix m o → Matrix n m → Matrix n o
_·_ A B i j = flip A j ∙ B i

identity : {n : ℕ} → Matrix n n
identity {n} i j = if ⌊ i ≟ j ⌋ then 1# else 0#
