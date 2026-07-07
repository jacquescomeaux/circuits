{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)

module Data.Matrix.Core {c ℓ : Level} (S : Setoid c ℓ) where

import Data.Vec.Relation.Binary.Equality.Setoid as PW-≈
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.Matrix.Raw as Raw using (_∥_; _≑_; _∷ᵥ_; _∷ₕ_; headₕ; tailₕ; headᵥ; tailᵥ; _ᵀ)
open import Data.Matrix.Vec using (transpose)
open import Data.Nat using (ℕ; _+_)
open import Data.Vec as Vec using (map; zipWith; head; tail; replicate)
open import Data.Vec.Properties using (map-cong; map-id)
open import Data.Vector.Core S using (Vector; Vectorₛ; _≊_) -- ; _++_; ⟨⟩; ⟨⟩-!)
open import Data.Vector.Vec using (zipWith-map; replicate-++)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open Setoid S
open ℕ

private
  variable
    n m p : ℕ
    A B C : ℕ

private

  module PW-≊ {n} = PW-≈ (Vectorₛ n)

open Raw.FixedBase Carrier using (Matrix) public

opaque

  unfolding Raw.PW

  -- Pointwise equality of matrices
  _≋_ : Rel (Matrix n m) (c ⊔ ℓ)
  _≋_ = Raw.PW _≈_

  infix 4 _≋_

  -- Pointwise equivalence is an equivalence relation
  ≋-isEquiv : IsEquivalence (_≋_ {n} {m})
  ≋-isEquiv {n} {m} = PW-≊.≋-isEquivalence m

module ≋ {n} {m} = IsEquivalence (≋-isEquiv {n} {m})

Matrixₛ : ℕ → ℕ → Setoid c (c ⊔ ℓ)
Matrixₛ n m = record
    { Carrier = Matrix n m
    ; _≈_ = _≋_ {n} {m}
    ; isEquivalence = ≋-isEquiv
  }

opaque

  unfolding _≋_

  ∥-cong
      : {M₁ M₂ : Matrix A C}
        {N₁ N₂ : Matrix B C}
      → M₁ ≋ M₂
      → N₁ ≋ N₂
      → M₁ ∥ N₁ ≋ M₂ ∥ N₂
  ∥-cong = Raw.Relation.R-∥

  ≑-cong
      : {M₁ M₂ : Matrix A B}
        {N₁ N₂ : Matrix A C}
      → M₁ ≋ M₂
      → N₁ ≋ N₂
      → M₁ ≑ N₁ ≋ M₂ ≑ N₂
  ≑-cong = Raw.Relation.R-≑

  ∷ᵥ-cong
      : {V₁ V₂ : Vector n}
        {M₁ M₂ : Matrix n m}
      → V₁ ≊ V₂
      → M₁ ≋ M₂
      → V₁ ∷ᵥ M₁ ≋ V₂ ∷ᵥ M₂
  ∷ᵥ-cong = Raw.Relation.R-∷ᵥ

  ∷ₕ-cong
      : {V₁ V₂ : Vector n}
        {M₁ M₂ : Matrix m n}
      → V₁ ≊ V₂
      → M₁ ≋ M₂
      → V₁ ∷ₕ M₁ ≋ V₂ ∷ₕ M₂
  ∷ₕ-cong = Raw.Relation.R-∷ₕ

  headₕ-cong : {M₁ M₂ : Matrix (suc n) m} → M₁ ≋ M₂ → headₕ M₁ ≊ headₕ M₂
  headₕ-cong = Raw.Relation.R-headₕ

  tailₕ-cong : {M₁ M₂ : Matrix (suc n) m} → M₁ ≋ M₂ → tailₕ M₁ ≋ tailₕ M₂
  tailₕ-cong = Raw.Relation.R-tailₕ

  headᵥ-cong : {M₁ M₂ : Matrix n (suc m)} → M₁ ≋ M₂ → headᵥ M₁ ≊ headᵥ M₂
  headᵥ-cong = Raw.Relation.R-headᵥ

  tailᵥ-cong : {M₁ M₂ : Matrix n (suc m)} → M₁ ≋ M₂ → tailᵥ M₁ ≋ tailᵥ M₂
  tailᵥ-cong = Raw.Relation.R-tailᵥ

  ᵀ-cong : {M₁ M₂ : Matrix n m} → M₁ ≋ M₂ → M₁ ᵀ ≋ M₂ ᵀ
  ᵀ-cong = Raw.Relation.R-ᵀ
