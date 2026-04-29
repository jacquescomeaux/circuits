{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Level using (Level; _⊔_)

-- The endofunctor in setoids sending A to Matrix A n m for fixed n and m
module Data.Matrix.Endofunctor (n m : ℕ) {c ℓ : Level} where

import Data.Vector.Endofunctor as Vector

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; _∘F_)
open import Data.Matrix.Core as Core using (Matrix; Matrixₛ)
open import Data.Vector.Core using (Vector)
open import Function using (_⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Composition using () renaming (function to compose)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (setoid)
open import Relation.Binary using (Setoid)

private

  Vec∘Vec : Functor (Setoids c ℓ) (Setoids c (c ⊔ ℓ))
  Vec∘Vec = Vector.Vec m ∘F Vector.Vec n

  module Vec∘Vec = Functor Vec∘Vec

opaque
  unfolding Matrix Vector
  map : {A B : Setoid c ℓ} → A ⟶ₛ B → Matrixₛ A n m ⟶ₛ Matrixₛ B n m
  map = Vec∘Vec.₁

abstract opaque

  unfolding map

  identity
      : {A : Setoid c ℓ}
        {M : Matrix A n m}
        (open Core A using (_≋_))
      → map (Id A) ⟨$⟩ M ≋ M
  identity = Vec∘Vec.identity

  homomorphism
      : {X Y Z : Setoid c ℓ}
        {f : X ⟶ₛ Y}
        {g : Y ⟶ₛ Z}
        {M : Matrix X n m}
        (open Core Z using (_≋_))
      → map (compose f g) ⟨$⟩ M ≋ map g ⟨$⟩ (map f ⟨$⟩ M)
  homomorphism = Vec∘Vec.homomorphism

  F-resp-≈
      : {A B : Setoid c ℓ}
        {f g : A ⟶ₛ B}
        (open Setoid (setoid A B))
      → (f ≈ g)
      → {M : Matrix A n m}
        (open Core B using (_≋_))
      → map f ⟨$⟩ M ≋ map g ⟨$⟩ M
  F-resp-≈ = Vec∘Vec.F-resp-≈

-- only a true endofunctor when c ≤ ℓ
Mat : Functor (Setoids c ℓ) (Setoids c (c ⊔ ℓ))
Mat = record
    { F₀ = λ A → Matrixₛ A n m
    ; F₁ = map
    ; identity = identity
    ; homomorphism = homomorphism
    ; F-resp-≈ = F-resp-≈
    }
