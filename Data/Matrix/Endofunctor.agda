{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Level using (Level; _⊔_)

-- The endofunctor in setoids sending A to Matrix A n m for fixed n and m
module Data.Matrix.Endofunctor (n m : ℕ) {c ℓ : Level} where

import Data.Vector.Endofunctor.Setoid as Vector

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor; _∘F_)
open import Data.Matrix.Raw as Raw using (map; map₂)
open import Data.Matrix.Core as Core using (Matrix; Matrixₛ)
open import Data.Vector.Core using (Vector)
open import Function using (_⟶ₛ_; _⟨$⟩_; Func)
open import Function.Construct.Composition using () renaming (function to compose)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (setoid)
open import Relation.Binary using (Setoid)

private

  Vec∘Vec : Functor (Setoids c ℓ) (Setoids c (c ⊔ ℓ))
  Vec∘Vec = Vector.Vec m ∘F Vector.Vec n

  module Vec∘Vec = Functor Vec∘Vec

open Func

opaque

  unfolding Core._≋_

  mapₛ : {A B : Setoid c ℓ} → A ⟶ₛ B → Matrixₛ A n m ⟶ₛ Matrixₛ B n m
  to (mapₛ f) = map (to f)
  cong (mapₛ f) = map₂ (cong f)

abstract opaque

  unfolding mapₛ

  identity
      : {A : Setoid c ℓ}
        {M : Matrix A n m}
        (open Core A using (_≋_))
      → mapₛ (Id A) ⟨$⟩ M ≋ M
  identity {A} = Vec∘Vec.identity {A}

  homomorphism
      : {X Y Z : Setoid c ℓ}
        {f : X ⟶ₛ Y}
        {g : Y ⟶ₛ Z}
        {M : Matrix X n m}
        (open Core Z using (_≋_))
      → mapₛ (compose f g) ⟨$⟩ M ≋ mapₛ g ⟨$⟩ (mapₛ f ⟨$⟩ M)
  homomorphism {f = f} {g} = Vec∘Vec.homomorphism {f = f} {g}

  F-resp-≈
      : {A B : Setoid c ℓ}
        {f g : A ⟶ₛ B}
        (open Setoid (setoid A B))
      → (f ≈ g)
      → {M : Matrix A n m}
        (open Core B using (_≋_))
      → mapₛ f ⟨$⟩ M ≋ mapₛ g ⟨$⟩ M
  F-resp-≈ {f = f} {g} = Vec∘Vec.F-resp-≈ {f = f} {g}

-- only a true endofunctor when c ≤ ℓ
Mat : Functor (Setoids c ℓ) (Setoids c (c ⊔ ℓ))
Mat = record
    { F₀ = λ A → Matrixₛ A n m
    ; F₁ = mapₛ
    ; identity = identity
    ; homomorphism = homomorphism
    ; F-resp-≈ = F-resp-≈
    }
