{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Level using (Level; _⊔_)

-- The endofunctor in setoids sending A to Matrix A n m for fixed n and m
module Data.Matrix.Endofunctor (n m : ℕ) {c ℓ : Level} where

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Data.Vec.Properties using (map-id; map-∘)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (map⁺)
open import Data.Vector.Core using (module ≊)
open import Data.Matrix.Core as Core using (Matrix; Matrixₛ; module ≋)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Composition using () renaming (function to compose)
open import Function.Construct.Identity using () renaming (function to Id)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Func

import Data.Vector.Endofunctor as Vector
import Data.Vec as Vec

opaque
  unfolding Matrix
  map : {A B : Setoid c ℓ} → A ⟶ₛ B → Matrixₛ A n m ⟶ₛ Matrixₛ B n m
  map f .to = Vec.map (to (Vector.map n f))
  map f .cong = map⁺ (cong (Vector.map n f))

abstract opaque

  unfolding map

  identity
      : {A : Setoid c ℓ}
        {M : Matrix A n m}
        (open Core A using (_≋_))
      → map (Id A) ⟨$⟩ M ≋ M
  identity {A} {M} = ≋.trans A (map⁺ (≊.trans A (Vector.identity n)) (≋.refl A)) (≋.reflexive A (map-id M))

  homomorphism
      : {X Y Z : Setoid c ℓ}
        {f : X ⟶ₛ Y}
        {g : Y ⟶ₛ Z}
        {M : Matrix X n m}
        (open Core Z using (_≋_))
      → map (compose f g) ⟨$⟩ M ≋ map g ⟨$⟩ (map f ⟨$⟩ M)
  homomorphism {X} {_} {Z} {f} {g} {M} =
      ≋.trans
          Z
          (map⁺ (λ x≈y → ≊.trans Z (Vector.homomorphism n) (cong (Vector.map n g) (cong (Vector.map n f) x≈y))) (≋.refl X))
          (≋.reflexive Z (map-∘ (to (Vector.map n g)) (to (Vector.map n f)) M))

  F-resp-≈
      : {A B : Setoid c ℓ}
        {f g : A ⟶ₛ B}
      → ({x : Setoid.Carrier A} → (B Setoid.≈ to f x) (to g x))
      → {M : Matrix A n m}
        (open Core B using (_≋_))
      → map f ⟨$⟩ M ≋ map g ⟨$⟩ M
  F-resp-≈ {A} {B} {f} {g} f≈g {M} =
      ≋.trans
          B
          (map⁺ (λ x≈y → ≊.trans B (Vector.F-resp-≈ n f≈g) (cong (Vector.map n g) x≈y)) (≋.refl A))
          (map⁺ (cong (Vector.map n g)) (≋.refl A))
    where
      module B = Setoid B

-- only a true endofunctor when c ≤ ℓ
Mat : Functor (Setoids c ℓ) (Setoids c (c ⊔ ℓ))
Mat = record
    { F₀ = λ A → Matrixₛ A n m
    ; F₁ = map
    ; identity = identity
    ; homomorphism = homomorphism
    ; F-resp-≈ = F-resp-≈
    }
