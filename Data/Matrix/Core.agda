{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)

module Data.Matrix.Core {c ℓ : Level} (S : Setoid c ℓ) where

import Data.Vec.Relation.Binary.Equality.Setoid as PW-≈
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.Matrix.Vec using (transpose)
open import Data.Nat using (ℕ; _+_)
open import Data.Vec as Vec using (Vec; map; zipWith; head; tail; replicate)
open import Data.Vec.Properties using (map-cong; map-id)
open import Data.Vector.Core S using (Vector; Vectorₛ; _++_; ⟨⟩; ⟨⟩-!; _≊_)
open import Data.Vector.Vec using (zipWith-map; replicate-++)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open Setoid S
open ℕ
open Vec.Vec

private
  variable
    n m p : ℕ
    A B C : ℕ

private

  module PW-≊ {n} = PW-≈ (Vectorₛ n)

opaque

  -- Matrices over a setoid
  Matrix : Rel ℕ c
  Matrix n m = Vec (Vector n) m

  -- Pointwise equality of matrices
  _≋_ : Rel (Matrix n m) (c ⊔ ℓ)
  _≋_ {n} {m} A B = A PW-≊.≋ B

  -- Pointwise equivalence is an equivalence relation
  ≋-isEquiv : IsEquivalence (_≋_ {n} {m})
  ≋-isEquiv {n} {m} = PW-≊.≋-isEquivalence m

  mapRows : (Vector n → Vector m) → Matrix n p → Matrix m p
  mapRows = map

  _∥_ : Matrix A C → Matrix B C → Matrix (A + B) C
  _∥_ M N = zipWith _++_ M N

  infixr 7 _∥_

  _≑_ : Matrix A B → Matrix A C → Matrix A (B + C)
  _≑_ M N = M Vec.++ N

  infixr 6 _≑_

  _∷ᵥ_ : Vector A → Matrix A B → Matrix A (suc B)
  _∷ᵥ_ V M = V Vec.∷ M

  infixr 5 _∷ᵥ_

  opaque

    unfolding Vector

    _∷ₕ_ : Vector B → Matrix A B → Matrix (suc A) B
    _∷ₕ_ V M = zipWith _∷_ V M

    infixr 5 _∷ₕ_

    ∷ₕ-cong : {V V′ : Vector B} {M M′ : Matrix A B} → V ≊ V′ → M ≋ M′ → V ∷ₕ M ≋ V′ ∷ₕ M′
    ∷ₕ-cong PW.[] PW.[] = PW.[]
    ∷ₕ-cong (≈x PW.∷ ≊V) (≊M₀ PW.∷ ≋M) = (≈x PW.∷ ≊M₀) PW.∷ (∷ₕ-cong ≊V ≋M)

    headₕ : Matrix (suc A) B → Vector B
    headₕ M = map Vec.head M

    tailₕ : Matrix (suc A) B → Matrix A B
    tailₕ M = map Vec.tail M

    head-∷-tailₕ : (M : Matrix (suc A) B) → headₕ M ∷ₕ tailₕ M ≡ M
    head-∷-tailₕ M = begin
        zipWith _∷_ (map Vec.head M) (map Vec.tail M) ≡⟨ zipWith-map head tail _∷_ M ⟩
        map (λ x → head x ∷ tail x) M                 ≡⟨ map-cong (λ { (_ ∷ _) → ≡.refl }) M ⟩
        map id M                                      ≡⟨ map-id M ⟩
        M ∎
      where
        open ≡-Reasoning

    []ᵥ : Matrix 0 B
    []ᵥ = replicate _ []

    []ᵥ-! : (E : Matrix 0 B) → E ≡ []ᵥ
    []ᵥ-! [] = ≡.refl
    []ᵥ-! ([] ∷ E) = ≡.cong ([] ∷_) ([]ᵥ-! E)

    []ᵥ-≑ : []ᵥ {A} ≑ []ᵥ {B} ≡ []ᵥ
    []ᵥ-≑ {A} {B} = replicate-++ A B []

    []ᵥ-∥ : (M : Matrix A B) → []ᵥ ∥ M ≡ M
    []ᵥ-∥ [] = ≡.refl
    []ᵥ-∥ (M₀ ∷ M) = ≡.cong (M₀ ∷_) ([]ᵥ-∥ M)

    ∷ₕ-∥ : (V : Vector C) (M : Matrix A C) (N : Matrix B C) → V ∷ₕ (M ∥ N) ≡ (V ∷ₕ M) ∥ N
    ∷ₕ-∥ [] [] [] = ≡.refl
    ∷ₕ-∥ (x ∷ V) (M₀ ∷ M) (N₀ ∷ N) = ≡.cong ((x ∷ M₀ ++ N₀) ∷_) (∷ₕ-∥ V M N)

    ∷ₕ-≑ : (V : Vector A) (W : Vector B) (M : Matrix C A) (N : Matrix C B) → (V ++ W) ∷ₕ (M ≑ N) ≡ (V ∷ₕ M) ≑ (W ∷ₕ N)
    ∷ₕ-≑ [] W [] N = ≡.refl
    ∷ₕ-≑ (x ∷ V) W (M₀ ∷ M) N = ≡.cong ((x ∷ M₀) ∷_) (∷ₕ-≑ V W M N)

  headᵥ : Matrix A (suc B) → Vector A
  headᵥ (V ∷ _) = V

  tailᵥ : Matrix A (suc B) → Matrix A B
  tailᵥ (_ ∷ M) = M

  head-∷-tailᵥ : (M : Matrix A (suc B)) → headᵥ M ∷ᵥ tailᵥ M ≡ M
  head-∷-tailᵥ (_ ∷ _) = ≡.refl

  []ₕ : Matrix A 0
  []ₕ = []

  []ₕ-! : (E : Matrix A 0) → E ≡ []ₕ
  []ₕ-! [] = ≡.refl

  []ₕ-≑ : (M : Matrix A B) → []ₕ ≑ M ≡ M
  []ₕ-≑ _ = ≡.refl

  ∷ᵥ-≑ : (V : Vector A) (M : Matrix A B) (N : Matrix A C) → V ∷ᵥ (M ≑ N) ≡ (V ∷ᵥ M) ≑ N
  ∷ᵥ-≑ V M N = ≡.refl

infix 4 _≋_

module ≋ {n} {m} = IsEquivalence (≋-isEquiv {n} {m})

Matrixₛ : ℕ → ℕ → Setoid c (c ⊔ ℓ)
Matrixₛ n m = record
    { Carrier = Matrix n m
    ; _≈_ = _≋_ {n} {m}
    ; isEquivalence = ≋-isEquiv
  }

opaque

  unfolding Vector

  head′ : Vector (suc A) → Carrier
  head′ = head

  head-cong : {V V′ : Vector (suc A)} → V ≊ V′ → head′ V ≈ head′ V′
  head-cong (≈x PW.∷ _) = ≈x

  tail′ : Vector (suc A) → Vector A
  tail′ = tail

  tail-cong : {V V′ : Vector (suc A)} → V ≊ V′ → tail′ V ≊ tail′ V′
  tail-cong (_ PW.∷ ≊V) = ≊V

opaque

  unfolding headₕ head′

  ≋headₕ : {M M′ : Matrix (suc A) B} → M ≋ M′ → headₕ M ≊ headₕ M′
  ≋headₕ M≋M′ = PW.map⁺ head-cong M≋M′

  ≋tailₕ : {M M′ : Matrix (suc A) B} → M ≋ M′ → tailₕ M ≋ tailₕ M′
  ≋tailₕ M≋M′ = PW.map⁺ tail-cong M≋M′

opaque
  unfolding _≋_ _∥_ []ᵥ _∷ₕ_
  ∥-cong : {M M′ : Matrix A C} {N N′ : Matrix B C} → M ≋ M′ → N ≋ N′ → M ∥ N ≋ M′ ∥ N′
  ∥-cong {zero} {C} {B} {M} {M′} {N} {N′} ≋M ≋N
    rewrite []ᵥ-! M
    rewrite []ᵥ-! M′ = begin
      ([]ᵥ ∥ N)   ≡⟨ []ᵥ-∥ N ⟩
      N           ≈⟨ ≋N ⟩
      N′          ≡⟨ []ᵥ-∥ N′ ⟨
      ([]ᵥ ∥ N′)  ∎
    where
      open ≈-Reasoning (Matrixₛ _ _)
  ∥-cong {suc A} {C} {B} {M} {M′} {N} {N′} ≋M ≋N
    rewrite ≡.sym (head-∷-tailₕ M)
    using M₀ ← headₕ M
    using M- ← tailₕ M
    rewrite ≡.sym (head-∷-tailₕ M′)
    using M₀′ ← headₕ M′
    using M-′ ← tailₕ M′ = begin
      (M₀ ∷ₕ M-) ∥ N     ≡⟨ ∷ₕ-∥ M₀ M- N ⟨
      M₀ ∷ₕ M- ∥ N       ≈⟨ ∷ₕ-cong ≊M₀ (∥-cong ≋M- ≋N) ⟩
      M₀′ ∷ₕ M-′ ∥ N′    ≡⟨ ∷ₕ-∥ M₀′ M-′ N′ ⟩
      (M₀′ ∷ₕ M-′) ∥ N′  ∎
    where
      ≊M₀ : M₀ ≊ M₀′
      ≊M₀ = begin
          headₕ M             ≡⟨ ≡.cong headₕ (head-∷-tailₕ M) ⟨
          headₕ (M₀ ∷ₕ M-)    ≈⟨ ≋headₕ ≋M ⟩
          headₕ (M₀′ ∷ₕ M-′)  ≡⟨ ≡.cong headₕ (head-∷-tailₕ M′) ⟩
          headₕ M′            ∎
        where
          open ≈-Reasoning (Vectorₛ _)
      ≋M- : M- ≋ M-′
      ≋M- = begin
          tailₕ M             ≡⟨ ≡.cong tailₕ (head-∷-tailₕ M) ⟨
          tailₕ (M₀ ∷ₕ M-)    ≈⟨ ≋tailₕ ≋M ⟩
          tailₕ (M₀′ ∷ₕ M-′)  ≡⟨ ≡.cong tailₕ (head-∷-tailₕ M′) ⟩
          tailₕ M′            ∎
        where
          open ≈-Reasoning (Matrixₛ _ _)
      open ≈-Reasoning (Matrixₛ _ _)

opaque
  unfolding _≑_
  ≑-cong : {M M′ : Matrix A B} {N N′ : Matrix A C} → M ≋ M′ → N ≋ N′ → M ≑ N ≋ M′ ≑ N′
  ≑-cong PW.[] ≋N = ≋N
  ≑-cong (M₀≊M₀′ PW.∷ ≋M) ≋N = M₀≊M₀′ PW.∷ ≑-cong ≋M ≋N

opaque

  unfolding Matrix

  _ᵀ : Matrix n m → Matrix m n
  _ᵀ [] = []ᵥ
  _ᵀ (M₀ ∷ M) = M₀ ∷ₕ M ᵀ

  infix 10 _ᵀ

  -ᵀ-cong : {M₁ M₂ : Matrix n m} → M₁ ≋ M₂ → M₁ ᵀ ≋ M₂ ᵀ
  -ᵀ-cong PW.[] = ≋.refl
  -ᵀ-cong (≊M₀ PW.∷ ≋M) = ∷ₕ-cong ≊M₀ (-ᵀ-cong ≋M)

  opaque

    unfolding []ᵥ []ₕ

    []ᵥ-ᵀ : []ᵥ ᵀ ≡ []ₕ {A}
    []ᵥ-ᵀ {zero} = ≡.refl
    []ᵥ-ᵀ {suc A} = ≡.cong (zipWith _∷_ []) ([]ᵥ-ᵀ)

  opaque

    unfolding _∷ₕ_ Vector

    ∷ₕ-ᵀ : (V : Vector A) (M : Matrix B A) → (V ∷ₕ M) ᵀ ≡ V ∷ᵥ M ᵀ
    ∷ₕ-ᵀ [] [] = ≡.refl
    ∷ₕ-ᵀ (x ∷ V) (M₀ ∷ M) = ≡.cong ((x ∷ M₀) ∷ₕ_) (∷ₕ-ᵀ V M)

  ∷ᵥ-ᵀ : (V : Vector B) (M : Matrix B A) → (V ∷ᵥ M) ᵀ ≡ V ∷ₕ M ᵀ
  ∷ᵥ-ᵀ V M = ≡.refl

  opaque

    _ᵀᵀ : (M : Matrix n m) → M ᵀ ᵀ ≡ M
    _ᵀᵀ [] = []ᵥ-ᵀ
    _ᵀᵀ (M₀ ∷ M) = begin
        (M₀ ∷ₕ M ᵀ) ᵀ ≡⟨ ∷ₕ-ᵀ M₀ (M ᵀ)  ⟩
        M₀ ∷ᵥ M ᵀ ᵀ   ≡⟨ ≡.cong (M₀ ∷ᵥ_) (M ᵀᵀ) ⟩
        M₀ ∷ᵥ M       ∎
      where
        open ≡-Reasoning

  infix 10 _ᵀᵀ
