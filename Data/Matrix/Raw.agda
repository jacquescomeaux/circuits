{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; REL)

module Data.Matrix.Raw where

open import Data.Nat using (ℕ; _+_)
open import Data.Vec as Vec using (Vec; zipWith; head; tail; replicate)
open import Data.Vec using (_++_)
open import Data.Vec.Properties using (map-cong; map-id; map-++; map-∘; map-replicate)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW-Vec using (Pointwise; map⁺)
open import Data.Vector.Raw as Vector using (R-zipWith)
open import Data.Vector.Vec using (zipWith-map; replicate-++; map-zipWith; zipWith-map-map; zipWith-cong)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open ℕ
open Vec.Vec

private
  variable
    n m p : ℕ
    a ℓ ℓ₁ ℓ₂ : Level
    A B C D E F : Set a

open ≡-Reasoning

module FixedBase (A : Set a) where

  opaque

    -- Matrices
    Matrix : Rel ℕ a
    Matrix n m = Vec (Vec A n) m

open FixedBase public

opaque

  unfolding Matrix

  PW : {a b : Level} {A : Set a} {B : Set b} (R : REL A B ℓ) → REL (Matrix A n m) (Matrix B n m) (a ⊔ b ⊔ ℓ)
  PW R = Pointwise (Pointwise R)

  mapRows : (Vec A n → Vec A m) → Matrix A n p → Matrix A m p
  mapRows = Vec.map

  map : (A → B) → Matrix A n m → Matrix B n m
  map f = Vec.map (Vec.map f)

  _∥_ : Matrix A n p → Matrix A m p → Matrix A (n + m) p
  _∥_ M N = zipWith _++_ M N

  infixr 7 _∥_

  _≑_ : Matrix A n m → Matrix A n p → Matrix A n (m + p)
  _≑_ M N = M ++ N

  infixr 6 _≑_

  _∷ᵥ_ : Vec A n → Matrix A n m → Matrix A n (suc m)
  _∷ᵥ_ V M = V Vec.∷ M

  infixr 5 _∷ᵥ_

  _∷ₕ_ : Vec A m → Matrix A n m → Matrix A (suc n) m
  _∷ₕ_ V M = zipWith _∷_ V M

  infixr 5 _∷ₕ_

  headₕ : Matrix A (suc n) m → Vec A m
  headₕ = Vec.map Vec.head

  tailₕ : Matrix A (suc n) m → Matrix A n m
  tailₕ = Vec.map Vec.tail

  head-∷-tailₕ : (M : Matrix A (suc n) m) → headₕ M ∷ₕ tailₕ M ≡ M
  head-∷-tailₕ M = begin
      zipWith _∷_ (Vec.map Vec.head M) (Vec.map Vec.tail M) ≡⟨ zipWith-map head tail _∷_ M ⟩
      Vec.map (λ x → head x ∷ tail x) M                     ≡⟨ map-cong (λ { (_ ∷ _) → ≡.refl }) M ⟩
      Vec.map id M                                          ≡⟨ map-id M ⟩
      M ∎

  []ᵥ : Matrix A 0 m
  []ᵥ = replicate _ []

  []ᵥ-! : (E : Matrix A 0 m) → E ≡ []ᵥ
  []ᵥ-! [] = ≡.refl
  []ᵥ-! ([] ∷ E) = ≡.cong ([] ∷_) ([]ᵥ-! E)

  []ᵥ-≑ : []ᵥ {m = n} ≑ []ᵥ ≡ []ᵥ {A = A} {n + m}
  []ᵥ-≑ {n = n} {m = m} = replicate-++ n m []

  []ᵥ-∥ : (M : Matrix A n m) → []ᵥ ∥ M ≡ M
  []ᵥ-∥ [] = ≡.refl
  []ᵥ-∥ (M₀ ∷ M) = ≡.cong (M₀ ∷_) ([]ᵥ-∥ M)

  ∷ₕ-∥ : (V : Vec A p) (M : Matrix A n p) (N : Matrix A m p) → V ∷ₕ (M ∥ N) ≡ (V ∷ₕ M) ∥ N
  ∷ₕ-∥ [] [] [] = ≡.refl
  ∷ₕ-∥ (x ∷ V) (M₀ ∷ M) (N₀ ∷ N) = ≡.cong ((x ∷ M₀ ++ N₀) ∷_) (∷ₕ-∥ V M N)

  ∷ₕ-≑ : (V : Vec A n) (W : Vec A m) (M : Matrix A p n) (N : Matrix A p m) → (V ++ W) ∷ₕ (M ≑ N) ≡ (V ∷ₕ M) ≑ (W ∷ₕ N)
  ∷ₕ-≑ [] W [] N = ≡.refl
  ∷ₕ-≑ (x ∷ V) W (M₀ ∷ M) N = ≡.cong ((x ∷ M₀) ∷_) (∷ₕ-≑ V W M N)

  headᵥ : Matrix A n (suc m) → Vec A n
  headᵥ = head

  tailᵥ : Matrix A n (suc m) → Matrix A n m
  tailᵥ = tail

  head-∷-tailᵥ : (M : Matrix A n (suc m)) → headᵥ M ∷ᵥ tailᵥ M ≡ M
  head-∷-tailᵥ (_ ∷ _) = ≡.refl

  []ₕ : Matrix A n 0
  []ₕ = []

  []ₕ-! : (E : Matrix A n 0) → E ≡ []ₕ
  []ₕ-! [] = ≡.refl

  []ₕ-≑ : (M : Matrix A n m) → []ₕ ≑ M ≡ M
  []ₕ-≑ _ = ≡.refl

  ∷ᵥ-≑ : (V : Vec A n) (M : Matrix A n m) (N : Matrix A n p) → V ∷ᵥ (M ≑ N) ≡ (V ∷ᵥ M) ≑ N
  ∷ᵥ-≑ V M N = ≡.refl

  _ᵀ : Matrix A n m → Matrix A m n
  _ᵀ [] = []ᵥ
  _ᵀ (M₀ ∷ M) = M₀ ∷ₕ M ᵀ

  infix 10 _ᵀ

  []ᵥ-ᵀ : []ᵥ ᵀ ≡ []ₕ {A = A} {n}
  []ᵥ-ᵀ {n = zero} = ≡.refl
  []ᵥ-ᵀ {n = suc n} = ≡.cong (zipWith _∷_ []) ([]ᵥ-ᵀ)

  ∷ₕ-ᵀ : (V : Vec A n) (M : Matrix A m n) → (V ∷ₕ M) ᵀ ≡ V ∷ᵥ M ᵀ
  ∷ₕ-ᵀ [] [] = ≡.refl
  ∷ₕ-ᵀ (x ∷ V) (M₀ ∷ M) = ≡.cong ((x ∷ M₀) ∷ₕ_) (∷ₕ-ᵀ V M)

  ∷ᵥ-ᵀ : (V : Vec A m) (M : Matrix A m n) → (V ∷ᵥ M) ᵀ ≡ V ∷ₕ M ᵀ
  ∷ᵥ-ᵀ V M = ≡.refl

  _ᵀᵀ : (M : Matrix A n m) → M ᵀ ᵀ ≡ M
  _ᵀᵀ [] = []ᵥ-ᵀ
  _ᵀᵀ (M₀ ∷ M) = begin
      (M₀ ∷ₕ M ᵀ) ᵀ ≡⟨ ∷ₕ-ᵀ M₀ (M ᵀ)  ⟩
      M₀ ∷ᵥ M ᵀ ᵀ   ≡⟨ ≡.cong (M₀ ∷ᵥ_) (M ᵀᵀ) ⟩
      M₀ ∷ᵥ M       ∎

  infix 10 _ᵀᵀ

open Pointwise

module Natural (f : A → B) where

  open Vector.Natural

  opaque

    unfolding map

    α-∥ : (M : Matrix A n p) (N : Matrix A m p) → map f (M ∥ N) ≡ map f M ∥ map f N
    α-∥ M N = begin
        Vec.map (Vec.map f) (zipWith _++_ M N)                        ≡⟨ map-zipWith (Vec.map f) _++_ M N ⟩
        zipWith (λ x y → Vec.map f (x ++ y)) M N                      ≡⟨ zipWith-cong (map-++ f) M N ⟩
        zipWith (λ x y → Vec.map f x ++ Vec.map f y) M N              ≡⟨ zipWith-map-map (Vec.map f) (Vec.map f) _++_ M N ⟩
        zipWith _++_ (Vec.map (Vec.map f) M) (Vec.map (Vec.map f) N)  ∎

    α-≑ : (M : Matrix A n m) (N : Matrix A n p) → map f (M ≑ N) ≡ map f M ≑ map f N
    α-≑ = map-++ (Vec.map f)

    α-∷ᵥ : (V : Vec A n) (M : Matrix A n m) → map f (V ∷ᵥ M) ≡ Vec.map f V ∷ᵥ map f M
    α-∷ᵥ _ _ = ≡.refl

    α-∷ₕ : (V : Vec A m) (M : Matrix A n m) → map f (V ∷ₕ M) ≡ Vec.map f V ∷ₕ map f M
    α-∷ₕ V M = begin
        Vec.map (Vec.map f) (zipWith _∷_ V M)             ≡⟨ map-zipWith (Vec.map f) _∷_ V M ⟩
        zipWith (λ x y → f x ∷ Vec.map f y) V M           ≡⟨ zipWith-map-map f (Vec.map f) _∷_ V M ⟩
        zipWith _∷_ (Vec.map f V) (Vec.map (Vec.map f) M) ∎

    α-headₕ : (M : Matrix A (suc n) m) → Vec.map f (headₕ M) ≡ headₕ (map f M)
    α-headₕ M = begin
        Vec.map f (Vec.map head M)            ≡⟨ map-∘ f head M ⟨
        Vec.map (f ∘ head) M                  ≡⟨ map-cong (α-head f) M ⟩
        Vec.map (head ∘ Vec.map f) M          ≡⟨ map-∘ head (Vec.map f) M ⟩
        Vec.map head (Vec.map (Vec.map f) M) ∎

    α-tailₕ : (M : Matrix A (suc n) m) → map f (tailₕ M) ≡ tailₕ (map f M)
    α-tailₕ M = begin
        Vec.map (Vec.map f) (Vec.map tail M)  ≡⟨ map-∘ (Vec.map f) tail M ⟨
        Vec.map (Vec.map f ∘ tail) M          ≡⟨ map-cong (α-tail f) M ⟩
        Vec.map (tail ∘ Vec.map f) M          ≡⟨ map-∘ tail (Vec.map f) M ⟩
        Vec.map tail (Vec.map (Vec.map f) M)  ∎

    α-[]ᵥ : map f ([]ᵥ {m = m}) ≡ []ᵥ
    α-[]ᵥ {m} = map-replicate (Vec.map f) [] m

    α-headᵥ : (M : Matrix A n (suc m)) → Vec.map f (headᵥ M) ≡ headᵥ (map f M)
    α-headᵥ = α-head (Vec.map f)

    α-tailᵥ : (M : Matrix A n (suc m)) → map f (tailᵥ M) ≡ tailᵥ (map f M)
    α-tailᵥ = α-tail (Vec.map f)

    α-[]ₕ : map f ([]ₕ {n = n}) ≡ []ₕ
    α-[]ₕ = ≡.refl

    α-ᵀ : (M : Matrix A n m) → map f (M ᵀ) ≡ map f M ᵀ
    α-ᵀ [] = α-[]ᵥ
    α-ᵀ (V ∷ M) = begin
        map f (V ∷ₕ M ᵀ)            ≡⟨ α-∷ₕ V (M ᵀ) ⟩
        Vec.map f V ∷ₕ map f (M ᵀ)  ≡⟨ ≡.cong (Vec.map f V ∷ₕ_) (α-ᵀ M) ⟩
        Vec.map f V ∷ₕ map f M ᵀ    ∎

opaque

  unfolding PW

  -- TODO double functor
  map₂
      : {R : REL A B ℓ}
        {S : REL C D ℓ}
        {f : A → C}
        {g : B → D}
      → (∀ {x y} → R x y → S (f x) (g y))
      → {M₁ : Matrix A m n}
        {M₂ : Matrix B m n}
      → PW R M₁ M₂
      → PW S (map f M₁) (map g M₂)
  map₂ R⇒S = map⁺ (map⁺ R⇒S)

module Relation {R : REL A B ℓ} where

  open Vector.Relation

  opaque

    unfolding PW

    R-∥ : {M₁ : Matrix A n p}
          {M₂ : Matrix B n p}
          {N₁ : Matrix A m p}
          {N₂ : Matrix B m p}
        → PW R M₁ M₂
        → PW R N₁ N₂
        → PW R (M₁ ∥ N₁) (M₂ ∥ N₂)
    R-∥ = R-zipWith {R = Pointwise R} (R-++ {R = R})

    R-≑ : {M₁ : Matrix A n m}
          {M₂ : Matrix B n m}
          {N₁ : Matrix A n p}
          {N₂ : Matrix B n p}
        → PW R M₁ M₂
        → PW R N₁ N₂
        → PW R (M₁ ≑ N₁) (M₂ ≑ N₂)
    R-≑ = R-++ {R = Pointwise R}

    R-∷ᵥ
        : {V₁ : Vec A n}
          {V₂ : Vec B n}
          {M₁ : Matrix A n m}
          {M₂ : Matrix B n m}
        → Pointwise R V₁ V₂
        → PW R M₁ M₂
        → PW R (V₁ ∷ᵥ M₁) (V₂ ∷ᵥ M₂)
    R-∷ᵥ R-V R-M = R-V ∷ R-M

    R-∷ₕ
        : {V₁ : Vec A n}
          {V₂ : Vec B n}
          {M₁ : Matrix A m n}
          {M₂ : Matrix B m n}
        → Pointwise R V₁ V₂
        → PW R M₁ M₂
        → PW R (V₁ ∷ₕ M₁) (V₂ ∷ₕ M₂)
    R-∷ₕ [] [] = []
    R-∷ₕ (R-x ∷ R-V) (R-M₀ ∷ R-M) = (R-x ∷ R-M₀) ∷ R-∷ₕ R-V R-M

    R-headₕ
        : {M₁ : Matrix A (suc n) m}
          {M₂ : Matrix B (suc n) m}
        → PW R M₁ M₂
        → Pointwise R (headₕ M₁) (headₕ M₂)
    R-headₕ = map⁺ R-head

    R-tailₕ
        : {M₁ : Matrix A (suc n) m}
          {M₂ : Matrix B (suc n) m}
        → PW R M₁ M₂
        → PW R (tailₕ M₁) (tailₕ M₂)
    R-tailₕ = map⁺ R-tail

    R-[]ᵥ : PW R []ᵥ ([]ᵥ {m = m})
    R-[]ᵥ = R-replicate []

    R-headᵥ
        : {M₁ : Matrix A n (suc m)}
          {M₂ : Matrix B n (suc m)}
        → PW R M₁ M₂
        → Pointwise R (headᵥ M₁) (headᵥ M₂)
    R-headᵥ = R-head

    R-tailᵥ
        : {M₁ : Matrix A n (suc m)}
          {M₂ : Matrix B n (suc m)}
        → PW R M₁ M₂
        → PW R (tailᵥ M₁) (tailᵥ M₂)
    R-tailᵥ = R-tail

    R-[]ₕ : PW R []ₕ ([]ₕ {n = n})
    R-[]ₕ = []

    R-ᵀ
        : {M₁ : Matrix A n m}
          {M₂ : Matrix B n m}
        → PW R M₁ M₂
        → PW R (M₁ ᵀ) (M₂ ᵀ)
    R-ᵀ [] = R-[]ᵥ
    R-ᵀ (R-V ∷ R-M) = R-∷ₕ R-V (R-ᵀ R-M)
