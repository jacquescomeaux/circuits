{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Semiring)
open import Level using (Level)

module Data.Mat.Cocartesian {c ℓ : Level} (Rig : Semiring c ℓ) where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW

open import Data.Mat.Category Rig
  using
   ( Mat; Matrix; Vector; zeros; I; _≊_; module ≊; ≊-setoid; _≋_; module ≋; ≋-setoid
   ; _ᵀ; mapRows; _·_; _∙_; _ᵀᵀ; _⊕_; ·-identityʳ; ∙-zerosʳ; ∙-zerosˡ
   )
  renaming ([_]_ to [_]′_)

open import Categories.Category.Cocartesian Mat using (Cocartesian)
open import Categories.Object.Coproduct Mat using (Coproduct)
open import Categories.Object.Initial Mat using (Initial)
open import Data.Mat.Util using (replicate-++; zipWith-map; transpose-zipWith; zipWith-cong)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Vec using (Vec; map; zipWith; replicate; _++_; head; tail)
open import Data.Vec.Properties using (zipWith-replicate; map-cong; map-const; map-id)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open Semiring Rig renaming (Carrier to R)
open Vec
open ℕ.ℕ

private
  variable
    A B C D : ℕ
    A₁ A₂ B₁ B₂ : ℕ

opaque
  unfolding Vector
  _+++_ : Vector A → Vector B → Vector (A ℕ.+ B)
  _+++_ = _++_

opaque
  unfolding Matrix Vector
  _∥_ : Matrix A C → Matrix B C → Matrix (A ℕ.+ B) C
  _∥_ M N = zipWith _++_ M N

opaque
  unfolding Matrix
  [_] : Vector A → Matrix A 1
  [_] V = V ∷ []

opaque
  unfolding Matrix Vector
  ⟦_⟧ : R → Matrix 1 1
  ⟦_⟧ x = [ x ∷ [] ]

[_]ᵀ : Vector A → Matrix 1 A
[_]ᵀ V = [ V ] ᵀ

opaque
  unfolding Vector
  ⟨⟩ : Vector 0
  ⟨⟩ = []

opaque
  unfolding Vector
  _∷′_ : R → Vector A → Vector (suc A)
  _∷′_ = _∷_

infixr 5 _∷′_

infixr 7 _∥_

opaque
  unfolding Matrix
  _≑_ : Matrix A B → Matrix A C → Matrix A (B ℕ.+ C)
  _≑_ M N = M ++ N

infixr 6 _≑_

opaque
  unfolding Matrix
  _∷ᵥ_ : Vector A → Matrix A B → Matrix A (suc B)
  _∷ᵥ_ V M = V ∷ M

infixr 5 _∷ᵥ_

opaque
  unfolding Matrix Vector
  _∷ₕ_ : Vector B → Matrix A B → Matrix (suc A) B
  _∷ₕ_ V M = zipWith _∷_ V M

infixr 5 _∷ₕ_

opaque
  unfolding Matrix
  headᵥ : Matrix A (suc B) → Vector A
  headᵥ (V ∷ _) = V

opaque
  unfolding Matrix
  tailᵥ : Matrix A (suc B) → Matrix A B
  tailᵥ (_ ∷ M) = M

opaque
  unfolding Matrix Vector
  headₕ : Matrix (suc A) B → Vector B
  headₕ M = map head M

opaque
  unfolding Matrix Vector
  tailₕ : Matrix (suc A) B → Matrix A B
  tailₕ M = map tail M

opaque
  unfolding _∷ᵥ_ headᵥ tailᵥ
  head-∷-tailᵥ : (M : Matrix A (suc B)) → headᵥ M ∷ᵥ tailᵥ M ≡ M
  head-∷-tailᵥ (_ ∷ _) = ≡.refl

opaque
  unfolding _∷ₕ_ headₕ tailₕ
  head-∷-tailₕ : (M : Matrix (suc A) B) → headₕ M ∷ₕ tailₕ M ≡ M
  head-∷-tailₕ M = begin
      zipWith _∷_ (map head M) (map tail M) ≡⟨ zipWith-map head tail _∷_ M ⟩
      map (λ x → head x ∷ tail x) M         ≡⟨ map-cong (λ { (_ ∷ _) → ≡.refl }) M ⟩
      map id M                              ≡⟨ map-id M ⟩
      M ∎
    where
      open ≡-Reasoning

opaque
  unfolding Matrix
  []ₕ : Matrix A 0
  []ₕ = []

opaque
  unfolding []ₕ _ᵀ
  []ᵥ : Matrix 0 B
  []ᵥ = []ₕ ᵀ

opaque
  unfolding []ᵥ
  []ᵥ-ᵀ : []ᵥ ᵀ ≡ []ₕ {A}
  []ᵥ-ᵀ = []ₕ ᵀᵀ

opaque
  unfolding []ₕ
  []ₕ-! : (E : Matrix A 0) → E ≡ []ₕ
  []ₕ-! [] = ≡.refl

opaque
  unfolding []ᵥ
  []ᵥ-! : (E : Matrix 0 B) → E ≡ []ᵥ
  []ᵥ-! [] = ≡.refl
  []ᵥ-! ([] ∷ E) = ≡.cong ([] ∷_) ([]ᵥ-! E)

opaque
  unfolding Matrix Vector
  _∷[_,_]_ : R → Vector B → Vector A → Matrix A B → Matrix (suc A) (suc B)
  _∷[_,_]_ v C R M = (v ∷ R) ∷ᵥ (C ∷ₕ M)

opaque
  unfolding Matrix
  𝟎 : Matrix A B
  𝟎 {A} {B} = replicate B zeros

opaque
  unfolding 𝟎 _ᵀ zeros _∷ₕ_ _∥_
  𝟎ᵀ : 𝟎 ᵀ ≡ 𝟎 {A} {B}
  𝟎ᵀ {zero} = ≡.refl
  𝟎ᵀ {suc A} = begin
      zeros ∷ₕ (𝟎 ᵀ)  ≡⟨ ≡.cong (zeros ∷ₕ_) 𝟎ᵀ ⟩
      zeros ∷ₕ 𝟎      ≡⟨ zipWith-replicate _∷_ 0# zeros ⟩
      𝟎               ∎
    where
      open ≡-Reasoning

opaque
  unfolding _∥_ []ᵥ
  []ᵥ-∥ : (M : Matrix A B) → []ᵥ ∥ M ≡ M
  []ᵥ-∥ [] = ≡.refl
  []ᵥ-∥ (M₀ ∷ M) = ≡.cong (M₀ ∷_) ([]ᵥ-∥ M)

opaque
  unfolding _≑_ []ₕ
  []ₕ-≑ : (M : Matrix A B) → []ₕ ≑ M ≡ M
  []ₕ-≑ _ = ≡.refl

opaque
  unfolding _∷ₕ_ _ᵀ _∷ᵥ_
  ∷ₕ-ᵀ : (V : Vector A) (M : Matrix B A) → (V ∷ₕ M) ᵀ ≡ V ∷ᵥ M ᵀ
  ∷ₕ-ᵀ = transpose-zipWith

opaque
  unfolding _∷ₕ_ _ᵀ _∷ᵥ_
  ∷ᵥ-ᵀ : (V : Vector B) (M : Matrix B A) → (V ∷ᵥ M) ᵀ ≡ V ∷ₕ M ᵀ
  ∷ᵥ-ᵀ V M = ≡.refl

opaque
  unfolding _∷ₕ_ _∥_
  ∷ₕ-∥ : (V : Vector C) (M : Matrix A C) (N : Matrix B C) → V ∷ₕ (M ∥ N) ≡ (V ∷ₕ M) ∥ N
  ∷ₕ-∥ [] [] [] = ≡.refl
  ∷ₕ-∥ (x ∷ V) (M₀ ∷ M) (N₀ ∷ N) = ≡.cong ((x ∷ M₀ ++ N₀) ∷_) (∷ₕ-∥ V M N)

opaque
  unfolding _∷ᵥ_ _≑_
  ∷ᵥ-≑ : (V : Vector A) (M : Matrix A B) (N : Matrix A C) → V ∷ᵥ (M ≑ N) ≡ (V ∷ᵥ M) ≑ N
  ∷ᵥ-≑ V M N = ≡.refl

opaque
  unfolding zeros [_]′_ Matrix _∙_
  [-]- : (V : Vector 0) (E : Matrix A 0) → [ V ]′ E ≡ zeros
  [-]- {zero} _ [] = ≡.refl
  [-]- {suc A} [] [] = ≡.cong (0# ∷_) ([-]- [] [])

opaque
  unfolding ⟨⟩ _+++_
  ⟨⟩-+++ : (V : Vector A) → ⟨⟩ +++ V ≡ V
  ⟨⟩-+++ V = ≡.refl

opaque
  unfolding _∷′_ _+++_
  ∷-+++ : (x : R) (M : Vector A) (N : Vector B) → (x ∷′ M) +++ N ≡ x ∷′ (M +++ N)
  ∷-+++ x M N = ≡.refl

opaque
  unfolding []ₕ [_]′_ _ᵀ []ᵥ ⟨⟩
  [-]-[]ᵥ : (V : Vector A) → [ V ]′ []ᵥ ≡ ⟨⟩
  [-]-[]ᵥ [] = ≡.refl
  [-]-[]ᵥ (x ∷ V) = ≡.cong (map ((x ∷ V) ∙_)) []ᵥ-ᵀ

opaque
  unfolding [_]′_ _ᵀ _∷ᵥ_ _∷′_
  [-]-∷ₕ : (V M₀ : Vector B) (M : Matrix A B) → [ V ]′ (M₀ ∷ₕ M) ≡ V ∙ M₀ ∷′ ([ V ]′ M)
  [-]-∷ₕ V M₀ M = ≡.cong (map (V ∙_)) (∷ₕ-ᵀ M₀ M)
    where
      open ≡-Reasoning

[-]--∥
    : (V : Vector C)
      (M : Matrix A C)
      (N : Matrix B C)
    → [ V ]′ (M ∥ N) ≡ ([ V ]′ M) +++ ([ V ]′ N)
[-]--∥ {C} {zero} V M N rewrite []ᵥ-! M = begin
    [ V ]′ ([]ᵥ ∥ N)            ≡⟨ ≡.cong ([ V ]′_) ([]ᵥ-∥ N) ⟩
    [ V ]′ N                    ≡⟨ ⟨⟩-+++ ([ V ]′ N) ⟨
    ⟨⟩ +++ ([ V ]′ N)           ≡⟨ ≡.cong (_+++ ([ V ]′ N)) ([-]-[]ᵥ V) ⟨
    ([ V ]′ []ᵥ) +++ ([ V ]′ N) ∎
  where
    open ≡-Reasoning
[-]--∥ {C} {suc A} V M N
  rewrite ≡.sym (head-∷-tailₕ M)
  using M₀ ← headₕ M
  using M ← tailₕ M = begin
    [ V ]′ ((M₀ ∷ₕ M) ∥ N)                ≡⟨ ≡.cong ([ V ]′_) (∷ₕ-∥ M₀ M N) ⟨
    [ V ]′ (M₀ ∷ₕ (M ∥ N))                ≡⟨ [-]-∷ₕ V M₀ (M ∥ N) ⟩
    V ∙ M₀ ∷′ ([ V ]′ (M ∥ N))            ≡⟨ ≡.cong (V ∙ M₀ ∷′_) ([-]--∥ V M N) ⟩
    V ∙ M₀ ∷′ (([ V ]′ M) +++ ([ V ]′ N)) ≡⟨ ∷-+++ (V ∙ M₀) ([ V ]′ M) ([ V ]′ N) ⟨
    (V ∙ M₀ ∷′ [ V ]′ M) +++ ([ V ]′ N)   ≡⟨ ≡.cong (_+++ ([ V ]′ N)) ([-]-∷ₕ V M₀ M) ⟨
    ([ V ]′ (M₀ ∷ₕ M)) +++ ([ V ]′ N)     ∎
  where
    open ≡-Reasoning

opaque
  unfolding _∥_ mapRows _+++_
  ·-∥
      : (M : Matrix C D)
        (N : Matrix A C)
        (P : Matrix B C)
      → M · (N ∥ P) ≡ M · N ∥ M · P
  ·-∥ {C} {D} {A} {B} [] N P = ≡.refl
  ·-∥ {C} {D} {A} {B} (M₀ ∷ M) N P = ≡.cong₂ _∷_ ([-]--∥ M₀ N P) (·-∥ M N P)

opaque
  unfolding _≑_ mapRows
  ≑-· : (M : Matrix B C)
        (N : Matrix B D)
        (P : Matrix A B)
      → (M ≑ N) · P ≡ (M · P) ≑ (N · P)
  ≑-· [] N P = ≡.refl
  ≑-· (M₀ ∷ M) N P = ≡.cong ([ M₀ ]′ P ∷_) (≑-· M N P)

opaque
  unfolding Matrix
  _[+]_ : Matrix A B → Matrix A B → Matrix A B
  _[+]_ = zipWith _⊕_

opaque
  unfolding _+++_ _≑_ _∷ₕ_
  ∷ₕ-≑ : (V : Vector A) (W : Vector B) (M : Matrix C A) (N : Matrix C B) → (V +++ W) ∷ₕ (M ≑ N) ≡ (V ∷ₕ M) ≑ (W ∷ₕ N)
  ∷ₕ-≑ [] W [] N = ≡.refl
  ∷ₕ-≑ (x ∷ V) W (M₀ ∷ M) N = ≡.cong ((x ∷ M₀) ∷_) (∷ₕ-≑ V W M N)

opaque
  unfolding _+++_ _∙_
  ∙-+++ : (W Y : Vector A) (X Z : Vector B) → (W +++ X) ∙ (Y +++ Z) ≈ W ∙ Y + X ∙ Z
  ∙-+++ [] [] X Z = sym (+-identityˡ (X ∙ Z))
  ∙-+++ (w ∷ W) (y ∷ Y) X Z = begin
      w * y + (W ++ X) ∙ (Y ++ Z) ≈⟨ +-congˡ (∙-+++ W Y X Z) ⟩
      w * y + (W ∙ Y + X ∙ Z)     ≈⟨ +-assoc _ _ _ ⟨
      (w * y + W ∙ Y) + X ∙ Z     ∎
    where
      open ≈-Reasoning setoid

opaque
  unfolding []ᵥ _≑_
  []ᵥ-≑ : []ᵥ {A} ≑ []ᵥ {B} ≡ []ᵥ
  []ᵥ-≑ {A} {B} = replicate-++ A B []

opaque
  unfolding _⊕_ ⟨⟩
  ⟨⟩-⊕ : ⟨⟩ ⊕ ⟨⟩ ≡ ⟨⟩
  ⟨⟩-⊕ = ≡.refl

opaque
  unfolding ≊-setoid _∷′_ _⊕_
  [+++]-≑
      : (V : Vector B)
        (W : Vector C)
        (M : Matrix A B)
        (N : Matrix A C)
      → [ V +++ W ]′ (M ≑ N)
      ≊ [ V ]′ M ⊕ [ W ]′ N
  [+++]-≑ {B} {C} {zero} V W M N
    rewrite []ᵥ-! M
    rewrite []ᵥ-! N = begin
      [ V +++ W ]′ ([]ᵥ {B} ≑ []ᵥ)  ≡⟨ ≡.cong ([ V +++ W ]′_) []ᵥ-≑ ⟩
      [ V +++ W ]′ []ᵥ              ≡⟨ [-]-[]ᵥ (V +++ W) ⟩
      ⟨⟩                            ≡⟨ ⟨⟩-⊕ ⟨
      ⟨⟩ ⊕ ⟨⟩                       ≡⟨ ≡.cong₂ _⊕_ ([-]-[]ᵥ V) ([-]-[]ᵥ W) ⟨
      [ V ]′ []ᵥ ⊕ [ W ]′ []ᵥ       ∎
    where
      open ≈-Reasoning (≊-setoid 0)
  [+++]-≑ {B} {C} {suc A} V W M N
    rewrite ≡.sym (head-∷-tailₕ M)
    rewrite ≡.sym (head-∷-tailₕ N)
    using M₀ ← headₕ M
    using M ← tailₕ M
    using N₀ ← headₕ N
    using N ← tailₕ N = begin
      [ V +++ W ]′ ((M₀ ∷ₕ M) ≑ (N₀ ∷ₕ N))              ≡⟨ ≡.cong ([ V +++ W ]′_) (∷ₕ-≑ M₀ N₀ M N) ⟨
      [ V +++ W ]′ ((M₀ +++ N₀) ∷ₕ (M ≑ N))             ≡⟨ [-]-∷ₕ (V +++ W) (M₀ +++ N₀) (M ≑ N) ⟩
      (V +++ W) ∙ (M₀ +++ N₀) ∷′ ([ V +++ W ]′ (M ≑ N)) ≈⟨ ∙-+++ V M₀ W N₀ PW.∷ [+++]-≑ V W M N ⟩
      (V ∙ M₀ ∷′ [ V ]′ M) ⊕ (W ∙ N₀ ∷′ [ W ]′ N)       ≡⟨ ≡.cong₂ _⊕_ ([-]-∷ₕ V M₀ M) ([-]-∷ₕ W N₀ N) ⟨
      ([ V ]′ (M₀ ∷ₕ M)) ⊕ ([ W ]′ (N₀ ∷ₕ N))           ∎
    where
      open ≈-Reasoning (≊-setoid (suc A))

opaque
  unfolding _∥_ _+++_ mapRows _[+]_ ≋-setoid
  ∥-·-≑
      : (W : Matrix A C)
        (X : Matrix B C)
        (Y : Matrix D A)
        (Z : Matrix D B)
      → (W ∥ X) · (Y ≑ Z) ≋ (W · Y) [+] (X · Z)
  ∥-·-≑ [] [] Y Z = PW.[]
  ∥-·-≑ {A} {C} {B} {D} (W₀ ∷ W) (X₀ ∷ X) Y Z = [+++]-≑ W₀ X₀ Y Z PW.∷ ∥-·-≑ W X Y Z
    where
      open ≈-Reasoning (≋-setoid A B)

opaque
  unfolding _⊕_ _≊_
  ⊕-cong : {V V′ W W′ : Vector A} → V ≊ V′ → W ≊ W′ → V ⊕ W ≊ V′ ⊕ W′
  ⊕-cong = zipWith-cong +-cong

opaque
  unfolding _[+]_ _≋_
  [+]-cong : {M M′ N N′ : Matrix A B} → M ≋ M′ → N ≋ N′ → M [+] N ≋ M′ [+] N′
  [+]-cong = zipWith-cong ⊕-cong

opaque
  unfolding ⟨⟩ []ₕ [_]′_ zeros _∙_
  [⟨⟩]-[]ₕ : [ ⟨⟩ ]′ ([]ₕ {A}) ≡ zeros {A}
  [⟨⟩]-[]ₕ {zero} = ≡.refl
  [⟨⟩]-[]ₕ {suc A} = ≡.cong (0# ∷_) [⟨⟩]-[]ₕ

opaque
  unfolding Vector ⟨⟩ zeros []ᵥ [_]′_ _ᵀ _∷ₕ_ 𝟎 _≊_
  [-]-𝟎 : (V : Vector A) →  [ V ]′ (𝟎 {B}) ≊ zeros
  [-]-𝟎 {A} {zero} V = ≊.reflexive (≡.cong (map (V ∙_)) 𝟎ᵀ)
  [-]-𝟎 {A} {suc B} V = begin
      map (V ∙_) (𝟎 ᵀ)          ≡⟨ ≡.cong (map (V ∙_)) 𝟎ᵀ ⟩
      V ∙ zeros ∷ map (V ∙_) 𝟎  ≡⟨ ≡.cong ((V ∙ zeros ∷_) ∘ map (V ∙_)) 𝟎ᵀ ⟨
      V ∙ zeros ∷ [ V ]′ 𝟎      ≈⟨ ∙-zerosʳ V PW.∷ ([-]-𝟎 V) ⟩
      0# ∷ zeros                ∎
    where
      open ≈-Reasoning (≊-setoid (suc B))

opaque
  unfolding _⊕_ zeros _≊_
  ⊕-zerosʳ : (V : Vector A) → V ⊕ zeros ≊ V
  ⊕-zerosʳ [] = PW.[]
  ⊕-zerosʳ (x ∷ V) = +-identityʳ x PW.∷ ⊕-zerosʳ V

opaque
  unfolding _⊕_ zeros _≊_
  ⊕-zerosˡ : (V : Vector A) → zeros ⊕ V ≊ V
  ⊕-zerosˡ [] = PW.[]
  ⊕-zerosˡ (x ∷ V) = +-identityˡ x PW.∷ ⊕-zerosˡ V

opaque
  unfolding Matrix _[+]_ _≋_ 𝟎
  [+]-𝟎ʳ : (M : Matrix A B) → M [+] 𝟎 ≋ M
  [+]-𝟎ʳ [] = PW.[]
  [+]-𝟎ʳ (M₀ ∷ M) = ⊕-zerosʳ M₀ PW.∷ [+]-𝟎ʳ M

opaque
  unfolding Matrix _[+]_ _≋_ 𝟎
  [+]-𝟎ˡ : (M : Matrix A B) → 𝟎 [+] M ≋ M
  [+]-𝟎ˡ [] = PW.[]
  [+]-𝟎ˡ (M₀ ∷ M) = ⊕-zerosˡ M₀ PW.∷ [+]-𝟎ˡ M


opaque
  unfolding ≋-setoid mapRows 𝟎
  ·-𝟎ʳ : (M : Matrix A B) →  M · 𝟎 {C} ≋ 𝟎
  ·-𝟎ʳ [] = ≋.refl
  ·-𝟎ʳ (M₀ ∷ M) = begin
      [ M₀ ]′ 𝟎 ∷ M · 𝟎 ≈⟨ [-]-𝟎 M₀ PW.∷ ·-𝟎ʳ M ⟩
      zeros ∷ 𝟎         ∎
    where
      open ≈-Reasoning (≋-setoid _ _)

opaque
  unfolding Matrix zeros ≊-setoid _∷′_ ⟨⟩
  [zeros]- : (M : Matrix A B) → [ zeros ]′ M ≊ zeros
  [zeros]- {zero} M rewrite []ᵥ-! M = ≊.reflexive ([-]-[]ᵥ zeros)
  [zeros]- {suc A} M
    rewrite ≡.sym (head-∷-tailₕ M)
    using M₀ ← headₕ M
    using M ← tailₕ M = begin
      [ zeros ]′ (M₀ ∷ₕ M)      ≡⟨ [-]-∷ₕ zeros M₀ M ⟩
      zeros ∙ M₀ ∷ [ zeros ]′ M ≈⟨ ∙-zerosˡ M₀ PW.∷ [zeros]- M ⟩
      0# ∷ zeros                ∎
    where
      open ≈-Reasoning (≊-setoid _)

opaque
  unfolding ≋-setoid mapRows 𝟎 _ᵀ []ᵥ
  ·-𝟎ˡ : (M : Matrix A B) →  𝟎 {B} {C} · M ≋ 𝟎
  ·-𝟎ˡ {A} {B} {zero} M = PW.[]
  ·-𝟎ˡ {A} {B} {suc C} M = [zeros]- M PW.∷ ·-𝟎ˡ M

opaque
  unfolding ≋-setoid
  inj₁ : (M : Matrix A C) (N : Matrix B C) → (M ∥ N) · (I ≑ 𝟎) ≋ M
  inj₁ {A} {C} M N = begin
      (M ∥ N) · (I ≑ 𝟎)   ≈⟨ ∥-·-≑ M N I 𝟎 ⟩
      (M · I) [+] (N · 𝟎) ≈⟨ [+]-cong ·-identityʳ (·-𝟎ʳ N) ⟩
      M [+] 𝟎             ≈⟨ [+]-𝟎ʳ M ⟩
      M ∎
    where
      open ≈-Reasoning (≋-setoid A C)

opaque
  unfolding ≋-setoid
  inj₂ : (M : Matrix A C) (N : Matrix B C) → (M ∥ N) · (𝟎 ≑ I) ≋ N
  inj₂ {A} {C} {B} M N = begin
      (M ∥ N) · (𝟎 ≑ I)   ≈⟨ ∥-·-≑ M N 𝟎 I ⟩
      (M · 𝟎) [+] (N · I) ≈⟨ [+]-cong (·-𝟎ʳ M) ·-identityʳ ⟩
      𝟎 [+] N             ≈⟨ [+]-𝟎ˡ N ⟩
      N ∎
    where
      open ≈-Reasoning (≋-setoid B C)

opaque
  unfolding Matrix
  split-∥ : (A : ℕ) → (M : Matrix (A ℕ.+ B) C) → Σ[ M₁ ∈ Matrix A C ] Σ[ M₂ ∈ Matrix B C ] M₁ ∥ M₂ ≡ M
  split-∥ zero M = []ᵥ , M , []ᵥ-∥ M
  split-∥ (suc A) M′
    rewrite ≡.sym (head-∷-tailₕ M′)
    using M₀ ← headₕ M′
    using M ← tailₕ M′
    with split-∥ A M
  ... | M₁ , M₂ , M₁∥M₂≡M = M₀ ∷ₕ M₁ , M₂ , (begin
      (M₀ ∷ₕ M₁) ∥ M₂ ≡⟨ ∷ₕ-∥ M₀ M₁ M₂ ⟨
      M₀ ∷ₕ M₁ ∥ M₂   ≡⟨ ≡.cong (M₀ ∷ₕ_) M₁∥M₂≡M ⟩
      M₀ ∷ₕ M ∎)
    where
      open ≡-Reasoning

opaque
  unfolding _≋_ _∷ₕ_
  ∷ₕ-cong : {V V′ : Vector B} {M M′ : Matrix A B} → V ≊ V′ → M ≋ M′ → V ∷ₕ M ≋ V′ ∷ₕ M′
  ∷ₕ-cong PW.[] PW.[] = PW.[]
  ∷ₕ-cong (≈x PW.∷ ≊V) (≊M₀ PW.∷ ≋M) = (≈x PW.∷ ≊M₀) PW.∷ (∷ₕ-cong ≊V ≋M)

opaque
  unfolding Vector
  head′ : Vector (suc A) → R
  head′ = head

opaque
  unfolding Vector
  tail′ : Vector (suc A) → Vector A
  tail′ = tail

opaque
  unfolding _≊_ head′
  head-cong : {V V′ : Vector (suc A)} → V ≊ V′ → head′ V ≈ head′ V′
  head-cong (≈x PW.∷ _) = ≈x

opaque
  unfolding _≊_ tail′
  tail-cong : {V V′ : Vector (suc A)} → V ≊ V′ → tail′ V ≊ tail′ V′
  tail-cong (_ PW.∷ ≊V) = ≊V

opaque
  unfolding _≋_ headₕ head′
  ≋headₕ : {M M′ : Matrix (suc A) B} → M ≋ M′ → headₕ M ≊ headₕ M′
  ≋headₕ M≋M′ = PW.map⁺ head-cong M≋M′

opaque
  unfolding _≋_ tailₕ tail′
  ≋tailₕ : {M M′ : Matrix (suc A) B} → M ≋ M′ → tailₕ M ≋ tailₕ M′
  ≋tailₕ M≋M′ = PW.map⁺ tail-cong M≋M′

opaque
  unfolding _≋_ _≊_ _∷ₕ_
  _≋∷ₕ_ : {V V′ : Vector B} → V ≊ V′ → {M M′ : Matrix A B} → M ≋ M′ → V ∷ₕ M ≋ V′ ∷ₕ M′
  _≋∷ₕ_ PW.[] PW.[] = PW.[]
  _≋∷ₕ_ (≈x PW.∷ ≊V) (≊M₀ PW.∷ ≋M) = (≈x PW.∷ ≊M₀) PW.∷ (≊V ≋∷ₕ ≋M)

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
      open ≈-Reasoning (≋-setoid _ _)
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
          open ≈-Reasoning (≊-setoid _)
      ≋M- : M- ≋ M-′
      ≋M- = begin
          tailₕ M             ≡⟨ ≡.cong tailₕ (head-∷-tailₕ M) ⟨
          tailₕ (M₀ ∷ₕ M-)    ≈⟨ ≋tailₕ ≋M ⟩
          tailₕ (M₀′ ∷ₕ M-′)  ≡⟨ ≡.cong tailₕ (head-∷-tailₕ M′) ⟩
          tailₕ M′            ∎
        where
          open ≈-Reasoning (≋-setoid _ _)
      open ≈-Reasoning (≋-setoid _ _)

opaque
  unfolding _≋_ _≑_
  ≑-cong : {M M′ : Matrix A B} {N N′ : Matrix A C} → M ≋ M′ → N ≋ N′ → M ≑ N ≋ M′ ≑ N′
  ≑-cong PW.[] ≋N = ≋N
  ≑-cong (M₀≊M₀′ PW.∷ ≋M) ≋N = M₀≊M₀′ PW.∷ ≑-cong ≋M ≋N

opaque
  unfolding ≋-setoid
  uniq
      : (H : Matrix (A ℕ.+ B) C)
        (M : Matrix A C)
        (N : Matrix B C)
      → H · (I ≑ 𝟎) ≋ M
      → H · (𝟎 ≑ I) ≋ N
      → M ∥ N ≋ H
  uniq {A} {B} {C} H M N eq₁ eq₂
    with (H₁ , H₂ , H₁∥H₂≡H) ← split-∥ A H
    rewrite ≡.sym H₁∥H₂≡H = begin
      M ∥ N                                         ≈⟨ ∥-cong eq₁ eq₂ ⟨
      (H₁ ∥ H₂) · (I {A} ≑ 𝟎) ∥ (H₁ ∥ H₂) · (𝟎 ≑ I) ≈⟨ ∥-cong (inj₁ H₁ H₂) (inj₂ H₁ H₂) ⟩
      (H₁ ∥ H₂) ∎
    where
      open ≈-Reasoning (≋-setoid (A ℕ.+ B) C)

coproduct : Coproduct A B
coproduct {A} {B} = record
    { A+B = A ℕ.+ B
    ; i₁ = I ≑ 𝟎
    ; i₂ = 𝟎 ≑ I
    ; [_,_] = _∥_
    ; inject₁ = λ {a} {b} {c} → inj₁ b c
    ; inject₂ = λ {a} {b} {c} → inj₂ b c
    ; unique = λ eq₁ eq₂ → uniq _ _ _ eq₁ eq₂
    }

opaque
  unfolding _≋_
  !-unique : (E : Matrix 0 B) → []ᵥ ≋ E
  !-unique E = ≋.reflexive (≡.sym ([]ᵥ-! E))

initial : Initial
initial = record
    { ⊥ = 0
    ; ⊥-is-initial = record
        { ! = []ᵥ
        ; !-unique = !-unique
        }
    }

Mat-Cocartesian : Cocartesian
Mat-Cocartesian = record
    { initial = initial
    ; coproducts = record
        { coproduct = coproduct
        }
    }
