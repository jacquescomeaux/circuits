{-# OPTIONS --without-K --safe #-}

open import Level using (Level; 0ℓ; _⊔_)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Algebra using (Semiring)

module Data.Matrix.Transform {c ℓ : Level} (R : Semiring c ℓ) where

module R = Semiring R

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; map; replicate; zipWith)
open import Data.Vec.Properties using (map-id; map-const; map-∘; zipWith-replicate; zipWith-replicate₁; map-replicate; map-cong)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_; _≡_; module ≡-Reasoning)
open import Function using (id; _∘_)

open import Data.Matrix.Core R.setoid
  using
    ( Matrix; Matrixₛ; _≋_; ≋-isEquiv; _ᵀ; _∷ₕ_; []ᵥ; []ₕ; []ᵥ-ᵀ; mapRows
    ; _ᵀᵀ; []ᵥ-!; ∷ₕ-ᵀ; ∷ₕ-cong; module ≋; -ᵀ-cong; _∥_; []ᵥ-∥; headₕ; tailₕ; head-∷-tailₕ; ∷ₕ-∥
    ; _≑_; []ᵥ-≑; ∷ₕ-≑
    )
open import Data.Matrix.Monoid R.+-monoid using (𝟎; 𝟎ᵀ; _[+]_)
open import Data.Vector.Core R.setoid using (Vector; Vectorₛ; ⟨⟩; module ≊; _≊_; _++_; ⟨⟩-++)
open import Data.Vector.Vec using (zipWith-map; map-zipWith; zipWith-map-map)
open import Data.Vector.Monoid R.+-monoid using (_⊕_; ⊕-cong; ⊕-identityˡ; ⊕-identityʳ) renaming (⟨ε⟩ to ⟨0⟩)
open import Data.Vector.Bisemimodule R using (_∙_; ∙-cong; ∙-zeroˡ; ∙-zeroʳ; _⟨_⟩; *-∙ˡ; *-∙ʳ; ∙-distribˡ; ∙-distribʳ)

open Vec
open ℕ
open R

private
  variable
    n m p : ℕ
    A B C D : ℕ

opaque

  unfolding Matrix

  opaque

    unfolding Vector

    _[_] : Matrix n m → Vector n → Vector m
    _[_] M V = map (_∙ V) M

    [_]_ : Vector m → Matrix n m → Vector n
    [_]_ V M = map (V ∙_) (M ᵀ)

    -[-]-cong : {x y : Vector n} (A : Matrix n m) → x ≊ y → A [ x ] ≊ A [ y ]
    -[-]-cong {x = x} {y} A ≋V = PW.map⁺ (λ ≋w → ∙-cong ≋w ≋V) {xs = A} ≋.refl

    -[-]-cong₁ : {M M′ : Matrix n m} → M ≋ M′ → (V : Vector n) → M [ V ] ≊ M′ [ V ]
    -[-]-cong₁ {n} {m} {M} {M′} ≋M V = PW.map⁺ (λ ≊V → ∙-cong ≊V ≊.refl) ≋M

    [-]--cong : {x y : Vector m} {A B : Matrix n m} → x ≊ y → A ≋ B → [ x ] A ≊ [ y ] B
    [-]--cong ≋V A≋B = PW.map⁺ (∙-cong ≋V) (-ᵀ-cong A≋B)

    opaque

      unfolding _ᵀ []ᵥ

      [-]-[]ᵥ : (V : Vector A) → [ V ] []ᵥ ≡ ⟨⟩
      [-]-[]ᵥ [] = ≡.refl
      [-]-[]ᵥ (x ∷ V) = ≡.cong (map ((x ∷ V) ∙_)) []ᵥ-ᵀ

    opaque

      unfolding []ᵥ _ᵀ ⟨0⟩ _∙_

      [-]-[]ₕ : (V : Vector 0) → [ V ] []ₕ ≡ ⟨0⟩ {n}
      [-]-[]ₕ {zero} [] = ≡.refl
      [-]-[]ₕ {suc A} [] = ≡.cong (0# ∷_) ([-]-[]ₕ [])

    opaque
      unfolding _⊕_
      -[⊕] : (M : Matrix A B) (V W : Vector A) → M [ V ⊕ W ] ≊ (M [ V ]) ⊕ (M [ W ])
      -[⊕] [] V W = PW.[]
      -[⊕] (x ∷ M) V W = ∙-distribˡ x V W PW.∷ -[⊕] M V W

opaque

  unfolding Matrix Vector

  -- The identity matrix
  I : Matrix n n
  I {zero} = []
  I {suc n} = (1# ∷ ⟨0⟩) ∷ ⟨0⟩ ∷ₕ I

  opaque

    unfolding _ᵀ _∷ₕ_

    Iᵀ : I ᵀ ≡ I {n}
    Iᵀ {zero} = ≡.sym ([]ᵥ-! [])
    Iᵀ {suc n} = begin
        (1# ∷ ⟨0⟩) ∷ₕ ((⟨0⟩ ∷ₕ I) ᵀ)  ≡⟨ ≡.cong ((1# ∷ ⟨0⟩) ∷ₕ_) (∷ₕ-ᵀ ⟨0⟩ I) ⟩
        (1# ∷ ⟨0⟩) ∷ (⟨0⟩ ∷ₕ (I ᵀ))   ≡⟨ ≡.cong (λ h → (1# ∷ ⟨0⟩) ∷ (⟨0⟩ ∷ₕ h)) Iᵀ ⟩
        (1# ∷ ⟨0⟩) ∷ (⟨0⟩ ∷ₕ I)       ∎
      where
        open ≡-Reasoning

opaque
  unfolding mapRows _ᵀ _[_] [_]_ []ᵥ
  -[-]ᵀ : (A : Matrix m p) (B : Matrix n m) → mapRows (A [_]) (B ᵀ) ≡ (mapRows ([_] B) A) ᵀ
  -[-]ᵀ [] B = map-const (B ᵀ) []
  -[-]ᵀ (A₀ ∷ A) B = begin
      map (λ V → A₀ ∙ V ∷ map (_∙ V) A) (B ᵀ) ≡⟨ zipWith-map (A₀ ∙_) (A [_]) _∷_ (B ᵀ) ⟨
      [ A₀ ] B ∷ₕ (map (A [_]) (B ᵀ))         ≡⟨ ≡.cong ([ A₀ ] B ∷ₕ_) (-[-]ᵀ A B) ⟩
      [ A₀ ] B ∷ₕ ((map ([_] B) A) ᵀ) ∎
    where
      open ≡-Reasoning

opaque
  unfolding [_]_ _[_] _ᵀ []ₕ _∙_ _∷ₕ_ _⟨_⟩

  []-∙ : (V : Vector m) (M : Matrix n m) (W : Vector n) → [ V ] M ∙ W ≈ V ∙ M [ W ]
  []-∙ {n = n} [] M@[] W = begin
      [ [] ] []ₕ ∙ W  ≡⟨ ≡.cong (_∙ W) ([-]-[]ₕ []) ⟩
      ⟨0⟩ ∙ W         ≈⟨ ∙-zeroˡ W ⟩
      0#              ∎
    where
      open ≈-Reasoning setoid
  []-∙ (V₀ ∷ V) (M₀ ∷ M) W = begin
      [ V₀ ∷ V ] (M₀ ∷ M) ∙ W                         ≡⟨ ≡.cong (_∙ W) (map-zipWith ((V₀ ∷ V) ∙_) _∷_ M₀ (M ᵀ)) ⟩
      (zipWith (λ x y → V₀ * x + V ∙ y) M₀ (M ᵀ)) ∙ W ≡⟨ ≡.cong (_∙ W) (zipWith-map-map (V₀ *_) (V ∙_) _+_ M₀ (M ᵀ)) ⟩
      (V₀ ⟨ M₀ ⟩ ⊕ [ V ] M) ∙ W                       ≈⟨ ∙-distribʳ (V₀ ⟨ M₀ ⟩) ([ V ] M) W ⟩
      V₀ ⟨ M₀ ⟩ ∙ W + [ V ] M ∙ W                     ≈⟨ +-congʳ (*-∙ˡ V₀ M₀ W) ⟨
      V₀ * (M₀ ∙ W) + ([ V ] M) ∙ W                   ≈⟨ +-congˡ ([]-∙ V M W) ⟩
      (V₀ ∷ V) ∙ (M₀ ∷ M) [ W ]                       ∎
    where
      open ≈-Reasoning setoid

opaque
  unfolding Vector [_]_ I _∙_ ⟨0⟩ mapRows _ᵀ []ᵥ
  [-]I : {n : ℕ} (V : Vector n) → [ V ] I ≊ V
  [-]I {zero} [] = ≊.refl
  [-]I {suc n} (x ∷ V) = begin
      map ((x ∷ V) ∙_) ((1# ∷ ⟨0⟩) ∷ₕ (⟨0⟩ ∷ₕ I) ᵀ)     ≡⟨ ≡.cong (λ h → map ((x ∷ V) ∙_) ((1# ∷ ⟨0⟩) ∷ₕ h)) (∷ₕ-ᵀ ⟨0⟩ I) ⟩
      x * 1# + V ∙ ⟨0⟩ ∷ map ((x ∷ V) ∙_) (⟨0⟩ ∷ₕ I ᵀ)  ≈⟨ +-congʳ (*-identityʳ x) PW.∷ ≊.refl ⟩
      x + V ∙ ⟨0⟩ ∷ map ((x ∷ V) ∙_) (⟨0⟩ ∷ₕ I ᵀ)       ≈⟨ +-congˡ (∙-zeroʳ V) PW.∷ ≊.refl ⟩
      x + 0# ∷ map ((x ∷ V) ∙_) (⟨0⟩ ∷ₕ I ᵀ)            ≈⟨ +-identityʳ x PW.∷ ≊.refl ⟩
      x ∷ map ((x ∷ V) ∙_) (⟨0⟩ ∷ₕ I ᵀ)                 ≡⟨ ≡.cong (λ h → x ∷ map ((x ∷ V) ∙_) h) (zipWith-replicate₁ _∷_ 0# (I ᵀ)) ⟩
      x ∷ map ((x ∷ V) ∙_) (map (0# ∷_) (I ᵀ))          ≡⟨ ≡.cong (x ∷_) (map-∘ ((x ∷ V) ∙_) (0# ∷_) (I ᵀ)) ⟨
      x ∷ map (λ y → x * 0# + V ∙ y) (I ᵀ)              ≈⟨ refl PW.∷ PW.map⁺ (λ ≊V → trans (+-congʳ (zeroʳ x)) (+-congˡ (∙-cong {v₁ = V} ≊.refl ≊V))) ≋.refl ⟩
      x ∷ map (λ y → 0# + V ∙ y) (I ᵀ)                  ≈⟨ refl PW.∷ PW.map⁺ (λ ≊V → trans (+-identityˡ (V ∙ _)) (∙-cong {v₁ = V} ≊.refl ≊V)) ≋.refl ⟩
      x ∷ map (V ∙_) (I ᵀ)                              ≈⟨ refl PW.∷ ([-]I V) ⟩
      x ∷ V                                             ∎
    where
      open ≈-Reasoning (Vectorₛ (suc n))

opaque
  unfolding _≊_ I _[_] _∙_ _≋_ _∷ₕ_ ⟨0⟩
  I[-] : {n : ℕ} (V : Vector n) → I [ V ] ≊ V
  I[-] {zero} [] = PW.[]
  I[-] {suc n} (x ∷ V) = hd PW.∷ tl
    where
      hd : (1# ∷ ⟨0⟩) ∙ (x ∷ V) ≈ x
      hd = begin
          1# * x + ⟨0⟩ ∙ V  ≈⟨ +-congʳ (*-identityˡ x) ⟩
          x + ⟨0⟩ ∙ V       ≈⟨ +-congˡ (∙-zeroˡ V) ⟩
          x + 0#            ≈⟨ +-identityʳ x ⟩
          x                 ∎
        where
          open ≈-Reasoning setoid
      tl : map (_∙ (x ∷ V)) (⟨0⟩ ∷ₕ I) ≊ V
      tl = begin
          map (_∙ (x ∷ V)) (⟨0⟩ ∷ₕ I)       ≡⟨ ≡.cong (map (_∙ (x ∷ V))) (zipWith-replicate₁ _∷_ 0# I) ⟩
          map (_∙ (x ∷ V)) (map (0# ∷_) I)  ≡⟨ map-∘ (_∙ (x ∷ V)) (0# ∷_) I ⟨
          map (λ t → 0# * x + t ∙ V) I      ≈⟨ PW.map⁺ (λ ≋X → trans (+-congʳ (zeroˡ x)) (+-congˡ (∙-cong ≋X ≊.refl))) {xs = I} ≋.refl ⟩
          map (λ t → 0# + t ∙ V) I          ≈⟨ PW.map⁺ (λ {t} ≋X → trans (+-identityˡ (t ∙ V)) (∙-cong ≋X ≊.refl)) {xs = I} ≋.refl ⟩
          map (_∙ V) I                      ≈⟨ I[-] V ⟩
          V                                 ∎
        where
          open ≈-Reasoning (Vectorₛ n)

opaque
  unfolding mapRows _[_] _ᵀ _∷ₕ_ I
  map--[-]-I : (M : Matrix n m) → mapRows (M [_]) I ≋ M ᵀ
  map--[-]-I {n} {m} [] = ≋.reflexive (map-const I [])
  map--[-]-I {n} {suc m} (M₀ ∷ M) = begin
      map ((M₀ ∷ M) [_]) I              ≡⟨⟩
      map (λ V → M₀ ∙ V ∷ M [ V ]) I    ≡⟨ zipWith-map (M₀ ∙_) (M [_]) _∷_ I ⟨
      map (M₀ ∙_) I ∷ₕ (map (M [_]) I)  ≈⟨ ∷ₕ-cong (≊.reflexive (≡.sym (≡.cong (map (M₀ ∙_)) Iᵀ))) (map--[-]-I M) ⟩
      [ M₀ ] I ∷ₕ (M ᵀ)                 ≈⟨ ∷ₕ-cong ([-]I M₀) ≋.refl ⟩
      M₀ ∷ₕ (M ᵀ)                       ∎
    where
      open ≈-Reasoning (Matrixₛ (suc m) n)

opaque

  unfolding [_]_

  [-]--∥
      : (V : Vector C)
        (M : Matrix A C)
        (N : Matrix B C)
      → [ V ] (M ∥ N) ≡ ([ V ] M) ++ ([ V ] N)
  [-]--∥ {C} {zero} V M N rewrite []ᵥ-! M = begin
      [ V ] ([]ᵥ ∥ N)           ≡⟨ ≡.cong ([ V ]_) ([]ᵥ-∥ N) ⟩
      [ V ] N                   ≡⟨ ⟨⟩-++ ([ V ] N) ⟨
      ⟨⟩ ++ ([ V ] N)           ≡⟨ ≡.cong (_++ ([ V ] N)) ([-]-[]ᵥ V) ⟨
      ([ V ] []ᵥ) ++ ([ V ] N)  ∎
    where
      open ≡-Reasoning
  [-]--∥ {C} {suc A} V M N
    rewrite ≡.sym (head-∷-tailₕ M)
    using M₀ ← headₕ M
    using M ← tailₕ M = begin
      [ V ] ((M₀ ∷ₕ M) ∥ N)                     ≡⟨ ≡.cong ([ V ]_) (∷ₕ-∥ M₀ M N) ⟨
      [ V ] (M₀ ∷ₕ (M ∥ N))                     ≡⟨ ≡.cong (map (V ∙_)) (∷ₕ-ᵀ M₀ (M ∥ N)) ⟩
      V ∙ M₀ ∷ ([ V ] (M ∥ N))                  ≡⟨ ≡.cong (V ∙ M₀ ∷_) ([-]--∥ V M N) ⟩
      V ∙ M₀ ∷ (([ V ] M) ++ ([ V ] N))         ≡⟨⟩
      (V ∙ M₀ ∷ map (V ∙_ ) (M ᵀ)) ++ ([ V ] N) ≡⟨ ≡.cong (λ h → map (V ∙_) h ++ ([ V ] N)) (∷ₕ-ᵀ M₀ M) ⟨
      ([ V ] (M₀ ∷ₕ M)) ++ ([ V ] N)            ∎
    where
      open ≡-Reasoning

opaque

  unfolding _++_ _∙_

  ∙-++ : (W Y : Vector A) (X Z : Vector B) → (W ++ X) ∙ (Y ++ Z) ≈ W ∙ Y + X ∙ Z
  ∙-++ [] [] X Z = sym (+-identityˡ (X ∙ Z))
  ∙-++ (w ∷ W) (y ∷ Y) X Z = begin
      w * y + (W ++ X) ∙ (Y ++ Z) ≈⟨ +-congˡ (∙-++ W Y X Z) ⟩
      w * y + (W ∙ Y + X ∙ Z)     ≈⟨ +-assoc _ _ _ ⟨
      (w * y + W ∙ Y) + X ∙ Z     ∎
    where
      open ≈-Reasoning setoid

opaque

  unfolding _⊕_ ⟨⟩ [_]_

  [++]-≑
      : (V : Vector B)
        (W : Vector C)
        (M : Matrix A B)
        (N : Matrix A C)
      → [ V ++ W ] (M ≑ N)
      ≊ [ V ] M ⊕ [ W ] N
  [++]-≑ {B} {C} {zero} V W M N
    rewrite []ᵥ-! M
    rewrite []ᵥ-! N = begin
      [ V ++ W ] ([]ᵥ {B} ≑ []ᵥ)  ≡⟨ ≡.cong ([ V ++ W ]_) []ᵥ-≑ ⟩
      [ V ++ W ] []ᵥ              ≡⟨ [-]-[]ᵥ (V ++ W) ⟩
      ⟨⟩ ⊕ ⟨⟩                     ≡⟨ ≡.cong₂ _⊕_ ([-]-[]ᵥ V) ([-]-[]ᵥ W) ⟨
      [ V ] []ᵥ ⊕ [ W ] []ᵥ       ∎
    where
      open ≈-Reasoning (Vectorₛ 0)
  [++]-≑ {B} {C} {suc A} V W M N
    rewrite ≡.sym (head-∷-tailₕ M)
    rewrite ≡.sym (head-∷-tailₕ N)
    using M₀ ← headₕ M
    using M ← tailₕ M
    using N₀ ← headₕ N
    using N ← tailₕ N = begin
      [ V ++ W ] ((M₀ ∷ₕ M) ≑ (N₀ ∷ₕ N))            ≡⟨ ≡.cong ([ V ++ W ]_) (∷ₕ-≑ M₀ N₀ M N) ⟨
      [ V ++ W ] ((M₀ ++ N₀) ∷ₕ (M ≑ N))            ≡⟨ ≡.cong (map ((V ++ W) ∙_)) (∷ₕ-ᵀ (M₀ ++ N₀) (M ≑ N)) ⟩
      (V ++ W) ∙ (M₀ ++ N₀) ∷ ([ V ++ W ] (M ≑ N))  ≈⟨ ∙-++ V M₀ W N₀ PW.∷ [++]-≑ V W M N ⟩
      (V ∙ M₀ ∷ [ V ] M) ⊕ (W ∙ N₀ ∷ [ W ] N)       ≡⟨ ≡.cong₂ (λ h₁ h₂ → map (V ∙_) h₁ ⊕ map (W ∙_) h₂) (∷ₕ-ᵀ M₀ M) (∷ₕ-ᵀ N₀ N) ⟨
      ([ V ] (M₀ ∷ₕ M)) ⊕ ([ W ] (N₀ ∷ₕ N))         ∎
    where
      open ≈-Reasoning (Vectorₛ (suc A))
opaque

  unfolding []ₕ []ᵥ [_]_ ⟨0⟩ _∙_ _ᵀ

  [⟨⟩]-[]ₕ : [ ⟨⟩ ] ([]ₕ {A}) ≡ ⟨0⟩ {A}
  [⟨⟩]-[]ₕ {zero} = ≡.refl
  [⟨⟩]-[]ₕ {suc A} = ≡.cong (0# ∷_) [⟨⟩]-[]ₕ

opaque

  unfolding Vector ⟨⟩ ⟨0⟩ []ᵥ [_]_ _ᵀ _∷ₕ_ 𝟎 _≊_

  [-]-𝟎 : (V : Vector A) →  [ V ] (𝟎 {B}) ≊ ⟨0⟩
  [-]-𝟎 {A} {zero} V = ≊.reflexive (≡.cong (map (V ∙_)) 𝟎ᵀ)
  [-]-𝟎 {A} {suc B} V = begin
      map (V ∙_) (𝟎 ᵀ)        ≡⟨ ≡.cong (map (V ∙_)) 𝟎ᵀ ⟩
      V ∙ ⟨0⟩ ∷ map (V ∙_) 𝟎  ≡⟨ ≡.cong ((V ∙ ⟨0⟩ ∷_) ∘ map (V ∙_)) 𝟎ᵀ ⟨
      V ∙ ⟨0⟩ ∷ [ V ] 𝟎       ≈⟨ ∙-zeroʳ V PW.∷ ([-]-𝟎 V) ⟩
      0# ∷ ⟨0⟩                ∎
    where
      open ≈-Reasoning (Vectorₛ (suc B))

opaque

  unfolding ⟨0⟩ ⟨⟩ [_]_

  [⟨0⟩]- : (M : Matrix A B) → [ ⟨0⟩ ] M ≊ ⟨0⟩
  [⟨0⟩]- {zero} M rewrite []ᵥ-! M = ≊.reflexive ([-]-[]ᵥ ⟨0⟩)
  [⟨0⟩]- {suc A} M
    rewrite ≡.sym (head-∷-tailₕ M)
    using M₀ ← headₕ M
    using M ← tailₕ M = begin
      [ ⟨0⟩ ] (M₀ ∷ₕ M)     ≡⟨ ≡.cong (map (⟨0⟩ ∙_)) (∷ₕ-ᵀ M₀ M) ⟩
      ⟨0⟩ ∙ M₀ ∷ [ ⟨0⟩ ] M  ≈⟨ ∙-zeroˡ M₀ PW.∷ [⟨0⟩]- M ⟩
      0# ∷ ⟨0⟩              ∎
    where
      open ≈-Reasoning (Vectorₛ _)

opaque
  unfolding _[_] ⟨0⟩
  -[⟨0⟩] : (M : Matrix A B) → M [ ⟨0⟩ ] ≊ ⟨0⟩
  -[⟨0⟩] {A} {B} [] = PW.[]
  -[⟨0⟩] {A} {B} (M₀ ∷ M) = ∙-zeroʳ M₀ PW.∷ -[⟨0⟩] M
