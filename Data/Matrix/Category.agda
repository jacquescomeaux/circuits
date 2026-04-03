{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semiring)
open import Level using (Level; 0ℓ; _⊔_)

module Data.Matrix.Category {c ℓ : Level} (R : Semiring c ℓ) where

module R = Semiring R

import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Data.Matrix.Core R.setoid using (Matrix; Matrixₛ; _≋_; ≋-isEquiv; _ᵀ; -ᵀ-cong; _∷ₕ_; mapRows; _ᵀᵀ; module ≋; _∥_; _≑_)
open import Data.Matrix.Monoid R.+-monoid using (𝟎; _[+]_)
open import Data.Matrix.Transform R using ([_]_; _[_]; -[-]-cong; [-]--cong; -[-]ᵀ; []-∙; [-]--∥; [++]-≑; I; Iᵀ; I[-]; map--[-]-I; [-]-𝟎; [⟨0⟩]-)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; map)
open import Data.Vec.Properties using (map-id; map-∘)
open import Data.Vector.Bisemimodule R using (_∙_; ∙-cong)
open import Data.Vector.Core R.setoid using (Vector; Vectorₛ; module ≊; _≊_)
open import Data.Vector.Monoid R.+-monoid using () renaming (⟨ε⟩ to ⟨0⟩)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open R
open Vec
open ℕ

private
  variable
    n m p : ℕ
    A B C D : ℕ

-- matrix multiplication
_·_ : Matrix m p → Matrix n m → Matrix n p
_·_ A B = mapRows ([_] B) A

-- alternative form
_·′_ : Matrix m p → Matrix n m → Matrix n p
_·′_ A B = mapRows (A [_]) (B ᵀ) ᵀ

infixr 9 _·_ _·′_

·-·′ : (A : Matrix m p) (B : Matrix n m) → A · B ≡ A ·′ B
·-·′ A B = begin
    mapRows ([_] B) A       ≡⟨ mapRows ([_] B) A ᵀᵀ ⟨
    mapRows ([_] B) A ᵀ ᵀ   ≡⟨ ≡.cong (_ᵀ) (-[-]ᵀ A B) ⟨
    mapRows (A [_]) (B ᵀ) ᵀ ∎
  where
    open ≡-Reasoning

opaque

  unfolding _[_]

  ·-[] : {A B C : ℕ} (M : Matrix A B) (N : Matrix B C) (V : Vector A) → (N · M) [ V ] ≊ N [ M [ V ] ]
  ·-[] {A} {B} {zero} M [] V = PW.[]
  ·-[] {A} {B} {suc C} M (N₀ ∷ N) V = []-∙ N₀ M V PW.∷ ·-[] M N V

opaque

  unfolding [_]_

  []-· : {A B C : ℕ} (V : Vector C) (M : Matrix A B) (N : Matrix B C) → [ V ] (N · M) ≊ [ [ V ] N ] M
  []-· {A} {B} {C} V M N = begin
      [ V ] (map ([_] M) N)           ≡⟨ ≡.cong (map (V ∙_)) (-[-]ᵀ N M) ⟨
      map (V ∙_) (map (N [_]) (M ᵀ))  ≡⟨ map-∘ (V ∙_) (N [_]) (M ᵀ) ⟨
      map (λ h → V ∙ N [ h ]) (M ᵀ)   ≈⟨ PW.map⁺ (λ {W} ≋W → trans ([]-∙ V N W) (∙-cong ≊.refl (-[-]-cong N ≋W))) {xs = M ᵀ} ≋.refl ⟨
      map ([ V ] N ∙_) (M ᵀ)          ∎
    where
      open ≈-Reasoning (Vectorₛ A)

opaque

  unfolding _∥_

  ·-∥
      : (M : Matrix C D)
        (N : Matrix A C)
        (P : Matrix B C)
      → M · (N ∥ P) ≡ M · N ∥ M · P
  ·-∥ {C} {D} {A} {B} [] N P = ≡.refl
  ·-∥ {C} {D} {A} {B} (M₀ ∷ M) N P = ≡.cong₂ _∷_ ([-]--∥ M₀ N P) (·-∥ M N P)

opaque

  unfolding _≑_

  ≑-· : (M : Matrix B C)
        (N : Matrix B D)
        (P : Matrix A B)
      → (M ≑ N) · P ≡ (M · P) ≑ (N · P)
  ≑-· [] N P = ≡.refl
  ≑-· (M₀ ∷ M) N P = ≡.cong ([ M₀ ] P ∷_) (≑-· M N P)

opaque

  unfolding _[+]_

  ∥-·-≑
      : (W : Matrix A C)
        (X : Matrix B C)
        (Y : Matrix D A)
        (Z : Matrix D B)
      → (W ∥ X) · (Y ≑ Z) ≋ (W · Y) [+] (X · Z)
  ∥-·-≑ [] [] Y Z = PW.[]
  ∥-·-≑ {A} {C} {B} {D} (W₀ ∷ W) (X₀ ∷ X) Y Z = [++]-≑ W₀ X₀ Y Z PW.∷ ∥-·-≑ W X Y Z
    where
      open ≈-Reasoning (Matrixₛ A B)

opaque

  unfolding Matrix

  ·-resp-≋ : {X X′ : Matrix n p} {Y Y′ : Matrix m n} → X ≋ X′ → Y ≋ Y′ → X · Y ≋ X′ · Y′
  ·-resp-≋ ≋X ≋Y = PW.map⁺ (λ {_} {y} ≋V → [-]--cong ≋V ≋Y) ≋X

  ·-assoc : {A B C D : ℕ} {f : Matrix A B} {g : Matrix B C} {h : Matrix C D} → (h · g) · f ≋ h · g · f
  ·-assoc {A} {B} {C} {D} {f} {g} {h} = begin
      map ([_] f) (map ([_] g) h) ≡⟨ map-∘ ([_] f) ([_] g) h ⟨
      map (λ v → [ [ v ] g ] f) h ≈⟨ PW.map⁺ (λ {x} x≊y → ≊.trans ([]-· x f g) ([-]--cong ([-]--cong x≊y ≋.refl) ≋.refl)) {xs = h} ≋.refl ⟨
      map (λ v → [ v ] (g · f)) h ∎
    where
      open ≈-Reasoning (Matrixₛ A D)

  ·-Iˡ : {f : Matrix n m} → I · f ≋ f
  ·-Iˡ {A} {B} {f} = begin
      I · f               ≡⟨ ·-·′ I f ⟩
      map (I [_]) (f ᵀ) ᵀ ≈⟨ -ᵀ-cong (PW.map⁺ (λ {x} ≊V → ≊.trans (I[-] x) ≊V) {xs = f ᵀ} ≋.refl) ⟩
      map id (f ᵀ) ᵀ      ≡⟨ ≡.cong (_ᵀ) (map-id (f ᵀ)) ⟩
      f ᵀ ᵀ               ≡⟨ f ᵀᵀ ⟩
      f                   ∎
    where
      open ≈-Reasoning (Matrixₛ A B)

  ·-Iʳ : {f : Matrix n m} → f · I ≋ f
  ·-Iʳ {A} {B} {f} = begin
      f · I               ≡⟨ ·-·′ f I ⟩
      map (f [_]) (I ᵀ) ᵀ ≈⟨ -ᵀ-cong (≋.reflexive (≡.cong (map (f [_])) Iᵀ)) ⟩
      map (f [_]) I ᵀ     ≈⟨ -ᵀ-cong (map--[-]-I f) ⟩
      f ᵀ ᵀ               ≡⟨ f ᵀᵀ ⟩
      f ∎
    where
      open ≈-Reasoning (Matrixₛ A B)

opaque

  unfolding 𝟎

  ·-𝟎ʳ : (M : Matrix A B) →  M · 𝟎 {C} ≋ 𝟎
  ·-𝟎ʳ [] = ≋.refl
  ·-𝟎ʳ (M₀ ∷ M) = begin
      [ M₀ ] 𝟎 ∷ M · 𝟎  ≈⟨ [-]-𝟎 M₀ PW.∷ ·-𝟎ʳ M ⟩
      ⟨0⟩ ∷ 𝟎           ∎
    where
      open ≈-Reasoning (Matrixₛ _ _)

  ·-𝟎ˡ : (M : Matrix A B) →  𝟎 {B} {C} · M ≋ 𝟎
  ·-𝟎ˡ {A} {B} {zero} M = PW.[]
  ·-𝟎ˡ {A} {B} {suc C} M = [⟨0⟩]- M PW.∷ ·-𝟎ˡ M

-- The category of matrices over a rig
Mat : Category 0ℓ c (c ⊔ ℓ)
Mat = categoryHelper record
    { Obj = ℕ
    ; _⇒_ = Matrix
    ; _≈_ = _≋_
    ; id = I
    ; _∘_ = _·_
    ; assoc = λ {A B C D f g h} → ·-assoc {f = f} {g} {h}
    ; identityˡ = ·-Iˡ
    ; identityʳ = ·-Iʳ
    ; equiv = ≋-isEquiv
    ; ∘-resp-≈ = ·-resp-≋
    }
