{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid)

module Data.Matrix.Cast {c ℓ : Level} (S : Setoid c ℓ) where

module S = Setoid S

open import Data.Matrix.Core S using (Matrix; _∥_; _≑_; _∷ₕ_; []ᵥ; []ᵥ-!; []ᵥ-∥; ∷ₕ-∥; head-∷-tailₕ; headₕ; tailₕ)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (suc-injective; +-assoc)
open import Data.Vec using (Vec; map) renaming (cast to castVec)
open import Data.Vec.Properties using (++-assoc-eqFree) renaming (cast-is-id to castVec-is-id)
open import Data.Vector.Core S using (Vector; _++_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open Vec
open ℕ

private
  variable
    A B C D E F : ℕ

opaque
  unfolding Matrix Vector
  cast₁ : .(A ≡ B) → Matrix A C → Matrix B C
  cast₁ eq = map (castVec eq)

opaque
  unfolding Matrix
  cast₂ : .(B ≡ C) → Matrix A B → Matrix A C
  cast₂ eq [] = castVec eq []
  cast₂ {B} {suc C} {A} eq (x ∷ M) = x ∷ cast₂ (suc-injective eq) M

opaque
  unfolding cast₁
  cast₁-is-id : .(eq : A ≡ A) (M : Matrix A B) → cast₁ eq M ≡ M
  cast₁-is-id _ [] = ≡.refl
  cast₁-is-id _ (M₀ ∷ M) = ≡.cong₂ _∷_ (castVec-is-id _ M₀) (cast₁-is-id _ M)

opaque
  unfolding cast₂
  cast₂-is-id : .(eq : B ≡ B) (M : Matrix A B) → cast₂ eq M ≡ M
  cast₂-is-id _ [] = ≡.refl
  cast₂-is-id eq (M₀ ∷ M) = ≡.cong (M₀ ∷_) (cast₂-is-id (suc-injective eq) M)

opaque
  unfolding cast₂
  cast₂-trans : .(eq₁ : B ≡ C) (eq₂ : C ≡ D) (M : Matrix A B) → cast₂ eq₂ (cast₂ eq₁ M) ≡ cast₂ (≡.trans eq₁ eq₂) M
  cast₂-trans {zero} {zero} {zero} {A} eq₁ eq₂ [] = ≡.refl
  cast₂-trans {suc B} {suc C} {suc D} {A} eq₁ eq₂ (M₀ ∷ M) = ≡.cong (M₀ ∷_) (cast₂-trans (suc-injective eq₁) (suc-injective eq₂) M)

opaque
  unfolding _∥_ cast₁
  ∥-assoc
      : (X : Matrix A D)
        (Y : Matrix B D)
        (Z : Matrix C D)
      → cast₁ (+-assoc A B C) ((X ∥ Y) ∥ Z) ≡ X ∥ Y ∥ Z
  ∥-assoc [] [] [] = cast₁-is-id ≡.refl []
  ∥-assoc (X₀ ∷ X) (Y₀ ∷ Y) (Z₀ ∷ Z) = ≡.cong₂ _∷_ (++-assoc-eqFree X₀ Y₀ Z₀) (∥-assoc X Y Z)

opaque
  unfolding _≑_ cast₂
  ≑-assoc
      : (X : Matrix A B)
        (Y : Matrix A C)
        (Z : Matrix A D)
      → cast₂ (+-assoc B C D) ((X ≑ Y) ≑ Z) ≡ X ≑ Y ≑ Z
  ≑-assoc [] Y Z = cast₂-is-id ≡.refl (Y ≑ Z)
  ≑-assoc (X₀ ∷ X) Y Z = ≡.cong (X₀ ∷_) (≑-assoc X Y Z)

≑-sym-assoc
    : (X : Matrix A B)
      (Y : Matrix A C)
      (Z : Matrix A D)
    → cast₂ (≡.sym (+-assoc B C D)) (X ≑ Y ≑ Z) ≡ (X ≑ Y) ≑ Z
≑-sym-assoc {A} {B} {C} {D} X Y Z = begin
    cast₂ _ (X ≑ Y ≑ Z)                 ≡⟨ ≡.cong (cast₂ _) (≑-assoc X Y Z) ⟨
    cast₂ _ (cast₂ assoc ((X ≑ Y) ≑ Z)) ≡⟨ cast₂-trans assoc (≡.sym assoc) ((X ≑ Y) ≑ Z) ⟩
    cast₂ _ ((X ≑ Y) ≑ Z)               ≡⟨ cast₂-is-id _ ((X ≑ Y) ≑ Z) ⟩
    (X ≑ Y) ≑ Z                         ∎
  where
    open ≡-Reasoning
    assoc : B + C + D ≡ B + (C + D)
    assoc = +-assoc B C D

opaque
  unfolding _∥_ _≑_
  ∥-≑ : {A₁ B₁ A₂ B₂ : ℕ}
        (W : Matrix A₁ B₁)
        (X : Matrix A₂ B₁)
        (Y : Matrix A₁ B₂)
        (Z : Matrix A₂ B₂)
      → W ∥ X ≑ Y ∥ Z ≡ (W ≑ Y) ∥ (X ≑ Z)
  ∥-≑ {A₁} {ℕ.zero} {A₂} {B₂} [] [] Y Z = ≡.refl
  ∥-≑ {A₁} {suc B₁} {A₂} {B₂} (W₀ ∷ W) (X₀ ∷ X) Y Z = ≡.cong ((W₀ ++ X₀) ∷_) (∥-≑ W X Y Z)

∥-≑⁴
    : (R : Matrix A D)
      (S : Matrix B D)
      (T : Matrix C D)
      (U : Matrix A E)
      (V : Matrix B E)
      (W : Matrix C E)
      (X : Matrix A F)
      (Y : Matrix B F)
      (Z : Matrix C F)
    → (R ∥ S ∥ T) ≑
      (U ∥ V ∥ W) ≑
      (X ∥ Y ∥ Z)
    ≡ (R ≑ U ≑ X) ∥
      (S ≑ V ≑ Y) ∥
      (T ≑ W ≑ Z)
∥-≑⁴ R S T U V W X Y Z = begin
    R ∥ S ∥ T ≑ U ∥ V ∥ W ≑ X ∥ Y ∥ Z               ≡⟨ ≡.cong (R ∥ S ∥ T ≑_) (∥-≑ U (V ∥ W) X (Y ∥ Z)) ⟩
    R ∥ S ∥ T ≑ (U ≑ X) ∥ (V ∥ W ≑ Y ∥ Z)           ≡⟨ ≡.cong (λ h → (R ∥ S ∥ T ≑ (U ≑ X) ∥ h)) (∥-≑ V W Y Z) ⟩
    R ∥ S ∥ T ≑ (U ≑ X) ∥ (V ≑ Y) ∥ (W ≑ Z)         ≡⟨ ∥-≑ R (S ∥ T) (U ≑ X) ((V ≑ Y) ∥ (W ≑ Z)) ⟩
    (R ≑ (U ≑ X)) ∥ ((S ∥ T) ≑ ((V ≑ Y) ∥ (W ≑ Z))) ≡⟨ ≡.cong ((R ≑ U ≑ X) ∥_) (∥-≑ S T (V ≑ Y) (W ≑ Z)) ⟩
    (R ≑ U ≑ X) ∥ (S ≑ V ≑ Y) ∥ (T ≑ W ≑ Z)         ∎
  where
    open ≡-Reasoning

opaque
  unfolding Vector
  cast : .(A ≡ B) → Vector A → Vector B
  cast = castVec

opaque
  unfolding cast cast₂ _∷ₕ_
  cast₂-∷ₕ : .(eq : B ≡ C) (V : Vector B) (M : Matrix A B) → cast eq V ∷ₕ cast₂ eq M ≡ cast₂ eq (V ∷ₕ M)
  cast₂-∷ₕ {zero} {zero} {A} _ [] [] = ≡.sym (cast₂-is-id ≡.refl ([] ∷ₕ []))
  cast₂-∷ₕ {suc B} {suc C} {A} eq (x ∷ V) (M₀ ∷ M) = ≡.cong ((x ∷ M₀) ∷_) (cast₂-∷ₕ _ V M)

opaque
  unfolding []ᵥ cast₂
  cast₂-[]ᵥ : .(eq : A ≡ B) → cast₂ eq []ᵥ ≡ []ᵥ
  cast₂-[]ᵥ {zero} {zero} _ = ≡.refl
  cast₂-[]ᵥ {suc A} {suc B} eq = ≡.cong ([] ∷_) (cast₂-[]ᵥ (suc-injective eq))

cast₂-∥ : .(eq : C ≡ D) (M : Matrix A C) (N : Matrix B C) → cast₂ eq M ∥ cast₂ eq N ≡ cast₂ eq (M ∥ N)
cast₂-∥ {C} {D} {zero} {B} eq M N
  rewrite ([]ᵥ-! M) = begin
    cast₂ _ []ᵥ ∥ cast₂ _ N ≡⟨ ≡.cong (_∥ cast₂ _ N) (cast₂-[]ᵥ _) ⟩
    []ᵥ ∥ cast₂ _ N         ≡⟨ []ᵥ-∥ (cast₂ _ N) ⟩
    cast₂ _ N               ≡⟨ ≡.cong (cast₂ _) ([]ᵥ-∥ N) ⟨
    cast₂ _ ([]ᵥ ∥ N)       ∎
  where
    open ≡-Reasoning
cast₂-∥ {C} {D} {suc A} {B} eq M N
  rewrite ≡.sym (head-∷-tailₕ M)
  using M₀ ← headₕ M
  using M ← tailₕ M = begin
    cast₂ _ (M₀ ∷ₕ M) ∥ (cast₂ _ N)         ≡⟨ ≡.cong (_∥ (cast₂ eq N)) (cast₂-∷ₕ eq M₀ M) ⟨
    (cast _ M₀ ∷ₕ cast₂ _ M) ∥ (cast₂ _ N)  ≡⟨ ∷ₕ-∥ (cast _ M₀) (cast₂ _ M) (cast₂ _ N) ⟨
    cast _ M₀ ∷ₕ (cast₂ _ M ∥ cast₂ _ N)    ≡⟨ ≡.cong (cast eq M₀ ∷ₕ_) (cast₂-∥ _ M N) ⟩
    cast _ M₀ ∷ₕ cast₂ _ (M ∥ N)            ≡⟨ cast₂-∷ₕ eq M₀ (M ∥ N) ⟩
    cast₂ _ (M₀ ∷ₕ (M ∥ N))                 ≡⟨ ≡.cong (cast₂ eq) (∷ₕ-∥ M₀ M N) ⟩
    cast₂ _ ((M₀ ∷ₕ M) ∥ N)                 ∎
  where
    open ≡-Reasoning
