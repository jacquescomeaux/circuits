{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeSemiring)
open import Level using (Level)

module Data.Mat.SemiadditiveDagger {c ℓ : Level} (Rig : CommutativeSemiring c ℓ) where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Data.Nat.Properties as ℕ-Props

module Rig = CommutativeSemiring Rig

open import Data.Mat.Util using (transpose-cong; replicate-++)
open import Data.Mat.Category Rig.semiring
  using
    ( Mat; _ᵀ; transpose-I; I; _≋_; module ≋; _≊_; module ≊; Matrix; Vector
    ; [_]_; _[_]; _·_; ≋-setoid; ≊-setoid; mapRows; zeros; _∙_
    ; ∙-cong; _ᵀᵀ; -[-]ᵀ
    ; [-]--cong
    ; ·-identityˡ
    ; ·-identityʳ
    )
open import Data.Mat.Cocartesian Rig.semiring
  using
    ( Mat-Cocartesian; []ᵥ; []ₕ; [-]-[]ᵥ; ⟨⟩; _∷ₕ_; ∷ₕ-cong; _∷ᵥ_
    ; [-]-∷ₕ; _∷′_; ∷ₕ-ᵀ; ∷ᵥ-ᵀ; 𝟎; _∥_; _≑_; []ᵥ-∥; []ₕ-≑; []ₕ-!
    ; _+++_; ∷ₕ-≑; []ᵥ-ᵀ; ∥-cong; ≑-cong; ≑-·; ·-𝟎ʳ; ·-𝟎ˡ; 𝟎ᵀ; ·-∥
    ; headₕ; tailₕ; head-∷-tailₕ
    ; ∷ₕ-∥; []ᵥ-!
    )

open import Category.Dagger.Semiadditive Mat using (DaggerCocartesianMonoidal; SemiadditiveDagger)
open import Data.Nat as ℕ using (ℕ)
open import Data.Vec using (Vec; map; replicate)
open import Function using (_∘_)
open import Data.Vec.Properties using (map-cong; map-const)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open ℕ.ℕ
open Vec
open Rig renaming (Carrier to R)

private
  variable
    A B C D E F : ℕ

opaque
  unfolding _≋_
  Iᵀ : I ᵀ ≋ I {A}
  Iᵀ = ≋.reflexive transpose-I

import Data.Vec.Relation.Binary.Pointwise.Inductive as PW

opaque
  unfolding Vector _∙_
  ∙-comm : (V W : Vector A) → V ∙ W ≈ W ∙ V
  ∙-comm [] [] = refl
  ∙-comm (x ∷ V) (w ∷ W) = +-cong (*-comm x w) (∙-comm V W)

opaque
  unfolding _[_] [_]_ _ᵀ []ᵥ ⟨⟩ _∷ₕ_ _≊_ _≋_ _∷ᵥ_
  [-]-ᵀ : (M : Matrix A B) (V : Vector A) →  M [ V ] ≊ [ V ] (M ᵀ)
  [-]-ᵀ [] V = ≊.sym (≊.reflexive ([-]-[]ᵥ V))
  [-]-ᵀ (M₀ ∷ M) V = begin
      M₀ ∙ V ∷ map (_∙ V) M         ≈⟨ ∙-comm M₀ V PW.∷ (PW.map⁺ (λ {x} ≊V → trans (∙-comm x V) (∙-cong ≊.refl ≊V)) ≋.refl) ⟩
      V ∙ M₀ ∷ map (V ∙_) M         ≡⟨⟩
      map (V ∙_) (M₀ ∷ᵥ M)          ≡⟨ ≡.cong (map (V ∙_) ∘ (M₀ ∷ᵥ_)) (M ᵀᵀ) ⟨
      map (V ∙_) (M₀ ∷ᵥ M ᵀ ᵀ)      ≡⟨ ≡.cong (map (V ∙_)) (∷ₕ-ᵀ M₀ (M ᵀ)) ⟨
      map (V ∙_) ((M₀ ∷ₕ (M ᵀ)) ᵀ)  ∎
    where
      open ≈-Reasoning (≊-setoid _)

opaque
  unfolding ≋-setoid []ᵥ mapRows ⟨⟩ _∷ₕ_ _∷ᵥ_
  ·-ᵀ
      : {A B C : ℕ}
        (M : Matrix A B)
        (N : Matrix B C)
      → (N · M) ᵀ ≋ M ᵀ · N ᵀ
  ·-ᵀ {A} {B} {zero} M [] = begin
      []ᵥ                   ≡⟨ map-const (M ᵀ) ⟨⟩ ⟨
      map (λ _ → ⟨⟩) (M ᵀ)  ≡⟨ map-cong [-]-[]ᵥ (M ᵀ) ⟨
      map ([_] []ᵥ) (M ᵀ)   ∎
    where
      open ≈-Reasoning (≋-setoid 0 A)
  ·-ᵀ {A} {B} {suc C} M (N₀ ∷ N) = begin
      map ([_] M) (N₀ ∷ᵥ N) ᵀ       ≡⟨ -[-]ᵀ (N₀ ∷ᵥ N) M ⟨
      map ((N₀ ∷ᵥ N) [_]) (M ᵀ)     ≈⟨ PW.map⁺ (λ {V} ≋V → ≊.trans ([-]-ᵀ (N₀ ∷ᵥ N) V) ([-]--cong {A = (N₀ ∷ᵥ N) ᵀ} ≋V ≋.refl)) ≋.refl ⟩
      map ([_] ((N₀ ∷ᵥ N) ᵀ)) (M ᵀ) ≡⟨ map-cong (λ V → ≡.cong ([ V ]_) (∷ᵥ-ᵀ N₀ N)) (M ᵀ) ⟩
      map ([_] (N₀ ∷ₕ N ᵀ)) (M ᵀ)   ∎
    where
      open ≈-Reasoning (≋-setoid (suc C) A)

opaque
  unfolding _ᵀ _≋_
  ᵀ-cong : {M M′ : Matrix A B} → M ≋ M′ → M ᵀ ≋ M′ ᵀ
  ᵀ-cong ≋M = transpose-cong setoid ≋M

opaque
  unfolding _≋_
  ᵀ-involutive : (M : Matrix A B) → (M ᵀ) ᵀ ≋ M
  ᵀ-involutive M = ≋.reflexive (M ᵀᵀ)

opaque
  unfolding _≋_
  ≋λᵀ : ([]ᵥ ∥ I) ᵀ ≋ 𝟎 ≑ I {A}
  ≋λᵀ = begin
      ([]ᵥ ∥ I) ᵀ ≡⟨ ≡.cong (_ᵀ) ([]ᵥ-∥ I) ⟩
      I ᵀ         ≈⟨ Iᵀ ⟩
      I           ≡⟨ []ₕ-≑ I ⟨
      []ₕ ≑ I     ≡⟨ ≡.cong (_≑ I) ([]ₕ-! 𝟎) ⟨
      𝟎 ≑ I       ∎
    where
      open ≈-Reasoning (≋-setoid _ _)

opaque
  unfolding Matrix _∥_ _ᵀ _≑_ _+++_ _∷ₕ_
  ∥-ᵀ : (M : Matrix A C) (N : Matrix B C) → (M ∥ N) ᵀ ≡ M ᵀ ≑ N ᵀ
  ∥-ᵀ {A} {zero} {B} [] [] = ≡.sym (replicate-++ A B [])
  ∥-ᵀ (M₀ ∷ M) (N₀ ∷ N) = begin
      (M₀ +++ N₀) ∷ₕ ((M ∥ N) ᵀ) ≡⟨ ≡.cong ((M₀ +++ N₀) ∷ₕ_) (∥-ᵀ M N) ⟩
      (M₀ +++ N₀) ∷ₕ (M ᵀ ≑ N ᵀ) ≡⟨ ∷ₕ-≑ M₀ N₀ (M ᵀ) (N ᵀ) ⟩
      (M₀ ∷ₕ M ᵀ) ≑ (N₀ ∷ₕ N ᵀ) ∎
    where
      open ≡-Reasoning

≑-ᵀ : (M : Matrix A B) (N : Matrix A C) → (M ≑ N) ᵀ ≡ M ᵀ ∥ N ᵀ
≑-ᵀ M N = begin
    (M ≑ N) ᵀ           ≡⟨ ≡.cong₂ (λ h₁ h₂ → (h₁ ≑ h₂) ᵀ) (M ᵀᵀ) (N ᵀᵀ) ⟨
    (M ᵀ ᵀ ≑ N ᵀ ᵀ ) ᵀ  ≡⟨ ≡.cong (_ᵀ) (∥-ᵀ (M ᵀ) (N ᵀ)) ⟨
    (M ᵀ ∥ N ᵀ ) ᵀ ᵀ    ≡⟨ (M ᵀ ∥ N ᵀ ) ᵀᵀ ⟩
    M ᵀ ∥ N ᵀ           ∎
  where
    open ≡-Reasoning

opaque
  unfolding _≋_
  ≋ρᵀ : (I ∥ []ᵥ) ᵀ ≋ I {A} ≑ 𝟎
  ≋ρᵀ {A} = begin
      (I ∥ []ᵥ) ᵀ ≡⟨ ∥-ᵀ I []ᵥ ⟩
      I ᵀ ≑ []ᵥ ᵀ ≡⟨ ≡.cong (I ᵀ ≑_) []ᵥ-ᵀ ⟩
      I ᵀ ≑ []ₕ   ≡⟨ ≡.cong (_≑ []ₕ) transpose-I ⟩
      I  ≑ []ₕ    ≡⟨ ≡.cong (I ≑_) ([]ₕ-! 𝟎) ⟨
      I ≑ 𝟎       ∎
    where
      open ≈-Reasoning (≋-setoid _ _)

open import Data.Vec using () renaming (cast to castVec)
open import Data.Vec.Properties using (++-assoc-eqFree) renaming (cast-is-id to castVec-is-id)

opaque
  unfolding Matrix Vector
  cast₁ : .(A ≡ B) → Matrix A C → Matrix B C
  cast₁ eq = map (castVec eq)

opaque
  unfolding Matrix
  cast₂ : .(B ≡ C) → Matrix A B → Matrix A C
  cast₂ eq [] = castVec eq []
  cast₂ {B} {suc C} {A} eq (x ∷ M) = x ∷ cast₂ (ℕ-Props.suc-injective eq) M

opaque
  unfolding cast₁
  cast₁-is-id : .(eq : A ≡ A) (M : Matrix A B) → cast₁ eq M ≡ M
  cast₁-is-id _ [] = ≡.refl
  cast₁-is-id _ (M₀ ∷ M) = ≡.cong₂ _∷_ (castVec-is-id _ M₀) (cast₁-is-id _ M)

opaque
  unfolding cast₂
  cast₂-is-id : .(eq : B ≡ B) (M : Matrix A B) → cast₂ eq M ≡ M
  cast₂-is-id _ [] = ≡.refl
  cast₂-is-id eq (M₀ ∷ M) = ≡.cong (M₀ ∷_) (cast₂-is-id (ℕ-Props.suc-injective eq) M)

opaque
  unfolding cast₂
  cast₂-trans : .(eq₁ : B ≡ C) (eq₂ : C ≡ D) (M : Matrix A B) → cast₂ eq₂ (cast₂ eq₁ M) ≡ cast₂ (≡.trans eq₁ eq₂) M
  cast₂-trans {zero} {zero} {zero} {A} eq₁ eq₂ [] = ≡.refl
  cast₂-trans {suc B} {suc C} {suc D} {A} eq₁ eq₂ (M₀ ∷ M) = ≡.cong (M₀ ∷_) (cast₂-trans (ℕ-Props.suc-injective eq₁) (ℕ-Props.suc-injective eq₂) M)

opaque
  unfolding _∥_ cast₁
  ∥-assoc
      : (X : Matrix A D)
        (Y : Matrix B D)
        (Z : Matrix C D)
      → cast₁ (ℕ-Props.+-assoc A B C) ((X ∥ Y) ∥ Z) ≡ X ∥ Y ∥ Z
  ∥-assoc [] [] [] = cast₁-is-id ≡.refl []
  ∥-assoc (X₀ ∷ X) (Y₀ ∷ Y) (Z₀ ∷ Z) = ≡.cong₂ _∷_ (++-assoc-eqFree X₀ Y₀ Z₀) (∥-assoc X Y Z)

opaque
  unfolding _≑_ cast₂
  ≑-assoc
      : (X : Matrix A B)
        (Y : Matrix A C)
        (Z : Matrix A D)
      → cast₂ (ℕ-Props.+-assoc B C D) ((X ≑ Y) ≑ Z) ≡ X ≑ Y ≑ Z
  ≑-assoc [] Y Z = cast₂-is-id ≡.refl (Y ≑ Z)
  ≑-assoc (X₀ ∷ X) Y Z = ≡.cong (X₀ ∷_) (≑-assoc X Y Z)

≑-sym-assoc
    : (X : Matrix A B)
      (Y : Matrix A C)
      (Z : Matrix A D)
    → cast₂ (≡.sym (ℕ-Props.+-assoc B C D)) (X ≑ Y ≑ Z) ≡ (X ≑ Y) ≑ Z
≑-sym-assoc {A} {B} {C} {D} X Y Z = begin
    cast₂ _ (X ≑ Y ≑ Z)                 ≡⟨ ≡.cong (cast₂ _) (≑-assoc X Y Z) ⟨
    cast₂ _ (cast₂ assoc ((X ≑ Y) ≑ Z)) ≡⟨ cast₂-trans assoc (≡.sym assoc) ((X ≑ Y) ≑ Z) ⟩
    cast₂ _ ((X ≑ Y) ≑ Z)               ≡⟨ cast₂-is-id _ ((X ≑ Y) ≑ Z) ⟩
    (X ≑ Y) ≑ Z                         ∎
  where
    open ≡-Reasoning
    assoc : B ℕ.+ C ℕ.+ D ≡ B ℕ.+ (C ℕ.+ D)
    assoc = ℕ-Props.+-assoc B C D

opaque
  unfolding _∥_ _≑_ _+++_
  ∥-≑ : {A₁ B₁ A₂ B₂ : ℕ}
        (W : Matrix A₁ B₁)
        (X : Matrix A₂ B₁)
        (Y : Matrix A₁ B₂)
        (Z : Matrix A₂ B₂)
      → W ∥ X ≑ Y ∥ Z ≡ (W ≑ Y) ∥ (X ≑ Z)
  ∥-≑ {A₁} {ℕ.zero} {A₂} {B₂} [] [] Y Z = ≡.refl
  ∥-≑ {A₁} {suc B₁} {A₂} {B₂} (W₀ ∷ W) (X₀ ∷ X) Y Z = ≡.cong ((W₀ +++ X₀) ∷_) (∥-≑ W X Y Z)

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
  cast₂-[]ᵥ {suc A} {suc B} eq = ≡.cong ([] ∷_) (cast₂-[]ᵥ (ℕ-Props.suc-injective eq))

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

opaque
  unfolding 𝟎 _≑_
  𝟎≑𝟎 : 𝟎 {A} {B} ≑ 𝟎 {A} {C} ≡ 𝟎
  𝟎≑𝟎 {B = zero} = ≡.refl
  𝟎≑𝟎 {B = suc B} = ≡.cong (zeros ∷_) (𝟎≑𝟎 {B = B})

opaque
  unfolding _∷ₕ_ 𝟎 zeros
  zeros∷ₕ𝟎 : zeros ∷ₕ 𝟎 {A} {B} ≡ 𝟎
  zeros∷ₕ𝟎 {A} {zero} = ≡.refl
  zeros∷ₕ𝟎 {A} {suc B} = ≡.cong (zeros ∷_) zeros∷ₕ𝟎

𝟎∥𝟎 : 𝟎 {A} {C} ∥ 𝟎 {B} {C} ≡ 𝟎
𝟎∥𝟎 {zero} {C} rewrite []ᵥ-! (𝟎 {0} {C}) = []ᵥ-∥ 𝟎
𝟎∥𝟎 {suc A} {C} {B} = begin
    𝟎 ∥ 𝟎                 ≡⟨ ≡.cong (_∥ 𝟎) (zeros∷ₕ𝟎 {A} {C}) ⟨
    (zeros ∷ₕ 𝟎 {A}) ∥ 𝟎  ≡⟨ ∷ₕ-∥ zeros 𝟎 𝟎 ⟨
    zeros ∷ₕ 𝟎 {A} ∥ 𝟎    ≡⟨ ≡.cong (zeros ∷ₕ_) 𝟎∥𝟎 ⟩
    zeros ∷ₕ 𝟎            ≡⟨ zeros∷ₕ𝟎 ⟩
    𝟎 ∎
  where
    open ≡-Reasoning

opaque
  unfolding _≋_
  ≋αᵀ : (((I {A} ≑ 𝟎 {A} {B ℕ.+ C}) ∥ (𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎)) ∥ (𝟎 {_} {A} ≑ I {B ℕ.+ C}) · (𝟎 ≑ I {C})) ᵀ
      ≋ (I {A ℕ.+ B} ≑ 𝟎) · (I {A} ≑ 𝟎) ∥ (I {A ℕ.+ B} ≑ 𝟎) · (𝟎 ≑ I {B}) ∥ (𝟎 ≑ I {C})
  ≋αᵀ {A} {B} {C} = begin
      (((I {A} ≑ 𝟎 {A} {B ℕ.+ C}) ∥ (𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎 {B} {C})) ∥ (𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (𝟎 {C} {B} ≑ I {C})) ᵀ
          ≡⟨ ∥-ᵀ ((I {A} ≑ 𝟎 {A} {B ℕ.+ C}) ∥ (𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎 {B} {C})) ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (𝟎 {C} {B} ≑ I {C})) ⟩
      ((I {A} ≑ 𝟎 {A} {B ℕ.+ C}) ∥ (𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎 {B} {C})) ᵀ ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (𝟎 {C} {B} ≑ I {C})) ᵀ
          ≡⟨ ≡.cong (_≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (𝟎 {C} {B} ≑ I {C})) ᵀ) (∥-ᵀ (I {A} ≑ 𝟎 {A} {B ℕ.+ C}) ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎 {B} {C}))) ⟩
      ((I {A} ≑ 𝟎 {A} {B ℕ.+ C}) ᵀ ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎 {B} {C})) ᵀ) ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (𝟎 {C} {B} ≑ I {C})) ᵀ
          ≡⟨ ≡.cong (λ h → (h ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎 {B} {C})) ᵀ) ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (𝟎 {C} {B} ≑ I {C})) ᵀ) (≑-ᵀ I 𝟎) ⟩
      (I {A} ᵀ ∥ 𝟎 {A} {B ℕ.+ C} ᵀ ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎 {B} {C})) ᵀ) ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (𝟎 {C} {B} ≑ I {C})) ᵀ
          ≡⟨ ≡.cong (λ h → (h ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎 {B} {C})) ᵀ) ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (𝟎 {C} {B} ≑ I {C})) ᵀ) (≡.cong₂ _∥_ Iᵀ′ 𝟎ᵀ) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎 {B} {C})) ᵀ) ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (𝟎 {C} {B} ≑ I {C})) ᵀ
          ≈⟨ ≑-cong (≑-cong ≋.refl (·-ᵀ (I ≑ 𝟎) (𝟎 ≑ I))) (·-ᵀ (𝟎 ≑ I) (𝟎 ≑ I)) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ (I {B} ≑ 𝟎 {B} {C}) ᵀ · (𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) ᵀ) ≑ (𝟎 {C} {B} ≑ I {C}) ᵀ · (𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) ᵀ
          ≡⟨ ≡.cong₂ _≑_ (≡.cong₂ (λ h₁ h₂ → I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ h₁ · h₂) (≑-ᵀ I 𝟎) (≑-ᵀ 𝟎 I)) (≡.cong₂ _·_ (≑-ᵀ 𝟎 I) (≑-ᵀ 𝟎 I)) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ (I {B} ᵀ ∥ 𝟎 {B} {C} ᵀ) · (𝟎 {B ℕ.+ C} {A} ᵀ ∥ I {B ℕ.+ C} ᵀ)) ≑ (𝟎 {C} {B} ᵀ ∥ I {C} ᵀ) · (𝟎 {B ℕ.+ C} {A} ᵀ ∥ I {B ℕ.+ C} ᵀ)
          ≡⟨ ≡.cong₂ _≑_ (≡.cong₂ (λ h₁ h₂ → I {A} ∥ 𝟎 ≑ h₁ · h₂) (≡.cong₂ _∥_ Iᵀ′ 𝟎ᵀ) (≡.cong₂ _∥_ 𝟎ᵀ Iᵀ′)) (≡.cong₂ _·_ (≡.cong₂ _∥_ 𝟎ᵀ Iᵀ′) (≡.cong₂ _∥_ 𝟎ᵀ Iᵀ′)) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ (I {B} ∥ 𝟎 {C} {B}) · (𝟎 {A} {B ℕ.+ C} ∥ I {B ℕ.+ C})) ≑ (𝟎 {B} {C} ∥ I {C}) · (𝟎 {A} {B ℕ.+ C} ∥ I {B ℕ.+ C})
          ≡⟨ ≡.cong (λ h → (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ h) ≑ (𝟎 {B} {C} ∥ I {C}) · (𝟎 {A} {B ℕ.+ C} ∥ I {B ℕ.+ C})) (·-∥ (I ∥ 𝟎) 𝟎 I) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ (I {B} ∥ 𝟎 {C} {B}) · 𝟎 {A} {B ℕ.+ C} ∥ (I {B} ∥ 𝟎 {C} {B}) · I {B ℕ.+ C}) ≑ (𝟎 {B} {C} ∥ I {C}) · (𝟎 {A} {B ℕ.+ C} ∥ I {B ℕ.+ C})
          ≈⟨ ≑-cong (≑-cong ≋.refl (∥-cong (·-𝟎ʳ (I ∥ 𝟎)) ·-identityʳ)) ≋.refl ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ 𝟎 {A} {B} ∥ I {B} ∥ 𝟎 {C} {B}) ≑ (𝟎 {B} {C} ∥ I {C}) · (𝟎 {A} {B ℕ.+ C} ∥ I {B ℕ.+ C})
          ≡⟨ ≡.cong ((I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ 𝟎 {A} {B} ∥ I {B} ∥ 𝟎 {C} {B}) ≑_) (·-∥ (𝟎 ∥ I) 𝟎 I) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ 𝟎 {A} {B} ∥ I {B} ∥ 𝟎 {C} {B}) ≑ (𝟎 {B} {C} ∥ I {C}) · (𝟎 {A} {B ℕ.+ C}) ∥ (𝟎 {B} {C} ∥ I {C}) · I {B ℕ.+ C}
          ≈⟨ ≑-cong ≋.refl (∥-cong (·-𝟎ʳ (𝟎 ∥ I)) ·-identityʳ) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ 𝟎 {A} {B} ∥ I {B} ∥ 𝟎 {C} {B}) ≑ 𝟎 {A} {C} ∥ 𝟎 {B} {C} ∥ I {C}
          ≡⟨ ≡.cong (λ h → (I {A} ∥ h ≑ 𝟎 {A} {B} ∥ I {B} ∥ 𝟎 {C} {B}) ≑ 𝟎 {A} {C} ∥ 𝟎 {B} {C} ∥ I {C}) 𝟎∥𝟎 ⟨
      (I {A} ∥ 𝟎 {B} ∥ 𝟎 {C} ≑ 𝟎 {A} ∥ I {B} ∥ 𝟎 {C}) ≑ 𝟎 {A} ∥ 𝟎 {B} ∥ I {C}
          ≡⟨ ≑-sym-assoc (I {A} ∥ 𝟎 {B} ∥ 𝟎 {C}) (𝟎 {A} ∥ I {B} ∥ 𝟎 {C}) (𝟎 {A} ∥ 𝟎 {B} ∥ I {C}) ⟨
      cast₂ _ (I {A} ∥ 𝟎 {B} ∥ 𝟎 {C} ≑ 𝟎 {A} ∥ I {B} ∥ 𝟎 {C} ≑ 𝟎 {A} ∥ 𝟎 {B} ∥ I {C})
          ≡⟨ ≡.cong (cast₂ _) (∥-≑⁴ I 𝟎 𝟎 𝟎 I 𝟎 𝟎 𝟎 I) ⟩
      cast₂ (≡.sym assoc) ((I {A} ≑ 𝟎 {A} {B} ≑ (𝟎 {A} {C})) ∥ (𝟎 {B} {A} ≑ I {B} ≑ 𝟎 {B} {C}) ∥ ((𝟎 {C} {A} ≑ 𝟎 {C} {B} ≑ I {C})))
          ≡⟨ cast₂-∥ (≡.sym assoc) ((I {A} ≑ 𝟎 {A} {B} ≑ (𝟎 {A} {C}))) ((𝟎 {B} {A} ≑ I {B} ≑ 𝟎 {B} {C}) ∥ ((𝟎 {C} {A} ≑ 𝟎 {C} {B} ≑ I {C})))  ⟨
      (cast₂ (≡.sym assoc) (I {A} ≑ 𝟎 {A} {B} ≑ (𝟎 {A} {C}))) ∥ cast₂ (≡.sym assoc) ((𝟎 {B} {A} ≑ I {B} ≑ 𝟎 {B} {C}) ∥ ((𝟎 {C} {A} ≑ 𝟎 {C} {B} ≑ I {C})))
          ≡⟨ ≡.cong (cast₂ (≡.sym assoc) (I {A} ≑ 𝟎 {A} {B} ≑ (𝟎 {A} {C})) ∥_) (cast₂-∥ (≡.sym assoc) (𝟎 {B} {A} ≑ I {B} ≑ 𝟎 {B} {C}) (𝟎 {C} {A} ≑ 𝟎 {C} {B} ≑ I {C})) ⟨
      cast₂ (≡.sym assoc) (I {A} ≑ 𝟎 {A} {B} ≑ (𝟎 {A} {C})) ∥ cast₂ (≡.sym assoc) (𝟎 {B} {A} ≑ I {B} ≑ 𝟎 {B} {C}) ∥ cast₂ (≡.sym assoc) (𝟎 {C} {A} ≑ 𝟎 {C} {B} ≑ I {C})
          ≡⟨ ≡.cong₂ _∥_ (≑-sym-assoc I 𝟎 𝟎) (≡.cong₂ _∥_ (≑-sym-assoc 𝟎 I 𝟎) (≑-sym-assoc 𝟎 𝟎 I)) ⟩
      ((I {A} ≑ 𝟎 {A} {B}) ≑ (𝟎 {A} {C})) ∥ ((𝟎 {B} {A} ≑ I {B}) ≑ 𝟎 {B} {C}) ∥ ((𝟎 {C} {A} ≑ 𝟎 {C} {B}) ≑ I {C})
          ≡⟨ ≡.cong (λ h → ((I {A} ≑ 𝟎 {A} {B}) ≑ (𝟎 {A} {C})) ∥ ((𝟎 {B} {A} ≑ I {B}) ≑ 𝟎 {B} {C}) ∥ (h ≑ I {C})) 𝟎≑𝟎 ⟩
      ((I {A} ≑ 𝟎 {A} {B}) ≑ (𝟎 {A} {C})) ∥ ((𝟎 {B} {A} ≑ I {B}) ≑ 𝟎 {B} {C}) ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C})
          ≈⟨ ∥-cong ≋.refl (∥-cong (≑-cong ·-identityˡ (·-𝟎ˡ (𝟎 ≑ I))) ≋.refl) ⟨
      ((I {A} ≑ 𝟎 {A} {B}) ≑ (𝟎 {A} {C})) ∥ (((I {A ℕ.+ B} · (𝟎 {B} {A} ≑ I {B})) ≑ (𝟎 {A ℕ.+ B} {C} · (𝟎 {B} {A} ≑ I {B})))) ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C})
          ≡⟨ ≡.cong (λ h → ((I {A} ≑ 𝟎 {A} {B}) ≑ (𝟎 {A} {C})) ∥ h ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C})) (≑-· I 𝟎 (𝟎 ≑ I)) ⟨
      ((I {A} ≑ 𝟎 {A} {B}) ≑ (𝟎 {A} {C})) ∥ ((I {A ℕ.+ B} ≑ 𝟎 {A ℕ.+ B} {C}) · (𝟎 {B} {A} ≑ I {B})) ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C})
          ≈⟨ ∥-cong (≑-cong ·-identityˡ (·-𝟎ˡ (I ≑ 𝟎))) ≋.refl ⟨
      ((I {A ℕ.+ B} · (I {A} ≑ 𝟎 {A} {B})) ≑ (𝟎 {A ℕ.+ B} {C} · (I {A} ≑ 𝟎 {A} {B}))) ∥ ((I {A ℕ.+ B} ≑ 𝟎 {A ℕ.+ B} {C}) · (𝟎 {B} {A} ≑ I {B})) ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C})
          ≡⟨ ≡.cong (λ h → h ∥ ((I {A ℕ.+ B} ≑ 𝟎 {A ℕ.+ B} {C}) · (𝟎 {B} {A} ≑ I {B})) ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C})) (≑-· I 𝟎 (I ≑ 𝟎)) ⟨
      (I {A ℕ.+ B} ≑ 𝟎 {A ℕ.+ B} {C}) · (I {A} ≑ 𝟎 {A} {B}) ∥ ((I {A ℕ.+ B} ≑ 𝟎 {A ℕ.+ B} {C}) · (𝟎 {B} {A} ≑ I {B})) ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C}) ∎
    where
      assoc : A ℕ.+ B ℕ.+ C ≡ A ℕ.+ (B ℕ.+ C)
      assoc = ℕ-Props.+-assoc A B C
      Iᵀ′ : {A : ℕ} → I ᵀ ≡ I {A}
      Iᵀ′ = transpose-I
      open ≈-Reasoning (≋-setoid _ _)

opaque
  unfolding ≋-setoid
  ≋σᵀ : ((𝟎 ≑ I {A}) ∥ (I {B} ≑ 𝟎)) ᵀ ≋ (𝟎 ≑ I {B}) ∥ (I {A} ≑ 𝟎)
  ≋σᵀ {A} {B} = begin
      ((𝟎 ≑ I) ∥ (I ≑ 𝟎)) ᵀ       ≡⟨ ∥-ᵀ (𝟎 ≑ I) (I ≑ 𝟎) ⟩
      (𝟎 ≑ I {A}) ᵀ ≑ (I ≑ 𝟎) ᵀ   ≡⟨ ≡.cong₂ _≑_ (≑-ᵀ 𝟎 I) (≑-ᵀ I 𝟎) ⟩
      𝟎 ᵀ ∥ (I {A}) ᵀ ≑ I ᵀ ∥ 𝟎 ᵀ ≡⟨ ≡.cong₂ _≑_ (≡.cong₂ _∥_ 𝟎ᵀ transpose-I) (≡.cong₂ _∥_ transpose-I 𝟎ᵀ) ⟩
      𝟎 ∥ I {A} ≑ I ∥ 𝟎           ≡⟨ ∥-≑ 𝟎 I I 𝟎 ⟩
      (𝟎 ≑ I {B}) ∥ (I ≑ 𝟎)       ∎
    where
      open ≈-Reasoning (≋-setoid _ _)

opaque
  unfolding ≋-setoid
  ≋⊗  : (M : Matrix A B)
        (N : Matrix C D)
      → (I ≑ 𝟎) · M ∥ (𝟎 ≑ I) · N
      ≋ (M ≑ 𝟎) ∥ (𝟎 ≑ N)
  ≋⊗ M N = begin
      (I ≑ 𝟎) · M ∥ (𝟎 ≑ I) · N         ≡⟨ ≡.cong₂ _∥_ (≑-· I 𝟎 M) (≑-· 𝟎 I N)  ⟩
      (I · M ≑ 𝟎 · M) ∥ (𝟎 · N ≑ I · N) ≈⟨ ∥-cong (≑-cong ·-identityˡ (·-𝟎ˡ M)) (≑-cong (·-𝟎ˡ N) ·-identityˡ) ⟩
      (M ≑ 𝟎) ∥ (𝟎 ≑ N)                 ∎
    where
      open ≈-Reasoning (≋-setoid _ _)

opaque
  unfolding ≋-setoid
  ᵀ-resp-⊗
      : {M : Matrix A B}
        {N : Matrix C D}
      → ((I ≑ 𝟎) · M ∥ (𝟎 ≑ I) · N) ᵀ
      ≋ (I ≑ 𝟎) · M ᵀ ∥ (𝟎 ≑ I) · N ᵀ
  ᵀ-resp-⊗ {M = M} {N = N} = begin
      ((I ≑ 𝟎) · M ∥ (𝟎 ≑ I) · N) ᵀ ≈⟨ ᵀ-cong (≋⊗ M N) ⟩
      ((M ≑ 𝟎) ∥ (𝟎 ≑ N)) ᵀ         ≡⟨ ≡.cong (_ᵀ) (∥-≑ M 𝟎 𝟎 N) ⟨
      ((M ∥ 𝟎) ≑ (𝟎 ∥ N)) ᵀ         ≡⟨ ≑-ᵀ (M ∥ 𝟎) (𝟎 ∥ N) ⟩
      (M ∥ 𝟎) ᵀ ∥ (𝟎 ∥ N) ᵀ         ≡⟨ ≡.cong₂ _∥_ (∥-ᵀ M 𝟎) (∥-ᵀ 𝟎 N) ⟩
      (M ᵀ ≑ 𝟎 ᵀ) ∥ (𝟎 ᵀ ≑ N ᵀ)     ≡⟨ ≡.cong₂ (λ h₁ h₂ → (M ᵀ ≑ h₁) ∥ (h₂ ≑ N ᵀ)) 𝟎ᵀ 𝟎ᵀ ⟩
      (M ᵀ ≑ 𝟎) ∥ (𝟎 ≑ N ᵀ)         ≈⟨ ≋⊗ (M ᵀ) (N ᵀ) ⟨
      (I ≑ 𝟎) · M ᵀ ∥ (𝟎 ≑ I) · N ᵀ ∎
    where
      open ≈-Reasoning (≋-setoid _ _)

Mat-DaggerCocartesian : DaggerCocartesianMonoidal
Mat-DaggerCocartesian = record
    { cocartesian = Mat-Cocartesian
    ; dagger = record
        { _† = λ M → M ᵀ
        ; †-identity = Iᵀ
        ; †-homomorphism = λ {f = f} {g} → ·-ᵀ f g
        ; †-resp-≈ = ᵀ-cong
        ; †-involutive = ᵀ-involutive
        }
    ; λ≅† = ≋λᵀ
    ; ρ≅† = ≋ρᵀ
    ; α≅† = ≋αᵀ
    ; σ≅† = ≋σᵀ
    ; †-resp-⊗ = ᵀ-resp-⊗
    }
