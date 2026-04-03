{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeSemiring)
open import Level using (Level)

module Data.Matrix.SemiadditiveDagger {c ℓ : Level} (R : CommutativeSemiring c ℓ) where

module R = CommutativeSemiring R

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Data.Nat.Properties as ℕ-Props
import Data.Nat as ℕ

open import Categories.Category.Cocartesian using (Cocartesian)
open import Categories.Object.Coproduct using (Coproduct)
open import Categories.Object.Initial using (Initial)
open import Category.Dagger.Semiadditive using (DaggerCocartesianMonoidal; SemiadditiveDagger)
open import Data.Matrix.Cast R.setoid using (cast₂; cast₂-∥; ∥-≑; ∥-≑⁴; ≑-sym-assoc)
open import Data.Matrix.Category R.semiring using (Mat; _·_; ≑-·; ·-Iˡ; ·-Iʳ; ·-𝟎ˡ; ·-𝟎ʳ; ·-∥; ∥-·-≑)
open import Data.Matrix.Core R.setoid using (Matrix; Matrixₛ; _ᵀ; _ᵀᵀ; _≋_; module ≋; mapRows; []ᵥ; []ᵥ-∥; []ₕ; []ₕ-!; []ₕ-≑; _∷ᵥ_; _∷ₕ_; ∷ᵥ-ᵀ; _∥_; _≑_; ∷ₕ-ᵀ; ∷ₕ-≑; []ᵥ-ᵀ; ∥-cong; ≑-cong; -ᵀ-cong; head-∷-tailₕ; headₕ; tailₕ; ∷ₕ-∥; []ᵥ-!)
open import Data.Matrix.Monoid R.+-monoid using (𝟎; 𝟎ᵀ; 𝟎≑𝟎; 𝟎∥𝟎; _[+]_; [+]-cong; [+]-𝟎ˡ; [+]-𝟎ʳ)
open import Data.Matrix.Transform R.semiring using (I; Iᵀ; [_]_; _[_]; -[-]ᵀ; [-]--cong; [-]-[]ᵥ; [⟨⟩]-[]ₕ)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Vec using (Vec; map; replicate)
open import Data.Vec.Properties using (map-cong; map-const)
open import Data.Vector.Bisemimodule R.semiring using (_∙_ ; ∙-cong)
open import Data.Vector.Core R.setoid using (Vector; Vectorₛ; ⟨⟩; _++_; module ≊; _≊_)
open import Data.Vector.Monoid R.+-monoid using () renaming (⟨ε⟩ to ⟨0⟩)
open import Data.Vector.Vec using (replicate-++)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open R
open Vec
open ℕ.ℕ

private
  variable
    A B C D E F : ℕ

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
      open ≈-Reasoning (Vectorₛ _)

opaque
  unfolding []ᵥ mapRows ⟨⟩ _∷ₕ_ _∷ᵥ_ _ᵀ
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
      open ≈-Reasoning (Matrixₛ 0 A)
  ·-ᵀ {A} {B} {suc C} M (N₀ ∷ N) = begin
      map ([_] M) (N₀ ∷ N) ᵀ        ≡⟨ -[-]ᵀ (N₀ ∷ N) M ⟨
      map ((N₀ ∷ N) [_]) (M ᵀ)      ≈⟨ PW.map⁺ (λ {V} ≋V → ≊.trans ([-]-ᵀ (N₀ ∷ N) V) ([-]--cong {A = (N₀ ∷ᵥ N) ᵀ} ≋V ≋.refl)) ≋.refl ⟩
      map ([_] ((N₀ ∷ N) ᵀ)) (M ᵀ)  ≡⟨ map-cong (λ V → ≡.cong ([ V ]_) (∷ᵥ-ᵀ N₀ N)) (M ᵀ) ⟩
      map ([_] (N₀ ∷ₕ N ᵀ)) (M ᵀ)   ∎
    where
      open ≈-Reasoning (Matrixₛ (suc C) A)

opaque
  unfolding _≋_
  ᵀ-involutive : (M : Matrix A B) → (M ᵀ) ᵀ ≋ M
  ᵀ-involutive M = ≋.reflexive (M ᵀᵀ)

opaque
  unfolding _≋_
  ≋λᵀ : ([]ᵥ ∥ I) ᵀ ≋ 𝟎 ≑ I {A}
  ≋λᵀ = begin
      ([]ᵥ ∥ I) ᵀ ≡⟨ ≡.cong (_ᵀ) ([]ᵥ-∥ I) ⟩
      I ᵀ         ≡⟨ Iᵀ ⟩
      I           ≡⟨ []ₕ-≑ I ⟨
      []ₕ ≑ I     ≡⟨ ≡.cong (_≑ I) ([]ₕ-! 𝟎) ⟨
      𝟎 ≑ I       ∎
    where
      open ≈-Reasoning (Matrixₛ _ _)

opaque
  unfolding Matrix _∥_ _ᵀ _≑_ _∷ₕ_
  ∥-ᵀ : (M : Matrix A C) (N : Matrix B C) → (M ∥ N) ᵀ ≡ M ᵀ ≑ N ᵀ
  ∥-ᵀ {A} {zero} {B} [] [] = ≡.sym (replicate-++ A B [])
  ∥-ᵀ (M₀ ∷ M) (N₀ ∷ N) = begin
      (M₀ ++ N₀) ∷ₕ ((M ∥ N) ᵀ) ≡⟨ ≡.cong ((M₀ ++ N₀) ∷ₕ_) (∥-ᵀ M N) ⟩
      (M₀ ++ N₀) ∷ₕ (M ᵀ ≑ N ᵀ) ≡⟨ ∷ₕ-≑ M₀ N₀ (M ᵀ) (N ᵀ) ⟩
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
      I ᵀ ≑ []ₕ   ≡⟨ ≡.cong (_≑ []ₕ) Iᵀ ⟩
      I  ≑ []ₕ    ≡⟨ ≡.cong (I ≑_) ([]ₕ-! 𝟎) ⟨
      I ≑ 𝟎       ∎
    where
      open ≈-Reasoning (Matrixₛ _ _)

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
          ≡⟨ ≡.cong (λ h → (h ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎 {B} {C})) ᵀ) ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (𝟎 {C} {B} ≑ I {C})) ᵀ) (≡.cong₂ _∥_ Iᵀ 𝟎ᵀ) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (I {B} ≑ 𝟎 {B} {C})) ᵀ) ≑ ((𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) · (𝟎 {C} {B} ≑ I {C})) ᵀ
          ≈⟨ ≑-cong (≑-cong ≋.refl (·-ᵀ (I ≑ 𝟎) (𝟎 ≑ I))) (·-ᵀ (𝟎 ≑ I) (𝟎 ≑ I)) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ (I {B} ≑ 𝟎 {B} {C}) ᵀ · (𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) ᵀ) ≑ (𝟎 {C} {B} ≑ I {C}) ᵀ · (𝟎 {B ℕ.+ C} {A} ≑ I {B ℕ.+ C}) ᵀ
          ≡⟨ ≡.cong₂ _≑_ (≡.cong₂ (λ h₁ h₂ → I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ h₁ · h₂) (≑-ᵀ I 𝟎) (≑-ᵀ 𝟎 I)) (≡.cong₂ _·_ (≑-ᵀ 𝟎 I) (≑-ᵀ 𝟎 I)) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ (I {B} ᵀ ∥ 𝟎 {B} {C} ᵀ) · (𝟎 {B ℕ.+ C} {A} ᵀ ∥ I {B ℕ.+ C} ᵀ)) ≑ (𝟎 {C} {B} ᵀ ∥ I {C} ᵀ) · (𝟎 {B ℕ.+ C} {A} ᵀ ∥ I {B ℕ.+ C} ᵀ)
          ≡⟨ ≡.cong₂ _≑_ (≡.cong₂ (λ h₁ h₂ → I {A} ∥ 𝟎 ≑ h₁ · h₂) (≡.cong₂ _∥_ Iᵀ 𝟎ᵀ) (≡.cong₂ _∥_ 𝟎ᵀ Iᵀ)) (≡.cong₂ _·_ (≡.cong₂ _∥_ 𝟎ᵀ Iᵀ) (≡.cong₂ _∥_ 𝟎ᵀ Iᵀ)) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ (I {B} ∥ 𝟎 {C} {B}) · (𝟎 {A} {B ℕ.+ C} ∥ I {B ℕ.+ C})) ≑ (𝟎 {B} {C} ∥ I {C}) · (𝟎 {A} {B ℕ.+ C} ∥ I {B ℕ.+ C})
          ≡⟨ ≡.cong (λ h → (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ h) ≑ (𝟎 {B} {C} ∥ I {C}) · (𝟎 {A} {B ℕ.+ C} ∥ I {B ℕ.+ C})) (·-∥ (I ∥ 𝟎) 𝟎 I) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ (I {B} ∥ 𝟎 {C} {B}) · 𝟎 {A} {B ℕ.+ C} ∥ (I {B} ∥ 𝟎 {C} {B}) · I {B ℕ.+ C}) ≑ (𝟎 {B} {C} ∥ I {C}) · (𝟎 {A} {B ℕ.+ C} ∥ I {B ℕ.+ C})
          ≈⟨ ≑-cong (≑-cong ≋.refl (∥-cong (·-𝟎ʳ (I ∥ 𝟎)) ·-Iʳ)) (≋.refl {x = (𝟎 {B} {C} ∥ I {C}) · (𝟎 {A} {B ℕ.+ C} ∥ I {B ℕ.+ C})}) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ 𝟎 {A} {B} ∥ I {B} ∥ 𝟎 {C} {B}) ≑ (𝟎 {B} {C} ∥ I {C}) · (𝟎 {A} {B ℕ.+ C} ∥ I {B ℕ.+ C})
          ≡⟨ ≡.cong ((I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ 𝟎 {A} {B} ∥ I {B} ∥ 𝟎 {C} {B}) ≑_) (·-∥ (𝟎 ∥ I) 𝟎 I) ⟩
      (I {A} ∥ 𝟎 {B ℕ.+ C} {A} ≑ 𝟎 {A} {B} ∥ I {B} ∥ 𝟎 {C} {B}) ≑ (𝟎 {B} {C} ∥ I {C}) · (𝟎 {A} {B ℕ.+ C}) ∥ (𝟎 {B} {C} ∥ I {C}) · I {B ℕ.+ C}
          ≈⟨ ≑-cong ≋.refl (∥-cong (·-𝟎ʳ (𝟎 ∥ I)) ·-Iʳ) ⟩
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
          ≈⟨ ∥-cong ≋.refl (∥-cong (≑-cong ·-Iˡ (·-𝟎ˡ (𝟎 ≑ I))) ≋.refl) ⟨
      ((I {A} ≑ 𝟎 {A} {B}) ≑ (𝟎 {A} {C})) ∥ (((I {A ℕ.+ B} · (𝟎 {B} {A} ≑ I {B})) ≑ (𝟎 {A ℕ.+ B} {C} · (𝟎 {B} {A} ≑ I {B})))) ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C})
          ≡⟨ ≡.cong (λ h → ((I {A} ≑ 𝟎 {A} {B}) ≑ (𝟎 {A} {C})) ∥ h ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C})) (≑-· I 𝟎 (𝟎 ≑ I)) ⟨
      ((I {A} ≑ 𝟎 {A} {B}) ≑ (𝟎 {A} {C})) ∥ ((I {A ℕ.+ B} ≑ 𝟎 {A ℕ.+ B} {C}) · (𝟎 {B} {A} ≑ I {B})) ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C})
          ≈⟨ ∥-cong (≑-cong ·-Iˡ (·-𝟎ˡ (I ≑ 𝟎))) ≋.refl ⟨
      ((I {A ℕ.+ B} · (I {A} ≑ 𝟎 {A} {B})) ≑ (𝟎 {A ℕ.+ B} {C} · (I {A} ≑ 𝟎 {A} {B}))) ∥ ((I {A ℕ.+ B} ≑ 𝟎 {A ℕ.+ B} {C}) · (𝟎 {B} {A} ≑ I {B})) ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C})
          ≡⟨ ≡.cong (λ h → h ∥ ((I {A ℕ.+ B} ≑ 𝟎 {A ℕ.+ B} {C}) · (𝟎 {B} {A} ≑ I {B})) ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C})) (≑-· I 𝟎 (I ≑ 𝟎)) ⟨
      (I {A ℕ.+ B} ≑ 𝟎 {A ℕ.+ B} {C}) · (I {A} ≑ 𝟎 {A} {B}) ∥ ((I {A ℕ.+ B} ≑ 𝟎 {A ℕ.+ B} {C}) · (𝟎 {B} {A} ≑ I {B})) ∥ (𝟎 {C} {A ℕ.+ B} ≑ I {C}) ∎
    where
      assoc : A ℕ.+ B ℕ.+ C ≡ A ℕ.+ (B ℕ.+ C)
      assoc = ℕ-Props.+-assoc A B C
      open ≈-Reasoning (Matrixₛ _ _)

≋σᵀ : ((𝟎 ≑ I {A}) ∥ (I {B} ≑ 𝟎)) ᵀ ≋ (𝟎 ≑ I {B}) ∥ (I {A} ≑ 𝟎)
≋σᵀ {A} {B} = begin
    ((𝟎 ≑ I) ∥ (I ≑ 𝟎)) ᵀ       ≡⟨ ∥-ᵀ (𝟎 ≑ I) (I ≑ 𝟎) ⟩
    (𝟎 ≑ I {A}) ᵀ ≑ (I ≑ 𝟎) ᵀ   ≡⟨ ≡.cong₂ _≑_ (≑-ᵀ 𝟎 I) (≑-ᵀ I 𝟎) ⟩
    𝟎 ᵀ ∥ (I {A}) ᵀ ≑ I ᵀ ∥ 𝟎 ᵀ ≡⟨ ≡.cong₂ _≑_ (≡.cong₂ _∥_ 𝟎ᵀ Iᵀ) (≡.cong₂ _∥_ Iᵀ 𝟎ᵀ) ⟩
    𝟎 ∥ I {A} ≑ I ∥ 𝟎           ≡⟨ ∥-≑ 𝟎 I I 𝟎 ⟩
    (𝟎 ≑ I {B}) ∥ (I ≑ 𝟎)       ∎
  where
    open ≈-Reasoning (Matrixₛ _ _)

≋⊗  : (M : Matrix A B)
      (N : Matrix C D)
    → (I ≑ 𝟎) · M ∥ (𝟎 ≑ I) · N
    ≋ (M ≑ 𝟎) ∥ (𝟎 ≑ N)
≋⊗ M N = begin
    (I ≑ 𝟎) · M ∥ (𝟎 ≑ I) · N         ≡⟨ ≡.cong₂ _∥_ (≑-· I 𝟎 M) (≑-· 𝟎 I N)  ⟩
    (I · M ≑ 𝟎 · M) ∥ (𝟎 · N ≑ I · N) ≈⟨ ∥-cong (≑-cong ·-Iˡ (·-𝟎ˡ M)) (≑-cong (·-𝟎ˡ N) ·-Iˡ) ⟩
    (M ≑ 𝟎) ∥ (𝟎 ≑ N)                 ∎
  where
    open ≈-Reasoning (Matrixₛ _ _)

ᵀ-resp-⊗
    : {M : Matrix A B}
      {N : Matrix C D}
    → ((I ≑ 𝟎) · M ∥ (𝟎 ≑ I) · N) ᵀ
    ≋ (I ≑ 𝟎) · M ᵀ ∥ (𝟎 ≑ I) · N ᵀ
ᵀ-resp-⊗ {M = M} {N = N} = begin
    ((I ≑ 𝟎) · M ∥ (𝟎 ≑ I) · N) ᵀ ≈⟨ -ᵀ-cong (≋⊗ M N) ⟩
    ((M ≑ 𝟎) ∥ (𝟎 ≑ N)) ᵀ         ≡⟨ ≡.cong (_ᵀ) (∥-≑ M 𝟎 𝟎 N) ⟨
    ((M ∥ 𝟎) ≑ (𝟎 ∥ N)) ᵀ         ≡⟨ ≑-ᵀ (M ∥ 𝟎) (𝟎 ∥ N) ⟩
    (M ∥ 𝟎) ᵀ ∥ (𝟎 ∥ N) ᵀ         ≡⟨ ≡.cong₂ _∥_ (∥-ᵀ M 𝟎) (∥-ᵀ 𝟎 N) ⟩
    (M ᵀ ≑ 𝟎 ᵀ) ∥ (𝟎 ᵀ ≑ N ᵀ)     ≡⟨ ≡.cong₂ (λ h₁ h₂ → (M ᵀ ≑ h₁) ∥ (h₂ ≑ N ᵀ)) 𝟎ᵀ 𝟎ᵀ ⟩
    (M ᵀ ≑ 𝟎) ∥ (𝟎 ≑ N ᵀ)         ≈⟨ ≋⊗ (M ᵀ) (N ᵀ) ⟨
    (I ≑ 𝟎) · M ᵀ ∥ (𝟎 ≑ I) · N ᵀ ∎
  where
    open ≈-Reasoning (Matrixₛ _ _)

inj₁ : (M : Matrix A C) (N : Matrix B C) → (M ∥ N) · (I ≑ 𝟎) ≋ M
inj₁ {A} {C} M N = begin
    (M ∥ N) · (I ≑ 𝟎)   ≈⟨ ∥-·-≑ M N I 𝟎 ⟩
    (M · I) [+] (N · 𝟎) ≈⟨ [+]-cong ·-Iʳ (·-𝟎ʳ N) ⟩
    M [+] 𝟎             ≈⟨ [+]-𝟎ʳ M ⟩
    M ∎
  where
    open ≈-Reasoning (Matrixₛ A C)

inj₂ : (M : Matrix A C) (N : Matrix B C) → (M ∥ N) · (𝟎 ≑ I) ≋ N
inj₂ {A} {C} {B} M N = begin
    (M ∥ N) · (𝟎 ≑ I)   ≈⟨ ∥-·-≑ M N 𝟎 I ⟩
    (M · 𝟎) [+] (N · I) ≈⟨ [+]-cong (·-𝟎ʳ M) ·-Iʳ ⟩
    𝟎 [+] N             ≈⟨ [+]-𝟎ˡ N ⟩
    N ∎
  where
    open ≈-Reasoning (Matrixₛ B C)

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
    open ≈-Reasoning (Matrixₛ (A ℕ.+ B) C)

coproduct : Coproduct Mat A B
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

initial : Initial Mat
initial = record
    { ⊥ = 0
    ; ⊥-is-initial = record
        { ! = []ᵥ
        ; !-unique = !-unique
        }
    }

Mat-Cocartesian : Cocartesian Mat
Mat-Cocartesian = record
    { initial = initial
    ; coproducts = record
        { coproduct = coproduct
        }
    }

Mat-DaggerCocartesian : DaggerCocartesianMonoidal Mat
Mat-DaggerCocartesian = record
    { cocartesian = Mat-Cocartesian
    ; dagger = record
        { _† = λ M → M ᵀ
        ; †-identity = ≋.reflexive Iᵀ
        ; †-homomorphism = λ {f = f} {g} → ·-ᵀ f g
        ; †-resp-≈ = -ᵀ-cong
        ; †-involutive = ᵀ-involutive
        }
    ; λ≅† = ≋λᵀ
    ; ρ≅† = ≋ρᵀ
    ; α≅† = ≋αᵀ
    ; σ≅† = ≋σᵀ
    ; †-resp-⊗ = ᵀ-resp-⊗
    }

p₁-i₁ : (I ≑ 𝟎) ᵀ · (I ≑ 𝟎 {A} {B}) ≋ I
p₁-i₁ = begin
    (I ≑ 𝟎) ᵀ · (I ≑ 𝟎)   ≡⟨ ≡.cong (_· (I ≑ 𝟎)) (≑-ᵀ I 𝟎) ⟩
    (I ᵀ ∥ 𝟎 ᵀ) · (I ≑ 𝟎) ≡⟨ ≡.cong₂ (λ h₁ h₂ → (h₁ ∥ h₂) · (I ≑ 𝟎)) Iᵀ 𝟎ᵀ ⟩
    (I ∥ 𝟎) · (I ≑ 𝟎)     ≈⟨ ∥-·-≑ I 𝟎 I 𝟎 ⟩
    (I · I) [+] (𝟎 · 𝟎)   ≈⟨ [+]-cong ·-Iˡ (·-𝟎ˡ 𝟎) ⟩
    I [+] 𝟎               ≈⟨ [+]-𝟎ʳ I ⟩
    I                     ∎
  where
    open ≈-Reasoning (Matrixₛ _ _)

p₂-i₂ : (𝟎 {A} {B} ≑ I) ᵀ · (𝟎 ≑ I) ≋ I
p₂-i₂ = begin
    (𝟎 ≑ I) ᵀ · (𝟎 ≑ I)   ≡⟨ ≡.cong (_· (𝟎 ≑ I)) (≑-ᵀ 𝟎 I) ⟩
    (𝟎 ᵀ ∥ I ᵀ) · (𝟎 ≑ I) ≡⟨ ≡.cong₂ (λ h₁ h₂ → (h₁ ∥ h₂) · (𝟎 ≑ I)) 𝟎ᵀ Iᵀ ⟩
    (𝟎 ∥ I) · (𝟎 ≑ I)     ≈⟨ ∥-·-≑ 𝟎 I 𝟎 I ⟩
    (𝟎 · 𝟎) [+] (I · I)   ≈⟨ [+]-cong (·-𝟎ˡ 𝟎) ·-Iˡ ⟩
    𝟎 [+] I               ≈⟨ [+]-𝟎ˡ I ⟩
    I                     ∎
  where
    open ≈-Reasoning (Matrixₛ _ _)

opaque
  unfolding 𝟎 ⟨⟩
  []ᵥ·[]ₕ : []ᵥ · []ₕ ≡ 𝟎 {A} {B}
  []ᵥ·[]ₕ {A} {B} = begin
      map ([_] []ₕ) []ᵥ   ≡⟨ map-cong (λ { [] → [⟨⟩]-[]ₕ }) []ᵥ ⟩
      map (λ _ → ⟨0⟩) []ᵥ ≡⟨ map-const []ᵥ ⟨0⟩ ⟩
      𝟎                   ∎
    where
      open ≡-Reasoning

p₂-i₁ : (𝟎 {A} ≑ I) ᵀ · (I ≑ 𝟎 {B}) ≋ []ᵥ · []ᵥ ᵀ
p₂-i₁ = begin
    (𝟎 ≑ I) ᵀ · (I ≑ 𝟎)   ≡⟨ ≡.cong (_· (I ≑ 𝟎)) (≑-ᵀ 𝟎 I) ⟩
    (𝟎 ᵀ ∥ I ᵀ) · (I ≑ 𝟎) ≡⟨ ≡.cong₂ (λ h₁ h₂ → (h₁ ∥ h₂) · (I ≑ 𝟎)) 𝟎ᵀ Iᵀ ⟩
    (𝟎 ∥ I) · (I ≑ 𝟎)     ≈⟨ ∥-·-≑ 𝟎 I I 𝟎 ⟩
    (𝟎 · I) [+] (I · 𝟎)   ≈⟨ [+]-cong (·-𝟎ˡ I) (·-𝟎ʳ I) ⟩
    𝟎 [+] 𝟎               ≈⟨ [+]-𝟎ˡ 𝟎 ⟩
    𝟎                     ≡⟨ []ᵥ·[]ₕ ⟨
    []ᵥ · []ₕ             ≡⟨ ≡.cong ([]ᵥ ·_) []ᵥ-ᵀ ⟨
    []ᵥ · []ᵥ ᵀ           ∎
  where
    open ≈-Reasoning (Matrixₛ _ _)

p₁-i₂ : (I ≑ 𝟎 {A}) ᵀ · (𝟎 {B} ≑ I) ≋ []ᵥ · []ᵥ ᵀ
p₁-i₂ = begin
    (I ≑ 𝟎) ᵀ · (𝟎 ≑ I)   ≡⟨ ≡.cong (_· (𝟎 ≑ I)) (≑-ᵀ I 𝟎) ⟩
    (I ᵀ ∥ 𝟎 ᵀ) · (𝟎 ≑ I) ≡⟨ ≡.cong₂ (λ h₁ h₂ → (h₁ ∥ h₂) · (𝟎 ≑ I)) Iᵀ 𝟎ᵀ ⟩
    (I ∥ 𝟎) · (𝟎 ≑ I)     ≈⟨ ∥-·-≑ I 𝟎 𝟎 I ⟩
    (I · 𝟎) [+] (𝟎 · I)   ≈⟨ [+]-cong (·-𝟎ʳ I) (·-𝟎ˡ I) ⟩
    𝟎 [+] 𝟎               ≈⟨ [+]-𝟎ˡ 𝟎 ⟩
    𝟎                     ≡⟨ []ᵥ·[]ₕ ⟨
    []ᵥ · []ₕ             ≡⟨ ≡.cong ([]ᵥ ·_) []ᵥ-ᵀ ⟨
    []ᵥ · []ᵥ ᵀ           ∎
  where
    open ≈-Reasoning (Matrixₛ _ _)

Mat-SemiadditiveDagger : SemiadditiveDagger Mat
Mat-SemiadditiveDagger = record
    { daggerCocartesianMonoidal = Mat-DaggerCocartesian
    ; p₁-i₁ = p₁-i₁
    ; p₂-i₂ = p₂-i₂
    ; p₂-i₁ = p₂-i₁
    ; p₁-i₂ = p₁-i₂
    }
