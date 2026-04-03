{-# OPTIONS --without-K --safe #-}

open import Algebra using (Idempotent; CommutativeSemiring)
open import Level using (Level)

module Data.Matrix.Dagger-2-Poset
    {c ℓ : Level}
    (R : CommutativeSemiring c ℓ)
    (let module R = CommutativeSemiring R)
    (+-idem : Idempotent R._≈_ R._+_)
  where

import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Category.Dagger.2-Poset using (dagger-2-poset; Dagger-2-Poset)
open import Category.Dagger.Semiadditive using (IdempotentSemiadditiveDagger)
open import Data.Matrix.Category R.semiring using (Mat; _·_; ·-Iˡ; ·-Iʳ; ·-resp-≋; ·-assoc; ∥-·-≑; ·-∥; ·-𝟎ˡ; ≑-·)
open import Data.Matrix.Core R.setoid using (Matrix; Matrixₛ; _≋_; _∥_; _≑_; _ᵀ; module ≋; ∥-cong; ≑-cong)
open import Data.Matrix.Monoid R.+-monoid using (𝟎; _[+]_; [+]-cong; [+]-𝟎ˡ; [+]-𝟎ʳ)
open import Data.Matrix.Transform R.semiring using (I; Iᵀ)
open import Data.Matrix.SemiadditiveDagger R using (∥-ᵀ; Mat-SemiadditiveDagger)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Data.Vector.Core R.setoid using (Vector; _≊_)
open import Data.Vector.Monoid R.+-monoid using (_⊕_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Vec

private
  variable
    A B : ℕ

opaque
  unfolding _≊_ _⊕_
  ⊕-idem : (V : Vector A) → V ⊕ V ≊ V
  ⊕-idem [] = PW.[]
  ⊕-idem (v ∷ V) = +-idem v PW.∷ ⊕-idem V

opaque
  unfolding _≋_ _[+]_
  [+]-idem : (M : Matrix A B) → M [+] M ≋ M
  [+]-idem [] = PW.[]
  [+]-idem (M₀ ∷ M) = ⊕-idem M₀ PW.∷ [+]-idem M

idem : (M : Matrix A B) → (I ∥ I) · (((I ≑ 𝟎) · M) ∥ ((𝟎 ≑ I) · M)) · (I ∥ I) ᵀ ≋ M
idem M = begin
    (I ∥ I) · (((I ≑ 𝟎) · M) ∥ ((𝟎 ≑ I) · M)) · (I ∥ I) ᵀ     ≡⟨ ≡.cong₂ (λ h₁ h₂ → (I ∥ I) · (h₁ ∥ h₂) · (I ∥ I) ᵀ) (≑-· I 𝟎 M) (≑-· 𝟎 I M) ⟩
    (I ∥ I) · ((I · M ≑ 𝟎 · M) ∥ (𝟎 · M ≑ I · M)) · (I ∥ I) ᵀ ≈⟨ ·-resp-≋ ≋.refl (·-resp-≋ (∥-cong (≑-cong ·-Iˡ (·-𝟎ˡ M)) (≑-cong (·-𝟎ˡ M) ·-Iˡ)) ≋.refl) ⟩
    (I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M)) · (I ∥ I) ᵀ                 ≡⟨ ≡.cong (λ h → (I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M)) · h) (∥-ᵀ I I) ⟩
    (I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M)) · (I ᵀ ≑ I ᵀ)               ≡⟨ ≡.cong₂ (λ h₁ h₂ → (I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M)) · (h₁ ≑ h₂)) Iᵀ Iᵀ ⟩
    (I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M)) · (I ≑ I)                   ≈⟨ ·-assoc ⟨
    ((I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M))) · (I ≑ I)                 ≡⟨ ≡.cong (_· (I ≑ I)) (·-∥ (I ∥ I) (M ≑ 𝟎) (𝟎 ≑ M)) ⟩
    (((I ∥ I) · (M ≑ 𝟎)) ∥ ((I ∥ I) · (𝟎 ≑ M))) · (I ≑ I)     ≈⟨ ∥-·-≑ ((I ∥ I) · (M ≑ 𝟎)) ((I ∥ I) · (𝟎 ≑ M)) I I ⟩
    (((I ∥ I) · (M ≑ 𝟎)) · I) [+] (((I ∥ I) · (𝟎 ≑ M)) · I)   ≈⟨ [+]-cong ·-Iʳ ·-Iʳ ⟩
    ((I ∥ I) · (M ≑ 𝟎)) [+] ((I ∥ I) · (𝟎 ≑ M))               ≈⟨ [+]-cong (∥-·-≑ I I M 𝟎) (∥-·-≑ I I 𝟎 M) ⟩
    ((I · M) [+] (I · 𝟎)) [+] ((I · 𝟎) [+] (I · M))           ≈⟨ [+]-cong ([+]-cong ·-Iˡ ·-Iˡ) ([+]-cong ·-Iˡ ·-Iˡ) ⟩
    (M [+] 𝟎) [+] (𝟎 [+] M)                                   ≈⟨ [+]-cong ([+]-𝟎ʳ M) ([+]-𝟎ˡ M) ⟩
    M [+] M                                                   ≈⟨ [+]-idem M ⟩
    M ∎
  where
    open ≈-Reasoning (Matrixₛ _ _)

Mat-IdempotentSemiadditiveDagger : IdempotentSemiadditiveDagger Mat
Mat-IdempotentSemiadditiveDagger = record
    { semiadditiveDagger = Mat-SemiadditiveDagger
    ; idempotent = idem _
    }

Mat-Dagger-2-Poset : Dagger-2-Poset
Mat-Dagger-2-Poset = dagger-2-poset Mat-IdempotentSemiadditiveDagger
