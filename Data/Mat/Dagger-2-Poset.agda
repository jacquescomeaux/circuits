{-# OPTIONS --without-K --safe #-}

open import Algebra using (Idempotent; CommutativeSemiring)
open import Level using (Level)

module Data.Mat.Dagger-2-Poset
    {c ℓ : Level}
    (Rig : CommutativeSemiring c ℓ)
    (let module Rig = CommutativeSemiring Rig)
    (+-idem : Idempotent Rig._≈_ Rig._+_)
  where

import Data.Vec.Relation.Binary.Pointwise.Inductive as PW
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.Mat.Util using (transpose-cong; replicate-++)
open import Data.Mat.Category Rig.semiring
  using
    ( Mat; _ᵀ; transpose-I; I; _≋_; module ≋; _≊_; Matrix; Vector
    ; ≋-setoid; _·_; ·-identityˡ; ·-identityʳ; ·-resp-≋; ·-assoc; _⊕_
    )
open import Data.Mat.Cocartesian Rig.semiring
  using
    ( 𝟎 ; _∥_; _≑_; ∥-cong; ≑-cong; ≑-·; ·-𝟎ˡ; ·-∥; ∥-·-≑
    ; _[+]_; [+]-cong; [+]-𝟎ʳ; [+]-𝟎ˡ
    )
open import Data.Mat.SemiadditiveDagger Rig using (∥-ᵀ; Mat-SemiadditiveDagger)
open import Category.Dagger.Semiadditive Mat using (IdempotentSemiadditiveDagger)
open import Category.Dagger.2-Poset using (dagger-2-poset; Dagger-2-Poset)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
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

opaque
  unfolding ≋-setoid
  idem : (M : Matrix A B) → (I ∥ I) · (((I ≑ 𝟎) · M) ∥ ((𝟎 ≑ I) · M)) · (I ∥ I) ᵀ ≋ M
  idem M = begin
      (I ∥ I) · (((I ≑ 𝟎) · M) ∥ ((𝟎 ≑ I) · M)) · (I ∥ I) ᵀ     ≡⟨ ≡.cong₂ (λ h₁ h₂ → (I ∥ I) · (h₁ ∥ h₂) · (I ∥ I) ᵀ) (≑-· I 𝟎 M) (≑-· 𝟎 I M) ⟩
      (I ∥ I) · ((I · M ≑ 𝟎 · M) ∥ (𝟎 · M ≑ I · M)) · (I ∥ I) ᵀ ≈⟨ ·-resp-≋ ≋.refl (·-resp-≋ (∥-cong (≑-cong ·-identityˡ (·-𝟎ˡ M)) (≑-cong (·-𝟎ˡ M) ·-identityˡ)) ≋.refl) ⟩
      (I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M)) · (I ∥ I) ᵀ                 ≡⟨ ≡.cong (λ h → (I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M)) · h) (∥-ᵀ I I) ⟩
      (I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M)) · (I ᵀ ≑ I ᵀ)               ≡⟨ ≡.cong₂ (λ h₁ h₂ → (I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M)) · (h₁ ≑ h₂)) transpose-I transpose-I ⟩
      (I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M)) · (I ≑ I)                   ≈⟨ ·-assoc ⟨
      ((I ∥ I) · ((M ≑ 𝟎) ∥ (𝟎 ≑ M))) · (I ≑ I)                 ≡⟨ ≡.cong (_· (I ≑ I)) (·-∥ (I ∥ I) (M ≑ 𝟎) (𝟎 ≑ M)) ⟩
      (((I ∥ I) · (M ≑ 𝟎)) ∥ ((I ∥ I) · (𝟎 ≑ M))) · (I ≑ I)     ≈⟨ ∥-·-≑ ((I ∥ I) · (M ≑ 𝟎)) ((I ∥ I) · (𝟎 ≑ M)) I I ⟩
      (((I ∥ I) · (M ≑ 𝟎)) · I) [+] (((I ∥ I) · (𝟎 ≑ M)) · I)   ≈⟨ [+]-cong ·-identityʳ ·-identityʳ ⟩
      ((I ∥ I) · (M ≑ 𝟎)) [+] ((I ∥ I) · (𝟎 ≑ M))               ≈⟨ [+]-cong (∥-·-≑ I I M 𝟎) (∥-·-≑ I I 𝟎 M) ⟩
      ((I · M) [+] (I · 𝟎)) [+] ((I · 𝟎) [+] (I · M))           ≈⟨ [+]-cong ([+]-cong ·-identityˡ ·-identityˡ) ([+]-cong ·-identityˡ ·-identityˡ) ⟩
      (M [+] 𝟎) [+] (𝟎 [+] M)                                   ≈⟨ [+]-cong ([+]-𝟎ʳ M) ([+]-𝟎ˡ M) ⟩
      M [+] M                                                   ≈⟨ [+]-idem M ⟩
      M ∎
    where
      open ≈-Reasoning (≋-setoid _ _)

Mat-IdempotentSemiadditiveDagger : IdempotentSemiadditiveDagger
Mat-IdempotentSemiadditiveDagger = record
    { semiadditiveDagger = Mat-SemiadditiveDagger
    ; idempotent = idem _
    }

Mat-Dagger-2-Poset : Dagger-2-Poset
Mat-Dagger-2-Poset = dagger-2-poset Mat-IdempotentSemiadditiveDagger
