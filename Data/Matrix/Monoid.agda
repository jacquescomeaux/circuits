{-# OPTIONS --without-K --safe #-}

open import Algebra using (Monoid)
open import Level using (Level)

module Data.Matrix.Monoid {c ℓ : Level} (M : Monoid c ℓ) where

module M = Monoid M

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW

open import Data.Matrix.Core M.setoid using (Matrix; _≋_; _ᵀ; _∷ₕ_; []ᵥ; _≑_; _∥_; []ᵥ-!; []ᵥ-∥; ∷ₕ-∥)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; replicate; zipWith)
open import Data.Vec.Properties using (zipWith-replicate)
open import Data.Vector.Monoid M using (_⊕_; ⊕-cong; ⊕-identityˡ; ⊕-identityʳ; ⟨ε⟩)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; module ≡-Reasoning)

open M
open Vec
open ℕ

private
  variable
    A B C : ℕ

opaque

  unfolding Matrix

  𝟎 : Matrix A B
  𝟎 {A} {B} = replicate B ⟨ε⟩

  opaque

    unfolding _ᵀ []ᵥ ⟨ε⟩

    𝟎ᵀ : 𝟎 ᵀ ≡ 𝟎 {A} {B}
    𝟎ᵀ {zero} = ≡.refl
    𝟎ᵀ {suc A} = let open ≡-Reasoning in begin
        ⟨ε⟩ ∷ₕ (𝟎 ᵀ)  ≡⟨ ≡.cong (⟨ε⟩ ∷ₕ_) 𝟎ᵀ ⟩
        ⟨ε⟩ ∷ₕ 𝟎      ≡⟨ zipWith-replicate _∷_ ε ⟨ε⟩ ⟩
        𝟎             ∎

  opaque

    unfolding _≑_

    𝟎≑𝟎 : 𝟎 {A} {B} ≑ 𝟎 {A} {C} ≡ 𝟎
    𝟎≑𝟎 {B = zero} = ≡.refl
    𝟎≑𝟎 {B = suc B} = ≡.cong (⟨ε⟩ ∷_) (𝟎≑𝟎 {B = B})

  opaque

    unfolding _∷ₕ_ ⟨ε⟩

    ⟨ε⟩∷ₕ𝟎 : ⟨ε⟩ ∷ₕ 𝟎 {A} {B} ≡ 𝟎
    ⟨ε⟩∷ₕ𝟎 {A} {zero} = ≡.refl
    ⟨ε⟩∷ₕ𝟎 {A} {suc B} = ≡.cong (⟨ε⟩ ∷_) ⟨ε⟩∷ₕ𝟎

𝟎∥𝟎 : 𝟎 {A} {C} ∥ 𝟎 {B} {C} ≡ 𝟎
𝟎∥𝟎 {zero} {C} rewrite []ᵥ-! (𝟎 {0} {C}) = []ᵥ-∥ 𝟎
𝟎∥𝟎 {suc A} {C} {B} = begin
    𝟎 ∥ 𝟎               ≡⟨ ≡.cong (_∥ 𝟎) (⟨ε⟩∷ₕ𝟎 {A} {C}) ⟨
    (⟨ε⟩ ∷ₕ 𝟎 {A}) ∥ 𝟎  ≡⟨ ∷ₕ-∥ ⟨ε⟩ 𝟎 𝟎 ⟨
    ⟨ε⟩ ∷ₕ 𝟎 {A} ∥ 𝟎    ≡⟨ ≡.cong (⟨ε⟩ ∷ₕ_) 𝟎∥𝟎 ⟩
    ⟨ε⟩ ∷ₕ 𝟎            ≡⟨ ⟨ε⟩∷ₕ𝟎 ⟩
    𝟎                   ∎
  where
    open ≡-Reasoning

opaque

  unfolding Matrix

  _[+]_ : Matrix A B → Matrix A B → Matrix A B
  _[+]_ = zipWith _⊕_

  [+]-cong : {M M′ N N′ : Matrix A B} → M ≋ M′ → N ≋ N′ → M [+] N ≋ M′ [+] N′
  [+]-cong = PW.zipWith-cong ⊕-cong

  opaque

    unfolding 𝟎

    [+]-𝟎ˡ : (M : Matrix A B) → 𝟎 [+] M ≋ M
    [+]-𝟎ˡ [] = PW.[]
    [+]-𝟎ˡ (M₀ ∷ M) = ⊕-identityˡ M₀ PW.∷ [+]-𝟎ˡ M

    [+]-𝟎ʳ : (M : Matrix A B) → M [+] 𝟎 ≋ M
    [+]-𝟎ʳ [] = PW.[]
    [+]-𝟎ʳ (M₀ ∷ M) = ⊕-identityʳ M₀ PW.∷ [+]-𝟎ʳ M
