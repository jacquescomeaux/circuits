{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)
open import Level using (0ℓ)

module Data.System.Values (A : CommutativeMonoid 0ℓ 0ℓ) where

import Algebra.Properties.CommutativeMonoid.Sum as Sum
import Data.Vec.Functional.Properties as VecProps
import Relation.Binary.PropositionalEquality as ≡

open import Data.Fin using (_↑ˡ_; _↑ʳ_; zero; suc)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid using (∣_∣)
open import Data.Vec.Functional as Vec using (Vector; zipWith; replicate)
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid using (≋-setoid)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; _∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Setoid)

open CommutativeMonoid A renaming (Carrier to Value)
open Func
open Sum A using (sum)

opaque

  Values : ℕ → Setoid 0ℓ 0ℓ
  Values = ≋-setoid (≡.setoid Value)

module _ {n : ℕ} where

  opaque

    unfolding Values

    merge : ∣ Values n ∣ → Value
    merge = sum

    _⊕_ : ∣ Values n ∣ → ∣ Values n ∣ → ∣ Values n ∣
    xs ⊕ ys = zipWith _∙_ xs ys

    <ε> : ∣ Values n ∣
    <ε> = replicate n ε

    head : ∣ Values (suc n) ∣ → Value
    head xs = xs zero

    tail : ∣ Values (suc n) ∣ → ∣ Values n ∣
    tail xs = xs ∘ suc

  module ≋ = Setoid (Values n)

  _≋_ : Rel ∣ Values n ∣ 0ℓ
  _≋_ = ≋._≈_

  infix 4 _≋_

opaque

  unfolding Values

  [] : ∣ Values 0 ∣
  [] = Vec.[]

  []-unique : (xs ys : ∣ Values 0 ∣) → xs ≋ ys
  []-unique xs ys ()

module _ {n m : ℕ} where

  opaque

    unfolding Values

    _++_ : ∣ Values n ∣ → ∣ Values m ∣ → ∣ Values (n + m) ∣
    _++_ = Vec._++_

    infixr 5 _++_

    ++-cong
        : (xs xs′ : ∣ Values n ∣)
          {ys ys′ : ∣ Values m ∣}
        → xs ≋ xs′
        → ys ≋ ys′
        → xs ++ ys ≋ xs′ ++ ys′
    ++-cong xs xs′ = VecProps.++-cong xs xs′

    splitₛ : Values (n + m) ⟶ₛ Values n ×ₛ Values m
    to splitₛ v = v ∘ (_↑ˡ m) , v ∘ (n ↑ʳ_)
    cong splitₛ v₁≋v₂ = v₁≋v₂ ∘ (_↑ˡ m) , v₁≋v₂ ∘ (n ↑ʳ_)

  ++ₛ : Values n ×ₛ Values m ⟶ₛ Values (n + m)
  to ++ₛ (xs , ys) = xs ++ ys
  cong ++ₛ (≗xs , ≗ys) = ++-cong _ _ ≗xs ≗ys
