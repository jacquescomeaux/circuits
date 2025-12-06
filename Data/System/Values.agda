{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)
open import Level using (0ℓ)

module Data.System.Values (A : CommutativeMonoid 0ℓ 0ℓ) where

import Algebra.Properties.CommutativeMonoid.Sum as Sum
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as Pointwise
import Relation.Binary.PropositionalEquality as ≡

open import Data.Fin using (_↑ˡ_; _↑ʳ_; zero; suc; splitAt)
open import Data.Nat using (ℕ; _+_; suc)
open import Data.Product using (_,_)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Data.Setoid using (∣_∣)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec.Functional as Vec using (Vector; zipWith; replicate)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; _∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

open CommutativeMonoid A renaming (Carrier to Value)
open Func
open Sum A using (sum)

open Pointwise setoid using (≋-setoid; ≋-isEquivalence)

opaque

  Values : ℕ → Setoid 0ℓ 0ℓ
  Values = ≋-setoid

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
  open Setoid
  ≋-isEquiv : ∀ n → IsEquivalence (_≈_ (Values n))
  ≋-isEquiv = ≋-isEquivalence

module _ {n : ℕ} where

  opaque
    unfolding _⊕_

    ⊕-cong : {x y u v : ≋.Carrier {n}} → x ≋ y → u ≋ v → x ⊕ u ≋ y ⊕ v
    ⊕-cong x≋y u≋v i = ∙-cong (x≋y i) (u≋v i)

    ⊕-assoc : (x y z : ≋.Carrier {n}) → (x ⊕ y) ⊕ z ≋ x ⊕ (y ⊕ z)
    ⊕-assoc x y z i = assoc (x i) (y i) (z i)

    ⊕-identityˡ : (x : ≋.Carrier {n}) → <ε> ⊕ x ≋ x
    ⊕-identityˡ x i = identityˡ (x i)

    ⊕-identityʳ : (x : ≋.Carrier {n}) → x ⊕ <ε> ≋ x
    ⊕-identityʳ x i = identityʳ (x i)

    ⊕-comm : (x y : ≋.Carrier {n}) → x ⊕ y ≋ y ⊕ x
    ⊕-comm x y i = comm (x i) (y i)

open CommutativeMonoid
Valuesₘ : ℕ → CommutativeMonoid 0ℓ 0ℓ
Valuesₘ n .Carrier = ∣ Values n ∣
Valuesₘ n ._≈_ = _≋_
Valuesₘ n ._∙_ = _⊕_
Valuesₘ n .ε = <ε>
Valuesₘ n .isCommutativeMonoid = record
    { isMonoid = record
        { isSemigroup = record
            { isMagma = record
                { isEquivalence = ≋-isEquiv n
                ; ∙-cong = ⊕-cong
                }
            ; assoc = ⊕-assoc
            }
        ; identity = ⊕-identityˡ , ⊕-identityʳ
        }
    ; comm = ⊕-comm
    }

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
    ++-cong xs xs′ xs≋xs′ ys≋ys′ i with splitAt n i
    ... | inj₁ i = xs≋xs′ i
    ... | inj₂ i = ys≋ys′ i

    splitₛ : Values (n + m) ⟶ₛ Values n ×ₛ Values m
    to splitₛ v = v ∘ (_↑ˡ m) , v ∘ (n ↑ʳ_)
    cong splitₛ v₁≋v₂ = v₁≋v₂ ∘ (_↑ˡ m) , v₁≋v₂ ∘ (n ↑ʳ_)

  ++ₛ : Values n ×ₛ Values m ⟶ₛ Values (n + m)
  to ++ₛ (xs , ys) = xs ++ ys
  cong ++ₛ (≗xs , ≗ys) = ++-cong _ _ ≗xs ≗ys
