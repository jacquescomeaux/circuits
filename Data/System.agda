{-# OPTIONS --without-K --safe #-}

module Data.System where

import Relation.Binary.Properties.Preorder as PreorderProperties

open import Data.Circuit.Value using (Value)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Functional using (Vector)
open import Data.Fin.Base using (Fin)
open import Level using (Level; suc; 0ℓ)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)
open import Relation.Binary using (Rel; Reflexive; Transitive; Preorder; _⇒_; Setoid)
open import Function.Base using (id; _∘_)

Input : ℕ → Set
Input = Vector Value

Output : ℕ → Set
Output = Vector Value

module _ {ℓ : Level} where

  record System (n : ℕ) : Set (suc ℓ) where
    field
      S : Set ℓ
      fₛ : Input n → S → S
      fₒ : Input n → S → Output n
      fₛ-cong : {i j : Input n} → i ≗ j → fₛ i ≗ fₛ j
      fₒ-cong : {i j : Input n} → i ≗ j → (s : S) → fₒ i s ≗ fₒ j s

  module _ {n : ℕ} where

    record ≤-System (a b : System n) : Set ℓ where
      module A = System a
      module B = System b
      field
        ⇒S : A.S → B.S
        ≗-fₛ : (i : Input n) (s : A.S) → ⇒S (A.fₛ i s) ≡ B.fₛ i (⇒S s)
        ≗-fₒ : (i : Input n) (s : A.S) (k : Fin n) → A.fₒ i s k ≡ B.fₒ i (⇒S s) k

    open ≤-System

    ≤-refl : Reflexive ≤-System
    ⇒S ≤-refl = id
    ≗-fₛ ≤-refl _ _ = ≡.refl
    ≗-fₒ ≤-refl _ _ _ = ≡.refl

    ≡⇒≤ : _≡_ ⇒ ≤-System
    ≡⇒≤ ≡.refl = ≤-refl

    open System
    ≤-trans : Transitive ≤-System
    ⇒S (≤-trans a b) = ⇒S b ∘ ⇒S a
    ≗-fₛ (≤-trans a b) i s = ≡.trans (≡.cong (⇒S b) (≗-fₛ a i s)) (≗-fₛ b i (⇒S a s))
    ≗-fₒ (≤-trans a b) i s k = ≡.trans (≗-fₒ a i s k) (≗-fₒ b i (⇒S a s) k)

    System-Preorder : Preorder (suc ℓ) (suc ℓ) ℓ
    System-Preorder = record
        { Carrier = System n
        ; _≈_ = _≡_
        ; _≲_ = ≤-System
        ; isPreorder = record
            { isEquivalence = ≡.isEquivalence
            ; reflexive = ≡⇒≤
            ; trans = ≤-trans
            }
        }

  module _ (n : ℕ) where

    open PreorderProperties (System-Preorder {n}) using (InducedEquivalence)
    System-Setoid : Setoid (suc ℓ) ℓ
    System-Setoid = InducedEquivalence
