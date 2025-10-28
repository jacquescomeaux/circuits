{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Data.System {ℓ : Level} where

import Function.Construct.Identity as Id
import Relation.Binary.Properties.Preorder as PreorderProperties

open import Data.Circuit.Value using (Value)
open import Data.Nat.Base using (ℕ)
open import Data.Setoid using (_⇒ₛ_; ∣_∣)
open import Data.System.Values Value using (Values; _≋_; module ≋)
open import Level using (Level; _⊔_; 0ℓ; suc)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary using (Reflexive; Transitive; Preorder; _⇒_; Setoid)
open import Function.Base using (_∘_)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Function.Construct.Setoid using (_∙_)

open Func

record System (n : ℕ) : Set (suc ℓ) where

  field
    S : Setoid ℓ ℓ
    fₛ : ∣ Values n ⇒ₛ S ⇒ₛ S ∣
    fₒ : ∣ S ⇒ₛ Values n ∣

  fₛ′ : ∣ Values n ∣ → ∣ S ∣ → ∣ S ∣
  fₛ′ = to ∘ to fₛ

  fₒ′ : ∣ S ∣ → ∣ Values n ∣
  fₒ′ = to fₒ

  open Setoid S public

module _ {n : ℕ} where

  record ≤-System (a b : System n) : Set ℓ where
    module A = System a
    module B = System b
    field
      ⇒S : ∣ A.S ⇒ₛ B.S ∣
      ≗-fₛ
          : (i : ∣ Values n ∣) (s : ∣ A.S ∣)
          → ⇒S ⟨$⟩ (A.fₛ′ i s) B.≈ B.fₛ′ i (⇒S ⟨$⟩ s)
      ≗-fₒ
          : (s : ∣ A.S ∣)
          → A.fₒ′ s ≋ B.fₒ′ (⇒S ⟨$⟩ s)

  open ≤-System

  ≤-refl : Reflexive ≤-System
  ⇒S ≤-refl = Id.function _
  ≗-fₛ (≤-refl {x}) _ _ = System.refl x
  ≗-fₒ (≤-refl {x}) _ = ≋.refl

  ≡⇒≤ : _≡_ ⇒ ≤-System
  ≡⇒≤ ≡.refl = ≤-refl

  open System

  ≤-trans : Transitive ≤-System
  ⇒S (≤-trans a b) = ⇒S b ∙ ⇒S a
  ≗-fₛ (≤-trans {x} {y} {z} a b) i s = System.trans z (cong (⇒S b) (≗-fₛ a i s)) (≗-fₛ b i (⇒S a ⟨$⟩ s))
  ≗-fₒ (≤-trans a b) s = ≋.trans (≗-fₒ a s) (≗-fₒ b (⇒S a ⟨$⟩ s))

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

  Systemₛ : Setoid (suc ℓ) ℓ
  Systemₛ = InducedEquivalence
