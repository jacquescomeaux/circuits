{-# OPTIONS --without-K --safe #-}

module Data.System where

import Relation.Binary.Properties.Preorder as PreorderProperties

open import Data.Circuit.Value using (Value)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Functional using (Vector)
open import Level using (Level; _⊔_; 0ℓ; suc)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary using (Rel; Reflexive; Transitive; Preorder; _⇒_; Setoid)
open import Function.Base using (id; _∘_)
import Function.Construct.Identity as Id
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid using (≋-setoid)

open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)

open import Function.Construct.Setoid using (setoid; _∙_)
open Func

_⇒ₛ_ : {a₁ a₂ b₁ b₂ : Level} → Setoid a₁ a₂ → Setoid b₁ b₂ → Setoid (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂) (a₁ ⊔ b₂)
_⇒ₛ_ = setoid

infixr 0 _⇒ₛ_

∣_∣ : {c ℓ : Level} → Setoid c ℓ → Set c
∣_∣ = Setoid.Carrier

Values : ℕ → Setoid 0ℓ 0ℓ
Values = ≋-setoid (≡.setoid Value)

_≋_ : {n : ℕ} → Rel (Vector Value n) 0ℓ
_≋_ {n} = Setoid._≈_ (Values n)

module ≋ {n : ℕ} = Setoid (Values n)

module _ {ℓ : Level} where

  record System (n : ℕ) : Set (suc ℓ) where
    field
      S : Setoid ℓ ℓ
      fₛ : ∣ Values n ⇒ₛ S ⇒ₛ S ∣
      fₒ : ∣ Values n ⇒ₛ S ⇒ₛ Values n ∣

    fₛ′ : ∣ Values n ∣ → ∣ S ∣ → ∣ S ∣
    fₛ′ = to ∘ to fₛ

    fₒ′ : ∣ Values n ∣ → ∣ S ∣ → ∣ Values n ∣
    fₒ′ = to ∘ to fₒ

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
            : (i : ∣ Values n ∣) (s : ∣ A.S ∣)
            → A.fₒ′ i s ≋ B.fₒ′ i (⇒S ⟨$⟩ s)

    open ≤-System

    ≤-refl : Reflexive ≤-System
    ⇒S ≤-refl = Id.function _
    ≗-fₛ (≤-refl {x}) p e = System.refl x
    ≗-fₒ (≤-refl {x}) _ _ = ≋.refl

    ≡⇒≤ : _≡_ ⇒ ≤-System
    ≡⇒≤ ≡.refl = ≤-refl

    open System
    ≤-trans : Transitive ≤-System
    ⇒S (≤-trans a b) = ⇒S b ∙ ⇒S a
    ≗-fₛ (≤-trans {x} {y} {z} a b) i s = System.trans z (cong (⇒S b) (≗-fₛ a i s)) (≗-fₛ b i (⇒S a ⟨$⟩ s))
    ≗-fₒ (≤-trans {x} {y} {z} a b) i s = ≋.trans (≗-fₒ a i s) (≗-fₒ b i (⇒S a ⟨$⟩ s))

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
