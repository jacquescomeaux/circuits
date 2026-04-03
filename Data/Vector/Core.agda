{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

open import Level using (Level; _⊔_)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)

module Data.Vector.Core {c ℓ : Level} (S : Setoid c ℓ) where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Data.Vec.Relation.Binary.Pointwise.Inductive as PW

open import Categories.Category.Instance.Nat using (Natop)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _+_)
open import Data.Setoid using (∣_∣)
open import Data.Vec as Vec using (Vec; lookup; tabulate)
open import Data.Vec.Properties using (tabulate∘lookup; lookup∘tabulate; tabulate-cong)
open import Data.Vec.Relation.Binary.Equality.Setoid S using (_≋_; ≋-isEquivalence)
open import Function using (Func; _⟶ₛ_; id; _⟨$⟩_; _∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≗_)

open Func
open Setoid S
open Fin
open Vec.Vec

private
  variable
    n A B C : ℕ

opaque

  -- Vectors over the rig
  Vector : ℕ → Set c
  Vector = Vec ∣ S ∣

  -- Pointwise equivalence of vectors
  _≊_ : Rel (Vector n) (c ⊔ ℓ)
  _≊_ A B = A ≋ B

  -- Pointwise equivalence is an equivalence relation
  ≊-isEquiv : IsEquivalence (_≊_ {n})
  ≊-isEquiv {n} = ≋-isEquivalence n

  _++_ : Vector A → Vector B → Vector (A + B)
  _++_ = Vec._++_

  ⟨⟩ : Vector 0
  ⟨⟩ = []

  ⟨⟩-! : (V : Vector 0) → V ≡ ⟨⟩
  ⟨⟩-! [] = ≡.refl

  ⟨⟩-++ : (V : Vector A) → ⟨⟩ ++ V ≡ V
  ⟨⟩-++ V = ≡.refl

-- A setoid of vectors for every natural number
Vectorₛ : ℕ → Setoid c (c ⊔ ℓ)
Vectorₛ n = record
    { Carrier = Vector n
    ; _≈_ = _≊_
    ; isEquivalence = ≊-isEquiv
  }

module ≊ {n} = Setoid (Vectorₛ n)

infix 4 _≊_

opaque

  unfolding Vector

  pull : (Fin B → Fin A) → Vectorₛ A ⟶ₛ Vectorₛ B
  pull f .to v = tabulate (λ i → lookup v (f i))
  pull f .cong ≊v = PW.tabulate⁺ (λ i → PW.lookup ≊v (f i))

  pull-id : {v : Vector n} → pull id ⟨$⟩ v ≊ v
  pull-id {v} = ≊.reflexive (tabulate∘lookup v)

  pull-∘
      : {f : Fin B → Fin A}
        {g : Fin C → Fin B}
        {v : Vector A}
      → pull (f ∘ g) ⟨$⟩ v ≊ pull g ⟨$⟩ (pull f ⟨$⟩ v)
  pull-∘ {f} {g} {v} = ≊.reflexive (≡.sym (tabulate-cong (λ i → lookup∘tabulate (lookup v ∘ f) (g i))))

  pull-cong
      : {f g : Fin B → Fin A}
      → f ≗ g
      → {v : Vector A}
      → pull f ⟨$⟩ v ≊ pull g ⟨$⟩ v
  pull-cong f≗g {v} = ≊.reflexive (tabulate-cong (λ i → ≡.cong (lookup v) (f≗g i)))

-- Copying, deleting, and rearranging elements
-- of a vector according to a function on indices
-- gives a contravariant functor from Nat to Setoids
Pull : Functor Natop (Setoids c (c ⊔ ℓ))
Pull = record
    { F₀ = Vectorₛ
    ; F₁ = pull
    ; identity = pull-id
    ; homomorphism = pull-∘
    ; F-resp-≈ = pull-cong
    }
