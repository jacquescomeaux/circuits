{-# OPTIONS --without-K --safe #-}

module Category.Instance.Preorders where

import Relation.Binary.Morphism.Construct.Identity as Id
import Relation.Binary.Morphism.Construct.Composition as Comp

open import Categories.Category using (Category)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (Preorder; IsEquivalence)
open import Relation.Binary.Morphism using (PreorderHomomorphism)

open Preorder using (Carrier; module Eq) renaming (_≈_ to ₍_₎_≈_; _≲_ to ₍_₎_≤_)
open PreorderHomomorphism using (⟦_⟧; cong)

module _ {c₁ c₂ ℓ₁ ℓ₂ e₁ e₂ : Level} {A : Preorder c₁ ℓ₁ e₁} {B : Preorder c₂ ℓ₂ e₂} where

  -- Pointwise equality of monotone maps

  _≗_ : (f g : PreorderHomomorphism A B) → Set (c₁ ⊔ ℓ₂)
  f ≗ g = {x : Carrier A} → ₍ B ₎ ⟦ f ⟧ x ≈ ⟦ g ⟧ x

  infix 4 _≗_

  ≗-isEquivalence : IsEquivalence _≗_
  ≗-isEquivalence = record
      { refl = Eq.refl B
      ; sym = λ f≈g → Eq.sym B f≈g
      ; trans = λ f≈g g≈h → Eq.trans B f≈g g≈h
      }

  module ≗ = IsEquivalence ≗-isEquivalence

-- The category of preorders and preorder homomorphisms

Preorders : (c ℓ e : Level) → Category (suc (c ⊔ ℓ ⊔ e)) (c ⊔ ℓ ⊔ e) (c ⊔ ℓ)
Preorders c ℓ e = record
    { Obj = Preorder c ℓ e
    ; _⇒_ = PreorderHomomorphism
    ; _≈_ = _≗_
    ; id  = λ {A} → Id.preorderHomomorphism A
    ; _∘_ = λ f g → Comp.preorderHomomorphism g f
    ; assoc = λ {_ _ _ D} → Eq.refl D
    ; sym-assoc = λ {_ _ _ D} → Eq.refl D
    ; identityˡ = λ {_ B} → Eq.refl B
    ; identityʳ = λ {_ B} → Eq.refl B
    ; identity² = λ {A} → Eq.refl A
    ; equiv = ≗-isEquivalence
    ; ∘-resp-≈ = λ {_ _ C _ h} f≈h g≈i → Eq.trans C f≈h (cong h g≈i)
    }
