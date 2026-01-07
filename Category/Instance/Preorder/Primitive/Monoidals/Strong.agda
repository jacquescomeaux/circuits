{-# OPTIONS --without-K --safe #-}

module Category.Instance.Preorder.Primitive.Monoidals.Strong where

import Preorder.Primitive.MonotoneMap as MonotoneMap using (_≃_; module ≃)

open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Category.Instance.Preorder.Primitive.Preorders using (Preorders)
open import Level using (Level; suc; _⊔_)
open import Preorder.Primitive using (module Isomorphism)
open import Preorder.Primitive.Monoidal using (MonoidalPreorder)
open import Preorder.Primitive.MonotoneMap.Monoidal.Strong using (MonoidalMonotone)
open import Relation.Binary using (IsEquivalence)

module _ {c₁ c₂ ℓ₁ ℓ₂ : Level} {A : MonoidalPreorder c₁ ℓ₁} {B : MonoidalPreorder c₂ ℓ₂} where

  -- Pointwise equality of monoidal monotone maps

  open MonoidalMonotone using (F)

  _≃_ : (f g : MonoidalMonotone A B) → Set (c₁ ⊔ ℓ₂)
  f ≃ g = F f MonotoneMap.≃ F g

  infix 4 _≃_

  ≃-isEquivalence : IsEquivalence _≃_
  ≃-isEquivalence = let open MonotoneMap.≃ in record
      { refl = λ {x} → refl {x = F x}
      ; sym = λ {f g} → sym {x = F f} {y = F g}
      ; trans = λ {f g h} → trans {i = F f} {j = F g} {k = F h}
      }

  module ≃ = IsEquivalence ≃-isEquivalence

private

  identity : {c ℓ : Level} (A : MonoidalPreorder c ℓ) → MonoidalMonotone A A
  identity A = record
      { F = Category.id (Preorders _ _)
      ; ε = ≅.refl
      ; ⊗-homo = λ p₁ p₂ → ≅.refl {p₁ ⊗ p₂}
      }
    where
      open MonoidalPreorder A
      open Isomorphism U using (module ≅)

  compose
      : {c ℓ : Level}
        {P Q R : MonoidalPreorder c ℓ}
      → MonoidalMonotone Q R
      → MonoidalMonotone P Q
      → MonoidalMonotone P R
  compose {R = R} G F = record
      { F = let open Category (Preorders _ _) in G.F ∘ F.F
      ; ε = ≅.trans G.ε (G.map-resp-≅ F.ε)
      ; ⊗-homo = λ p₁ p₂ → ≅.trans (G.⊗-homo (F.map p₁) (F.map p₂)) (G.map-resp-≅ (F.⊗-homo p₁ p₂))
      }
    where
      module F = MonoidalMonotone F
      module G = MonoidalMonotone G
      open MonoidalPreorder R
      open Isomorphism U using (module ≅)

  compose-resp-≃
      : {c ℓ : Level}
        {A B C : MonoidalPreorder c ℓ}
        {f h : MonoidalMonotone B C}
        {g i : MonoidalMonotone A B}
      → f ≃ h
      → g ≃ i
      → compose f g ≃ compose h i
  compose-resp-≃ {C = C} {f = f} {g} {h} {i} = ∘-resp-≈ {f = F f} {F g} {F h} {F i}
    where
      open Category (Preorders _ _)
      open MonoidalMonotone using (F)

Monoidals : (c ℓ : Level) → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Monoidals c ℓ = categoryHelper record
    { Obj = MonoidalPreorder c ℓ
    ; _⇒_ = MonoidalMonotone
    ; _≈_ = _≃_
    ; id  = λ {A} → identity A
    ; _∘_ = compose
    ; assoc = λ {f = f} {g h} → ≃.refl {x = compose (compose h g) f}
    ; identityˡ = λ {f = f} → ≃.refl {x = f}
    ; identityʳ = λ {f = f} → ≃.refl {x = f}
    ; equiv = ≃-isEquivalence
    ; ∘-resp-≈ = λ {f = f} {g h i} → compose-resp-≃ {f = f} {g} {h} {i}
    }
  where
    open MonoidalMonotone using (F)
