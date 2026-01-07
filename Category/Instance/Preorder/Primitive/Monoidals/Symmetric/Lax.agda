{-# OPTIONS --without-K --safe #-}

module Category.Instance.Preorder.Primitive.Monoidals.Symmetric.Lax where

import Category.Instance.Preorder.Primitive.Monoidals.Lax as MP using (_≃_; module ≃)

open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Category.Instance.Preorder.Primitive.Monoidals.Lax using (Monoidals)
open import Level using (Level; suc; _⊔_)
open import Preorder.Primitive.Monoidal using (SymmetricMonoidalPreorder)
open import Preorder.Primitive.MonotoneMap.Monoidal.Lax using (SymmetricMonoidalMonotone)
open import Relation.Binary using (IsEquivalence)

module _ {c₁ c₂ ℓ₁ ℓ₂ : Level} {A : SymmetricMonoidalPreorder c₁ ℓ₁} {B : SymmetricMonoidalPreorder c₂ ℓ₂} where

  open SymmetricMonoidalMonotone using () renaming (monoidalMonotone to mM)

  -- Pointwise isomorphism of symmetric monoidal monotone maps
  _≃_ : (f g : SymmetricMonoidalMonotone A B) → Set (c₁ ⊔ ℓ₂)
  f ≃ g = mM f MP.≃ mM g

  infix 4 _≃_

  ≃-isEquivalence : IsEquivalence _≃_
  ≃-isEquivalence = let open MP.≃ in record
      { refl = λ {x} → refl {x = mM x}
      ; sym = λ {f g} → sym {x = mM f} {y = mM g}
      ; trans = λ {f g h} → trans {i = mM f} {j = mM g} {k = mM h}
      }

  module ≃ = IsEquivalence ≃-isEquivalence

private

  identity : {c ℓ : Level} (A : SymmetricMonoidalPreorder c ℓ) → SymmetricMonoidalMonotone A A
  identity {c} {ℓ} A = record
      { monoidalMonotone = id {monoidalPreorder}
      }
    where
      open SymmetricMonoidalPreorder A using (monoidalPreorder)
      open Category (Monoidals c ℓ) using (id)

  compose
      : {c ℓ : Level}
        {P Q R : SymmetricMonoidalPreorder c ℓ}
      → SymmetricMonoidalMonotone Q R
      → SymmetricMonoidalMonotone P Q
      → SymmetricMonoidalMonotone P R
  compose {c} {ℓ} {R = R} G F = record
      { monoidalMonotone = G.monoidalMonotone ∘ F.monoidalMonotone
      }
    where
      module G = SymmetricMonoidalMonotone G
      module F = SymmetricMonoidalMonotone F
      open Category (Monoidals c ℓ) using (_∘_)

  compose-resp-≃
      : {c ℓ : Level}
        {A B C : SymmetricMonoidalPreorder c ℓ}
        {f h : SymmetricMonoidalMonotone B C}
        {g i : SymmetricMonoidalMonotone A B}
      → f ≃ h
      → g ≃ i
      → compose f g ≃ compose h i
  compose-resp-≃ {C = C} {f = f} {g} {h} {i} = ∘-resp-≈ {f = mM f} {mM g} {mM h} {mM i}
    where
      open Category (Monoidals _ _)
      open SymmetricMonoidalMonotone using () renaming (monoidalMonotone to mM)

-- The category of symmetric monoidal preorders and lax symmetric monoidal monotone
SymMonPre : (c ℓ : Level) → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
SymMonPre c ℓ = categoryHelper record
    { Obj = SymmetricMonoidalPreorder c ℓ
    ; _⇒_ = SymmetricMonoidalMonotone
    ; _≈_ = _≃_
    ; id  = λ {A} → identity A
    ; _∘_ = compose
    ; assoc = λ {f = f} {g h} → ≃.refl {x = compose (compose h g) f}
    ; identityˡ = λ {f = f} → ≃.refl {x = f}
    ; identityʳ = λ {f = f} → ≃.refl {x = f}
    ; equiv = ≃-isEquivalence
    ; ∘-resp-≈ = λ {f = f} {g h i} → compose-resp-≃ {f = f} {g} {h} {i}
    }
