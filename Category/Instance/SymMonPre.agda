{-# OPTIONS --without-K --safe #-}

module Category.Instance.SymMonPre where

import Category.Instance.MonoidalPreorders as MP using (_≗_; module ≗)

open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Category.Instance.MonoidalPreorders using (MonoidalPreorders)
open import Level using (Level; suc; _⊔_)
open import Preorder.Monoidal using (SymmetricMonoidalPreorder; SymmetricMonoidalMonotone)
open import Relation.Binary using (IsEquivalence)

private

  identity : {c ℓ e : Level} (A : SymmetricMonoidalPreorder c ℓ e) → SymmetricMonoidalMonotone A A
  identity {c} {ℓ} {e} A = record
      { monoidalMonotone = id {monoidalPreorder}
      }
    where
      open SymmetricMonoidalPreorder A using (monoidalPreorder)
      open Category (MonoidalPreorders c ℓ e) using (id)

  compose
      : {c ℓ e : Level}
        {P Q R : SymmetricMonoidalPreorder c ℓ e}
      → SymmetricMonoidalMonotone Q R
      → SymmetricMonoidalMonotone P Q
      → SymmetricMonoidalMonotone P R
  compose {c} {ℓ} {e} {R = R} G F = record
      { monoidalMonotone = G.monoidalMonotone ∘ F.monoidalMonotone
      }
    where
      module G = SymmetricMonoidalMonotone G
      module F = SymmetricMonoidalMonotone F
      open Category (MonoidalPreorders c ℓ e) using (_∘_)

module _ {c₁ c₂ ℓ₁ ℓ₂ e₁ e₂ : Level} {A : SymmetricMonoidalPreorder c₁ ℓ₁ e₁} {B : SymmetricMonoidalPreorder c₂ ℓ₂ e₂} where

  open SymmetricMonoidalMonotone using () renaming (monoidalMonotone to mM)

  -- Pointwise equality of symmetric monoidal monotone maps
  _≗_ : (f g : SymmetricMonoidalMonotone A B) → Set (c₁ ⊔ ℓ₂)
  f ≗ g = mM f MP.≗ mM g

  infix 4 _≗_

  ≗-isEquivalence : IsEquivalence _≗_
  ≗-isEquivalence = let open MP.≗ in record
      { refl = λ {x} → refl {x = mM x}
      ; sym = λ {f g} → sym {x = mM f} {y = mM g}
      ; trans = λ {f g h} → trans {i = mM f} {j = mM g} {k = mM h}
      }

  module ≗ = IsEquivalence ≗-isEquivalence

-- The category of symmetric monoidal preorders
SymMonPre : (c ℓ e : Level) → Category (suc (c ⊔ ℓ ⊔ e)) (c ⊔ ℓ ⊔ e) (c ⊔ ℓ)
SymMonPre c ℓ e = categoryHelper record
    { Obj = SymmetricMonoidalPreorder c ℓ e
    ; _⇒_ = SymmetricMonoidalMonotone
    ; _≈_ = _≗_
    ; id  = λ {A} → identity A
    ; _∘_ = λ {A B C} f g → compose f g
    ; assoc = λ {_ _ _ D _ _ _ _} → Eq.refl D
    ; identityˡ = λ {_ B _ _} → Eq.refl B
    ; identityʳ = λ {_ B _ _} → Eq.refl B
    ; equiv = ≗-isEquivalence
    ; ∘-resp-≈ = λ {_ _ C _ h} f≈h g≈i → Eq.trans C f≈h (cong h g≈i)
    }
  where
    open SymmetricMonoidalMonotone using (cong)
    open SymmetricMonoidalPreorder using (refl; module Eq)
