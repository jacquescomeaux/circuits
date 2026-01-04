{-# OPTIONS --without-K --safe #-}

module Category.Instance.MonoidalPreorders where

import Category.Instance.Preorders as MonotoneMap using (_≗_; module ≗)
import Relation.Binary.Morphism.Construct.Composition as Comp
import Relation.Binary.Morphism.Construct.Identity as Id

open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Level using (Level; suc; _⊔_)
open import Preorder.Monoidal using (MonoidalPreorder; MonoidalMonotone)
open import Relation.Binary using (IsEquivalence)

private

  identity : {c ℓ e : Level} (A : MonoidalPreorder c ℓ e) → MonoidalMonotone A A
  identity A = let open MonoidalPreorder A in record
      { F = Id.preorderHomomorphism U
      ; ε = refl {unit}
      ; ⊗-homo = λ p₁ p₂ → refl {p₁ ⊗ p₂}
      }

  compose
      : {c ℓ e : Level}
        {P Q R : MonoidalPreorder c ℓ e}
      → MonoidalMonotone Q R
      → MonoidalMonotone P Q
      → MonoidalMonotone P R
  compose {R = R} G F = record
      { F = Comp.preorderHomomorphism F.F G.F
      ; ε = trans G.ε (G.mono F.ε)
      ; ⊗-homo = λ p₁ p₂ → trans (G.⊗-homo F.⟦ p₁ ⟧ F.⟦ p₂ ⟧) (G.mono (F.⊗-homo p₁ p₂))
      }
    where
      module F = MonoidalMonotone F
      module G = MonoidalMonotone G
      open MonoidalPreorder R

module _ {c₁ c₂ ℓ₁ ℓ₂ e₁ e₂ : Level} {A : MonoidalPreorder c₁ ℓ₁ e₁} {B : MonoidalPreorder c₂ ℓ₂ e₂} where

  -- Pointwise equality of monoidal monotone maps

  open MonoidalMonotone using (F)

  _≗_ : (f g : MonoidalMonotone A B) → Set (c₁ ⊔ ℓ₂)
  f ≗ g = F f MonotoneMap.≗ F g

  infix 4 _≗_

  ≗-isEquivalence : IsEquivalence _≗_
  ≗-isEquivalence = let open MonotoneMap.≗ in record
      { refl = λ {x} → refl {x = F x}
      ; sym = λ {f g} → sym {x = F f} {y = F g}
      ; trans = λ {f g h} → trans {i = F f} {j = F g} {k = F h}
      }

  module ≗ = IsEquivalence ≗-isEquivalence

MonoidalPreorders : (c ℓ e : Level) → Category (suc (c ⊔ ℓ ⊔ e)) (c ⊔ ℓ ⊔ e) (c ⊔ ℓ)
MonoidalPreorders c ℓ e = categoryHelper record
    { Obj = MonoidalPreorder c ℓ e
    ; _⇒_ = MonoidalMonotone
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
    open MonoidalMonotone using (F; cong)
    open MonoidalPreorder using (U; refl; module Eq)
