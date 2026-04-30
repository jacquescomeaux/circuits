{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Category.Instance.Monoids (c ℓ : Level) where

import Algebra.Morphism.Bundles as Raw
import Algebra.Morphism.Construct.Composition as Compose
import Algebra.Morphism.Construct.Identity as Identity

open import Algebra using (Monoid)
open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Relation.Binary using (IsEquivalence)

open Monoid hiding (_≈_)

record MonoidHomomorphism (M N : Monoid c ℓ) : Set (c ⊔ ℓ) where

  constructor mk-⇒

  field
    rawMonoidHomomorphism : Raw.MonoidHomomorphism (rawMonoid M) (rawMonoid N)

  open Raw.MonoidHomomorphism rawMonoidHomomorphism public

module _ {M N : Monoid c ℓ} where

  -- Pointwise equality of monoid homomorphisms

  open MonoidHomomorphism

  _≗_ : (f g : MonoidHomomorphism M N) → Set (c ⊔ ℓ)
  _≗_ f g = (x : Carrier M) → let open Monoid N in ⟦ f ⟧ x ≈ ⟦ g ⟧ x

  infix 4 _≗_

  ≗-isEquivalence : IsEquivalence _≗_
  ≗-isEquivalence = record
      { refl = λ x → refl N
      ; sym = λ f≈g x → sym N (f≈g x)
      ; trans = λ f≈g g≈h x → trans N (f≈g x) (g≈h x)
      }

  module ≗ = IsEquivalence ≗-isEquivalence

private

  id : {M : Monoid c ℓ} → MonoidHomomorphism M M
  id {M} = mk-⇒ record
      { isMonoidHomomorphism = Identity.isMonoidHomomorphism (rawMonoid M) (refl M)
      }

  compose
      : {M N P : Monoid c ℓ}
      → MonoidHomomorphism N P
      → MonoidHomomorphism M N
      → MonoidHomomorphism M P
  compose {P = P} f g = mk-⇒ record
      { isMonoidHomomorphism =
          Compose.isMonoidHomomorphism
              (trans P)
              g.isMonoidHomomorphism
              f.isMonoidHomomorphism
      }
    where
      module f = MonoidHomomorphism f
      module g = MonoidHomomorphism g

open MonoidHomomorphism

-- the category of monoids and monoid homomorphisms
Monoids : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Monoids = categoryHelper record
    { Obj = Monoid c ℓ
    ; _⇒_ = MonoidHomomorphism
    ; _≈_ = _≗_
    ; id = id
    ; _∘_ = compose
    ; assoc = λ {_ _ _ Q} _ → refl Q
    ; identityˡ = λ {_ B} _ → refl B
    ; identityʳ = λ {_ B} _ → refl B
    ; equiv = ≗-isEquivalence
    ; ∘-resp-≈ = λ {C = C} {f g h i} eq₁ eq₂ x → trans C (⟦⟧-cong f (eq₂ x)) (eq₁ (⟦ i ⟧ x))
    }
