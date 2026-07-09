{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Category.Instance.CMonoids (c ℓ : Level) where

import Algebra.Morphism.Bundles as Raw
import Algebra.Morphism.Construct.Composition as Compose
import Algebra.Morphism.Construct.Identity as Identity

open import Algebra using (CommutativeMonoid)
open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Relation.Binary using (IsEquivalence)
open import Function using (Func; _⟶ₛ_)

open CommutativeMonoid hiding (_≈_)
open Func

record CMonoidHomomorphism (M N : CommutativeMonoid c ℓ) : Set (c ⊔ ℓ) where

  constructor mk-⇒

  field
    rawMonoidHomomorphism : Raw.MonoidHomomorphism (rawMonoid M) (rawMonoid N)

  open Raw.MonoidHomomorphism rawMonoidHomomorphism public

  func : setoid M ⟶ₛ setoid N
  func .to = ⟦_⟧
  func .cong = ⟦⟧-cong

module _ {M N : CommutativeMonoid c ℓ} where

  -- Pointwise equality of monoid homomorphisms

  open CMonoidHomomorphism

  _≗_ : (f g : CMonoidHomomorphism M N) → Set (c ⊔ ℓ)
  _≗_ f g = (x : Carrier M) → let open CommutativeMonoid N in ⟦ f ⟧ x ≈ ⟦ g ⟧ x

  infix 4 _≗_

  ≗-isEquivalence : IsEquivalence _≗_
  ≗-isEquivalence = record
      { refl = λ x → refl N
      ; sym = λ f≈g x → sym N (f≈g x)
      ; trans = λ f≈g g≈h x → trans N (f≈g x) (g≈h x)
      }

  module ≗ = IsEquivalence ≗-isEquivalence

private

  id : {M : CommutativeMonoid c ℓ} → CMonoidHomomorphism M M
  id {M} = mk-⇒ record
      { isMonoidHomomorphism = Identity.isMonoidHomomorphism (rawMonoid M) (refl M)
      }

  compose
      : {M N P : CommutativeMonoid c ℓ}
      → CMonoidHomomorphism N P
      → CMonoidHomomorphism M N
      → CMonoidHomomorphism M P
  compose {P = P} f g = mk-⇒ record
      { isMonoidHomomorphism =
          Compose.isMonoidHomomorphism
              (trans P)
              g.isMonoidHomomorphism
              f.isMonoidHomomorphism
      }
    where
      module f = CMonoidHomomorphism f
      module g = CMonoidHomomorphism g

open CMonoidHomomorphism

-- the category of commutative monoids and monoid homomorphisms
CMonoids : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
CMonoids = categoryHelper record
    { Obj = CommutativeMonoid c ℓ
    ; _⇒_ = CMonoidHomomorphism
    ; _≈_ = _≗_
    ; id = id
    ; _∘_ = compose
    ; assoc = λ {_ _ _ Q} _ → refl Q
    ; identityˡ = λ {_ B} _ → refl B
    ; identityʳ = λ {_ B} _ → refl B
    ; equiv = ≗-isEquivalence
    ; ∘-resp-≈ = λ {C = C} {f g h i} eq₁ eq₂ x → trans C (⟦⟧-cong f (eq₂ x)) (eq₁ (⟦ i ⟧ x))
    }
