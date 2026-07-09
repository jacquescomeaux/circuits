{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Category.Instance.Rigs {c ℓ : Level} where

import Algebra.Morphism.Construct.Composition as Compose
import Algebra.Morphism.Construct.Identity as Identity

open import Algebra using (Semiring)
open import Algebra.Morphism.Bundles using (SemiringHomomorphism)
open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Function using (_⟶ₛ_; Func)
open import Relation.Binary using (IsEquivalence)

open Func
open Semiring hiding (_≈_)

record RigHomomorphism (R S : Semiring c ℓ) : Set (c ⊔ ℓ) where

  constructor mk-⇒

  field
    semiringHomomorphism : SemiringHomomorphism (rawSemiring R) (rawSemiring S)

  open SemiringHomomorphism semiringHomomorphism public

  func : setoid R ⟶ₛ setoid S
  func .to = ⟦_⟧
  func .cong = ⟦⟧-cong

module _ {R S : Semiring c ℓ} where

  -- Pointwise equality of rig homomorphisms

  open RigHomomorphism

  _≗_ : (f g : RigHomomorphism R S) → Set (c ⊔ ℓ)
  _≗_ f g = (x : Carrier R) → let open Semiring S in ⟦ f ⟧ x ≈ ⟦ g ⟧ x

  infix 4 _≗_

  ≗-isEquivalence : IsEquivalence _≗_
  ≗-isEquivalence = record
      { refl = λ x → refl S
      ; sym = λ f≈g x → sym S (f≈g x)
      ; trans = λ f≈g g≈h x → trans S (f≈g x) (g≈h x)
      }

  module ≗ = IsEquivalence ≗-isEquivalence

id : (R : Semiring c ℓ) → RigHomomorphism R R
id R = mk-⇒ record
    { isSemiringHomomorphism = Identity.isSemiringHomomorphism (rawSemiring R) (refl R)
    }

compose
    : (R S T : Semiring c ℓ)
    → RigHomomorphism S T
    → RigHomomorphism R S
    → RigHomomorphism R T
compose R S T f g = mk-⇒ record
    { isSemiringHomomorphism =
        Compose.isSemiringHomomorphism
            (trans T)
            g.isSemiringHomomorphism
            f.isSemiringHomomorphism
    }
  where
    module f = RigHomomorphism f
    module g = RigHomomorphism g

open RigHomomorphism

Rigs : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Rigs = categoryHelper record
    { Obj = Semiring c ℓ
    ; _⇒_ = RigHomomorphism
    ; _≈_ = _≗_
    ; id = λ {R} → id R
    ; _∘_ = λ {R S T} f g → compose R S T f g
    ; assoc = λ {D = D} _ → refl D
    ; identityˡ = λ {B = B} _ → refl B
    ; identityʳ = λ {B = B} _ → refl B
    ; equiv = ≗-isEquivalence
    ; ∘-resp-≈ = λ {C = C} {f h g i} eq₁ eq₂ x → trans C (⟦⟧-cong f (eq₂ x)) (eq₁ (⟦ i ⟧ x))
    }
