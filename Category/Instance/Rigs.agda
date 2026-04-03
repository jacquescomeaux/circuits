{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Category.Instance.Rigs {c ℓ : Level} where

import Algebra.Morphism.Construct.Identity as Identity
import Algebra.Morphism.Construct.Composition as Compose

open import Algebra using (Semiring)
open import Algebra.Morphism.Bundles using (SemiringHomomorphism)
open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

open Semiring using (rawSemiring; refl; trans)
open SemiringHomomorphism using (⟦_⟧)

id : (R : Semiring c ℓ) → SemiringHomomorphism (rawSemiring R) (rawSemiring R)
id R = record
    { isSemiringHomomorphism = Identity.isSemiringHomomorphism (rawSemiring R) (refl R)
    }

compose
    : (R S T : Semiring c ℓ)
    → SemiringHomomorphism (rawSemiring S) (rawSemiring T)
    → SemiringHomomorphism (rawSemiring R) (rawSemiring S)
    → SemiringHomomorphism (rawSemiring R) (rawSemiring T)
compose R S T f g = record
    { isSemiringHomomorphism =
        Compose.isSemiringHomomorphism
            (trans T)
            g.isSemiringHomomorphism
            f.isSemiringHomomorphism
    }
  where
    module f = SemiringHomomorphism f
    module g = SemiringHomomorphism g

Rigs : Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) c
Rigs = categoryHelper record
    { Obj = Semiring c ℓ
    ; _⇒_ = λ R S → SemiringHomomorphism (rawSemiring R) (rawSemiring S)
    ; _≈_ = λ f g → ⟦ f ⟧ ≗ ⟦ g ⟧
    ; id = λ {R} → id R
    ; _∘_ = λ {R S T} f g → compose R S T f g
    ; assoc = λ _ → ≡.refl
    ; identityˡ = λ _ → ≡.refl
    ; identityʳ = λ _ → ≡.refl
    ; equiv = record
        { refl = λ _ → ≡.refl
        ; sym = λ f≈g x → ≡.sym (f≈g x)
        ; trans = λ f≈g g≈h x → ≡.trans (f≈g x) (g≈h x)
        }
    ; ∘-resp-≈ = λ {f = f} {h g i} eq₁ eq₂ x → ≡.trans (≡.cong ⟦ f ⟧ (eq₂ x)) (eq₁ (⟦ i ⟧ x))
    }
