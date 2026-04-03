{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeSemiring)
open import Level using (Level; suc; _⊔_)

module Category.Instance.Semimodules {c ℓ m ℓm : Level} (R : CommutativeSemiring c ℓ) where

import Algebra.Module.Morphism.Construct.Composition as Compose
import Algebra.Module.Morphism.Construct.Identity as Identity

open import Algebra.Module using (Semimodule)
open import Algebra.Module.Morphism.Structures using (IsSemimoduleHomomorphism)
open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

record SemimoduleHomomorphism (M N : Semimodule R m ℓm) : Set (c ⊔ m ⊔ ℓm) where

  private
    module M = Semimodule M
    module N = Semimodule N

  field
    ⟦_⟧ : M.Carrierᴹ → N.Carrierᴹ
    isSemimoduleHomomorphism : IsSemimoduleHomomorphism M.rawSemimodule N.rawSemimodule ⟦_⟧

id : (M : Semimodule R m ℓm) → SemimoduleHomomorphism M M
id M = record
    { isSemimoduleHomomorphism = Identity.isSemimoduleHomomorphism M.rawSemimodule M.≈ᴹ-refl
    }
  where
    module M = Semimodule M

compose
    : (M N P : Semimodule R m ℓm)
    → SemimoduleHomomorphism N P
    → SemimoduleHomomorphism M N
    → SemimoduleHomomorphism M P
compose M N P f g = record
    { isSemimoduleHomomorphism =
        Compose.isSemimoduleHomomorphism
            P.≈ᴹ-trans
            g.isSemimoduleHomomorphism
            f.isSemimoduleHomomorphism
    }
  where
    module f = SemimoduleHomomorphism f
    module g = SemimoduleHomomorphism g
    module P = Semimodule P

open SemimoduleHomomorphism

Semimodules : Category (c ⊔ ℓ ⊔ suc (m ⊔ ℓm)) (c ⊔ m ⊔ ℓm) m
Semimodules = categoryHelper record
    { Obj = Semimodule R m ℓm
    ; _⇒_ = SemimoduleHomomorphism
    ; _≈_ = λ f g → ⟦ f ⟧ ≗ ⟦ g ⟧
    ; id = λ {M} → id M
    ; _∘_ = λ {M N P} f g → compose M N P f g
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
