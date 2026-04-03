{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semiring)
open import Level using (Level; suc; _⊔_)

module Category.Instance.Bisemimodules {c₁ c₂ ℓ₁ ℓ₂ m ℓm : Level} (R : Semiring c₁ ℓ₁) (S : Semiring c₂ ℓ₂) where

import Algebra.Module.Morphism.Construct.Composition as Compose
import Algebra.Module.Morphism.Construct.Identity as Identity

open import Algebra.Module using (Bisemimodule)
open import Algebra.Module.Morphism.Structures using (IsBisemimoduleHomomorphism)
open import Categories.Category using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

record BisemimoduleHomomorphism (M N : Bisemimodule R S m ℓm) : Set (c₁ ⊔ c₂ ⊔ m ⊔ ℓm) where

  private
    module M = Bisemimodule M
    module N = Bisemimodule N

  field
    ⟦_⟧ : M.Carrierᴹ → N.Carrierᴹ
    isBisemimoduleHomomorphism : IsBisemimoduleHomomorphism M.rawBisemimodule N.rawBisemimodule ⟦_⟧

id : (M : Bisemimodule R S m ℓm) → BisemimoduleHomomorphism M M
id M = record
    { isBisemimoduleHomomorphism = Identity.isBisemimoduleHomomorphism M.rawBisemimodule M.≈ᴹ-refl
    }
  where
    module M = Bisemimodule M

compose
    : (M N P : Bisemimodule R S m ℓm)
    → BisemimoduleHomomorphism N P
    → BisemimoduleHomomorphism M N
    → BisemimoduleHomomorphism M P
compose M N P f g = record
    { isBisemimoduleHomomorphism =
        Compose.isBisemimoduleHomomorphism
            P.≈ᴹ-trans
            g.isBisemimoduleHomomorphism
            f.isBisemimoduleHomomorphism
    }
  where
    module f = BisemimoduleHomomorphism f
    module g = BisemimoduleHomomorphism g
    module P = Bisemimodule P

open BisemimoduleHomomorphism

Bisemimodules : Category (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ suc (m ⊔ ℓm)) (c₁ ⊔ c₂ ⊔ m ⊔ ℓm) m
Bisemimodules = categoryHelper record
    { Obj = Bisemimodule R S m ℓm
    ; _⇒_ = BisemimoduleHomomorphism
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
