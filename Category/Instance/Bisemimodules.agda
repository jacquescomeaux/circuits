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
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

record BisemimoduleHomomorphism (M N : Bisemimodule R S m ℓm) : Set (c₁ ⊔ c₂ ⊔ m ⊔ ℓm) where

  private
    module M = Bisemimodule M
    module N = Bisemimodule N

  field
    ⟦_⟧ : M.Carrierᴹ → N.Carrierᴹ
    isBisemimoduleHomomorphism : IsBisemimoduleHomomorphism M.rawBisemimodule N.rawBisemimodule ⟦_⟧

  open IsBisemimoduleHomomorphism isBisemimoduleHomomorphism public

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

_≈_ : {M N : Bisemimodule R S m ℓm} → Rel (BisemimoduleHomomorphism M N) (m ⊔ ℓm)
_≈_ {M} {N} f g = (x : M.Carrierᴹ) → ⟦ f ⟧ x N.≈ᴹ ⟦ g ⟧ x
  where
    module M = Bisemimodule M
    module N = Bisemimodule N

≈-isEquiv : {M N : Bisemimodule R S m ℓm} → IsEquivalence (_≈_ {M} {N})
≈-isEquiv {M} {N} = record
    { refl = λ _ → N.≈ᴹ-refl
    ; sym = λ f≈g x → N.≈ᴹ-sym (f≈g x)
    ; trans = λ f≈g g≈h x → N.≈ᴹ-trans (f≈g x) (g≈h x)
    }
  where
    module M = Bisemimodule M
    module N = Bisemimodule N

∘-resp-≈
    : {M N P : Bisemimodule R S m ℓm}
      {f h : BisemimoduleHomomorphism N P}
      {g i : BisemimoduleHomomorphism M N}
    → f ≈ h
    → g ≈ i
    → compose M N P f g ≈ compose M N P h i
∘-resp-≈ {M} {N} {P} {f} {g} {h} {i} f≈h g≈i x = P.≈ᴹ-trans (f.⟦⟧-cong (g≈i x)) (f≈h (⟦ i ⟧ x))
  where
    module P = Bisemimodule P
    module f = BisemimoduleHomomorphism f

open Bisemimodule

Bisemimodules : Category (c₁ ⊔ c₂ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ suc (m ⊔ ℓm)) (c₁ ⊔ c₂ ⊔ m ⊔ ℓm) (m ⊔ ℓm)
Bisemimodules = categoryHelper record
    { Obj = Bisemimodule R S m ℓm
    ; _⇒_ = BisemimoduleHomomorphism
    ; _≈_ = _≈_
    ; id = λ {M} → id M
    ; _∘_ = λ {M N P} f g → compose M N P f g
    ; assoc = λ {D = D} _ → ≈ᴹ-refl D
    ; identityˡ = λ {B = B} _ → ≈ᴹ-refl B
    ; identityʳ = λ {B = B} _ → ≈ᴹ-refl B
    ; equiv = ≈-isEquiv
    ; ∘-resp-≈ = λ {f = f} {g h i } → ∘-resp-≈ {f = f} {g} {h} {i}
    }
