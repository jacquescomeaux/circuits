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
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

record SemimoduleHomomorphism (M N : Semimodule R m ℓm) : Set (c ⊔ m ⊔ ℓm) where

  private
    module M = Semimodule M
    module N = Semimodule N

  field
    ⟦_⟧ : M.Carrierᴹ → N.Carrierᴹ
    isSemimoduleHomomorphism : IsSemimoduleHomomorphism M.rawSemimodule N.rawSemimodule ⟦_⟧

  open IsSemimoduleHomomorphism isSemimoduleHomomorphism public

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

_≈_ : {M N : Semimodule R m ℓm} → Rel (SemimoduleHomomorphism M N) (m ⊔ ℓm)
_≈_ {M} {N} f g = (x : M.Carrierᴹ) → ⟦ f ⟧ x N.≈ᴹ ⟦ g ⟧ x
  where
    module M = Semimodule M
    module N = Semimodule N

≈-isEquiv : {M N : Semimodule R m ℓm} → IsEquivalence (_≈_ {M} {N})
≈-isEquiv {M} {N} = record
    { refl = λ _ → N.≈ᴹ-refl
    ; sym = λ f≈g x → N.≈ᴹ-sym (f≈g x)
    ; trans = λ f≈g g≈h x → N.≈ᴹ-trans (f≈g x) (g≈h x)
    }
  where
    module M = Semimodule M
    module N = Semimodule N

∘-resp-≈
    : {M N P : Semimodule R m ℓm}
      {f h : SemimoduleHomomorphism N P}
      {g i : SemimoduleHomomorphism M N}
    → f ≈ h
    → g ≈ i
    → compose M N P f g ≈ compose M N P h i
∘-resp-≈ {M} {N} {P} {f} {g} {h} {i} f≈h g≈i x = P.≈ᴹ-trans (f.⟦⟧-cong (g≈i x)) (f≈h (⟦ i ⟧ x))
  where
    module P = Semimodule P
    module f = SemimoduleHomomorphism f

open Semimodule

Semimodules : Category (c ⊔ ℓ ⊔ suc (m ⊔ ℓm)) (c ⊔ m ⊔ ℓm) (m ⊔ ℓm)
Semimodules = categoryHelper record
    { Obj = Semimodule R m ℓm
    ; _⇒_ = SemimoduleHomomorphism
    ; _≈_ = _≈_
    ; id = λ {M} → id M
    ; _∘_ = λ {M N P} f g → compose M N P f g
    ; assoc = λ {D = D} _ → ≈ᴹ-refl D
    ; identityˡ = λ {B = B} _ → ≈ᴹ-refl B
    ; identityʳ = λ {B = B} _ → ≈ᴹ-refl B
    ; equiv = ≈-isEquiv
    ; ∘-resp-≈ = λ {f = f} {g h i } → ∘-resp-≈ {f = f} {g} {h} {i}
    }
