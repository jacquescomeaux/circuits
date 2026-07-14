{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeSemiring)
open import Level using (Level; suc; _⊔_)

module Category.Cartesian.Instance.Semimodules {c ℓ m ℓm : Level} (R : CommutativeSemiring c ℓ) where

import Algebra.Module.Construct.Zero as 𝟎
import Algebra.Module.Construct.DirectProduct as ×

open import Algebra.Module using (Semimodule)
open import Algebra.Morphism.Construct.DirectProduct using () renaming (module Monoid-Export to Monoid-×)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Object.Terminal using (Terminal)
open import Category.Instance.Semimodules {c} {ℓ} {m} {ℓm} R using (Semimodules; SemimoduleHomomorphism)
open import Data.Product using (_,_; proj₁; proj₂; <_,_>)
open import Data.Unit.Polymorphic using (tt)

open Semimodule using (≈ᴹ-refl; ≈ᴹ-sym)

terminal : Terminal Semimodules
terminal = record
    { ⊤ = 𝟎.semimodule
    ; ⊤-is-terminal = record
        { ! = record { ⟦_⟧ = λ _ → tt }
        ; !-unique = λ _ _ → tt
        }
    }

module _ (A B : Semimodule R m ℓm) where

  π₁ : SemimoduleHomomorphism (×.semimodule A B) A
  π₁ = record
      { ⟦_⟧ = proj₁
      ; isSemimoduleHomomorphism = record
          { isBisemimoduleHomomorphism = record
              { +ᴹ-isMonoidHomomorphism = Monoid-×.proj₁ {refl = ≈ᴹ-refl A}
              ; *ₗ-homo = λ _ _ → ≈ᴹ-refl A
              ; *ᵣ-homo = λ _ _ → ≈ᴹ-refl A
              }
          }
      }

  π₂ : SemimoduleHomomorphism (×.semimodule A B) B
  π₂ = record
      { ⟦_⟧ = proj₂
      ; isSemimoduleHomomorphism = record
          { isBisemimoduleHomomorphism = record
              { +ᴹ-isMonoidHomomorphism = Monoid-×.proj₂ {refl = ≈ᴹ-refl B}
              ; *ₗ-homo = λ _ _ → ≈ᴹ-refl B
              ; *ᵣ-homo = λ _ _ → ≈ᴹ-refl B
              }
          }
      }

module _ {A B C : Semimodule R m ℓm} where

  open SemimoduleHomomorphism

  ⟨_,_⟩  : SemimoduleHomomorphism C A
      → SemimoduleHomomorphism C B
      → SemimoduleHomomorphism C (×.semimodule A B)
  ⟨_,_⟩ f g = record
      { ⟦_⟧ = < ⟦ f ⟧ , ⟦ g ⟧ >
      ; isSemimoduleHomomorphism = record
          { isBisemimoduleHomomorphism = record
              { +ᴹ-isMonoidHomomorphism = Monoid-×.< +ᴹ-isMonoidHomomorphism f , +ᴹ-isMonoidHomomorphism g >
              ; *ₗ-homo = λ r x → *ₗ-homo f r x , *ₗ-homo g r x
              ; *ᵣ-homo = λ r x → *ᵣ-homo f r x , *ᵣ-homo g r x
              }
          }
      }

products : BinaryProducts Semimodules
products = record
    { product = λ {A B} → record
        { A×B = ×.semimodule A B
        ; π₁ = π₁ A B
        ; π₂ = π₂ A B
        ; ⟨_,_⟩ = ⟨_,_⟩
        ; project₁ = λ _ → ≈ᴹ-refl A
        ; project₂ = λ _ → ≈ᴹ-refl B
        ; unique = λ eq₁ eq₂ x → ≈ᴹ-sym A (eq₁ x) , ≈ᴹ-sym B (eq₂ x)
        }
    }

Semimodules-Cartesian : Cartesian Semimodules
Semimodules-Cartesian = record
    { terminal = terminal
    ; products = products
    }

Semimodules-CC : CartesianCategory (c ⊔ ℓ ⊔ suc (m ⊔ ℓm)) (c ⊔ m ⊔ ℓm) (m ⊔ ℓm)
Semimodules-CC = record
    { U = Semimodules
    ; cartesian = Semimodules-Cartesian
    }

module Semimodules-CC = CartesianCategory Semimodules-CC
