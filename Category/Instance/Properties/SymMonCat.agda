{-# OPTIONS --without-K --safe #-}
{-# OPTIONS --lossy-unification #-}

open import Level using (Level; suc; _⊔_)
module Category.Instance.Properties.SymMonCat {o ℓ e : Level} where

import Categories.Category.Monoidal.Reasoning as ⊗-Reasoning
import Categories.Morphism.Reasoning as ⇒-Reasoning
import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal.Symmetric as SMNI
import Categories.Functor.Monoidal.Symmetric {o} {o} {ℓ} {ℓ} {e} {e} as SMF

open import Category.Instance.SymMonCat {o} {ℓ} {e} using (SymMonCat)

open import Categories.Category using (Category; _[_≈_]; _[_∘_])
open import Categories.Object.Product.Core SymMonCat using (Product)
open import Categories.Object.Terminal SymMonCat using (Terminal)
open import Categories.Category.Instance.One using (One)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Cartesian SymMonCat using (Cartesian)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Category.BinaryProducts SymMonCat using (BinaryProducts)
open import Categories.Functor.Monoidal.Construction.Product
  using ()
  renaming
    ( πˡ-SymmetricMonoidalFunctor to πˡ-SMF
    ; πʳ-SymmetricMonoidalFunctor to πʳ-SMF
    ; ※-SymmetricMonoidalFunctor to ※-SMF
    )
open import Categories.Category.Monoidal.Construction.Product using (Product-SymmetricMonoidalCategory)
open import Categories.Category.Product.Properties using () renaming (project₁ to p₁; project₂ to p₂; unique to u)
open import Data.Product.Base using (_,_; proj₁; proj₂)

open SMF.Lax using (SymmetricMonoidalFunctor)
open SMNI.Lax using (SymmetricMonoidalNaturalIsomorphism; id; isEquivalence)

module Cone
  {A B X : SymmetricMonoidalCategory o ℓ e}
  {F : SymmetricMonoidalFunctor X A}
  {G : SymmetricMonoidalFunctor X B} where

  module A = SymmetricMonoidalCategory A
  module B = SymmetricMonoidalCategory B
  module X = SymmetricMonoidalCategory X
  module F = SymmetricMonoidalFunctor X A F
  module G = SymmetricMonoidalFunctor X B G

  A×B : SymmetricMonoidalCategory o ℓ e
  A×B = (Product-SymmetricMonoidalCategory A B)

  πˡ : SymmetricMonoidalFunctor A×B A
  πˡ = πˡ-SMF {o} {ℓ} {e} {o} {ℓ} {e} {A} {B}

  πʳ : SymmetricMonoidalFunctor A×B B
  πʳ = πʳ-SMF {o} {ℓ} {e} {o} {ℓ} {e} {A} {B}

  module _ where
    open Category A.U
    open Equiv
    open ⇒-Reasoning A.U
    open ⊗-Reasoning A.monoidal
    project₁ : SymMonCat [ SymMonCat [ πˡ ∘ ※-SMF F G ] ≈ F ]
    project₁ = record
        { U = p₁ {o} {ℓ} {e} {o} {ℓ} {e} {o} {ℓ} {e} {A.U} {B.U} {X.U} {F.F} {G.F}
        ; F⇒G-isMonoidal = record
            { ε-compat = identityˡ ○ identityʳ
            ; ⊗-homo-compat = λ { {C} {D} → identityˡ ○ refl⟩∘⟨ sym A.⊗.identity }
            }
        }
    module _ (H : SymmetricMonoidalFunctor X A×B) (eq₁ : SymMonCat [ SymMonCat [ πˡ ∘ H ] ≈ F ]) where
      private
        module H = SymmetricMonoidalFunctor X A×B H
      open SymmetricMonoidalNaturalIsomorphism eq₁
      ε-compat₁ : ⇐.η X.unit A.∘ F.ε A.≈ H.ε .proj₁
      ε-compat₁ = refl⟩∘⟨ sym ε-compat ○ cancelˡ (iso.isoˡ X.unit) ○ identityʳ
      ⊗-homo-compat₁
          : ∀ {C D}
          → ⇐.η (X.⊗.₀ (C , D)) ∘ F.⊗-homo.η (C , D)
          ≈ H.⊗-homo.η (C , D) .proj₁ ∘ A.⊗.₁ (⇐.η C , ⇐.η D)
      ⊗-homo-compat₁ {C} {D} =
          insertʳ
              (sym ⊗-distrib-over-∘
              ○ iso.isoʳ C ⟩⊗⟨ iso.isoʳ D
              ○ A.⊗.identity)
          ○ (pullʳ (sym ⊗-homo-compat)
            ○ cancelˡ (iso.isoˡ (X.⊗.₀ (C , D)))
            ○ identityʳ) ⟩∘⟨refl

  module _ where
    open Category B.U
    open Equiv
    open ⇒-Reasoning B.U
    open ⊗-Reasoning B.monoidal
    project₂ : SymMonCat [ SymMonCat [ πʳ ∘ ※-SMF F G ] ≈ G ]
    project₂ = record
        { U = p₂ {o} {ℓ} {e} {o} {ℓ} {e} {o} {ℓ} {e} {A.U} {B.U} {X.U} {F.F} {G.F}
        ; F⇒G-isMonoidal = record
            { ε-compat = identityˡ ○ identityʳ
            ; ⊗-homo-compat = λ { {C} {D} → identityˡ ○ refl⟩∘⟨ sym B.⊗.identity }
            }
        }
    module _ (H : SymmetricMonoidalFunctor X A×B) (eq₂ : SymMonCat [ SymMonCat [ πʳ ∘ H ] ≈ G ]) where
      private
        module H = SymmetricMonoidalFunctor X A×B H
      open SymmetricMonoidalNaturalIsomorphism eq₂
      ε-compat₂ : ⇐.η X.unit ∘ G.ε ≈ H.ε .proj₂
      ε-compat₂ = refl⟩∘⟨ sym ε-compat ○ cancelˡ (iso.isoˡ X.unit) ○ identityʳ
      ⊗-homo-compat₂
          : ∀ {C D}
          → ⇐.η (X.⊗.₀ (C , D)) ∘ G.⊗-homo.η (C , D)
          ≈ H.⊗-homo.η (C , D) .proj₂ ∘ B.⊗.₁ (⇐.η C , ⇐.η D)
      ⊗-homo-compat₂ {C} {D} =
          insertʳ
              (sym ⊗-distrib-over-∘
              ○ iso.isoʳ C ⟩⊗⟨ iso.isoʳ D
              ○ B.⊗.identity)
          ○ (pullʳ (sym ⊗-homo-compat)
            ○ cancelˡ (iso.isoˡ (X.⊗.₀ (C , D)))
            ○ identityʳ) ⟩∘⟨refl

  unique
      : (H : SymmetricMonoidalFunctor X A×B)
      → SymMonCat [ SymMonCat [ πˡ ∘ H ] ≈ F ]
      → SymMonCat [ SymMonCat [ πʳ ∘ H ] ≈ G ]
      → SymMonCat [ ※-SMF F G ≈ H ]
  unique H eq₁ eq₂ = record
      { U = u {o} {ℓ} {e} {o} {ℓ} {e} {o} {ℓ} {e} {A.U} {B.U} {X.U} {F.F} {G.F} {H.F} eq₁.U eq₂.U
      ; F⇒G-isMonoidal = record
          { ε-compat = ε-compat₁ H eq₁ , ε-compat₂ H eq₂
          ; ⊗-homo-compat = ⊗-homo-compat₁ H eq₁ , ⊗-homo-compat₂ H eq₂
          }
      }
    where
      module H = SymmetricMonoidalFunctor X A×B H
      module eq₁ = SymmetricMonoidalNaturalIsomorphism eq₁
      module eq₂ = SymmetricMonoidalNaturalIsomorphism eq₂

prod-SymMonCat : ∀ {A B} → Product A B
prod-SymMonCat {A} {B} = record
    { A×B = Product-SymmetricMonoidalCategory A B
    ; π₁ = πˡ-SMF {o} {ℓ} {e} {o} {ℓ} {e} {A} {B}
    ; π₂ = πʳ-SMF {o} {ℓ} {e} {o} {ℓ} {e} {A} {B}
    ; ⟨_,_⟩ = ※-SMF
    ; project₁ = λ { {X} {f} {g} → Cone.project₁ {A} {B} {X} {f} {g} }
    ; project₂ = λ { {X} {f} {g} → Cone.project₂ {A} {B} {X} {f} {g} }
    ; unique = λ { {X} {h} {f} {g} eq₁ eq₂ → Cone.unique {A} {B} {X} {f} {g} h eq₁ eq₂ }
    }

SymMonCat-BinaryProducts : BinaryProducts
SymMonCat-BinaryProducts = record { product = prod-SymMonCat }

SymMonCat-Terminal : Terminal
SymMonCat-Terminal = record
    { ⊤ = record
        { U = One
        ; monoidal = _
        ; symmetric = _
        }
    ; ⊤-is-terminal = _
    }

SymMonCat-Cartesian : Cartesian
SymMonCat-Cartesian = record
    { terminal = SymMonCat-Terminal
    ; products = SymMonCat-BinaryProducts
    }
