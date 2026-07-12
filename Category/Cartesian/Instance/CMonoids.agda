{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)

module Category.Cartesian.Instance.CMonoids {c ℓ : Level} where

import Algebra.Construct.DirectProduct as ×
import Algebra.Construct.Terminal as Term
import Algebra.Morphism.Construct.DirectProduct as ×-⇒
import Algebra.Morphism.Construct.Terminal as Term-⇒

open import Algebra using (CommutativeMonoid)
open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.Cartesian.Bundle using (CartesianCategory)
open import Categories.Object.Terminal using (Terminal)
open import Category.Instance.CMonoids c ℓ using (CMonoids; CMonoidHomomorphism; mk-⇒)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic using (tt)

open CMonoidHomomorphism using (isMonoidHomomorphism)
open CommutativeMonoid using (rawMonoid; refl; sym)

terminal : Terminal CMonoids
terminal = record
    { ⊤ = Term.commutativeMonoid
    ; ⊤-is-terminal = record
        { ! = λ {M} → mk-⇒ record { isMonoidHomomorphism = Term-⇒.isMonoidHomomorphism (rawMonoid M) }
        ; !-unique = λ _ _ → tt
        }
    }

products : BinaryProducts CMonoids
products = record
    { product = λ {M N} → record
        { A×B = ×.commutativeMonoid M N
        ; π₁ = mk-⇒ record { isMonoidHomomorphism = ×-⇒.Monoid-Export.proj₁ {refl = refl M} }
        ; π₂ = mk-⇒ record { isMonoidHomomorphism = ×-⇒.Monoid-Export.proj₂ {refl = refl N} }
        ; ⟨_,_⟩ = λ {C} f g → mk-⇒ record
            { isMonoidHomomorphism = ×-⇒.Monoid-Export.< isMonoidHomomorphism f , isMonoidHomomorphism g > }
        ; project₁ = λ _ → refl M
        ; project₂ = λ _ → refl N
        ; unique = λ eq₁ eq₂ x → sym M (eq₁ x) , sym N (eq₂ x)
        }
    }

CMonoids-Cartesian : Cartesian CMonoids
CMonoids-Cartesian = record
    { terminal = terminal
    ; products = products
    }

CMonoids-CC : CartesianCategory (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
CMonoids-CC = record { cartesian = CMonoids-Cartesian }

module CMonoids-CC = CartesianCategory CMonoids-CC
