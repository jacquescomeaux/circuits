{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
module Data.Monoid {c ℓ : Level} where

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Category.Instance.Setoids.SymmetricMonoidal {c} {ℓ} using (Setoids-×; ×-monoidal′)
open import Categories.Object.Monoid using (Monoid; Monoid⇒)

module Setoids-× = SymmetricMonoidalCategory Setoids-×

import Algebra.Bundles as Alg

open import Data.Setoid using (∣_∣)
open import Relation.Binary using (Setoid)
open import Function using (Func)
open import Data.Product using (curry′; uncurry′; _,_)
open Func

-- A monoid object in the (monoidal) category of setoids is just a monoid

open import Function.Construct.Constant using () renaming (function to Const)
open import Categories.Category.Instance.SingletonSet using () renaming (SingletonSetoid to ⊤ₛ)

opaque
  unfolding ×-monoidal′
  toMonoid : Monoid Setoids-×.monoidal → Alg.Monoid c ℓ
  toMonoid M = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _∙_ = curry′ (to μ)
      ; ε = to η _
      ; isMonoid = record
          { isSemigroup = record
              { isMagma = record
                  { isEquivalence = isEquivalence
                  ; ∙-cong = curry′ (cong μ)
                  }
              ; assoc = λ x y z → assoc {(x , y) , z}
              }
          ; identity = (λ x → sym (identityˡ {_ , x}) ) , λ x → sym (identityʳ {x , _})
          }
      }
    where
      open Monoid M renaming (Carrier to A)
      open Setoid A

  fromMonoid : Alg.Monoid c ℓ → Monoid Setoids-×.monoidal
  fromMonoid M = record
      { Carrier = setoid
      ; isMonoid = record
          { μ = record { to = uncurry′ _∙_ ; cong = uncurry′ ∙-cong }
          ; η = Const ⊤ₛ setoid ε
          ; assoc = λ { {(x , y) , z} → assoc x y z }
          ; identityˡ = λ { {_ , x} → sym (identityˡ x) }
          ; identityʳ = λ { {x , _} → sym (identityʳ x) }
          }
      }
    where
      open Alg.Monoid M

-- A morphism of monoids in the (monoidal) category of setoids is a monoid homomorphism

module  _ (M N : Monoid Setoids-×.monoidal) where

  module M = Alg.Monoid (toMonoid M)
  module N = Alg.Monoid (toMonoid N)

  open import Data.Product using (Σ; _,_)
  open import Function using (_⟶ₛ_)
  open import Algebra.Morphism using (IsMonoidHomomorphism)
  open Monoid⇒

  opaque

    unfolding toMonoid

    toMonoid⇒
        : Monoid⇒ Setoids-×.monoidal M N
        → Σ (M.setoid ⟶ₛ N.setoid) (λ f
        → IsMonoidHomomorphism M.rawMonoid N.rawMonoid (to f))
    toMonoid⇒ f = arr f , record
        { isMagmaHomomorphism = record
            { isRelHomomorphism = record { cong = cong (arr f) }
            ; homo = λ x y → preserves-μ f {x , y}
            }
        ; ε-homo = preserves-η f
        }
