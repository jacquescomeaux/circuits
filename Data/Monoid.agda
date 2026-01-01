{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Data.Monoid {c ℓ : Level} where

import Algebra.Bundles as Alg

open import Algebra.Morphism using (IsMonoidHomomorphism)
open import Categories.Object.Monoid using (Monoid; Monoid⇒)
open import Category.Instance.Setoids.SymmetricMonoidal {c} {ℓ} using (Setoids-×; ×-monoidal′)
open import Data.Product using (curry′; uncurry′; _,_; Σ)
open import Data.Setoid using (∣_∣)
open import Data.Setoid.Unit using (⊤ₛ)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Constant using () renaming (function to Const)
open import Function.Construct.Identity using () renaming (function to Id)
open import Relation.Binary using (Setoid)

open Func

-- A monoid object in the (monoidal) category of setoids is just a monoid

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

module FromMonoid (M : Alg.Monoid c ℓ) where

  open Alg.Monoid M
  open Setoids-× using (_⊗₁_; _⊗₀_; _∘_; unit; module unitorˡ; module unitorʳ; module associator)

  opaque

    unfolding ×-monoidal′

    μ : setoid ⊗₀ setoid ⟶ₛ setoid
    μ .to = uncurry′ _∙_
    μ .cong = uncurry′ ∙-cong

    η : unit ⟶ₛ setoid
    η = Const ⊤ₛ setoid ε

  opaque

    unfolding μ

    μ-assoc
        : {x : ∣ (setoid ⊗₀ setoid) ⊗₀ setoid ∣}
        → μ ∘ μ ⊗₁ Id setoid ⟨$⟩ x
        ≈ μ ∘ Id setoid ⊗₁ μ ∘ associator.from ⟨$⟩ x
    μ-assoc {(x , y) , z} = assoc x y z

    μ-identityˡ
        : {x : ∣ unit ⊗₀ setoid ∣}
        → unitorˡ.from ⟨$⟩ x
        ≈ μ ∘ η ⊗₁ Id setoid ⟨$⟩ x
    μ-identityˡ {_ , x} = sym (identityˡ x)

    μ-identityʳ
        : {x : ∣ setoid ⊗₀ unit ∣}
        → unitorʳ.from ⟨$⟩ x
        ≈ μ ∘ Id setoid ⊗₁ η ⟨$⟩ x
    μ-identityʳ {x , _} = sym (identityʳ x)

  fromMonoid : Monoid Setoids-×.monoidal
  fromMonoid = record
      { Carrier = setoid
      ; isMonoid = record
          { μ = μ
          ; η = η
          ; assoc = μ-assoc
          ; identityˡ = μ-identityˡ
          ; identityʳ = μ-identityʳ
          }
      }

open FromMonoid using (fromMonoid) public

-- A morphism of monoids in the (monoidal) category of setoids is a monoid homomorphism

module  _ (M N : Monoid Setoids-×.monoidal) where

  module M = Alg.Monoid (toMonoid M)
  module N = Alg.Monoid (toMonoid N)

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
