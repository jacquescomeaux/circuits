{-# OPTIONS --without-K --safe #-}

open import Level using (Level)

module Functor.Free.Instance.InducedMonoid {c ℓ : Level} where

-- The induced monoid of a monoidal preorder

open import Category.Instance.Setoids.SymmetricMonoidal {c} {ℓ} using (Setoids-×; ×-monoidal′)
open import Categories.Object.Monoid Setoids-×.monoidal using (Monoid; Monoid⇒)
open import Categories.Category.Construction.Monoids Setoids-×.monoidal using (Monoids)
open import Categories.Functor using (Functor)
open import Category.Instance.Preorder.Primitive.Monoidals.Strong using (Monoidals)
open import Category.Cartesian.Instance.Preorders.Primitive using (Preorders-CC; ⊤ₚ)
open import Preorder.Primitive using (Preorder)
open import Preorder.Primitive.Monoidal using (MonoidalPreorder; _×ₚ_)
open import Preorder.Primitive.MonotoneMap.Monoidal.Strong using (MonoidalMonotone)
open import Preorder.Primitive using (module Isomorphism)
open import Data.Product using (_,_)
open import Functor.Cartesian.Instance.InducedSetoid using () renaming (module InducedSetoid to IS)
open import Function using (Func; _⟨$⟩_)
open import Function.Construct.Setoid using (_∙_)
open import Data.Setoid.Unit using (⊤ₛ)
open import Data.Setoid using (∣_∣)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (_×ₛ_)
open import Function.Construct.Constant using () renaming (function to Const)
open import Function.Construct.Identity using () renaming (function to Id)
open import Relation.Binary using (Setoid)

open Setoids-× using (_⊗₀_; _⊗₁_; module unitorˡ; module unitorʳ; module associator; _≈_)

module _ (P : MonoidalPreorder c ℓ) where

  open MonoidalPreorder P
  open Isomorphism U using (module ≅; _≅_)

  M : Setoid c ℓ
  M = IS.₀ U

  opaque
    unfolding ×-monoidal′
    μ : Func (M ⊗₀ M) M
    μ = IS.₁ tensor ∙ IS.×-iso.to U U

  η : Func Setoids-×.unit M
  η = Const Setoids-×.unit M unit

  opaque
    unfolding μ
    assoc : μ ∙ μ ⊗₁ Id M ≈ μ ∙ Id M ⊗₁ μ ∙ associator.from
    assoc {(x , y) , z} = associative x y z

    identityˡ : unitorˡ.from ≈ μ ∙ η ⊗₁ Id M
    identityˡ {_ , x} = ≅.sym (unitaryˡ x)

    identityʳ : unitorʳ.from ≈ μ ∙ Id M ⊗₁ η
    identityʳ {x , _} = ≅.sym (unitaryʳ x)

  ≅-monoid : Monoid
  ≅-monoid = record
      { Carrier = M
      ; isMonoid = record
          { μ = μ
          ; η = Const Setoids-×.unit M unit
          ; assoc = assoc
          ; identityˡ = identityˡ
          ; identityʳ = identityʳ
          }
      }

module _ {A B : MonoidalPreorder c ℓ} (f : MonoidalMonotone A B) where

  private
    module A = MonoidalPreorder A
    module B = MonoidalPreorder B

  open Isomorphism B.U using (_≅_; module ≅)
  open MonoidalMonotone f

  opaque
    unfolding μ
    preserves-μ
        : {x : ∣ IS.₀ A.U ⊗₀ IS.₀ A.U ∣}
        → map (μ A ⟨$⟩ x)
        ≅ μ B ⟨$⟩ (IS.₁ F ⊗₁ IS.₁ F ⟨$⟩ x)
    preserves-μ {x , y} = ≅.sym (⊗-homo x y)

  monoid⇒ : Monoid⇒ (≅-monoid A) (≅-monoid B)
  monoid⇒ = record
      { arr = IS.₁ F
      ; preserves-μ = preserves-μ
      ; preserves-η = ≅.sym ε
      }

InducedMonoid : Functor (Monoidals c ℓ) Monoids
InducedMonoid = record
    { F₀ = ≅-monoid
    ; F₁ = monoid⇒
    ; identity = λ {A} {x} → ≅.refl (U A)
    ; homomorphism = λ {Z = Z} → ≅.refl (U Z)
    ; F-resp-≈ = λ f≃g {x} → f≃g x
    }
  where
    open MonoidalPreorder using (U)
    open Isomorphism using (module ≅)

module InducedMonoid = Functor InducedMonoid
