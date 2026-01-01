{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
module Data.CMonoid {c ℓ : Level} where

import Algebra.Bundles as Alg

open import Algebra.Morphism using (IsMonoidHomomorphism)
open import Categories.Object.Monoid using (Monoid)
open import Category.Instance.Setoids.SymmetricMonoidal {c} {ℓ} using (Setoids-×; ×-symmetric′)
open import Data.Monoid {c} {ℓ} using (toMonoid; fromMonoid; toMonoid⇒; module FromMonoid)
open import Data.Product using (_,_; Σ)
open import Function using (Func; _⟨$⟩_; _⟶ₛ_)
open import Object.Monoid.Commutative using (CommutativeMonoid; CommutativeMonoid⇒)

open Func

-- A commutative monoid object in the (symmetric monoidal) category of setoids
-- is just a commutative monoid

toCMonoid : CommutativeMonoid Setoids-×.symmetric → Alg.CommutativeMonoid c ℓ
toCMonoid M = record
    { M
    ; isCommutativeMonoid = record
        { isMonoid = M.isMonoid
        ; comm = comm
        }
    }
  where
    open CommutativeMonoid M using (monoid; commutative; μ)
    module M = Alg.Monoid (toMonoid monoid)
    opaque
      unfolding toMonoid
      comm : (x y : M.Carrier) → x M.∙ y M.≈ y M.∙ x
      comm x y = commutative {x , y}

fromCMonoid : Alg.CommutativeMonoid c ℓ → CommutativeMonoid Setoids-×.symmetric
fromCMonoid M = record
    { M
    ; isCommutativeMonoid = record
        { isMonoid = M.isMonoid
        ; commutative = commutative
        }
    }
  where
    open Alg.CommutativeMonoid M using (monoid; comm)
    module M = Monoid (fromMonoid monoid)
    open Setoids-× using (_≈_; _∘_; module braiding)
    opaque
      unfolding FromMonoid.μ
      commutative : M.μ ≈ M.μ ∘ braiding.⇒.η _
      commutative {x , y} = comm x y

-- A morphism of monoids in the (monoidal) category of setoids is a monoid homomorphism

module  _ (M N : CommutativeMonoid Setoids-×.symmetric) where

  module M = Alg.CommutativeMonoid (toCMonoid M)
  module N = Alg.CommutativeMonoid (toCMonoid N)

  open CommutativeMonoid
  open CommutativeMonoid⇒

  toCMonoid⇒
      : CommutativeMonoid⇒ Setoids-×.symmetric M N
      → Σ (M.setoid ⟶ₛ N.setoid) (λ f
      → IsMonoidHomomorphism M.rawMonoid N.rawMonoid (to f))
  toCMonoid⇒ f = toMonoid⇒ (monoid M) (monoid N) (monoid⇒ f)
