{-# OPTIONS --without-K --safe #-}

open import Algebra using (CommutativeSemiring)
open import Level using (Level)

module Functor.Forgetful.Instance.Semimodule {c ℓ m ℓm : Level} (R : CommutativeSemiring c ℓ) where

open import Algebra.Module using (Semimodule)
open import Categories.Functor using (Functor)
open import Category.Instance.CMonoids using (CMonoids; CMonoidHomomorphism; mk-⇒)
open import Category.Instance.Semimodules {c} {ℓ} {m} {ℓm} R using (Semimodules; SemimoduleHomomorphism)
open import Function using (id)

open Semimodule

map : {M N : Semimodule R m ℓm}
    → SemimoduleHomomorphism M N
    → CMonoidHomomorphism m ℓm (+ᴹ-commutativeMonoid M) (+ᴹ-commutativeMonoid N)
map f = mk-⇒ record
    { ⟦_⟧ = ⟦_⟧
    ; isMonoidHomomorphism = +ᴹ-isMonoidHomomorphism
    }
  where
    open SemimoduleHomomorphism f

+-CMonoid : Functor Semimodules (CMonoids m ℓm)
+-CMonoid = record
    { F₀ = +ᴹ-commutativeMonoid
    ; F₁ = map
    ; identity = λ {A} x → ≈ᴹ-refl A {x}
    ; homomorphism = λ {_ _ C} _ → ≈ᴹ-refl C
    ; F-resp-≈ = id
    }

module +-CMonoid = Functor +-CMonoid
