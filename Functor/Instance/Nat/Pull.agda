{-# OPTIONS --without-K --safe #-}

module Functor.Instance.Nat.Pull where

open import Level using (0ℓ)

open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} {0ℓ} using (Setoids-×)

open import Categories.Category.Instance.Nat using (Natop)
open import Categories.Functor using (Functor)
open import Category.Construction.CMonoids Setoids-×.symmetric using (CMonoids)
open import Data.CMonoid using (fromCMonoid)
open import Data.Circuit.Value using (monoid)
open import Data.Fin.Base using (Fin)
open import Data.Monoid using (fromMonoid)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_)
open import Data.Setoid using (∣_∣; _⇒ₛ_)
open import Data.Values monoid using (Values; _⊕_; module Object)
open import Data.Unit using (⊤; tt)
open import Function.Base using (id; _∘_)
open import Function.Bundles using (Func; _⟶ₛ_; _⟨$⟩_)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (setoid; _∙_)
open import Object.Monoid.Commutative Setoids-×.symmetric using (CommutativeMonoid; CommutativeMonoid⇒)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

open CommutativeMonoid using (Carrier; monoid)
open CommutativeMonoid⇒ using (arr)
open Functor
open Func
open Object using (Valuesₘ)

private

  variable A B C : ℕ

-- Pull takes a natural number n to the commutative monoid Valuesₘ n

Pull₀ : ℕ → CommutativeMonoid
Pull₀ n = Valuesₘ n

-- action of Pull on morphisms (contravariant)

-- setoid morphism
opaque
  unfolding Valuesₘ Values
  Pullₛ : (Fin A → Fin B) → Carrier (Pull₀ B) ⟶ₛ Carrier (Pull₀ A)
  Pullₛ f .to x = x ∘ f
  Pullₛ f .cong x≗y = x≗y ∘ f

-- monoid morphism
opaque
  unfolding _⊕_ Pullₛ
  Pullₘ : (Fin A → Fin B) → CommutativeMonoid⇒ (Pull₀ B) (Pull₀ A)
  Pullₘ {A} f = record
      { monoid⇒ = record
          { arr = Pullₛ f
          ; preserves-μ = Setoid.refl (Values A)
          ; preserves-η = Setoid.refl (Values A)
          }
      }

-- Pull respects identity
opaque
  unfolding Pullₘ
  Pull-identity
      : (open Setoid (Carrier (Pull₀ A) ⇒ₛ Carrier (Pull₀ A)))
      → arr (Pullₘ id) ≈ Id (Carrier (Pull₀ A))
  Pull-identity {A} = Setoid.refl (Values A)

-- Pull flips composition
opaque
  unfolding Pullₘ
  Pull-homomorphism
      : (f : Fin A → Fin B)
        (g : Fin B → Fin C)
        (open Setoid (Carrier (Pull₀ C) ⇒ₛ Carrier (Pull₀ A)))
      → arr (Pullₘ (g ∘ f)) ≈ arr (Pullₘ f) ∙ arr (Pullₘ g)
  Pull-homomorphism {A} _ _ = Setoid.refl (Values A)

-- Pull respects equality
opaque
  unfolding Pullₘ
  Pull-resp-≈
      : {f g : Fin A → Fin B}
      → f ≗ g
      → (open Setoid (Carrier (Pull₀ B) ⇒ₛ Carrier (Pull₀ A)))
      → arr (Pullₘ f) ≈ arr (Pullₘ g)
  Pull-resp-≈ f≗g {v} = ≡.cong v ∘ f≗g

Pull : Functor Natop CMonoids
Pull .F₀ = Pull₀
Pull .F₁ = Pullₘ
Pull .identity = Pull-identity
Pull .homomorphism = Pull-homomorphism _ _
Pull .F-resp-≈ = Pull-resp-≈

module Pull = Functor Pull
