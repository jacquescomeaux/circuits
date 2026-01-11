{-# OPTIONS --without-K --safe #-}

module Functor.Instance.Nat.Push where

open import Level using (0ℓ)
open import Category.Instance.Setoids.SymmetricMonoidal {0ℓ} {0ℓ} using (Setoids-×)

open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Category.Construction.CMonoids Setoids-×.symmetric using (CMonoids)
open import Data.Circuit.Value using (Monoid)
open import Data.Fin using (Fin)
open import Data.Fin.Preimage using (preimage; preimage-cong₁)
open import Data.Nat using (ℕ)
open import Data.Setoid using (∣_∣; _⇒ₛ_)
open import Data.Subset.Functional using (⁅_⁆)
open import Data.System.Values Monoid using (Values; module Object; _⊕_; <ε>; _≋_; ≋-isEquiv; merge; push; merge-⊕; merge-<ε>; merge-cong; merge-⁅⁆; merge-push; merge-cong₂; lookup)
open import Function using (Func; _⟶ₛ_; _⟨$⟩_; _∘_; id)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (_∙_)
open import Object.Monoid.Commutative Setoids-×.symmetric using (CommutativeMonoid; CommutativeMonoid⇒)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

open Func
open Functor
open Object using (Valuesₘ)

private

  variable A B C : ℕ

-- Push sends a natural number n to Values n
Push₀ : ℕ → CommutativeMonoid
Push₀ n = Valuesₘ n

-- action of Push on morphisms (covariant)

opaque

  unfolding Values

  open CommutativeMonoid using (Carrier)
  open CommutativeMonoid⇒ using (arr)

  -- setoid morphism
  Pushₛ : (Fin A → Fin B) → Values A ⟶ₛ Values B
  Pushₛ f .to v = merge v ∘ preimage f ∘ ⁅_⁆
  Pushₛ f .cong x≗y i = merge-cong (preimage f ⁅ i ⁆) x≗y

private opaque

  unfolding Pushₛ _⊕_

  Push-⊕
      : (f : Fin A → Fin B)
      → (xs ys : ∣ Values A ∣)
      → Pushₛ f ⟨$⟩ (xs ⊕ ys)
      ≋ (Pushₛ f ⟨$⟩ xs) ⊕ (Pushₛ f ⟨$⟩ ys)
  Push-⊕ f xs ys i = merge-⊕ xs ys (preimage f ⁅ i ⁆)

  Push-<ε>
      : (f : Fin A → Fin B)
      → Pushₛ f ⟨$⟩ <ε> ≋ <ε>
  Push-<ε> f i = merge-<ε> (preimage f ⁅ i ⁆)

opaque

  unfolding Valuesₘ ≋-isEquiv

  -- monoid morphism
  Pushₘ : (Fin A → Fin B) → CommutativeMonoid⇒ (Valuesₘ A) (Valuesₘ B)
  Pushₘ f = record
      { monoid⇒ = record
          { arr = Pushₛ f
          ; preserves-μ = Push-⊕ f _ _
          ; preserves-η = Push-<ε> f
          }
      }

private opaque

  unfolding Pushₘ Pushₛ push lookup

  -- Push respects identity
  Push-identity
    : (open Setoid (Carrier (Push₀ A) ⇒ₛ Carrier (Push₀ A)))
    → arr (Pushₘ id) ≈ Id (Carrier (Push₀ A))
  Push-identity {_} {v} i = merge-⁅⁆ v i

  -- Push respects composition
  Push-homomorphism
      : {f : Fin A → Fin B}
        {g : Fin B → Fin C}
      → (open Setoid (Carrier (Push₀ A) ⇒ₛ Carrier (Push₀ C)))
      → arr (Pushₘ (g ∘ f)) ≈ arr (Pushₘ g) ∙ arr (Pushₘ f)
  Push-homomorphism {f = f} {g} {v} = merge-push f g v

  -- Push respects equality
  Push-resp-≈
      : {f g : Fin A → Fin B}
      → f ≗ g
      → (open Setoid (Carrier (Push₀ A) ⇒ₛ Carrier (Push₀ B)))
      → arr (Pushₘ f) ≈ arr (Pushₘ g)
  Push-resp-≈ f≗g {v} = merge-cong₂ v ∘ preimage-cong₁ f≗g ∘ ⁅_⁆

-- the Push functor
Push : Functor Nat CMonoids
Push .F₀ = Push₀
Push .F₁ = Pushₘ
Push .identity = Push-identity
Push .homomorphism = Push-homomorphism
Push .F-resp-≈ = Push-resp-≈

module Push = Functor Push
