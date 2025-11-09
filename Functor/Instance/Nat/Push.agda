{-# OPTIONS --without-K --safe #-}

module Functor.Instance.Nat.Push where

open import Categories.Functor using (Functor)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Data.Circuit.Merge using (merge; merge-cong₁; merge-cong₂; merge-⁅⁆; merge-preimage)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Preimage using (preimage; preimage-cong₁)
open import Data.Nat.Base using (ℕ)
open import Data.Subset.Functional using (⁅_⁆)
open import Function.Base using (id; _∘_)
open import Function.Bundles using (Func; _⟶ₛ_)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (setoid; _∙_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)
open import Data.Circuit.Value using (Monoid)
open import Data.System.Values Monoid using (Values)
open import Data.Unit using (⊤; tt)

open Func
open Functor

-- Push sends a natural number n to Values n

private

  variable A B C : ℕ

  _≈_ : {X Y : Setoid 0ℓ 0ℓ} → Rel (X ⟶ₛ Y) 0ℓ
  _≈_ {X} {Y} = Setoid._≈_ (setoid X Y)
  infixr 4 _≈_

  opaque

    unfolding Values

    -- action of Push on morphisms (covariant)
    Push₁ : (Fin A → Fin B) → Values A ⟶ₛ Values B
    to (Push₁ f) v = merge v ∘ preimage f ∘ ⁅_⁆
    cong (Push₁ f) x≗y = merge-cong₁ x≗y ∘ preimage f ∘ ⁅_⁆

    -- Push respects identity
    Push-identity : Push₁ id ≈ Id (Values A)
    Push-identity {_} {v} = merge-⁅⁆ v

    -- Push respects composition
    Push-homomorphism
        : {f : Fin A → Fin B}
          {g : Fin B → Fin C}
        → Push₁ (g ∘ f) ≈ Push₁ g ∙ Push₁ f
    Push-homomorphism {f = f} {g} {v} = merge-preimage f v ∘ preimage g ∘ ⁅_⁆

    -- Push respects equality
    Push-resp-≈
        : {f g : Fin A → Fin B}
        → f ≗ g
        → Push₁ f ≈ Push₁ g
    Push-resp-≈ f≗g {v} = merge-cong₂ v ∘ preimage-cong₁ f≗g ∘ ⁅_⁆

opaque

  unfolding Push₁

  Push-defs : ⊤
  Push-defs = tt

-- the Push functor
Push : Functor Nat (Setoids 0ℓ 0ℓ)
F₀ Push = Values
F₁ Push = Push₁
identity Push = Push-identity
homomorphism Push = Push-homomorphism
F-resp-≈ Push = Push-resp-≈

module Push = Functor Push
