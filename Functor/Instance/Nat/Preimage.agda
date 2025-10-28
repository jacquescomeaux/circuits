{-# OPTIONS --without-K --safe #-}

module Functor.Instance.Nat.Preimage where

open import Categories.Category.Instance.Nat using (Natop)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Data.Fin.Base using (Fin)
open import Data.Bool.Base using (Bool)
open import Data.Nat.Base using (ℕ)
open import Data.Subset.Functional using (Subset)
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid using (≋-setoid)
open import Function.Base using (id; _∘_)
open import Function.Bundles using (Func; _⟶ₛ_)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (setoid; _∙_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

open Functor
open Func

_≈_ : {X Y : Setoid 0ℓ 0ℓ} → Rel (X ⟶ₛ Y) 0ℓ
_≈_ {X} {Y} = Setoid._≈_ (setoid X Y)
infixr 4 _≈_

private
  variable A B C : ℕ

-- action on objects (Subset n)
Subsetₛ : ℕ → Setoid 0ℓ 0ℓ
Subsetₛ = ≋-setoid (≡.setoid Bool)

-- action of Preimage on morphisms (contravariant)
Preimage₁ : (Fin A → Fin B) → Subsetₛ B ⟶ₛ Subsetₛ A
to (Preimage₁ f) i = i ∘ f
cong (Preimage₁ f) x≗y = x≗y ∘ f

-- Preimage respects identity
Preimage-identity : Preimage₁ id ≈ Id (Subsetₛ A)
Preimage-identity {A} = Setoid.refl (Subsetₛ A)

-- Preimage flips composition
Preimage-homomorphism
    : {A B C : ℕ}
      (f : Fin A → Fin B)
      (g : Fin B → Fin C)
    → Preimage₁ (g ∘ f) ≈ Preimage₁ f ∙ Preimage₁ g
Preimage-homomorphism {A} _ _ = Setoid.refl (Subsetₛ A)

-- Preimage respects equality
Preimage-resp-≈
    : {f g : Fin A → Fin B}
    → f ≗ g
    → Preimage₁ f ≈ Preimage₁ g
Preimage-resp-≈ f≗g {v} = ≡.cong v ∘ f≗g

-- the Preimage functor
Preimage : Functor Natop (Setoids 0ℓ 0ℓ)
F₀ Preimage = Subsetₛ
F₁ Preimage = Preimage₁
identity Preimage = Preimage-identity
homomorphism Preimage {f = f} {g} {v} = Preimage-homomorphism g f {v}
F-resp-≈ Preimage = Preimage-resp-≈
