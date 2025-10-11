{-# OPTIONS --without-K --safe #-}

module Functor.Instance.Nat.Pull where

open import Categories.Category.Core using (module Category)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Data.Circuit.Merge using (merge; merge-cong₁; merge-cong₂; merge-⁅⁆; merge-preimage)
open import Data.Circuit.Value using (Value)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Preimage using (preimage; preimage-cong₁)
open import Data.Nat.Base using (ℕ)
open import Data.Subset.Functional using (⁅_⁆)
open import Data.Vec.Functional.Relation.Binary.Equality.Setoid using (≋-setoid)
open import Function.Base using (id; flip; _∘_)
open import Function.Bundles using (Func; _⟶ₛ_)
open import Function.Construct.Identity using () renaming (function to Id)
open import Function.Construct.Setoid using (setoid; _∙_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.PropositionalEquality as ≡ using (_≗_)

open Functor
open Func

module Nat = Category Nat

_≈_ : {X Y : Setoid 0ℓ 0ℓ} → Rel (X ⟶ₛ Y) 0ℓ
_≈_ {X} {Y} = Setoid._≈_ (setoid X Y)
infixr 4 _≈_

private
  variable A B C : ℕ

-- action on objects (Vector Value n)
Values : ℕ → Setoid 0ℓ 0ℓ
Values = ≋-setoid (≡.setoid Value)

-- action of Pull on morphisms (contravariant)
Pull₁ : (Fin A → Fin B) → Values B ⟶ₛ Values A
to (Pull₁ f) i = i ∘ f
cong (Pull₁ f) x≗y = x≗y ∘ f

-- Pull respects identity
Pull-identity : Pull₁ id ≈ Id (Values A)
Pull-identity {A} = Setoid.refl (Values A)

-- Pull flips composition
Pull-homomorphism
    : {A B C : ℕ}
      (f : Fin A → Fin B)
      (g : Fin B → Fin C)
    → Pull₁ (g ∘ f) ≈ Pull₁ f ∙ Pull₁ g
Pull-homomorphism {A} _ _ = Setoid.refl (Values A)

-- Pull respects equality
Pull-resp-≈
    : {f g : Fin A → Fin B}
    → f ≗ g
    → Pull₁ f ≈ Pull₁ g
Pull-resp-≈ f≗g {v} = ≡.cong v ∘ f≗g

-- the Pull functor
Pull : Functor Nat.op (Setoids 0ℓ 0ℓ)
F₀ Pull = Values
F₁ Pull = Pull₁
identity Pull = Pull-identity
homomorphism Pull {f = f} {g} {v} = Pull-homomorphism g f {v}
F-resp-≈ Pull = Pull-resp-≈
