{-# OPTIONS --without-K --safe #-}

module Functor.Forgetful.Instance.Preorder where

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Category.Instance.Preorders using (Preorders)
open import Level using (Level)
open import Relation.Binary.Bundles using (Preorder)
open import Relation.Binary.Morphism using (PreorderHomomorphism)

-- Get the underlying setoid of a preorder.
-- This is not the same thing as the setoid induced by _≲_.

Forget : {c ℓ e : Level} → Functor (Preorders c ℓ e) (Setoids c ℓ)
Forget = let open Preorder.Eq in record
    { F₀ = setoid
    ; F₁ = λ F → let open PreorderHomomorphism F in record
        { to = ⟦_⟧
        ; cong = cong
        }
    ; identity = λ {A} → refl A
    ; homomorphism = λ {_ _ Z} → refl Z
    ; F-resp-≈ = λ f≗g → f≗g
    }
