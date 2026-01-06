{-# OPTIONS --without-K --safe #-}

module Functor.Free.Instance.Preorder where

open import Categories.Category using (Category)
open import Categories.Category.Instance.Cats using (Cats)
open import Function using (flip)
open import Categories.Functor using (Functor; _∘F_)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)
open import Category.Instance.Preorders.Primitive using (Preorders)
open import Level using (Level; _⊔_; suc)
open import Preorder.Primitive using (Preorder; module Isomorphism)
open import Preorder.Primitive.MonotoneMap using (MonotoneMap; _≃_; module ≃)
 
-- The "free preorder" of a category
-- i.e. (0,1)-truncation

-- In this setting, a category is a proof-relevant preorder,
-- i.e. each proof of A ≤ B is a distinct morphism.

-- To get a preorder from a category,
-- we ignore this distinction,
-- making all morphisms A ⇒ B "the same".
-- Identity and composition become reflexivity and transitivity.

-- Likewise, we can get a monotone map from a functor,
-- and a pointwise isomorphism of monotone maps from
-- a natural isomorphism of functors, simply by
-- forgetting morphism equalities.

module _ {o ℓ e : Level} where

  preorder : Category o ℓ e → Preorder o ℓ
  preorder C = let open Category C in record
      { Carrier = Obj
      ; _≲_ = _⇒_
      ; refl = id
      ; trans = flip _∘_
      }

  module _ {A B : Category o ℓ e} where

    monotoneMap : Functor A B → MonotoneMap (preorder A) (preorder B)
    monotoneMap F = let open Functor F in record
        { map = F₀
        ; mono = F₁
        }

    open NaturalIsomorphism using (module ⇒; module ⇐)

    pointwiseIsomorphism : {F G : Functor A B} → NaturalIsomorphism F G → monotoneMap F ≃ monotoneMap G
    pointwiseIsomorphism F≃G X = record
        { from = ⇒.η F≃G X
        ; to = ⇐.η F≃G X
        }

Free : {o ℓ e : Level} → Functor (Cats o ℓ e) (Preorders o ℓ)
Free = record
    { F₀ = preorder
    ; F₁ = monotoneMap
    ; identity = ≃.refl {x = id}
    ; homomorphism = λ {f = f} {h} → ≃.refl {x = monotoneMap (h ∘F f)}
    ; F-resp-≈ = pointwiseIsomorphism
    }
  where
    open Category (Preorders _ _) using (id)

module Free {o ℓ e} = Functor (Free {o} {ℓ} {e})
