{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_; suc)

module Preorder.Primitive where

import Relation.Binary.Bundles as SetoidBased using (Preorder)

open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; IsEquivalence)

-- A primitive preorder is a type with a reflexive and transitive
-- relation (in other words, a preorder). The "primitive" qualifier
-- is used to distinguish it from preorders in the Agda standard library,
-- which include an underlying equivalence relation on the carrier set.

record Preorder (c ℓ : Level) : Set (suc (c ⊔ ℓ)) where

  field
    Carrier : Set c
    _≲_ : Rel Carrier ℓ
    refl : Reflexive _≲_
    trans : Transitive _≲_

  infix 4 _≲_

-- Isomorphism in a primitive preorder

module Isomorphism {c ℓ : Level} (P : Preorder c ℓ) where

  open Preorder P

  record _≅_ (x y : Carrier) : Set ℓ where
    field
      from : x ≲ y
      to : y ≲ x

  infix 4 _≅_

  private

    ≅-refl : Reflexive _≅_
    ≅-refl = record
        { from = refl
        ; to = refl
        }

    ≅-sym : Symmetric _≅_
    ≅-sym x≅y = let open _≅_ x≅y in record
        { from = to
        ; to = from
        }

    ≅-trans : Transitive _≅_
    ≅-trans x≅y y≅z = let open _≅_ in record
        { from = trans (from x≅y) (from y≅z)
        ; to = trans (to y≅z) (to x≅y)
        }

  ≅-isEquivalence : IsEquivalence _≅_
  ≅-isEquivalence = record
      { refl = ≅-refl
      ; sym = ≅-sym
      ; trans = ≅-trans
      }

  module ≅ = IsEquivalence ≅-isEquivalence

-- Every primitive preorder can be extended to a setoid-based preorder
-- using isomorphism (_≅_) as the underlying equivalence relation.
setoidBased : {c ℓ : Level} → Preorder c ℓ → SetoidBased.Preorder c ℓ ℓ
setoidBased P = record
    { Carrier = Carrier
    ; _≈_ = _≅_
    ; _≲_ = _≲_
    ; isPreorder = record
        { isEquivalence = ≅-isEquivalence
        ; reflexive = _≅_.from
        ; trans = trans
        }
    }
  where
    open Preorder P
    open Isomorphism P
