{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Level using (Level)
open import Category.Dagger.Semiadditive using (IdempotentSemiadditiveDagger)

module Data.WiringDiagram.Core
    {o ℓ e : Level}
    {𝒞 : Category o ℓ e}
    (S : IdempotentSemiadditiveDagger 𝒞)
  where

open import Categories.Category.Monoidal.Utilities using (module Shorthands)
open import Relation.Binary using (IsEquivalence)

open Category 𝒞 using (Obj; _∘_; _⇒_; id; _≈_; module Equiv)
open IdempotentSemiadditiveDagger S using (_⊕₀_; _⊕₁_; p₂; +-monoidal; △; ▽; _†)
open Shorthands +-monoidal using (α⇒)

-- A "Box" is a pair of objects from the underlying category,
-- representing input and output ports
-- +-----------+
-- |           |
-- Aᵢ    A     Aₒ
-- |           |
-- +-----------+
record Box : Set o where

  constructor _□_

  field
    ᵢ : Obj
    ₒ : Obj

infix 4 _□_

-- A Wiring Diagram between two boxes
-- is a pair of morphisms from the underlying category
-- (which can be thought of as generalized relations):
-- 1. A relation from the output of the inner box
--    plus the input of the outer box to the input of
--    the inner box
-- 2. A relation from the output of the inner box
--    to the output of the outer box
-- This choice of definition gives a way to represent
-- feedback from output to input.
--
--          outer box (B)
-- +--------------------------------+
-- |                                |
-- |     /-------------------\      |
-- |     |                   |      |
-- |     |    +-------+      |      |
-- |     \----|       |      |      |
-- |  Aₒ ⊕ Bᵢ | inner |------+------|
-- |   ⇒ Aᵢ   |  box  |  Aₒ ⇒ Bₒ    |
-- |----------|  (A)  |  output     |
-- | input    |       |  relation   |
-- | relation +-------+             |
-- |                                |
-- +--------------------------------+
record WiringDiagram (A B : Box) : Set ℓ where

  constructor _⧈_

  private
    module A = Box A
    module B = Box B

  field
    input : A.ₒ ⊕₀ B.ᵢ ⇒ A.ᵢ
    output : A.ₒ ⇒ B.ₒ

infix 4 _⧈_

-- Two wiring diagrams are equivalent when their
-- input and output relations are equivalent as
-- morphism in the underlying category.
record _≈-⧈_ {A B : Box} (f g : WiringDiagram A B) : Set e where

  constructor _⌸_

  private

    module f = WiringDiagram f
    module g = WiringDiagram g

  field
    ≈i : f.input ≈ g.input
    ≈o : f.output ≈ g.output

infix 4 _≈-⧈_

-- Equivalence of boxes is a legitimate equivalence relation
module _ {A B : Box} where

  open Equiv

  ≈-refl : {x : WiringDiagram A B} → x ≈-⧈ x
  ≈-refl = refl ⌸ refl

  ≈-sym : {x y : WiringDiagram A B} → x ≈-⧈ y → y ≈-⧈ x
  ≈-sym (≈i ⌸ ≈o) = sym ≈i ⌸ sym ≈o

  ≈-trans : {x y z : WiringDiagram A B} → x ≈-⧈ y → y ≈-⧈ z → x ≈-⧈ z
  ≈-trans (≈i₁ ⌸ ≈o₁) (≈i₂ ⌸ ≈o₂) = trans ≈i₁ ≈i₂ ⌸ trans ≈o₁ ≈o₂

  ≈-isEquiv : IsEquivalence (_≈-⧈_ {A} {B})
  ≈-isEquiv = record
      { refl = ≈-refl
      ; sym = ≈-sym
      ; trans = ≈-trans
      }

-- The identity wiring diagram
id-⧈ : {A : Box} → WiringDiagram A A
id-⧈ = p₂ ⧈ id

-- Composition of wiring diagrams
_⌻_ : {A B C : Box} → WiringDiagram B C → WiringDiagram A B → WiringDiagram A C
_⌻_ {Aᵢ □ Aₒ} {Bᵢ □ Bₒ} {Cᵢ □ Cₒ} (f′ ⧈ g′) (f ⧈ g) = f″ ⧈ g′ ∘ g
  where
    f″ : Aₒ ⊕₀ Cᵢ ⇒ Aᵢ
    f″ = f ∘ id ⊕₁ (f′ ∘ g ⊕₁ id) ∘ α⇒ ∘ △ ⊕₁ id

infixr 9 _⌻_

-- Special wiring diagrams

loop : {A : Obj} → WiringDiagram (A □ A) (A □ A)
loop = ▽ ⧈ id

pulsh : {A B C D : Obj} → A ⇒ B → C ⇒ D → WiringDiagram (B □ C) (A □ D)
pulsh f g = f ∘ p₂ ⧈ g

push : {A B : Obj} → A ⇒ B → WiringDiagram (A □ A) (B □ B)
push f = pulsh (f †) f

pull : {A B : Obj} → A ⇒ B → WiringDiagram (B □ B) (A □ A)
pull f = pulsh f (f †)

merge : {A B : Obj} → A ⇒ B → WiringDiagram (A □ A) (B □ B)
merge f = f † ∘ ▽ ∘ f ⊕₁ id ⧈ f

split : {A B : Obj} → A ⇒ B → WiringDiagram (B □ B) (A □ A)
split f = ▽ ∘ id ⊕₁ f ⧈ f †
