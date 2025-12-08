{-# OPTIONS --without-K --safe #-}

open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Level using (Level; _⊔_)

module Category.Diagram.Cospan {o ℓ e : Level} (𝒞 : FinitelyCocompleteCategory o ℓ e) where

import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as ⇒-Reasoning

open import Relation.Binary using (IsEquivalence)

module 𝒞 = FinitelyCocompleteCategory 𝒞

open 𝒞 hiding (i₁; i₂; _≈_)
open ⇒-Reasoning U using (switch-fromtoˡ; glueTrianglesˡ)
open Morphism U using (_≅_; module ≅)

record Cospan (A B : Obj) : Set (o ⊔ ℓ) where

  constructor cospan

  field
    {N} : Obj
    f₁  : A ⇒ N
    f₂  : B ⇒ N

private
  variable
    A B C D : Obj

record _≈_ (C D : Cospan A B) : Set (ℓ ⊔ e) where

  module C = Cospan C
  module D = Cospan D

  field
    ≅N : C.N ≅ D.N

  open _≅_ ≅N public
  module ≅N = _≅_ ≅N

  field
    from∘f₁≈f₁ : from ∘ C.f₁ 𝒞.≈ D.f₁
    from∘f₂≈f₂ : from ∘ C.f₂ 𝒞.≈ D.f₂

infix 4 _≈_

private
  variable
    f g h : Cospan A B

≈-refl : f ≈ f
≈-refl {f = cospan f₁ f₂} = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁ = from∘f₁≈f₁
    ; from∘f₂≈f₂ = from∘f₂≈f₂
    }
  where abstract
    from∘f₁≈f₁ : id ∘ f₁ 𝒞.≈ f₁
    from∘f₁≈f₁ = identityˡ
    from∘f₂≈f₂ : id ∘ f₂ 𝒞.≈ f₂
    from∘f₂≈f₂ = identityˡ

≈-sym : f ≈ g → g ≈ f
≈-sym f≈g = record
    { ≅N = ≅.sym ≅N
    ; from∘f₁≈f₁ = a
    ; from∘f₂≈f₂ = b
    }
  where abstract
    open _≈_ f≈g
    a : ≅N.to ∘ D.f₁ 𝒞.≈ C.f₁
    a = Equiv.sym (switch-fromtoˡ ≅N from∘f₁≈f₁)
    b : ≅N.to ∘ D.f₂ 𝒞.≈ C.f₂
    b = Equiv.sym (switch-fromtoˡ ≅N from∘f₂≈f₂)

≈-trans : f ≈ g → g ≈ h → f ≈ h
≈-trans f≈g g≈h = record
    { ≅N = ≅.trans f≈g.≅N g≈h.≅N
    ; from∘f₁≈f₁ = a
    ; from∘f₂≈f₂ = b
    }
  where abstract
    module f≈g = _≈_ f≈g
    module g≈h = _≈_ g≈h
    a : (g≈h.≅N.from ∘ f≈g.≅N.from) ∘ f≈g.C.f₁ 𝒞.≈ g≈h.D.f₁
    a = glueTrianglesˡ g≈h.from∘f₁≈f₁ f≈g.from∘f₁≈f₁
    b : (g≈h.≅N.from ∘ f≈g.≅N.from) ∘ f≈g.C.f₂ 𝒞.≈ g≈h.D.f₂
    b = glueTrianglesˡ g≈h.from∘f₂≈f₂ f≈g.from∘f₂≈f₂

≈-equiv : {A B : 𝒞.Obj} → IsEquivalence (_≈_ {A} {B})
≈-equiv = record
    { refl = ≈-refl
    ; sym = ≈-sym
    ; trans = ≈-trans
    }

compose : Cospan A B → Cospan B C → Cospan A C
compose (cospan f g) (cospan h i) = cospan (i₁ ∘ f) (i₂ ∘ i)
  where
    open pushout g h

identity : Cospan A A
identity = cospan id id

compose-3 : Cospan A B → Cospan B C → Cospan C D → Cospan A D
compose-3 (cospan f₁ f₂) (cospan g₁ g₂) (cospan h₁ h₂) = cospan (P₃.i₁ ∘ P₁.i₁ ∘ f₁) (P₃.i₂ ∘ P₂.i₂ ∘ h₂)
  where
    module P₁ = pushout f₂ g₁
    module P₂ = pushout g₂ h₁
    module P₃ = pushout P₁.i₂ P₂.i₁

_⊗_ :  Cospan A B → Cospan C D → Cospan (A + C) (B + D)
_⊗_ (cospan f₁ f₂) (cospan g₁ g₂) = cospan (f₁ +₁ g₁) (f₂ +₁ g₂)

infixr 10 _⊗_
