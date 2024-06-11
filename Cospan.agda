{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Cocomplete.Bundle using (FinitelyCocompleteCategory)
open import Function using (flip)
open import Level using (_⊔_)

module Cospan {o ℓ e} (𝒞 : FinitelyCocompleteCategory o ℓ e) where

open FinitelyCocompleteCategory 𝒞

open import Categories.Diagram.Duality U using (Pushout⇒coPullback)
open import Categories.Diagram.Pushout U using (Pushout)
open import Categories.Diagram.Pushout.Properties U using (glue; swap)
open import Categories.Morphism U using (_≅_)
open import Categories.Morphism.Duality U using (op-≅⇒≅)

import Categories.Diagram.Pullback op as Pb using (up-to-iso)


private

  variable
    A B C D X Y Z : Obj
    f g h : A ⇒ B

record Cospan (A B : Obj) : Set (o ⊔ ℓ) where

  field
    {N} : Obj
    f₁    : A ⇒ N
    f₂    : B ⇒ N

compose : Cospan A B → Cospan B C → Cospan A C
compose c₁ c₂ = record { f₁ = p.i₁ ∘ C₁.f₁ ; f₂ = p.i₂ ∘ C₂.f₂ }
  where
    module C₁ = Cospan c₁
    module C₂ = Cospan c₂
    module p = pushout C₁.f₂ C₂.f₁

identity : Cospan A A
identity = record { f₁ = id ; f₂ = id }

compose-3 : Cospan A B → Cospan B C → Cospan C D → Cospan A D
compose-3 c₁ c₂ c₃ = record { f₁ = P₃.i₁ ∘ P₁.i₁ ∘ C₁.f₁ ; f₂ = P₃.i₂ ∘ P₂.i₂ ∘ C₃.f₂ }
  where
    module C₁ = Cospan c₁
    module C₂ = Cospan c₂
    module C₃ = Cospan c₃
    module P₁ = pushout C₁.f₂ C₂.f₁
    module P₂ = pushout C₂.f₂ C₃.f₁
    module P₃ = pushout P₁.i₂ P₂.i₁

record Same (P P′ : Cospan A B) : Set (ℓ ⊔ e) where

  field
    iso : Cospan.N P ≅ Cospan.N P′
    from∘f₁≈f₁′ : _≅_.from iso ∘ Cospan.f₁ P ≈ Cospan.f₁ P′
    from∘f₂≈f₂′ : _≅_.from iso ∘ Cospan.f₂ P ≈ Cospan.f₂ P′

glue-i₁ : (p : Pushout f g) → Pushout h (Pushout.i₁ p) → Pushout (h ∘ f) g
glue-i₁ p = glue p

glue-i₂ : (p₁ : Pushout f g) → Pushout (Pushout.i₂ p₁) h → Pushout f (h ∘ g)
glue-i₂ p₁ p₂ = swap (glue (swap p₁) (swap p₂))

up-to-iso : (p p′ : Pushout f g) → Pushout.Q p ≅ Pushout.Q p′
up-to-iso p p′ = op-≅⇒≅ (Pb.up-to-iso (Pushout⇒coPullback p) (Pushout⇒coPullback p′))

compose-3-right
    : {c₁ : Cospan A B}
      {c₂ : Cospan B C}
      {c₃ : Cospan C D}
    → Same (compose c₁ (compose c₂ c₃)) (compose-3 c₁ c₂ c₃)
compose-3-right {_} {_} {_} {_} {c₁} {c₂} {c₃} = record
    { iso = up-to-iso P₄′ P₄
    ; from∘f₁≈f₁′ = sym-assoc ○ P₄′.universal∘i₁≈h₁ ⟩∘⟨refl ○ assoc
    ; from∘f₂≈f₂′ = sym-assoc ○ P₄′.universal∘i₂≈h₂ ⟩∘⟨refl
    }
  where
    open HomReasoning
    module C₁ = Cospan c₁
    module C₂ = Cospan c₂
    module C₃ = Cospan c₃
    P₁ = pushout C₁.f₂ C₂.f₁
    P₂ = pushout C₂.f₂ C₃.f₁
    module P₁ = Pushout P₁
    module P₂ = Pushout P₂
    P₃ = pushout P₁.i₂ P₂.i₁
    module P₃ = Pushout P₃
    P₄ = glue-i₂ P₁ P₃
    module P₄ = Pushout P₄
    P₄′ = pushout C₁.f₂ (P₂.i₁ ∘ C₂.f₁)
    module P₄′ = Pushout P₄′

compose-3-left
    : {c₁ : Cospan A B}
      {c₂ : Cospan B C}
      {c₃ : Cospan C D}
    → Same (compose (compose c₁ c₂) c₃) (compose-3 c₁ c₂ c₃)
compose-3-left {_} {_} {_} {_} {c₁} {c₂} {c₃} = record
    { iso = up-to-iso P₄′ P₄
    ; from∘f₁≈f₁′ = sym-assoc ○ P₄′.universal∘i₁≈h₁ ⟩∘⟨refl
    ; from∘f₂≈f₂′ = sym-assoc ○ P₄′.universal∘i₂≈h₂ ⟩∘⟨refl ○ assoc
    }
  where
    open HomReasoning
    module C₁ = Cospan c₁
    module C₂ = Cospan c₂
    module C₃ = Cospan c₃
    P₁ = pushout C₁.f₂ C₂.f₁
    P₂ = pushout C₂.f₂ C₃.f₁
    module P₁ = Pushout P₁
    module P₂ = Pushout P₂
    P₃ = pushout P₁.i₂ P₂.i₁
    module P₃ = Pushout P₃
    P₄ = glue-i₁ P₂ P₃
    module P₄ = Pushout P₄
    P₄′ = pushout (P₁.i₂ ∘ C₂.f₂) C₃.f₁
    module P₄′ = Pushout P₄′

compose-assoc
    : {c₁ : Cospan A B}
      {c₂ : Cospan B C}
      {c₃ : Cospan C D}
    → Same (compose c₁ (compose c₂ c₃)) (compose (compose c₁ c₂) c₃)
compose-assoc = ?

compose-sym-assoc
    : {c₁ : Cospan A B}
      {c₂ : Cospan B C}
      {c₃ : Cospan C D}
    → Same (compose (compose c₁ c₂) c₃) (compose c₁ (compose c₂ c₃))
compose-sym-assoc = ?

CospanC : Category _ _ _
CospanC = record
    { Obj = Obj
    ; _⇒_ = Cospan
    ; _≈_ = Same
    ; id = identity
    ; _∘_ = flip compose
    ; assoc = ?
    ; sym-assoc = compose-sym-assoc
    ; identityˡ = ?
    ; identityʳ = {! !}
    ; identity² = {! !}
    ; equiv = {! !}
    ; ∘-resp-≈ = {! !}
    }
