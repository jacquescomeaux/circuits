{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Function using (flip)
open import Level using (_⊔_)

module Category.Instance.Cospans {o ℓ e} (𝒞 : FinitelyCocompleteCategory o ℓ e) where

module 𝒞 = FinitelyCocompleteCategory 𝒞
open 𝒞 using (U; pushout)
open Category U hiding (_≈_)

open import Categories.Diagram.Pushout U using (Pushout)
open import Categories.Diagram.Pushout.Properties U using (pushout-resp-≈; up-to-iso)
open import Categories.Morphism U using (_≅_; module ≅)
open import Categories.Morphism.Reasoning U
  using
    ( switch-fromtoˡ
    ; pullˡ ; pullʳ
    ; cancelˡ
    )

open import Category.Diagram.Pushout U 
  using
    ( glue-i₁ ; glue-i₂
    ; pushout-f-id ; pushout-id-g
    ; extend-i₁-iso ; extend-i₂-iso
    )

open import Category.Diagram.Cospan 𝒞 using (Cospan; compose; compose-3; identity; _≈_; cospan; ≈-trans; ≈-sym; ≈-equiv)

private
  variable
    A B C D : Obj

private
  variable
    f g h : Cospan A B

compose-idˡ : compose f identity ≈ f
compose-idˡ {f = cospan {N} f₁ f₂} = record
    { ≅N = ≅P
    ; from∘f₁≈f₁ = from∘f₁≈f₁
    ; from∘f₂≈f₂ = from∘f₂≈f₂
    }
  where
    open HomReasoning
    P P′ : Pushout f₂ id
    P = pushout f₂ id
    P′ = pushout-f-id {f = f₂}
    module P = Pushout P
    ≅P : P.Q ≅ N
    ≅P = up-to-iso P P′
    module ≅P = _≅_ ≅P
    abstract
      from∘f₁≈f₁ : ≅P.from ∘ P.i₁ ∘ f₁ 𝒞.≈ f₁
      from∘f₁≈f₁ = begin
          ≅P.from ∘ P.i₁ ∘ f₁ ≈⟨ cancelˡ P.universal∘i₁≈h₁ ⟩
          f₁                  ∎
      from∘f₂≈f₂ : ≅P.from ∘ P.i₂ ∘ id 𝒞.≈ f₂
      from∘f₂≈f₂ = begin
          ≅P.from ∘ P.i₂ ∘ id ≈⟨ refl⟩∘⟨ identityʳ ⟩
          ≅P.from ∘ P.i₂      ≈⟨ P.universal∘i₂≈h₂ ⟩
          f₂                  ∎

compose-idʳ : compose identity f ≈ f
compose-idʳ {f = cospan {N} f₁ f₂} = record
    { ≅N = ≅P
    ; from∘f₁≈f₁ = from∘f₁≈f₁
    ; from∘f₂≈f₂ = from∘f₂≈f₂
    }
  where
    open HomReasoning
    P P′ : Pushout id f₁
    P = pushout id f₁
    module P = Pushout P
    P′ = pushout-id-g {g = f₁}
    ≅P : P.Q ≅ N
    ≅P = up-to-iso P P′
    module ≅P = _≅_ ≅P
    abstract
      from∘f₁≈f₁ : ≅P.from ∘ P.i₁ ∘ id 𝒞.≈ f₁
      from∘f₁≈f₁ = begin
          ≅P.from ∘ P.i₁ ∘ id ≈⟨ refl⟩∘⟨ identityʳ ⟩
          ≅P.from ∘ P.i₁      ≈⟨ P.universal∘i₁≈h₁ ⟩
          f₁                  ∎
      from∘f₂≈f₂ : ≅P.from ∘ P.i₂ ∘ f₂ 𝒞.≈ f₂
      from∘f₂≈f₂ = begin
          ≅P.from ∘ P.i₂ ∘ f₂ ≈⟨ cancelˡ P.universal∘i₂≈h₂ ⟩
          f₂                  ∎

compose-id² : compose identity identity ≈ identity {A}
compose-id² = compose-idˡ

compose-3-right : compose f (compose g h) ≈ compose-3 f g h
compose-3-right {f = f} {g = g} {h = h} = record
    { ≅N = ≅N
    ; from∘f₁≈f₁ = from∘f₁≈f₁
    ; from∘f₂≈f₂ = from∘f₂≈f₂
    }
  where
    open HomReasoning
    module C₁ = Cospan f
    module C₂ = Cospan g
    module C₃ = Cospan h
    P₁ : Pushout C₁.f₂ C₂.f₁
    P₁ = pushout C₁.f₂ C₂.f₁
    P₂ : Pushout C₂.f₂ C₃.f₁
    P₂ = pushout C₂.f₂ C₃.f₁
    module P₁ = Pushout P₁
    module P₂ = Pushout P₂
    P₃ : Pushout P₁.i₂ P₂.i₁
    P₃ = pushout P₁.i₂ P₂.i₁
    module P₃ = Pushout P₃
    P₄ P₄′ : Pushout C₁.f₂ (P₂.i₁ ∘ C₂.f₁)
    P₄ = glue-i₂ P₁ P₃
    P₄′ = pushout C₁.f₂ (P₂.i₁ ∘ C₂.f₁)
    module P₄ = Pushout P₄
    module P₄′ = Pushout P₄′
    ≅N : P₄′.Q ≅ P₄.Q
    ≅N = up-to-iso P₄′ P₄
    module ≅N = _≅_ ≅N
    abstract
      from∘f₁≈f₁ : ≅N.from ∘ P₄′.i₁ ∘ C₁.f₁ 𝒞.≈ P₃.i₁ ∘ P₁.i₁ ∘ C₁.f₁
      from∘f₁≈f₁ = sym-assoc ○ P₄′.universal∘i₁≈h₁ ⟩∘⟨refl ○ assoc
      from∘f₂≈f₂ : ≅N.from ∘ P₄′.i₂ ∘ P₂.i₂ ∘ C₃.f₂ 𝒞.≈ P₄.i₂ ∘ P₂.i₂ ∘ C₃.f₂
      from∘f₂≈f₂ = sym-assoc ○ P₄′.universal∘i₂≈h₂ ⟩∘⟨refl

compose-3-left : compose (compose f g) h ≈ compose-3 f g h
compose-3-left {f = f} {g = g} {h = h} = record
    { ≅N = up-to-iso P₄′ P₄
    ; from∘f₁≈f₁ = from∘f₁≈f₁
    ; from∘f₂≈f₂ = from∘f₂≈f₂
    }
  where
    open HomReasoning
    module C₁ = Cospan f
    module C₂ = Cospan g
    module C₃ = Cospan h
    P₁ : Pushout C₁.f₂ C₂.f₁
    P₁ = pushout C₁.f₂ C₂.f₁
    P₂ : Pushout C₂.f₂ C₃.f₁
    P₂ = pushout C₂.f₂ C₃.f₁
    module P₁ = Pushout P₁
    module P₂ = Pushout P₂
    P₃ : Pushout P₁.i₂ P₂.i₁
    P₃ = pushout P₁.i₂ P₂.i₁
    module P₃ = Pushout P₃
    P₄ P₄′ : Pushout (P₁.i₂ ∘ C₂.f₂) C₃.f₁
    P₄ = glue-i₁ P₂ P₃
    P₄′ = pushout (P₁.i₂ ∘ C₂.f₂) C₃.f₁
    module P₄ = Pushout P₄
    module P₄′ = Pushout P₄′
    ≅N : P₄′.Q ≅ P₄.Q
    ≅N = up-to-iso P₄′ P₄
    module ≅N = _≅_ ≅N
    abstract
      from∘f₁≈f₁ : ≅N.from ∘ P₄′.i₁ ∘ P₁.i₁ ∘ C₁.f₁ 𝒞.≈ P₄.i₁ ∘ P₁.i₁ ∘ C₁.f₁
      from∘f₁≈f₁ = sym-assoc ○ P₄′.universal∘i₁≈h₁ ⟩∘⟨refl
      from∘f₂≈f₂ : ≅N.from ∘ P₄′.i₂ ∘ C₃.f₂ 𝒞.≈ P₃.i₂ ∘ P₂.i₂ ∘ C₃.f₂
      from∘f₂≈f₂ = sym-assoc ○ P₄′.universal∘i₂≈h₂ ⟩∘⟨refl ○ assoc

compose-assoc
    : {c₁ : Cospan A B}
      {c₂ : Cospan B C}
      {c₃ : Cospan C D}
    → compose c₁ (compose c₂ c₃) ≈ (compose (compose c₁ c₂) c₃)
compose-assoc = ≈-trans compose-3-right (≈-sym compose-3-left)

compose-sym-assoc
    : {c₁ : Cospan A B}
      {c₂ : Cospan B C}
      {c₃ : Cospan C D}
    → compose (compose c₁ c₂) c₃ ≈ compose c₁ (compose c₂ c₃)
compose-sym-assoc = ≈-trans compose-3-left (≈-sym compose-3-right)

compose-equiv
    : {c₂ c₂′ : Cospan B C}
      {c₁ c₁′ : Cospan A B}
    → c₂ ≈ c₂′
    → c₁ ≈ c₁′
    → compose c₁ c₂ ≈ compose c₁′ c₂′
compose-equiv {_} {_} {_} {c₂} {c₂′} {c₁} {c₁′} ≈C₂ ≈C₁ = record
    { ≅N = ≅P
    ; from∘f₁≈f₁ = from∘f₁≈f₁
    ; from∘f₂≈f₂ = from∘f₂≈f₂
    }
  where
    module C₁ = Cospan c₁
    module C₁′ = Cospan c₁′
    module C₂ = Cospan c₂
    module C₂′ = Cospan c₂′
    P : Pushout C₁.f₂ C₂.f₁
    P = pushout C₁.f₂ C₂.f₁
    P′ : Pushout C₁′.f₂ C₂′.f₁
    P′ = pushout C₁′.f₂ C₂′.f₁
    module ≈C₁ = _≈_ ≈C₁
    module ≈C₂ = _≈_ ≈C₂
    P′′ : Pushout (≈C₁.to ∘ C₁′.f₂) (≈C₂.to ∘ C₂′.f₁)
    P′′ = extend-i₂-iso (extend-i₁-iso P′ (≅.sym ≈C₁.≅N)) (≅.sym ≈C₂.≅N)
    P″ : Pushout C₁.f₂ C₂.f₁
    P″ =
        pushout-resp-≈
            P′′
            (Equiv.sym (switch-fromtoˡ ≈C₁.≅N ≈C₁.from∘f₂≈f₂))
            (Equiv.sym (switch-fromtoˡ ≈C₂.≅N ≈C₂.from∘f₁≈f₁))
    module P = Pushout P
    module P′ = Pushout P′
    ≅P : P.Q ≅ P′.Q
    ≅P = up-to-iso P P″
    module ≅P = _≅_ ≅P
    open HomReasoning
    abstract
      from∘f₁≈f₁ : ≅P.from ∘ P.i₁ ∘ C₁.f₁ 𝒞.≈ P′.i₁ ∘ C₁′.f₁
      from∘f₁≈f₁ = begin
          ≅P.from ∘ P.i₁ ∘ C₁.f₁      ≈⟨ pullˡ P.universal∘i₁≈h₁ ⟩
          (P′.i₁ ∘ ≈C₁.from) ∘ C₁.f₁  ≈⟨ pullʳ ≈C₁.from∘f₁≈f₁ ⟩
          P′.i₁ ∘ C₁′.f₁              ∎
      from∘f₂≈f₂ : ≅P.from ∘ P.i₂ ∘ C₂.f₂ 𝒞.≈ P′.i₂ ∘ C₂′.f₂
      from∘f₂≈f₂ = begin
          ≅P.from ∘ P.i₂ ∘ C₂.f₂      ≈⟨ pullˡ P.universal∘i₂≈h₂ ⟩
          (P′.i₂ ∘ ≈C₂.from) ∘ C₂.f₂  ≈⟨ pullʳ ≈C₂.from∘f₂≈f₂ ⟩
          P′.i₂ ∘ C₂′.f₂              ∎

Cospans : Category o (o ⊔ ℓ) (ℓ ⊔ e)
Cospans = record
    { Obj = Obj
    ; _⇒_ = Cospan
    ; _≈_ = _≈_
    ; id = identity
    ; _∘_ = flip compose
    ; assoc = compose-assoc
    ; sym-assoc = compose-sym-assoc
    ; identityˡ = compose-idˡ
    ; identityʳ = compose-idʳ
    ; identity² = compose-id²
    ; equiv = ≈-equiv
    ; ∘-resp-≈ = compose-equiv
    }
