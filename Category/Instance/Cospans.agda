{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Category.Cocomplete.Finitely.Bundle using (FinitelyCocompleteCategory)
open import Function using (flip)
open import Level using (_⊔_)

module Category.Instance.Cospans {o ℓ e} (𝒞 : FinitelyCocompleteCategory o ℓ e) where

open FinitelyCocompleteCategory 𝒞

open import Categories.Diagram.Pushout U using (Pushout)
open import Categories.Diagram.Pushout.Properties U using (pushout-resp-≈; up-to-iso)
open import Categories.Morphism U using (_≅_; module ≅)
open import Categories.Morphism.Reasoning U
  using
    ( switch-fromtoˡ
    ; glueTrianglesˡ
    ; pullˡ ; pullʳ
    )

open import Category.Diagram.Pushout U 
  using
    ( glue-i₁ ; glue-i₂
    ; pushout-f-id ; pushout-id-g
    ; extend-i₁-iso ; extend-i₂-iso
    )

private

  variable
    A B C D X Y Z : Obj
    f g h : A ⇒ B

record Cospan (A B : Obj) : Set (o ⊔ ℓ) where

  field
    {N} : Obj
    f₁  : A ⇒ N
    f₂  : B ⇒ N

compose : Cospan A B → Cospan B C → Cospan A C
compose c₁ c₂ = record { f₁ = p.i₁ ∘ C₁.f₁ ; f₂ = p.i₂ ∘ C₂.f₂ }
  where
    module C₁ = Cospan c₁
    module C₂ = Cospan c₂
    module p = pushout C₁.f₂ C₂.f₁

id-Cospan : Cospan A A
id-Cospan = record { f₁ = id ; f₂ = id }

compose-3 : Cospan A B → Cospan B C → Cospan C D → Cospan A D
compose-3 c₁ c₂ c₃ = record { f₁ = P₃.i₁ ∘ P₁.i₁ ∘ C₁.f₁ ; f₂ = P₃.i₂ ∘ P₂.i₂ ∘ C₃.f₂ }
  where
    module C₁ = Cospan c₁
    module C₂ = Cospan c₂
    module C₃ = Cospan c₃
    module P₁ = pushout C₁.f₂ C₂.f₁
    module P₂ = pushout C₂.f₂ C₃.f₁
    module P₃ = pushout P₁.i₂ P₂.i₁

record Same (C C′ : Cospan A B) : Set (ℓ ⊔ e) where

  module C = Cospan C
  module C′ = Cospan C′

  field
    ≅N : C.N ≅ C′.N

  open _≅_ ≅N public
  module ≅N = _≅_ ≅N

  field
    from∘f₁≈f₁′ : from ∘ C.f₁ ≈ C′.f₁
    from∘f₂≈f₂′ : from ∘ C.f₂ ≈ C′.f₂

same-refl : {C : Cospan A B} → Same C C
same-refl = record
    { ≅N = ≅.refl
    ; from∘f₁≈f₁′ = identityˡ
    ; from∘f₂≈f₂′ = identityˡ
    }

same-sym : {C C′ : Cospan A B} → Same C C′ → Same C′ C
same-sym C≅C′ = record
    { ≅N = ≅.sym ≅N
    ; from∘f₁≈f₁′ = Equiv.sym (switch-fromtoˡ ≅N from∘f₁≈f₁′)
    ; from∘f₂≈f₂′ = Equiv.sym (switch-fromtoˡ ≅N from∘f₂≈f₂′)
    }
  where
    open Same C≅C′

same-trans : {C C′ C″ : Cospan A B} → Same C C′ → Same C′ C″ → Same C C″
same-trans C≈C′ C′≈C″ = record
    { ≅N = ≅.trans C≈C′.≅N C′≈C″.≅N
    ; from∘f₁≈f₁′ = glueTrianglesˡ C′≈C″.from∘f₁≈f₁′ C≈C′.from∘f₁≈f₁′
    ; from∘f₂≈f₂′ = glueTrianglesˡ C′≈C″.from∘f₂≈f₂′ C≈C′.from∘f₂≈f₂′
    }
  where
    module C≈C′ = Same C≈C′
    module C′≈C″ = Same C′≈C″

compose-idˡ : {C : Cospan A B} → Same (compose C id-Cospan) C
compose-idˡ {_} {_} {C} = record
    { ≅N = ≅P
    ; from∘f₁≈f₁′ = begin
          ≅P.from ∘ P.i₁ ∘ C.f₁     ≈⟨ assoc ⟨
          (≅P.from ∘ P.i₁) ∘ C.f₁   ≈⟨ P.universal∘i₁≈h₁ ⟩∘⟨refl ⟩
          id ∘ C.f₁                 ≈⟨ identityˡ ⟩
          C.f₁                      ∎
    ; from∘f₂≈f₂′ = begin
          ≅P.from ∘ P.i₂ ∘ id       ≈⟨ refl⟩∘⟨ identityʳ ⟩
          ≅P.from ∘ P.i₂            ≈⟨ P.universal∘i₂≈h₂ ⟩
          C.f₂                      ∎
    }
  where
    open HomReasoning
    module C = Cospan C
    P = pushout C.f₂ id
    module P = Pushout P
    P′ = pushout-f-id {f = C.f₂}
    ≅P = up-to-iso P P′
    module ≅P = _≅_ ≅P

compose-idʳ : {C : Cospan A B} → Same (compose id-Cospan C) C
compose-idʳ {_} {_} {C} = record
    { ≅N = ≅P
    ; from∘f₁≈f₁′ = begin
          ≅P.from ∘ P.i₁ ∘ id       ≈⟨ refl⟩∘⟨ identityʳ ⟩
          ≅P.from ∘ P.i₁            ≈⟨ P.universal∘i₁≈h₁ ⟩
          C.f₁                      ∎
    ; from∘f₂≈f₂′ = begin
          ≅P.from ∘ P.i₂ ∘ C.f₂     ≈⟨ assoc ⟨
          (≅P.from ∘ P.i₂) ∘ C.f₂   ≈⟨ P.universal∘i₂≈h₂ ⟩∘⟨refl ⟩
          id ∘ C.f₂                 ≈⟨ identityˡ ⟩
          C.f₂                      ∎
    }
  where
    open HomReasoning
    module C = Cospan C
    P = pushout id C.f₁
    module P = Pushout P
    P′ = pushout-id-g {g = C.f₁}
    ≅P = up-to-iso P P′
    module ≅P = _≅_ ≅P

compose-id² : Same {A} (compose id-Cospan id-Cospan) id-Cospan
compose-id² = compose-idˡ

compose-3-right
    : {c₁ : Cospan A B}
      {c₂ : Cospan B C}
      {c₃ : Cospan C D}
    → Same (compose c₁ (compose c₂ c₃)) (compose-3 c₁ c₂ c₃)
compose-3-right {_} {_} {_} {_} {c₁} {c₂} {c₃} = record
    { ≅N = up-to-iso P₄′ P₄
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
    { ≅N = up-to-iso P₄′ P₄
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
compose-assoc = same-trans compose-3-right (same-sym compose-3-left)

compose-sym-assoc
    : {c₁ : Cospan A B}
      {c₂ : Cospan B C}
      {c₃ : Cospan C D}
    → Same (compose (compose c₁ c₂) c₃) (compose c₁ (compose c₂ c₃))
compose-sym-assoc = same-trans compose-3-left (same-sym compose-3-right)

compose-equiv
    : {c₂ c₂′ : Cospan B C}
      {c₁ c₁′ : Cospan A B}
    → Same c₂ c₂′
    → Same c₁ c₁′
    → Same (compose c₁ c₂) (compose c₁′ c₂′)
compose-equiv {_} {_} {_} {c₂} {c₂′} {c₁} {c₁′} ≈C₂ ≈C₁ = record
    { ≅N = up-to-iso P P″
    ; from∘f₁≈f₁′ = begin
          ≅P.from ∘ P.i₁ ∘ C₁.f₁      ≈⟨ assoc ⟨
          (≅P.from ∘ P.i₁) ∘ C₁.f₁    ≈⟨ P.universal∘i₁≈h₁ ⟩∘⟨refl ⟩
          (P′.i₁ ∘ ≈C₁.from) ∘ C₁.f₁  ≈⟨ assoc ⟩
          P′.i₁ ∘ ≈C₁.from ∘ C₁.f₁    ≈⟨ refl⟩∘⟨ ≈C₁.from∘f₁≈f₁′ ⟩
          P′.i₁ ∘ C₁′.f₁              ∎
    ; from∘f₂≈f₂′ = begin
          ≅P.from ∘ P.i₂ ∘ C₂.f₂      ≈⟨ assoc ⟨
          (≅P.from ∘ P.i₂) ∘ C₂.f₂    ≈⟨ P.universal∘i₂≈h₂ ⟩∘⟨refl ⟩
          (P′.i₂ ∘ ≈C₂.from) ∘ C₂.f₂  ≈⟨ assoc ⟩
          P′.i₂ ∘ ≈C₂.from ∘ C₂.f₂    ≈⟨ refl⟩∘⟨ ≈C₂.from∘f₂≈f₂′ ⟩
          P′.i₂ ∘ C₂′.f₂              ∎
    }
  where
    module C₁ = Cospan c₁
    module C₁′ = Cospan c₁′
    module C₂ = Cospan c₂
    module C₂′ = Cospan c₂′
    P = pushout C₁.f₂ C₂.f₁
    P′ = pushout C₁′.f₂ C₂′.f₁
    module ≈C₁ = Same ≈C₁
    module ≈C₂ = Same ≈C₂
    P′′ : Pushout (≈C₁.to ∘ C₁′.f₂) (≈C₂.to ∘ C₂′.f₁)
    P′′ = extend-i₂-iso (extend-i₁-iso P′ (≅.sym ≈C₁.≅N)) (≅.sym ≈C₂.≅N)
    P″ : Pushout C₁.f₂ C₂.f₁
    P″ =
        pushout-resp-≈
            P′′
            (Equiv.sym (switch-fromtoˡ ≈C₁.≅N ≈C₁.from∘f₂≈f₂′))
            (Equiv.sym (switch-fromtoˡ ≈C₂.≅N ≈C₂.from∘f₁≈f₁′))
    module P = Pushout P
    module P′ = Pushout P′
    ≅P : P.Q ≅ P′.Q
    ≅P = up-to-iso P P″
    module ≅P = _≅_ ≅P
    open HomReasoning

Cospans : Category o (o ⊔ ℓ) (ℓ ⊔ e)
Cospans = record
    { Obj = Obj
    ; _⇒_ = Cospan
    ; _≈_ = Same
    ; id = id-Cospan
    ; _∘_ = flip compose
    ; assoc = compose-assoc
    ; sym-assoc = compose-sym-assoc
    ; identityˡ = compose-idˡ
    ; identityʳ = compose-idʳ
    ; identity² = compose-id²
    ; equiv = record
        { refl = same-refl
        ; sym = same-sym
        ; trans = same-trans
        }
    ; ∘-resp-≈ = compose-equiv
    }
