{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core using (Category)

module Category.Diagram.Pushout {o ℓ e} (𝒞 : Category o ℓ e) where

open Category 𝒞

import Categories.Diagram.Pullback op as Pb using (up-to-iso)

open import Categories.Diagram.Duality 𝒞 using (Pushout⇒coPullback)
open import Categories.Diagram.Pushout 𝒞 using (Pushout)
open import Categories.Diagram.Pushout.Properties 𝒞 using (glue; swap)
open import Categories.Morphism 𝒞 using (_≅_)
open import Categories.Morphism.Duality 𝒞 using (op-≅⇒≅)
open import Categories.Morphism.Reasoning 𝒞 using
    ( id-comm
    ; id-comm-sym
    ; assoc²''
    ; assoc²'
    )


private

  variable
    A B C D : Obj
    f g h : A ⇒ B

glue-i₁ : (p : Pushout f g) → Pushout h (Pushout.i₁ p) → Pushout (h ∘ f) g
glue-i₁ p = glue p

glue-i₂ : (p₁ : Pushout f g) → Pushout (Pushout.i₂ p₁) h → Pushout f (h ∘ g)
glue-i₂ p₁ p₂ = swap (glue (swap p₁) (swap p₂))

up-to-iso : (p p′ : Pushout f g) → Pushout.Q p ≅ Pushout.Q p′
up-to-iso p p′ = op-≅⇒≅ (Pb.up-to-iso (Pushout⇒coPullback p) (Pushout⇒coPullback p′))

pushout-f-id : Pushout f id
pushout-f-id {_} {_} {f} = record
    { i₁ = id
    ; i₂ = f
    ; commute = id-comm-sym
    ; universal = λ {B} {h₁} {h₂} eq → h₁
    ; unique = λ {E} {h₁} {h₂} {eq} {j} j∘i₁≈h₁ j∘i₂≈h₂ → Equiv.sym identityʳ ○ j∘i₁≈h₁
    ; universal∘i₁≈h₁ = λ {E} {h₁} {h₂} {eq} → identityʳ
    ; universal∘i₂≈h₂ = λ {E} {h₁} {h₂} {eq} → eq ○ identityʳ
    }
  where
    open HomReasoning

pushout-id-g : Pushout id g
pushout-id-g {_} {_} {g} = record
    { i₁ = g
    ; i₂ = id
    ; commute = id-comm
    ; universal = λ {B} {h₁} {h₂} eq → h₂
    ; unique = λ {E} {h₁} {h₂} {eq} {j} j∘i₁≈h₁ j∘i₂≈h₂ → Equiv.sym identityʳ ○ j∘i₂≈h₂
    ; universal∘i₁≈h₁ = λ {E} {h₁} {h₂} {eq} → Equiv.sym eq ○ identityʳ
    ; universal∘i₂≈h₂ = λ {E} {h₁} {h₂} {eq} → identityʳ
    }
  where
    open HomReasoning

extend-i₁-iso
    : {f : A ⇒ B}
      {g : A ⇒ C}
      (p : Pushout f g)
      (B≅D : B ≅ D)
    → Pushout (_≅_.from B≅D ∘ f) g
extend-i₁-iso {_} {_} {_} {_} {f} {g} p B≅D = record
    { i₁ = P.i₁ ∘ B≅D.to
    ; i₂ = P.i₂
    ; commute = begin
          (P.i₁ ∘ B≅D.to) ∘ B≅D.from ∘ f  ≈⟨ assoc²'' ⟨
          P.i₁ ∘ (B≅D.to ∘ B≅D.from) ∘ f  ≈⟨ refl⟩∘⟨ B≅D.isoˡ ⟩∘⟨refl ⟩
          P.i₁ ∘ id ∘ f                   ≈⟨ refl⟩∘⟨ identityˡ ⟩
          P.i₁ ∘ f                        ≈⟨ P.commute ⟩
          P.i₂ ∘ g                        ∎
    ; universal = λ { eq → P.universal (assoc ○ eq) }
    ; unique = λ {_} {h₁} {_} {j} ≈₁ ≈₂ →
          let
            ≈₁′ = begin
                j ∘ P.i₁                        ≈⟨ refl⟩∘⟨ identityʳ ⟨
                j ∘ P.i₁ ∘ id                   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ B≅D.isoˡ ⟨
                j ∘ P.i₁ ∘ B≅D.to ∘ B≅D.from    ≈⟨ assoc²' ⟨
                (j ∘ P.i₁ ∘ B≅D.to) ∘ B≅D.from  ≈⟨ ≈₁ ⟩∘⟨refl ⟩
                h₁ ∘ B≅D.from                   ∎
          in P.unique ≈₁′ ≈₂
    ; universal∘i₁≈h₁ = λ {E} {h₁} {_} {eq} →
        begin
            P.universal (assoc ○ eq) ∘ P.i₁ ∘ B≅D.to    ≈⟨ sym-assoc ⟩
            (P.universal (assoc ○ eq) ∘ P.i₁) ∘ B≅D.to  ≈⟨ P.universal∘i₁≈h₁ ⟩∘⟨refl ⟩
            (h₁ ∘ B≅D.from) ∘ B≅D.to                    ≈⟨ assoc ⟩
            h₁ ∘ B≅D.from ∘ B≅D.to                      ≈⟨ refl⟩∘⟨ B≅D.isoʳ ⟩
            h₁ ∘ id                                     ≈⟨ identityʳ ⟩
            h₁                                          ∎
    ; universal∘i₂≈h₂ = P.universal∘i₂≈h₂
    }
  where
    module P = Pushout p
    module B≅D = _≅_ B≅D
    open HomReasoning

extend-i₂-iso
    : {f : A ⇒ B}
      {g : A ⇒ C}
      (p : Pushout f g)
      (C≅D : C ≅ D)
    → Pushout f (_≅_.from C≅D ∘ g)
extend-i₂-iso {_} {_} {_} {_} {f} {g} p C≅D = swap (extend-i₁-iso (swap p) C≅D)
