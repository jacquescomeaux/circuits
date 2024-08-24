{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core using (Category)

module Coeq {o ℓ e} (C : Category o ℓ e) where

open import Categories.Diagram.Coequalizer C using (IsCoequalizer)
open import Categories.Object.Coproduct C using (Coproduct; IsCoproduct; IsCoproduct⇒Coproduct)
open import Categories.Morphism.Reasoning.Core C using (pullˡ; pushˡ; extendˡ; extendʳ; assoc²')
open import Function using (_$_)

open Category C

coequalizer-on-coproduct
    : {A B A+B C Q₁ Q₂ : Obj}
    → {i₁ : A ⇒ A+B}
    → {i₂ : B ⇒ A+B}
    → {f g : A+B ⇒ C}
    → {q₁ : C ⇒ Q₁}
    → {q₂ : Q₁ ⇒ Q₂}
    → IsCoproduct i₁ i₂
    → IsCoequalizer (f ∘ i₁) (g ∘ i₁) q₁
    → IsCoequalizer (q₁ ∘ f ∘ i₂) (q₁ ∘ g ∘ i₂) q₂
    → IsCoequalizer f g (q₂ ∘ q₁)
coequalizer-on-coproduct {C = C} {Q₁} {Q₂} {f = f} {g} {q₁} {q₂} coprod coeq₁ coeq₂ = record
    { equality = assoc ○ equality ○ sym-assoc
    ; coequalize = λ eq → Cocone.u₂ eq
    ; universal = λ { {eq = eq} → Cocone.univ eq }
    ; unique = λ { {eq = eq} h≈i∘q₂∘q₁ → Cocone.uniq eq h≈i∘q₂∘q₁ }
    }
  where
    open HomReasoning
    module X₁ = IsCoequalizer coeq₁
    module X₂ = IsCoequalizer coeq₂
    open Coproduct (IsCoproduct⇒Coproduct coprod) using (g-η; [_,_]; unique; i₁; i₂)
    on-i₁ : (q₂ ∘ q₁ ∘ f) ∘ i₁ ≈ (q₂ ∘ q₁ ∘ g) ∘ i₁
    on-i₁ = assoc²' ○ refl⟩∘⟨ X₁.equality ○ Equiv.sym assoc²'
    on-i₂ : (q₂ ∘ q₁ ∘ f) ∘ i₂ ≈ (q₂ ∘ q₁ ∘ g) ∘ i₂
    on-i₂ = assoc²' ○ X₂.equality ○ Equiv.sym assoc²'
    equality : q₂ ∘ q₁ ∘ f ≈ q₂ ∘ q₁ ∘ g
    equality = begin
      q₂ ∘ q₁ ∘ f                                 ≈⟨ unique on-i₁ on-i₂ ⟨
      [ (q₂ ∘ q₁ ∘ g) ∘ i₁ , (q₂ ∘ q₁ ∘ g) ∘ i₂ ] ≈⟨ g-η ⟩
      q₂ ∘ q₁ ∘ g                                 ∎
    module Cocone {Q : Obj} {h : C ⇒ Q} (eq : h ∘ f ≈ h ∘ g) where
        u₁ : Q₁ ⇒ Q
        u₁ = X₁.coequalize (extendʳ eq)
        u₂ : Q₂ ⇒ Q
        u₂ = X₂.coequalize $ begin
            u₁ ∘ q₁ ∘ f ∘ i₂ ≈⟨ pullˡ (Equiv.sym X₁.universal) ⟩
            h ∘ f ∘ i₂       ≈⟨ extendʳ eq ⟩
            h ∘ g ∘ i₂       ≈⟨ pushˡ X₁.universal ⟩
            u₁ ∘ q₁ ∘ g ∘ i₂ ∎
        univ : h ≈ u₂ ∘ q₂ ∘ q₁
        univ = begin
            h            ≈⟨ X₁.universal ⟩
            u₁ ∘ q₁      ≈⟨ pushˡ X₂.universal ⟩
            u₂ ∘ q₂ ∘ q₁ ∎
        uniq : {i : Q₂ ⇒ Q} → h ≈ i ∘ q₂ ∘ q₁ → i ≈ u₂
        uniq h≈i∘q₂∘q₁ = X₂.unique (Equiv.sym (X₁.unique (h≈i∘q₂∘q₁ ○ sym-assoc)))
