{-# OPTIONS --without-K --safe #-}
module Coeq where

open import Categories.Category.Core using (Category)
open import Categories.Category.Instance.Nat using (Nat)
open import Categories.Diagram.Coequalizer Nat using (IsCoequalizer)
open import Categories.Object.Coproduct Nat using (Coproduct; IsCoproduct; IsCoproduct⇒Coproduct)


open Category Nat

-- TODO: any category
≈-i₁-i₂
    : {A B A+B C : Obj}
    → {i₁ : A ⇒ A+B}
    → {i₂ : B ⇒ A+B}
    → (f g : A+B ⇒ C)
    → IsCoproduct i₁ i₂
    → f ∘ i₁ ≈ g ∘ i₁
    → f ∘ i₂ ≈ g ∘ i₂
    → f ≈ g
≈-i₁-i₂ f g coprod ≈₁ ≈₂ = begin
    f                   ≈⟨ Equiv.sym g-η ⟩
    [ f ∘ i₁ , f ∘ i₂ ] ≈⟨ []-cong₂ ≈₁ ≈₂ ⟩
    [ g ∘ i₁ , g ∘ i₂ ] ≈⟨ g-η ⟩
    g                   ∎
  where
    open Coproduct (IsCoproduct⇒Coproduct coprod)
    open HomReasoning

coequalizer-on-coproduct
    : {A B A+B C Q₁ Q₂ : Obj}
    → (i₁ : A ⇒ A+B)
    → (i₂ : B ⇒ A+B)
    → (f g : A+B ⇒ C)
    → (q₁ : C ⇒ Q₁)
    → (q₂ : Q₁ ⇒ Q₂)
    → IsCoproduct i₁ i₂
    → IsCoequalizer (f ∘ i₁) (g ∘ i₁) q₁
    → IsCoequalizer (q₁ ∘ f ∘ i₂) (q₁ ∘ g ∘ i₂) q₂
    → IsCoequalizer f g (q₂ ∘ q₁)
coequalizer-on-coproduct {C = C} {Q₁} {Q₂} i₁ i₂ f g q₁ q₂ coprod coeq₁ coeq₂ = record
    { equality = ≈-i₁-i₂
        (q₂ ∘ q₁ ∘ f)
        (q₂ ∘ q₁ ∘ g)
        coprod
        (∘-resp-≈ʳ {g = q₂} X₁.equality)
        X₂.equality
    ; coequalize = λ {Q} {q} q∘f≈q∘g → let module X = Cocone {Q} {q} q∘f≈q∘g in X.u₂
    ; universal = λ {Q} {q} {q∘f≈q∘g} → let module X = Cocone {Q} {q} q∘f≈q∘g in X.q≈u₂∘q₂∘q₁
    ; unique = λ {Q} {q} {i} {q∘f≈q∘g} q≈i∘q₂∘q₁ →
        let module X = Cocone {Q} {q} q∘f≈q∘g in X.q≈i∘q₂∘q₁⇒i≈u₂ q≈i∘q₂∘q₁
    }
  where
    module X₁ = IsCoequalizer coeq₁
    module X₂ = IsCoequalizer coeq₂
    module Cocone {Q : Obj} {q : C ⇒ Q} (q∘f≈q∘g : q ∘ f ≈ q ∘ g) where
        open HomReasoning
        u₁ : Q₁ ⇒ Q
        u₁ = X₁.coequalize (∘-resp-≈ˡ q∘f≈q∘g)
        q≈u₁∘q₁ : q ≈ u₁ ∘ q₁
        q≈u₁∘q₁ = X₁.universal
        u₁∘q₁∘f∘i₂≈u₁∘q₁∘g∘i₂ : u₁ ∘ q₁ ∘ f ∘ i₂ ≈ u₁ ∘ q₁ ∘ g ∘ i₂
        u₁∘q₁∘f∘i₂≈u₁∘q₁∘g∘i₂ = begin
            u₁ ∘ q₁ ∘ f ∘ i₂ ≈⟨ ∘-resp-≈ˡ (Equiv.sym q≈u₁∘q₁) ⟩
            q ∘ f ∘ i₂       ≈⟨ ∘-resp-≈ˡ q∘f≈q∘g ⟩
            q ∘ g ∘ i₂       ≈⟨ ∘-resp-≈ˡ q≈u₁∘q₁ ⟩
            u₁ ∘ q₁ ∘ g ∘ i₂ ∎
        u₂ : Q₂ ⇒ Q
        u₂ = X₂.coequalize u₁∘q₁∘f∘i₂≈u₁∘q₁∘g∘i₂
        u₁≈u₂∘q₂ : u₁ ≈ u₂ ∘ q₂
        u₁≈u₂∘q₂ = X₂.universal
        q≈u₂∘q₂∘q₁ : q ≈ u₂ ∘ q₂ ∘ q₁
        q≈u₂∘q₂∘q₁ = begin
            q            ≈⟨ q≈u₁∘q₁ ⟩
            u₁ ∘ q₁      ≈⟨ ∘-resp-≈ˡ u₁≈u₂∘q₂ ⟩
            u₂ ∘ q₂ ∘ q₁ ∎
        q≈i∘q₂∘q₁⇒i≈u₂ : {i : Q₂ ⇒ Q} → q ≈ i ∘ q₂ ∘ q₁ → i ≈ u₂
        q≈i∘q₂∘q₁⇒i≈u₂ q≈i∘q₂∘q₁ = X₂.unique (Equiv.sym (X₁.unique q≈i∘q₂∘q₁))
