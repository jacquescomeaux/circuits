{-# OPTIONS --without-K --safe #-}

open import Level using (Level; suc; _⊔_)
open import Categories.Category using (Category)

module Category.Dagger.Semiadditive {o ℓ e : Level} (𝒞 : Category o ℓ e) where

import Categories.Morphism.Reasoning 𝒞 as ⇒-Reasoning

open import Categories.Category.Dagger using (HasDagger)
open import Category.Semiadditive using (Semiadditive)
open import Relation.Binary using (Rel)

record SemiadditiveDagger : Set (suc (o ⊔ ℓ ⊔ e)) where

  field
    semiadditive : Semiadditive 𝒞
    dagger : HasDagger 𝒞

  open Category 𝒞
  open HasDagger dagger public
  open Semiadditive semiadditive public

  field
    π₁† : {A B : Obj} → π₁ {A} {B} † ≈ i₁
    π₂† : {A B : Obj} → π₂ {A} {B} † ≈ i₂
    ⟨⟩-† : {A B C : Obj} {f : A ⇒ B} {g : A ⇒ C} → ⟨ f , g ⟩ † ≈ [ f † , g † ]

  open HomReasoning
  open ⇒-Reasoning

  Δ† : {A : Obj} → Δ {A} † ≈ ∇
  Δ† = begin
      ⟨ id , id ⟩ †   ≈⟨ ⟨⟩-† ⟩
      [ id † , id † ] ≈⟨ []-cong₂ †-identity †-identity ⟩
      [ id , id ]     ∎

  ∇† : {A : Obj} → ∇ {A} † ≈ Δ
  ∇† = begin
      ∇ †   ≈⟨ ⟨ Δ† ⟩† ⟨
      Δ † † ≈⟨ †-involutive Δ ⟩
      Δ     ∎

  †-resp-×₁ : {A B C D : Obj} {f : A ⇒ B} {g : C ⇒ D} → (f ×₁ g) † ≈ (f †) ×₁ (g †)
  †-resp-×₁ {f = f} {g} = begin
      ⟨ f ∘ π₁ , g ∘ π₂ ⟩ †       ≈⟨ ⟨⟩-† ⟩
      [ (f ∘ π₁) † , (g ∘ π₂) † ] ≈⟨ []-cong₂ †-homomorphism †-homomorphism ⟩
      [ π₁ † ∘ f † , π₂ † ∘ g † ] ≈⟨ []-cong₂ (π₁† ⟩∘⟨refl) (π₂† ⟩∘⟨refl) ⟩
      [ i₁ ∘ f † , i₂ ∘ g † ]     ≈⟨ ×₁-+₁ (f †) (g †) ⟨
      ⟨ f † ∘ π₁ , g † ∘ π₂ ⟩     ∎

  +-congˡ : {A B : Obj} {f g h : A ⇒ B} → g ≈ h → f + g ≈ f + h
  +-congˡ g≈h = +-cong Equiv.refl g≈h

  +-congʳ : {A B : Obj} {f g h : A ⇒ B} → f ≈ g → f + h ≈ g + h
  +-congʳ f≈g = +-cong f≈g Equiv.refl

  +-† : {A B : Obj} {f g : A ⇒ B} → (f + g) † ≈ (f †) + (g †)
  +-† {f = f} {g} = begin
      (∇ ∘ f ×₁ g ∘ Δ) †     ≈⟨ †-homomorphism ⟩
      (f ×₁ g ∘ Δ) † ∘ ∇ †   ≈⟨ pushˡ †-homomorphism ⟩
      Δ † ∘ (f ×₁ g) † ∘ ∇ † ≈⟨ Δ† ⟩∘⟨ †-resp-×₁ ⟩∘⟨ ∇† ⟩
      ∇ ∘ (f †) ×₁ (g †) ∘ Δ ∎

  -- bilinearity of composition
  ∘-distribˡ : {A B C : Obj} {f : B ⇒ C} {g h : A ⇒ B} → f ∘ (g + h) ≈ f ∘ g + f ∘ h
  ∘-distribˡ {f = f} {g} {h} = begin
      f ∘ (g + h)             ≈⟨ refl⟩∘⟨ identityʳ ⟨
      f ∘ (g + h) ∘ id        ≈⟨ +-resp-∘ ⟩
      f ∘ g ∘ id + f ∘ h ∘ id ≈⟨ +-cong (refl⟩∘⟨ identityʳ) (refl⟩∘⟨ identityʳ) ⟩
      f ∘ g + f ∘ h           ∎

  ∘-distribʳ : {A B C : Obj} {f g : B ⇒ C} {h : A ⇒ B} → (f + g) ∘ h ≈ f ∘ h + g ∘ h
  ∘-distribʳ {f = f} {g} {h} = begin
      (f + g) ∘ h             ≈⟨ pushˡ (Equiv.sym identityˡ) ⟩
      id ∘ (f + g) ∘ h        ≈⟨ +-resp-∘ ⟩
      id ∘ f ∘ h + id ∘ g ∘ h ≈⟨ +-cong (pullˡ identityˡ) (pullˡ identityˡ) ⟩
      f ∘ h + g ∘ h           ∎

record IdempotentSemiadditiveDagger : Set (suc (o ⊔ ℓ ⊔ e)) where

  field
    semiadditiveDagger : SemiadditiveDagger

  open SemiadditiveDagger semiadditiveDagger public

  open Category 𝒞
  open HomReasoning
  open ⇒-Reasoning

  field
    idempotent : {A B : Obj} {f : A ⇒ B} → f + f ≈ f

  _≤_ : {A B : Obj} → Rel (A ⇒ B) e
  _≤_ {A} {B} f g = f + g ≈ g

  ≤-refl : {A B : Obj} {f : A ⇒ B} → f ≤ f
  ≤-refl = idempotent

  ≤-antisym : {A B : Obj} {f g : A ⇒ B} → f ≤ g → g ≤ f → f ≈ g
  ≤-antisym {A} {B} {f} {g} f≤g g≤f = begin
      f     ≈⟨ g≤f ⟨
      g + f ≈⟨ +-comm g f ⟩
      f + g ≈⟨ f≤g ⟩
      g ∎

  ≤-trans : {A B : Obj} {f g h : A ⇒ B} → f ≤ g → g ≤ h → f ≤ h
  ≤-trans {A} {B} {f} {g} {h} f≤g g≤h = begin
      f + h       ≈⟨ refl⟩∘⟨ ×₁-congˡ g≤h ⟩∘⟨refl ⟨
      f + (g + h) ≈⟨ +-assoc f g h ⟨
      (f + g) + h ≈⟨ refl⟩∘⟨ ×₁-congʳ f≤g ⟩∘⟨refl ⟩
      g + h       ≈⟨ g≤h ⟩
      h           ∎

  ≤-resp-+
      : {A B : Obj}
        {f g h i : A ⇒ B}
      → f ≤ h
      → g ≤ i
      → (f + g) ≤ (h + i)
  ≤-resp-+ {f = f} {g} {h} {i} f≤h g≤i = begin
      (f + g) + (h + i) ≈⟨ +-assoc f g (h + i) ⟩
      f + (g + (h + i)) ≈⟨ +-congˡ (+-assoc g h i) ⟨
      f + ((g + h) + i) ≈⟨ +-congˡ (+-congʳ (+-comm g h)) ⟩
      f + ((h + g) + i) ≈⟨ +-congˡ (+-assoc h g i) ⟩
      f + (h + (g + i)) ≈⟨ +-assoc f h (g + i) ⟨
      (f + h) + (g + i) ≈⟨ +-cong f≤h g≤i ⟩
      h + i             ∎

  ≤-resp-∘
      : {A B C : Obj}
        {f h : B ⇒ C}
        {g i : A ⇒ B}
      → f ≤ h
      → g ≤ i
      → (f ∘ g) ≤ (h ∘ i)
  ≤-resp-∘ {f = f} {h} {g} {i} f≤h g≤i = begin
      f ∘ g + (h ∘ i)         ≈⟨ +-congˡ (f≤h ⟩∘⟨refl) ⟨
      f ∘ g + ((f + h) ∘ i)   ≈⟨ +-congˡ ∘-distribʳ ⟩
      f ∘ g + (f ∘ i + h ∘ i) ≈⟨ +-assoc (f ∘ g) (f ∘ i) (h ∘ i) ⟨
      (f ∘ g + f ∘ i) + h ∘ i ≈⟨ +-congʳ ∘-distribˡ ⟨
      f ∘ (g + i) + h ∘ i     ≈⟨ +-congʳ (refl⟩∘⟨ g≤i) ⟩
      f ∘ i + h ∘ i           ≈⟨ ∘-distribʳ ⟨
      (f + h) ∘ i             ≈⟨ f≤h ⟩∘⟨refl ⟩
      h ∘ i                   ∎

  †-resp-≤ : {A B : Obj} {f g : A ⇒ B} → f ≤ g → (f †) ≤ (g †)
  †-resp-≤ {A} {B} {f} {g} f≤g = begin
      (f †) + (g †) ≈⟨ +-† ⟨
      (f + g) †     ≈⟨ ⟨ f≤g ⟩† ⟩
      g †           ∎

  -- special law
  ∇∘Δ : {A : Obj} → ∇ ∘ Δ ≈ id {A}
  ∇∘Δ = begin
      ∇ ∘ Δ             ≈⟨ refl⟩∘⟨ introˡ id×₁id ⟩
      ∇ ∘ id ×₁ id ∘ Δ  ≈⟨ idempotent ⟩
      id                ∎
