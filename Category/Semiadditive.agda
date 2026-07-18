{-# OPTIONS --without-K --safe #-}

open import Level using (Level; levelOfTerm)
open import Categories.Category using (Category)

module Category.Semiadditive {o ℓ e : Level} (𝒞 : Category o ℓ e) where

import Categories.Morphism.Reasoning 𝒞 as ⇒-Reasoning

open import Algebra using (IsCommutativeMonoid; CommutativeMonoid)
open import Categories.Category.CMonoidEnriched using (CM-Category)
open import Categories.Object.Zero 𝒞 using (Zero)
open import Category.BinaryBiproducts 𝒞 using (BinaryBiproducts)
open import Data.Product using (_,_)

private module 𝒞 = Category 𝒞

-- A semiadditive category has all finite biproducts
record Semiadditive : Set (levelOfTerm 𝒞) where

  field
    zero : Zero
    biproducts : BinaryBiproducts

  open Zero zero public
  open BinaryBiproducts biproducts public

  open 𝒞

  open HomReasoning
  open ⇒-Reasoning

  module _ {A B : Obj} where

    π₁∘i₂≈0 : π₁ {A} {B} ∘ i₂ ≈ zero⇒
    π₁∘i₂≈0 = begin
        π₁ ∘ i₂             ≈⟨ π₁i₂-absorbˡ zero⇒ ⟨
        zero⇒ {A} ∘ π₁ ∘ i₂ ≈⟨ zero-∘ʳ (π₁ ∘ i₂) ⟩
        zero⇒               ∎

    π₂∘i₁≈0 : π₂ {A} {B} ∘ i₁ ≈ zero⇒
    π₂∘i₁≈0 = begin
        π₂ ∘ i₁             ≈⟨ π₂i₁-absorbˡ zero⇒ ⟨
        zero⇒ {A} ∘ π₂ ∘ i₁ ≈⟨ zero-∘ʳ (π₂ ∘ i₁) ⟩
        zero⇒               ∎

  module _ {A B : Obj} where

    _+_ _+′_ : A ⇒ B → A ⇒ B → A ⇒ B
    f + g = ∇ ∘ f ×₁ g ∘ Δ
    f +′ g = ∇ ∘ f +₁ g ∘ Δ

    infix 8 _+_

    +-cong : {x y u v : A ⇒ B} → x ≈ y → u ≈ v → x + u ≈ y + v
    +-cong eq₁ eq₂ = refl⟩∘⟨ ×₁-cong₂ eq₁ eq₂ ⟩∘⟨refl

    +-assoc : (x y z : A ⇒ B) → (x + y) + z ≈ x + (y + z)
    +-assoc x y z = begin
        ∇ ∘ (∇ ∘ x ×₁ y ∘ Δ) ×₁ z ∘ Δ                           ≈⟨ refl⟩∘⟨ pushˡ (Equiv.sym first∘×₁) ⟩
        ∇ ∘ ∇ ×₁ id ∘ (x ×₁ y ∘ Δ) ×₁ z ∘ Δ                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ×₁-cong₂ Equiv.refl identityʳ ⟩∘⟨refl ⟨
        ∇ ∘ ∇ ×₁ id ∘ (x ×₁ y ∘ Δ) ×₁ (z ∘ id) ∘ Δ              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (Equiv.sym ×₁∘×₁) ⟩
        ∇ ∘ ∇ ×₁ id ∘ (x ×₁ y) ×₁ z ∘ Δ ×₁ id ∘ Δ               ≈⟨ refl⟩∘⟨ ×₁-+₁ ∇ id ⟩∘⟨refl ⟩
        ∇ ∘ ∇ +₁ id ∘ (x ×₁ y) ×₁ z ∘ Δ ×₁ id ∘ Δ               ≈⟨ extendʳ ∇-assoc ⟩
        ∇ ∘ (id +₁ ∇ ∘ +-assocˡ) ∘ (x ×₁ y) ×₁ z ∘ Δ ×₁ id ∘ Δ  ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ assocˡ≈+-assocˡ) ⟩∘⟨refl ⟨
        ∇ ∘ (id +₁ ∇ ∘ assocˡ) ∘ (x ×₁ y) ×₁ z ∘ Δ ×₁ id ∘ Δ    ≈⟨ refl⟩∘⟨ pullʳ (extendʳ assocˡ∘×₁) ⟩
        ∇ ∘ id +₁ ∇ ∘ x ×₁ (y ×₁ z) ∘ assocˡ ∘ Δ ×₁ id ∘ Δ      ≈⟨ refl⟩∘⟨ ×₁-+₁ id ∇ ⟩∘⟨ refl⟩∘⟨ Δ-assoc ⟨
        ∇ ∘ id ×₁ ∇ ∘ x ×₁ (y ×₁ z) ∘ id ×₁ Δ ∘ Δ               ≈⟨ refl⟩∘⟨ pullˡ second∘×₁ ⟩
        ∇ ∘ x ×₁ (∇ ∘ y ×₁ z) ∘ id ×₁ Δ ∘ Δ                     ≈⟨ refl⟩∘⟨ pullˡ ×₁∘×₁ ⟩
        ∇ ∘ (x ∘ id) ×₁ ((∇ ∘ y ×₁ z) ∘ Δ) ∘ Δ                  ≈⟨ refl⟩∘⟨ ×₁-cong₂ identityʳ assoc ⟩∘⟨refl ⟩
        ∇ ∘ x ×₁ (∇ ∘ y ×₁ z ∘ Δ) ∘ Δ                           ∎

    +-identityˡ : (x : A ⇒ B) → zero⇒ + x ≈ x
    +-identityˡ x = begin
        ∇ ∘ zero⇒ ×₁ x ∘ Δ              ≈⟨ refl⟩∘⟨ ×₁∘Δ ⟩
        ∇ ∘ ⟨ zero⇒ , x ⟩               ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (zero-∘ʳ x) identityˡ ⟨
        ∇ ∘ ⟨ zero⇒ ∘ x , id ∘ x ⟩      ≈⟨ refl⟩∘⟨ ⟨⟩∘ ⟨
        ∇ ∘ ⟨ zero⇒ , id ⟩ ∘ x          ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ π₁∘i₂≈0 π₂∘i₂≈id ⟩∘⟨refl ⟨
        ∇ ∘ ⟨ π₁ ∘ i₂ , π₂ ∘ i₂ ⟩ ∘ x   ≈⟨ refl⟩∘⟨ g-η ⟩∘⟨refl ⟩
        ∇ ∘ i₂ ∘ x                      ≈⟨ cancelˡ ∇-identityˡ ⟩
        x                               ∎

    +-identityʳ : (x : A ⇒ B) → x + zero⇒ ≈ x
    +-identityʳ x = begin
        ∇ ∘ x ×₁ zero⇒ ∘ Δ              ≈⟨ refl⟩∘⟨ ×₁∘Δ ⟩
        ∇ ∘ ⟨ x , zero⇒ ⟩               ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ identityˡ (zero-∘ʳ x) ⟨
        ∇ ∘ ⟨ id ∘ x , zero⇒ ∘ x ⟩      ≈⟨ refl⟩∘⟨ ⟨⟩∘ ⟨
        ∇ ∘ ⟨ id , zero⇒ ⟩ ∘ x          ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ π₁∘i₁≈id π₂∘i₁≈0 ⟩∘⟨refl ⟨
        ∇ ∘ ⟨ π₁ ∘ i₁ , π₂ ∘ i₁ ⟩ ∘ x   ≈⟨ refl⟩∘⟨ g-η ⟩∘⟨refl ⟩
        ∇ ∘ i₁ ∘ x                      ≈⟨ cancelˡ ∇-identityʳ ⟩
        x                               ∎

    ∇∘+-swap : {A : Obj} → ∇ ∘ +-swap {A} ≈ ∇
    ∇∘+-swap = begin
        ∇ ∘ [ i₂ , i₁ ]     ≈⟨ ∘[] ⟩
        [ ∇ ∘ i₂ , ∇ ∘ i₁ ] ≈⟨ []-cong₂ inject₂ inject₁ ⟩
        [ id , id ]         ∎

    swap∘Δ : {A : Obj} → swap {A} ∘ Δ ≈ Δ
    swap∘Δ = begin
        ⟨ π₂ , π₁ ⟩ ∘ Δ     ≈⟨ ⟨⟩∘ ⟩
        ⟨ π₂ ∘ Δ , π₁ ∘ Δ ⟩ ≈⟨ ⟨⟩-cong₂ project₂ project₁ ⟩
        ⟨ id , id ⟩         ∎

    +-comm : (x y : A ⇒ B) → x + y ≈ y + x
    +-comm x y = begin
        ∇ ∘ x ×₁ y ∘ Δ          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ swap∘Δ ⟨
        ∇ ∘ x ×₁ y ∘ swap ∘ Δ   ≈⟨ refl⟩∘⟨ extendʳ swap∘×₁ ⟨
        ∇ ∘ swap ∘ y ×₁ x ∘ Δ   ≈⟨ refl⟩∘⟨ swap≈+-swap ⟩∘⟨refl ⟩
        ∇ ∘ +-swap ∘ y ×₁ x ∘ Δ ≈⟨ pullˡ ∇∘+-swap ⟩
        ∇ ∘ y ×₁ x ∘ Δ          ∎

    isCM : IsCommutativeMonoid (_≈_ {A} {B}) _+_ zero⇒
    isCM = record
        { isMonoid = record
            { isSemigroup = record
                { isMagma = record
                    { isEquivalence = equiv
                    ; ∙-cong = +-cong
                    }
                ; assoc = +-assoc
                }
            ; identity = +-identityˡ , +-identityʳ
            }
        ; comm = +-comm
        }

  hom : Obj → Obj → CommutativeMonoid ℓ e
  hom A B = record
      { Carrier = A ⇒ B
      ; _≈_ = _≈_
      ; _∙_ = _+_
      ; ε = zero⇒
      ; isCommutativeMonoid = isCM
      }

  +-resp-∘
      : {A B C D : Obj}
        {f g : B ⇒ C}
        {h : A ⇒ B}
        {k : C ⇒ D}
      → k ∘ (f + g) ∘ h ≈ k ∘ f ∘ h + k ∘ g ∘ h
  +-resp-∘ {f = f} {g} {h} {k} = begin
      k ∘ (∇ ∘ f ×₁ g ∘ Δ) ∘ h            ≈⟨ extendʳ (extendʳ ⇒∇) ⟩
      ∇ ∘ (k +₁ k ∘ f ×₁ g ∘ Δ) ∘ h       ≈⟨ refl⟩∘⟨ (×₁-+₁ k k ⟩∘⟨refl) ⟩∘⟨refl ⟨
      ∇ ∘ (k ×₁ k ∘ f ×₁ g ∘ Δ) ∘ h       ≈⟨ refl⟩∘⟨ pullʳ (pullʳ ⇒Δ) ⟩
      ∇ ∘ k ×₁ k ∘ f ×₁ g ∘ h ×₁ h ∘ Δ    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ×₁∘×₁ ⟩
      ∇ ∘ k ×₁ k ∘ (f ∘ h) ×₁ (g ∘ h) ∘ Δ ≈⟨ refl⟩∘⟨ pullˡ ×₁∘×₁ ⟩
      ∇ ∘ (k ∘ f ∘ h) ×₁ (k ∘ g ∘ h) ∘ Δ  ∎

  0-resp-∘
      : {A C D : Obj}
        {h : A ⇒ C}
        {k : C ⇒ D}
      → k ∘ zero⇒ ∘ h ≈ zero⇒
  0-resp-∘ {h = h} {k} = begin
      k ∘ zero⇒ ∘ h ≈⟨ pullˡ (zero-∘ˡ k) ⟩
      zero⇒ ∘ h     ≈⟨ zero-∘ʳ h ⟩
      zero⇒         ∎

  cm-category : CM-Category o ℓ e
  cm-category = record
      { 𝒞
      ; Hom = hom
      ; +-resp-∘ = +-resp-∘
      ; 0-resp-∘ = 0-resp-∘
      }
